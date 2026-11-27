# Four primes between consecutive positive cubes

For every integer \(n\ge1\), the open interval \((n^3,(n+1)^3)\) contains at least four distinct primes. The bound is optimal. For \(n=1\), the interval contains precisely \(2,3,5,7\). Cino Hilliard posed the four-prime question in 2003 in [OEIS A060199](https://oeis.org/A060199).

## Proof used in Lean

Write \(u=n\), \(y=n+1\) and \(W=(y^3-u^3)/4\). For \(u\ge576\), one has \(\log y\le(5/18)\sqrt y\). To see this, put \(v=\sqrt y\ge24\) and apply \(\log t\le t-1\) to \(t=v/16\). This gives \(\log y\le 8\log 2+v/8-2\). The rational inequality \(2\le(1+7/640)^{64}\) gives \(\log 2\le7/10\) by the same logarithm bound. Substitution yields the claimed estimate.

For \(4\le x\le y^3\), it follows that

\[
\frac{22}{25}\sqrt{x}\log x
\le \frac{22}{25}y\sqrt y\cdot3\frac{5}{18}\sqrt y
=\frac{11}{15}y^2 < W-1.
\]

The final strict inequality is equivalent to \(u^2-43u-89>0\), which holds for \(u\ge576\). For each \(k=0,1,2,3\), apply the Carneiro–Milinovich–Soundararajan short-interval theorem at \(x=u^3+kW+1\). Its closed interval lies strictly inside the \(k\)th quarter of the cube interval. The four primes so obtained are distinct. [Carneiro, Milinovich and Soundararajan, Theorem 5](https://doi.org/10.4171/CMH/467)

For \(1\le n\le575\), the proof supplies four prime witnesses per interval. For the three smallest indices it checks the witnesses directly. For the others it verifies the ordering, endpoints and a primality certificate. Each witness \(p\) satisfies \(2\le p\le B^2\) and \(\gcd(p,B!)=1\) for an explicitly chosen power of two \(B\). Every composite \(p\) would have a divisor between \(2\) and \(\sqrt p\le B\). The balanced product in the source lets Lean check the factorial certificates by kernel reduction.

## A shorter independent argument

Chamberland and Straub proved under RH that every interval from \(t^{9/4}\) to \((t+1)^{9/4}\), for real \(t\ge1\), contains a prime. For \(n\ge27\), the mean value theorem gives \((n+1)^{4/3}-n^{4/3}>4\). Four disjoint closed intervals of length one fit strictly between those two endpoints. Raising their endpoints to the \(9/4\) power gives four disjoint prime-containing intervals strictly between the cubes. The finite certificates above include all remaining 26 cases. This argument explains how the conclusion also follows from earlier literature. [Chamberland and Straub, *Weakening the Legendre Conjecture*](https://arxiv.org/abs/2602.22502)

## Lean modules

`HilliardCubes.lean` defines `Hilliard.primeCount` as the cardinality of the primes in the open interval. Its main theorems are `Hilliard.four_le_primeCount_of_bound` and `Hilliard.minimum_of_bound`. Their only mathematical hypothesis is the stated short-interval bound.

`full/HilliardRH.lean` supplies the bound with `Cramer.cmsPrimeInterval_of_RH riemannHypothesis`. It exports `Hilliard.four_primes_between_consecutive_cubes` and `Hilliard.minimum_between_consecutive_cubes`. Both package configurations pin their dependencies. The Cramér project records its independent build of the bound with this RH proof. [Cramér verification record](https://github.com/senamakel/cramer-rh/blob/c465db4c64dcfd914075a76ac0ed66d1a05151d8/README.md#unconditional-version) · [Lean FRO and Mathlib statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)

## Reproduce the checks

From the project root, run the following commands with Lean 4.36.0.

```sh
lake update
lake exe cache get Mathlib.Data.Nat.Prime.Defs Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Tactic.LinearCombination Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring Mathlib.Data.Nat.Sqrt Mathlib.Data.Finset.Card Mathlib.Order.Interval.Finset.Nat
lake build
```

The root build checks all finite certificates and both deductions from the interval theorem. To use existing compiled checkouts for the final theorems, set `RH_DIR` and `CRAMER_DIR` to the matching project directories specified in `full/lakefile.toml`. After the root build, run these commands from the project root.

```sh
rh_path=$(cd "$RH_DIR" && lake env printenv LEAN_PATH)
cramer_path=$(cd "$CRAMER_DIR" && lake env printenv LEAN_PATH)
LEAN_PATH="$PWD/.lake/build/lib/lean:$rh_path:$cramer_path" lean full/HilliardRH.lean
```

Alternatively, run `lake update` and `lake build` inside `full` to build its dependencies from the pinned sources. The Cramér verification record describes the resources and shared cache for the full RH import.

## Verification on November 27, 2026

The root package built successfully with Lean 4.36.0 and mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The source also passed a direct Lean invocation. The kernel's axiom report for both root theorems lists only `propext`, `Classical.choice` and `Quot.sound`.

A separate local check established by `rfl` that the short-interval hypothesis is definitionally equal to the two upstream interval definitions composed as in `Cramer.CMSPrimeInterval`. It also type-checked the final proof expressions with the upstream theorems supplied as parameters. The full import of the compiled RH project was verified upstream on November 25. This project used that verification for the two upstream theorems and did not repeat the full import locally. The package includes the executable composition in `full/HilliardRH.lean` and the local compiler output in `verification.txt`.
