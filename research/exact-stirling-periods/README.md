# Exact modular periods of A354242 and A354253

[The five-page proof](ExactPeriods.pdf) determines the least eventual period of both sequences at every positive modulus. Let $a_b(n)$ have exponential generating function $(1-4b(e^x-1))^{-1/2}$. The parameter $b=1$ gives [A354242](https://oeis.org/A354242) and $b=2$ gives [A354253](https://oeis.org/A354253).

| Exact prime-power factor | A354242 | A354253 |
| --- | --- | --- |
| $p^e$ for prime $p\ge5$ | $(p-1)p^{e-1}$ | $(p-1)p^{e-1}$ |
| $3^e$ | $1$ at $e=1$, then $2\cdot3^{e-1}$ | $3^{e-1}$ through $e=5$, then $2\cdot3^{e-1}$ |
| $2^e$ | $1$ through $e=3$, then $2^{\max(1,e-5)}$ | $1$ through $e=6$, then $2^{\max(1,e-7)}$ |

The period modulo 1 is 1. For every larger modulus take the least common multiple of the answers for its prime-power factors. For example, modulo 1024 the periods are 32 and 8, respectively. A corollary on page 2 gives the sharp uniform starting index and period for the full class of integral substitutions $G(e^x-1)$.

Peter Bala's conjecture asked for a period dividing Euler's totient. A previous general result covers both sequences and gives the totient as a period from index $m$. The least-period formulas and their derivation are presented here. Historical priority for those formulas is unverified. [Earlier proof by the Omega Institute](https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.html)

## Reproduce the checks

The Python verifier uses only the standard library. It computes two full universal periods from the original differential recurrence for each of 515 moduli per sequence, verifies all 13 small-prime windows, and tests 888 instances of the normalized odd-prime difference formula. The Stirling transform provides an independent check on the first 101 terms of each sequence.

```sh
python3 verify.py
```

To check the displayed OEIS terms, place `A354242.seq` and `A354253.seq` from the [pinned OEIS source directory](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A354) in one directory, then run `python3 verify.py --oeis-dir /path/to/entries`.

For Lean 4.33.1, use the pinned Mathlib dependency from this directory.

```sh
lake update
lake exe cache get
lake build
```

| File | What Lean checks |
| --- | --- |
| [FiniteCertificates.lean](FiniteCertificates.lean) | All 13 finite windows, including factorial divisibility and the residues needed for the lower bounds. The five certificate theorems have empty axiom lists. |
| [ExponentialWindows.lean](ExponentialWindows.lean) | Consecutive zeros propagate for finite exponential sums over any commutative ring. Over a field, a shift fixes the sum on a tail exactly when it fixes every distinct nonzero base of nonzero weight. |
| [OddLift.lean](OddLift.lean) | The normalized odd-power lift and the first-order translation of an integer power with a quadratic error. |
| [DyadicLift.lean](DyadicLift.lean) | The divisibility law that propagates the dyadic certificates to all larger powers. |

The [written proof](ExactPeriods.tex) supplies the generating-function identities, their relation to the original OEIS sequences, the odd-prime weight calculation, and the final classification. The [verification record](verification.txt) includes the actual axiom reports and the Python cross-checks.
