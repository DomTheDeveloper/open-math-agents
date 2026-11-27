# Prime divisors of fifteen algebraic coefficient sequences

Clark Kimberling asked in October 2024 whether every prime divides infinitely many terms of each sequence below and whether the gaps between those indices eventually repeat. The answer to the divisibility question is yes for twelve sequences. Three omit the primes shown here at every index.

| Power being expanded | Coefficient of 1 | Other coefficients |
| --- | --- | --- |
| $(1+\sqrt2+\sqrt3)^n$ | A188570 omits 23 | A188571–A188573 each contain infinitely many multiples of every prime |
| $(2+\sqrt2+\sqrt3)^n$ | A377109 omits 241 | A377110–A377112 each contain infinitely many multiples of every prime |
| $(3+\sqrt2+\sqrt3)^n$ | A377113 omits 167 | A377114–A377116 each contain infinitely many multiples of every prime |
| $(u+u^2)^n$, $u^3=2$ | A377117 contains infinitely many multiples of every prime | The same holds for A377118 and A377119 |

For every positive case, the multiples of each prime occur on an entire arithmetic progression, and their successive index gaps eventually repeat. Each excluded prime in the table is the smallest prime dividing no term in its sequence. The supplied CSV gives an explicit term for each smaller prime.

## Proof

Multiplication of the four coordinates by $c+\sqrt2+\sqrt3$ has determinant $c^4-10c^2+1$. This equals $-8,-23,-8$ for $c=1,2,3$. Modulo a prime away from the determinant the state evolution is a permutation, so the initial vector $(1,0,0,0)$ returns. The three nonconstant coordinates vanish at every return. The exceptional primes have explicit returning states. The cubic family has determinant 6. Its nonconstant coordinates vanish at index 0, its constant coordinate at index 1, and the whole state vanishes from index 3 modulo 2 and 3.

For each counterexample, choose square roots $r$ of 2 and $s$ of 3 in the prime field. Four times the constant coefficient at index $n$ equals the sum of the $n$th powers of $c\pm r\pm s$. All four bases are units, so checking $p-1$ indices suffices for every $n$. The products of the constant residues in these three blocks are 5 modulo 23, 231 modulo 241 and 153 modulo 167. The complete argument, exceptional states and a worked 22-step certificate appear in [the note](Note.pdf).

## Reproduce the verification

The Lean project pins Lean 4.33.1 and the Mathlib revision in [lakefile.toml](lakefile.toml). Run these commands from this directory.

```sh
lake update
lake exe cache get
lake build RadicalPrimes
lake env lean Audit.lean
python3 verify.py
python3 audit_sources.py
```

[RadicalPrimes.lean](RadicalPrimes.lean) proves the coefficient expansions in a commutative ring, the three all-index exclusions, arithmetic progressions of hits for the twelve positive cases, periodicity of the divisibility pattern, and periodicity of consecutive gaps for an increasing enumeration of all hits. [Audit.lean](Audit.lean) prints the axioms of the main theorems. The kernel handles the bounded calculations in the prime-field certificates.

[verify.py](verify.py) uses only the Python standard library. It multiplies basis monomials directly, compares the constant coefficients to powers in the prime field, checks the finite exceptional cases, and produces [smaller-prime-witnesses.csv](smaller-prime-witnesses.csv) and [gap-cycles.csv](gap-cycles.csv). The latter starts each repeating word at the first zero in the periodic state cycle. Any earlier hits and the gaps up to that point are given separately.

[audit_sources.py](audit_sources.py) reads the fifteen entries at a fixed [OEIS data revision](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b). It accepts an optional `--source-dir` containing the original sequence files. Of 81 explicit source blocks, 2 agree with the labeled prime up to cyclic rotation and 75 agree with the prime indexed by that label. The script records all 86 claimed lengths in [source-cycle-audit.csv](source-cycle-audit.csv). For A377117 the source lists 1 at index 1, while the defining power has constant coefficient 0. A change at that single index preserves all eventual results. The tables in this packet follow the defining power.

## Sources

The conjectures and the coefficient sequences are recorded in the [OEIS family guide](https://oeis.org/A377109) and the linked entries. Sela Fried derived the quadratic coefficient recurrences for general parameters in [On the coefficients of powers of a sum of radicals](https://oeis.org/A188571/a188571_1.pdf) (2025). The finite-state arguments and explicit divisibility certificates are set out in the note. Historical priority has not been established.
