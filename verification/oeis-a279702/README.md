# The eight negative terms of OEIS A279702

Exactly eight colossally abundant integers have a negative integer Robin residual. They are 2, 6, 12, 60, 120, 360, 2520 and 5040. Since the sequence has offset 2, exactly the terms at indices 2 through 9 are negative. [OEIS A279702](https://oeis.org/A279702)

## The sign calculation

For integer σ(k), the residual ⌊exp(γ) k log log k⌋ − σ(k) is negative exactly when exp(γ) k log log k < σ(k). In `Eight.lean`, rational bounds for the exponential and logarithm and exact divisor sums establish this strict inequality at all eight integers. The compiled kernel proof uses Lean's three standard axioms. For k > 5040, Robin's inequality gives a nonnegative residual. The final theorem imports the pinned Robin equivalence and RH. [RH verification](https://math.mit.edu/~drew/grh/)

## The colossally abundant prefix

A colossally abundant integer maximizes σ(m)/mˢ over integers m > 1 for some real s > 1. The pinned Robin formalization exhibits a global maximum at 5040 for a specific exponent at most 1 + 1/27. In `Champions.lean`, this bound and the monotonicity of pairwise score ratios reduce the classification through 5040 to comparisons at rational exponents. Seven rational exponents certify the seven earlier winners. For every other candidate between consecutive winners, two strict comparisons rule it out over the entire range of possible exponents. Integer powers and divisor sums decide all the finite comparisons in a single `native_decide`. [Pinned Robin formalization](https://github.com/kimihiro64/Robin1984/tree/5ce18bf3487c68d9353276ef5811057f60d17808)

`Exact.lean` combines the classification with the signs. For every strictly increasing enumeration of all colossally abundant integers, the residual is negative at precisely the first eight positions. The theorem assumes only the defining properties of the enumeration. In `FromRH.lean`, the published theorems supply the analytic inputs.

Lean 4.33.1 checked the arithmetic, the global classification from the stated maximum, and the all-index conclusion against the analytic inputs' interfaces. The full RH dependency build is separate. For the combined project run `lake update && lake build`. For an independent integer certificate of the prime-exponent transitions through the next winner, 55440, run `python3 check_ca_prefix.py`. [OEIS A004490](https://oeis.org/A004490)
