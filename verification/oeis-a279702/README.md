# The first eight colossally abundant Robin residuals

In [OEIS A279702](https://oeis.org/A279702), exactly the terms at indices 2 through 9 are negative. The offset is 2. The corresponding colossally abundant integers are 2, 6, 12, 60, 120, 360, 2520 and 5040. The next is 55440.

## Sign

For integer σ(k), the inequality ⌊exp(γ) k log log k⌋ − σ(k) < 0 is equivalent to the strict real inequality exp(γ) k log log k < σ(k). Lean 4.33.1 checked strict negativity for all eight inputs using rational bounds, exact divisor sums, and kernel reduction. For k > 5040 Robin's strict inequality implies a nonnegative integer residual. The RH link uses the same arithmetic theorem as the [published verification](https://math.mit.edu/~drew/grh/).

## Why these are the first eight colossally abundant integers

A colossally abundant integer maximizes σ(m)/mˢ for some s>1 over m>1. Multiplicativity separates maximization over prime exponents. Increasing the exponent of p from e to e+1 multiplies the objective by

$$\frac{p^{e+2}-1}{(p^{e+1}-1)p^s}.$$

For fixed p the ratio before division by pˢ equals p + (p−1)/(p^(e+1)−1), so it strictly decreases with e. Starting at a large s, each unique threshold crosses from an exponent e to e+1 as s decreases. For unused primes, the threshold is 1 + log(1+1/p)/log p, strictly decreasing with p. It suffices to consider every used prime and the first two unused primes. For fixed s>1 only finitely many primes and exponents are active. At a unique transition both neighboring integers maximize the objective. Allowing 1 in the comparison adds no integer above 1 before the first transition: if every prime factor worsens the objective then the largest single-prime objective is at 2, and products or larger exponents give smaller values. Indeed (p+1)/pˢ = (1+1/p)p^(1−s) decreases with p.

The nine rational separators in `check_ca_prefix.py` identify the unique maximal next threshold at every step. For a separator a/b, the transition exceeds it exactly when (p^(e+2)−1)^b > (p^(e+1)−1)^b p^a. The script verifies both strict sides with integers. This gives every maximizer through 5040 and its successor, including potential ties at the transition points. [OEIS A004490](https://oeis.org/A004490)

Run `python3 check_ca_prefix.py` for the prefix certificate. Run `lake update && lake build` for the pinned Lean components. Lean verifies the sign calculations and the all-index implication from the prefix; the prime-threshold enumeration above is verified separately in Python. The full RH import was not rebuilt for this PR.
