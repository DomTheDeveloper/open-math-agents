# Nonnegativity of the Lagarias floor sequence

For every positive integer n, the integer floor of Hₙ + exp(Hₙ) log Hₙ is at least σ(n). This is the nonnegativity assertion for [OEIS A057641](https://oeis.org/A057641), indexed from one. At n = 1 the residual is zero.

For any integer m and real x, m ≤ ⌊x⌋ is equivalent to m ≤ x. Applying this with m = σ(n) makes the sequence inequality equivalent, term by term, to Lagarias's divisor inequality. The final declaration supplies the published RH proof to the RH–Lagarias equivalence. [Lagarias (2002)](https://arxiv.org/abs/math/0008177) · [Verified arithmetic application and axiom audit](https://math.mit.edu/~drew/grh/)

Lean 4.33.1 checked the floor equivalence. The RH-to-Lagarias application was independently checked in the published arithmetic verification. The full dependency build can be reproduced in this directory with `lake update && lake build`. Its final target prints the axioms of `oeis_A057641`.
