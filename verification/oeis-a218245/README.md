# Nonnegativity of Nicolas's primorial floor sequence

For k ≥ 1 let Pₖ be the product of the first k primes. Every term of [OEIS A218245](https://oeis.org/A218245) is nonnegative.

Nicolas's inequality states that Pₖ/φ(Pₖ) exceeds exp(γ) log log Pₖ. Subtracting gives a positive real. Its floor is a nonnegative integer. The term uses the index in the prime sequence, so P₁ = 2, and division takes place in the reals. [Nicolas's inequality in Lean](https://github.com/senamakel/nicolas-rh/tree/3d453a6851594ce074e627e25516d346fa066053)

Lean checked the floor equivalence. The final module supplies `riemannHypothesis` to the upstream `Nicolas.nicolas_of_RH`. That result's published audit records one native finite check in addition to the three standard axioms. The local certificate here is for the floor deduction. Run `lake update && lake build` from this directory for the integrated RH target. [Upstream verification](https://github.com/senamakel/nicolas-rh/blob/3d453a6851594ce074e627e25516d346fa066053/README.md)
