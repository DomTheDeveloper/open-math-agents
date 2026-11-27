## oeis-a025064

Lean proves both one-based ranks, including the three excluded square arguments, the maximum 1848, the cardinality 65, and the polynomial simplification for every n ≥ 22. The wrapper translates the ternary-form definition into the complement of the Weinberger list. [Problem source](https://oeis.org/A025064)

The new deduction was checked on Lean 4.36.0. To run the full pinned dependency build, use `lake update && lake build` from this directory. The final module prints its axioms. The dependency build itself was not repeated here.

## Merged registry target

`RegistryStatement.lean` is the [merged statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5402) at Git blob `00ae3a1a2ec04acfba542815f7488ff13666a783`. The single placeholder in that file is upstream's challenge. `RegistryProof.lean` uses `type_of%` to pin `OMA.solution` to that exact type and supplies the proof from `FromGRH.lean`. The check prints the axioms of the solution. The upstream checker allows only the challenge and Mathlib imports. This project makes its additional dependencies explicit for independent review.

The pinned Weinberger completeness proof uses native computation for its large finite range. Its README lists the native declarations in the axiom audit. [Weinberger audit](https://github.com/senamakel/weinberger-grh/tree/5d3c42b16ab217a82fcfe74e75cd7ddc65ce7c66#verification)
