## oeis-a181564

The kernel checks the exact filter of all 65 idoneal numbers against the 16 listed semiprimes. Both directions then follow from the published Weinberger classification with Dirichlet GRH supplied. [Problem source](https://oeis.org/A181564)

The new deduction was checked on Lean 4.36.0. To run the full pinned dependency build, use `lake update && lake build` from this directory. The final module prints its axioms. The dependency build itself was not repeated here.

## Merged registry target

`RegistryStatement.lean` is the [merged statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5400) at Git blob `d2e68d2cf1f0902bab0ba8e6c90596e1edca4eac`. The single placeholder in that file is upstream's challenge. `RegistryProof.lean` uses `type_of%` to pin `OMA.solution` to that exact type and supplies the proof from `FromGRH.lean`. The check prints the axioms of the solution. The upstream checker allows only the challenge and Mathlib imports. This project makes its additional dependencies explicit for independent review.

The pinned Weinberger completeness proof uses native computation for its large finite range. Its README lists the native declarations in the axiom audit. [Weinberger audit](https://github.com/senamakel/weinberger-grh/tree/5d3c42b16ab217a82fcfe74e75cd7ddc65ce7c66#verification)
