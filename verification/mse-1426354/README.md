## mse-1426354

The bound agrees with the Lagarias expression through 5040 and drops the positive harmonic term at every larger n. The wrapper uses the proved RH theorem, both arithmetic criteria, and the Robin-to-harmonic comparison from Robin1984. [Problem source](https://math.stackexchange.com/q/1426354)

The new deduction was checked on Lean 4.33.1. To run the full pinned dependency build, use `lake update && lake build` from this directory. The final module prints its axioms. The dependency build itself was not repeated here.

## Merged registry target

`RegistryStatement.lean` is the [merged statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5405) at Git blob `09e5c3e17039144f76328f3d5fb4535f4e99622e`. The single placeholder in that file is upstream's challenge. `RegistryProof.lean` uses `type_of%` to pin `OMA.solution` to that exact type and supplies the proof from `FromRH.lean`. The check prints the axioms of the solution. The upstream checker allows only the challenge and Mathlib imports. This project makes its additional dependencies explicit for independent review.
