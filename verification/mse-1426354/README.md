## mse-1426354

The bound agrees with the Lagarias expression through 5040 and drops the positive harmonic term at every larger n. The wrapper uses the proved RH theorem, both arithmetic criteria, and the Robin-to-harmonic comparison from Robin1984. [Problem source](https://math.stackexchange.com/q/1426354)

The new deduction was checked on Lean 4.33.1. To run the full pinned dependency build, use `lake update && lake build` from this directory. The final module prints its axioms. The dependency build itself was not repeated here.
