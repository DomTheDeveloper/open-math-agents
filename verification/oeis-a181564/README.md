## oeis-a181564

The kernel checks the exact filter of all 65 idoneal numbers against the 16 listed semiprimes. Both directions then follow from the published Weinberger classification with Dirichlet GRH supplied. [Problem source](https://oeis.org/A181564)

The new deduction was checked on Lean 4.36.0. To run the full pinned dependency build, use `lake update && lake build` from this directory. The final module prints its axioms. The dependency build itself was not repeated here.
