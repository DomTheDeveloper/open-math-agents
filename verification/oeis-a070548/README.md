## oeis-a070548

Exact counting identities give the sum and difference of the two signs. Dominated convergence applied to the square-divisor sum proves squarefree density. Mertens’s RH bound at half the requested epsilon gives strict coefficient one eventually. At epsilon 1/4 the signed imbalance divided by n tends to zero, giving the positive-sign density. [Problem source](https://oeis.org/A070548)

The two Möbius identities are from the upstream module by Mayank Pandey and collaborators. Run `python3 fetch_mobius.py` here first. This downloads the unmodified 275-line module at its pinned revision and verifies the SHA-256. Lean 4.36.0 checked this module and the complete sign-count proof against the precise Mertens and RH interfaces. [Source module](https://github.com/mayankpandey9973/squarefree-explicit-formalized/blob/f0c7baf2d046503f49c8f220690ba1c91e42fe82/squarefree_lean/Squarefree/Mobius.lean)

The new deduction was checked on Lean 4.36.0. To run the full pinned dependency build, use `lake update && lake build` from this directory. The final module prints its axioms. The dependency build itself was not repeated here.
