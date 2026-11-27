# Ten decimal places of Mills' constant under RH

This project packages the Caldwell–Cheng interval for comparison against the exact Lean type of Google DeepMind's `Mills.lower_bound_of_RH`. The challenge unfolds the catalogue's abbreviations. The hypothesis is Mathlib's Riemann hypothesis for the Riemann zeta function.

`Solution.lean` constructs the least Mills number using the least prime above each successive cube. It bounds its 81st power using the fourth greedy prime, 2521008887, and performs both decimal comparisons with rational arithmetic. The pinned Cramér library supplies the short-interval estimate assuming RH. `HilliardCubes.lean` converts it into explicit prime witnesses between consecutive cubes. The project takes RH as an argument, so checking this statement does not require rebuilding the proof of RH itself.

The challenge and solution have separate Lake targets and the Comparator configuration permits only `propext`, `Classical.choice`, and `Quot.sound`. Run `lake exe cache get` and `lake build Challenge Solution` with the pinned toolchain. The Comparator configuration compares `Mills.lower_bound_of_RH`.

## Provenance

- W. H. Mills, “A prime-representing function” (1947).
- Chris K. Caldwell and Yuanyou Cheng, “Determining Mills' Constant and a Note on Honaker's Problem” (2005). [Journal article](https://cs.uwaterloo.ca/journals/JIS/VOL8/Caldwell/caldwell78.html)
- [Google DeepMind's catalogue statement](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/Mills.lean)
- [Greedy construction, exact digits and Lucas certificate](https://github.com/DomTheDeveloper/open-math-agents/tree/bff5be5359b53f94ac0266e217d52cc7b48f08ba/verification/oeis-a051254)
- [Earlier use of the Lucas witness data by @senamakel](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/279168a6976d1af73c215f586ef95e0ffc775c98/reductions/Mills.lower_bound_of_RH.R1.lean)
- [Hilliard four-prime deduction](https://github.com/DomTheDeveloper/open-math-agents/tree/2f9d0f04d85abbc5af728771e4de8cba75196773/verification/oeis-a060199) and [Cramér formalization](https://github.com/senamakel/cramer-rh/tree/c465db4c64dcfd914075a76ac0ed66d1a05151d8).

This snapshot prepares the source for external verification. Registration requires a matching mechanical report and registry review.
