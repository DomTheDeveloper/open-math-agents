# The prime sequence of the least Mills number

Start with 2. At each step choose the least prime strictly above the cube of the previous prime. This yields 2, 11, 1361, 2521008887, … . If A is the least Mills number, Lean proves that the entire sequence, indexed from zero in the code, equals floor(A^(3^(n+1))). [OEIS A051254](https://oeis.org/A051254) · [Caldwell and Cheng (2005)](https://cs.uwaterloo.ca/journals/JIS/VOL8/Caldwell/caldwell78.html)

The lower endpoint at stage n is the 3^(n+1)-th root of the greedy prime g(n). The corresponding upper endpoint uses g(n)+1. The cube-gap input makes the upper endpoints strictly decreasing, and the lower endpoints increase by the defining prime recurrence. Their supremum therefore lies in every half-open interval. Taking powers gives the prescribed floor at each index.

For every competing Mills number B, induction proves g(n) ≤ floor(B^(3^(n+1))). The prime floor at the next stage cannot equal an integer cube. Taking roots makes B an upper bound for all the lower endpoints and hence for their supremum. This establishes leastness.

Lean 4.36.0 checked the construction, greedy minimality, and all-index floor theorem. The axiom audit of `least_and_floors` printed only the three standard axioms. The final module supplies the [four-prime cube bound](https://github.com/DomTheDeveloper/open-math-agents/tree/2f9d0f04d85abbc5af728771e4de8cba75196773/verification/oeis-a060199) and the existing RH theorem. Run `lake update && lake build` here for that combined target.

## Google DeepMind's Mills statements

The final module exports the positive-index existence and leastness theorems and both forms of the ten-decimal interval for the least constant A. In the catalogue these are `Mills.exists'`, `Mills.exists_least`, `Mills.lower_bound_of_RH` and `Mills.mem_Ioo`. The formalizations use the exact catalogue types with its two abbreviations unfolded. The decimal result is due to Caldwell and Cheng. [Google DeepMind's Mills statements](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/Mills.lean)

The fourth greedy prime is 2521008887. Its primality follows from Lucas's theorem with witness 5. Exact arithmetic shows there is no prime between 1361³ and this prime. Bounding A⁸¹ by 2521008887 and 2521008888 and comparing rational powers gives 1.3063778838 < A < 1.3063778839. The prime certificate data also appear in [@senamakel's earlier registry reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/279168a6976d1af73c215f586ef95e0ffc775c98/reductions/Mills.lower_bound_of_RH.R1.lean).

Lean 4.33.1 checked the construction, exact prime certificate, decimal bounds and all four catalogue conclusions against the four-prime theorem's interface. Each printed only `propext`, `Classical.choice` and `Quot.sound`. The combined build that imports the pinned RH project is separate.
