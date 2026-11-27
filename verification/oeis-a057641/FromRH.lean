import LagariasFloor
import Main
import Solution

/-- Every term of OEIS A057641 is nonnegative. -/
theorem oeis_A057641 (n : ℕ) (hn : 0 < n) : 0 ≤ LagariasFloor.residual n :=
  (LagariasFloor.nonnegative_iff n).2
    (Robin1984.riemann_hypothesis_iff_lagarias_elementary_criterion.mp riemannHypothesis n hn)

#print axioms oeis_A057641
