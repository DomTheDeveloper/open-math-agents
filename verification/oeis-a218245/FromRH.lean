import NicolasFloor
import Nicolas
import Main

namespace NicolasFloor

noncomputable def term (k : ℕ) : ℤ :=
  ⌊(Nicolas.kthPrimorial k : ℝ) / Nat.totient (Nicolas.kthPrimorial k) -
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (Nicolas.kthPrimorial k))⌋

/-- Every term of OEIS A218245, indexed from one, is nonnegative. -/
theorem oeis_A218245 (k : ℕ) (hk : 1 ≤ k) : 0 ≤ term k :=
  (nonnegative_iff _ _).2 ((Nicolas.nicolas_of_RH riemannHypothesis k hk).le)

#print axioms oeis_A218245

end NicolasFloor
