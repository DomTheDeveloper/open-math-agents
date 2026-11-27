import Positions
import Weinberger.Main
import Main

namespace IdonealPositions

def representable (v : ℕ) := ∃ a b c : ℕ, 0<a ∧ a<b ∧ b<c ∧ v=a*b+b*c+a*c

private theorem complement (v : ℕ) (hv : 0<v) : representable v ↔ v ∉ known := by
  have h := Weinberger.isIdoneal_iff_of_GRH LFunction_ne_zero_of_half_lt_re v
  change (0 < v ∧ ¬ representable v) ↔ v ∈ known at h
  constructor
  · exact fun repr member => (h.mpr member).2 repr
  · intro absent
    by_contra noRepr
    exact absent (h.mp ⟨hv,noRepr⟩)

theorem formula (n : ℕ) (hn : 22 ≤ n) : ∃ k : ℕ, 0 < k ∧ representable (3*k^2) ∧
    rank (fun j => representable (3*j^2)) k = n ∧
    rank representable (3*k^2) = 3*n^2+18*n-38 := positions representable complement n hn

#print axioms formula
end IdonealPositions
