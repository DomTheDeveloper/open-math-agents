import Eight
import Main
import Solution

theorem robin_residual_nonnegative_after {k : ℕ} (hk : 5040 < k) :
    0 ≤ RobinSigns.residual k :=
  RobinSigns.nonnegative_after
    (Robin1984.robin_inequality_iff_riemannHypothesis.mpr riemannHypothesis) hk

#print axioms robin_residual_nonnegative_after

/-- On any nondecreasing list with the certified eight-term prefix and the
next entry above 5040, exactly the first eight values of the residual are negative. -/
theorem eight_terms_exact (a : ℕ → ℕ) (ordered : Monotone a)
    (prefix : ∀ i : Fin 8, a i ∈ ([2,6,12,60,120,360,2520,5040] : List ℕ))
    (next : 5040 < a 8) (i : ℕ) : RobinSigns.residual (a i) < 0 ↔ i < 8 := by
  by_cases h : i < 8
  · exact ⟨fun _ => h, fun _ => RobinSigns.eight_negative _ (prefix ⟨i,h⟩)⟩
  · have hi : 8 ≤ i := by omega
    have hnonneg := robin_residual_nonnegative_after (next.trans_le (ordered hi))
    exact ⟨fun hn => False.elim (hn.not_ge hnonneg), fun hi => False.elim (h hi)⟩

#print axioms eight_terms_exact
