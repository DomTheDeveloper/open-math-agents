import Mathlib

namespace LagariasBound

noncomputable def tailTerm (n : ℕ) : ℝ :=
  Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

noncomputable def upperBound (n : ℕ) : ℝ :=
  if n ≤ 5040 then (harmonic n : ℝ) + tailTerm n else tailTerm n

theorem bounds
    (lagarias : ∀ n : ℕ, 0 < n → (ArithmeticFunction.sigma 1 n : ℝ) ≤ (harmonic n : ℝ) + tailTerm n)
    (robin : ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n))
    (comparison : ∀ {n : ℕ}, 3 ≤ n →
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤ tailTerm n)
    (n : ℕ) (hn : 1 ≤ n) :
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ upperBound n ∧
    upperBound n ≤ (harmonic n : ℝ) + tailTerm n ∧
    (5040 < n → upperBound n < (harmonic n : ℝ) + tailTerm n) := by
  by_cases small : n ≤ 5040
  · simp only [upperBound, if_pos small]
    exact ⟨lagarias n hn, le_rfl, fun h => False.elim (h.not_ge small)⟩
  · have large : 5040 < n := by omega
    have hpos : 0 < (harmonic n : ℝ) :=
      (Real.log_pos (show 1 < ((n+1 : ℕ) : ℝ) by exact_mod_cast (show 1<n+1 by omega))).trans_le
        (log_add_one_le_harmonic n)
    simp only [upperBound, if_neg small]
    have h := (robin n large).trans_le (comparison (by omega))
    exact ⟨h.le, by linarith, fun _ => by linarith⟩

#print axioms bounds

end LagariasBound
