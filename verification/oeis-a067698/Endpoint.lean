import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The endpoint of Robin's inequality, for OEIS A067698. -/

namespace RobinExceptions

/-- OEIS A067698 starts at 2, where `log (log n)` is defined in real analysis. -/
def exceptions : Set ℕ := {n | 2 ≤ n ∧
  Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
    (ArithmeticFunction.sigma 1 n : ℝ)}

private theorem gamma_upper : Real.eulerMascheroniConstant < (58 / 100 : ℝ) := by
  have hh : harmonic 256 ≤ (15311 / 2500 : ℚ) := by
    set_option maxRecDepth 8192 in decide +kernel
  have hc : (harmonic 256 : ℝ) ≤ ((15311 / 2500 : ℚ) : ℝ) := Rat.cast_mono hh
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  have hg := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  change Real.eulerMascheroniConstant < (harmonic 256 : ℝ) - Real.log 256 at hg
  rw [show (256 : ℝ) = 2^8 by norm_num, Real.log_pow] at hg
  norm_num only [Nat.cast_ofNat] at hg
  linarith only [hg, hc, Real.log_two_gt_d9]

private theorem exp_gamma_upper : Real.exp Real.eulerMascheroniConstant < (1787 / 1000 : ℝ) := by
  refine (Real.exp_lt_exp.mpr gamma_upper).trans_le ?_
  refine (Real.exp_bound' (x := (58 / 100 : ℝ)) (by norm_num) (by norm_num) (n := 8)
    (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

private theorem loglog_upper : Real.log (Real.log 5040) < (2144 / 1000 : ℝ) := by
  have hlog : Real.log (5040 : ℝ) < 853 / 100 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 853 / 100) 18)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  apply (Real.log_lt_iff_lt_exp (Real.log_pos (by norm_num))).2
  refine hlog.trans_le <| le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2144 / 1000) 10)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

/-- Factorization or exact finite divisor arithmetic gives `σ(5040) = 19344`. -/
theorem sigma_5040 : ArithmeticFunction.sigma 1 5040 = 19344 := by
  rw [ArithmeticFunction.sigma_one_apply]
  set_option maxRecDepth 20000 in decide +kernel

/-- The endpoint violates Robin's strict inequality, with strict room to spare. -/
theorem endpoint_strict :
    Real.exp Real.eulerMascheroniConstant * 5040 * Real.log (Real.log 5040) < (19344 : ℝ) := by
  calc
    _ < Real.exp Real.eulerMascheroniConstant * 5040 * (2144 / 1000) :=
      mul_lt_mul_of_pos_left loglog_upper (by positivity)
    _ < (1787 / 1000 : ℝ) * 5040 * (2144 / 1000) := by
      nlinarith only [exp_gamma_upper]
    _ < 19344 := by norm_num

theorem endpoint_mem : 5040 ∈ exceptions := by
  refine ⟨by decide, ?_⟩
  change Real.exp _ * 5040 * Real.log (Real.log 5040) ≤ ((ArithmeticFunction.sigma 1 5040 : ℕ) : ℝ)
  rw [sigma_5040]
  exact endpoint_strict.le

/-- The exact positive-domain sequence has greatest element 5040 once Robin's tail is supplied. -/
theorem greatest_of_robin
    (tail : ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))) :
    IsGreatest exceptions 5040 := by
  refine ⟨endpoint_mem, ?_⟩
  intro n hn
  exact le_of_not_gt (fun h => (tail n h).not_ge hn.2)

/-- The greatest-element formulation is equivalent to the exact tail in Robin's criterion. -/
theorem greatest_iff_robin :
    IsGreatest exceptions 5040 ↔
      ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  refine ⟨?_, greatest_of_robin⟩
  intro h n hn
  apply lt_of_not_ge
  intro hbad
  exact (not_le_of_gt hn) (h.2 (show n ∈ exceptions from ⟨by omega, hbad⟩))

#print axioms sigma_5040
#print axioms endpoint_mem
#print axioms greatest_of_robin
#print axioms greatest_iff_robin

end RobinExceptions
