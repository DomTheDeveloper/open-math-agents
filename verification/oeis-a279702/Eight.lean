import RobinSigns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace RobinSigns

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


private theorem loglog_bound {n v u : ℝ} (hn : 1 < n) (hv : 0 ≤ v) (hu : 0 ≤ u)
    (h1 : n < ∑ i ∈ Finset.range 26, v ^ i / (i.factorial : ℝ))
    (h2 : v < ∑ i ∈ Finset.range 14, u ^ i / (i.factorial : ℝ)) :
    Real.log (Real.log n) < u := by
  have hlog := (Real.log_lt_iff_lt_exp (by linarith : 0 < n)).2
    (h1.trans_le (Real.sum_le_exp_of_nonneg hv 26))
  exact (Real.log_lt_iff_lt_exp (Real.log_pos hn)).2
    (hlog.trans (h2.trans_le (Real.sum_le_exp_of_nonneg hu 14)))

private theorem term_negative {k : ℕ} {v u : ℝ} {s : ℕ}
    (hk : 1 < (k : ℝ)) (hv : 0 ≤ v) (hu : 0 < u)
    (h1 : (k : ℝ) < ∑ i ∈ Finset.range 26, v ^ i / (i.factorial : ℝ))
    (h2 : v < ∑ i ∈ Finset.range 14, u ^ i / (i.factorial : ℝ))
    (hs : ArithmeticFunction.sigma 1 k = s) (h3 : (1787/1000 : ℝ) * k * u < s) :
    residual k < 0 := by
  apply (negative_iff k).2
  rw [hs]
  calc
    bound k < Real.exp Real.eulerMascheroniConstant * k * u :=
      mul_lt_mul_of_pos_left (loglog_bound hk hv hu.le h1 h2) (mul_pos (Real.exp_pos _) (by linarith))
    _ ≤ (1787/1000 : ℝ) * k * u := by gcongr; exact exp_gamma_upper.le
    _ < _ := h3

set_option maxRecDepth 20000 in
theorem eight_negative (k : ℕ)
    (hk : k ∈ ([2,6,12,60,120,360,2520,5040] : List ℕ)) : residual k < 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply term_negative (v := 139 / 200) (u := 1 / 10) (s := 3)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 1793 / 1000) (u := 117 / 200) (s := 12)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 1243 / 500) (u := 114 / 125) (s := 28)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 512 / 125) (u := 1411 / 1000) (s := 168)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 4789 / 1000) (u := 1567 / 1000) (s := 360)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 736 / 125) (u := 887 / 500) (s := 1170)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 3917 / 500) (u := 2059 / 1000) (s := 9360)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num
  · apply term_negative (v := 8527 / 1000) (u := 268 / 125) (s := 19344)
    · norm_num
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · norm_num [Finset.sum_range_succ, Nat.factorial_succ]
    · rw [ArithmeticFunction.sigma_one_apply]; decide +kernel
    · norm_num

#print axioms eight_negative

end RobinSigns
