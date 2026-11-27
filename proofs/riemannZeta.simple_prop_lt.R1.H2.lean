import OMAReductions.R_riemannZeta_simple_prop_lt_R1
import Mathlib

open ZetaZeros

theorem OMA.solution : OMA.R_riemannZeta_simple_prop_lt_R1.H2 := by
  let H : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)
  change H = 2 - montgomeryTaylorConst⁻¹ ∧ (1 / 2 : ℝ) < H
  let r := Real.sqrt 2
  let x := r⁻¹
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr₂ : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 0 < x := inv_pos.mpr hr
  have hπ : x < Real.pi / 2 := by
    have : x ≤ 1 := inv_le_one_of_one_le₀ Real.one_lt_sqrt_two.le
    linarith [Real.pi_gt_three]
  have ht := Real.lt_tan hx hπ
  have heq : H = 3 / 2 - x / x.tan := by
    dsimp only [H, x, r]
    rw [Real.tan_eq_sin_div_cos, div_div_eq_mul_div, mul_div_assoc]
  rw [heq]
  constructor
  · unfold montgomeryTaylorConst
    simp only [one_div]
    change 3 / 2 - r⁻¹ / x.tan = 2 - (r * x.tan / (1 + x.tan / r))⁻¹
    rw [inv_div]
    have ht0 : 0 < x.tan := hx.trans ht
    field_simp
    nlinarith [congrArg (fun y : ℝ => y * x.tan) hr₂]
  · have hlt : x / x.tan < 1 := (div_lt_one (hx.trans ht)).2 ht
    linarith
