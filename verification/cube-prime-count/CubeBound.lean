import Mathlib

namespace CubeBound

/-- The endpoints of the interval are composite cubes (or one). -/
def count (n : ℕ) : ℕ := ((n+1)^3).primeCounting - (n^3).primeCounting

private theorem log_fourthRoot (y : ℝ) (hy : 0 < y) :
    Real.log y ≤ 3 / 2 * Real.sqrt (Real.sqrt y) := by
  let z := Real.sqrt (Real.sqrt y)
  have hz : 0 < z := Real.sqrt_pos.2 (Real.sqrt_pos.2 hy)
  have hzy : z^4 = y := by
    calc z^4 = (z^2)^2 := by ring
         _ = y := by rw [Real.sq_sqrt (Real.sqrt_nonneg y), Real.sq_sqrt hy.le]
  have hl := Real.add_one_le_exp (Real.log z - 1)
  rw [Real.exp_sub, Real.exp_log hz] at hl
  have hlog : Real.log z ≤ z / Real.exp 1 := by linarith
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hdiv : z / Real.exp 1 ≤ (3 / 8) * z := by
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    nlinarith only [mul_le_mul_of_nonneg_left he hz.le]
  have hlogy : Real.log y = 4 * Real.log z := by
    rw [← hzy, Real.log_pow]; norm_num
  change Real.log y ≤ 3 / 2 * z
  linarith

/-- Elementary tail estimate after subtracting the upper and lower Schoenfeld errors. -/
theorem tail {x c : ℝ} (hx : 64 ≤ x)
    (h : x^2 / Real.log (x+1) -
      (3 / (4 * Real.pi)) * ((x+1) * Real.sqrt (x+1)) * Real.log (x+1) < c) :
    2*x+1 < c := by
  let y := x+1
  let l := Real.log y
  have hy : 0 < y := by dsimp [y]; linarith
  have hl : 0 < l := Real.log_pos (by dsimp [y]; linarith)
  have hp : 0 ≤ 3 / (4*Real.pi) := by positivity
  have hp' : 3 / (4*Real.pi) ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).2
    linarith [Real.pi_gt_three]
  have hlog := log_fourthRoot y hy
  have hls : l^2 ≤ (9/4)*Real.sqrt y := by
    have ht := pow_le_pow_left₀ hl.le hlog 2
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg y)]
  have he : (3/(4*Real.pi))* (y*Real.sqrt y) * l^2 ≤ (9/16)*y^2 := by
    calc
      _ ≤ (1/4)*(y*Real.sqrt y)*((9/4)*Real.sqrt y) := by
        gcongr
      _ = _ := by nlinarith [congrArg (fun t : ℝ => y*t) (Real.sq_sqrt hy.le)]
  have hlog8 : l ≤ x/8 := by
    have hd := Real.log_le_sub_one_of_pos (show 0 < y/64 by positivity)
    rw [Real.log_div hy.ne' (by norm_num)] at hd
    have h64 : Real.log (64:ℝ) < 6 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    dsimp [l,y] at *
    linarith
  have hf : (2*x+1)*l ≤ (2*x+1)*(x/8) := mul_le_mul_of_nonneg_left hlog8 (by linarith)
  have hpoly : (2*x+1)*(x/8) + (9/16)*y^2 < x^2 := by
    dsimp [y]; nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ x)]
  have hc : 2*x+1 < x^2/l - (3/(4*Real.pi))*(y*Real.sqrt y)*l := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hl]
    nlinarith only [he, hf, hpoly]
  exact hc.trans h

#print axioms tail

end CubeBound
