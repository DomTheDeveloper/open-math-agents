import CubeBound

namespace CubeBound

def PiEstimate (F : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, 2657 ≤ m → |(m.primeCounting : ℝ) - F m| <
    (1/(8*Real.pi)) * (Real.sqrt m * Real.log m)

def IntegralLower (F : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 2 ≤ a → a ≤ b → (b-a)/Real.log b ≤ F b-F a

private lemma cube_error (x : ℝ) (h : 0 ≤ x) :
    Real.sqrt (x^3) * Real.log (x^3) = 3 * (x * Real.sqrt x) * Real.log x := by
  rw [show x^3=x^2*x by ring, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq h]
  rw [← pow_succ, Real.log_pow]
  norm_num; ring

theorem large (F : ℝ → ℝ) (hpi : PiEstimate F) (hli : IntegralLower F)
    {n : ℕ} (hn : 64 ≤ n) : 2*n+1 < count n := by
  let x : ℝ := n
  let y := x+1
  have hx : 64 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hy : 0 < y := by dsimp [y]; linarith
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hl : 0 < Real.log y := Real.log_pos (by dsimp [y]; linarith)
  have hn1 : 2657 ≤ n^3 := (by decide : 2657 ≤ 64^3).trans (Nat.pow_le_pow_left hn 3)
  have hn2 : 2657 ≤ (n+1)^3 := hn1.trans (Nat.pow_le_pow_left (by omega) 3)
  have ha := (abs_lt.mp (hpi _ hn1)).2
  have hb := (abs_lt.mp (hpi _ hn2)).1
  push_cast at ha hb
  change (n^3).primeCounting - F (x^3) < _ at ha
  change _ < ((n+1)^3).primeCounting - F (y^3) at hb
  rw [cube_error x hx0.le] at ha
  rw [cube_error y hy.le] at hb
  have err : 3*(x*Real.sqrt x)*Real.log x ≤ 3*(y*Real.sqrt y)*Real.log y := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    gcongr
  have herr := mul_le_mul_of_nonneg_left err (by positivity : (0:ℝ) ≤ 1/(8*Real.pi))
  have hinc := hli (x^3) (y^3) (le_trans (by norm_num : (2:ℝ) ≤ 64^3) (pow_le_pow_left₀ (by norm_num) hx 3)) (pow_le_pow_left₀ hx0.le hxy 3)
  rw [Real.log_pow] at hinc
  norm_num only [Nat.cast_ofNat] at hinc
  have hwidth : x^2/Real.log y ≤ (y^3-x^3)/(3*Real.log y) := by
    have hw : 3*x^2 ≤ y^3-x^3 := by dsimp [y]; nlinarith only [hx0]
    calc
      _ = 3*x^2/(3*Real.log y) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hw (by positivity)
  have hcounts : x^2/Real.log y - 3/(4*Real.pi)*(y*Real.sqrt y)*Real.log y <
      (((n+1)^3).primeCounting : ℝ) - (n^3).primeCounting := by
    have hc : (3/(4*Real.pi))*(y*Real.sqrt y)*Real.log y =
        2*((1/(8*Real.pi))*(3*(y*Real.sqrt y)*Real.log y)) := by ring
    rw [hc]
    linarith only [ha,hb,herr,hinc,hwidth]
  have h := tail hx hcounts
  have hmono : (n^3).primeCounting ≤ ((n+1)^3).primeCounting :=
    Nat.monotone_primeCounting (Nat.pow_le_pow_left (by omega) 3)
  unfold count
  apply (Nat.cast_lt (α := ℝ)).mp
  rw [Nat.cast_sub hmono]; push_cast; exact h

end CubeBound
