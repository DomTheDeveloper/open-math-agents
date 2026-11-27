import OMAReductions.R_riemannZeta_simple_prop_lt_R1
import Mathlib

/-!
The three-point estimate uses two results from Thomas Lince's development.
The first bounds an explicit function of two nonnegative gaps. The second
turns any such gap bound into a count of simple zeros in the dyadic window.
Their three-point instance has block length 745 and pressure denominator 3000.
-/

namespace OMA.R_riemannZeta_simple_prop_lt_R1_H1_R1

open ZetaZeros

def H1 : Prop :=
  let K (x : ℝ) := ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
    Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
  let w (x : ℝ) := (K x / K 0) ^ 2
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    (1345 / 1000000 : ℝ) ≤ (x + y) / 3000 + w x + w y + 2 * w (x + y)

def H2 : Prop :=
  let K (x : ℝ) := ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
    Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
  let w (x : ℝ) := (K x / K 0) ^ 2
  let H : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ *
    (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)
  ∀ c : ℝ, 0 < c → c * 743 ≤ 1 →
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      c ≤ (x + y) / 3000 + w x + w y + 2 * w (x + y)) →
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((H - 2 * 744 / (3000 * 745)) / (1 - c * 743 / 745) - ε) *
        (N riemannZeta T (2 * T) : ℝ) ≤ Ns riemannZeta T (2 * T)

theorem main : H1 → H2 → OMA.R_riemannZeta_simple_prop_lt_R1.H1 := by
  intro gaps countZeros
  have bound := countZeros (1345 / 1000000) (by norm_num) (by norm_num) gaps
  have coefficient (h : ℝ) :
      (h - 2 * 744 / (3000 * 745)) / (1 - 1345 / 1000000 * 743 / 745) =
        (149000000 * h - 99200) / 148800133 := by ring
  unfold OMA.R_riemannZeta_simple_prop_lt_R1.H1
  simpa only [coefficient] using bound

end OMA.R_riemannZeta_simple_prop_lt_R1_H1_R1
