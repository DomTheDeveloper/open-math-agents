import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs

namespace LagariasFloor

noncomputable def residual (n : ℕ) : ℤ :=
  ⌊(harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)⌋ -
    (ArithmeticFunction.sigma 1 n : ℤ)

theorem nonnegative_iff (n : ℕ) : 0 ≤ residual n ↔
    (ArithmeticFunction.sigma 1 n : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  unfold residual
  rw [sub_nonneg, Int.le_floor]
  norm_cast

end LagariasFloor
