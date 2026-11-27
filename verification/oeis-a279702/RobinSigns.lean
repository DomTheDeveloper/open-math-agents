import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace RobinSigns

noncomputable def bound (k : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * k * Real.log (Real.log k)

noncomputable def residual (k : ℕ) : ℤ :=
  ⌊bound k⌋ - (ArithmeticFunction.sigma 1 k : ℤ)

theorem negative_iff (k : ℕ) :
    residual k < 0 ↔ bound k < (ArithmeticFunction.sigma 1 k : ℝ) := by
  unfold residual
  rw [sub_neg, Int.floor_lt]
  norm_cast

theorem nonnegative_after
    (robin : ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) < bound n)
    {k : ℕ} (hk : 5040 < k) : 0 ≤ residual k :=
  le_of_not_gt (fun h => (robin k hk).asymm ((negative_iff k).mp h))

end RobinSigns
