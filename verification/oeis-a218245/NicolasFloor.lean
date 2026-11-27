import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace NicolasFloor

theorem nonnegative_iff (quotient boundary : ℝ) :
    0 ≤ ⌊quotient - boundary⌋ ↔ boundary ≤ quotient := by
  rw [Int.floor_nonneg, sub_nonneg]

end NicolasFloor
