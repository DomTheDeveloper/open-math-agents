import Small
import ExplicitFormula
import Schoenfeld
import Schoenfeld.Check.Li
import Main

namespace CubeBound

private theorem piEstimate : PiEstimate Real.logIntegral := by
  intro m hm
  have h := (Schoenfeld.schoenfeld_of_RH riemannHypothesis).2.2 (m : ℝ) (by exact_mod_cast hm)
  simpa using h

private theorem integralLower : IntegralLower Real.logIntegral := by
  intro a b ha hab
  rw [Schoenfeld.Check.logIntegral_eq_add ha (ha.trans hab), add_sub_cancel_left]
  exact (Schoenfeld.Check.integral_inv_log_bounds (by linarith) hab).1

/-- At least 2n+1 primes lie strictly between consecutive positive cubes; equality holds only at two. -/
theorem all_cubes (n : ℕ) (hn : 0 < n) :
    2*n+1 ≤ count n ∧ (count n = 2*n+1 ↔ n = 2) := by
  by_cases h : n < 64
  · exact small hn h
  · have hlarge := large _ piEstimate integralLower (by omega : 64 ≤ n)
    exact ⟨hlarge.le, by omega⟩

#print axioms all_cubes

end CubeBound
