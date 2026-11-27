module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.PNat.Basic

public section

/-!
# The first ten decimal places of Mills' constant

Under the Riemann hypothesis for the Riemann zeta function, the least real
number A > 1 whose positive-index Mills floors are all prime lies between the
two displayed rational decimals. This is the Caldwell–Cheng interval.
-/

/-- The statement of Mills.lower_bound_of_RH with both catalogue abbreviations expanded. -/
theorem Mills.lower_bound_of_RH (hRH : RiemannHypothesis) {A : ℝ}
    (hA : IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  sorry
