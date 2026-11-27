import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace NovemberRobin

/-- Robin’s inequality with a variable coefficient. The verified coefficient is `exp γ`. -/
abbrev RobinAt (K : ℝ) : Prop := ∀ n : ℕ, 5040 < n →
  ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
    K * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- Multiplying by a chosen coprime integer turns the original Robin bound
into a bound with the explicit factor `q / σ(q)` for the remaining integer. -/
theorem coprime_bound {K : ℝ} (robin : RobinAt K) {q n : ℕ} (hc : q.Coprime n) (h : 5040 < q*n) :
    ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) * (ArithmeticFunction.sigma 1 n : ℕ) <
      K * ((q : ℝ) * n) * Real.log (Real.log ((q : ℝ)*n)) := by
  simpa only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc, Nat.cast_mul] using robin (q*n) h

/-- A single explicit inequality for every positive odd integer, including the small ones. -/
theorem odd_bound {K : ℝ} (robin : RobinAt K) {n : ℕ} (hodd : Odd n) :
    16383 * ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      K * (8192 * (n : ℝ)) * Real.log (Real.log (8192 * (n : ℝ))) := by
  have hq : (8192 : ℕ).Coprime n := hodd.coprime_two_left.pow_left 13
  have hn : 0 < n := by obtain ⟨k,hk⟩ := hodd; omega
  have hs : ArithmeticFunction.sigma 1 8192 = 16383 := by
    rw [show (8192:ℕ) = 2^13 from by decide, ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    decide
  have hi := coprime_bound robin hq (by omega : 5040 < 8192*n)
  simpa only [hs, Nat.cast_ofNat] using hi

end NovemberRobin
