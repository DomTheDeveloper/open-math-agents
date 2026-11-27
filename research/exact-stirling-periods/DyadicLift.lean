import Mathlib.Tactic.Ring

/-! The all-exponent arithmetic step used in the proof at the prime 2. -/
namespace DyadicLift

private def quotients (Q t : ℤ) : ℕ → ℤ
  | 0 => t
  | k+1 => let x := quotients Q t k; x + 2^k * Q * x^2

private theorem powers (Q t : ℤ) (k : ℕ) :
    (1+2*Q*t)^(2^k) = 1 + 2*(2:ℤ)^k*Q*quotients Q t k := by
  induction k with
  | zero => simp [quotients]
  | succ k ih =>
    rw [Nat.pow_succ, pow_mul, ih, pow_succ]
    simp only [quotients]
    ring

private theorem stable (Q t : ℤ) (k : ℕ) : Q ∣ quotients Q t k - t := by
  induction k with
  | zero => simp [quotients]
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    use w + 2^k * (quotients Q t k)^2
    change quotients Q t k + 2^k * Q * (quotients Q t k)^2 - t = _
    calc
      _ = (quotients Q t k - t) + Q*(2^k*(quotients Q t k)^2) := by ring
      _ = _ := by rw [hw]; ring

/-- With v = 1 + 2Qt, an arbitrary number of doublings has a controlled remainder. -/
theorem doubling_remainder (Q t v : ℤ) (hv : v = 1+2*Q*t) (k : ℕ) :
    (2*(2:ℤ)^k*Q^2) ∣ (v^(2^k)-1) - (2:ℤ)^k*(v-1) := by
  subst v
  rw [powers]
  obtain ⟨w, hw⟩ := stable Q t k
  use w
  calc
    _ = 2*(2:ℤ)^k*Q*(quotients Q t k-t) := by ring
    _ = _ := by rw [hw]; ring

/-- For odd u its 2^(r+1)-th power is 1 modulo 2^(r+3). -/
theorem odd_power (u : ℤ) (odd : u%2=1) (r : ℕ) :
    ∃ t : ℤ, u^(2^(r+1)) = 1+2*(2:ℤ)^(r+2)*t := by
  induction r with
  | zero =>
    have cases : u = 4*(u/4)+1 ∨ u = 4*(u/4)+3 := by omega
    rcases cases with h | h
    · refine ⟨(u/4)*(2*(u/4)+1), ?_⟩
      conv_lhs => rw [h]
      ring
    · refine ⟨2*(u/4)^2+3*(u/4)+1, ?_⟩
      conv_lhs => rw [h]
      ring
  | succ r ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t+(2:ℤ)^(r+2)*t^2, ?_⟩
    rw [show r+1+1 = (r+1)+1 by omega, Nat.pow_succ, pow_mul, ht]
    rw [show r+1+2 = (r+2)+1 by omega, pow_succ]
    ring

/-- This is the lifting modulus for s = r+1+k and R = r+1 in the written proof. -/
theorem odd_power_remainder (u : ℤ) (odd : u%2=1) (r k : ℕ) :
    (2*(2:ℤ)^k*((2:ℤ)^(r+2))^2) ∣
      (u^(2^(r+1+k))-1) - (2:ℤ)^k*(u^(2^(r+1))-1) := by
  obtain ⟨t, ht⟩ := odd_power u odd r
  rw [pow_add (2:ℕ) (r+1) k, pow_mul]
  exact doubling_remainder _ t _ ht k

#print axioms odd_power_remainder
end DyadicLift
