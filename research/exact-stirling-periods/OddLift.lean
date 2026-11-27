import Mathlib.Tactic.Ring

/-! First-order lifting and translation identities for the Fermat quotients on page 3. -/
namespace OddLift

private def triangle : ℕ → ℤ
  | 0 => 0
  | n+1 => triangle n + n

private theorem triangle_twice (n : ℕ) : 2*triangle n = (n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => simp [triangle]
  | succ n ih =>
    change 2*(triangle n + (n:ℤ)) = _
    rw [mul_add, ih, Nat.cast_succ]
    ring

private theorem odd_triangle (p : ℕ) (odd : Odd p) : ∃ h : ℤ, triangle p = (p:ℤ)*h := by
  obtain ⟨k,hk⟩ := odd
  have hk' : p = 2*k + 1 := by omega
  have hc : (p:ℤ) = 2*(k:ℤ)+1 := by exact_mod_cast hk'
  refine ⟨k, ?_⟩
  have eq : 2*triangle p = 2*((p:ℤ)*k) := by rw [triangle_twice, hc]; ring
  omega

private theorem expand_three (x : ℤ) (n : ℕ) :
    ∃ z : ℤ, (1+x)^n = 1 + (n:ℤ)*x + triangle n*x^2 + x^3*z := by
  induction n with
  | zero => exact ⟨0, by simp [triangle]⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z+x*z+triangle n, ?_⟩
    rw [pow_succ, hz, Nat.cast_succ]
    simp only [triangle]
    ring

/-- If v=1+p*q and p is odd, then (v^(p^r)-1)/p^(r+1) equals q modulo p.
This form avoids division and holds over the integers without any coprimality premise. -/
theorem normalized_lift (p : ℕ) (odd : Odd p) (q : ℤ) (r : ℕ) :
    ∃ t : ℤ, (1+(p:ℤ)*q)^(p^r) = 1+(p:ℤ)^r*p*(q+p*t) := by
  obtain ⟨h, hh⟩ := odd_triangle p odd
  induction r with
  | zero => exact ⟨0, by simp⟩
  | succ r ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨z, hz⟩ := expand_three ((p:ℤ)^r*p*(q+p*t)) p
    refine ⟨t+h*(p:ℤ)^r*(q+p*t)^2+((p:ℤ)^r)^2*(q+p*t)^3*z, ?_⟩
    rw [Nat.pow_succ, pow_mul, ht, hz, hh, pow_succ]
    ring

/-- Translation of an integer power through first order, with a quadratic error. -/
theorem translated_power (a x : ℤ) (n : ℕ) :
    ∃ z : ℤ, (a+x)^(n+1) = a^(n+1)+((n:ℤ)+1)*a^n*x+x^2*z := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨a*z+x*z+((n:ℤ)+1)*a^n, ?_⟩
    rw [pow_succ (a+x) (n+1), hz, Nat.cast_succ]
    simp only [pow_succ a]
    ring

#print axioms normalized_lift
#print axioms translated_power
end OddLift
