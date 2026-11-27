import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime

namespace SunPrimeCertificates

def candidate (n k : ℕ) : ℕ := k * (k + 1) ^ (n - k).totient + 1

private theorem powModOne {a e m : ℕ} (hm : 1 < m) :
    (a : ZMod m) ^ e = 1 ↔ a ^ e % m = 1 := by
  have hone : 1 % m = 1 := Nat.mod_eq_of_lt hm
  constructor
  · intro h
    have hh : ((a ^ e : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by simpa using h
    have he : a ^ e % m = 1 % m := (ZMod.natCast_eq_natCast_iff _ _ _).mp hh
    exact he.trans hone
  · intro h
    have he : a ^ e ≡ 1 [MOD m] := h.trans hone.symm
    have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr he
    simpa using hh

/-- The prime divisors to check in a full-order certificate come from the two
small consecutive integers k and k+1. -/
theorem prime_of_certificate {n k a : ℕ} (hk : 0 < k)
    (full : a ^ (candidate n k - 1) % candidate n k = 1)
    (proper : ∀ q : ℕ, q.Prime → (q ∣ k ∨ q ∣ k + 1) →
      a ^ ((candidate n k - 1) / q) % candidate n k ≠ 1) :
    (candidate n k).Prime := by
  have hp : 1 < candidate n k := by
    have hpos : 0 < k * (k + 1) ^ (n - k).totient :=
      Nat.mul_pos hk (Nat.pow_pos (by omega))
    unfold candidate
    omega
  apply lucas_primality (candidate n k) (a : ZMod (candidate n k))
  · exact (powModOne hp).2 full
  · intro q hq hd heq
    have hdiv : q ∣ k * (k + 1) ^ (n - k).totient := by simpa [candidate] using hd
    have hs : q ∣ k ∨ q ∣ k + 1 :=
      (hq.dvd_mul.mp hdiv).imp_right fun h => hq.dvd_of_dvd_pow h
    exact proper q hq hs ((powModOne hp).1 heq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- At the upper endpoint the witness k=9999 produces the prime 99,990,001. -/
theorem witness_at_ten_thousand :
    ∃ k : ℕ, 0 < k ∧ k < 10000 ∧ (candidate 10000 k).Prime := by
  refine ⟨9999, by decide, by decide, ?_⟩
  change Nat.Prime 99990001
  norm_num1

end SunPrimeCertificates
