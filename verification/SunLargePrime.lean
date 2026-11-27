import SunPrimeCertificates
import Mathlib.Tactic.Ring

/-!
The square-and-multiply loop below is adapted from Dev Pratap Singh's
OeisA234360/Checker.lean at revision 2dd137006c176c1b8780f50452e9a102f695d80c.
The full-order certificate with base 5 and the proofs of these two witnesses
are supplied for the computation through 10,000.
-/

/-
MIT License

Copyright (c) 2026 Dev Pratap Singh

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/

namespace SunPrimeCertificates.Large

def force (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | t + 1 => f (t + 1)

@[simp] theorem force_eq (f : ℕ → ℕ) (x : ℕ) : force f x = f x := by cases x <;> rfl

/-- One square-and-multiply step for bit `i` of the exponent `e`. The bit is read as
`e / 2 ^ i % 2`: the kernel evaluates `/`, `^` and `%` on numerals directly, whereas `e >>> i`
is unfolded into `i` nested halvings. -/
def stepK (b m e i acc : ℕ) : ℕ :=
  bif e / 2 ^ i % 2 == 1 then acc * acc % m * b % m else acc * acc % m

/-- Square-and-multiply from the top bit down; structurally recursive, so the kernel can run it. -/
def loopK (b m e : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | i + 1, acc => force (loopK b m e i) (stepK b m e i acc)

theorem stepK_eq (b m e i : ℕ) :
    stepK b m e i (b ^ (e / 2 ^ (i + 1)) % m) = b ^ (e / 2 ^ i) % m := by
  have hE : e / 2 ^ (i + 1) = (e / 2 ^ i) / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  set E := e / 2 ^ (i + 1)
  have hsq : b ^ E % m * (b ^ E % m) ≡ b ^ E * b ^ E [MOD m] :=
    (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
  unfold stepK
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ i) with h | h
  · have key : b ^ (e / 2 ^ i) = b ^ E * b ^ E := by
      conv_lhs => rw [show e / 2 ^ i = E + E by omega]
      ring
    simp only [h, show ((0 : ℕ) == 1) = false from rfl, cond_false]
    rw [key]; exact hsq
  · have key : b ^ (e / 2 ^ i) = b ^ E * b ^ E * b := by
      conv_lhs => rw [show e / 2 ^ i = E + E + 1 by omega]
      ring
    simp only [h, show ((1 : ℕ) == 1) = true from rfl, cond_true]
    rw [key]; exact ((Nat.mod_modEq _ _).trans hsq).mul_right b

theorem loopK_eq (b m e : ℕ) : ∀ i, loopK b m e i (b ^ (e / 2 ^ i) % m) = b ^ e % m := by
  intro i
  induction i with
  | zero => simp [loopK]
  | succ i ih => rw [loopK, force_eq, stepK_eq, ih]


private def residue (e m : ℕ) : ℕ :=
  loopK 5 m e 19548 (5 ^ (e / 2 ^ 19548) % m)

private theorem residue_eq (e m : ℕ) : residue e m = 5 ^ e % m :=
  loopK_eq 5 m e 19548

def largePrime : ℕ := 5157 * 5158 ^ 1584 + 1

private theorem phi2185 : Nat.totient 2185 = 1584 := by
  rw [show (2185:ℕ) = 5 * (19 * 23) from by decide,
      Nat.totient_mul (by decide : Nat.Coprime 5 (19 * 23)),
      Nat.totient_mul (by decide : Nat.Coprime 19 23),
      Nat.totient_prime (by decide : Nat.Prime 5),
      Nat.totient_prime (by decide : Nat.Prime 19),
      Nat.totient_prime (by decide : Nat.Prime 23)]

private theorem phi4824 : Nat.totient 4824 = 1584 := by
  rw [show (4824:ℕ) = 2 ^ 3 * (3 ^ 2 * 67) from by decide,
      Nat.totient_mul (by decide : Nat.Coprime (2 ^ 3) (3 ^ 2 * 67)),
      Nat.totient_mul (by decide : Nat.Coprime (3 ^ 2) 67),
      Nat.totient_prime_pow (by decide : Nat.Prime 2) (by decide : 0 < 3),
      Nat.totient_prime_pow (by decide : Nat.Prime 3) (by decide : 0 < 2),
      Nat.totient_prime (by decide : Nat.Prime 67)]
  decide

private theorem represented (n : ℕ) (h : (n - 5157).totient = 1584) :
    candidate n 5157 = largePrime := by
  unfold candidate largePrime
  rw [h]

private theorem repr7342 : candidate 7342 5157 = largePrime := by
  apply represented
  rw [show (7342 : ℕ) - 5157 = 2185 from by decide]
  exact phi2185

private theorem repr9981 : candidate 9981 5157 = largePrime := by
  apply represented
  rw [show (9981 : ℕ) - 5157 = 4824 from by decide]
  exact phi4824

private theorem factors {q : ℕ} (hq : q.Prime) (h : q ∣ 5157 ∨ q ∣ 5158) :
    q = 2 ∨ q = 3 ∨ q = 191 ∨ q = 2579 := by
  rcases h with ha | hb
  · rw [show (5157 : ℕ) = 3 ^ 3 * 191 from by decide] at ha
    rcases hq.dvd_mul.mp ha with h3 | h191
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp
        (hq.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 191)).mp h191)))
  · rw [show (5158 : ℕ) = 2 * 2579 from by decide] at hb
    rcases hq.dvd_mul.mp hb with h2 | h2579
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num1 : Nat.Prime 2579)).mp h2579)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem full : residue (largePrime - 1) largePrime = 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem cut2 : residue ((largePrime - 1) / 2) largePrime ≠ 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem cut3 : residue ((largePrime - 1) / 3) largePrime ≠ 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem cut191 : residue ((largePrime - 1) / 191) largePrime ≠ 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private theorem cut2579 : residue ((largePrime - 1) / 2579) largePrime ≠ 1 := by decide +kernel


theorem isPrime : Nat.Prime largePrime := by
  rw [← repr9981]
  apply prime_of_certificate (a := 5) (by decide)
  · rw [repr9981, ← residue_eq]
    exact full
  · intro q hq hd
    rw [repr9981, ← residue_eq]
    rcases factors hq hd with rfl | rfl | rfl | rfl
    · exact cut2
    · exact cut3
    · exact cut191
    · exact cut2579

theorem both_prime_witnesses :
    (candidate 7342 5157).Prime ∧ (candidate 9981 5157).Prime := by
  rw [repr7342, repr9981]
  exact ⟨isPrime, isPrime⟩

end SunPrimeCertificates.Large
