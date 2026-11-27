import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Ring

namespace ExponentialWindows

/-- A finite exponential sum. Each pair records a base and its weight. -/
def moment {R : Type*} [CommRing R] (terms : List (R × R)) (n : ℕ) : R :=
  match terms with
  | [] => 0
  | (x,w) :: rest => w*x^n + moment rest n

private def eliminate {R : Type*} [CommRing R] (a : R) (L : List (R × R)) :=
  L.map fun (x,w) => (x, w*(x-a))

private theorem elimination {R : Type*} [CommRing R] (a : R) (L : List (R × R)) (n : ℕ) :
    moment (eliminate a L) n = moment L (n+1) - a * moment L n := by
  induction L with
  | nil => simp [eliminate, moment]
  | cons h t ih =>
    rcases h with ⟨x,w⟩
    change w*(x-a)*x^n + moment (eliminate a t) n = _
    rw [ih]
    simp only [moment, pow_succ]
    ring

private theorem dropFirst {R : Type*} [CommRing R] (a w : R) (L : List (R × R)) (n : ℕ) :
    moment (eliminate a L) n = moment ((a,w)::L) (n+1) - a * moment ((a,w)::L) n := by
  rw [elimination]
  simp only [moment, pow_succ]
  ring

/-- K consecutive zeros force the entire future of a K-term exponential sum to vanish,
including over rings with zero divisors. -/
theorem window_zero {R : Type*} [CommRing R] (K : ℕ) (L : List (R × R)) (len : L.length = K)
    (N : ℕ) (hw : ∀ i < K, moment L (N+i) = 0) : ∀ k, moment L (N+k) = 0 := by
  induction K generalizing L with
  | zero =>
    have : L = [] := List.length_eq_zero_iff.mp len
    subst L
    simp [moment]
  | succ K ih =>
    cases L with
    | nil => simp at len
    | cons h t =>
      rcases h with ⟨a,w⟩
      have lt : t.length = K := Nat.succ.inj len
      have ez := ih (eliminate a t) (by simpa [eliminate] using lt) (fun i hi => by
        rw [dropFirst a w t (N+i), Nat.add_assoc, hw (i+1) (by omega), hw i (by omega)]
        simp)
      intro k
      induction k with
      | zero => exact hw 0 (Nat.zero_lt_succ _)
      | succ k hk =>
        have z := ez k
        rw [dropFirst a w t (N+k), hk] at z
        simpa [Nat.add_assoc] using z

open Finset

/-- Distinct nonzero exponential functions remain linearly independent on every tail. -/
theorem tail_zero_iff {F : Type*} [Field F] {k : ℕ} (x w : Fin k → F)
    (inj : Function.Injective x) (nz : ∀ j, x j ≠ 0) :
    (∃ N : ℕ, ∀ n : ℕ, (∑ j, w j * x j^(N+n)) = 0) ↔ ∀ j, w j = 0 := by
  constructor
  · rintro ⟨N,h⟩
    have vec : (fun j => w j * x j^N) = 0 :=
      Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero inj (fun i => by
        simpa only [pow_add, mul_assoc] using h (i:ℕ))
    intro j
    have z : w j * x j^N = 0 := congrFun vec j
    exact (mul_eq_zero.mp z).resolve_right (pow_ne_zero _ (nz j))
  · intro h
    exact ⟨0, fun n => by simp [h]⟩

/-- A positive shift is an eventual period precisely when it fixes every base of nonzero weight. -/
theorem period_iff {F : Type*} [Field F] {k : ℕ} (x w : Fin k → F)
    (inj : Function.Injective x) (nz : ∀ j, x j ≠ 0) (d : ℕ) :
    (∃ N : ℕ, ∀ n : ℕ, (∑ j, w j * x j^(N+n+d)) = ∑ j, w j * x j^(N+n)) ↔
      ∀ j, w j ≠ 0 → x j^d = 1 := by
  have diff (i : ℕ) : (∑ j, (w j*(x j^d-1))*x j^i) =
      (∑ j, w j*x j^(i+d)) - ∑ j, w j*x j^i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  constructor
  · rintro ⟨N,h⟩
    have z := (tail_zero_iff x (fun j => w j*(x j^d-1)) inj nz).mp
      ⟨N, fun n => by rw [diff, h n, sub_self]⟩
    intro j hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp (z j)).resolve_left hw)
  · intro h
    refine ⟨0,fun n => sub_eq_zero.mp ?_⟩
    rw [← diff]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hw : w j=0
    · simp [hw]
    · simp [h j hw]

#print axioms window_zero
#print axioms tail_zero_iff
#print axioms period_iff
end ExponentialWindows
