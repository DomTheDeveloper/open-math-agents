import Mathlib

namespace MillsGreedy

def height (n : ℕ) := 3^(n+1)

noncomputable def root (x : ℝ) (n : ℕ) := x ^ ((height n : ℝ)⁻¹)

private lemma height_ne (n : ℕ) : height n ≠ 0 := by simp [height]

private lemma root_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : root x n ^ height n = x := by
  rw [root, ← Real.rpow_natCast, ← Real.rpow_mul hx, inv_mul_cancel₀, Real.rpow_one]
  exact_mod_cast height_ne n

private lemma root_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ root x n :=
  Real.rpow_nonneg hx _

private lemma pow_step (a : ℝ) (n : ℕ) : a ^ height (n+1) = (a ^ height n)^3 := by
  simp [height, pow_succ 3 (n+1), pow_mul]

noncomputable def next (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n^3+1))

noncomputable def g : ℕ → ℕ
  | 0 => 2
  | n+1 => next (g n)

theorem next_least (n : ℕ) : IsLeast {p : ℕ | n^3 < p ∧ p.Prime} (next n) := by
  have hs := Nat.find_spec (Nat.exists_infinite_primes (n^3+1))
  exact ⟨⟨hs.1, hs.2⟩, fun p hp => Nat.find_min' _ ⟨hp.1, hp.2⟩⟩

private lemma g_prime : ∀ n, (g n).Prime
  | 0 => Nat.prime_two
  | n+1 => (next_least (g n)).1.2

def candidates : Set ℝ := {a | 1 < a ∧ ∀ n : ℕ, (⌊a ^ height n⌋₊).Prime}

private lemma lower {a : ℝ} (ha : a ∈ candidates) : ∀ n, g n ≤ ⌊a ^ height n⌋₊ := by
  intro n
  have hpos : 0 ≤ a := by linarith [ha.1]
  induction n with
  | zero => exact (ha.2 0).two_le
  | succ n ih =>
    apply (next_least _).2
    refine ⟨?_, ha.2 _⟩
    have hcast : (g n : ℝ) ≤ a ^ height n :=
      (by exact_mod_cast ih : (g n : ℝ) ≤ (⌊a ^ height n⌋₊ : ℕ)).trans
        (Nat.floor_le (pow_nonneg hpos _))
    have hweak : g n ^ 3 ≤ ⌊a ^ height (n+1)⌋₊ := by
      apply Nat.le_floor
      rw [pow_step]; push_cast; exact pow_le_pow_left₀ (by positivity) hcast _
    apply lt_of_le_of_ne hweak
    intro he
    have := ((ha.2 (n+1)).pow_eq_iff.mp he).2
    omega

/-- The floors of the least Mills number agree at every index with the greedy recurrence. -/
theorem least_and_floors
    (gap : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n^3 < p ∧ p+1 < (n+1)^3) :
    ∃ A : ℝ, IsLeast candidates A ∧ ∀ n : ℕ, ⌊A ^ height n⌋₊ = g n := by
  let lo (n : ℕ) := root (g n) n
  let hi (n : ℕ) := root ((g n : ℝ)+1) n
  have lo0 (n) : 0 ≤ lo n := root_nonneg (by positivity) _
  have hi0 (n) : 0 ≤ hi n := root_nonneg (by positivity) _
  have lp (n) : lo n ^ height n = g n := root_pow (by positivity) _
  have hp (n) : hi n ^ height n = (g n : ℝ)+1 := root_pow (by positivity) _
  have up (n) : g (n+1)+1 < (g n+1)^3 := by
    obtain ⟨p, prime, ha, hb⟩ := gap (g n) (g_prime n).pos
    have hle : g (n+1) ≤ p := (next_least _).2 ⟨ha, prime⟩
    omega
  have lm : Monotone lo := monotone_nat_of_le_succ fun n => by
    apply (pow_le_pow_iff_left₀ (lo0 n) (lo0 (n+1)) (height_ne (n+1))).1
    rw [pow_step (lo n), lp, lp]
    exact_mod_cast (next_least (g n)).1.1.le
  have hs (n) : hi (n+1) < hi n := by
    apply lt_of_pow_lt_pow_left₀ (height (n+1)) (hi0 n)
    rw [hp, pow_step (hi n), hp]
    exact_mod_cast up n
  have hm : Antitone hi := antitone_nat_of_succ_le fun n => (hs n).le
  have leHi (n m) : lo n ≤ hi m := by
    let k := max n m
    have mid : lo k ≤ hi k := by
      apply (pow_le_pow_iff_left₀ (lo0 k) (hi0 k) (height_ne k)).1
      rw [lp,hp]; linarith
    exact (lm (le_max_left n m)).trans (mid.trans (hm (le_max_right n m)))
  let A : ℝ := ⨆ n, lo n
  have loA (n) : lo n ≤ A := le_ciSup ⟨hi 0, by rintro _ ⟨m,rfl⟩; exact leHi m 0⟩ n
  have Ahi (n) : A < hi n := (ciSup_le fun k => leHi k (n+1)).trans_lt (hs n)
  have A0 := (lo0 0).trans (loA 0)
  have hfloor (n) : ⌊A ^ height n⌋₊ = g n := by
    rw [Nat.floor_eq_iff (pow_nonneg A0 _)]
    constructor
    · rw [← lp n]; exact pow_le_pow_left₀ (lo0 n) (loA n) _
    · rw [← hp n]; exact pow_lt_pow_left₀ (Ahi n) A0 (height_ne n)
  have hA : 1 < A := by
    by_contra! h
    have hle := (pow_le_one₀ A0 h : A ^ height 0 ≤ 1)
    have htwo := Nat.floor_le (pow_nonneg A0 (height 0))
    rw [hfloor] at htwo; change (2 : ℝ) ≤ _ at htwo
    linarith
  refine ⟨A, ⟨⟨hA, fun n => (hfloor n) ▸ g_prime n⟩, ?_⟩, hfloor⟩
  intro B hB
  apply ciSup_le
  intro n
  apply (pow_le_pow_iff_left₀ (lo0 n) (by linarith [hB.1]) (height_ne n)).1
  rw [lp]
  have hB' := Nat.floor_le (pow_nonneg (by linarith [hB.1] : 0 ≤ B) (height n))
  exact (by exact_mod_cast lower hB n : (g n : ℝ) ≤ (⌊B ^ height n⌋₊ : ℕ)).trans hB'

#print axioms least_and_floors

end MillsGreedy
