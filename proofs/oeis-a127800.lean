import OMAStatements.S_oeis_a127800

/-!
Proof by @DomTheDeveloper. Subtract two consecutive row equations.
At an even index their lower endpoints agree. At an odd index the lower
endpoint advances by one, giving the row sum at half the index.
-/

open OMA.S_oeis_a127800

private lemma firstValues (r : ℕ → Rat) (hr : rowEquations r) :
    r 0 = 1 ∧ r 1 = 2 := by
  have h0 := hr 0
  have h1 := hr 1
  change (0 + r 0) - 0 = 1 at h0
  change ((0 + r 0) + r 1) - (0 + r 0) = 2 at h1
  grind

private lemma zeroAtEven (r : ℕ → Rat) (hr : rowEquations r) (k : ℕ) :
    r (2*k+2) = 0 := by
  have high := hr (2*k+2)
  have low := hr (2*k+1)
  rw [if_neg (by omega), show (2*k+2+1)/2 = k+1 by omega, prefixSum] at high
  rw [if_neg (by omega), show (2*k+1+1)/2 = k+1 by omega] at low
  grind

private lemma halveAtOdd (r : ℕ → Rat) (hr : rowEquations r) (k : ℕ) (hk : 0 < k) :
    r (2*k+1) = r k := by
  have high := hr (2*k+1)
  have low := hr (2*k)
  rw [if_neg (by omega), show (2*k+1+1)/2 = k+1 by omega] at high
  change (prefixSum r (2*k+1) + r (2*k+1)) - (prefixSum r k + r k) = 2 at high
  rw [if_neg (by omega), show (2*k+1)/2 = k by omega] at low
  grind

theorem OMA.solution : type_of% @OMA.S_oeis_a127800.main := by
  intro r hr
  obtain ⟨h0, h1⟩ := firstValues r hr
  refine ⟨h0, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hone : n = 1
    · subst n
      exact ⟨fun _ => h1, fun h => (h ⟨1, rfl⟩).elim⟩
    by_cases he : n % 2 = 0
    · have hn' : n = 2*((n-2)/2)+2 := by omega
      constructor
      · rintro ⟨e, h⟩
        cases e with
        | zero => simp at h; omega
        | succ e => rw [Nat.pow_succ] at h; omega
      · intro _
        exact (congrArg r hn').trans (zeroAtEven r hr _)
    · let k := n/2
      have hk : 0 < k := by dsimp [k]; omega
      have hn' : n = 2*k+1 := by dsimp [k]; omega
      have hrow := (congrArg r hn').trans (halveAtOdd r hr k hk)
      obtain ⟨hp, hz⟩ := ih k (by omega) hk
      rw [hrow]
      constructor
      · rintro ⟨e, h⟩
        cases e with
        | zero => simp at h; omega
        | succ e =>
          rw [Nat.pow_succ] at h
          exact hp ⟨e, by omega⟩
      · intro h
        apply hz
        rintro ⟨e, hpow⟩
        exact h ⟨e+1, by rw [Nat.pow_succ]; omega⟩
