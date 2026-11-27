import MillsGreedy

namespace MillsGreedy

/-- Exact positive-natural indexing used by FormalConjectures.Wikipedia.Mills. -/
theorem candidates_pnat (A : ℝ) :
    A ∈ candidates ↔ A > 1 ∧ ∀ n : ℕ+, Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊ := by
  constructor
  · rintro ⟨ha,hp⟩
    refine ⟨ha,fun n => ?_⟩
    obtain ⟨k,hk⟩ : ∃ k : ℕ, (n:ℕ) = k+1 := ⟨(n:ℕ)-1,by have := n.pos; omega⟩
    rw [hk]; exact Nat.prime_iff.mp (hp k)
  · rintro ⟨ha,hp⟩
    exact ⟨ha,fun n => Nat.prime_iff.mpr (hp n.succPNat)⟩

theorem exists_least_of_floors (A : ℝ) (h : IsLeast candidates A) :
    ∃ L : ℝ, IsLeast {x : ℝ | x>1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} L := by
  have eq : candidates = {x : ℝ | x>1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} :=
    Set.ext candidates_pnat
  exact ⟨A, eq ▸ h⟩

end MillsGreedy

namespace MillsGreedy

private theorem next_eq {n p : ℕ} (hn : n^3 < p) (hp : p.Prime)
    (between : ∀ k, n^3 < k → k < p → ¬ k.Prime) : next n = p := by
  have h := next_least n
  apply le_antisymm (h.2 ⟨hn,hp⟩)
  exact le_of_not_gt (fun hl => between _ h.1.1 hl h.1.2)

private theorem g_one : g 1 = 11 := by
  change next 2 = 11
  apply next_eq (by norm_num) (by norm_num1)
  intro k lo hi
  norm_num at lo
  interval_cases k <;> norm_num1

private theorem g_two : g 2 = 1361 := by
  change next (g 1) = 1361
  rw [g_one]
  apply next_eq (by norm_num) (by norm_num1)
  intro k lo hi
  norm_num at lo
  interval_cases k <;> norm_num1

/-- The Lucas witness 5 and the factorization of p-1 are also used in
@senamakel's Mills.lower_bound_of_RH.R1 in open-math-agents. -/
private theorem fourth_prime : Nat.Prime 2521008887 := by
  have hlast : Nat.Prime 4982231 := by norm_num
  apply lucas_primality 2521008887 (5 : ZMod 2521008887)
  · change (5 : ZMod 2521008887)^2521008886 = 1
    reduce_mod_char
  · intro q hq hd
    have hf : 2521008887 - 1 = 2*11*23*4982231 := by decide
    rw [hf, hq.dvd_mul, hq.dvd_mul, hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hq hlast] at hd
    rcases hd with ((rfl | rfl) | rfl) | rfl <;> norm_num1 <;> reduce_mod_char <;> decide

private theorem g_three : g 3 = 2521008887 := by
  change next (g 2) = 2521008887
  rw [g_two]
  apply next_eq (by norm_num) fourth_prime
  intro k lo hi
  norm_num at lo
  interval_cases k <;> norm_num1

theorem ten_decimals {A : ℝ} (ha : 1 < A)
    (floors : ∀ n : ℕ, ⌊A ^ height n⌋₊ = g n) :
    A ∈ Set.Ioo (1.3063778838:ℝ) 1.3063778839 := by
  have h := floors 3
  rw [g_three] at h
  change ⌊A ^ 81⌋₊ = 2521008887 at h
  have hpow := (Nat.floor_eq_iff (pow_nonneg (by linarith : 0 ≤ A) 81)).mp h
  norm_num only [Nat.cast_ofNat] at hpow
  constructor
  · apply lt_of_pow_lt_pow_left₀ 81 (by positivity)
    exact (by norm_num : (1.3063778838:ℝ)^81 < 2521008887).trans_le hpow.1
  · apply lt_of_pow_lt_pow_left₀ 81 (by norm_num)
    exact hpow.2.trans_le (by norm_num : (2521008888:ℝ) ≤ (1.3063778839:ℝ)^81)

#print axioms ten_decimals
end MillsGreedy
