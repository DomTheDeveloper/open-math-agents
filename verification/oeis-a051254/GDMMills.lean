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
