import Mathlib

namespace IdonealPositions

def known : Finset ℕ :=
  {1,2,3,4,5,6,7,8,9,10,12,13,15,16,18,21,22,24,25,28,30,33,37,40,42,45,48,
   57,58,60,70,72,78,85,88,93,102,105,112,120,130,133,165,168,177,190,210,232,
   240,253,273,280,312,330,345,357,385,408,462,520,760,840,1320,1365,1848}

noncomputable def rank (P : ℕ → Prop) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 m).filter P).card

private lemma count_complement (S : Finset ℕ) (m : ℕ) (h : S ⊆ Finset.Icc 1 m)
    (P : ℕ → Prop) (hp : ∀ j ∈ Finset.Icc 1 m, P j ↔ j ∉ S) :
    rank P m = m - S.card := by
  classical
  have heq : (Finset.Icc 1 m).filter P = Finset.Icc 1 m \ S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact and_congr_right (fun hj => hp j hj)
  rw [rank, heq, Finset.card_sdiff_of_subset h, Nat.card_Icc]
  omega

private lemma range_known : ∀ j ∈ known, 1 ≤ j ∧ j ≤ 1848 := by decide +kernel
private lemma size_known : known.card = 65 := by decide +kernel
private lemma excluded (j : ℕ) : 3*j^2 ∈ known ↔ j ∈ ({1,2,4} : Finset ℕ) := by
  by_cases h : j < 25
  · exact (by decide +kernel : ∀ i : Fin 25, 3*i.val^2 ∈ known ↔ i.val ∈ ({1,2,4}:Finset ℕ)) ⟨j,h⟩
  · have hbig : 1848 < 3*j^2 := by nlinarith [Nat.pow_le_pow_left (by omega : 25 ≤ j) 2]
    have hno : 3*j^2 ∉ known := fun hj => (hbig.not_ge (range_known _ hj).2)
    simp [hno]; omega

theorem positions (P : ℕ → Prop) (complete : ∀ v, 0 < v → (P v ↔ v ∉ known))
    (n : ℕ) (hn : 22 ≤ n) : ∃ k : ℕ, 0 < k ∧ P (3*k^2) ∧
    rank (fun j => P (3*j^2)) k = n ∧ rank P (3*k^2) = 3*n^2+18*n-38 := by
  let k := n+3
  have hk : 25 ≤ k := by dsimp [k]; omega
  have big : 1848 < 3*k^2 := by nlinarith [Nat.pow_le_pow_left hk 2]
  have hgood : P (3*k^2) := (complete _ (by omega)).2
    (fun h => big.not_ge (range_known _ h).2)
  refine ⟨k,by omega,hgood,?_,?_⟩
  · let S : Finset ℕ := {1,2,4}
    have hs : S ⊆ Finset.Icc 1 k := by
      intro x hx; simp [S] at hx; rcases hx with rfl|rfl|rfl <;> simp [Finset.mem_Icc] <;> omega
    rw [count_complement S k hs]
    · have : S.card = 3 := by decide
      dsimp [k]; omega
    · intro j hj
      have hj1 := (Finset.mem_Icc.mp hj).1
      rw [complete _ (by positivity), excluded]
  · have hs : known ⊆ Finset.Icc 1 (3*k^2) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨(range_known _ hj).1,(range_known _ hj).2.trans big.le⟩
    rw [count_complement known _ hs _ (fun j hj => complete j (Finset.mem_Icc.mp hj).1), size_known]
    dsimp [k]
    have heq : 3*(n+3)^2 = 3*n^2+18*n+27 := by ring
    omega

#print axioms positions

end IdonealPositions
