import OMAReductions.R_Erdos427_erdos_427_variants_shiu_R1

-- Step Erdos427.erdos_427.variants.shiu.R1.H2: hypothesis H2 of reduction Erdos427.erdos_427.variants.shiu.R1
-- Credit: @DomTheDeveloper
-- H2 := ∀ (good : ℕ → Bool) (l r k : ℕ), 1 ≤ k →     (k - 1) * (((Finset.Ico l r).filter (fun i => good i = false)).card + 1) <         ((Finset.Ico l r).filter (fun i => good i = true)).card →     ∃ m : ℕ, l ≤ m ∧ m + k ≤ r ∧ ∀ i ∈ Finset.Ico m (m + k), good i = true
--
-- Pigeonhole on runs. If no window of k consecutive indices in [l, l + n) is entirely good,
-- then the number of good indices is at most (k - 1) * (number of bad indices + 1).
-- Strong induction on the length n: a short interval has at most k - 1 indices at all;
-- otherwise the first window [l, l + k) contains a bad index j, the piece [l, j] has at
-- most k - 1 good indices and at least one bad one, and the rest [j + 1, l + n) is shorter.

lemma OMA.run_count (good : ℕ → Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∀ n l : ℕ,
      (∀ m : ℕ, l ≤ m → m + k ≤ l + n → ∃ i ∈ Finset.Ico m (m + k), good i = false) →
      ((Finset.Ico l (l + n)).filter (fun i => good i = true)).card ≤
        (k - 1) * (((Finset.Ico l (l + n)).filter (fun i => good i = false)).card + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hno
    by_cases hnk : n < k
    · calc ((Finset.Ico l (l + n)).filter (fun i => good i = true)).card
          ≤ (Finset.Ico l (l + n)).card := Finset.card_filter_le _ _
        _ = n := by simp
        _ ≤ k - 1 := by omega
        _ ≤ (k - 1) * (((Finset.Ico l (l + n)).filter (fun i => good i = false)).card + 1) :=
            Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    · have hkn : k ≤ n := not_lt.mp hnk
      obtain ⟨j, hj, hjbad⟩ := hno l le_rfl (by omega)
      rw [Finset.mem_Ico] at hj
      have hsplit : Finset.Ico l (l + n) = Finset.Ico l (j + 1) ∪ Finset.Ico (j + 1) (l + n) :=
        (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
      have hdisj : Disjoint (Finset.Ico l (j + 1)) (Finset.Ico (j + 1) (l + n)) :=
        Finset.Ico_disjoint_Ico_consecutive l (j + 1) (l + n)
      have hG : ((Finset.Ico l (l + n)).filter (fun i => good i = true)).card =
          ((Finset.Ico l (j + 1)).filter (fun i => good i = true)).card +
            ((Finset.Ico (j + 1) (l + n)).filter (fun i => good i = true)).card := by
        rw [hsplit, Finset.filter_union]
        exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)
      have hB : ((Finset.Ico l (l + n)).filter (fun i => good i = false)).card =
          ((Finset.Ico l (j + 1)).filter (fun i => good i = false)).card +
            ((Finset.Ico (j + 1) (l + n)).filter (fun i => good i = false)).card := by
        rw [hsplit, Finset.filter_union]
        exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)
      have hG1 : ((Finset.Ico l (j + 1)).filter (fun i => good i = true)).card ≤ k - 1 := by
        have hsub : (Finset.Ico l (j + 1)).filter (fun i => good i = true) ⊆ Finset.Ico l j := by
          intro i hi
          rw [Finset.mem_filter, Finset.mem_Ico] at hi
          rw [Finset.mem_Ico]
          refine ⟨hi.1.1, ?_⟩
          rcases Nat.lt_or_ge i j with h | h
          · exact h
          · have hij : i = j := by omega
            rw [hij, hjbad] at hi
            exact absurd hi.2 (by decide)
        calc ((Finset.Ico l (j + 1)).filter (fun i => good i = true)).card
            ≤ (Finset.Ico l j).card := Finset.card_le_card hsub
          _ = j - l := by simp
          _ ≤ k - 1 := by omega
      have hB1 : 1 ≤ ((Finset.Ico l (j + 1)).filter (fun i => good i = false)).card := by
        apply Finset.card_pos.mpr
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hj.1, by omega⟩, hjbad⟩⟩
      have hrest := ih (l + n - (j + 1)) (by omega) (j + 1) (by
        intro m hm hmk
        exact hno m (by omega) (by omega))
      rw [show j + 1 + (l + n - (j + 1)) = l + n by omega] at hrest
      rw [hG, hB]
      calc ((Finset.Ico l (j + 1)).filter (fun i => good i = true)).card +
            ((Finset.Ico (j + 1) (l + n)).filter (fun i => good i = true)).card
          ≤ (k - 1) + (k - 1) *
              (((Finset.Ico (j + 1) (l + n)).filter (fun i => good i = false)).card + 1) :=
            Nat.add_le_add hG1 hrest
        _ = (k - 1) *
              (1 + ((Finset.Ico (j + 1) (l + n)).filter (fun i => good i = false)).card + 1) := by
            ring
        _ ≤ (k - 1) * (((Finset.Ico l (j + 1)).filter (fun i => good i = false)).card +
              ((Finset.Ico (j + 1) (l + n)).filter (fun i => good i = false)).card + 1) :=
            Nat.mul_le_mul_left _ (by omega)

theorem OMA.solution : OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2 := by
  unfold OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2
  intro good l r k hk h
  by_contra hrun
  rcases Nat.lt_or_ge r l with hlr | hlr
  · rw [Finset.Ico_eq_empty_of_le hlr.le] at h
    simp at h
  · have hcount := OMA.run_count good k hk (r - l) l (by
      intro m hm hmk
      by_contra hall
      apply hrun
      refine ⟨m, hm, by omega, ?_⟩
      intro i hi
      by_contra hi2
      apply hall
      refine ⟨i, hi, ?_⟩
      cases hgi : good i
      · rfl
      · exact absurd hgi hi2)
    rw [show l + (r - l) = r by omega] at hcount
    omega
