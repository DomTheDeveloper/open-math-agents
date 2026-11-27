import GDMMills
import HilliardCubes
import Cramer.Main6
import Main

namespace MillsGreedy

private theorem floors_of_rh (rh : RiemannHypothesis) : ∃ A : ℝ, IsLeast candidates A ∧
    ∀ n : ℕ, ⌊A ^ height n⌋₊ = g n := by
  apply least_and_floors
  intro n hn
  obtain ⟨p,q,r,s,hp,_,_,_,ha,hb,hc,hd,he⟩ :=
    Hilliard.fourPrimes_of_bound (Cramer.cmsPrimeInterval_of_RH rh) hn
  exact ⟨p, hp, ha, by omega⟩

/-- The positive-index floors of the least Mills number are OEIS A051254. -/
theorem oeis_A051254 : ∃ A : ℝ, IsLeast candidates A ∧
    ∀ n : ℕ, ⌊A ^ height n⌋₊ = g n :=
  floors_of_rh riemannHypothesis

/-- Mills.exists_least with its positive-index convention and its abbreviations unfolded. -/
theorem gdm_exists_least : ∃ A : ℝ,
    IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} A := by
  obtain ⟨A,h,_⟩ := oeis_A051254
  exact exists_least_of_floors A h

/-- The positive-index existence statement in Mills' theorem. -/
theorem gdm_exists : ∃ A : ℝ, A > 1 ∧ ∀ n : ℕ+, Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊ := by
  obtain ⟨A,hA⟩ := gdm_exists_least
  exact ⟨A,hA.1⟩

/-- Caldwell and Cheng's ten-decimal interval in the catalogue's indexing. -/
theorem gdm_lower_bound_of_RH (rh : RiemannHypothesis) {A : ℝ}
    (hA : IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  obtain ⟨B,hB,hfloor⟩ := floors_of_rh rh
  have heq : candidates = {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} :=
    Set.ext candidates_pnat
  rw [← heq] at hA
  have hab : A = B := le_antisymm (hA.2 hB.1) (hB.2 hA.1)
  rw [hab]
  exact ten_decimals hB.1.1 hfloor

/-- The same interval after supplying the pinned RH theorem. -/
theorem gdm_mem_Ioo {A : ℝ}
    (hA : IsLeast {x : ℝ | x > 1 ∧ ∀ n : ℕ+, Prime ⌊x ^ (3 ^ (n : ℕ))⌋₊} A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 :=
  gdm_lower_bound_of_RH riemannHypothesis hA

#print axioms oeis_A051254
#print axioms gdm_exists
#print axioms gdm_exists_least
#print axioms gdm_lower_bound_of_RH
#print axioms gdm_mem_Ioo

end MillsGreedy
