import MillsGreedy
import HilliardCubes
import Cramer.Main6
import Main

namespace MillsGreedy

/-- The positive-index floors of the least Mills number are OEIS A051254. -/
theorem oeis_A051254 : ∃ A : ℝ, IsLeast candidates A ∧
    ∀ n : ℕ, ⌊A ^ height n⌋₊ = g n := by
  apply least_and_floors
  intro n hn
  obtain ⟨p,q,r,s,hp,_,_,_,ha,hb,hc,hd,he⟩ :=
    Hilliard.fourPrimes_of_bound (Cramer.cmsPrimeInterval_of_RH riemannHypothesis) hn
  exact ⟨p, hp, ha, by omega⟩

#print axioms oeis_A051254

end MillsGreedy
