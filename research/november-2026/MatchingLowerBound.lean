import Solution
import BipartiteMatching

/-! Build against `anthropics/formal-math`, project `vp-vnp`, commit
`11b6c7e3c927df2658f513b6b68ea7f8929c62c5`. -/
open MvPolynomial

namespace NovemberMatching

universe u

noncomputable def matchingPolynomial (F : Type u) [CommSemiring F] (m : ℕ) :
    MvPolynomial (Fin m × Fin m) F := weighted (fun i j => X (i,j))

theorem matchingPolynomial_eq (F : Type u) [CommSemiring F] (m : ℕ) :
    matchingPolynomial F m = Statement.perm F m := weighted_eq_permanent _

theorem matching_circuit_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p ≠ 2 → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p],
      ∀ m ≥ m₀, ∀ s : ℕ, Statement.Computes (matchingPolynomial F m) s → Statement.Beyond c m s := by
  obtain ⟨c,hc,H⟩ := Solution.mainTheorem.{u}
  refine ⟨c,hc,fun p hp => ?_⟩
  obtain ⟨m₀,hm⟩ := H p
  refine ⟨m₀,fun F _ _ m hmt s hs => ?_⟩
  rw [matchingPolynomial_eq] at hs
  exact (hm F m hmt s).2 hp hs

end NovemberMatching
