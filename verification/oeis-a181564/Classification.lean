import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Image

namespace SemiprimeIdoneal

def known : Finset ℕ :=
  {1,2,3,4,5,6,7,8,9,10,12,13,15,16,18,21,22,24,25,28,30,33,37,40,42,45,48,
   57,58,60,70,72,78,85,88,93,102,105,112,120,130,133,165,168,177,190,210,232,
   240,253,273,280,312,330,345,357,385,408,462,520,760,840,1320,1365,1848}

def listed : Finset ℕ := {4,6,9,10,15,21,22,25,33,57,58,85,93,133,177,253}

private theorem exact_filter : known.filter (fun n => n.primeFactorsList.length = 2) = listed := by
  decide +kernel

theorem classify (I : ℕ → Prop) (complete : ∀ n, I n ↔ n ∈ known) (n : ℕ) :
    (I n ∧ n.primeFactorsList.length = 2) ↔ n ∈ listed := by
  rw [complete, ← exact_filter, Finset.mem_filter]

#print axioms classify

end SemiprimeIdoneal
