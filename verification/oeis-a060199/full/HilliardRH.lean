import HilliardCubes
import Cramer.Main6
import Main

namespace Hilliard

/-- Hilliard's 2003 conjecture on consecutive positive cubes (OEIS A060199). -/
theorem four_primes_between_consecutive_cubes (n : ℕ) (hn : 1 ≤ n) :
    4 ≤ primeCount n :=
  four_le_primeCount_of_bound (Cramer.cmsPrimeInterval_of_RH riemannHypothesis) hn

/-- The exact minimum for positive indices. -/
theorem minimum_between_consecutive_cubes : IsLeast (primeCount '' Set.Ici 1) 4 :=
  minimum_of_bound (Cramer.cmsPrimeInterval_of_RH riemannHypothesis)

#print axioms four_primes_between_consecutive_cubes
#print axioms minimum_between_consecutive_cubes

end Hilliard
