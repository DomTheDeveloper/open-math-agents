import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime-indexed primes: strict decrease of their nth roots

Source: https://oeis.org/A006450
Conjecture: Zhi-Wei Sun, August 17, 2015.
Credit: @DomTheDeveloper

The source defines a(n) = prime(prime(n)), with indices starting at 1,
and conjectures that a(n)^(1/n) is strictly decreasing for n = 1, 2, ... .
This file states that conjecture; it does not provide a proof.
-/

namespace OMA.S_oeis_a006450

/-- The nth prime with the source's one-based indexing, for n ≥ 1.
Mathlib's `Nat.nth Nat.Prime` uses zero-based indexing. -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- OEIS A006450 at a positive index: a(n) = prime(prime(n)).
The first terms, at n = 1, 2, 3, are 3, 5, 11. -/
noncomputable def primeIndexedPrime (n : ℕ) : ℕ :=
  nthPrime (nthPrime n)

/-- The real nth roots of the prime-indexed primes strictly decrease
over all positive integer indices, as conjectured in the source. -/
theorem main :
    ∀ i j : ℕ, 1 ≤ i → i < j →
      (primeIndexedPrime j : ℝ) ^ (1 / (j : ℝ)) <
        (primeIndexedPrime i : ℝ) ^ (1 / (i : ℝ)) := by
  sorry

end OMA.S_oeis_a006450
