import Exact
import Main
import Solution
import Robin1984.Finite.RobinFiniteStartupCATangentEndpoints
import Robin1984.Finite.RobinTangentStartupComplete

namespace RobinSigns

private theorem after_cutoff {k : ℕ} (hk : 5040 < k) : 0 ≤ residual k :=
  nonnegative_after
    (Robin1984.robin_inequality_iff_riemannHypothesis.mpr riemannHypothesis) hk

private theorem classified (n : ℕ) (hn : n ≤ 5040) :
    RobinChampions.IsCA n ↔ n ∈ RobinChampions.listed := by
  have peak := Robin1984.colossallyAbundantWith_5040_at_cutoff
  exact RobinChampions.ca_prefix (1 + Robin1984.ca5040To55440Cutoff)
    (by linarith [peak.1])
    (by linarith [Robin1984.ca5040To55440Cutoff_lt_one_div_27])
    (fun m hm => peak.2.2 m hm) n hn

theorem exactly_eight_arguments (n : ℕ) :
    (RobinChampions.IsCA n ∧ residual n < 0) ↔ n ∈ RobinChampions.listed :=
  negative_arguments classified after_cutoff n

/-- The zero-based offsets 0 to 7 are exactly OEIS indices 2 through 9. -/
theorem oeis_A279702 (a : ℕ → ℕ) (ha : StrictMono a)
    (enumerates : ∀ n, RobinChampions.IsCA n ↔ ∃ i, a i = n) (i : ℕ) :
    residual (a i) < 0 ↔ i < 8 :=
  index_iff classified after_cutoff a ha enumerates i

#print axioms exactly_eight_arguments
#print axioms oeis_A279702

end RobinSigns
