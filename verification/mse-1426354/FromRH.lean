import LagariasBound
import Main
import Solution
import Robin1984.Lagarias.Elementary

namespace LagariasBound

theorem answer (n : ℕ) (hn : 1 ≤ n) :
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ upperBound n ∧
    upperBound n ≤ (harmonic n : ℝ) + tailTerm n ∧
    (5040 < n → upperBound n < (harmonic n : ℝ) + tailTerm n) := bounds
  (Robin1984.riemann_hypothesis_iff_lagarias_elementary_criterion.mp riemannHypothesis)
  (Robin1984.robin_inequality_iff_riemannHypothesis.mpr riemannHypothesis)
  (fun hn => Robin1984.robinBound_le_exp_harmonic_mul_log_harmonic hn) n hn

#print axioms answer

end LagariasBound
