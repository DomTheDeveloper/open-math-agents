import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Infinite

namespace PositivePolynomial

/-- Real polynomials equal on a nonempty open box are equal as formal polynomials.
Each coordinate is allowed to use its own radius. -/
theorem eq_of_equal_on_positive_box {ι : Type*} (p q : MvPolynomial ι ℝ)
    (radius : ι → ℝ) (hpos : ∀ i, 0 < radius i)
    (h : ∀ x : ι → ℝ, (∀ i, 0 < x i ∧ x i < radius i) →
      MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  classical
  apply MvPolynomial.funext_set (fun i => Set.Ioo 0 (radius i)) (fun i => Set.Ioo_infinite (hpos i))
  intro x hx
  exact h x (fun i => hx i (Set.mem_univ i))

end PositivePolynomial
