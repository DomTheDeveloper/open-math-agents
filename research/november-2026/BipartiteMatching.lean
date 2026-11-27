import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Perm

/-! The weighted perfect matchings of a balanced bipartite graph are the
permanent of its biadjacency matrix, over any commutative semiring. -/
namespace NovemberMatching

structure Matching (I : Type*) where
  leftMate : I → I
  rightMate : I → I
  returnLeft : Function.LeftInverse rightMate leftMate
  returnRight : Function.RightInverse rightMate leftMate

def mateEquiv (I : Type*) : Matching I ≃ Equiv.Perm I where
  toFun M := ⟨M.leftMate, M.rightMate, M.returnLeft, M.returnRight⟩
  invFun σ := ⟨σ, σ.symm, σ.symm_apply_apply, σ.apply_symm_apply⟩
  left_inv M := by cases M; rfl
  right_inv σ := by cases σ; rfl

noncomputable instance {I : Type*} [Fintype I] [DecidableEq I] : Fintype (Matching I) :=
  Fintype.ofEquiv (Equiv.Perm I) (mateEquiv I).symm

/-- A zero edge weight allows the same definition for a graph with missing edges.
Columns index the left vertices, and rows index the right vertices. -/
noncomputable def weighted {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
    (A : I → I → R) : R := ∑ M : Matching I, ∏ i, A (M.leftMate i) i

theorem weighted_eq_permanent {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
    (A : I → I → R) : weighted A = ∑ σ : Equiv.Perm I, ∏ i, A (σ i) i := by
  unfold weighted
  exact Fintype.sum_equiv (mateEquiv I) _ _ (fun M => rfl)

end NovemberMatching
