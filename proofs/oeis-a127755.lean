import OMAStatements.S_oeis_a127755
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Paul Barry's inverse factorial triangle

Source: OEIS A127755. Proof by @DomTheDeveloper.
Clearing the denominators one row at a time gives a lower triangular integer
matrix with diagonal entries 1. Its adjugate recovers the inverse. In fact,
every entry in column j of the inverse is a multiple of j!.
-/

open OMA.S_oeis_a127755

theorem OMA.solution : type_of% @OMA.S_oeis_a127755.main := by
  intro N i j
  let U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun r c =>
    if c.val ≤ r.val ∧ r.val ≤ 2 * c.val then 1 else 0
  let f (r : Fin (N + 1)) : ℚ := r.val.factorial
  let φ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ →+*
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ := (Int.castRingHom ℚ).mapMatrix
  have htri : U.IsLowerTriangular := by
    intro r c h
    change r.val < c.val at h
    exact if_neg (fun hc => (Nat.not_le_of_gt h) hc.1)
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U htri]
    apply Finset.prod_eq_one
    intro r _
    simp [U, show r.val ≤ 2 * r.val by omega]
  have hclear : Matrix.diagonal f * triangle N = φ U := by
    ext r c
    rw [Matrix.diagonal_mul]
    change f r * (if c.val ≤ r.val ∧ r.val ≤ 2 * c.val then (f r)⁻¹ else 0) =
      ((if c.val ≤ r.val ∧ r.val ≤ 2 * c.val then 1 else 0 : ℤ) : ℚ)
    have hpos : 0 < f r := by
      dsimp only [f]
      exact_mod_cast (Nat.factorial_pos r.val)
    split <;> simp [hpos.ne']
  have hadj : U.adjugate * U = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
  have hinv : (triangle N)⁻¹ = φ U.adjugate * Matrix.diagonal f := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, hclear, ← map_mul, hadj, map_one]
  refine ⟨U.adjugate i j * (j.val.factorial : ℤ), ?_⟩
  rw [hinv, Matrix.mul_diagonal]
  change (U.adjugate i j : ℚ) * (j.val.factorial : ℚ) = _
  push_cast
  rfl
