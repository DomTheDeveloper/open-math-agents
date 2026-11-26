import FormalConjectures.OpenQuantumProblems.«23»

open OpenQuantumProblem23

namespace QubitCoordinates

lemma state0 : qubitSICFamily ⟨0, by decide⟩ = vec2 1 0 := rfl
lemma state1 : qubitSICFamily ⟨1, by decide⟩ = vec2 (tetraA : ℂ) (tetraB : ℂ) := rfl
lemma state2 : qubitSICFamily ⟨2, by decide⟩ = vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω) := rfl
lemma state3 : qubitSICFamily ⟨3, by decide⟩ = vec2 (tetraA : ℂ) ((tetraB : ℂ) * (ω ^ 2)) := rfl

lemma coordinates (a b c d : ℂ) :
    overlapSq (vec2 a b) (vec2 c d) = Complex.normSq (star a * c + star b * d) := by
  rw [overlapSq, Fin.sum_univ_two]
  rfl

end QubitCoordinates

open QubitCoordinates

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OpenQuantumProblem23.qubitSICFamily_pairwise := by
  have hw : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : tetraA ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hb : tetraB ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  intro i j hij
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals
    simp only [state0, state1, state2, state3, coordinates,
      Complex.normSq_apply, ω, Complex.star_def, pow_two,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im]
    norm_num [sicOverlapSq] <;> ring_nf <;> grobner
