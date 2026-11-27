import OMAStatements.S_oeis_a251328


/-!
# A transfer calculation for the two-column arrays of OEIS A251328

For a fixed first row there are three distinct completion counts. A row of odd
sum has four possible successors, all odd. A row of sum zero or four permits
one extreme and three middle rows. A row of sum two permits two extreme and
three middle rows. This accounts for actual arrays at every length.
-/

namespace A251328Proof
open OMA.S_oeis_a251328

/-- Odd, extreme (zero or four), and middle (two) starting row sums. -/
def counts : Nat → Nat × Nat × Nat
  | 0 => (1, 1, 1)
  | n + 1 =>
      let v := counts n
      (4 * v.1, v.2.1 + 3 * v.2.2, 2 * v.2.1 + 3 * v.2.2)

def weight (v : Nat × Nat × Nat) (r : Row) : Nat :=
  if rowSum r % 2 = 1 then v.1 else if rowSum r = 2 then v.2.2 else v.2.1

theorem transfer (v : Nat × Nat × Nat) (r : Row) :
    (rows.map (fun s => if fits r s then weight v s else 0)).sum =
      weight (4 * v.1, v.2.1 + 3 * v.2.2, 2 * v.2.1 + 3 * v.2.2) r := by
  obtain ⟨i,j⟩ := r
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases fin3 i with rfl | rfl | rfl <;>
    rcases fin3 j with rfl | rfl | rfl <;>
    first
    | change 0 + (0 + (v.2.2 + (0 + (v.2.2 + (0 + (v.2.2 + (0 + (v.2.1 + (0))))))))) = v.2.1 + 3*v.2.2
    | change 0 + (v.1 + (0 + (v.1 + (0 + (v.1 + (0 + (v.1 + (0 + (0))))))))) = 4*v.1
    | change v.2.1 + (0 + (v.2.2 + (0 + (v.2.2 + (0 + (v.2.2 + (0 + (v.2.1 + (0))))))))) = 2*v.2.1 + 3*v.2.2
    | change v.2.1 + (0 + (v.2.2 + (0 + (v.2.2 + (0 + (v.2.2 + (0 + (0 + (0))))))))) = v.2.1 + 3*v.2.2
  all_goals omega

theorem strip_count (n : Nat) (r : Row) : (strips n r).length = weight (counts n) r := by
  induction n generalizing r with
  | zero => simp [strips, counts, weight]
  | succ n ih =>
    rw [strips, List.length_flatMap]
    have h (s : Row) : (if fits r s then (strips n s).map (r :: ·) else []).length =
        (if fits r s then weight (counts n) s else 0) := by
      by_cases hf : fits r s <;> simp [hf, ih]
    simp only [h]
    exact transfer (counts n) r

theorem total_count (n : Nat) :
    a n = 4 * (counts n).1 + 2 * (counts n).2.1 + 3 * (counts n).2.2 := by
  rw [a, List.length_flatMap]
  simp only [strip_count]
  let v := counts n
  change v.2.1 + (v.1 + (v.2.2 + (v.1 + (v.2.2 + (v.1 + (v.2.2 + (v.1 + (v.2.1 + (0))))))))) = 4*v.1 + 2*v.2.1 + 3*v.2.2
  omega

theorem recurrence (n : Nat) :
    a (n+3) + 13 * a (n+1) + 12 * a n = 8 * a (n+2) := by
  simp only [total_count, counts] <;> omega

theorem a_zero : a 0 = 9 := by rw [total_count]; rfl
theorem a_one : a 1 = 39 := by rw [total_count]; rfl
theorem a_two : a 2 = 171 := by rw [total_count]; rfl
theorem a_three : a 3 = 753 := by rw [total_count]; rfl


-- The coefficients of (2 + sqrt 7)^n in the basis 1, sqrt 7.
def quadraticPower : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 =>
    let q := quadraticPower n
    (2*q.1 + 7*q.2, q.1 + 2*q.2)

theorem components (n : Nat) :
    (counts n).1 = 4^n ∧
    (counts n).2.1 = (quadraticPower n).1 + 2*(quadraticPower n).2 ∧
    (counts n).2.2 = (quadraticPower n).1 + 3*(quadraticPower n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨ho, he, hm⟩ := ih
    simp only [counts, quadraticPower, Nat.pow_succ, ho, he, hm]
    constructor
    · omega
    · constructor <;> omega

/-- The radical formula after adding its conjugates and clearing the denominator. -/
theorem exact_radical_coefficients (n : Nat) :
    14*(a n) = 56*4^n + 70*(quadraticPower n).1 + 182*(quadraticPower n).2 := by
  obtain ⟨ho, he, hm⟩ := components n
  rw [total_count, ho, he, hm]
  omega


theorem quadratic_powers (n : Nat) :
    qPow (2,1) n = (((quadraticPower n).1 : Int), ((quadraticPower n).2 : Int)) ∧
    qPow (2,-1) n = (((quadraticPower n).1 : Int), -((quadraticPower n).2 : Int)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [qPow, quadraticPower, ih.1, ih.2, qMul,
      Int.natCast_add, Int.natCast_mul]
    constructor <;> apply Prod.ext <;> dsimp <;> omega

theorem leading (n : Nat) : 7 * 2^(3+2*n) = 56 * 4^n := by
  rw [Nat.pow_add, Nat.pow_mul]
  change 7 * (8 * 4^n) = 56 * 4^n
  omega

theorem add_conjugates (value p u v : Nat) (h : 14*value = 56*p + 70*u + 182*v) :
    qAdd (qAdd (((56*p : Nat) : Int), 0) (qMul (35,-13) ((u : Int), -(v : Int))))
      (qMul ((u : Int), (v : Int)) (35,13)) = (14*(value : Int), 0) := by
  simp only [qAdd, qMul, Int.natCast_mul]
  apply Prod.ext <;> dsimp <;> omega

theorem radical_identity (n : Nat) :
    closedNumerator n = (14*(a n : Int), 0) := by
  rw [closedNumerator, leading, (quadratic_powers n).1, (quadratic_powers n).2]
  exact add_conjugates _ _ _ _ (exact_radical_coefficients n)

theorem series_identity (n : Nat) :
    linearDenominator (quadraticDenominator seriesCoeff) n = polynomialNumerator n := by
  match n with
  | 0 => rfl
  | 1 => simp [linearDenominator, quadraticDenominator, seriesCoeff, polynomialNumerator,
      constantSeries, shift, a_one]
  | 2 => simp [linearDenominator, quadraticDenominator, seriesCoeff, polynomialNumerator,
      constantSeries, shift, a_one, a_two]
  | 3 => simp [linearDenominator, quadraticDenominator, seriesCoeff, polynomialNumerator,
      constantSeries, shift, a_one, a_two, a_three]
  | k+4 =>
    have h : a (k+4) + 13*a (k+2) + 12*a (k+1) = 8*a (k+3) := recurrence (k+1)
    change (a (k+4) : Int) - 4*(a (k+3) : Int) - 3*(a (k+2) : Int) -
      4*((a (k+3) : Int) - 4*(a (k+2) : Int) - 3*(a (k+1) : Int)) = 0
    omega

end A251328Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a251328.main := by
  exact ⟨A251328Proof.series_identity, fun n _ => A251328Proof.radical_identity n⟩
