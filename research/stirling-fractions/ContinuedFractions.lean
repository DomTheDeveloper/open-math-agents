import Std

/-! A coefficientwise proof of the change of basis behind the Stieltjes fractions.
The parameters are arbitrary integers. In the three polynomial applications, equality
at every integer specialization implies identity of the row polynomials. -/
namespace AffineFractions

def source (a u v : Int) : Nat → Nat → Int
  | 0, _ => 1
  | n+1, k => (k:Int)*(v-u)*source a u v n k + (a+k*u)*source a u v n (k+1)

/-- Weights of paths from height 2h to zero in 2n unit steps. -/
def excursions (a u v : Int) : Nat → Nat → Int
  | 0, h => if h=0 then 1 else 0
  | n+1, 0 => a*(v*excursions a u v n 1 + excursions a u v n 0)
  | n+1, h+1 =>
      (a+((h:Int)+1)*u)*(v*excursions a u v n (h+2)+excursions a u v n (h+1))
       + ((h:Int)+1)*(v*excursions a u v n (h+1)+excursions a u v n h)

/-- The coefficient functional applied to X^h (1+vX)^k. -/
private def mixed (a u v : Int) : Nat → Nat → Nat → Int
  | 0, h, _ => if h=0 then 1 else 0
  | n+1, 0, k => (a+k*v)*mixed a u v n 0 k + v*(a+k*u)*mixed a u v n 1 k
  | n+1, h+1, k => ((h:Int)+1)*mixed a u v n h k +
      (a+((h:Int)+1)*(u+v)+k*v)*mixed a u v n (h+1) k +
      v*(a+((h:Int)+1+k)*u)*mixed a u v n (h+2) k

set_option maxHeartbeats 2000000
/-- Multiplying the basis element by 1+vX, before or after n applications. -/
private theorem basis_step (a u v : Int) (n h k : Nat) :
    mixed a u v n h (k+1) = mixed a u v n h k + v*mixed a u v n (h+1) k := by
  induction n generalizing h k with
  | zero => cases h <;> simp [mixed]
  | succ n ih =>
    cases h with
    | zero =>
      simp only [mixed, Int.natCast_succ, Int.natCast_zero]
      rw [ih 0 k, ih 1 k]
      grind
    | succ h =>
      simp only [mixed, Int.natCast_succ]
      rw [ih h k, ih (h+1) k, ih (h+2) k]
      grind

private theorem affine (a u v : Int) (n k : Nat) :
    mixed a u v n 0 k = source a u v n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [mixed, source, ← ih k, ← ih (k+1), basis_step a u v n 0 k]
    grind

private theorem paths (a u v : Int) (n h : Nat) :
    mixed a u v n h 0 = excursions a u v n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    cases h with
    | zero =>
      rw [mixed, excursions, ih 0, ih 1]
      grind
    | succ h =>
      rw [mixed, excursions, ih h, ih (h+1), ih (h+2)]
      grind

theorem all_coefficients (a u v : Int) (n : Nat) :
    source a u v n 0 = excursions a u v n 0 := by
  rw [← affine, ← paths]

#print axioms all_coefficients
end AffineFractions
