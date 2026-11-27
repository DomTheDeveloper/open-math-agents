import Std

/-! The all-exponent lifting step for the odd bases in the even-parameter proof. -/
namespace DyadicPower

/-- q_h is an integral witness to the congruence after h doublings. -/
private def remainder (z : Int) : Nat → Int
  | 0 => 0
  | h+1 => remainder z h + 2^h*(z+16*remainder z h)^2

private theorem lift (u z : Int) (hu : u^8 = 1+32*z) (h : Nat) :
    u^(8*2^h) = 1+2^h*32*z+2^h*512*remainder z h := by
  induction h with
  | zero => simp [remainder,hu]
  | succ h ih =>
    have exponent : 8 * 2^(h+1) = (8*2^h)*2 := by simp [Nat.pow_succ, Nat.mul_assoc]
    rw [exponent, Int.pow_mul, ih, remainder]
    simp only [Int.pow_succ (n:=h)]
    grind

/-- If u^8 is 1 mod 32, the remainder is divisible by 512 times the doubling factor. -/
theorem shift_lift (u z : Int) (hu : u^8 = 1+32*z) (h : Nat) :
    (2^h*512 : Int) ∣ (u^(8*2^h)-1) - 2^h*(u^8-1) := by
  refine ⟨remainder z h, ?_⟩
  rw [lift u z hu h, hu]
  grind

/-- Every odd integer base satisfies the all-exponent congruence. -/
theorem odd_shift_lift (u : Int) (odd : u%2=1) (h : Nat) :
    (2^h*512 : Int) ∣ (u^(8*2^h)-1) - 2^h*(u^8-1) := by
  obtain ⟨r, hr⟩ : ∃ r : Int, u^2=1+8*r := by
    let q := u/4
    by_cases hq : u%4=1
    · have hu : u=4*q+1 := by dsimp [q]; omega
      refine ⟨2*q^2+q, ?_⟩
      calc u^2 = (4*q+1)^2 := congrArg (fun x : Int => x^2) hu
           _ = _ := by grind
    · have hu : u=4*q+3 := by dsimp [q]; omega
      refine ⟨2*q^2+3*q+1, ?_⟩
      calc u^2 = (4*q+3)^2 := congrArg (fun x : Int => x^2) hu
           _ = _ := by grind
  let t := r+4*r^2
  have h4 : u^4=1+16*t := by
    calc u^4 = (u^2)^2 := by grind
         _ = _ := by rw [hr]; dsimp [t]; grind
  apply shift_lift u (t+8*t^2)
  calc u^8 = (u^4)^2 := by grind
       _ = _ := by rw [h4]; grind

#print axioms odd_shift_lift
end DyadicPower
