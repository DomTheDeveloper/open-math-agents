import IdonealFactorWindow

namespace IdonealFactorWindow

/-- An explicit obstruction to a universal first-term bound of thirteen. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem least_first_at_136173 :
    (14 < 17 ∧ 17 < 4385 ∧ 136173 = 14*17 + 17*4385 + 14*4385) ∧
    ∀ a b c : Nat, 0 < a → a < b → b < c → 136173 = a*b + b*c + a*c → 14 ≤ a := by
  refine ⟨by decide, ?_⟩
  intro a b c ha hab hbc he
  by_cases h : 14 ≤ a
  · exact h
  · have small : a ≤ 13 := by omega
    let d := a+b
    let e := a+c
    have w : Window 136173 a d e := by
      refine ⟨ha,by dsimp [d]; omega,by dsimp [d,e]; omega,?_⟩
      rw [he]
      simpa only [d,e] using ((show (a+b)*(a+c) = (a*b+b*c+a*c)+a*a by
        simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]))
    have da : d*d < 136173+a*a := (bounds w).2
    have aa := Nat.mul_self_le_mul_self small
    have hd : d < 370 := by
      by_cases good : d < 370
      · exact good
      · have hh := Nat.mul_self_le_mul_self (show 370 ≤ d by omega)
        omega
    have checked : (List.range 14).all (fun x => (List.range 370).all
      (fun y => !(accepts 136173 x y))) = true := by decide +kernel
    have hn := List.all_eq_true.mp (List.all_eq_true.mp checked a (List.mem_range.mpr (by omega))) d (List.mem_range.mpr hd)
    have hy := (accepts_iff 136173 a d).2 ⟨e,w⟩
    simp [hy] at hn

end IdonealFactorWindow
