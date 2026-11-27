import Lean

/-!
A factor certificate for Euler's idoneal-number problem. `Triple n` is the
existential condition whose negation occurs in Formal Conjectures' `Idoneal.IsIdoneal`.
The factorization equivalence and its search bounds hold for all natural numbers.
-/
namespace IdonealFactorWindow

def Triple (n : Nat) : Prop :=
  ∃ a b c : Nat, 0 < a ∧ a < b ∧ b < c ∧ n = a*b + b*c + a*c

def Window (n a d e : Nat) : Prop :=
  0 < a ∧ 2*a < d ∧ d < e ∧ d*e = n + a*a

private theorem expand (a b c : Nat) :
    (a+b)*(a+c) = (a*b + b*c + a*c) + a*a := by
  simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem triple_iff (n : Nat) : Triple n ↔ ∃ a d e, Window n a d e := by
  constructor
  · rintro ⟨a,b,c,ha,hab,hbc,rfl⟩
    exact ⟨a,a+b,a+c,ha,by omega,by omega,expand a b c⟩
  · rintro ⟨a,d,e,ha,hd,he,hprod⟩
    let b := d-a
    let c := e-a
    have hbd : d = a+b := by dsimp [b]; omega
    have hce : e = a+c := by dsimp [c]; omega
    have hv := expand a b c
    rw [← hbd, ← hce, hprod] at hv
    exact ⟨a,b,c,ha,by omega,by omega,by omega⟩

/-- A valid witness lies strictly inside both search windows. -/
theorem bounds {n a d e : Nat} (h : Window n a d e) :
    3*(a*a) < n ∧ d*d < n+a*a := by
  obtain ⟨ha,had,hde,hs⟩ := h
  have hd : 0 < d := by omega
  have hsq : d*d < n+a*a := hs ▸ Nat.mul_lt_mul_of_pos_left hde hd
  have hlow := Nat.mul_self_lt_mul_self had
  have hprod : 2*a*(2*a) = 4*(a*a) := by
    calc 2*a*(2*a) = (2*2)*(a*a) := by ac_rfl
         _ = 4*(a*a) := rfl
  rw [hprod] at hlow
  exact ⟨by omega, hsq⟩

/-- Test one proposed divisor. The complementary factor determines the triple. -/
def accepts (n a d : Nat) : Bool :=
  decide (0 < a ∧ 2*a < d ∧ (n+a*a) % d = 0 ∧ d < (n+a*a)/d)

theorem accepts_iff (n a d : Nat) : accepts n a d = true ↔ ∃ e, Window n a d e := by
  simp only [accepts, decide_eq_true_eq]
  constructor
  · rintro ⟨ha,hd,hm,he⟩
    exact ⟨(n+a*a)/d,ha,hd,he,Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)⟩
  · rintro ⟨e,ha,hd,he,hm⟩
    have hp : 0 < d := by omega
    have hv : (n+a*a)/d = e := by rw [← hm, Nat.mul_div_cancel_left _ hp]
    exact ⟨ha,hd,Nat.mod_eq_zero_of_dvd ⟨e,hm.symm⟩,hv ▸ he⟩

/-- The exact relation used by the executable search. -/
theorem searchable_iff (n : Nat) : Triple n ↔
    ∃ a d, 3*(a*a) < n ∧ d*d < n+a*a ∧ accepts n a d = true := by
  rw [triple_iff]
  constructor
  · rintro ⟨a,d,e,hw⟩
    exact ⟨a,d,(bounds hw).1,(bounds hw).2,(accepts_iff n a d).2 ⟨e,hw⟩⟩
  · rintro ⟨a,d,_,_,h⟩
    obtain ⟨e,he⟩ := (accepts_iff n a d).1 h
    exact ⟨a,d,e,he⟩

end IdonealFactorWindow
