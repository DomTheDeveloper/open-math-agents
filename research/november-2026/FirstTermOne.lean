import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-! An exact test, at every positive integer, for a representation with first term one. -/
namespace IdonealFirstTerm

def HasFirstOne (n : ℕ) : Prop :=
  ∃ b c : ℕ, 1 < b ∧ b < c ∧ n = b + b*c + c

private def Split (m : ℕ) : Prop :=
  ∃ d e : ℕ, 2 < d ∧ d < e ∧ d*e = m

private theorem split_iff (n : ℕ) : HasFirstOne n ↔ Split (n+1) := by
  constructor
  · rintro ⟨b,c,hb,hc,rfl⟩
    exact ⟨b+1,c+1,by omega,by omega,by ring⟩
  · rintro ⟨d,e,hd,he,h⟩
    refine ⟨d-1,e-1,by omega,by omega,?_⟩
    have h₁ : d-1+1=d := by omega
    have h₂ : e-1+1=e := by omega
    have ht : (d-1)+(d-1)*(e-1)+(e-1)+1 = d*e := by
      calc
        _ = (d-1+1)*(e-1+1) := by ring
        _ = d*e := by rw [h₁,h₂]
    omega

/-- The possible values of n+1 when n has no representation with first term one. -/
def Exceptional (m : ℕ) : Prop :=
  m.Prime ∨ (∃ p : ℕ, p.Prime ∧ m = 2*p) ∨
    (∃ p : ℕ, p.Prime ∧ m = p*p) ∨ m=8 ∨ m=16

private theorem factors_equal {m x y : ℕ} (h : ¬ Split m)
    (hx : 2<x) (hy : 2<y) (hm : x*y=m) : x=y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact (h ⟨x,y,hx,hxy,hm⟩).elim
  · exact hxy
  · exact (h ⟨y,x,hy,hxy,by simpa [Nat.mul_comm] using hm⟩).elim

private theorem exceptional_of_no_split {m : ℕ} (hm : 2≤m) (h : ¬ Split m) : Exceptional m := by
  obtain ⟨p,hp,q,hmq⟩ := Nat.exists_prime_and_dvd (by omega : m≠1)
  have hp₂ := hp.two_le
  have hq₀ : q≠0 := by rintro rfl; simp at hmq; omega
  by_cases hq₁ : q=1
  · subst q
    exact Or.inl (by simpa [hmq] using hp)
  by_cases hp₂' : p=2
  · subst p
    by_cases hq : q.Prime
    · exact Or.inr (Or.inl ⟨q,hq,hmq⟩)
    obtain ⟨u,v,hu,hv,huv⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2≤q)).mp hq
    have hu₂ : 2≤u := by
      by_contra! hn
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : u≤1) with h | h <;> subst u <;> simp_all
    have hv₂ : 2≤v := by
      by_contra! hn
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : v≤1) with h | h <;> subst v <;> simp_all
    have hf : 2*(u*v)=m := by rw [huv,hmq]
    by_cases hu' : u=2
    · subst u
      by_cases hv' : v=2
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by subst v; omega))))
      · have h4 := factors_equal h (by decide : 2<4) (by omega : 2<v) (by simpa [← Nat.mul_assoc] using hf)
        exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    by_cases hv' : v=2
    · subst v
      have h4 := factors_equal h (by omega : 2<u) (by decide : 2<4) (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hf)
      exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    have h₁ := factors_equal h (by omega : 2<u) (by omega : 2<2*v) (by simpa [Nat.mul_left_comm] using hf)
    have h₂ := factors_equal h (by omega : 2<v) (by omega : 2<2*u) (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hf)
    omega
  · by_cases hq₂ : q=2
    · subst q
      exact Or.inr (Or.inl ⟨p,hp,by simpa [Nat.mul_comm] using hmq⟩)
    have heq := factors_equal h (by omega : 2<p) (by omega : 2<q) hmq.symm
    exact Or.inr (Or.inr (Or.inl ⟨p,hp,by simpa [← heq] using hmq⟩))

private theorem complementary_dvd {p x y k : ℕ} (hp : p.Prime) (h : x*y=p*k) :
    x∣k ∨ y∣k := by
  have cancel {a b : ℕ} (ha : p∣a) (hab : a*b=p*k) : b∣k := by
    obtain ⟨u,rfl⟩ := ha
    have hk := Nat.eq_of_mul_eq_mul_left hp.pos (show p*(u*b)=p*k by simpa [Nat.mul_assoc] using hab)
    exact ⟨u,by simpa [Nat.mul_comm] using hk.symm⟩
  rcases hp.dvd_or_dvd (show p∣x*y from ⟨k,h⟩) with hd | he
  · exact Or.inr (cancel hd h)
  · exact Or.inl (cancel he (by simpa [Nat.mul_comm] using h))

private theorem no_split_of_exceptional {m : ℕ} (h : Exceptional m) : ¬ Split m := by
  rintro ⟨d,e,hd,he,hde⟩
  rcases h with hp | ⟨p,hp,hm⟩ | ⟨p,hp,hm⟩ | hm | hm
  · exact Nat.not_prime_of_mul_eq hde (by omega) (by omega) hp
  · have h := complementary_dvd hp (show d*e=p*2 by simpa [Nat.mul_comm] using hde.trans hm)
    rcases h with h | h <;> have := Nat.le_of_dvd (by decide : 0<2) h <;> omega
  · have hz := hde.trans hm
    rcases complementary_dvd hp hz with h | h
    · have hh := (hp.eq_one_or_self_of_dvd d h).resolve_left (by omega)
      subst d
      have := Nat.eq_of_mul_eq_mul_left hp.pos hz
      omega
    · have hh := (hp.eq_one_or_self_of_dvd e h).resolve_left (by omega)
      subst e
      have := Nat.eq_of_mul_eq_mul_left hp.pos (show p*d=p*p by simpa [Nat.mul_comm] using hz)
      omega
  all_goals
    by_cases h4 : 4≤d
    · have := Nat.mul_le_mul h4 (by omega : 5≤e)
      omega
    · have hh : d=3 := by omega
      subst d
      omega

/-- The classification covers all positive n. -/
theorem no_first_one_iff {n : ℕ} (hn : 0<n) : ¬ HasFirstOne n ↔ Exceptional (n+1) := by
  rw [split_iff]
  exact ⟨exceptional_of_no_split (by omega), no_split_of_exceptional⟩

end IdonealFirstTerm
