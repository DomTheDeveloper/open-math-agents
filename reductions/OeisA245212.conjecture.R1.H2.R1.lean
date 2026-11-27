import OMAReductions.R_OeisA245212_conjecture_R1
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Divisibility and large prime factors for Krizek’s OEIS A245212. Builds on project PRs 488 and 1048. -/

namespace OMA.R_OeisA245212_conjecture_R1_H2_R1

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private lemma order_odd {a : ℕ} (ha : Odd a) : padicValNat 2 a = 0 :=
  padicValNat.eq_zero_of_not_dvd ha.not_two_dvd_nat

private lemma order_two_mul {a : ℕ} (ha : 0 < a) :
    padicValNat 2 (2*a) = 1 + padicValNat 2 a := by
  rw [padicValNat.mul (by decide) ha.ne', padicValNat_self]

private lemma shift_order {a b j : ℕ} (ha : a ≠ 0) (hb : 2^(j+1) ∣ b) :
    padicValNat 2 (a+b) = j ↔ padicValNat 2 a = j := by
  have test (n : ℕ) (hn : n ≠ 0) :
      padicValNat 2 n = j ↔ 2^j ∣ n ∧ ¬ 2^(j+1) ∣ n := by
    rw [padicValNat_dvd_iff_le hn, padicValNat_dvd_iff_le hn]
    omega
  have hb' : 2^j ∣ b := (pow_dvd_pow 2 (by omega : j ≤ j+1)).trans hb
  rw [test (a+b) (by omega), test a ha, ← Nat.dvd_add_iff_left hb', ← Nat.dvd_add_iff_left hb]

private lemma geom_positive (p n : ℕ) (hn : 0 < n) :
    0 < ∑ j ∈ range n, p^j :=
  sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr hn, by simp⟩

private lemma moment_positive (p n : ℕ) (hn : 0 < n) :
    0 < ∑ j ∈ range n, p^j*(j+1) :=
  sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr hn, by simp⟩

private lemma geom_double (p n : ℕ) :
    (∑ j ∈ range (2*n), p^j) = (1+p^n)*(∑ j ∈ range n, p^j) := by
  rw [two_mul, sum_range_add]
  simp_rw [pow_add]
  rw [← mul_sum]
  ring

private lemma moment_double (p n : ℕ) :
    (∑ j ∈ range (2*n), p^j*(j+1)) =
      (1+p^n)*(∑ j ∈ range n, p^j*(j+1)) +
      n*p^n*(∑ j ∈ range n, p^j) := by
  rw [two_mul, sum_range_add]
  have h (j : ℕ) : p^(n+j)*(n+j+1) =
      p^n*(p^j*(j+1)) + (n*p^n)*p^j := by rw [pow_add]; ring
  simp_rw [h]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  ring

private lemma order_geom_ge (p n : ℕ) (hp : Odd p) (hn : 0 < n) :
    padicValNat 2 n ≤ padicValNat 2 (∑ j ∈ range n, p^j) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨t, ht⟩ := he
      have hnt : n = 2*t := by omega
      have ht0 : 0 < t := by omega
      have hind := ih t (by omega) ht0
      have hpow := Nat.odd_iff.mp (hp.pow : Odd (p^t))
      have hd : 2^1 ∣ 1+p^t := by simpa using (show 2 ∣ 1+p^t by omega)
      have hu := (padicValNat_dvd_iff_le (by omega : 1+p^t ≠ 0)).mp hd
      rw [hnt, geom_double, padicValNat.mul (by omega) (geom_positive p t ht0).ne', order_two_mul ht0]
      omega
    · rw [order_odd ho]
      exact Nat.zero_le _

private lemma moment_pairs_mod (p t : ℕ) (hp : Odd p) :
    (∑ j ∈ range (2*t), p^j*(j+1)) % 2 = t % 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2*(t+1)=2*t+1+1 by omega, sum_range_succ, sum_range_succ]
    have hodd := Nat.odd_iff.mp ((hp.pow : Odd (p^(2*t))).mul (show Odd (2*t+1) from ⟨t,rfl⟩))
    have hev : 2 ∣ p^(2*t+1)*(2*t+1+1) := dvd_mul_of_dvd_right (by omega) _
    omega

private lemma order_one_add_square (p t : ℕ) (hp : Odd p) :
    padicValNat 2 (1+p^(2*t)) = 1 := by
  obtain ⟨u, hu⟩ := (hp.pow : Odd (p^t))
  have hform : 1+p^(2*t) = 2*(2*(u*u+u)+1) := by
    rw [mul_comm 2 t, pow_mul, hu]
    ring
  rw [hform, order_two_mul (by omega), order_odd (show Odd (2*(u*u+u)+1) from ⟨_,rfl⟩)]

/-- The weighted geometric sum with an even number of terms has the same
two-adic order as half the number of terms, independently of the odd base. -/
private lemma order_even_moment (p t : ℕ) (hp : Odd p) (ht : 0 < t) :
    padicValNat 2 (∑ j ∈ range (2*t), p^j*(j+1)) = padicValNat 2 t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rcases Nat.even_or_odd t with he | ho
    · obtain ⟨u, hu⟩ := he
      have htu : t = 2*u := by omega
      have hu0 : 0 < u := by omega
      have hind := ih u (by omega) hu0
      rw [← htu] at hind
      have hfactor : padicValNat 2 (1+p^t) = 1 := htu ▸ order_one_add_square p u hp
      have hmain : padicValNat 2 ((1+p^t)*(∑ j ∈ range t, p^j*(j+1))) =
          padicValNat 2 t := by
        rw [padicValNat.mul (by omega) (moment_positive p t ht).ne', hfactor, hind, htu, order_two_mul hu0]
      have htval : 1 ≤ padicValNat 2 t := by rw [htu, order_two_mul hu0]; omega
      have hgeo := order_geom_ge p t hp ht
      have h2g : 2^1 ∣ ∑ j ∈ range t, p^j :=
        (padicValNat_dvd_iff_le (geom_positive p t ht).ne').mpr (by omega)
      have htail : 2^(padicValNat 2 t+1) ∣ t*p^t*(∑ j ∈ range t, p^j) := by
        rw [pow_succ]
        exact Nat.mul_dvd_mul (dvd_mul_of_dvd_left pow_padicValNat_dvd _) (by simpa using h2g)
      rw [moment_double]
      exact (shift_order (Nat.mul_ne_zero (by omega) (moment_positive p t ht).ne') htail).mpr hmain
    · have hm := moment_pairs_mod p t hp
      have hodd : Odd (∑ j ∈ range (2*t), p^j*(j+1)) := Nat.odd_iff.mpr (hm.trans (Nat.odd_iff.mp ho))
      rw [order_odd hodd, order_odd ho]

private lemma local_order (p e : ℕ) (hp : Odd p) :
    padicValNat 2 (∑ j ∈ range (e+1), p^j*(j+1)) + 1 =
      padicValNat 2 (e+1) + padicValNat 2 (e+2) := by
  rcases Nat.even_or_odd e with he | ho
  · obtain ⟨u, hu⟩ := he
    let t := u+1
    have ht : 0 < t := by dsimp [t]; omega
    have hdouble : e+2=2*t := by dsimp [t]; omega
    have htail : 2^(padicValNat 2 t+1) ∣ p^(e+1)*(e+2) := by
      have h : 2^(padicValNat 2 t+1) ∣ e+2 := by
        rw [padicValNat_dvd_iff_le (by omega), hdouble, order_two_mul ht]
        omega
      exact dvd_mul_of_dvd_right h _
    have hbig := order_even_moment p t hp ht
    rw [← hdouble, show e+2=e+1+1 by omega, sum_range_succ] at hbig
    have hsmall := (shift_order (moment_positive p (e+1) (by omega)).ne' htail).mp hbig
    rw [hsmall, hdouble, order_two_mul ht, order_odd (show Odd (e+1) from ⟨u,by omega⟩)]
    omega
  · obtain ⟨u, hu⟩ := ho
    have hdouble : e+1=2*(u+1) := by omega
    rw [hdouble, order_even_moment p (u+1) hp (by omega), order_two_mul (by omega),
      order_odd (show Odd (e+2) from ⟨u+1,by omega⟩)]
    omega

private lemma order_prod (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ p ∈ s, f p ≠ 0) :
    padicValNat 2 (∏ p ∈ s, f p) = ∑ p ∈ s, padicValNat 2 (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have h := fun q hq => hf q (mem_insert_of_mem hq)
    rw [prod_insert hps, sum_insert hps, padicValNat.mul (hf p (mem_insert_self _ _))
      (prod_ne_zero_iff.mpr h), ih h]

private lemma moment_function :
    ∃ F : ArithmeticFunction ℕ, F.IsMultiplicative ∧
      ∀ n, F n = ∑ d ∈ n.divisors, d*d.divisors.card := by
  refine ⟨(ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta,
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta, ?_⟩
  intro n
  rw [ArithmeticFunction.mul_zeta_apply]
  simp only [pmul_apply, id_apply, sigma_zero_apply]

private lemma moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u*v).divisors, d*d.divisors.card) =
      (∑ d ∈ u.divisors, d*d.divisors.card)*(∑ d ∈ v.divisors, d*d.divisors.card) := by
  obtain ⟨F,hF,h⟩ := moment_function
  simpa only [h] using hF.map_mul_of_coprime hc

private lemma moment_at_power (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d*d.divisors.card) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp, card_map, card_range]

private lemma moment_nonzero (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, d*d.divisors.card) ≠ 0 := by
  apply Nat.ne_of_gt
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨1, Nat.one_mem_divisors.mpr hn, by simp⟩

private lemma prime_factor_odd {m p : ℕ} (hm : Odd m) (hp : p ∈ m.primeFactors) : Odd p := by
  apply (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two
  rintro rfl
  exact hm.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp)

private lemma order_tau_le_sigma (m : ℕ) (hm : Odd m) :
    padicValNat 2 m.divisors.card ≤ padicValNat 2 (σ 1 m) := by
  rw [Nat.card_divisors hm.pos.ne',
    sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm.pos.ne']
  simp only [mul_one]
  rw [order_prod _ _ (fun p _ => by omega),
    order_prod _ _ (fun p _ => (geom_positive p _ (by omega)).ne')]
  exact sum_le_sum fun p hp => order_geom_ge p _ (prime_factor_odd hm hp) (by omega)

/-- The prime bases disappear from the order of the weighted divisor sum. -/
lemma odd_moment_order (m : ℕ) (hm : Odd m) :
    padicValNat 2 (∑ d ∈ m.divisors, d*d.divisors.card) + m.primeFactors.card =
      padicValNat 2 m.divisors.card + ∑ p ∈ m.primeFactors, padicValNat 2 (m.factorization p+2) := by
  obtain ⟨F,hF,h⟩ := moment_function
  rw [← h, hF.multiplicative_factorization F hm.pos.ne',
    Nat.prod_factorization_eq_prod_primeFactors, Nat.card_divisors hm.pos.ne']
  simp only [h]
  rw [order_prod _ _ (fun p _ => moment_nonzero _ (pow_ne_zero _ (by
      exact (Nat.prime_of_mem_primeFactors ‹p ∈ m.primeFactors›).ne_zero))),
    order_prod _ _ (fun p _ => by omega)]
  have H := sum_congr (s₁ := m.primeFactors) (s₂ := m.primeFactors) rfl
    (fun p hp => local_order p (m.factorization p) (prime_factor_odd hm hp))
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at H
  convert H using 2
  exact sum_congr rfl (fun p hp => congrArg (padicValNat 2)
    (moment_at_power p _ (Nat.prime_of_mem_primeFactors hp)))

private lemma equality_nat (n : ℕ) (hn : n ≠ 0) :
    OeisA245212.a n = (σ 1 n : ℤ) ↔
      (∑ d ∈ n.divisors, d*d.divisors.card) + σ 1 n = 2 * n * n.divisors.card := by
  have hs : (∑ d ∈ n.divisors, d*d.divisors.card) =
      n*n.divisors.card + ∑ d ∈ n.properDivisors, d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors, d*d.divisors.card := by rw [Nat.insert_self_properDivisors hn]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [hs]
  unfold OeisA245212.a
  constructor
  · intro h
    zify
    linarith
  · intro h
    zify at h
    linarith

private lemma two_moment_odd (k : ℕ) :
    Odd (∑ d ∈ (2^k).divisors, d*d.divisors.card) := by
  rw [moment_at_power _ _ Nat.prime_two, Nat.odd_iff]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h : 2 ∣ 2^(k+1)*(k+1+1) := dvd_mul_of_dvd_left (by rw [pow_succ]; exact dvd_mul_left _ _) _
    omega

/-- Every equality, with any exponent at 2, obeys this restriction on the odd
prime exponents. It also applies when the input is odd. -/
lemma exponent_obstruction (k m : ℕ) (hm : Odd m)
    (h : OeisA245212.a (2^k*m) = (σ 1 (2^k*m) : ℤ)) :
    m.primeFactors.card ≤ ∑ p ∈ m.primeFactors, padicValNat 2 (m.factorization p+2) := by
  have hc : (2^k).Coprime m := (Nat.coprime_two_left.mpr hm).pow_left k
  have hn : 2^k*m ≠ 0 := Nat.mul_ne_zero (by positivity) hm.pos.ne'
  have positiveSigma : σ 1 m ≠ 0 := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm.pos.ne']
    simp only [mul_one]
    exact prod_ne_zero_iff.mpr fun p _ => (geom_positive p _ (by omega)).ne'
  have hs : 2^padicValNat 2 m.divisors.card ∣ σ 1 (2^k*m) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hc]
    exact dvd_mul_of_dvd_right ((padicValNat_dvd_iff_le positiveSigma).mpr (order_tau_le_sigma m hm)) _
  have ht : 2^padicValNat 2 m.divisors.card ∣ 2*(2^k*m)*(2^k*m).divisors.card := by
    rw [hc.card_divisors_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right pow_padicValNat_dvd _) _
  rw [← (equality_nat _ hn).mp h] at ht
  have hM := (Nat.dvd_add_iff_left hs).mpr ht
  have hle := (padicValNat_dvd_iff_le (moment_nonzero _ hn)).mp hM
  rw [moment_mul _ _ hc, padicValNat.mul (moment_nonzero _ (by positivity))
    (moment_nonzero _ hm.pos.ne'), order_odd (two_moment_odd k), zero_add] at hle
  have ho := odd_moment_order m hm
  omega

private lemma at_power_product (p e b : ℕ) (hp : p.Prime) (hb : b ≠ 0) (hc : p.Coprime b) :
    OeisA245212.a (p^e*b) = (σ 1 (p^e*b) : ℤ) ↔
      (∑ j ∈ range (e+1), ((j+1)*(∑ d ∈ b.divisors, d*d.divisors.card)+σ 1 b)*p^j) =
        (2*b*(e+1)*b.divisors.card)*p^e := by
  have hc' := hc.pow_left e
  rw [equality_nat _ (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hb),
    moment_mul _ _ hc', moment_at_power _ _ hp, isMultiplicative_sigma.map_mul_of_coprime hc',
    sigma_apply_prime_pow hp, hc'.card_divisors_mul, Nat.divisors_prime_pow hp, card_map, card_range]
  simp only [mul_one]
  have split : (∑ j ∈ range (e+1), ((j+1)*(∑ d ∈ b.divisors, d*d.divisors.card)+σ 1 b)*p^j) =
      (∑ j ∈ range (e+1), p^j*(j+1))*(∑ d ∈ b.divisors, d*d.divisors.card) +
        (∑ j ∈ range (e+1), p^j)*σ 1 b := by
    rw [sum_mul, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [split]
  ring_nf

private lemma cross_weighted (f : ℕ → ℕ) (hf : 0 < f 0) (p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (e : ℕ) :
    (∑ j ∈ range (e+1), f j*q^j)*p^e ≤ (∑ j ∈ range (e+1), f j*p^j)*q^e ∧
    (0 < e → (∑ j ∈ range (e+1), f j*q^j)*p^e < (∑ j ∈ range (e+1), f j*p^j)*q^e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpos : 0 < (∑ j ∈ range (e+1), f j*p^j)*q^e := Nat.mul_pos
      (sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr (by omega), by simpa using hf⟩)
      (pow_pos (by omega) _)
    have hs := lt_of_le_of_lt (Nat.mul_le_mul_right p ih.1) (Nat.mul_lt_mul_of_pos_left hpq hpos)
    have hstrict : (∑ j ∈ range (e+1+1), f j*q^j)*p^(e+1) <
        (∑ j ∈ range (e+1+1), f j*p^j)*q^(e+1) := by
      rw [sum_range_succ (fun j => f j*q^j) (e+1), sum_range_succ (fun j => f j*p^j) (e+1)]
      simp only [pow_succ]
      nlinarith only [hs]
    exact ⟨hstrict.le, fun _ => hstrict⟩

/-- For each cofactor and positive exponent there is at most one prime base
that can produce equality. The normalized equation decreases in the base. -/
lemma unique_prime_base {p q e b : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 0 < e)
    (hb : 0 < b) (hc : p.Coprime b) (hd : q.Coprime b)
    (h₁ : OeisA245212.a (p^e*b) = (σ 1 (p^e*b) : ℤ))
    (h₂ : OeisA245212.a (q^e*b) = (σ 1 (q^e*b) : ℤ)) : p = q := by
  let f (j : ℕ) := (j+1)*(∑ d ∈ b.divisors, d*d.divisors.card)+σ 1 b
  have hf : 0 < f 0 := by
    have h := moment_nonzero b hb.ne'
    dsimp [f]
    omega
  have H₁ := (at_power_product p e b hp hb.ne' hc).mp h₁
  have H₂ := (at_power_product q e b hq hb.ne' hd).mp h₂
  have exchange : (∑ j ∈ range (e+1), f j*q^j)*p^e = (∑ j ∈ range (e+1), f j*p^j)*q^e := by
    dsimp only [f]
    rw [H₁,H₂]
    ring
  rcases lt_trichotomy p q with lt | eq | gt
  · exact False.elim (((cross_weighted f hf p q hp.pos lt e).2 he).ne exchange)
  · exact eq
  · exact False.elim (((cross_weighted f hf q p hq.pos gt e).2 he).ne exchange.symm)

/-- Finite counting form of cofactor uniqueness for primes above a cutoff. -/
lemma large_prime_count (S : Finset ℕ) (X Y e : ℕ) (he : 0 < e)
    (hS : ∀ n ∈ S, ∃ p b : ℕ, p.Prime ∧ Y < p ∧ 0 < b ∧ p.Coprime b ∧
      n = p^e*b ∧ n ≤ X ∧ OeisA245212.a n = (σ 1 n : ℤ)) :
    S.card ≤ X / (Y+1)^e := by
  classical
  choose! p b h using hS
  have target (n : ℕ) (hn : n ∈ S) : b n ∈ Icc 1 (X/(Y+1)^e) := by
    obtain ⟨_,hp,hb,_,hn',hx,_⟩ := h n hn
    refine mem_Icc.mpr ⟨hb,(Nat.le_div_iff_mul_le (pow_pos (by omega) _)).mpr ?_⟩
    calc
      b n*(Y+1)^e ≤ b n*(p n)^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp e)
      _ = n := (Nat.mul_comm _ _).trans hn'.symm
      _ ≤ X := hx
  have inj : Set.InjOn b (S : Set ℕ) := by
    intro n hn v hv hb
    obtain ⟨hnp,_,hbn,hcn,hen,_,h₁⟩ := h n hn
    obtain ⟨hvp,_,_,hcv,hev,_,h₂⟩ := h v hv
    rw [hen] at h₁
    rw [hev, ← hb] at h₂
    rw [← hb] at hcv
    have hp := unique_prime_base hnp hvp he hbn hcn hcv h₁ h₂
    calc
      n = (p n)^e*b n := hen
      _ = (p v)^e*b v := by rw [hp,hb]
      _ = v := hev.symm
  calc
    S.card ≤ (Icc 1 (X/(Y+1)^e)).card := card_le_card_of_injOn b target inj
    _ = _ := by simp

private lemma linear_criterion (p b : ℕ) (hp : p.Prime) (hb : 0 < b) (hc : p.Coprime b) :
    OeisA245212.a (p*b) = (σ 1 (p*b) : ℤ) ↔
      let T := ∑ d ∈ b.divisors, d*d.divisors.card
      let N := T + σ 1 b
      let D := 4*b*b.divisors.card - (2*T + σ 1 b)
      0 < D ∧ N = p*D := by
  have H := at_power_product p 1 b hp hb.ne' hc
  simp only [pow_one, sum_range_succ, sum_range_zero, zero_add, pow_zero, mul_one, one_mul] at H
  rw [H]
  let T := ∑ d ∈ b.divisors, d*d.divisors.card
  let N := T+σ 1 b
  let B := 2*T+σ 1 b
  let A := 4*b*b.divisors.card
  change N+B*p = 2*b*(1+1)*b.divisors.card*p ↔ 0 < A-B ∧ N=p*(A-B)
  have ha : 2*b*(1+1)*b.divisors.card = A := by dsimp [A]; ring
  have hN : 0 < N := by
    have h := moment_nonzero b hb.ne'
    dsimp only [N,T]
    omega
  rw [ha]
  constructor
  · intro h
    have hlt : B < A := by
      by_contra! hge
      have := Nat.mul_le_mul_right p hge
      omega
    refine ⟨by omega, ?_⟩
    rw [Nat.mul_sub, mul_comm p A, mul_comm p B]
    omega
  · rintro ⟨_,h⟩
    rw [Nat.mul_sub, mul_comm p A, mul_comm p B] at h
    have hle : B*p ≤ A*p := Nat.mul_le_mul_right _ (by omega)
    omega

/-- Split all positive equalities at the largest prime. For a fixed positive
exponent, the remaining cofactor determines at most one possible prime. -/
lemma counting_bound (X Y : ℕ) (hY : 0 < Y) :
    ((Icc 1 X).filter (fun n => OeisA245212.a n = (σ 1 n : ℤ))).card ≤
      (Nat.smoothNumbersUpTo X (Y+1)).card + X/Y := by
  classical
  let E := (Icc 1 X).filter (fun n => OeisA245212.a n = (σ 1 n : ℤ))
  let B (i : ℕ) := E.filter (fun n => ∃ p b : ℕ,
    p.Prime ∧ Y < p ∧ 0 < b ∧ p.Coprime b ∧ n = p^(i+1)*b)
  let R := range ((Nat.log (Y+1) X)+1)
  have cover : E ⊆ Nat.smoothNumbersUpTo X (Y+1) ∪ R.biUnion B := by
    intro n hn
    have hn' := mem_filter.mp hn
    obtain ⟨hn0,hnX⟩ := mem_Icc.mp hn'.1
    by_cases smooth : n ∈ Nat.smoothNumbers (Y+1)
    · exact mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨hnX,smooth⟩)
    · rw [Nat.mem_smoothNumbers'] at smooth
      push Not at smooth
      obtain ⟨p,hp,hd,hpY⟩ := smooth
      obtain ⟨e,b,hb,heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
      have hc := hp.coprime_iff_not_dvd.mpr hb
      have hbpos : 0 < b := by
        by_contra! h
        have hz : b = 0 := by omega
        rw [heq,hz,mul_zero] at hn0
        omega
      cases e with
      | zero => simp only [pow_zero,one_mul] at heq; exact (hb (heq ▸ hd)).elim
      | succ i =>
        have hpow : (Y+1)^(i+1) ≤ X := calc
          _ ≤ p^(i+1) := Nat.pow_le_pow_left hpY _
          _ ≤ p^(i+1)*b := Nat.le_mul_of_pos_right _ hbpos
          _ ≤ X := heq ▸ hnX
        have hbound := Nat.le_log_of_pow_le (by omega : 1 < Y+1) hpow
        exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),
          mem_filter.mpr ⟨hn,p,b,hp,hpY,hbpos,hc,heq⟩⟩)
  have bound (i : ℕ) : (B i).card ≤ X/(Y+1)^(i+1) := by
    apply large_prime_count (B i) X Y (i+1) (by omega)
    intro n hn
    obtain ⟨hnE,p,b,hp,hy,hb,hc,eqn⟩ := mem_filter.mp hn
    obtain ⟨hnI,ha⟩ := mem_filter.mp hnE
    exact ⟨p,b,hp,hy,hb,hc,eqn,(mem_Icc.mp hnI).2,ha⟩
  have hsum : (∑ i ∈ R, X/(Y+1)^(i+1)) ≤ X/Y := by
    have H := Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := Y+1) X
    change _ * (∑ i ∈ R, X/(Y+1)^(i+1)) = _ at H
    simp only [Nat.add_sub_cancel] at H
    apply (Nat.le_div_iff_mul_le hY).mpr
    rw [mul_comm]
    omega
  calc
    E.card ≤ (Nat.smoothNumbersUpTo X (Y+1) ∪ R.biUnion B).card := card_le_card cover
    _ ≤ (Nat.smoothNumbersUpTo X (Y+1)).card + (R.biUnion B).card := card_union_le _ _
    _ ≤ (Nat.smoothNumbersUpTo X (Y+1)).card + X/Y := by
      exact Nat.add_le_add_left ((card_biUnion_le.trans
        (sum_le_sum fun i _ => bound i)).trans hsum) _

/-- An effective, integral formulation of density zero, with the threshold
given in the proof. This counts the powers of two along with every exception. -/
lemma density_zero_integral (K : ℕ) : ∃ M : ℕ, ∀ X ≥ M,
    K * ((Icc 1 X).filter (fun n => OeisA245212.a n = (σ 1 n : ℤ))).card ≤ X := by
  let Y := 2*(K+1)
  let C := 2^(Y+1).primesBelow.card
  refine ⟨(Y*C)^2, ?_⟩
  intro X hX
  have hY : 0 < Y := by dsimp [Y]; omega
  have hc := counting_bound X Y hY
  have hs : (Nat.smoothNumbersUpTo X (Y+1)).card ≤ C*X.sqrt :=
    Nat.smoothNumbersUpTo_card_le _ _
  have hroot : Y*C ≤ X.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hX)
  have hsqrt : Y*(C*X.sqrt) ≤ X := calc
    _ = (Y*C)*X.sqrt := by ring
    _ ≤ X.sqrt*X.sqrt := Nat.mul_le_mul_right _ hroot
    _ ≤ X := Nat.sqrt_le X
  have hdiv : Y*(X/Y) ≤ X := by simpa [mul_comm] using Nat.div_mul_le_self X Y
  have hbound := Nat.mul_le_mul_left Y (hc.trans (Nat.add_le_add_right hs _))
  rw [Nat.mul_add] at hbound
  dsimp only [Y] at hbound hsqrt hdiv
  nlinarith only [hbound,hsqrt,hdiv]

/-- The positive equality set for OEIS A245212 has natural density zero. -/
lemma equality_density_zero :
    Filter.Tendsto (fun X : ℕ =>
      (((Icc 1 X).filter (fun n => OeisA245212.a n = (σ 1 n : ℤ))).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε)
  have hK0 : 0 < (K : ℝ) := lt_trans (by positivity : (0:ℝ) < 1/ε) hK
  obtain ⟨M,hM⟩ := density_zero_integral K
  refine ⟨M+1, fun X hX => ?_⟩
  have hx : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have h := hM X (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  refine lt_of_le_of_lt (b := 1/(K:ℝ)) ((div_le_div_iff₀ hx hK0).mpr ?_) ?_
  · rw [one_mul,mul_comm]
    exact_mod_cast h
  · apply (div_lt_iff₀ hK0).mpr
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hK

/-- The odd part has no prime occurring just once. Only exponent patterns
surviving the two-adic test remain. -/
def H1 : Prop :=
  ∀ k m : ℕ, 1 ≤ k → Odd m → 1 < m →
    m.primeFactors.card ≤ (∑ p ∈ m.primeFactors, padicValNat 2 (m.factorization p+2)) →
    (¬ ∃ p b : ℕ, p.Prime ∧ Odd p ∧ p.Coprime b ∧ 2^k*m = p*b) →
    OeisA245212.a (2^k*m) ≠ (σ 1 (2^k*m) : ℤ)

/-- For an even cofactor, the sole possible odd prime of exponent one is an
explicit quotient. This hypothesis rules out exactly its admissible values. -/
def H2 : Prop :=
  ∀ b : ℕ, 0 < b → Even b →
    let T := ∑ d ∈ b.divisors, d*d.divisors.card
    let N := T+σ 1 b
    let D := 4*b*b.divisors.card - (2*T+σ 1 b)
    let p := N/D
    ¬ (0 < D ∧ D ∣ N ∧ p.Prime ∧ Odd p ∧ p.Coprime b)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1.H2 := by
  intro powerful quotient k m hk hm hm1 eqn
  by_cases hasPrime : ∃ p b : ℕ, p.Prime ∧ Odd p ∧ p.Coprime b ∧ 2^k*m = p*b
  · obtain ⟨p,b,hp,ho,hc,hpb⟩ := hasPrime
    have hpos : 0 < 2^k*m := Nat.mul_pos (by positivity) hm.pos
    have hb : 0 < b := by
      by_contra! h
      have hb0 : b=0 := by omega
      rw [hpb,hb0,mul_zero] at hpos
      omega
    have heven : Even (2^k*m) :=
      even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega : k ≠ 0)) _)
    rw [hpb, Nat.even_mul] at heven
    have heb : Even b := heven.resolve_left (Nat.not_even_iff_odd.mpr ho)
    rw [hpb] at eqn
    obtain ⟨hd,hn⟩ := (linear_criterion p b hp hb hc).mp eqn
    have h := quotient b hb heb
    dsimp only at h
    rw [Nat.div_eq_of_eq_mul_left hd hn] at h
    exact h ⟨hd, ⟨p,hn.trans (Nat.mul_comm _ _)⟩, hp,ho,hc⟩
  · exact powerful k m hk hm hm1 (exponent_obstruction k m hm eqn) hasPrime eqn

end OMA.R_OeisA245212_conjecture_R1_H2_R1
