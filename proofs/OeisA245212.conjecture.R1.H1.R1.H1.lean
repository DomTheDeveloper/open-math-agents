import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1

/-! A uniform totient bound for Krizek’s OEIS A245212. Extends the local estimates in project PR 1048. -/

namespace OeisA245212.TotientGap
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private lemma geom_bound (p c e : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ j ∈ range (e + 1), p ^ j) ≤ (c + 1) * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ]
    simp only [pow_succ p e]
    nlinarith only [ih, Nat.mul_le_mul_right (p^e) hp]

/-- The loss of one in the leading coefficient is important for small exponents. -/
private lemma weighted_bound (p c e : ℕ) (hp : c + 1 ≤ p) :
    c * (∑ j ∈ range (e + 1), p ^ j * (j + 1)) ≤ ((c + 1) * e + c) * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hcoef : (c + 1) * e + c ≤ (e + 1) * p := by
      calc
        _ ≤ (e + 1) * (c + 1) := by nlinarith
        _ ≤ (e + 1) * p := Nat.mul_le_mul_left _ hp
    rw [sum_range_succ]
    simp only [pow_succ p e]
    nlinarith only [ih, Nat.mul_le_mul_right (p^e) hcoef]

private lemma moment_function :
    ∃ F : ArithmeticFunction ℕ, F.IsMultiplicative ∧
      ∀ n, F n = ∑ d ∈ n.divisors, d*d.divisors.card := by
  refine ⟨(ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta,
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta, ?_⟩
  intro n
  rw [ArithmeticFunction.mul_zeta_apply]
  simp only [pmul_apply, id_apply, sigma_zero_apply]

private lemma moment_at_power (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d*d.divisors.card) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp, card_map, card_range]



private lemma product_step (b c s A B C F : ℕ) (hc : s*b ≤ c)
    (hAB : B ≤ A) (hw : C+A ≤ F+B) (hF : s*A ≤ F) :
    c*C + s*((b+1)*A) ≤ (c+1)*F + s*(b*B) := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hc
  nlinarith only [Nat.mul_le_mul_left (s*b+v) hw, Nat.mul_le_mul_left v hAB, hF]

private lemma product_weak (s : Finset ℕ) (b c : ℕ → ℕ)
    (h : ∀ i ∈ s, 2*(b i+1) ≤ c i+1) :
    (∏ i ∈ s, c i) + (∏ i ∈ s, (b i+1)) ≤
      (∏ i ∈ s, (c i+1)) + (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have ht := fun j (hj : j ∈ t) => h j (mem_insert_of_mem hj)
    have hi := h i (mem_insert_self _ _)
    have hAB : (∏ j ∈ t, b j) ≤ ∏ j ∈ t, (b j+1) := prod_le_prod' fun _ _ => by omega
    have hF : (∏ j ∈ t, (b j+1)) ≤ ∏ j ∈ t, (c j+1) :=
      prod_le_prod' fun j hj => by have := ht j hj; omega
    simpa only [prod_insert hit, one_mul] using
      product_step (b i) (c i) 1 _ _ _ _ (by omega) hAB (ih ht) (by simpa using hF)

private lemma product_gap (s : Finset ℕ) (b c : ℕ → ℕ) (hs : 1 < s.card)
    (h : ∀ i ∈ s, 2*(b i+1) ≤ c i+1) :
    (∏ i ∈ s, c i) + 2*(∏ i ∈ s, (b i+1)) ≤
      (∏ i ∈ s, (c i+1)) + 2*(∏ i ∈ s, b i) := by
  classical
  obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < s.card)
  let t := s.erase i
  have hit : i ∉ t := notMem_erase _ _
  have heq : insert i t = s := insert_erase hi
  have ht := fun j (hj : j ∈ t) => h j (mem_of_mem_erase hj)
  have hAB : (∏ j ∈ t, b j) ≤ ∏ j ∈ t, (b j+1) := prod_le_prod' fun _ _ => by omega
  have hF : 2*(∏ j ∈ t, (b j+1)) ≤ ∏ j ∈ t, (c j+1) := by
    have hcard : 0 < t.card := by dsimp [t]; rw [card_erase_of_mem hi]; omega
    have htwo : 2 ≤ 2^t.card :=
      calc 2 = 2^(1:ℕ) := by decide
           _ ≤ 2^t.card := Nat.pow_le_pow_right (by decide) hcard
    calc
      _ ≤ 2^t.card * (∏ j ∈ t, (b j+1)) := Nat.mul_le_mul_right _ htwo
      _ = ∏ j ∈ t, (2*(b j+1)) := by simp [prod_mul_distrib]
      _ ≤ _ := prod_le_prod' ht
  have hstep := product_step (b i) (c i) 2 _ _ _ _
    (by have := h i hi; omega) hAB (product_weak t b c ht) hF
  rw [← heq]
  simpa only [prod_insert hit] using hstep

private lemma moment_product (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, d*d.divisors.card) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p+1), p^j*(j+1) := by
  obtain ⟨F,hF,h⟩ := moment_function
  rw [← h, hF.multiplicative_factorization F hn, Nat.prod_factorization_eq_prod_primeFactors]
  exact prod_congr rfl fun p hp => (h _).trans (moment_at_power p _ (Nat.prime_of_mem_primeFactors hp))

private lemma sum_bound (n : ℕ) (hn : n ≠ 0) (hS : 1 < n.primeFactors.card) :
    n.totient * ((∑ d ∈ n.divisors, d*d.divisors.card) + σ 1 n) + n*n ≤
      n*n*n.divisors.card + 2*n*n.totient := by
  classical
  let S := n.primeFactors
  let E := fun p => n.factorization p + 1
  let b := fun p : ℕ => p-1
  let c := fun p : ℕ => p*(n.factorization p)+(p-1)
  let A := ∏ p ∈ S, p
  let B := ∏ p ∈ S, b p
  let C := ∏ p ∈ S, c p
  let M := ∑ d ∈ n.divisors, d*d.divisors.card
  have hp0 (p) (hp : p ∈ S) := (Nat.prime_of_mem_primeFactors hp).pos
  have hb (p) (hp : p ∈ S) : b p+1 = p := by dsimp [b]; have := hp0 p hp; omega
  have hc (p) (hp : p ∈ S) : c p+1 = p*E p := by
    dsimp [c,E]
    rw [Nat.mul_add, mul_one]
    have := hp0 p hp
    omega
  have hstrong := product_gap S b c hS (fun p hp => by
    rw [hb p hp, hc p hp, mul_comm p]
    have he : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.mul_le_mul_right p (by dsimp [E]; omega))
  have hA : (∏ p ∈ S, (b p+1)) = A := prod_congr rfl hb
  have hF : (∏ p ∈ S, (c p+1)) = A*n.divisors.card := by
    rw [prod_congr rfl hc, prod_mul_distrib, Nat.card_divisors hn]
  rw [hA,hF] at hstrong
  change C + 2*A ≤ A*n.divisors.card + 2*B at hstrong
  have hnprod : (∏ p ∈ S, p^n.factorization p) = n :=
    (Nat.prod_primeFactors_pow_factorization hn).symm
  have hmoment : B*M ≤ C*n := by
    have hh := prod_le_prod' (s := S) (fun p hp => weighted_bound p (b p) (n.factorization p) (hb p hp).le)
    simp only [prod_mul_distrib] at hh
    have hcoeff : (∏ p ∈ S, ((b p+1)*n.factorization p+b p)) = C :=
      prod_congr rfl fun p hp => by rw [hb p hp]
    rw [hcoeff,hnprod] at hh
    dsimp only [M]
    rw [moment_product n hn]
    exact hh
  have hsum : B*(σ 1 n) ≤ A*n := by
    have hh := prod_le_prod' (s := S) (fun p hp => geom_bound p (b p) (n.factorization p) (hb p hp).le)
    simp only [prod_mul_distrib] at hh
    rw [hA,hnprod] at hh
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
    simpa only [mul_one] using hh
  have blend : B*(M+σ 1 n)+n*A ≤ n*(A*n.divisors.card+2*B) := by
    nlinarith only [hmoment,hsum,Nat.mul_le_mul_left n hstrong]
  have hphi : n.totient*A = n*B := Nat.totient_mul_prod_primeFactors n
  have ha : 0 < A := prod_pos fun p hp => hp0 p hp
  refine Nat.le_of_mul_le_mul_left ?_ ha
  change A*(n.totient*(M + σ 1 n)+n*n) ≤ A*(n*n*n.divisors.card+2*n*n.totient)
  calc
    _ = (n.totient*A)*(M+σ 1 n)+n*(n*A) := by ring
    _ = n*(B*(M+σ 1 n)+n*A) := by rw [hphi]; ring
    _ ≤ n*(n*(A*n.divisors.card+2*B)) := Nat.mul_le_mul_left n blend
    _ = A*(n*n*n.divisors.card)+2*n*(n*B) := by ring
    _ = _ := by rw [←hphi]; ring

/-- A uniform signed gap for every integer with at least two distinct prime factors. -/
theorem totient_gap (n : ℕ) (hn : 1 < n) (h : 1 < n.primeFactors.card) :
    (n : ℤ) * (2 * (n.totient : ℤ) - n) * ((n.divisors.card : ℤ) - 1) ≤
      (n.totient : ℤ) * (OeisA245212.a n - (σ 1 n : ℤ)) := by
  have hn0 : n ≠ 0 := by omega
  have hs : (∑ d ∈ n.divisors, d*d.divisors.card) =
      n*n.divisors.card + ∑ d ∈ n.properDivisors, d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors, d*d.divisors.card := by rw [Nat.insert_self_properDivisors hn0]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  have H := sum_bound n hn0 h
  rw [hs] at H
  zify at H
  unfold OeisA245212.a
  linarith only [H]

end OeisA245212.TotientGap

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1.H1 := by
  intro n hn ho hp hphi _ heq
  have hS := Finset.one_lt_card_iff_nontrivial.mpr ((Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hp)
  have H := OeisA245212.TotientGap.totient_gap n hn hS
  have hstrict : n < 2*n.totient := lt_of_le_of_ne hphi (fun he => ho.not_two_dvd_nat ⟨_,he⟩)
  have ht : 1 < n.divisors.card := Finset.one_lt_card_iff_nontrivial.mpr
    ⟨1,Nat.one_mem_divisors.mpr (by omega),n,n.mem_divisors_self (by omega),by omega⟩
  rw [heq, sub_self, mul_zero] at H
  have hpos : (0 : ℤ) < (n : ℤ)*(2*(n.totient:ℤ)-n)*((n.divisors.card:ℤ)-1) := by
    apply mul_pos (mul_pos (by exact_mod_cast (show 0<n by omega)) (by omega)) (by omega)
  exact (not_lt_of_ge H) hpos
