import Mathlib

namespace RobinChampions

abbrev sigma (n : ℕ) := ArithmeticFunction.sigma 1 n
noncomputable def score (s : ℝ) (n : ℕ) : ℝ := (sigma n : ℝ)/(n:ℝ)^s
def IsCA (n : ℕ) := ∃ s : ℝ, 1 < s ∧ 1 < n ∧ ∀ m : ℕ, 1 < m → score s m ≤ score s n
def listed : List ℕ := [2,6,12,60,120,360,2520,5040]

private lemma rational_pow (x : ℝ) (hx : 0 ≤ x) (a b : ℕ) (hb : b≠0) :
    (x^((a:ℝ)/b))^b = x^a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, div_mul_cancel₀, Real.rpow_natCast]
  exact_mod_cast hb

private def weak (a b m n : ℕ) := (sigma m)^b*n^a ≤ (sigma n)^b*m^a
private def strict (a b m n : ℕ) := (sigma m)^b*n^a < (sigma n)^b*m^a

private instance (a b m n) : Decidable (weak a b m n) := inferInstanceAs (Decidable (_ ≤ _))
private instance (a b m n) : Decidable (strict a b m n) := inferInstanceAs (Decidable (_ < _))

private lemma weak_iff {a b m n : ℕ} (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) :
    score ((a:ℝ)/b) m ≤ score ((a:ℝ)/b) n ↔ weak a b m n := by
  unfold score weak
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)]
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) hb.ne',
    mul_pow,mul_pow,rational_pow _ (by positivity) _ _ hb.ne',
    rational_pow _ (by positivity) _ _ hb.ne']
  norm_cast

private lemma strict_lt {a b m n : ℕ} (hb : 0 < b) (hm : 0 < m) (hn : 0 < n)
    (h : strict a b m n) : score ((a:ℝ)/b) m < score ((a:ℝ)/b) n :=
  lt_of_not_ge (fun hnle => h.not_ge ((weak_iff hb hn hm).mp hnle))

private lemma score_add (s t : ℝ) (n : ℕ) (hn : 0 < n) :
    score (s+t) n = score s n/(n:ℝ)^t := by
  rw [score,score,Real.rpow_add (by exact_mod_cast hn)]; ring

private lemma score_nonneg (s : ℝ) (n : ℕ) : 0 ≤ score s n := by
  unfold score; positivity

private lemma shift_upper {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) {s t : ℝ} (hst : s ≤ t) :
    score t j ≤ score s j/(i:ℝ)^(t-s) := by
  have hj := hi.trans_le hij
  conv_lhs => rw [show t=s+(t-s) by ring, score_add _ _ _ hj]
  apply div_le_div_of_nonneg_left (score_nonneg _ _)
    (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hij) (sub_nonneg.mpr hst)

private lemma shift_le {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) {s t : ℝ} (hst : s ≤ t)
    (h : score s j ≤ score s i) : score t j ≤ score t i := by
  apply (shift_upper hi hij hst).trans
  conv_rhs => rw [show t=s+(t-s) by ring, score_add _ _ _ hi]
  exact div_le_div_of_nonneg_right h (by positivity)

private lemma shift_lt {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) {s t : ℝ} (hst : s ≤ t)
    (h : score s j < score s i) : score t j < score t i := by
  apply (shift_upper hi hij hst).trans_lt
  conv_rhs => rw [show t=s+(t-s) by ring, score_add _ _ _ hi]
  exact div_lt_div_of_pos_right h (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)

private structure Winner where
  n : ℕ
  a : ℕ
  b : ℕ
deriving DecidableEq

private structure Cut where
  lo : ℕ
  hi : ℕ
  a : ℕ
  b : ℕ
deriving DecidableEq

private def winners : List Winner :=
  [⟨2,3,2⟩,⟨6,5,4⟩,⟨12,6,5⟩,⟨60,10,9⟩,⟨120,12,11⟩,⟨360,15,14⟩,⟨2520,16,15⟩]

private def cuts : List Cut :=
  [⟨2,6,5,4⟩,⟨6,12,3,2⟩,⟨12,60,10,9⟩,⟨60,120,6,5⟩,
   ⟨120,360,12,11⟩,⟨360,2520,15,14⟩,⟨2520,5040,8,7⟩]

private theorem witnesses : ∀ n ∈ listed, n=5040 ∨
    ∃ w ∈ winners, w.n=n ∧ 1 < n ∧ 0 < w.b ∧ 28*w.b ≤ 27*w.a := by decide +kernel

private theorem bounded_checks : ∀ k : Fin 5041, 1 < k.val →
    (∀ w ∈ winners, weak w.a w.b k.val w.n) ∧
    (k.val ∉ listed → ∃ c ∈ cuts, 1 < c.lo ∧ c.lo < k.val ∧ k.val < c.hi ∧ 0 < c.b ∧
      strict c.a c.b k.val c.lo ∧ strict c.a c.b k.val c.hi) := by
  native_decide

/-- A single published global maximizer at the cutoff suffices to certify this entire prefix. -/
theorem ca_prefix (s₀ : ℝ) (hpos : 1 < s₀) (hcut : s₀ ≤ 1+1/27)
    (hmax : ∀ m : ℕ, 1 < m → score s₀ m ≤ score s₀ 5040)
    (n : ℕ) (hn : n ≤ 5040) : IsCA n ↔ n ∈ listed := by
  constructor
  · rintro ⟨s,_,hn1,maximum⟩
    by_contra absent
    obtain ⟨c,_,hlo,hl,hu,hb,cl,cu⟩ :=
      (bounded_checks ⟨n,by omega⟩ hn1).2 absent
    let t : ℝ := (c.a:ℝ)/c.b
    have hl' : score t n < score t c.lo := strict_lt hb (by omega) (by omega) cl
    have hu' : score t n < score t c.hi := strict_lt hb (by omega) (by omega) cu
    by_cases hts : t ≤ s
    · exact (shift_lt (by omega) hl.le hts hl').not_ge (maximum c.lo hlo)
    · have hwrong := shift_le (i:=n) (j:=c.hi) (by omega) hu.le (lt_of_not_ge hts).le
        (maximum c.hi (by omega))
      exact hu'.not_ge hwrong
  · intro mem
    rcases witnesses n mem with rfl | ⟨w,hw,rfl,hn1,hb,hs⟩
    · exact ⟨s₀,hpos,by decide,hmax⟩
    · let t : ℝ := (w.a:ℝ)/w.b
      have ht : 1+1/27 ≤ t := by
        apply (le_div_iff₀ (by exact_mod_cast hb : 0<(w.b:ℝ))).2
        have := (show (28:ℝ)*w.b ≤ 27*w.a by exact_mod_cast hs)
        linarith
      refine ⟨t,by linarith,hn1,?_⟩
      intro m hm
      by_cases h : m ≤ 5040
      · exact (weak_iff hb (by omega) (by omega)).2
          ((bounded_checks ⟨m,by omega⟩ hm).1 w hw)
      · have ma := shift_le (i:=5040) (j:=m) (by decide) (by omega) (hcut.trans ht) (hmax m hm)
        exact ma.trans <| (weak_iff hb (by decide) (by omega)).2
          ((bounded_checks ⟨5040,by decide⟩ (by decide)).1 w hw)

#print axioms ca_prefix
end RobinChampions
