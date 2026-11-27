import FormalConjectures.GreensOpenProblems.«25»

-- Problem: Green's Open Problem 25 — upper ess89
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/25.lean:108 (declaration Green25.green_25.variants.upper_ess89)
-- Credit: @DomTheDeveloper (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Original proof (written for this submission, not adapted from an existing formalisation).

Take `k N = ⌈16 N / log N⌉`.  The witnesses are `N_r = m_0 ⋯ m_{r-1}` with `m_i = 2 ^ 2 ^ (i + 3) + 1`
(Fermat numbers, pairwise coprime and odd).  Label `x ∈ [1, N_r]` by its residues modulo each `m_i`
taken up to sign.  Two distinct numbers with the same label have the same residue up to sign for
every `i`; if all the signs were `+` they would be congruent modulo `N_r`, hence equal.  So some
`m_i` divides their sum.  All restricted sums inside one label class therefore lie in
`⋃ i, {t ≤ 2 N_r : m_i ∣ t}`, which has at most `∑ i, 2 N_r / m_i ≤ N_r / 64` elements.
There are at most `∏ (m_i + 1) / 2 ≤ 2 N_r / 2 ^ r ≤ 16 N_r / log N_r ≤ k N_r` classes, and classes can
be split one element at a time until there are exactly `k N_r` of them (this only removes
restricted sums).  Hence `Property25 (k N_r) N_r` fails for every `r ≥ 1`.
-/

/-- The moduli: the Fermat numbers `F₃, F₄, …`. -/
def OMA.m (i : ℕ) : ℕ := Nat.fermatNumber (i + 3)

/-- `N_r = m₀ ⋯ m_{r-1}`. -/
def OMA.Nr (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, OMA.m i

/-- The label of `x`: its residue modulo each `m i`, up to sign. -/
def OMA.lab (r x : ℕ) : Fin r → ℕ :=
  fun i => min (x % OMA.m i) (OMA.m i - x % OMA.m i)

theorem OMA.m_eq (i : ℕ) : OMA.m i = 2 ^ 2 ^ (i + 3) + 1 := rfl

theorem OMA.m_ge (i : ℕ) : 2 ^ (i + 8) ≤ OMA.m i := by
  rw [OMA.m_eq]
  have h1 : i < 2 ^ i := Nat.lt_two_pow_self
  have h2 : 2 ^ (i + 3) = 8 * 2 ^ i := by ring
  have h3 : i + 8 ≤ 2 ^ (i + 3) := by omega
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h3) (Nat.le_succ _)

theorem OMA.m_two_le (i : ℕ) : 2 ≤ OMA.m i := by
  have h1 : 2 ^ 1 ≤ 2 ^ (i + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := OMA.m_ge i
  have h3 : (2 : ℕ) ^ 1 = 2 := by norm_num
  exact le_trans (h3 ▸ h1) h2

theorem OMA.m_pos (i : ℕ) : 0 < OMA.m i :=
  lt_of_lt_of_le (by norm_num) (OMA.m_two_le i)

theorem OMA.m_odd (i : ℕ) : ∃ t, OMA.m i = 2 * t + 1 := Nat.odd_fermatNumber (i + 3)

theorem OMA.Nr_zero : OMA.Nr 0 = 1 := by
  simp [OMA.Nr]

theorem OMA.Nr_succ (r : ℕ) : OMA.Nr (r + 1) = OMA.Nr r * OMA.m r := by
  unfold OMA.Nr
  exact Finset.prod_range_succ _ _

theorem OMA.Nr_ge (r : ℕ) : r + 1 ≤ OMA.Nr r := by
  induction r with
  | zero => simp [OMA.Nr_zero]
  | succ r ih =>
    rw [OMA.Nr_succ]
    have h2 := OMA.m_two_le r
    calc r + 1 + 1 ≤ OMA.Nr r * 2 := by omega
      _ ≤ OMA.Nr r * OMA.m r := Nat.mul_le_mul_left _ h2

theorem OMA.Nr_lt (r : ℕ) : OMA.Nr r + 2 ≤ 2 ^ 2 ^ (r + 3) := by
  induction r with
  | zero => simp [OMA.Nr_zero]
  | succ r ih =>
    have e0 : 2 ^ (r + 1 + 3) = 2 ^ (r + 3) + 2 ^ (r + 3) := by ring
    have e : 2 ^ 2 ^ (r + 1 + 3) = 2 ^ 2 ^ (r + 3) * 2 ^ 2 ^ (r + 3) := by rw [e0, pow_add]
    rw [OMA.Nr_succ, OMA.m_eq, e]
    generalize 2 ^ 2 ^ (r + 3) = Q at ih ⊢
    generalize OMA.Nr r = B at ih ⊢
    nlinarith [Nat.mul_le_mul_right (Q + 1) ih, Nat.zero_le Q]

theorem OMA.Nr_coprime (r : ℕ) : Nat.Coprime (OMA.Nr r) (OMA.m r) := by
  unfold OMA.Nr
  rw [Nat.coprime_prod_left_iff]
  intro i hi
  have hi' : i < r := Finset.mem_range.mp hi
  show Nat.Coprime (Nat.fermatNumber (i + 3)) (Nat.fermatNumber (r + 3))
  exact Nat.coprime_fermatNumber_fermatNumber (by omega)

theorem OMA.Nr_dvd (d : ℕ) (r : ℕ) (h : ∀ i, i < r → OMA.m i ∣ d) : OMA.Nr r ∣ d := by
  induction r with
  | zero => rw [OMA.Nr_zero]; exact one_dvd d
  | succ r ih =>
    rw [OMA.Nr_succ]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (OMA.Nr_coprime r)
      (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h r (Nat.lt_succ_self r))

theorem OMA.min_eq (M a b : ℕ) (ha : a < M) (hb : b < M)
    (h : min a (M - a) = min b (M - b)) : a = b ∨ a + b = M := by
  omega

/-- Two distinct numbers of `[1, N_r]` with the same label have a sum divisible by some `m i`. -/
theorem OMA.key (r x y : ℕ) (hx : x ∈ Finset.Icc 1 (OMA.Nr r)) (hy : y ∈ Finset.Icc 1 (OMA.Nr r))
    (hxy : x ≠ y) (hlab : OMA.lab r x = OMA.lab r y) : ∃ i, i < r ∧ OMA.m i ∣ x + y := by
  by_contra hcon
  have hmod : ∀ i, i < r → x % OMA.m i = y % OMA.m i := by
    intro i hi
    have h1 : min (x % OMA.m i) (OMA.m i - x % OMA.m i)
        = min (y % OMA.m i) (OMA.m i - y % OMA.m i) := congrFun hlab ⟨i, hi⟩
    rcases OMA.min_eq _ _ _ (Nat.mod_lt x (OMA.m_pos i)) (Nat.mod_lt y (OMA.m_pos i)) h1 with h | h
    · exact h
    · exfalso
      refine hcon ⟨i, hi, Nat.dvd_of_mod_eq_zero ?_⟩
      rw [Nat.add_mod, h, Nat.mod_self]
  have hdvd : ∀ u v : ℕ, v < u → (∀ i, i < r → u % OMA.m i = v % OMA.m i) →
      OMA.Nr r ∣ u - v := by
    intro u v hvu h
    exact OMA.Nr_dvd (u - v) r fun i hi => (Nat.modEq_iff_dvd' hvu.le).mp (h i hi).symm
  rw [Finset.mem_Icc] at hx hy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have h1 := Nat.le_of_dvd (by omega) (hdvd y x hlt fun i hi => (hmod i hi).symm)
    omega
  · have h1 := Nat.le_of_dvd (by omega) (hdvd x y hgt hmod)
    omega

theorem OMA.lab_mem (r x : ℕ) :
    OMA.lab r x ∈ Fintype.piFinset (fun i : Fin r => Finset.range ((OMA.m i + 1) / 2)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_range]
  obtain ⟨t, ht⟩ := OMA.m_odd i
  have hlt : x % OMA.m i < OMA.m i := Nat.mod_lt _ (OMA.m_pos i)
  show min (x % OMA.m i) (OMA.m i - x % OMA.m i) < (OMA.m i + 1) / 2
  omega

/-- The number of labels is at most `∏ (m i + 1) / 2`. -/
theorem OMA.card_lab (r : ℕ) (s : Finset ℕ) :
    (s.image (fun x => (OMA.lab r x, (0 : ℕ)))).card
      ≤ ∏ i ∈ Finset.range r, ((OMA.m i + 1) / 2) := by
  have hsub : s.image (fun x => (OMA.lab r x, (0 : ℕ))) ⊆
      (Fintype.piFinset (fun i : Fin r => Finset.range ((OMA.m i + 1) / 2))) ×ˢ
        ({0} : Finset ℕ) := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨OMA.lab_mem r x, Finset.mem_singleton_self 0⟩
  have hcard : ((Fintype.piFinset (fun i : Fin r => Finset.range ((OMA.m i + 1) / 2))) ×ˢ
      ({0} : Finset ℕ)).card = ∏ i ∈ Finset.range r, ((OMA.m i + 1) / 2) := by
    rw [Finset.card_product, Fintype.card_piFinset, Finset.card_singleton, mul_one]
    simp only [Finset.card_range]
    exact Fin.prod_univ_eq_prod_range (fun i => (OMA.m i + 1) / 2) r
  exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)

theorem OMA.arith_step (p C B M c : ℕ) (ih : 2 * p * (p * C) + B ≤ 4 * p * B)
    (hm : 8 * p ≤ M + 2) (hodd : 2 * c = M + 1) :
    4 * p * (2 * p * (C * c)) + B * M ≤ 8 * p * (B * M) := by
  have key : 4 * p * (2 * p * (C * c)) = (2 * p * (p * C)) * (2 * (M + 1)) := by
    rw [← hodd]; ring
  rw [key]
  nlinarith [Nat.mul_le_mul_right (2 * (M + 1)) ih, Nat.mul_le_mul_left B hm]

/-- `2 ^ r * ∏ (m i + 1) / 2 ≤ (2 - 2 ^ (-(r + 1))) * N_r`, cleared of denominators. -/
theorem OMA.count_bound (r : ℕ) :
    2 ^ (r + 1) * (2 ^ r * ∏ i ∈ Finset.range r, ((OMA.m i + 1) / 2)) + OMA.Nr r
      ≤ 2 ^ (r + 2) * OMA.Nr r := by
  induction r with
  | zero => simp [OMA.Nr_zero]
  | succ r ih =>
    obtain ⟨t, ht⟩ := OMA.m_odd r
    have hodd : 2 * ((OMA.m r + 1) / 2) = OMA.m r + 1 := by omega
    have hm : 8 * 2 ^ r ≤ OMA.m r + 2 := by
      have h1 := OMA.m_ge r
      have h2 : 2 ^ (r + 8) = 256 * 2 ^ r := by ring
      omega
    have e1 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    have e2 : 2 ^ (r + 2) = 4 * 2 ^ r := by ring
    have e3 : 2 ^ (r + 1 + 1) = 4 * 2 ^ r := by ring
    have e4 : 2 ^ (r + 1 + 2) = 8 * 2 ^ r := by ring
    rw [e1, e2] at ih
    rw [Finset.prod_range_succ, OMA.Nr_succ, e3, e1, e4]
    exact OMA.arith_step (2 ^ r) _ (OMA.Nr r) (OMA.m r) _ ih hm hodd

/-- `∑_{i<r} ⌊2N / m i⌋ ≤ (1 - 2 ^ (-r)) * N / 64`, cleared of denominators. -/
theorem OMA.sum_bound (N r : ℕ) :
    2 ^ (r + 6) * (∑ i ∈ Finset.range r, 2 * N / OMA.m i) + N ≤ 2 ^ r * N := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hq : 2 ^ (r + 7) * (2 * N / OMA.m r) ≤ N := by
      have h1 : 2 ^ (r + 8) ≤ OMA.m r := OMA.m_ge r
      have h2 : OMA.m r * (2 * N / OMA.m r) ≤ 2 * N := Nat.mul_div_le _ _
      have h3 : 2 ^ (r + 8) * (2 * N / OMA.m r) ≤ 2 * N :=
        le_trans (Nat.mul_le_mul_right _ h1) h2
      have e : 2 ^ (r + 8) = 2 * 2 ^ (r + 7) := by ring
      rw [e, mul_assoc] at h3
      exact Nat.le_of_mul_le_mul_left h3 (by norm_num)
    have e1 : 2 ^ (r + 6) = 64 * 2 ^ r := by ring
    have e2 : 2 ^ (r + 7) = 128 * 2 ^ r := by ring
    have e3 : 2 ^ (r + 1 + 6) = 128 * 2 ^ r := by ring
    have e4 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [e1] at ih
    rw [e2] at hq
    rw [Finset.sum_range_succ, e3, e4]
    generalize (∑ i ∈ Finset.range r, 2 * N / OMA.m i) = S at ih ⊢
    generalize 2 * N / OMA.m r = q at hq ⊢
    generalize 2 ^ r = p at ih hq ⊢
    nlinarith [ih, hq]

/-- A labelling with few values can be refined, one element at a time, to one with exactly
`d` more values. -/
theorem OMA.refine_labels {L : Type} [DecidableEq L] [Infinite L] (s : Finset ℕ) (d : ℕ) :
    ∀ g : ℕ → L, (s.image g).card + d ≤ s.card →
      ∃ g' : ℕ → L, (s.image g').card = (s.image g).card + d ∧
        ∀ a ∈ s, ∀ b ∈ s, g' a = g' b → g a = g b := by
  induction d with
  | zero => exact fun g _ => ⟨g, rfl, fun _ _ _ _ h => h⟩
  | succ d ih =>
    intro g hg
    obtain ⟨g1, hcard, href⟩ := ih g (by omega)
    obtain ⟨x, hx, y, hy, hxy, hgxy⟩ :=
      Finset.exists_ne_map_eq_of_card_image_lt (show (s.image g1).card < s.card by omega)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (s.image g1)
    have himg : s.image (Function.update g1 x c) = insert c (s.image g1) := by
      ext l
      rw [Finset.mem_image, Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, hal⟩
        by_cases hax : a = x
        · left
          rw [← hal, hax, Function.update_self]
        · right
          exact ⟨a, ha, by rw [← hal, Function.update_of_ne hax]⟩
      · rintro (hlc | ⟨a, ha, hal⟩)
        · exact ⟨x, hx, by rw [hlc, Function.update_self]⟩
        · by_cases hax : a = x
          · refine ⟨y, hy, ?_⟩
            rw [Function.update_of_ne (Ne.symm hxy), ← hal, hax, hgxy]
          · exact ⟨a, ha, by rw [← hal, Function.update_of_ne hax]⟩
    refine ⟨Function.update g1 x c, ?_, ?_⟩
    · rw [himg, Finset.card_insert_of_notMem hc, hcard]
      omega
    · intro a ha b hb hab
      apply href a ha b hb
      by_cases hax : a = x
      · by_cases hbx : b = x
        · rw [hax, hbx]
        · exfalso
          rw [hax, Function.update_self, Function.update_of_ne hbx] at hab
          exact hc (by rw [hab]; exact Finset.mem_image_of_mem g1 hb)
      · by_cases hbx : b = x
        · exfalso
          rw [hbx, Function.update_self, Function.update_of_ne hax] at hab
          exact hc (by rw [← hab]; exact Finset.mem_image_of_mem g1 ha)
        · rwa [Function.update_of_ne hax, Function.update_of_ne hbx] at hab

/-- The fibres of a labelling form a finpartition. -/
theorem OMA.exists_partition {L : Type} [DecidableEq L] (s : Finset ℕ) (g : ℕ → L) :
    ∃ P : Finpartition s, P.parts.card = (s.image g).card ∧
      ∀ p ∈ P.parts, ∀ a ∈ p, ∀ b ∈ p, g a = g b := by
  have hF : ∀ a ∈ s, a ∈ s.filter (fun b => g b = g a) :=
    fun a ha => Finset.mem_filter.mpr ⟨ha, rfl⟩
  refine ⟨⟨(s.image g).image (fun c => s.filter (fun b => g b = c)), ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro p hp q hq hpq
    obtain ⟨c, _, hcp⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    obtain ⟨c', _, hcq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
    show Disjoint p q
    rw [Finset.disjoint_left]
    intro a ha ha'
    apply hpq
    rw [← hcp] at ha ⊢
    rw [← hcq] at ha' ⊢
    have h1 : g a = c := (Finset.mem_filter.mp ha).2
    have h2 : g a = c' := (Finset.mem_filter.mp ha').2
    rw [← h1, ← h2]
  · ext a
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨p, hp, ha⟩
      obtain ⟨c, _, hcp⟩ := Finset.mem_image.mp hp
      rw [← hcp] at ha
      exact (Finset.mem_filter.mp ha).1
    · intro ha
      exact ⟨s.filter (fun b => g b = g a),
        Finset.mem_image.mpr ⟨g a, Finset.mem_image_of_mem g ha, rfl⟩, hF a ha⟩
  · intro h
    obtain ⟨c, hc, hF0⟩ := Finset.mem_image.mp h
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
    have h1 := hF a ha
    rw [hac, hF0] at h1
    exact Finset.notMem_empty a h1
  · refine Finset.card_image_of_injOn ?_
    intro c hc c' _ h
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
    have h1 := hF a ha
    have h2 : s.filter (fun b => g b = c) = s.filter (fun b => g b = c') := h
    rw [hac, h2] at h1
    rw [← hac]
    exact (Finset.mem_filter.mp h1).2
  · intro p hp a ha b hb
    obtain ⟨c, _, hcp⟩ := Finset.mem_image.mp hp
    rw [← hcp] at ha hb
    rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]

/-- The real-number comparison: at `N = N_r` the number of labels is at most `k N`. -/
theorem OMA.real_step (r C N : ℕ) (hN2 : 2 ≤ N)
    (hA : 2 ^ (r + 1) * (2 ^ r * C) + N ≤ 2 ^ (r + 2) * N) (hB : N + 2 ≤ 2 ^ 2 ^ (r + 3)) :
    C ≤ Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog : Real.log (N : ℝ) ≤ (2 : ℝ) ^ (r + 3) := by
    have h1 : (N : ℝ) ≤ (2 : ℝ) ^ 2 ^ (r + 3) := by
      exact_mod_cast (show N ≤ 2 ^ 2 ^ (r + 3) by omega)
    have h2 : Real.log (N : ℝ) ≤ Real.log ((2 : ℝ) ^ 2 ^ (r + 3)) := Real.log_le_log hNpos h1
    rw [Real.log_pow] at h2
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have h4 : (0 : ℝ) ≤ ((2 ^ (r + 3) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h5 : ((2 ^ (r + 3) : ℕ) : ℝ) = (2 : ℝ) ^ (r + 3) := by norm_num
    calc Real.log (N : ℝ) ≤ ((2 ^ (r + 3) : ℕ) : ℝ) * Real.log 2 := h2
      _ ≤ ((2 ^ (r + 3) : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 h4
      _ = (2 : ℝ) ^ (r + 3) := by rw [mul_one, h5]
  have h2 : 2 ^ r * C ≤ 2 * N := by
    have e : 2 ^ (r + 2) * N = 2 ^ (r + 1) * (2 * N) := by ring
    have h1 : 2 ^ (r + 1) * (2 ^ r * C) ≤ 2 ^ (r + 1) * (2 * N) := by
      rw [← e]
      exact le_trans (Nat.le_add_right _ _) hA
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 : (2 : ℝ) ^ r * (C : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h2
  have hreal : (C : ℝ) ≤ 16 * (N : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hlogpos]
    have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
    have h5 : (C : ℝ) * Real.log (N : ℝ) ≤ (C : ℝ) * (2 : ℝ) ^ (r + 3) :=
      mul_le_mul_of_nonneg_left hlog hC0
    have h6 : (C : ℝ) * (2 : ℝ) ^ (r + 3) = 8 * ((2 : ℝ) ^ r * (C : ℝ)) := by ring
    linarith
  exact Nat.cast_le.mp (le_trans hreal (Nat.le_ceil _))

theorem OMA.count_le_k (r : ℕ) (hN2 : 2 ≤ OMA.Nr r) :
    ∏ i ∈ Finset.range r, ((OMA.m i + 1) / 2)
      ≤ Nat.ceil (16 * (OMA.Nr r : ℝ) / Real.log (OMA.Nr r : ℝ)) :=
  OMA.real_step r _ _ hN2 (OMA.count_bound r) (OMA.Nr_lt r)

/-- The partition into (refined) label classes contradicts `Property25` at `N = N_r`. -/
theorem OMA.no_property (r k : ℕ)
    (hCk : ∏ i ∈ Finset.range r, ((OMA.m i + 1) / 2) ≤ k) (hkN : k ≤ OMA.Nr r)
    (hall : ∀ P : Finpartition (Finset.Icc 1 (OMA.Nr r)), P.parts.card = k →
      10 * (P.parts.biUnion Finset.restrictedSumset).card ≥ OMA.Nr r) : False := by
  have hN1 : 1 ≤ OMA.Nr r := le_trans (Nat.le_add_left 1 r) (OMA.Nr_ge r)
  have hcard := OMA.card_lab r (Finset.Icc 1 (OMA.Nr r))
  have hsN : (Finset.Icc 1 (OMA.Nr r)).card = OMA.Nr r := by simp
  obtain ⟨g, hgcard, hgref⟩ := OMA.refine_labels (Finset.Icc 1 (OMA.Nr r))
    (k - ((Finset.Icc 1 (OMA.Nr r)).image (fun x => (OMA.lab r x, (0 : ℕ)))).card)
    (fun x => (OMA.lab r x, (0 : ℕ))) (by omega)
  obtain ⟨P, hPcard, hPconst⟩ := OMA.exists_partition (Finset.Icc 1 (OMA.Nr r)) g
  have h10 := hall P (by rw [hPcard, hgcard]; omega)
  have hsub : P.parts.biUnion Finset.restrictedSumset ⊆
      (Finset.range r).biUnion
        (fun i => (Finset.Ioc 0 (2 * OMA.Nr r)).filter (fun t => OMA.m i ∣ t)) := by
    intro t ht
    obtain ⟨p, hp, htp⟩ := Finset.mem_biUnion.mp ht
    unfold Finset.restrictedSumset at htp
    obtain ⟨⟨a, b⟩, hab, habt⟩ := Finset.mem_image.mp htp
    obtain ⟨ha, hb, hne⟩ : a ∈ p ∧ b ∈ p ∧ a ≠ b := Finset.mem_offDiag.mp hab
    have habt' : a + b = t := habt
    have ha' : a ∈ Finset.Icc 1 (OMA.Nr r) := P.le hp ha
    have hb' : b ∈ Finset.Icc 1 (OMA.Nr r) := P.le hp hb
    have hlab : OMA.lab r a = OMA.lab r b :=
      congrArg Prod.fst (hgref a ha' b hb' (hPconst p hp a ha b hb))
    obtain ⟨i, hi, hdvd⟩ := OMA.key r a b ha' hb' hne hlab
    rw [Finset.mem_Icc] at ha' hb'
    rw [← habt']
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hdvd⟩⟩
  have hU : ((Finset.range r).biUnion
      (fun i => (Finset.Ioc 0 (2 * OMA.Nr r)).filter (fun t => OMA.m i ∣ t))).card
      ≤ ∑ i ∈ Finset.range r, 2 * OMA.Nr r / OMA.m i := by
    refine le_trans Finset.card_biUnion_le (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => Nat.Ioc_filter_dvd_card_eq_div _ _
  have h64 : 64 * (∑ i ∈ Finset.range r, 2 * OMA.Nr r / OMA.m i) ≤ OMA.Nr r := by
    have hS := OMA.sum_bound (OMA.Nr r) r
    have e : 2 ^ (r + 6) = 2 ^ r * 64 := by ring
    rw [e, mul_assoc] at hS
    exact Nat.le_of_mul_le_mul_left (le_trans (Nat.le_add_right _ _) hS) (by positivity)
  have hcc := Finset.card_le_card hsub
  omega

theorem OMA.k_bounds (N : ℕ) (hlog : 16 ≤ Real.log (N : ℝ)) :
    (1 ≤ Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) ∧
      Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) ≤ N) ∧
    (N : ℝ) / Real.log (N : ℝ) ≤ ((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ) ∧
    ((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ) ≤ 17 * ((N : ℝ) / Real.log (N : ℝ)) ∧
    0 ≤ (N : ℝ) / Real.log (N : ℝ) := by
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h, Nat.cast_zero, Real.log_zero] at hlog
      norm_num at hlog
    · exact h
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hle : Real.log (N : ℝ) ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hq1 : 1 ≤ (N : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hlogpos]
    linarith
  have hx : 16 * (N : ℝ) / Real.log (N : ℝ) = 16 * ((N : ℝ) / Real.log (N : ℝ)) := by ring
  have hxpos : 0 < 16 * (N : ℝ) / Real.log (N : ℝ) := by
    rw [hx]
    linarith
  have hceil1 : 16 * (N : ℝ) / Real.log (N : ℝ)
      ≤ ((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ) := Nat.le_ceil _
  have hceil2 : ((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ)
      < 16 * (N : ℝ) / Real.log (N : ℝ) + 1 := Nat.ceil_lt_add_one hxpos.le
  refine ⟨⟨Nat.ceil_pos.mpr hxpos, Nat.ceil_le.mpr ?_⟩, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hlogpos]
    nlinarith [mul_le_mul_of_nonneg_left hlog hNpos.le]
  · linarith
  · linarith
  · linarith

theorem OMA.solution : type_of% @Green25.green_25.variants.upper_ess89 := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (16 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 16
  refine ⟨fun N => Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)), ?_,
    Asymptotics.IsBigO.antisymm ?_ ?_, ?_⟩
  · exact hev.mono fun N hN => (OMA.k_bounds N hN).1
  · refine Asymptotics.IsBigO.of_bound 17 (hev.mono fun N hN => ?_)
    obtain ⟨_, _, h4, h0⟩ := OMA.k_bounds N hN
    have e1 : ‖((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ)‖
        = ((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ) :=
      Real.norm_of_nonneg (Nat.cast_nonneg _)
    have e2 : ‖Green25.bestUpper N‖ = (N : ℝ) / Real.log (N : ℝ) := Real.norm_of_nonneg h0
    show ‖((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ)‖ ≤ 17 * ‖Green25.bestUpper N‖
    rw [e1, e2]
    exact h4
  · refine Asymptotics.IsBigO.of_bound 1 (hev.mono fun N hN => ?_)
    obtain ⟨_, h3, _, h0⟩ := OMA.k_bounds N hN
    have e1 : ‖((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ)‖
        = ((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ) :=
      Real.norm_of_nonneg (Nat.cast_nonneg _)
    have e2 : ‖Green25.bestUpper N‖ = (N : ℝ) / Real.log (N : ℝ) := Real.norm_of_nonneg h0
    show ‖Green25.bestUpper N‖ ≤ 1 * ‖((Nat.ceil (16 * (N : ℝ) / Real.log (N : ℝ)) : ℕ) : ℝ)‖
    rw [e1, e2, one_mul]
    exact h3
  · intro hP
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hP
    have hge := OMA.Nr_ge (N₀ + 1)
    obtain ⟨_, hkN, hall⟩ := hN₀ (OMA.Nr (N₀ + 1)) (by omega)
    exact OMA.no_property (N₀ + 1) _ (OMA.count_le_k (N₀ + 1) (by omega)) hkN hall
