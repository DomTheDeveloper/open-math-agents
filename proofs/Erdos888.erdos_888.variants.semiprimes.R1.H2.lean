import OMAReductions.R_Erdos888_erdos_888_variants_semiprimes_R1

-- Step Erdos888.erdos_888.variants.semiprimes.R1.H2: hypothesis H2 of reduction Erdos888.erdos_888.variants.semiprimes.R1
-- Credit: @DomTheDeveloper
-- H2 := ∀ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℕ,     p₁.Prime → q₁.Prime → p₁ < q₁ → p₂.Prime → q₂.Prime → p₂ < q₂ →     p₃.Prime → q₃.Prime → p₃ < q₃ → p₄.Prime → q₄.Prime → p₄ < q₄ →     p₁ * q₁ ≤ p₂ * q₂ → p₂ * q₂ ≤ p₃ * q₃ → p₃ * q₃ ≤ p₄ * q₄ →     IsSquare (p₁ * q₁ * (p₂ * q₂) * (p₃ * q₃) * (p₄ * q₄)) →     p₁ * q₁ * (p₄ * q₄) = p₂ * q₂ * (p₃ * q₃)
--
-- Proof. Call m a semiprime here if m = c * d with c, d distinct primes.
--
-- (1) Pairing. If four semiprimes have a square product, then they split into two pairs with
--     equal products. Take a prime p of the first, n1 = p * q. Since p divides the square
--     n1 * n2 * n3 * n4 an even number of times and n1 only once, p divides another one, say
--     nj = p * x. Cancelling p * p leaves q * x * nk * nl a square. Now q divides x * nk * nl:
--       * if q = x then nk * nl is a square of two squarefree numbers, so nk = nl, and n1 = nj;
--       * if q divides nk = q * y, then x * y * nl is a square, x cannot equal y (nl is not a
--         square), so x divides nl = x * z and y * z is a square, forcing y = z; then
--         q * nl = q * x * y = x * nk, that is n1 * nl = nj * nk;
--       * symmetrically if q divides nl.
--
-- (2) Order. For positive a ≤ b ≤ c ≤ d, any of a * b = c * d, a * c = b * d, a * d = b * c
--     gives a * d = b * c: the first two force a = c, b = d, respectively a = b, c = d.

/-- Transport `IsSquare` along an equation, so that products can be regrouped by `ring`. -/
lemma OMA.isSquare_congr {a b : ℕ} (h : IsSquare a) (e : b = a) : IsSquare b := by
  subst e
  exact h

/-- A prime dividing a square `r * M` once must divide the cofactor. -/
lemma OMA.prime_dvd_of_isSquare_mul {r M : ℕ} (hr : r.Prime) (h : IsSquare (r * M)) : r ∣ M := by
  obtain ⟨s, hs⟩ := h
  have h1 : r ∣ s * s := ⟨M, hs.symm⟩
  have h2 : r ∣ s := (hr.dvd_mul.mp h1).elim id id
  obtain ⟨t, rfl⟩ := h2
  have h3 : r * M = r * (r * (t * t)) := by rw [hs]; ring
  exact ⟨t * t, Nat.eq_of_mul_eq_mul_left hr.pos h3⟩

/-- Cancelling the square of a prime from a square. -/
lemma OMA.isSquare_of_mul_self_mul {r M : ℕ} (hr : r.Prime) (h : IsSquare (r * r * M)) :
    IsSquare M := by
  obtain ⟨s, hs⟩ := h
  have h1 : r ∣ s * s := ⟨r * M, by rw [← hs]; ring⟩
  have h2 : r ∣ s := (hr.dvd_mul.mp h1).elim id id
  obtain ⟨t, rfl⟩ := h2
  have h3 : r * r * M = r * r * (t * t) := by rw [hs]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr.pos hr.pos) h3⟩

/-- Two primes whose product is a square are equal. -/
lemma OMA.prime_eq_of_isSquare_mul {x y : ℕ} (hx : x.Prime) (hy : y.Prime)
    (h : IsSquare (x * y)) : x = y :=
  (Nat.prime_dvd_prime_iff_eq hx hy).mp (OMA.prime_dvd_of_isSquare_mul hx h)

/-- A product of two distinct primes. -/
def OMA.SP (m : ℕ) : Prop := ∃ c d : ℕ, c.Prime ∧ d.Prime ∧ c ≠ d ∧ m = c * d

/-- A prime divisor of a semiprime splits it as that prime times another prime. -/
lemma OMA.SP.split {m r : ℕ} (hm : OMA.SP m) (hr : r.Prime) (h : r ∣ m) :
    ∃ x : ℕ, x.Prime ∧ x ≠ r ∧ m = r * x := by
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hm
  rcases (hr.dvd_mul).mp h with h1 | h1
  · have hrc : r = c := (Nat.prime_dvd_prime_iff_eq hr hc).mp h1
    subst hrc
    exact ⟨d, hd, fun e => hcd e.symm, rfl⟩
  · have hrd : r = d := (Nat.prime_dvd_prime_iff_eq hr hd).mp h1
    subst hrd
    exact ⟨c, hc, hcd, Nat.mul_comm _ _⟩

/-- A semiprime is not a square. -/
lemma OMA.SP.not_isSquare {m : ℕ} (hm : OMA.SP m) : ¬ IsSquare m := by
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hm
  intro h
  exact hcd ((Nat.prime_dvd_prime_iff_eq hc hd).mp (OMA.prime_dvd_of_isSquare_mul hc h))

/-- Two semiprimes whose product is a square are equal. -/
lemma OMA.SP.eq_of_isSquare_mul {m n : ℕ} (hm : OMA.SP m) (hn : OMA.SP n)
    (h : IsSquare (m * n)) : m = n := by
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hm
  have h1 : c ∣ d * n :=
    OMA.prime_dvd_of_isSquare_mul hc (OMA.isSquare_congr h (by ring) : IsSquare (c * (d * n)))
  have h2 : c ∣ n := by
    rcases (hc.dvd_mul).mp h1 with h3 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hc hd).mp h3) hcd
    · exact h3
  obtain ⟨x, hx, _, rfl⟩ := hn.split hc h2
  have h4 : IsSquare (d * x) :=
    OMA.isSquare_of_mul_self_mul hc (OMA.isSquare_congr h (by ring) : IsSquare (c * c * (d * x)))
  rw [OMA.prime_eq_of_isSquare_mul hd hx h4]

/-- The core case analysis after one shared prime has been cancelled. -/
lemma OMA.core {a b m n : ℕ} (ha : a.Prime) (hb : b.Prime) (hm : OMA.SP m) (hn : OMA.SP n)
    (h : IsSquare (a * b * m * n)) : (a = b ∧ m = n) ∨ a * n = b * m ∨ a * m = b * n := by
  have h1 : a ∣ b * (m * n) :=
    OMA.prime_dvd_of_isSquare_mul ha
      (OMA.isSquare_congr h (by ring) : IsSquare (a * (b * (m * n))))
  rcases (ha.dvd_mul).mp h1 with h2 | h2
  · have hab : a = b := (Nat.prime_dvd_prime_iff_eq ha hb).mp h2
    subst hab
    left
    refine ⟨rfl, ?_⟩
    exact hm.eq_of_isSquare_mul hn
      (OMA.isSquare_of_mul_self_mul ha
        (OMA.isSquare_congr h (by ring) : IsSquare (a * a * (m * n))))
  · rcases (ha.dvd_mul).mp h2 with h3 | h3
    · obtain ⟨x, hx, _, rfl⟩ := hm.split ha h3
      have h4 : IsSquare (b * (x * n)) :=
        OMA.isSquare_of_mul_self_mul ha
          (OMA.isSquare_congr h (by ring) : IsSquare (a * a * (b * (x * n))))
      have h5 : b ∣ x * n := OMA.prime_dvd_of_isSquare_mul hb h4
      rcases (hb.dvd_mul).mp h5 with h6 | h6
      · have hbx : b = x := (Nat.prime_dvd_prime_iff_eq hb hx).mp h6
        subst hbx
        exact absurd
          (OMA.isSquare_of_mul_self_mul hb
            (OMA.isSquare_congr h4 (by ring) : IsSquare (b * b * n)))
          hn.not_isSquare
      · obtain ⟨y, hy, _, rfl⟩ := hn.split hb h6
        have h7 : IsSquare (x * y) :=
          OMA.isSquare_of_mul_self_mul hb
            (OMA.isSquare_congr h4 (by ring) : IsSquare (b * b * (x * y)))
        have hxy : x = y := OMA.prime_eq_of_isSquare_mul hx hy h7
        subst hxy
        right
        left
        ring
    · obtain ⟨x, hx, _, rfl⟩ := hn.split ha h3
      have h4 : IsSquare (b * (x * m)) :=
        OMA.isSquare_of_mul_self_mul ha
          (OMA.isSquare_congr h (by ring) : IsSquare (a * a * (b * (x * m))))
      have h5 : b ∣ x * m := OMA.prime_dvd_of_isSquare_mul hb h4
      rcases (hb.dvd_mul).mp h5 with h6 | h6
      · have hbx : b = x := (Nat.prime_dvd_prime_iff_eq hb hx).mp h6
        subst hbx
        exact absurd
          (OMA.isSquare_of_mul_self_mul hb
            (OMA.isSquare_congr h4 (by ring) : IsSquare (b * b * m)))
          hm.not_isSquare
      · obtain ⟨y, hy, _, rfl⟩ := hm.split hb h6
        have h7 : IsSquare (x * y) :=
          OMA.isSquare_of_mul_self_mul hb
            (OMA.isSquare_congr h4 (by ring) : IsSquare (b * b * (x * y)))
        have hxy : x = y := OMA.prime_eq_of_isSquare_mul hx hy h7
        subst hxy
        right
        right
        ring

/-- Four semiprimes with a square product split into two pairs with equal products. -/
lemma OMA.pair {n₁ n₂ n₃ n₄ : ℕ} (h₁ : OMA.SP n₁) (h₂ : OMA.SP n₂) (h₃ : OMA.SP n₃)
    (h₄ : OMA.SP n₄) (h : IsSquare (n₁ * n₂ * n₃ * n₄)) :
    n₁ * n₂ = n₃ * n₄ ∨ n₁ * n₃ = n₂ * n₄ ∨ n₁ * n₄ = n₂ * n₃ := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h₁
  have h1 : p ∣ q * (n₂ * (n₃ * n₄)) :=
    OMA.prime_dvd_of_isSquare_mul hp
      (OMA.isSquare_congr h (by ring) : IsSquare (p * (q * (n₂ * (n₃ * n₄)))))
  rcases (hp.dvd_mul).mp h1 with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h2) hpq
  rcases (hp.dvd_mul).mp h2 with h3 | h3
  · obtain ⟨x, hx, _, rfl⟩ := h₂.split hp h3
    have h5 : IsSquare (q * x * n₃ * n₄) :=
      OMA.isSquare_of_mul_self_mul hp
        (OMA.isSquare_congr h (by ring) : IsSquare (p * p * (q * x * n₃ * n₄)))
    rcases OMA.core hq hx h₃ h₄ h5 with ⟨hqx, h34⟩ | h6 | h6
    · right
      left
      rw [hqx, h34]
    · right
      right
      calc p * q * n₄ = p * (q * n₄) := by ring
        _ = p * (x * n₃) := by rw [h6]
        _ = p * x * n₃ := by ring
    · right
      left
      calc p * q * n₃ = p * (q * n₃) := by ring
        _ = p * (x * n₄) := by rw [h6]
        _ = p * x * n₄ := by ring
  rcases (hp.dvd_mul).mp h3 with h4 | h4
  · obtain ⟨x, hx, _, rfl⟩ := h₃.split hp h4
    have h5 : IsSquare (q * x * n₂ * n₄) :=
      OMA.isSquare_of_mul_self_mul hp
        (OMA.isSquare_congr h (by ring) : IsSquare (p * p * (q * x * n₂ * n₄)))
    rcases OMA.core hq hx h₂ h₄ h5 with ⟨hqx, h24⟩ | h6 | h6
    · left
      rw [hqx, h24]
    · right
      right
      calc p * q * n₄ = p * (q * n₄) := by ring
        _ = p * (x * n₂) := by rw [h6]
        _ = n₂ * (p * x) := by ring
    · left
      calc p * q * n₂ = p * (q * n₂) := by ring
        _ = p * (x * n₄) := by rw [h6]
        _ = p * x * n₄ := by ring
  · obtain ⟨x, hx, _, rfl⟩ := h₄.split hp h4
    have h5 : IsSquare (q * x * n₂ * n₃) :=
      OMA.isSquare_of_mul_self_mul hp
        (OMA.isSquare_congr h (by ring) : IsSquare (p * p * (q * x * n₂ * n₃)))
    rcases OMA.core hq hx h₂ h₃ h5 with ⟨hqx, h23⟩ | h6 | h6
    · left
      rw [hqx, h23]
      ring
    · right
      left
      calc p * q * n₃ = p * (q * n₃) := by ring
        _ = p * (x * n₂) := by rw [h6]
        _ = n₂ * (p * x) := by ring
    · left
      calc p * q * n₂ = p * (q * n₂) := by ring
        _ = p * (x * n₃) := by rw [h6]
        _ = n₃ * (p * x) := by ring

/-- For positive `a ≤ b ≤ c ≤ d`, any pairing with equal products is the outer–inner one. -/
lemma OMA.order {a b c d : ℕ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (h : a * b = c * d ∨ a * c = b * d ∨ a * d = b * c) : a * d = b * c := by
  rcases h with h | h | h
  · have hac : a = c := by
      by_contra hne
      have hlt : a < c := lt_of_le_of_ne (hab.trans hbc) hne
      have hb : 0 < b := lt_of_lt_of_le ha hab
      have h1 : a * b < c * b := mul_lt_mul_of_pos_right hlt hb
      have h2 : c * b ≤ c * d := Nat.mul_le_mul (le_refl c) (hbc.trans hcd)
      exact absurd h (Nat.ne_of_lt (lt_of_lt_of_le h1 h2))
    subst hac
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left ha h
    subst hbd
    exact Nat.mul_comm _ _
  · have hab' : a = b := by
      by_contra hne
      have hlt : a < b := lt_of_le_of_ne hab hne
      have hc : 0 < c := lt_of_lt_of_le ha (hab.trans hbc)
      have h1 : a * c < b * c := mul_lt_mul_of_pos_right hlt hc
      have h2 : b * c ≤ b * d := Nat.mul_le_mul (le_refl b) hcd
      exact absurd h (Nat.ne_of_lt (lt_of_lt_of_le h1 h2))
    subst hab'
    have hcd' : c = d := Nat.eq_of_mul_eq_mul_left ha h
    subst hcd'
    rfl
  · exact h

theorem OMA.solution : OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2 := by
  unfold OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2
  intro p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ hp₁ hq₁ h₁ hp₂ hq₂ h₂ hp₃ hq₃ h₃ hp₄ hq₄ h₄ h12 h23 h34 hsq
  have s₁ : OMA.SP (p₁ * q₁) := ⟨p₁, q₁, hp₁, hq₁, Nat.ne_of_lt h₁, rfl⟩
  have s₂ : OMA.SP (p₂ * q₂) := ⟨p₂, q₂, hp₂, hq₂, Nat.ne_of_lt h₂, rfl⟩
  have s₃ : OMA.SP (p₃ * q₃) := ⟨p₃, q₃, hp₃, hq₃, Nat.ne_of_lt h₃, rfl⟩
  have s₄ : OMA.SP (p₄ * q₄) := ⟨p₄, q₄, hp₄, hq₄, Nat.ne_of_lt h₄, rfl⟩
  exact OMA.order (Nat.mul_pos hp₁.pos hq₁.pos) h12 h23 h34 (OMA.pair s₁ s₂ s₃ s₄ hsq)
