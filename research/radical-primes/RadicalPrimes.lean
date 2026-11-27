import Mathlib.Algebra.Field.ZMod
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
Prime divisors of coefficients of powers of c + √2 + √3 and ∛2 + (∛2)².
The state coordinates are the coefficients in the ordered power bases.
-/

namespace RadicalPrimes

open Function

abbrev Quad (R : Type) := R × R × R × R
abbrev Cubic (R : Type) := R × R × R

def quadOne (R : Type) [Semiring R] : Quad R := (1, 0, 0, 0)
def cubicOne (R : Type) [Semiring R] : Cubic R := (1, 0, 0)

/-- Multiply by t + u + v in the basis (1,u,v,uv), with u²=2 and v²=3. -/
def quadStep {R : Type} [Semiring R] (t : R) (w : Quad R) : Quad R :=
  let (a, b, c, d) := w
  (t*a + 2*b + 3*c, a + t*b + 3*d, a + t*c + 2*d, b + c + t*d)

/-- Multiply by u + u² in the basis (1,u,u²), with u³=2. -/
def cubicStep {R : Type} [Semiring R] (w : Cubic R) : Cubic R :=
  let (a, b, c) := w
  (2*b + 2*c, a + 2*c, a + b)

def quad (t n : ℕ) : Quad ℕ := (quadStep t)^[n] (quadOne ℕ)
def cubic (n : ℕ) : Cubic ℕ := cubicStep^[n] (cubicOne ℕ)

inductive Radical | sqrtTwo | sqrtThree | sqrtSix
inductive CubicSlot | scalar | linear | square

def radicalCoord {R : Type} (j : Radical) (w : Quad R) : R :=
  match j with
  | .sqrtTwo => w.2.1
  | .sqrtThree => w.2.2.1
  | .sqrtSix => w.2.2.2

def cubicCoord {R : Type} (j : CubicSlot) (w : Cubic R) : R :=
  match j with
  | .scalar => w.1
  | .linear => w.2.1
  | .square => w.2.2

/-- The hit indices contain an entire arithmetic progression of positive step. -/
def Progression (P : ℕ → Prop) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, P (a + d*k)

/-- A binary membership pattern repeats from index s, with positive period d. -/
def RepeatingTail (P : ℕ → Prop) : Prop :=
  ∃ s d : ℕ, 0 < d ∧ ∀ n, P (s+n+d) ↔ P (s+n)

theorem progression_unbounded {P : ℕ → Prop} (h : Progression P) (N : ℕ) :
    ∃ n > N, P n := by
  obtain ⟨a, d, hd, hh⟩ := h
  exact ⟨a+d*(N+1), by nlinarith, hh (N+1)⟩

private theorem fromLoop {X : Type} (f : X → X) (x : X) (P : X → Prop)
    {s d i : ℕ} (hd : 0 < d) (loop : IsPeriodicPt f d (f^[s] x))
    (hit : P (f^[i] (f^[s] x))) : Progression (fun n => P (f^[n] x)) := by
  refine ⟨i+s, d, hd, fun k => ?_⟩
  change P (f^[i+s+d*k] x)
  rw [show i+s+d*k = i+(d*k+s) by omega, iterate_add_apply, iterate_add_apply,
      (show f^[d*k] (f^[s] x) = f^[s] x from loop.mul_const k)]
  exact hit

private theorem fromPermutation {X : Type} [Finite X] (f : X → X) (x : X)
    (P : X → Prop) (hf : Injective f) (i : ℕ) (hit : P (f^[i] x)) :
    Progression (fun n => P (f^[n] x)) := by
  obtain ⟨d, hd, loop⟩ := hf.mem_periodicPts x
  exact fromLoop f x P (s := 0) (i := i) hd loop hit

private theorem finiteTail {X : Type} [Finite X] (f : X → X) (x : X) (P : X → Prop) :
    RepeatingTail (fun n => P (f^[n] x)) := by
  obtain ⟨a, b, hab, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => f^[n] x) (fun _ => Set.mem_univ _)
  refine ⟨a, b-a, by omega, fun n => ?_⟩
  change P (f^[a+n+(b-a)] x) ↔ P (f^[a+n] x)
  rw [show a+n+(b-a) = n+b by omega, show a+n = n+a by omega,
      iterate_add_apply, iterate_add_apply, heq]

private def quadCast (R : Type) [Semiring R] (w : Quad ℕ) : Quad R :=
  (w.1, w.2.1, w.2.2.1, w.2.2.2)
private def cubicCast (R : Type) [Semiring R] (w : Cubic ℕ) : Cubic R :=
  (w.1, w.2.1, w.2.2)

private theorem mapQuad (R : Type) [Semiring R] (t n : ℕ) :
    quadCast R (quad t n) = (quadStep (t : R))^[n] (quadOne R) := by
  induction n with
  | zero => simp [quad, quadCast, quadOne]
  | succ n ih =>
    rw [show quad t (n+1) = quadStep t (quad t n) from iterate_succ_apply' _ _ _, iterate_succ_apply', ← ih]
    rcases quad t n with ⟨a,b,c,d⟩
    simp [quadStep, quadCast]

private theorem mapCubic (R : Type) [Semiring R] (n : ℕ) :
    cubicCast R (cubic n) = cubicStep^[n] (cubicOne R) := by
  induction n with
  | zero => simp [cubic, cubicCast, cubicOne]
  | succ n ih =>
    rw [show cubic (n+1) = cubicStep (cubic n) from iterate_succ_apply' _ _ _, iterate_succ_apply', ← ih]
    rcases cubic n with ⟨a,b,c⟩
    simp [cubicStep, cubicCast]

private theorem quadDvd (t p n : ℕ) (j : Radical) :
    (p ∣ radicalCoord j (quad t n)) ↔
    radicalCoord j ((quadStep (t : ZMod p))^[n] (quadOne (ZMod p))) = 0 := by
  rw [← mapQuad, ← ZMod.natCast_eq_zero_iff]
  cases j <;> rfl

private theorem cubicDvd (p n : ℕ) (j : CubicSlot) :
    (p ∣ cubicCoord j (cubic n)) ↔
    cubicCoord j (cubicStep^[n] (cubicOne (ZMod p))) = 0 := by
  rw [← mapCubic, ← ZMod.natCast_eq_zero_iff]
  cases j <;> rfl

theorem quadratic_radical_tail (t p : ℕ) [NeZero p] (j : Radical) :
    RepeatingTail (fun n => p ∣ radicalCoord j (quad t n)) := by
  simpa only [quadDvd] using
    finiteTail (quadStep (t : ZMod p)) (quadOne _) (fun w => radicalCoord j w = 0)

theorem quadratic_scalar_tail (t p : ℕ) [NeZero p] :
    RepeatingTail (fun n => p ∣ (quad t n).1) := by
  have h (n : ℕ) : (p ∣ (quad t n).1) ↔
      ((quadStep (t : ZMod p))^[n] (quadOne _)).1 = 0 := by
    rw [← mapQuad, ← ZMod.natCast_eq_zero_iff]; rfl
  simpa only [h] using finiteTail (quadStep (t : ZMod p)) (quadOne _) (fun w => w.1 = 0)

theorem cubic_tail (p : ℕ) [NeZero p] (j : CubicSlot) :
    RepeatingTail (fun n => p ∣ cubicCoord j (cubic n)) := by
  simpa only [cubicDvd] using
    finiteTail cubicStep (cubicOne (ZMod p)) (fun w => cubicCoord j w = 0)

private theorem quadInjective {K : Type} [Field K] (t : K)
    (hn : t^4 - 10*t^2 + 1 ≠ 0) : Injective (quadStep t) := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ he
  obtain ⟨h₁,h₂,h₃,h₄⟩ := (show _ ∧ _ ∧ _ ∧ _ from
    (by simpa only [quadStep, Prod.mk.injEq] using he))
  apply Prod.ext
  · apply mul_left_cancel₀ hn
    linear_combination (t^3-5*t)*h₁ + (-2*t^2-2)*h₂ + (3-3*t^2)*h₃ + 12*t*h₄
  · apply Prod.ext
    · apply mul_left_cancel₀ hn
      linear_combination (-t^2-1)*h₁ + (t^3-5*t)*h₂ + 6*t*h₃ + (3-3*t^2)*h₄
    · apply Prod.ext
      · apply mul_left_cancel₀ hn
        linear_combination (1-t^2)*h₁ + 4*t*h₂ + (t^3-5*t)*h₃ + (-2*t^2-2)*h₄
      · apply mul_left_cancel₀ hn
        linear_combination (2*t)*h₁ + (1-t^2)*h₂ + (-t^2-1)*h₃ + (t^3-5*t)*h₄

private theorem cubicInjective {K : Type} [Field K] (hn : (6 : K) ≠ 0) :
    Injective (cubicStep (R := K)) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ he
  obtain ⟨h₁,h₂,h₃⟩ := (show _ ∧ _ ∧ _ from
    (by simpa only [cubicStep, Prod.mk.injEq] using he))
  apply Prod.ext
  · apply mul_left_cancel₀ hn
    linear_combination -2*h₁ + 2*h₂ + 4*h₃
  · apply Prod.ext
    · apply mul_left_cancel₀ hn
      linear_combination 2*h₁ - 2*h₂ + 2*h₃
    · apply mul_left_cancel₀ hn
      linear_combination h₁ + 2*h₂ - 2*h₃

private theorem primeCastNe {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    (q : ZMod p) ≠ 0 :=
  fun z => h ((Nat.prime_dvd_prime_iff_eq hp hq).mp ((ZMod.natCast_eq_zero_iff q p).mp z))

private theorem quadOrdinary (t p : ℕ) [Fact p.Prime] (j : Radical)
    (h : (t : ZMod p)^4 - 10*(t : ZMod p)^2 + 1 ≠ 0) :
    Progression (fun n => p ∣ radicalCoord j (quad t n)) := by
  simp only [quadDvd]
  apply fromPermutation (quadStep (t : ZMod p)) (quadOne _) (fun w => radicalCoord j w = 0) (quadInjective _ h) 0
  cases j <;> rfl

private theorem quadOddConstant (t : ℕ) (ht : t = 1 ∨ t = 3) (p : ℕ) (hp : p.Prime)
    (j : Radical) : Progression (fun n => p ∣ radicalCoord j (quad t n)) := by
  by_cases h : p = 2
  · subst p
    simp only [quadDvd]
    apply fromLoop (quadStep (t : ZMod 2)) (quadOne _) (fun w => radicalCoord j w = 0)
      (s := 2) (d := 1) (i := 0) (by decide)
    · rcases ht with rfl | rfl <;> decide
    · rcases ht with rfl | rfl <;> cases j <;> decide
  · let : Fact p.Prime := ⟨hp⟩
    have h₂ : (2 : ZMod p) ≠ 0 := primeCastNe hp Nat.prime_two h
    have h₈ : (8 : ZMod p) ≠ 0 := by
      rw [show (8 : ZMod p) = 2^3 by ring]; exact pow_ne_zero _ h₂
    apply quadOrdinary
    rcases ht with rfl | rfl <;>
      convert neg_ne_zero.mpr h₈ using 1 <;> push_cast <;> ring

/-- A list of intermediate states checks a long return one small transition at a time. -/
private def checkSteps {X : Type} [DecidableEq X] (f : X → X) (stop : X) :
    List X → X → Bool
  | [], x => decide (x = stop)
  | y :: ys, x => decide (f x = y) && checkSteps f stop ys y

private theorem checkedReturn {X : Type} [DecidableEq X] (f : X → X) (stop : X)
    (states : List X) (x : X) (ok : checkSteps f stop states x = true) :
    f^[states.length] x = stop := by
  induction states generalizing x with
  | nil => simpa [checkSteps] using ok
  | cons y ys ih =>
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq] at ok
    rw [List.length_cons, iterate_succ_apply, ok.1]
    exact ih y ok.2

private theorem returnAt23 : IsPeriodicPt (quadStep (2 : ZMod 23)) 22
    ((quadStep (2 : ZMod 23))^[1] (quadOne _)) := by
  let start : Quad (ZMod 23) := (2,1,1,0)
  let states : List (Quad (ZMod 23)) :=
    [(9,4,4,2), (15,0,21,12), (1,5,12,22), (2,8,0,15),
     (20,17,9,15), (9,7,22,10), (6,7,4,3), (15,6,20,17),
     (10,9,20,14), (6,1,9,11), (18,18,0,9), (3,12,13,13),
     (0,20,9,5), (21,9,5,16), (6,18,17,0), (7,19,17,12),
     (11,12,19,14), (11,8,8,13), (16,20,7,19), (1,21,22,19),
     (18,8,14,12), (2,1,1,0)]
  change (quadStep (2 : ZMod 23))^[states.length] start = start
  exact checkedReturn _ _ states start (by decide +kernel)

private theorem quadTwo (p : ℕ) (hp : p.Prime) (j : Radical) :
    Progression (fun n => p ∣ radicalCoord j (quad 2 n)) := by
  by_cases h : p = 23
  · subst p
    simp only [quadDvd]
    have loop : IsPeriodicPt (quadStep (2 : ZMod 23)) 22
        ((quadStep (2 : ZMod 23))^[1] (quadOne _)) := returnAt23
    cases j with
    | sqrtTwo => exact fromLoop _ _ (fun w => radicalCoord .sqrtTwo w = 0) (i := 2) (by decide) loop (by decide)
    | sqrtThree => exact fromLoop _ _ (fun w => radicalCoord .sqrtThree w = 0) (i := 4) (by decide) loop (by decide)
    | sqrtSix => exact fromLoop _ _ (fun w => radicalCoord .sqrtSix w = 0) (i := 0) (by decide) loop (by decide)
  · let : Fact p.Prime := ⟨hp⟩
    have h₂₃ : (23 : ZMod p) ≠ 0 := primeCastNe hp (by decide : Nat.Prime 23) h
    apply quadOrdinary
    change (2 : ZMod p)^4 - 10*2^2 + 1 ≠ 0
    rw [show (2 : ZMod p)^4 - 10*2^2 + 1 = -23 by ring]
    exact neg_ne_zero.mpr h₂₃

/-- The nine nonconstant quadratic coefficient sequences all have a progression of
p-divisible terms for every prime p. -/
theorem quadratic_radical_hits (t p : ℕ) (ht : t = 1 ∨ t = 2 ∨ t = 3)
    (hp : p.Prime) (j : Radical) : Progression (fun n => p ∣ radicalCoord j (quad t n)) := by
  rcases ht with h | h | h
  · exact quadOddConstant t (Or.inl h) p hp j
  · subst t; exact quadTwo p hp j
  · exact quadOddConstant t (Or.inr h) p hp j

/-- All three cubic coordinates have a progression of p-divisible terms for every prime. -/
theorem cubic_hits (p : ℕ) (hp : p.Prime) (j : CubicSlot) :
    Progression (fun n => p ∣ cubicCoord j (cubic n)) := by
  simp only [cubicDvd]
  by_cases h : p = 2 ∨ p = 3
  · apply fromLoop cubicStep (cubicOne (ZMod p)) (fun w => cubicCoord j w = 0)
      (s := 3) (d := 1) (i := 0) (by decide)
    · rcases h with rfl | rfl <;> decide
    · rcases h with rfl | rfl <;> cases j <;> decide
  · let : Fact p.Prime := ⟨hp⟩
    have h₂ : (2 : ZMod p) ≠ 0 := primeCastNe hp Nat.prime_two (fun e => h (Or.inl e))
    have h₃ : (3 : ZMod p) ≠ 0 := primeCastNe hp Nat.prime_three (fun e => h (Or.inr e))
    have inj : Injective (cubicStep (R := ZMod p)) := cubicInjective (K := ZMod p) (by
      rw [show (6 : ZMod p) = 2*3 by ring]; exact mul_ne_zero h₂ h₃)
    cases j with
    | scalar => exact fromPermutation _ _ (fun w => cubicCoord .scalar w = 0) inj 1 (by simp [cubicCoord, cubicOne, cubicStep])
    | linear => exact fromPermutation _ _ (fun w => cubicCoord .linear w = 0) inj 0 rfl
    | square => exact fromPermutation _ _ (fun w => cubicCoord .square w = 0) inj 0 rfl

/-- If e lists every hit once in increasing order, its consecutive gaps repeat.
This applies to the natural enumeration of every infinite hit set. -/
theorem gaps_of_repeatingTail {P : ℕ → Prop} (tail : RepeatingTail P)
    (e : ℕ → ℕ) (he : StrictMono e) (cover : ∀ n, P n ↔ ∃ i, e i = n) :
    ∃ b k : ℕ, 0 < k ∧ ∀ i,
      e (b+i+k+1) - e (b+i+k) = e (b+i+1) - e (b+i) := by
  obtain ⟨s,d,hd,period⟩ := tail
  have mem (i : ℕ) : P (e i) := (cover _).mpr ⟨i,rfl⟩
  have shift (n : ℕ) (hn : s ≤ n) : P (n+d) ↔ P n := by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hn
    exact period l
  obtain ⟨j,hj⟩ := (cover _).mp ((shift (e s) (he.id_le s)).mpr (mem _))
  have hjlt : s < j := he.lt_iff_lt.mp (by omega)
  have liftHit (i : ℕ) : e (j+i) = e (s+i)+d := by
    induction i with
    | zero => simpa using hj
    | succ i ih =>
      have h₁ : e (s+i) < e (s+i+1) := he (Nat.lt_succ_self _)
      have h₂ : e (j+i) < e (j+i+1) := he (Nat.lt_succ_self _)
      have h₃ : s ≤ e (s+i) := le_trans (Nat.le_add_right _ _) (he.id_le _)
      obtain ⟨v,hv⟩ := (cover _).mp ((shift (e (s+i+1)) (by omega)).mpr (mem _))
      have vj : j+i < v := he.lt_iff_lt.mp (by omega)
      have upper := he.monotone (show j+i+1 ≤ v by omega)
      have low : s ≤ e (j+i+1)-d := by omega
      have recover : e (j+i+1)-d+d = e (j+i+1) := by omega
      have hit : P (e (j+i+1)-d) := (shift _ low).mp (by rw [recover]; exact mem _)
      obtain ⟨u,hu⟩ := (cover _).mp hit
      have us : s+i < u := he.lt_iff_lt.mp (by omega)
      have lower := he.monotone (show s+i+1 ≤ u by omega)
      change e (j+i+1) = e (s+i+1)+d
      omega
  refine ⟨s,j-s,by omega, fun i => ?_⟩
  have eq₀ := liftHit i
  have eq₁ := liftHit (i+1)
  rw [show s+i+(j-s)=j+i by omega]
  simp only [← Nat.add_assoc] at eq₁
  omega

private def evaluate {R : Type} [CommRing R] (r s : R) (w : Quad R) : R :=
  w.1 + w.2.1*r + w.2.2.1*s + w.2.2.2*r*s

private theorem evaluationPow {K : Type} [CommRing K] (t r s : K)
    (hr : r^2 = 2) (hs : s^2 = 3) (n : ℕ) :
    evaluate r s ((quadStep t)^[n] (quadOne K)) = (t+r+s)^n := by
  induction n with
  | zero => simp [evaluate, quadOne]
  | succ n ih =>
    rw [iterate_succ_apply', pow_succ, ← ih]
    rcases (quadStep t)^[n] (quadOne K) with ⟨a,b,c,d⟩
    dsimp [evaluate, quadStep]
    linear_combination -(b+d*s)*hr - (c+d*r)*hs

/-- Integer coordinates from the recurrence reconstruct the literal quadratic power. -/
theorem quadratic_expansion {K : Type} [CommRing K] (t n : ℕ) (r s : K)
    (hr : r^2=2) (hs : s^2=3) :
    ((quad t n).1 : K) + ((quad t n).2.1 : K)*r + ((quad t n).2.2.1 : K)*s +
      ((quad t n).2.2.2 : K)*r*s = ((t : K)+r+s)^n := by
  change evaluate r s (quadCast K (quad t n)) = _
  rw [mapQuad]
  exact evaluationPow _ _ _ hr hs n

private def cubicEval {K : Type} [CommRing K] (r : K) (w : Cubic K) : K :=
  w.1 + w.2.1*r + w.2.2*r^2

/-- Integer coordinates from the recurrence reconstruct the literal cubic power. -/
theorem cubic_expansion {K : Type} [CommRing K] (n : ℕ) (r : K) (hr : r^3=2) :
    ((cubic n).1 : K) + ((cubic n).2.1 : K)*r + ((cubic n).2.2 : K)*r^2 = (r+r^2)^n := by
  change cubicEval r (cubicCast K (cubic n)) = _
  rw [mapCubic]
  induction n with
  | zero => simp [cubicEval, cubicOne]
  | succ n ih =>
    rw [iterate_succ_apply', pow_succ, ← ih]
    rcases cubicStep^[n] (cubicOne K) with ⟨a,b,c⟩
    dsimp [cubicEval, cubicStep]
    linear_combination -(b+c+c*r)*hr

private def fourPowers {K : Type} [CommRing K] (a b c d : K) (n : ℕ) : K :=
  a^n + b^n + c^n + d^n

private theorem fourTimesConstant {K : Type} [CommRing K] (t r s : K)
    (hr : r^2=2) (hs : s^2=3) (n : ℕ) :
    fourPowers (t+r+s) (t+r+(-s)) (t+(-r)+s) (t+(-r)+(-s)) n =
    4 * ((quadStep t)^[n] (quadOne K)).1 := by
  have hr' : (-r)^2=2 := by simpa using hr
  have hs' : (-s)^2=3 := by simpa using hs
  rw [fourPowers, ← evaluationPow t r s hr hs, ← evaluationPow t r (-s) hr hs',
    ← evaluationPow t (-r) s hr' hs, ← evaluationPow t (-r) (-s) hr' hs']
  unfold evaluate
  ring

private theorem reduceExponent {K : Type} [Monoid K] (b : K) {k : ℕ} (h : b^k=1) (n : ℕ) :
    b^n = b^(n%k) := by
  conv_lhs => rw [← Nat.mod_add_div n k, pow_add, pow_mul, h, one_pow, mul_one]

private theorem missingPrime (t p k : ℕ) (r s : ZMod p) (hk : 0 < k)
    (hr : r^2=2) (hs : s^2=3)
    (orders : ((t : ZMod p)+r+s)^k=1 ∧ ((t : ZMod p)+r+(-s))^k=1 ∧
      ((t : ZMod p)+(-r)+s)^k=1 ∧ ((t : ZMod p)+(-r)+(-s))^k=1)
    (block : ∀ i : Fin k, fourPowers ((t : ZMod p)+r+s) ((t : ZMod p)+r+(-s))
       ((t : ZMod p)+(-r)+s) ((t : ZMod p)+(-r)+(-s)) i.val ≠ 0) (n : ℕ) :
    ¬ p ∣ (quad t n).1 := by
  intro dvd
  have zero : ((quadStep (t : ZMod p))^[n] (quadOne _)).1 = 0 := by
    rw [← mapQuad]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr dvd
  have e := fourTimesConstant (t : ZMod p) r s hr hs n
  rw [zero, mul_zero, fourPowers, reduceExponent _ orders.1 n,
    reduceExponent _ orders.2.1 n, reduceExponent _ orders.2.2.1 n,
    reduceExponent _ orders.2.2.2 n] at e
  exact block ⟨n%k, Nat.mod_lt n hk⟩ e

/-- 23 never divides the rational coefficient of (1 + √2 + √3)^n. -/
theorem A188570_missing (n : ℕ) : ¬ 23 ∣ (quad 1 n).1 := by
  apply missingPrime 1 23 22 5 7 <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
/-- 241 never divides the rational coefficient of (2 + √2 + √3)^n. -/
theorem A377109_missing (n : ℕ) : ¬ 241 ∣ (quad 2 n).1 := by
  apply missingPrime 2 241 240 22 56 <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
/-- 167 never divides the rational coefficient of (3 + √2 + √3)^n. -/
theorem A377113_missing (n : ℕ) : ¬ 167 ∣ (quad 3 n).1 := by
  apply missingPrime 3 167 166 13 62 <;> decide +kernel

set_option maxRecDepth 16000 in
theorem witnesses_prime : Nat.Prime 23 ∧ Nat.Prime 241 ∧ Nat.Prime 167 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end RadicalPrimes
