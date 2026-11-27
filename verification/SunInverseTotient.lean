import SunLargePrime

/-!
The inverse totient of 1584 gives every input where the fixed choice `k = 5157`
produces the prime certified in `SunLargePrime`. The finite table is a certificate.
Its closure under adjoining a prime establishes completeness by strong induction,
without an upper bound on the input. The reverse implication checks each totient.
-/

namespace SunPrimeCertificates.Large

/-- Positive differences `n - 5157` for which the exponent is 1584. -/
def offsets : List ℕ := [
    1679, 1691, 1985, 2093, 2185, 2345, 2403, 2553, 2613,
    2691, 2985, 3015, 3105, 3176, 3184, 3358, 3382, 3404,
    3484, 3496, 3752, 3970, 3980, 4186, 4370, 4690, 4764,
    4776, 4806, 4824, 4968, 5106, 5226, 5244, 5382, 5628,
    5796, 5970, 6030, 6210]

private def possiblePrimes : List ℕ := [2, 3, 5, 7, 13, 17, 19, 23, 37, 67, 73, 89, 199, 397]

/-- Candidate pairs `(m, φ(m))` with `φ(m)` dividing 1584. -/
private def states : List (ℕ × ℕ) := [
    (1, 1), (2, 1), (3, 2), (4, 2), (5, 4), (6, 2), (7, 6),
    (8, 4), (9, 6), (10, 4), (12, 4), (13, 12), (14, 6), (15, 8),
    (16, 8), (17, 16), (18, 6), (19, 18), (20, 8), (21, 12), (23, 22),
    (24, 8), (26, 12), (27, 18), (28, 12), (30, 8), (32, 16), (34, 16),
    (35, 24), (36, 12), (37, 36), (38, 18), (39, 24), (40, 16), (42, 12),
    (45, 24), (46, 22), (48, 16), (52, 24), (54, 18), (56, 24), (57, 36),
    (60, 16), (63, 36), (65, 48), (67, 66), (69, 44), (70, 24), (72, 24),
    (73, 72), (74, 36), (76, 36), (78, 24), (84, 24), (89, 88), (90, 24),
    (91, 72), (92, 44), (95, 72), (104, 48), (105, 48), (108, 36), (111, 72),
    (112, 48), (114, 36), (115, 88), (117, 72), (126, 36), (130, 48), (134, 66),
    (135, 72), (138, 44), (140, 48), (144, 48), (146, 72), (148, 72), (152, 72),
    (156, 48), (161, 132), (168, 48), (178, 88), (180, 48), (182, 72), (184, 88),
    (185, 144), (190, 72), (199, 198), (201, 132), (207, 132), (210, 48), (216, 72),
    (219, 144), (222, 72), (228, 72), (230, 88), (234, 72), (252, 72), (267, 176),
    (268, 132), (270, 72), (273, 144), (276, 88), (285, 144), (292, 144), (296, 144),
    (299, 264), (304, 144), (315, 144), (322, 132), (335, 264), (345, 176), (356, 176),
    (364, 144), (368, 176), (370, 144), (380, 144), (397, 396), (398, 198), (402, 132),
    (414, 132), (432, 144), (437, 396), (438, 144), (444, 144), (456, 144), (460, 176),
    (468, 144), (469, 396), (483, 264), (504, 144), (534, 176), (536, 264), (540, 144),
    (546, 144), (552, 176), (570, 144), (597, 396), (598, 264), (603, 396), (621, 396),
    (623, 528), (630, 144), (644, 264), (670, 264), (690, 176), (794, 396), (796, 396),
    (801, 528), (804, 264), (805, 528), (828, 264), (851, 792), (871, 792), (874, 396),
    (897, 528), (938, 396), (966, 264), (995, 792), (1005, 528), (1035, 528), (1072, 528),
    (1191, 792), (1194, 396), (1196, 528), (1206, 396), (1242, 396), (1246, 528), (1288, 528),
    (1311, 792), (1340, 528), (1407, 792), (1449, 792), (1588, 792), (1592, 792), (1602, 528),
    (1608, 528), (1610, 528), (1656, 528), (1679, 1584), (1691, 1584), (1702, 792), (1742, 792),
    (1748, 792), (1794, 528), (1876, 792), (1932, 528), (1985, 1584), (1990, 792), (2010, 528),
    (2070, 528), (2093, 1584), (2185, 1584), (2345, 1584), (2382, 792), (2388, 792), (2403, 1584),
    (2412, 792), (2484, 792), (2553, 1584), (2613, 1584), (2622, 792), (2691, 1584), (2814, 792),
    (2898, 792), (2985, 1584), (3015, 1584), (3105, 1584), (3176, 1584), (3184, 1584), (3358, 1584),
    (3382, 1584), (3404, 1584), (3484, 1584), (3496, 1584), (3752, 1584), (3970, 1584), (3980, 1584),
    (4186, 1584), (4370, 1584), (4690, 1584), (4764, 1584), (4776, 1584), (4806, 1584), (4824, 1584),
    (4968, 1584), (5106, 1584), (5226, 1584), (5244, 1584), (5382, 1584), (5628, 1584), (5796, 1584),
    (5970, 1584), (6030, 1584), (6210, 1584)]

private def nextPhi (m v p : ℕ) := if p ∣ m then p * v else (p - 1) * v

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem eligible {p : ℕ} (hp : p.Prime) (hd : p - 1 ∣ 1584) : p ∈ possiblePrimes := by
  have check : (List.range 1586).all (fun a => decide (a - 1 ∣ 1584 → a ∈ possiblePrimes ∨ ¬a.Prime)) = true := by decide +kernel
  have bound := Nat.le_of_dvd (by decide : 0 < 1584) hd
  have h := List.all_eq_true.mp check p (List.mem_range.mpr (by omega))
  exact ((of_decide_eq_true h) hd).resolve_right (fun hnp => hnp hp)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem closed {m v p : ℕ} (hm : (m,v) ∈ states) (hp : p ∈ possiblePrimes)
    (hd : nextPhi m v p ∣ 1584) : (p*m, nextPhi m v p) ∈ states := by
  have check : states.all (fun x => possiblePrimes.all (fun a => decide
      (nextPhi x.1 x.2 a ∣ 1584 → (a*x.1, nextPhi x.1 x.2 a) ∈ states))) = true := by decide +kernel
  have h := List.all_eq_true.mp (List.all_eq_true.mp check (m,v) hm) p hp
  exact (of_decide_eq_true h) hd

private theorem covered (n : ℕ) : n.totient ∣ 1584 → (n, n.totient) ∈ states := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hd
    by_cases hz : n = 0
    · subst n
      norm_num at hd
    by_cases ho : n = 1
    · subst n
      decide
    let p := n.minFac
    let q := n / p
    have hp : p.Prime := Nat.minFac_prime ho
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hprod : p*q = n := Nat.mul_div_cancel' hpn
    have hq : q < n := Nat.div_lt_self (by omega) hp.one_lt
    have hqn : q ∣ n := ⟨p, hprod.symm.trans (Nat.mul_comm p q)⟩
    have hdq := (Nat.totient_dvd_of_dvd hqn).trans hd
    have hdp : p - 1 ∣ 1584 := by
      rw [← Nat.totient_prime hp]; exact (Nat.totient_dvd_of_dvd hpn).trans hd
    have hval : n.totient = nextPhi q q.totient p := by
      calc
        n.totient = (p*q).totient := congrArg Nat.totient hprod.symm
        _ = _ := by
          by_cases hh : p ∣ q
          · simpa [nextPhi, hh] using Nat.totient_mul_of_prime_of_dvd hp hh
          · simpa [nextPhi, hh] using Nat.totient_mul_of_prime_of_not_dvd hp hh
    have hnext : nextPhi q q.totient p ∣ 1584 := hval ▸ hd
    have result := closed (ih q hq hdq) (eligible hp hdp) hnext
    simpa only [hprod, ← hval] using result

private def factorLists : List (List ℕ) := [
    [23, 73], [19, 89], [5, 397], [7, 13, 23],
    [5, 19, 23], [5, 7, 67], [3, 3, 3, 89], [3, 23, 37],
    [3, 13, 67], [3, 3, 13, 23], [3, 5, 199], [3, 3, 5, 67],
    [3, 3, 3, 5, 23], [2, 2, 2, 397], [2, 2, 2, 2, 199], [2, 23, 73],
    [2, 19, 89], [2, 2, 23, 37], [2, 2, 13, 67], [2, 2, 2, 19, 23],
    [2, 2, 2, 7, 67], [2, 5, 397], [2, 2, 5, 199], [2, 7, 13, 23],
    [2, 5, 19, 23], [2, 5, 7, 67], [2, 2, 3, 397], [2, 2, 2, 3, 199],
    [2, 3, 3, 3, 89], [2, 2, 2, 3, 3, 67], [2, 2, 2, 3, 3, 3, 23], [2, 3, 23, 37],
    [2, 3, 13, 67], [2, 2, 3, 19, 23], [2, 3, 3, 13, 23], [2, 2, 3, 7, 67],
    [2, 2, 3, 3, 7, 23], [2, 3, 5, 199], [2, 3, 3, 5, 67], [2, 3, 3, 3, 5, 23]]

private def evaluate : List ℕ → ℕ × ℕ
  | [] => (1, 1)
  | p :: rest =>
    let v := evaluate rest
    (p * v.1, nextPhi v.1 v.2 p)

private theorem evaluate_correct (factors : List ℕ) (hp : ∀ p ∈ factors, p.Prime) :
    (evaluate factors).1.totient = (evaluate factors).2 := by
  induction factors with
  | nil => decide
  | cons p rest ih =>
    have hp' := hp p (by simp)
    have h := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    change (p * (evaluate rest).1).totient = nextPhi (evaluate rest).1 (evaluate rest).2 p
    rw [← h]
    by_cases hd : p ∣ (evaluate rest).1
    · simpa [nextPhi,hd] using Nat.totient_mul_of_prime_of_dvd hp' hd
    · simpa [nextPhi,hd] using Nat.totient_mul_of_prime_of_not_dvd hp' hd

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem verify_offset (n : ℕ) (hm : n ∈ offsets) : n.totient = 1584 := by
  have cert : offsets.all (fun t => factorLists.any (fun f =>
      (evaluate f == (t,1584)) && f.all (fun p => decide p.Prime))) = true := by decide +kernel
  obtain ⟨f, _, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp cert n hm)
  obtain ⟨he,hp⟩ := Bool.and_eq_true_iff.mp hf
  have h := evaluate_correct f (fun p h => of_decide_eq_true (List.all_eq_true.mp hp p h))
  have hv : evaluate f = (n,1584) := beq_iff_eq.mp he
  rw [hv] at h
  exact h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem inverse_totient_1584 (n : ℕ) : n.totient = 1584 ↔ n ∈ offsets := by
  constructor
  · intro h
    have check : states.all (fun x => decide (x.2 = 1584 → x.1 ∈ offsets)) = true := by decide +kernel
    have hd : n.totient ∣ 1584 := h ▸ dvd_refl _
    have ok := List.all_eq_true.mp check (n,n.totient) (covered n hd)
    exact (of_decide_eq_true ok) h
  · intro h
    exact verify_offset n h

private theorem candidate_exponent_injective (b c : ℕ)
    (h : 5157 * 5158 ^ b + 1 = 5157 * 5158 ^ c + 1) : b = c := by
  have hm : 5157 * 5158 ^ b = 5157 * 5158 ^ c := Nat.add_right_cancel h
  have hp : (5158 : ℕ) ^ b = 5158 ^ c := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5157) hm
  exact Nat.pow_right_injective (by decide : 2 ≤ 5158) hp

/-- The same exact prime occurs for these forty offsets and no others at `k = 5157`. -/
theorem fixed_prime_iff (t : ℕ) : candidate (5157 + t) 5157 = largePrime ↔ t ∈ offsets := by
  rw [← inverse_totient_1584]
  unfold candidate largePrime
  rw [Nat.add_sub_cancel_left]
  constructor
  · intro h
    exact candidate_exponent_injective _ _ h
  · intro h
    rw [h]

theorem all_forty_prime (t : ℕ) (h : t ∈ offsets) : (candidate (5157+t) 5157).Prime := by
  rw [(fixed_prime_iff t).2 h]
  exact isPrime

theorem forty_distinct_offsets : offsets.length = 40 ∧ offsets.Nodup := by decide

end SunPrimeCertificates.Large
