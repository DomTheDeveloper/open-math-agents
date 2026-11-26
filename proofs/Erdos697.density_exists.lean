import FormalConjectures.ErdosProblems.«697»

/-! The admissible divisors all divide one factorial. Counting complete periods
and the final partial period gives the natural density. -/

open Filter Set
open scoped Topology

namespace OMA.Density

/-- Full blocks and the last incomplete block give an exact counting formula. -/
private theorem count_blocks (S : Set ℕ) [DecidablePred (· ∈ S)] (M : ℕ)
    (period : ∀ i, M + i ∈ S ↔ i ∈ S) (q r : ℕ) :
    Nat.count (· ∈ S) (M * q + r) = q * Nat.count (· ∈ S) M + Nat.count (· ∈ S) r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have step : Nat.count (· ∈ S) (M + (M * q + r)) =
        Nat.count (· ∈ S) M + Nat.count (· ∈ S) (M * q + r) := by
      rw [Nat.count_add]
      simp only [Nat.count_eq_card_filter_range, period]
    rw [show M * (q + 1) + r = M + (M * q + r) by ring, step, ih]
    ring

private theorem periodic_density (S : Set ℕ) (M : ℕ) (hM : 0 < M)
    (period : ∀ i, M + i ∈ S ↔ i ∈ S) :
    ∃ δ, S.HasDensity δ := by
  classical
  let C := Nat.count (· ∈ S)
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  let d : ℝ := C M / (M : ℝ)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    apply (div_le_one hMR).2
    exact_mod_cast (Nat.count_le (p := (· ∈ S)) (n := M))
  have hMd : (M : ℝ) * d = C M := by dsimp [d]; field_simp
  refine ⟨d, ?_⟩
  have hcount (n : ℕ) : (S ∩ Iio n).ncard = C n := by
    change _ = Nat.count (· ∈ S) n
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [and_comm]
  have bound (n : ℕ) (hn : 0 < n) : |(C n : ℝ) / n - d| ≤ (M : ℝ) / n := by
    let q := n / M
    let r := n % M
    have hr : r ≤ M := (Nat.mod_lt _ hM).le
    have hq : M * q + r = n := Nat.div_add_mod n M
    have hc : C n = q * C M + C r := hq ▸ count_blocks S M period q r
    have hc' : (C n : ℝ) = q * (C M : ℝ) + C r := by exact_mod_cast hc
    have hq' : (M : ℝ) * q + r = n := by exact_mod_cast hq
    have hdiff : (C n : ℝ) - d * n = C r - d * r := by
      rw [hc', ← hq', ← hMd]
      ring
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [show (C n : ℝ)/n - d = ((C n : ℝ) - d*n)/n by field_simp, abs_div, abs_of_pos hn', div_le_div_iff_of_pos_right hn', hdiff, abs_le]
    have hcr : (C r : ℝ) ≤ M := by exact_mod_cast ((Nat.count_le (p := (· ∈ S)) (n := r)).trans hr : C r ≤ M)
    have hr' : (r : ℝ) ≤ M := by exact_mod_cast hr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg r), Nat.cast_nonneg (C r)]
    · nlinarith [mul_nonneg hd0 (Nat.cast_nonneg r)]
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, Nat.ncard_Iio, hcount]
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (eventually_atTop.2 ⟨1, fun n hn => by simpa [Real.dist_eq] using bound n hn⟩)
  simpa [div_eq_mul_inv] using (tendsto_one_div_atTop_nhds_zero_nat.const_mul (M : ℝ))

end OMA.Density

theorem OMA.solution : type_of% @Erdos697.density_exists := by
  intro m α
  let B : ℝ := Real.exp ((m : ℝ) ^ α)
  obtain ⟨N, hN⟩ := exists_nat_gt B
  apply OMA.Density.periodic_density _ (N.factorial) (Nat.factorial_pos N)
  intro i
  constructor
  · rintro ⟨d, hd, hb, hdiv⟩
    have hle : d ≤ N := by exact_mod_cast (hb.2.trans hN).le
    have hpos : 0 < d := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ) < 1) hb.1)
    exact ⟨d, hd, hb, (Nat.dvd_add_iff_right (Nat.dvd_factorial hpos hle)).mpr hdiv⟩
  · rintro ⟨d, hd, hb, hdiv⟩
    have hle : d ≤ N := by exact_mod_cast (hb.2.trans hN).le
    have hpos : 0 < d := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ) < 1) hb.1)
    exact ⟨d, hd, hb, dvd_add (Nat.dvd_factorial hpos hle) hdiv⟩
