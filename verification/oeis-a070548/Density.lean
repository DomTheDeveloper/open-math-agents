import Mathlib

namespace MobiusSigns

open Filter Finset ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius

noncomputable def countSign (s : ℤ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => μ k = s)).card

def mass (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, if Squarefree k then 1 else 0

theorem counts (n : ℕ) :
    (countSign 1 n : ℤ) + countSign (-1) n = mass n ∧
    (countSign 1 n : ℤ) - countSign (-1) n = ∑ k ∈ Icc 1 n, μ k := by
  classical
  have one (s : ℤ) : (countSign s n : ℤ) =
      ∑ k ∈ Icc 1 n, if μ k = s then (1:ℤ) else 0 := by
    simp [countSign, ← Finset.sum_filter]
  rw [one,one, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  constructor <;> apply Finset.sum_congr rfl <;> intro k hk <;>
    rcases ArithmeticFunction.moebius_eq_or k with h|h|h <;>
    simp [h, ← ArithmeticFunction.moebius_ne_zero_iff_squarefree]

private theorem divratio {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => ((n/q : ℕ) : ℝ) / n) atTop (𝓝 (1/(q:ℝ))) := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hzero := (tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop))
  have hlow : Tendsto (fun n : ℕ => 1/(q:ℝ) - 1/n) atTop (𝓝 (1/(q:ℝ))) := by
    simpa [one_div,Function.comp_def] using
      (tendsto_const_nhds (x := 1/(q:ℝ)) (f := (atTop : Filter ℕ))).sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have h : n < (n/q+1)*q := by
      have hm := Nat.mod_lt n hq
      have hd := Nat.mod_add_div n q
      nlinarith only [hm,hd]
    have hc : (n : ℝ) < (((n/q : ℕ) : ℝ)+1)*q := by exact_mod_cast h
    apply (le_div_iff₀ hn').2
    field_simp [hq'.ne',hn'.ne'] at * <;> nlinarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    apply (div_le_iff₀ hn').2
    simpa [div_eq_mul_inv,mul_comm] using (Nat.cast_div_le (m := n) (n := q) (α := ℝ))

set_option maxHeartbeats 1600000 in
/-- Dominated convergence applied to the square-divisor expansion, including d=0. -/
theorem density
    (formula : ∀ n, mass n = ∑ d ∈ Icc 1 n.sqrt, μ d * ((n/d^2 : ℕ) : ℤ))
    (euler : (∑' d : ℕ, (μ d : ℝ)/(d:ℝ)^2) = 6/Real.pi^2) :
    Tendsto (fun n : ℕ => ((countSign 1 n : ℝ) + countSign (-1) n)/n) atTop
      (𝓝 (6/Real.pi^2)) := by
  let f (n d : ℕ) : ℝ := (μ d : ℝ)*(((n/d^2 : ℕ):ℝ)/n)
  have hSummable : Summable (fun d : ℕ => 1/(d:ℝ)^2) := by
    simpa using (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have point (d : ℕ) : Tendsto (fun n => f n d) atTop (𝓝 ((μ d : ℝ)/(d:ℝ)^2)) := by
    by_cases hd : d = 0
    · subst d; simp [f]
    · have ht := (divratio (q:=d^2) (by positivity)).const_mul (μ d : ℝ)
      simpa only [f,Nat.cast_pow,div_eq_mul_inv,one_mul] using ht
  have dom : ∀ᶠ n : ℕ in atTop, ∀ d, ‖f n d‖ ≤ 1/(d:ℝ)^2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn d
    have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hu : |(μ d : ℝ)| ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with h|h|h <;> simp [h]
    dsimp only [f]; rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((n/d^2:ℕ):ℝ)/n)]
    calc
      _ ≤ 1*(((n/d^2:ℕ):ℝ)/n) := mul_le_mul_of_nonneg_right hu (by positivity)
      _ ≤ _ := by
        rw [one_mul,div_le_iff₀ hn']
        calc
          ((n / d^2 : ℕ) : ℝ) ≤ (n:ℝ)/((d^2:ℕ):ℝ) := Nat.cast_div_le
          _ = 1/(d:ℝ)^2 * n := by rw [Nat.cast_pow]; ring
  have ht := tendsto_tsum_of_dominated_convergence hSummable point dom
  rw [euler] at ht
  apply ht.congr
  intro n
  change (∑' d, f n d) = _
  rw [tsum_eq_sum (s:=Icc 1 n.sqrt)]
  · have hh := (counts n).1.trans (formula n)
    have hr := congrArg (fun z : ℤ => (z:ℝ)) hh
    simp only [Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hr
    rw [hr,Finset.sum_div]
    apply Finset.sum_congr rfl; intro d _; simp [f,mul_div_assoc]
  · intro d hd
    by_cases hzero : d = 0
    · subst d; simp [f]
    · have hl : n.sqrt < d := by
        by_contra! he
        exact hd (mem_Icc.mpr ⟨by omega,he⟩)
      have hlt : n < d^2 := Nat.sqrt_lt'.mp hl
      simp [f,Nat.div_eq_of_lt hlt]

end MobiusSigns
