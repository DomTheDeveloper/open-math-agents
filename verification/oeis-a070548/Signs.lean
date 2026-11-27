import Density

namespace MobiusSigns

open Filter Finset ArithmeticFunction Asymptotics
open scoped Topology ArithmeticFunction.Moebius

noncomputable def gap (n : ℕ) : ℝ := (countSign 1 n : ℝ) - countSign (-1) n

theorem imbalance
    (estimate : ∀ ε : ℝ, 0<ε → gap =O[atTop] fun n : ℕ => (n:ℝ)^(1/2+ε))
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |gap n| < (n:ℝ)^(1/2+ε) := by
  obtain ⟨C, _, hC⟩ := (estimate (ε/2) (half_pos he)).exists_pos
  have ht := (tendsto_rpow_atTop (half_pos he)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [hC.bound, ht.eventually_gt_atTop C, eventually_ge_atTop 1] with n hn hpow hn1
  have hx : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  simp only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx _)] at hn
  calc
    |gap n| ≤ C * (n:ℝ)^(1/2+ε/2) := hn
    _ < (n:ℝ)^(ε/2) * (n:ℝ)^(1/2+ε/2) := by
      exact mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hx _)
    _ = (n:ℝ)^(1/2+ε) := by rw [← Real.rpow_add hx]; congr 1; ring

theorem positive_density
    (massLimit : Tendsto (fun n : ℕ => ((countSign 1 n : ℝ) + countSign (-1) n)/n)
      atTop (𝓝 (6/Real.pi^2)))
    (imb : ∀ᶠ n : ℕ in atTop, |gap n| < (n:ℝ)^(1/2+(1/4:ℝ))) :
    Tendsto (fun n : ℕ => (countSign 1 n : ℝ)/n) atTop (𝓝 (3/Real.pi^2)) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hgap : Tendsto (fun n : ℕ => gap n/n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
    filter_upwards [imb,eventually_ge_atTop 1] with n h hn
    have hx : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hx]
    change _ ≤ (n:ℝ)^(-(1/4:ℝ))
    apply (div_le_iff₀ hx).2
    have he : (n:ℝ)^(-(1/4:ℝ)) * n = (n:ℝ)^(1/2+(1/4:ℝ)) := by
      calc
        _ = (n:ℝ)^(-(1/4:ℝ)) * (n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hx]; congr 1; ring
    rw [he]; exact h.le
  have h := (massLimit.add hgap).div_const 2
  convert h using 1
  · funext n; dsimp [gap]; ring
  · ring

end MobiusSigns
