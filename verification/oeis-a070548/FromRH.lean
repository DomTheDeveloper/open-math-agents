import Signs
import Mobius
import Mertens
import Main

namespace MobiusSigns

open Filter Finset ArithmeticFunction Asymptotics
open scoped Topology ArithmeticFunction.Moebius

private theorem formula (n : ℕ) :
    mass n = ∑ d ∈ Icc 1 n.sqrt, μ d * ((n/d^2 : ℕ) : ℤ) := by
  unfold mass
  simpa only [Squarefree.Mob.count_multiples 1 n _ le_rfl, Nat.sub_self, Nat.zero_div,
    Nat.sub_zero] using Squarefree.Mob.interval_sqf_eq 1 n le_rfl

private theorem bigO (rh : RiemannHypothesis) (ε : ℝ) (he : 0 < ε) :
    gap =O[atTop] fun n : ℕ => (n:ℝ)^(1/2+ε) := by
  have h := ((Mertens.mertens_of_RH rh) ε he).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hg (n : ℕ) : gap n = (Mertens.mertens ↑n : ℝ) := by
    simp only [gap,Mertens.mertens,Nat.floor_natCast]
    exact_mod_cast (counts n).2
  simpa only [Function.comp_def,← hg] using h

theorem sign_counts :
    Tendsto (fun n : ℕ => ((countSign 1 n : ℝ) + countSign (-1) n)/n)
      atTop (𝓝 (6/Real.pi^2)) ∧
    (RiemannHypothesis → ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N,
      |(countSign 1 n : ℝ)-countSign (-1) n| < (n:ℝ)^(1/2+ε)) ∧
    Tendsto (fun n : ℕ => (countSign 1 n : ℝ)/n) atTop (𝓝 (3/Real.pi^2)) := by
  have hm := density formula Squarefree.Mob.tsum_moebius_div_sq
  exact ⟨hm, fun rh ε he => eventually_atTop.mp (imbalance (bigO rh) ε he),
    positive_density hm (imbalance (bigO riemannHypothesis) (1/4) (by norm_num))⟩

#print axioms sign_counts
end MobiusSigns
