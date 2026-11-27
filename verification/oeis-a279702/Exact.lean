import Champions
import Eight

namespace RobinSigns

private theorem as_finset : RobinChampions.listed.toFinset.card = 8 := by decide +kernel

theorem negative_arguments
    (prefixClass : ∀ n ≤ 5040, RobinChampions.IsCA n ↔ n ∈ RobinChampions.listed)
    (tail : ∀ {n : ℕ}, 5040 < n → 0 ≤ residual n) (n : ℕ) :
    (RobinChampions.IsCA n ∧ residual n < 0) ↔ n ∈ RobinChampions.listed := by
  have bounded : ∀ k ∈ RobinChampions.listed, k ≤ 5040 := by decide +kernel
  constructor
  · rintro ⟨ca,neg⟩
    have hle : n ≤ 5040 := le_of_not_gt fun h => neg.not_ge (tail h)
    exact (prefixClass n hle).mp ca
  · intro h
    exact ⟨(prefixClass n (bounded n h)).mpr h, eight_negative n h⟩

/-- For the increasing enumeration (array offset zero), the negative indices are 0,...,7.
The OEIS display adds 2, giving indices 2,...,9. -/
theorem index_iff
    (prefixClass : ∀ n ≤ 5040, RobinChampions.IsCA n ↔ n ∈ RobinChampions.listed)
    (tail : ∀ {n : ℕ}, 5040 < n → 0 ≤ residual n)
    (a : ℕ → ℕ) (ha : StrictMono a)
    (enumerates : ∀ n, RobinChampions.IsCA n ↔ ∃ i, a i = n) (i : ℕ) :
    residual (a i) < 0 ↔ i < 8 := by
  have upto : ∀ k ∈ RobinChampions.listed, k ≤ 5040 := by decide +kernel
  have last : 5040 ∈ RobinChampions.listed := by decide
  obtain ⟨j,hj⟩ := (enumerates _).mp ((prefixClass _ le_rfl).mpr last)
  have hset : (Finset.range (j+1)).image a = RobinChampions.listed.toFinset := by
    ext k
    rw [List.mem_toFinset, Finset.mem_image]
    constructor
    · rintro ⟨u,hu,rfl⟩
      have huv : u ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
      exact (prefixClass _ ((ha.monotone huv).trans hj.le)).mp ((enumerates _).mpr ⟨u,rfl⟩)
    · intro mem
      have hle := upto k mem
      obtain ⟨u,hu⟩ := (enumerates _).mp ((prefixClass _ hle).mpr mem)
      have hui : u ≤ j := ha.le_iff_le.mp (by simpa only [hu,hj] using hle)
      exact ⟨u,Finset.mem_range.mpr (by omega),hu⟩
  have hc := congrArg Finset.card hset
  rw [Finset.card_image_of_injective _ ha.injective,Finset.card_range,as_finset] at hc
  have ca := (enumerates _).mpr (show ∃ k, a k = a i from ⟨i,rfl⟩)
  constructor
  · intro neg
    have hle := upto _ ((negative_arguments prefixClass tail _).mp ⟨ca,neg⟩)
    have hij : i ≤ j := ha.le_iff_le.mp (by simpa only [hj] using hle)
    omega
  · intro hi
    have hle := (ha.monotone (show i ≤ j by omega)).trans hj.le
    exact ((negative_arguments prefixClass tail _).mpr ((prefixClass _ hle).mp ca)).2

end RobinSigns
