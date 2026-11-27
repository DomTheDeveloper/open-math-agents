import CubeBound

namespace CubeBound

/-- Both the exact minimum margin and its unique index on the finite range. -/
private theorem small_table : ∀ k : Fin 64, 0 < k.val →
    2*k.val+1 ≤ count k.val ∧ (count k.val = 2*k.val+1 ↔ k.val = 2) := by
  native_decide

theorem small {n : ℕ} (hn : 0 < n) (ht : n < 64) :
    2*n+1 ≤ count n ∧ (count n = 2*n+1 ↔ n = 2) :=
  small_table ⟨n,ht⟩ hn

end CubeBound
