/-
Unit U-7c `bdy_mass_split` (easy) — the (BDY) mass split.
moves_ref: "no read omitted, none double-charged".
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem bdy_mass_split (μm : ℕ → ℝ) (L fe : ℕ) (h : fe ≤ L) :
    ∑ r ∈ Finset.range (L + 1), μm r =
      (∑ r ∈ Finset.Icc 0 fe, μm r) + (∑ r ∈ Finset.Icc (fe + 1) L, μm r) := by
  have hsplit : Finset.range (L + 1) = Finset.Icc 0 fe ∪ Finset.Icc (fe + 1) L := by
    ext r; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 0 fe) (Finset.Icc (fe + 1) L) := by
    rw [Finset.disjoint_left]; intro r hr1 hr2
    simp only [Finset.mem_Icc] at hr1 hr2; omega
  rw [hsplit, Finset.sum_union hdisj]

end LeanUrat.MovesS
