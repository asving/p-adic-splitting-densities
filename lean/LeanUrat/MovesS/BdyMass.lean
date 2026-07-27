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
      (∑ r ∈ Finset.Icc 0 fe, μm r) + (∑ r ∈ Finset.Icc (fe + 1) L, μm r) :=
  sorry

end LeanUrat.MovesS
