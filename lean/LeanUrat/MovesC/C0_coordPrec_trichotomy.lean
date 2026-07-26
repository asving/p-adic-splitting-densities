/-
Unit C0.coordPrec_trichotomy  (moves_ref: §C.0 the global order ≺)
≺ (level ascending, index descending) is a strict linear order on ℕ×ℕ;
trichotomy by Nat trichotomy on levels then indices.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

theorem C0_coordPrec_trichotomy (c c' : Coord) : CoordPrec c c' ∨ c = c' ∨ CoordPrec c' c := by
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  simp only [CoordPrec, Prod.mk.injEq]
  omega

end LeanUrat.MovesC
