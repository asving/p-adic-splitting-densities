/-
Unit XA.7a latSlice  [E-phase: stated, body sorry]
moves_ref: (IND)'s region as column blocks (slice above rectangle; stride vertices
absorbed). deps: Defs. difficulty: HARD.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem latSlice (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) :
    (p1Region s0 u0 e h ell).card =
      ∑ k ∈ Finset.range ell,
        ((p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card
          + e * ((ell - 1 - k) * h)) := by
  sorry

end LeanUrat.MovesX
