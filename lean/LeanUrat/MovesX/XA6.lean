/-
Unit XA.6 lat1  [E-phase: stated, body sorry]
moves_ref: "strict-interior count (EH−E−H−d)/2 + 1, on-side non-vertex count d − 1"
at ℓ = 1. sketch: center-reflection involution + no on-segment points (coprime).
deps: Defs. difficulty: HARD.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem lat1 (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) :
    2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1) := by
  sorry

end LeanUrat.MovesX
