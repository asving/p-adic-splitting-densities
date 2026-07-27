/-
Unit XA.7b latGen  [E-phase: stated, body sorry]
moves_ref: "(IND) ind(S) = ½·ℓ·(ehℓ − e − h + 1)" + example anchors
(ℓ = 1 ↦ XA.6; e = h = ℓ = 1 ↦ 0). deps: XA.6, XA.7a. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA6
import LeanUrat.MovesX.XA7a

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem latGen (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell)
    (hcop : Nat.Coprime e h) :
    2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 - e - h) := by
  sorry

/-- anchor: at ℓ = 1 the display is XA.6's. -/
example (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) :
    2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1) := by
  sorry

/-- anchor: e = h = ℓ = 1 ↦ 0. -/
example (s0 u0 : ℕ) : 2 * (p1Region s0 u0 1 1 1).card = 0 := by
  sorry

end LeanUrat.MovesX
