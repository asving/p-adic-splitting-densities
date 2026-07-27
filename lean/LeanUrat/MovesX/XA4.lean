/-
Unit XA.4 t1Arith  [E-phase: stated, body sorry]
moves_ref: T1 column bracket "[e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]".
deps: none (Defs only, for the namespace). difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) :
    e + h ≤ e * h * ell + 1 ∧ h * (ell - 1) ≤ e * h * ell + 1 - e - h ∧
    1 ≤ ell * (e * h * ell + 1 - e - h) := by
  sorry

end LeanUrat.MovesX
