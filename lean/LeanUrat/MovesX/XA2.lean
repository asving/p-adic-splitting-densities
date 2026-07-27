/-
Unit XA.2 selForce  [E-phase: stated, body sorry]
moves_ref: "μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side".
deps: XA.1. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem selForce {n : ℕ} (ν : XNode n) (g μ : ℕ) (hs : ν.sel = some (g, μ))
    (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell ∧ rowOf ν = .T1 := by
  sorry

end LeanUrat.MovesX
