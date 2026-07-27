/-
Unit XA.3 t1Witness  [E-phase: stated, body sorry]
moves_ref: T1 witness "(s+e, u+(ℓ−1)h): ON S …" — the (P1) ON-OR-BELOW pin (§4 trap).
deps: XA.1. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t1Witness {n : ℕ} (ν : XNode n) (h1 : rowOf ν = .T1) :
    (ν.s0 + ν.e, ν.u0 + (ν.ell - 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card := by
  sorry

end LeanUrat.MovesX
