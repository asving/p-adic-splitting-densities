/-
Unit XA.5 t2Witness  [E-phase: stated, body sorry]
moves_ref: T2 witness "(s+1, u+1) … gcd(e,h) = 1 excludes (2,2)".
deps: XA.1. difficulty: MEDIUM (EASY-MEDIUM band).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t2Witness {n : ℕ} (ν : XNode n) (h2 : rowOf ν = .T2) :
    (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e - 1) * (ν.h - 1) ∧
    2 ∣ (ν.e - 1) * (ν.h - 1) := by
  sorry

end LeanUrat.MovesX
