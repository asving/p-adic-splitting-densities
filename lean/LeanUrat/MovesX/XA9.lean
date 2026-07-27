/-
Unit XA.9 ind2Region  [E-phase: stated, body sorry]
moves_ref: the table's ind(S) column, EQUALITY (doubled per D2).
deps: XA.3–XA.8. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA3
import LeanUrat.MovesX.XA4
import LeanUrat.MovesX.XA5
import LeanUrat.MovesX.XA6
import LeanUrat.MovesX.XA7a
import LeanUrat.MovesX.XA7b
import LeanUrat.MovesX.XA8

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem ind2Region {n : ℕ} (ν : XNode n) (hc : ν.continuing) :
    ind2 ν = 2 * ν.region.card ∧ ((rowOf ν = .T1 ∨ rowOf ν = .T2) → 1 ≤ ind2 ν) := by
  sorry

end LeanUrat.MovesX
