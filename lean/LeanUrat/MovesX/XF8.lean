/-
Unit XF.8 tailZero — UNCONDITIONAL  [E-phase: stated, body sorry]
moves_ref: "→ 0 as D → ∞".
sketch: tailExp → ∞ linearly; geometric squeeze. deps: XF.7. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF7

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem tailZero (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) :
    Filter.Tendsto (fun D => (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D))
      Filter.atTop (nhds 0) := by
  sorry

end LeanUrat.MovesX
