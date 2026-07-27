/-
Unit XD.2 x2hypCount  [E-phase: stated, body sorry]
moves_ref: "Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read
history is carried by the +1" (unconditional; empty case both sides 0).
deps: Defs. difficulty: MEDIUM. hyp: HistWF.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x2hypCount {n : ℕ} (H : XHistory n) (W : HistWF n H) :
    sumH H ≤ (dTotal H + 1) * maxH H := by
  sorry

end LeanUrat.MovesX
