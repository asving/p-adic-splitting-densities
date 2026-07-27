/-
Unit XB.4 t3Charge  [E-phase: stated, body sorry]
moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋
(derived…)"; exponential step proved in-unit, only Πe ≤ n rides (`HistWF.degProd`,
MovesSp-discharged). deps: XA.1. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t3Charge {n : ℕ} (H : XHistory n) (W : HistWF n H) (hn : 1 ≤ n) :
    countPop H .t3 ≤ Nat.log 2 n := by
  sorry

end LeanUrat.MovesX
