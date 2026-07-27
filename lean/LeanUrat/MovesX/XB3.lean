/-
Unit XB.3 fourPop  [E-phase: stated, body sorry]
moves_ref: "{T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}" (coherence fields make
it typecheck). deps: XA.1. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem fourPop {n : ℕ} (H : XHistory n) :
    dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4 := by
  sorry

end LeanUrat.MovesX
