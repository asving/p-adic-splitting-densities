/-
Unit XA.8 t34Zero  [E-phase: stated, body sorry]
moves_ref: T3/T4 zero rulings. FINDING-1 SEMANTICS: the "0" records that the table
supplies NO POSITIVE PER-SIDE BOUND at T3/T4 — NEVER "actual ind_r = 0".
deps: XA.1, XA.6. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1
import LeanUrat.MovesX.XA6

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- T3/T4 zero rulings: empty region and `ind2 = 0` — "no positive per-side bound",
never "actual index zero" (finding-1 semantics). -/
theorem t34Zero {n : ℕ} (ν : XNode n) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) :
    ν.region.card = 0 ∧ ind2 ν = 0 := by
  sorry

end LeanUrat.MovesX
