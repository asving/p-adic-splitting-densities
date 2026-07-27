/-
Unit Sp.reflBudget — moves_ref: "(B1)–(B5) are inequalities between INTEGERS
attached to shape fields".
sketch: as reflCoherent. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem budgetB_iff (n : ℕ) (s : Species) : budgetB n s = true ↔ Budget n s := sorry

end LeanUrat.MovesSp
