/-
Unit Sp.collapseEqSelf — moves_ref: "self-loop repetition counts (DEPTHS —
run-lengths of equal-species consecutive reads)" (collapse is identity exactly on
run-free words).
deps: Sp.collapseSublist. sketch: Mathlib `List.destutter_eq_self_iff` (the Defs
identity collapseRuns = destutter (· ≠ ·)), or direct induction.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem collapseRuns_eq_self_iff (l : List Species) :
    collapseRuns l = l ↔ l.Chain' (· ≠ ·) := sorry

end LeanUrat.MovesSp
