/-
Unit Sp.collapseSublist [REV 4, Codex-13 — the rev-3 four-lemma unit split into
four] — moves_ref: "(the number of letters after collapsing self-loop runs)".
sketch: induction on the defining equations; if-branch via sublist-cons.
difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem collapseRuns_sublist (l : List Species) :
    (collapseRuns l).Sublist l := sorry

end LeanUrat.MovesSp
