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
    (collapseRuns l).Sublist l := by
  induction l using collapseRuns.induct with
  | case1 => simp [collapseRuns]
  | case2 s => simp [collapseRuns]
  | case3 s' rest ih =>
      simp only [collapseRuns]
      exact ih.cons s'
  | case4 s s' rest h ih =>
      simp only [collapseRuns, if_neg h]
      exact ih.cons_cons s

end LeanUrat.MovesSp
