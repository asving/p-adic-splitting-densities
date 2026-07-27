/-
Unit Sp.collapseNeNil — moves_ref: "one marker letter + one depth slot per
maximal run" (a nonempty word keeps ≥ 1 marker letter).
sketch: induction; both branches of the two-head case keep a head.
difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem collapseRuns_ne_nil {l : List Species} (h : l ≠ []) :
    collapseRuns l ≠ [] := sorry

end LeanUrat.MovesSp
