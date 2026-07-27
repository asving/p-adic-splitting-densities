/-
Unit Sp.n3multiSideMem — moves_ref: "the sel-carrying Q3 copies" (six DISTINCT
letters of group Q3).
sketch: decide; Nodup rules out repeated letters (the C-8 repeat scenario).
difficulty: easy. (Threshold-unit docstring duty: see SP6_exclusionLists.lean.)
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem multiSide6_mem : (multiSide6.all groupQ3.contains) = true
    ∧ multiSide6.Nodup := sorry

end LeanUrat.MovesSp
