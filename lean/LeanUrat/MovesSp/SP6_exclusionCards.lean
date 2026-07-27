/-
Unit Sp.n3exclusionCards — moves_ref: "the 11 letters" / "exactly the 2 letters"
(the displayed counts).
sketch: rfl/decide. difficulty: easy. (Threshold-unit docstring duty: see
SP6_exclusionLists.lean.)
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem exclusion_cards : fieldSizeExcluded2.length = 11 ∧
    fieldSizeExcluded3.length = 2 := sorry

end LeanUrat.MovesSp
