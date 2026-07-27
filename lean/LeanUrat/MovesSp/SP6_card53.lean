/-
Unit Sp.n3card53 — moves_ref: "|𝒮₃^raw| = 21 + 21 + 6 + 1 + 4 = 53."
sketch: rfl/decide (Nodup by `decide`; length by `rfl`). difficulty: easy.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem catalogue3_card : catalogue3.length = 53 ∧ catalogue3.Nodup := sorry

theorem groups_card : groupR.length = 21
    ∧ groupQ3.length = 21 ∧ groupQ2.length = 6 ∧ groupQ1.length = 1
    ∧ groupI.length = 4 := sorry

end LeanUrat.MovesSp
