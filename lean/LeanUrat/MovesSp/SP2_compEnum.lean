/-
Unit Sp.compEnumComplete — moves_ref: "each flank is a composition of its span"
(G1).
sketch: strong induction on span; compEnum span = [[]] at 0, else first-part
split. difficulty: medium. [REV 4, Codex-11 — compEnum_nodup spelled.]
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem compEnum_complete {span : ℕ} {c : List ℕ} :
    IsComposition c span ↔ c ∈ compEnum span := sorry

theorem compEnum_nodup (span : ℕ) : (compEnum span).Nodup := sorry

end LeanUrat.MovesSp
