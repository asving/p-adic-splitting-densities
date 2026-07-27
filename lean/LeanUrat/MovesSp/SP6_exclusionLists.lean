/-
Unit Sp.n3exclusionLists [REV 5, Codex rev-4 gap — one display each; the REV-4
literal-RHS pins and Bool routing unchanged, redistributed] — moves_ref: "p = 2
(one nonzero root): the 11 letters with λ ⊇ two distinct linears — {(1,1)²}: …;
{(1,2),(1,1)}: …; {(1,1)³}: …. p = 3 (two nonzero roots): exactly the 2 letters
with λ = {(1,1)³}."
sketch: decide (two 53-letter filters). difficulty: easy.
Docstring duty (all six threshold units): field-size pass is "NECESSARY for
realization, NOT sufficient"; N*₃ values are gate-censused data (M-n3-V2), never
theorems; realizability semantics stays out (§0).
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem exclusion_lists_pinned :
    catalogue3.filter (fun s => decide (2 ≤ linCount s)) = fieldSizeExcluded2 ∧
    catalogue3.filter (fun s => decide (3 ≤ linCount s)) = fieldSizeExcluded3 := sorry

end LeanUrat.MovesSp
