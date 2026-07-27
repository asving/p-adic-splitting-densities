/-
Unit Sp.n3NstarValues — moves_ref: "THE SIX COMPUTATIONS (all at p = 3 — the
labels are N*_3): … the three Q3(R4)-copies …: N*_3 = 6; · Q3(R2)/Q3(R3)-copies
…: N*_3 = 6; · the Q3(R1)-copy …: N*_3 = 7."
sketch: six rfl/decide reads of the table. difficulty: easy. N*₃ values are
gate-censused DATA (M-n3-V2) + a SEALED PREDICTION, never theorems (§0); the
field-size pass is NECESSARY for realization, NOT sufficient.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem nstar_values : Nstar3six msQ3R1 = some 7 ∧
    Nstar3six msQ3R2 = some 6 ∧ Nstar3six msQ3R3 = some 6 ∧
    Nstar3six msQ3R4a = some 6 ∧ Nstar3six msQ3R4b = some 6 ∧
    Nstar3six msQ3R4c = some 6 := sorry

end LeanUrat.MovesSp
