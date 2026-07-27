/-
Unit Sp.n3R3check [REV 2, F6 — BOTH flank variants, as the two named letters of
DefsN3] — moves_ref: "R3 = (ROOT, (D,w,W) = (1,1,3), e = 1, ℓ = 1, a = 2,
s₀′ = 2, slots {2,3}, λ = {(1,1)} ▸ (1,1), left flank (2) or (1,1), right empty)"
+ "(B5, corrected anchor bound) a = 2 ≤ ⌊(W − w′)/e⌋ = 2 ✓ (saturated)".
sketch: decide — the note's own saturating witnesses for the corrected (B5), one
per flank composition. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem R3_members : coherentB R3letterA = true ∧
    budgetB 3 R3letterA = true ∧ R3letterA ∈ groupR ∧ R3letterA.a = 2 ∧
    R3letterA.lflank = [2] ∧ coherentB R3letterB = true ∧
    budgetB 3 R3letterB = true ∧ R3letterB ∈ groupR ∧ R3letterB.a = 2 ∧
    R3letterB.lflank = [1, 1] := by decide

end LeanUrat.MovesSp
