/-
Unit Sp.n3multiSide6 [REV 4, Codex-8 pin: RHS = literal Species terms
transcribing the note's rows; field order: tag, D, w, W, e, s0, ell, a, d, slots,
lam, sel, lflank, rflank] — moves_ref: "the exceptions are the multi-side μ = 3
letters — the sel-carrying Q3 copies whose child window [0,3] has ≥ 2 sides:
Q3(R1, right flank (1,1)), Q3(R2), Q3(R3, left flank (1,1)), and the three
Q3(R4) λ-rows" + the R1–R4 group-R row displays.
sketch: decide (list of literals). difficulty: easy. (Threshold-unit docstring
duty: see SP6_exclusionLists.lean.)
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem multiSide6_pinned : multiSide6 =
    [⟨.postRec, 1, 1, 3, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1,1)}, some (1,1),
       [], [1,1]⟩,                                        -- Q3(R1), rf (1,1)
     ⟨.postRec, 1, 1, 3, 1, 1, 1, 1, 2, Finset.Icc 1 2, {(1,1)}, some (1,1),
       [1], [1]⟩,                                         -- Q3(R2)
     ⟨.postRec, 1, 1, 3, 1, 2, 1, 2, 2, Finset.Icc 2 3, {(1,1)}, some (1,1),
       [1,1], []⟩,                                        -- Q3(R3), lf (1,1)
     ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(2,1)}, some (2,1),
       [], [1]⟩,                                          -- Q3(R4) ▸(2,1)
     ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,2)}, some (1,2),
       [], [1]⟩,                                          -- Q3(R4) ▸(1,2)
     ⟨.postRec, 1, 1, 3, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1,1),(1,1)},
       some (1,1), [], [1]⟩]                              -- Q3(R4) ▸(1,1)
    := by rfl

end LeanUrat.MovesSp
