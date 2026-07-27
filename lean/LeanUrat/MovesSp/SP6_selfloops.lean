/-
Unit Sp.n3selfloops [REV 3, C1 — target reordered to catalogue3's pinned order:
loopQ3 ∈ groupQ3 precedes loopQ23 ∈ groupQ2 in groupR ++ groupQ3 ++ groupQ2 ++
groupQ1 ++ groupI] — moves_ref: "SELF-LOOPS: Q2.3▸(1,2) → Q2 (the μ = 2 loop)
and Q3's ▸(1,3) rows → Q3 (the μ = 3 loop) — exactly two loop classes at n = 3,
both POST-REC".
sketch: decide. Cross-check `Sp.selfloopFull`: both are the full POST-REC
letters. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem loops3 : catalogue3.filter (fun s => succStepB 3 s s) =
    [loopQ3, loopQ23] := sorry

end LeanUrat.MovesSp
