/-
Unit Sp.n3closureStep [REV 4, Codex-6 — Bool-routed via List.contains] —
moves_ref: "the (G5) closure from the root stage (1,1,3) generates exactly the
five displayed stage groups … nothing further from Q2/Q3; W = 1 terminal by (G6)".
sketch: decide (≈53 × |enum3| succStepB evals — THE perf hotspot; pre-split into
5 per-group units if needed, blueprint §1.6). difficulty: medium (perf).
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem closure_step3 : (catalogue3.all fun s => (speciesEnum 3).all fun s' =>
    !(succStepB 3 s s') || catalogue3.contains s') = true := sorry

end LeanUrat.MovesSp
