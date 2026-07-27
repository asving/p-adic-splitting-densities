/-
Unit Sp.rankStepInc — moves_ref: "· e·g ≥ 2: D′ = e·g·D > D."
sketch: D′ = e·g·D ≥ 2·D > D (D ≥ 1). difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem rank_step_inc {n} {s s'} (h : SuccStep n s s')
    (hcb : Coherent s ∧ Budget n s) (hg : ∀ g μ, s.sel = some (g,μ) → 2 ≤ s.e * g) :
    s.D < s'.D := sorry

end LeanUrat.MovesSp
