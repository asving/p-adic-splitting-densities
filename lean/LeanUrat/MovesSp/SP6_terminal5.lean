/-
Unit Sp.n3terminal5 — moves_ref: "The five W = 1 letters of SP.6 have
Out(s) = V_term exactly." + "W = 1 letters read the confirming side … and are
TERMINAL: selection ⊥".
sketch: decide ×3 (5 letters + the (G6) instance + empty menus = the
closure-marker face; V_term itself is unconditional in Out's definition).
ORDER DISCIPLINE: terminal3's pinned list groupQ1 ++ groupI is in catalogue3
order. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem terminal3 : catalogue3.filter (fun s => s.W == 1) =
    groupQ1 ++ groupI ∧ (catalogue3.all fun s => (s.W == 1) == (s.sel == none)) =
    true ∧ ((groupQ1 ++ groupI).all fun s => catalogue3.all fun s' =>
    !(succStepB 3 s s')) = true := sorry

end LeanUrat.MovesSp
