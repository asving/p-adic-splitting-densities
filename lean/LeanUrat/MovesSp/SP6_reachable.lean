/-
Unit Sp.n3reachable — moves_ref: "root selections (1,1)/(1,2)/(1,3) → stages
(1,1,1)/(1,1,2)/(1,1,3); ▸(2,1), ▸(3,1), e=2, e=3 → the four POST-INC W = 1
stages".
sketch: decide (53 × 21). Every non-root letter is one SuccStep from a ROOT
letter at n = 3. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem reachable3 : (catalogue3.all fun s' => rootAdmissibleB 3 s' ||
    groupR.any fun s => succStepB 3 s s') = true := sorry

end LeanUrat.MovesSp
