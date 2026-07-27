/-
Unit Sp.memCoherent — moves_ref: "the least set … that contains every
(G1)–(G4)+(G6)-coherent, (B1)–(B5)-admissible ROOT-stage tuple … (each generated
tuple again … admissible)".
sketch: induction on h; both constructors carry the conjuncts. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem InCatalogue.coherent_budget {n s} (h : InCatalogue n s) :
    Coherent s ∧ Budget n s := by
  cases h with
  | root ha => exact ha.2
  | step _ hstep => exact hstep.2

end LeanUrat.MovesSp
