/-
Unit U11.root_height_of_inBox  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.root_height` docstring ("D.4's ROOT case: every side slope
≥ 1; the cluster zeros pin level 0, floor height 1").
deps: MovesD `InBox` (E-phase core).  difficulty: medium.  hypothesis_fields: hbox.
RISK (blueprint, pre-declared flex point): if MovesD's `InBox` turns out weaker than the
height bound, this unit's hypothesis must be upgraded to the D.4 root clause —
statement-fence event, sign-off required (never prove from junk).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The root line dominates the cluster floor (verbatim `JetSetup.root_height`'s type). -/
theorem root_height_of_inBox {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {H : History p F} (hcoh : HistoryCoherent H) (hbox : InBox n H) :
    ∀ (hj : 0 < H.nodes.length) (b : ℕ),
      b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth →
      1 ≤ (H.nodes[0]'hj).line.at b := by
  sorry

end LeanUrat.MovesJ
