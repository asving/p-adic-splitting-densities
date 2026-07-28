/-
Unit U11.root_height_of_inBox  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.root_height` docstring ("D.4's ROOT case: every side slope
≥ 1; the cluster zeros pin level 0, floor height 1").
deps: MovesD `InBox` (E-phase core).  difficulty: medium.  hypothesis_fields: hbox, hd4.
RISK (blueprint, pre-declared flex point): if MovesD's `InBox` turns out weaker than the
height bound, this unit's hypothesis must be upgraded to the D.4 root clause —
statement-fence event, sign-off required (never prove from junk).
N-5 RESTATEMENT (2026-07-28, sign-off round — §9 F-6 executed; the pre-declared RISK
FIRED): the unit was UNPROVABLE-AND-REFUTABLE as stated (a one-node coherent in-box
history with `ustar := −5` satisfies every hypothesis and fails the conclusion —
`ShapeWF` carries no height law; NO value bound on `ustar` exists anywhere in the
corpus, grep-confirmed corpus-wide at F-6). GAINS `hd4 : RootD4 H` (Defs N-5 addendum =
§B2-DEF D.4's root clause). Derivation route (F-6's sketch, records why the two
conjuncts suffice): root `Dwidth = 1` (hroot + hDwidth) and `STR = 1` give `slope = h/e`,
so `1 ≤ slope` IS D.4's "every side slope ≥ 1"; every interior base `b < μ·childWidth`
sits at least one step left of the vertex base, whence `line.at b ≥ ustar + slope ≥ 1`
by `hLineU`. Proof queued for the fleet round; the Shape-side alternative was REJECTED
(frozen MovesD Defs; silent shape-universe shrink).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The root line dominates the cluster floor (verbatim `JetSetup.root_height`'s type;
N-5: under the D.4 root clause `hd4`). -/
theorem root_height_of_inBox {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {H : History p F} (hcoh : HistoryCoherent H) (hbox : InBox n H)
    (hd4 : RootD4 H) :
    ∀ (hj : 0 < H.nodes.length) (b : ℕ),
      b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth →
      1 ≤ (H.nodes[0]'hj).line.at b := by
  sorry

end LeanUrat.MovesJ
