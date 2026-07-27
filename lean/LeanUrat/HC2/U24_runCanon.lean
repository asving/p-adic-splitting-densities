/-
Unit U24.readsOf_canonical  (HC-2 campaign, E-phase — blueprint §5 Layer D)
moves_ref: §D4-R "the classifier is run with ONE lift rule" + rev-6 canonRoot pinning.
deps: D4 (SideReads(v) — the E-phase decision BAKES `lift = polOM.liftOf` at every node
and `zbar = canonRoot` into the run predicate, so this unit is a PROJECTION).
difficulty: easy.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A classifier run carries the canonical presentation (polOM lifts + canonical roots at
every read). -/
theorem readsOf_canonical {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) : (polOM p F).IsCanonPres H := by
  sorry

end LeanUrat.MovesJ
