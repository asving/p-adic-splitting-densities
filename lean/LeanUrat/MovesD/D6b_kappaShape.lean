/-
Unit D6b.kappaH_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — κ_r = h_r/(e_r·STR_r) is shape data).
deps: D6a.
sketch: getElem?-elim; Matches e/h + D6a.  difficulty: easy.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {P : Shape n}

/-- The level weights κ_r are shape data. -/
theorem kappaH_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ r, H.kappaH r = (P : ShapePrefix).kappaS r := by
  sorry

end LeanUrat.MovesD
