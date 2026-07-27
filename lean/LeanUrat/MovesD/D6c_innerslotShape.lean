/-
Unit D6c.innerslot_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — inner slots from the retained width chain).
deps: Defs.
sketch: getElem?-elim; Matches e/g/Dwidth.  difficulty: easy.  hypothesis_fields: none.
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

/-- Inner slots are shape data. -/
theorem innerslot_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ r b, H.innerslotH r b = (P : ShapePrefix).innerslotS r b := by
  sorry

end LeanUrat.MovesD
