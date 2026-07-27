/-
Unit D6e.prevRim_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — the rim thresholds μ_{i−1}·D_i are shape data).
deps: Defs.
sketch: case split on i; getElem?-elim; Matches μ/e/g/Dwidth.  difficulty: easy.
hypothesis_fields: none.
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

/-- The rim thresholds are shape data. -/
theorem prevRim_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i, H.prevRim n i = (P : ShapePrefix).prevRimS n i := by
  sorry

end LeanUrat.MovesD
