/-
Unit D6a.strFrame_shape  (MovesD campaign, E-phase)
moves_ref: (L9's "SHAPE data" — STR_i = ∏_{m<i} e_m).
deps: Defs.
sketch: List.take/map congruence from Matches' e-clause.  difficulty: easy.
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

/-- The history stretch is shape data. -/
theorem strFrame_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i, H.strFrame i = (P : ShapePrefix).strS i := by
  sorry

end LeanUrat.MovesD
