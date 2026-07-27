/-
Unit D8.band_shape  (MovesD campaign, E-phase)
moves_ref: (L9's per-read exponent — `inFreshBand` is §C C.1(ii)'s inventory; all three
conjuncts shape formulas).
deps: D6d, D6e, D7b, D7c (coherence via `J.coherent`).
sketch: conjunct-wise transfer.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {P : Shape n}

/-- The fresh band is the shape band, coordinate for coordinate. -/
theorem band_shape {H : History p F} {J : JetSetup H n N m}
    (hP : (P : ShapePrefix).MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (c : Fin m) :
    inFreshBand H n J.coordOf r (H.nodes[r]'hr) c
      ↔ (P : ShapePrefix).bandS n r (J.coordOf c) := by
  sorry

end LeanUrat.MovesD
