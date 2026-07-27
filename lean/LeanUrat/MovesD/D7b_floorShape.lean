/-
Unit D7b.floorH_shape  (MovesD campaign, E-phase)
moves_ref: "the fresh inventory's strip depths run between the recorded old/new lines,
each pinned only WITH its height" (L9 rev 9).
deps: D7a.
sketch: fold congruence over the first-i staircases (List.take/map/range).
difficulty: medium.  hypothesis_fields: none.
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

/-- The cumulative floor is shape data. -/
theorem floorH_shape {H : History p F} (hcoh : HistoryCoherent H)
    (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i b, H.floorH i b = (P : ShapePrefix).floorS i b := by
  sorry

end LeanUrat.MovesD
