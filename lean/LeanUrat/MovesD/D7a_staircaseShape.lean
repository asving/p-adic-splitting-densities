/-
Unit D7a.staircase_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — the (ZC-a) staircases: line + μ + widths, all retained).
deps: D5b.
sketch: unfold; rewrite line by D5b, μ/childWidth by Matches.  difficulty: easy.
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

/-- The (ZC-a) staircases are shape data. -/
theorem staircase_shape {H : History p F} (hcoh : HistoryCoherent H)
    (hP : (P : ShapePrefix).MatchesHist H) (r : ℕ) (hr : r < H.nodes.length)
    (hr' : r < (P : ShapePrefix).reads.length) :
    ∀ b, (H.nodes[r]'hr).staircase b
      = ((P : ShapePrefix).reads[r]'hr').staircaseS ((P : ShapePrefix).lineS r) b := by
  sorry

end LeanUrat.MovesD
