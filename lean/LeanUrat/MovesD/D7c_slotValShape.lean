/-
Unit D7c.slotVal_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — the band's fine-slot upper edge `new(j) = line.at(j·Dwidth)`, MovesC
ROUND 6's boundary).
deps: D5b.
sketch: unfold slotVal/fineSlot; D5b + Matches Dwidth.  difficulty: easy.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D5b_lineShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {P : Shape n}

/-- The fine-slot exact valuations are shape data. -/
theorem slotVal_shape {H : History p F} (hcoh : HistoryCoherent H)
    (hP : (P : ShapePrefix).MatchesHist H) (r : ℕ) (hr : r < H.nodes.length)
    (hr' : r < (P : ShapePrefix).reads.length) :
    ∀ b, (H.nodes[r]'hr).slotVal ((H.nodes[r]'hr).fineSlot b)
      = ((P : ShapePrefix).lineS r).at
          ((b / ((P : ShapePrefix).reads[r]'hr').Dwidth) * ((P : ShapePrefix).reads[r]'hr').Dwidth) := by
  -- D5b: the recorded read line IS the shape line.
  have hline : (H.nodes[r]'hr).line = (P : ShapePrefix).lineS r := line_shape hcoh hP r hr
  -- Matches: the recorded frame width IS the shape width.
  obtain ⟨hlen, hmatch⟩ := hP
  obtain ⟨_, _, _, _, _, _, _, _, hDw, -⟩ := hmatch r hr
  intro b
  simp only [Node.slotVal, Node.fineSlot]
  rw [hline, hDw]

end LeanUrat.MovesD
