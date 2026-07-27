/-
Unit D5b.line_shape  (MovesD campaign, E-phase)
moves_ref: "each line is the slope −h_r/e_r line through (j*_r, u*_r), pinned only WITH
its height … A is a function of P̂ only because u*_r ∈ P̂" (L9 rev 9 — u* enters HERE,
through the intercept).
deps: D5a, D6a.
sketch: `Line` ext; slope from coherence's slope law (e·STR·D ≠ 0 via he/D5a/strS ≥ 1);
intercept solved from `hLineU` at the matched right endpoint.  difficulty: medium.
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

/-- The recorded read line IS the shape line (slope + intercept both shape data). -/
theorem line_shape {H : History p F} (hcoh : HistoryCoherent H)
    (hP : (P : ShapePrefix).MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) :
    (H.nodes[r]'hr).line = (P : ShapePrefix).lineS r := by
  sorry

end LeanUrat.MovesD
