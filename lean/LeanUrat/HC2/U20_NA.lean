/-
Unit U20.readsOf_NA  (HC-2 campaign, E-phase — blueprint §5 Layer D)
moves_ref: §C C.0 (NA) display; C.3 "the classifier reads actual hull sides".
deps: D4 (SideReads(i)), hull convexity (Moves L2_widthBound/L2_strideRule + line
arithmetic).  difficulty: medium-hard.  hypothesis_fields: none.
sketch: the new side is a lower hull edge of the CHILD development whose window ends
strictly left of the standing vertex; strict convexity of the hull at the vertex + the
side's minimality give the strict gap at base index μ·D.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (NA) for runs: at a non-adjacent consecutive read of a run, the pinned old vertex
lies STRICTLY ABOVE the extended new line (the (NA) conjunct of
`TransitionAdmissible`, extracted). -/
theorem readsOf_NA {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hna : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      < (H.nodes[i]'(by omega)).μ) :
    (H.nodes[i+1]'hi1).line.at
        ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)
      < (H.nodes[i]'(by omega)).line.at
        ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  sorry

end LeanUrat.MovesJ
