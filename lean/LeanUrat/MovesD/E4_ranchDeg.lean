/-
Unit E4.Ranch_deg  (MovesD campaign, E-phase)  [AUX]
informal: deg R_anch = ℓ_r — the note's "deg R_anch,r equals that side's NORMALIZED
horizontal length ℓ_r := w'_r/e_r" (L11), PROVED from the node Props.
deps: MovesC.
sketch: `hRanch` (the pattern sum) + `hpatTop` (top digit ≠ 0): natDegree of
Σ_{k≤len} C(pat k)·X^k with nonzero top.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- deg R_anch = ℓ_r = wSide/e, from the node Props alone. -/
theorem Ranch_deg (ν : Node p F) : ν.Ranch.natDegree = ν.wSide / ν.e := by
  sorry

end LeanUrat.MovesD
