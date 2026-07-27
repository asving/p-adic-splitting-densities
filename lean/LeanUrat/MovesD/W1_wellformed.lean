/-
Unit W1′.wellformed_of_wf  (MovesD campaign, E-phase)  [REV 6: shape-internal — no member
needed; the rev-5 member-transport version is SUPERSEDED]
moves_ref: "COARSE CHAIN … deg R_anch,r ≤ n always" (L11) — over the note's shape
universe BY TYPE, unconditional.
deps: Defs.
sketch: induction down the reads on the CERTIFICATE P.2: root — ℓ₀ ≤ s0+wSide ≤ n
(root_box); step — ℓ_{r+1} ≤ s0'+wSide' ≤ μ_r (window) ≤ ℓ_r (gmu, g ≥ 1).
difficulty: easy-medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {n : ℕ}

/-- Wellformedness holds unconditionally over the subtype (ℓ_r ≤ n at every read). -/
theorem wellformed_of_wf (P : Shape n) : (P : ShapePrefix).Wellformed n := by
  sorry

end LeanUrat.MovesD
