/-
Unit D5a.Dwidth_pos  (MovesD campaign, E-phase)  [AUX]
informal: every read of a coherent history has positive frame width.
deps: MovesC.Defs.
sketch: induction on r — root `deg Φ₀ = 1` + `hDwidth`; step width chain
`D_{r+1} = e·g·D_r`, e, g ≥ 1.  difficulty: medium.  hypothesis_fields: none.
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

/-- Coherent histories have positive frame width at every read. -/
theorem Dwidth_pos {H : History p F} (hcoh : HistoryCoherent H) (r : ℕ)
    (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).Dwidth := by
  sorry

end LeanUrat.MovesD
