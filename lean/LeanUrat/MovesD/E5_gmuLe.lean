/-
Unit E5.gmu_le_len  (MovesD campaign, E-phase)  [AUX]
informal: g·μ ≤ ℓ_r (each eligible factor contributes g·μ to deg R_anch — L11).
deps: E4.
sketch: `hOrd` gives ψ^μ ∣ Ranch, Ranch ≠ 0 (hpatTop); degrees: μ·g = deg ψ^μ ≤
deg Ranch = ℓ (hψdeg, E4).  difficulty: medium.  hypothesis_fields: none.
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

/-- g·μ ≤ ℓ_r: the descend factor's degree contribution fits the side length. -/
theorem gmu_le_len (ν : Node p F) : ν.g * ν.μ ≤ ν.wSide / ν.e := by
  sorry

end LeanUrat.MovesD
