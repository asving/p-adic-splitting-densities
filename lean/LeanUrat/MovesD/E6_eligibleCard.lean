/-
Unit E6.eligible_card_le  (MovesD campaign, E-phase)  [AUX]
informal: R_anch holds at most m̄ = ⌊ℓ/(g·μ)⌋ monic irreducible degree-g ord-μ factors —
L11's "each contributes g_r·μ_r to its degree".
deps: E4.
sketch: distinct monic irreducibles are coprime; the product of q^μ over any k eligible
factors divides Ranch (UFD), so k·g·μ ≤ deg Ranch = ℓ, k ≤ ⌊ℓ/(gμ)⌋.
difficulty: medium-hard.  hypothesis_fields: none.
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

/-- The K-side eligible-factor count is bounded by m̄ = ⌊ℓ/(g·μ)⌋. -/
theorem eligible_card_le (ν : Node p F) :
    Nat.card {q : Polynomial ↥ν.σ.K //
        q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ}
      ≤ (ν.wSide / ν.e) / (ν.g * ν.μ) := by
  sorry

end LeanUrat.MovesD
