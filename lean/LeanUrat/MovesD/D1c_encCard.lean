/-
Unit D1c.encTargetP_card  (MovesD campaign, E-phase)  [AUX]
moves_ref: (L11's codomain count ∏_r Q_r^{d_r}·m̄_r).
deps: E2.
sketch: Pi/product cards; (card pool)^{d} ≤ (p^w)^d; regroup = p^W·Mfac.
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

/-- L11's codomain count: the encoding target has at most M(P̂)·p^{W(P̂)} elements. -/
theorem encTargetP_card {P : Shape n} (hp : 2 ≤ p) :
    Nat.card (EncTargetP p F (P : ShapePrefix))
      ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W := by
  sorry

end LeanUrat.MovesD
