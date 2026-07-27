/-
Unit E2.pool_card_le  (MovesD campaign, E-phase)  [AUX]
deps: Defs.
sketch: roots of the nonzero X^{p^w} − X; `Polynomial.card_roots`.
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

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The pool has at most p^w elements (roots of the nonzero X^{p^w} − X). -/
theorem pool_card_le {w : ℕ} (hp : 2 ≤ p) (hw : 1 ≤ w) :
    Nat.card ↥(pool p w F) ≤ p ^ w := by
  sorry

end LeanUrat.MovesD
