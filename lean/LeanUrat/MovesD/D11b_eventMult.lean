/-
Unit D11b.event_iff_mult  (MovesD campaign, E-phase)
moves_ref: "S(P̂,⊤) = {f : mult_P̂(f) ≥ 1}" (L6 corollary).
deps: Defs.
sketch: iUnion membership ↔ nonempty index subtype ↔ positive card.
difficulty: easy.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- Event membership is positive multiplicity. -/
theorem event_iff_mult (S : Presented p F n N m pol P) (x : Box p m) :
    x ∈ S.event ↔ 1 ≤ S.mult x := by
  sorry

end LeanUrat.MovesD
