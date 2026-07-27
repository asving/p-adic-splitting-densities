/-
Unit D11a.mult_sum  (MovesD campaign, E-phase)
moves_ref: (double counting — the multiplicity sum equals the fiber-count sum).
deps: D2a.
sketch: Fintype double counting on the incidence set.  difficulty: medium.
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

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- Double counting: Σ_x mult(x) = Σ_i #fiber(i). -/
theorem mult_sum (S : Presented p F n N m pol P) :
    ∑ x : Box p m, S.mult x = ∑ᶠ i : PrefIdx n pol P, Nat.card ↥(S.fiber i) := by
  sorry

end LeanUrat.MovesD
