/-
Unit D13.D4R1_EV_iff  (MovesD campaign, E-phase)
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … count-equality ⟺ … mult_P̂ ≡ 1
POINTWISE on the event — the finite-level statement carries no measure-zero exception"
(D4R.1/L12).
deps: D10, D11a, D11b.
sketch: cancel p^{A′} (p ≥ 2); Finset double counting, pointwise.
difficulty: medium-hard.  hypothesis_fields: none beyond D10's.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- The EV equality criterion: count-equality ⟺ mult ≡ 1 pointwise on the event. -/
theorem D4R1_EV_iff (hne : (P : ShapePrefix).reads ≠ []) (N : ℕ)
    (hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (S : Presented p F n N m pol P) :
    (Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
        = Nat.card (PrefIdx n pol P) * p ^ (n * N))
      ↔ (∀ x ∈ S.event, S.mult x = 1) := by
  sorry

end LeanUrat.MovesD
