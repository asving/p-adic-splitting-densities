/-
Unit E3.frameField_eq_pool  (MovesD campaign, E-phase)  [AUX]
informal: the frame field's image in F IS the pool (the unique subfield per order — what
lets classes of DIFFERENT members share one eligible-factor universe).
deps: E1, E2.
sketch: range is a subfield of card p^w inside pool (E1); pool has ≤ p^w elements (E2);
equal cards force equality.  difficulty: medium.  hypothesis_fields: none.
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

/-- The matched frame field's image in F IS the pool. -/
theorem frameField_eq_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) :
    (Set.range (fun a : ↥ν.σ.K => (a : F))) = pool p R.w F := by
  sorry

end LeanUrat.MovesD
