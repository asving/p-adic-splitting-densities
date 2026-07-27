/-
Unit D12.D4R1_EV  (MovesD campaign, E-phase)
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡ "(D4R.4-EV) … the
union bound within the level-N box", at every N ≥ N(P̂) (same quantifier note as D10).
deps: D10, D11a, D11b.
sketch: card event = #{mult ≥ 1} ≤ Σ mult.  difficulty: medium.
hypothesis_fields: none beyond D10's.
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

/-- D4R.1-EV ≡ D4R.4-EV: the union bound, division-free. -/
theorem D4R1_EV (hne : (P : ShapePrefix).reads ≠ []) (N : ℕ)
    (hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (S : Presented p F n N m pol P) :
    Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
      ≤ Nat.card (PrefIdx n pol P) * p ^ (n * N) := by
  sorry

end LeanUrat.MovesD
