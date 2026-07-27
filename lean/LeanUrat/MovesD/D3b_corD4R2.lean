/-
Unit D3b.D4R2_cor  (MovesD campaign, E-phase)
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} ≤ M(P̂)·p^{W(P̂)−A(P̂)} = M(P̂)·p^{−A_net(P̂)},
A_net(P̂) := A(P̂) − W(P̂)" (Corollary D4R.2), division-free (`Anet` records the named
exponent).
deps: D12, D3a, D2a.
sketch: chain D4R1_EV with D4R2' (via CD_eq); pow_add.  difficulty: easy.
hypothesis_fields: `hnorm` (through the deps), `hne`, `hA` (the stabilized-level
quantifier, discharged by L9s/NP_stab).
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

/-- Corollary D4R.2, division-free: event count · p^A ≤ M · p^{W + nN}. -/
theorem D4R2_cor (hne : (P : ShapePrefix).reads ≠ []) (N : ℕ)
    (hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (S : Presented p F n N m pol P) :
    Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
      ≤ (P : ShapePrefix).Mfac * p ^ ((P : ShapePrefix).W + n * N) := by
  sorry

end LeanUrat.MovesD
