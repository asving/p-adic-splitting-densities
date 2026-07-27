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
import LeanUrat.MovesD.D2a_finite
import LeanUrat.MovesD.D3a_poolBound
import LeanUrat.MovesD.D12_evBound

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
  -- D4R.1-EV: the union bound within the level-N box (division-free).
  have h1 := D4R1_EV hne N hA S
  -- D4R.2′: C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, on the CD form; hnorm from the Presented setup.
  have h2 := D4R2' (P := P) S.hnorm
  -- On the nonempty shape, CD is the class count (CD_eq), so #PrefIdx ≤ M·p^W.
  rw [CD_eq S.hnorm hne] at h2
  calc Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
      ≤ Nat.card (PrefIdx n pol P) * p ^ (n * N) := h1
    _ ≤ ((P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W) * p ^ (n * N) := by
        gcongr
    _ = (P : ShapePrefix).Mfac * p ^ ((P : ShapePrefix).W + n * N) := by
        rw [mul_assoc, ← pow_add]

end LeanUrat.MovesD
