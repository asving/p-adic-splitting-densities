/-
Unit E1.digit_in_pool  (MovesD campaign, E-phase)  [AUX]
informal: a matched node's side digits lie in the order-p^w root set.
deps: Defs.
sketch: `FiniteField.pow_card` on ↥ν.σ.K (card p^w by hM); ring-hom coercion.
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

/-- A matched node's side digits lie in the order-p^w root set (the pool). -/
theorem digit_in_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) (k : ℕ) :
    ν.sideDigit k ∈ pool p R.w F := by
  -- `hM` records the frame field's cardinality: `#(↥ν.σ.K) = p ^ R.w`.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcard, _⟩ := hM
  -- The frame field is a finite field (a subfield of the finite ambient `F`).
  letI : Fintype ↥ν.σ.K := Fintype.ofFinite _
  have hcard' : Fintype.card ↥ν.σ.K = p ^ R.w := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  -- Frobenius: every element of a field of order `q` satisfies `x ^ q = x`.
  have key : (ν.pat k) ^ (p ^ R.w) = ν.pat k := by
    rw [← hcard']; exact FiniteField.pow_card _
  -- Transport the identity along the subfield inclusion `↥ν.σ.K ↪ F`.
  change ((ν.pat k : ↥ν.σ.K) : F) ^ (p ^ R.w) = ((ν.pat k : ↥ν.σ.K) : F)
  rw [← SubmonoidClass.coe_pow, key]

end LeanUrat.MovesD
