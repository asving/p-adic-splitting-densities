/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.S2_childW

/-!
# HC1.S9w_residualLaws — the residual law pack for `(childW, childR)`

S9 DECOMPOSITION unit (blueprint §9.5): hR0/hRne/hRadd/hRlt/hRmul +
w_strict/w_jump/R_neg for the pair `(childW, childR)`. The `childR`-involving
laws are the `ChildResData` fields, so given S9r's inhabitation they PROJECT
through the choice (proved below); the childW-only tie law w_strict is this
unit's genuine remaining leg (sorry — it rides S2's development plumbing:
developments add, and a strictly lower slot minimum survives the sum).
deps: D7, `L3_DIV`, S2/S4/S5 (per §9.5) — consumed by the w_strict leg.
difficulty: HARD (§9.8: the S9r+S9w block). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

open scoped Classical

/-- Unit S9w: the full (w, R)-law pack at `(childW, childR)`: the eight
`ChildResData` laws hold of the DEFINED `childR` (projections through the
choice), plus the childW-only StageCore tie law w_strict. -/
theorem S9w_residualLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hne : Nonempty (ChildResData σ Φhat e' h' zbar s' t')) :
    (childR σ Φhat e' h' zbar s' t' 0 = 0) ∧
    (∀ f, f ≠ 0 → childR σ Φhat e' h' zbar s' t' f ≠ 0) ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 → childR σ Φhat e' h' zbar s' t' (f * g')
      = childR σ Φhat e' h' zbar s' t' f * childR σ Φhat e' h' zbar s' t' g') ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f →
      childR σ Φhat e' h' zbar s' t' (f + g')
        = childR σ Φhat e' h' zbar s' t' f + childR σ Φhat e' h' zbar s' t' g') ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childR σ Φhat e' h' zbar s' t' (f + g') = childR σ Φhat e' h' zbar s' t' f) ∧
    (childR σ Φhat e' h' zbar s' t' Φhat = LaurentPolynomial.T s') ∧
    (∀ B, B ≠ 0 → inC Φhat B →
      ∃ c' : (↥(σ.nextField zbar))ˣ,
        childR σ Φhat e' h' zbar s' t' B = LaurentPolynomial.C ((c' : ↥(σ.nextField zbar))) *
            LaurentPolynomial.T (- t' * σ.w B) ∧
        ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B) ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g' →
      childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g') →
      childR σ Φhat e' h' zbar s' t' f + childR σ Φhat e' h' zbar s' t' g' = 0) ∧
    (∀ f, childR σ Φhat e' h' zbar s' t' (-f) = - childR σ Φhat e' h' zbar s' t' f) ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 → childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) := by
  have hcR : childR σ Φhat e' h' zbar s' t' = hne.some.Rc := by
    unfold childR
    exact dif_pos hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcR]; exact hne.some.hR0
  · rw [hcR]; exact hne.some.hRne
  · rw [hcR]; exact hne.some.hRmul
  · rw [hcR]; exact hne.some.hRadd
  · rw [hcR]; exact hne.some.hRlt
  · rw [hcR]; exact hne.some.hRPhi
  · rw [hcR]; exact hne.some.hS5'
  · rw [hcR]; exact hne.some.hWjump
  · rw [hcR]; exact hne.some.hRneg
  · -- w_strict for childW: the genuine leg (S2's development plumbing)
    sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9w_residualLaws
