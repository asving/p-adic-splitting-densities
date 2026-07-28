/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.V8_childResidual

/-!
# HC1.S9w_residualLaws — THE hard new-algebra unit: a LAWFUL child residual exists

S9 DECOMPOSITION unit (blueprint §9.5): hR0/hRne/hRadd/hRlt/hRmul +
w_strict/w_jump/R_neg for the pair `(childW, childR)` — billed by §9.5 as "HARD
(the one genuinely new algebra block)".

RESTORED SHAPE (2026-07-28 remediation round — the Codex batch-confirmation S9
rejection repair): the E-phase draft had bundled the whole law pack as
`ChildResData` FIELDS, relocating this unit's hardness into S9r's inhabitation
sorry and reducing this file to choice projections. Post-unbundle (DefsChild):
`ChildResData` is the carrier + normalization pins ONLY, `ChildResLaws` is the
law pack as a `Prop` on carriers, and THIS unit's own statement is the genuine
construction: a carrier satisfying the FULL law pack exists (the D.7(vi)
normalized residual with the carry-exact product — D7's cmul law + `L3_DIV`;
the additive laws via the slot-min ties), together with the childW-only
StageCore tie law w_strict (S2's development plumbing: developments add, and a
strictly lower slot minimum survives the sum). The laws OF THE DEFINED `childR`
are then the clearly-labeled PROJECTION corollary `childR_laws` (proved below —
it is NOT this unit's content). Once this unit lands, S9r's carrier inhabitation
follows from the first conjunct.
deps: D7, `L3_DIV`, S2/S4/S5 (per §9.5).
difficulty: HARD (§9.8: the S9r+S9w block — the hardness lives HERE). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

open scoped Classical

/-- Unit S9w (the §9.5 hard new-algebra block, restored shape): for every legal
read of a cored stage and every child Bézout pair `(s′, t′)` (P2-pinned at
e′ = 1), (i) a carrier of the D.7(vi)-normalized child residual satisfying the
FULL law pack `ChildResLaws` (hR0/hRne/hRmul/hRadd/hRlt + w_jump/R_neg) EXISTS,
and (ii) the childW-only StageCore tie law w_strict holds. -/
theorem S9w_residualLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    (∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D) ∧
    (∀ f g', f ≠ 0 → g' ≠ 0 → childW σ Φhat e' h' f < childW σ Φhat e' h' g' →
      childW σ Φhat e' h' (f + g') = childW σ Φhat e' h' f) := by
  -- The blueprint §10's staged closure (V′ kernel): the statement is byte-identical
  -- to the V8 capstone.  Conjunct (ii) [w_strict] is PROVED (V8c, Lean-core);
  -- conjunct (i) rides on V8b's carrier construction (the remaining hard block —
  -- this unit inherits V8b's sorryAx until it lands; wired 2026-07-28 escalation).
  exact V8_childResidual σ hσ th s' t' hbez' ht'0

/-- PROJECTION COROLLARY (PROVED; explicitly NOT this unit's hard content — that
is `S9w_residualLaws` above): given S9w's lawful-carrier existence, the DEFINED
`childR` carries the two carrier pins (hRΦ′, hS5′) and the seven `ChildResLaws`
laws through the choice. This is the consumer-facing `(childW, childR)` form the
pre-unbundle file exposed. -/
theorem childR_laws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    {s' t' : ℤ}
    (hex : ∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D) :
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
    (∀ f, childR σ Φhat e' h' zbar s' t' (-f) = - childR σ Φhat e' h' zbar s' t' f) := by
  have hcR : childR σ Φhat e' h' zbar s' t' = hex.choose.Rc := by
    unfold childR
    exact dif_pos hex
  obtain ⟨h0, hne, hmul, hadd, hlt, hjump, hneg⟩ := hex.choose_spec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcR]; exact h0
  · rw [hcR]; exact hne
  · rw [hcR]; exact hmul
  · rw [hcR]; exact hadd
  · rw [hcR]; exact hlt
  · rw [hcR]; exact hex.choose.hRPhi
  · rw [hcR]; exact hex.choose.hS5'
  · rw [hcR]; exact hjump
  · rw [hcR]; exact hneg

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9w_residualLaws
#print axioms LeanUrat.HC1.childR_laws
