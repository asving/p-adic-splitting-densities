/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.D7_digD_mul
import LeanUrat.HC1.S2_childW

/-!
# HC1.S9r_childR — the D.7(vi)-normalized child residual EXISTS (the hard
construction block's seed)

S9 DECOMPOSITION unit (blueprint §9.5, pre-approved split; S9's own statement
UNCHANGED): `childR` definition (DefsChild, by choice) + the S5′ shape lemma —
here rendered as the INHABITATION of `ChildResData` (the structure carries the
S5′ pinned shape as its `hS5'` field, so the shape lemma of the defined `childR`
is its projection through the choice, S9w). moves_ref: MOVES 2395–2418 (D.7(vi):
normalize the minimal-slot development data by the transported unit
`T′^{−w′(f)}`). deps (§9.5): D7 (the twisted DIG homomorphism — the carry-exact
scalar law `hRmul` needs), S2 (the development/attained-min plumbing `childW`
rides). THE ONE REMAINING HARD CONSTRUCTION BLOCK (with S9w's genuine leg;
blueprint §9.8 post-event state). difficulty: HARD. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S9r: for every legal read of a cored stage and every child Bézout pair
`(s′, t′)` (P2-pinned at e′ = 1), the D.7(vi)-normalized child residual data
exists — `childR`'s choice spec is inhabited. -/
theorem S9r_childR {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    Nonempty (ChildResData σ Φhat e' h' zbar s' t') := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9r_childR
