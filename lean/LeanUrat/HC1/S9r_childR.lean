/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.D7_digD_mul
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S9w_residualLaws

/-!
# HC1.S9r_childR — the D.7(vi)-normalized child residual CARRIER exists (the
construction block's seed)

S9 DECOMPOSITION unit (blueprint §9.5, pre-approved split; S9's own statement
UNCHANGED): `childR` definition (DefsChild, by choice) + the S5′ shape lemma —
rendered as the INHABITATION of `ChildResData`. UNBUNDLED (2026-07-28
remediation round — the Codex batch-confirmation S9 rejection repair):
`ChildResData` is now the CARRIER ONLY (Rc + the D.3(b) key pin + the S5′
pinned shape — exactly §9.5's S9r billing), so this unit is the construction
SEED; the residual apparatus/tie laws moved to `ChildResLaws`, whose
lawful-carrier existence is S9w's OWN theorem (`S9w_residualLaws` — the §9.5
hard new-algebra block, where the S9 hardness now honestly lives). Once S9w
lands, this unit follows from its first conjunct
(`⟨(S9w_residualLaws σ hσ th s' t' hbez' ht'0).1.choose⟩`); it is kept as the
named seed unit per the §9.5 split. moves_ref: MOVES 2395–2418 (D.7(vi):
normalize the minimal-slot development data by the transported unit
`T′^{−w′(f)}`). deps (§9.5): D7, S2 (the development/attained-min plumbing
`childW` rides). difficulty: hard (subsumed by S9w). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S9r: for every legal read of a cored stage and every child Bézout pair
`(s′, t′)` (P2-pinned at e′ = 1), the D.7(vi)-normalized child residual CARRIER
exists (post-unbundle: the normalization pins alone — the seed; the LAWFUL
carrier is S9w's own theorem, which subsumes this one). -/
theorem S9r_childR {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0) :
    Nonempty (ChildResData σ Φhat e' h' zbar s' t') :=
  -- §9.5 seed reduction: S9r is the named CARRIER-inhabitation unit; a lawful
  -- carrier is S9w's own theorem, so the carrier follows from its first conjunct.
  ⟨(S9w_residualLaws σ hσ th s' t' hbez' ht'0).1.choose⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9r_childR
