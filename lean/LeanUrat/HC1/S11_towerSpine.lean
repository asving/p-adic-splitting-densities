/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine

/-!
# HC1.S11_towerSpine — the spine: StageCoreL at every tower level

moves_ref: MOVES 1862 ("Everything below is self-contained given the ACCEPTED §A
and §B1") + D.7/D.10 closes. deps: T1 (base), S9, S10; DefsTower. NOTE: `Tower`
CARRIES `TransitionCoreL`/`IsRecenteringCore` witnesses, so the spine is the
PROPAGATION of StageCoreL, with S9/S10 showing such witnesses EXIST for legal
reads — both directions recorded. `tower_wf` = every move's child data matches the
transition's output shape (K/e/h fields). difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S11: every tower level carries the round-5 core, and each move's child
stage records the move's own data (the wf leg). -/
theorem S11_towerSpine {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) :
    (∀ k : Fin (T.K + 1), StageCoreL (T.stg k)) ∧
    (∀ k : Fin T.K,
      match T.move k with
      | .inc _ _ _ e' h' zbar _ _ =>
          (T.stg k.succ).K = (T.stg k.castSucc).nextField zbar ∧
          (T.stg k.succ).e = e' ∧ (T.stg k.succ).h = h'
      | .recenter _ _ _ =>
          (T.stg k.succ).e = 1 ∧ (T.stg k.succ).K = (T.stg k.castSucc).K) := by
  refine ⟨?_, ?_⟩
  · -- PART 1: the spine.  Fin.induction: base seeds `stg 0`, the step uses `T.move i`.
    intro k
    induction k using Fin.induction with
    | zero => exact T.base.2
    | succ i IH =>
        -- IH : StageCoreL (T.stg i.castSucc);  goal : StageCoreL (T.stg i.succ)
        -- T.move i : MoveWitness (T.stg i.castSucc) (T.stg i.succ)
        cases hmv : T.move i with
        -- OBSTRUCTION — TWO INDEPENDENT VERDICTS (2026-07-27 route failure; 2026-07-28
        -- escalation COUNTERMODEL).  Both branches reduce to `StageCoreL (T.stg i.succ)`
        -- for the SPECIFIC tower child, from IH + the carried recording relation only.
        --
        -- (I) ROUTE FAILURE (prover 1, machine-confirmed): the intended propagators
        -- S9_transStage / S10_recStage are OPEN (both `sorry`, marked HARD) and
        -- MIS-SHAPED — each proves `∃ σ', … ∧ StageCoreL σ' ∧ …`, an EXISTENTIAL child,
        -- type-mismatched against `StageCoreL (T.stg i.succ)` (verified).
        --
        -- (II) SEMANTIC COUNTERMODEL (escalation, sharper locus).  The direct route
        -- "records + child's own round-2 Stage axioms + parent StageCoreL ⇒ child
        -- StageCoreL" transports MORE than verdict (I) credited: wPrev_mul/ult
        -- (child_wPrev + parent hwmul/hwult), both reps legs, w_strict (the valuation
        -- trick: w(−1) = 0 from hwmul), and even R_neg (child_dig_frame at B = 1 pins
        -- z̄^{mfun 0} = 1, then B = −1 with parent R_neg gives σ'.R (−1) = −1).  But the
        -- TVEC legs are NOT valid consequences: the SIGN-TWIST countermodel
        --   σ''.R f := σ'.R f · C(ξ^{σ'.w f})   (ξ ∈ FQˣ, ξ^{h'} = 1, ξ ≠ 1;
        --   e.g. odd p, h' even, ξ = −1)
        -- preserves EVERY round-2 Stage field (hRmul/hRadd/hRlt: f ↦ ξ^{w f} is a
        -- weight-hom, equal weights ⇒ equal twist; hRΦ: ξ^{h'} = 1; hS5: monomial units
        -- stay monomial; hS6a/hS6b: FQˣ and Kˣ are closed under ·ξ^{−e'ν} since ξ ∈ FQ)
        -- and EVERY carried record (TransitionData is weight/field/reps data only;
        -- child_Tvec untouched; child_dig_frame via mfun'' ν := mfun ν + m₁·e'·ν
        -- whenever ξ = z̄^{m₁} ∈ ⟨z̄⟩, e.g. z̄ primitive), yet BREAKS TvecLaw and
        -- TvecUnitLaw: num/den twist factors differ by exactly ξ^{w num − w den} = ξ ≠ 1
        -- (net weight 1 by hbez — the same identity that closes the w-leg).  So Part 1
        -- has no proof from the carried witnesses unless the theory refutes every odd-p
        -- tower ending in an even-h' increment with −1 ∈ ⟨z̄⟩ — false in the intended
        -- semantics (h' = 2 wild reads are the certified generic case).
        --
        -- FAITHFUL REPAIR (Defs/statement change, outside this unit's fence): carry
        -- `StageCoreL σ'` in `MoveWitness`, or restate S9/S10 as propagation TO A GIVEN
        -- record-pinned child AND add the tvec legs to the records — the twist shows
        -- they are independent of the current ones.
        | inc ψ g Φhat e' h' zbar hyp core =>
            sorry
        | recenter cc tt core =>
            sorry
  · -- PART 2: the wf leg — reads straight off the carried transition records.
    intro k
    cases hmv : T.move k with
    | inc ψ g Φhat e' h' zbar hyp core =>
        exact ⟨core.base.child_field, core.base.child_e, core.base.child_h⟩
    | recenter cc tt core =>
        obtain ⟨_, he1', _, _, _, _, _, _, _, _, hK, _, _, _⟩ := core.base
        exact ⟨he1', hK⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S11_towerSpine
