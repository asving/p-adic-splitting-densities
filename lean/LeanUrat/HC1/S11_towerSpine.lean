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
        -- OBSTRUCTION (machine-confirmed, 2026-07-27).  Both branches reduce to
        -- `StageCoreL (T.stg i.succ)` for the SPECIFIC tower child, from
        --   IH : StageCoreL (T.stg i.castSucc)  and the carried recording relation.
        -- The Tower carries only `TransitionCoreL`/`IsRecenteringCore` (§DefsTower,
        -- `MoveWitness`), NOT `StageCoreL` of the child.  The intended propagators
        -- S9_transStage / S10_recStage are (i) OPEN (both still `sorry`, marked HARD)
        -- and, decisively, (ii) MIS-SHAPED: each proves `∃ σ', … ∧ StageCoreL σ' ∧ …`,
        -- an EXISTENTIAL child, not `StageCoreL` of the given `T.stg i.succ`.  Applying
        -- them yields `StageCoreL σ'` and a type mismatch against `StageCoreL (T.stg i.succ)`
        -- (verified: `hsc : StageCoreL σ'` ≠ goal).  No uniqueness bridges them: the
        -- recording relations underdetermine the child (they pin K, e, h, reps, wPrev,
        -- Tvec and `R` on Ĉ only — leaving `σ'.R` off-Ĉ, `σ'.w`, weightSet, s, t free),
        -- while `StageCore` demands R_neg / w_jump / SlotDecomp / CoeffFieldLawCore on all
        -- of `σ'.R`, `σ'.w`.  So the spine leg is NOT provable sorry/axiom-free as stated;
        -- the faithful repair pins the child (carry `StageCoreL` in `MoveWitness`, or
        -- restate S9/S10 as propagation to a given child) — a Defs/statement change.
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
