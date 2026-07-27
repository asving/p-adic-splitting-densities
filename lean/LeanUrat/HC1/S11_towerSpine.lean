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
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S11_towerSpine
