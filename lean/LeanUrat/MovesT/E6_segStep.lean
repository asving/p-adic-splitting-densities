/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E6 `fiber_seg_step` — UNBRANCHED SEGMENT (MOVES 7496–7499): the state↔cell tie
CONSUMED AS THE LEDGER FIELD `state_cell` (REV 3, Fable-2 CRIT-3; §0 refutation record
#6); the entrance is the CARRIER value. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem fiber_seg_step (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (Tr : VTree p F) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H : History p F) (hH : H ∈ Tr.chains)
    (hone : L.sides H = 1)
    (E : Set (Box p m)) (hspec : SpectatorFor (L.freshCoords H) E) :
    Nat.card ↥(stateEvent T (some H) ∩ E) * p ^ L.siteExp H
      = Nat.card ↥(entEvent T χ (L.parentSt H) ∩ E) := by
  sorry

end LeanUrat.MovesT
