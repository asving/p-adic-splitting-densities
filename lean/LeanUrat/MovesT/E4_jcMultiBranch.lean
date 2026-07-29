/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E4 `jcMulti_branching` — "A multi-side site is always a BRANCHING site (k
sides ⟹ ≥ k branches)" (MOVES 7473–7483). The DEF deliverable (`JCmultiAt`) is in
Defs §2.5; `JCmultiAt` is NEVER proved — hypothesis `hjcm` downstream, PER-SITE only.
PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem jcMulti_branching (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (c : CA.Cell) {fd : FreshData p m}
    (ss : SideSplit T CA c fd) :
    ss.k ≤ (CA.branchSetOf c).card := by
  classical
  choose f hf1 hf2 using ss.side_ne
  have hinj : ∀ j j' : Fin ss.k, f j = f j' → j = j' := by
    intro j j' h
    rw [← hf2 j, ← hf2 j', h]
  calc ss.k = (Finset.univ : Finset (Fin ss.k)).card := by simp
    _ ≤ (CA.branchSetOf c).card := by
        apply Finset.card_le_card_of_injOn f (fun j _ => hf1 j)
        intro j _ j' _ h
        exact hinj j j' h

end LeanUrat.MovesT
