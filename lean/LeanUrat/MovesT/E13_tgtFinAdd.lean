/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E9_fiberDisjoint

/-! # T-E13 `tgt_finadd` — (TGT)'s regrouping license AT FINITE LEVEL (MOVES
7017–7030): disjointness DERIVED from T-E9 through the DISPLAYED `VTree.ext`; the
DENSITY form stays X.3-tagged and UNSTATED (§0). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem tgt_finadd (𝒯 : Finset (VTree p F)) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m)
    (hpair : ∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, Tr ≠ Tr' → ¬ VTree.ext Tr Tr') :
    Nat.card ↥(⋃ Tr ∈ 𝒯, {x | VTree.fiberAt Tr T χ x})
      = ∑ Tr ∈ 𝒯, Nat.card ↥{x | VTree.fiberAt Tr T χ x} := by
  sorry

end LeanUrat.MovesT
