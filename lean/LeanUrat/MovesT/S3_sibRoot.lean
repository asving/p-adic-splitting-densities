/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-S3 `sib_root_instance` — DEPTH-0 INSTANCE: (SIB) at η = ∅ is the root read's
cross-cluster product (MOVES 7298–7304). RECORD (do not encode): JOINT-D1 is
single-cluster EVIDENCE, not the theorem — the root clause carries NO separate
hypothesis; it rides the same `hsib` tag. PROVED (specialize es := .amb). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem sib_root_instance (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hrc : RootCellsOf T CA χ) (h : SibCount T CA χ) :
    ∀ (c : CA.Cell) (S : Node p F → Set (Box p m)),
      2 ≤ (CA.branchSetOf c).card →
      (∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
        S ν = {x | ContFiber T none ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
      Nat.card ↥(cellEventE T CA χ .amb c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
          * (Nat.card ↥(cellEventE T CA χ .amb c)) ^ ((CA.branchSetOf c).card - 1)
        = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ .amb c ∩ S ν) :=
  fun c S h2 hS => h .amb c S h2 hS

end LeanUrat.MovesT
