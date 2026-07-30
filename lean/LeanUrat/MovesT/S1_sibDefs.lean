/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-S1 `sib_pair_form` — the m = 2 specialization of (SIB)'s count face (MOVES
7292, 7523–7525): the gate-checked shape at the F1 `.red`-entrance site. This unit
only RESHAPES the kernel. PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem sibCount_pair_form (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m) (h : SibCount T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p))
    (hred : RedCellPartition T CA χ trackOf)
    (es : EntSt p F n) (c : CA.Cell)
    (hcard : (CA.branchSetOf c).card = 2) (S : Node p F → Set (Box p m))
    (hS : ∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
      S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) :
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * Nat.card ↥(cellEventE T CA χ es c)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν) := by
  simpa [hcard] using h es c S hcard.ge hS

end LeanUrat.MovesT
