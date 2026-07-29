/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D1 `eligibleT_apparatus` — W4-1(c)'s re-keyed `eligible` (MovesD §2.5 W4-1 +
§T.1 (c1) 7093–7100). REV 6 (Fable-5 CRIT-1): the child iff at SOME-STATES; the
o = none leg is REFUTED, not omitted (§0 record 13) — the root layer carries the
⊆ face + the per-track law (`RedCellPartition`). HONEST SCOPE: these theorems hold
over ANY CellData; the CANONICAL instance is HC-2's by the contract's own (c) clause.
PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem eligibleT_iff_child (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (H : History p F) (ν : Node p F)
    (x : Box p m) (hmem : T.mem (some H) x) :
    T.child (some H) ν x ↔ eligibleT T CA (some H) ν x :=
  CA.child_cell H ν x hmem

theorem eligibleT_root_sub (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (ν : Node p F) (x : Box p m)
    (h : T.child none ν x) : eligibleT T CA none ν x :=
  CA.child_root_sub ν x h

theorem eligibleT_cell_data (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x x' : Box p m)
    (h : CA.cellOf (embE o) x = CA.cellOf (embE o) x') :
    eligibleT T CA o ν x ↔ eligibleT T CA o ν x' := by
  unfold eligibleT
  rw [h]

end LeanUrat.MovesT
