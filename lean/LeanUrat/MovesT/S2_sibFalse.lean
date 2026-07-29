/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-S2 `sib_falsifier` — the doctrine gate: (SIB) is a CONTENTFUL law (MOVES
7397–7400); a toy model with two children whose continuation events are IDENTICAL
fails the product AT THE CELL EVENT. Gate architecture (REV 2, Fable GAP-6): finite
surrogate + hand bridge. [E-DEV, recorded: the blueprint's display reuses the name
`toyχ` at box size 2; the T-G1 chart `toyχ : Fin 2 → Fin 9` has box size 9, so THIS
unit's chart is the size-2 identity chart `toyχ2` below — same values on `Fin 2`.] -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- the size-2 toy chart of this unit's falsifier (identity embedding). -/
def toyχ2 : Fin 2 → Fin 2 := id

theorem sib_falsifier : ∃ (T : TreeModel 2 (ZMod 2) 2 1 2 polTriv)
    (CA : CellData 2 (ZMod 2) 2 1 2 polTriv T), ¬ SibCount T CA toyχ2 := by
  sorry

end LeanUrat.MovesT
