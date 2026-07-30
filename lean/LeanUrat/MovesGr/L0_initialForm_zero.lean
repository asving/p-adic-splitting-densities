import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

set_option linter.style.longLine false
set_option linter.style.header false

theorem L0_initialForm_zero (S : SideVal p) : S.initialForm 0 = 0 := by
  have h : S.mkPiece 0 = 0 := Submodule.Quotient.mk_zero _
  unfold SideVal.initialForm
  rw [h, map_zero]

#print axioms L0_initialForm_zero
