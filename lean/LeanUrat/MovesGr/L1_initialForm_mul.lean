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

theorem L1_initialForm_mul (S : SideVal p) (Rg : GradedRingStr S) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) : letI := Rg.ring; S.initialForm (f * g) = S.initialForm f * S.initialForm g := by
  exact Rg.if_mul f g hf hg

#print axioms L1_initialForm_mul
