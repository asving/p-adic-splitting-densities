import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem L0_gt_le_ge (S : SideVal p) (γ : ℤ) : S.gt γ ≤ S.ge γ := by
  intro x hx
  have hlt : (γ : WithTop ℤ) < S.w x := hx
  exact le_of_lt hlt
