import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs
open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem L0_pmul_mk (S : SideVal p) (γ δ : ℤ) (a : S.ge γ) (b : S.ge δ) : S.pmul γ δ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = Submodule.Quotient.mk (S.mulToGe γ δ a b) := by
  rfl

#print axioms L0_pmul_mk
