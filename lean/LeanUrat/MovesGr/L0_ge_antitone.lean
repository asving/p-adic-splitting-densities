import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem L0_ge_antitone (S : SideVal p) {γ δ : ℤ} (h : γ ≤ δ) : S.ge δ ≤ S.ge γ := by
  intro x hx
  exact le_trans (WithTop.coe_le_coe.mpr h) hx

#print axioms L0_ge_antitone
