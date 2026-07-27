import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem L0_deg_add (S : SideVal p) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f * g ≠ 0) (hval : S.w (f * g) = S.w f + S.w g) : S.deg (f * g) = S.deg f + S.deg g := by
  have h : (↑(S.deg (f * g)) : WithTop ℤ) = ↑(S.deg f + S.deg g) := by
    rw [S.deg_eq hfg, hval, ← S.deg_eq hf, ← S.deg_eq hg, ← WithTop.coe_add]
  exact WithTop.coe_inj.mp h

#print axioms L0_deg_add
