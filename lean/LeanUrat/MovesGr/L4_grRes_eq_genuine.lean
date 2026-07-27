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

theorem L4_grRes_eq_genuine (σ : Stage p F) (M : GenuineStageModel σ) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : letI := M.Rg.ring; letI := M.Loring; letI := M.alg; σ.grRes f = M.Θ (algebraMap M.S.Gr M.Lo (M.S.initialForm f)) := by
  exact (M.discharge f hf).symm

#print axioms L4_grRes_eq_genuine
