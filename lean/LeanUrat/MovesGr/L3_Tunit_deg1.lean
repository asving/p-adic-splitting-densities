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

theorem L3_Tunit_deg1 (σ : Stage p F) (M : GenuineStageModel σ) : letI := M.Loring; M.Θ (M.Tunit : M.Lo) = (locT ↥σ.K : LTwo ↥σ.K) := by
  exact M.hT
