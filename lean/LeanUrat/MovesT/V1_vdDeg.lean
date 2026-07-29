/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V1 `vd_deg_hen` — the (τ-hen) verdict degree (MOVES 7072–7073 + 7062).
PROVED (E-phase prove-now set). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

theorem vd_deg_hen (g : ℕ) (hg : 1 ≤ g) : (henVerdict g hg).deg = g := by
  simp [Vd.deg, henVerdict]

end LeanUrat.MovesT
