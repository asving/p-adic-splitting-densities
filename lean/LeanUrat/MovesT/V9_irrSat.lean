/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V9 `irr_saturation` — the note's own parenthetical stated ON `IrrHalts`:
saturation ⟺ μ = 1 under lawfulness (MOVES 7078–7080). Together with T-V3's species
leg this displays BOTH equalities of the note line. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- the Dwidth chain telescopes the latest read's key degree to accE·accF. -/
theorem acc_childWidth (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (hne : H.nodes ≠ []) :
    accE H * accF H = (H.nodes.getLast?).elim 1 (fun ν => ν.childWidth) := by
  sorry

theorem irr_iff_mu_one (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (ν : Node p F) (hν : H.nodes.getLast? = some ν) :
    IrrHalts H ↔ ν.μ = 1 := by
  sorry

end LeanUrat.MovesT
