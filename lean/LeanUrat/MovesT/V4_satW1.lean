/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V4 `sat_iff_confirming` — saturation ⟺ μ = 1 (MOVES 7078–7080), split into its
two exactly-warranted MovesSp legs (REV 2, Codex 36). DOCSTRING DUTY: CORPUS-TIE
lemmas (VP-2's τ-irr = MovesSp's confirming W = 1 letter), not note-display
transcriptions. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- warrant: StageLaws's W-law (s'.W = μ). -/
theorem sat_iff_W1 {n : ℕ} (s s' : MovesSp.Species)
    (hstep : MovesSp.StageLaws s s') (g μ : ℕ) (hsel : s.sel = some (g, μ)) :
    (μ = 1) ↔ (s'.W = 1) := by
  simp only [MovesSp.StageLaws, hsel] at hstep
  obtain ⟨_, _, hW, _, _⟩ := hstep
  rw [hW]

/-- warrant: (G6) "selection = ⊥ iff W = 1". -/
theorem sat_iff_selNone {n : ℕ} (s s' : MovesSp.Species)
    (hstep : MovesSp.StageLaws s s') (hcoh : MovesSp.Coherent s')
    (g μ : ℕ) (hsel : s.sel = some (g, μ)) :
    (μ = 1) ↔ s'.sel = none := by
  simp only [MovesSp.StageLaws, hsel] at hstep
  obtain ⟨_, _, hW, _, _⟩ := hstep
  obtain ⟨_, _, _, _, _, hG6⟩ := hcoh
  rw [hW] at hG6
  exact hG6.symm

end LeanUrat.MovesT
