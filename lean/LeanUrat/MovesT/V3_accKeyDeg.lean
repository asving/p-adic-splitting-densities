/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V3 `accEF_keyDeg` — the E·F = key-degree leg (MOVES 7078–7080), SPECIES
vocabulary. DOCSTRING DUTY: the cluster-degree·μ leg lives at T-V9 (node side); this
unit claims nothing beyond the E·F = D′ telescope. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- E·F = the CHILD key degree D′ = e·g·D: list induction along `Chain' StageLaws`
(D_{r+1} = e_r·g_r·D_r with D₀ = 1 telescopes to ∏e·∏g = D′). -/
theorem accEF_keyDeg {n : ℕ} (l : List MovesSp.Species) (sels : List (ℕ × ℕ))
    (hzip : l.length = sels.length ∧
      ∀ (r : ℕ) (s : MovesSp.Species) (gm : ℕ × ℕ),
        l[r]? = some s → sels[r]? = some gm → s.sel = some gm)
    (hne : l ≠ []) (hroot : ∀ s, l.head? = some s → MovesSp.RootStage n s)
    (hchain : l.Chain' MovesSp.StageLaws)
    (s : MovesSp.Species) (hlast : l.getLast? = some s)
    (g μ : ℕ) (hsel : sels.getLast? = some (g, μ) ∧ s.sel = some (g, μ)) :
    (l.map fun t => t.e).prod * (sels.map Prod.fst).prod = s.e * g * s.D := by
  sorry

end LeanUrat.MovesT
