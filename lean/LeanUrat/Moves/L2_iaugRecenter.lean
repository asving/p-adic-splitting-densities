/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L2_iaugRecenter — the (I-aug) chord inequality in the recentered frame (D.4)

`moves_ref`: D.4 (I-aug) after recentering — the SAME chord inequality in the primed frame
(`v = v'`), MOVES ~2095-2098.

The RS-landing box (`hbox`/`hvtx`) is stated directly in the primed valuation `σ'.w`.
`hvtx` pins the vertex weight `w f = w(B μ) + μ·wΦ`; `hbox` gives the strict below-line
condition at slot `j`. Substituting the vertex identity into the box inequality yields the
chord inequality at `(j, μ)` — pure ordered-ring arithmetic, no recentering data needed
beyond the primed statements already supplied by `L5.recRSland` at `g = 1`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L2_iaugRecenter {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p]) (hrec : IsRecentering σ σ' cc tt) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment σ'.Φ f B N) (j : ℕ) (hj : j < μ) (hjnz : B j ≠ 0) (hbox : σ'.w f < σ'.w (B j) + (j : ℤ) * σ'.w σ'.Φ) (hvtx : σ'.w (B μ) + (μ : ℤ) * σ'.w σ'.Φ = σ'.w f) : ((μ : ℤ) - j) * σ'.w σ'.Φ < σ'.w (B j) - σ'.w (B μ) := by
  have hexp : ((μ : ℤ) - j) * σ'.w σ'.Φ
      = (μ : ℤ) * σ'.w σ'.Φ - (j : ℤ) * σ'.w σ'.Φ := by ring
  rw [hexp]
  linarith [hbox, hvtx]

end LeanUrat.Moves
