/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C4 `ns_ladder` — "|Z_M| → ∞" along the tower at finite level (MOVES
7227–7229), the REV-4 tower form: the squeeze over an arbitrary index with a
diverging lower bound (exactly the shape T-C7 consumes). PROVED (E-phase prove-now
set): p ≥ 2, zpow-antitone squeeze below p^{−lower}. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem ns_ladder {ι : Type*} [Preorder ι] (Zcard lower : ι → ℕ)
    (hlad : ∀ k, lower k ≤ Zcard k)
    (hgrow : Filter.Tendsto lower Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun k => (p : ℝ) ^ (-(Zcard k : ℤ))) Filter.atTop (nhds 0) := by
  have hp : (1 : ℝ) < (p : ℝ) := by
    have := (Fact.out : p.Prime).two_le
    exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two this
  have hZ : Filter.Tendsto Zcard Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hlad hgrow
  have hpow : Filter.Tendsto (fun j : ℕ => (p : ℝ) ^ j) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp
  have h0 : Filter.Tendsto (fun k => ((p : ℝ) ^ (Zcard k : ℕ))⁻¹)
      Filter.atTop (nhds 0) :=
    (hpow.comp hZ).inv_tendsto_atTop
  have heq : (fun k => (p : ℝ) ^ (-(Zcard k : ℤ)))
      = fun k => ((p : ℝ) ^ (Zcard k : ℕ))⁻¹ := by
    funext k
    rw [zpow_neg, zpow_natCast]
  rw [heq]
  exact h0

end LeanUrat.MovesT
