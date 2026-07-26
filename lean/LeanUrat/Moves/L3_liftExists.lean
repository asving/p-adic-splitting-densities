/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L3_liftExists — the standard lift exists (§B2 D.5)

The DISPLAYED standard lift `Φ̂ = Φ^{eg} + Σ_{0≤k<g, ψ_k≠0} t_k·Φ^{ek}` exists (D.5): for each
`k < g` with `ψ_k := ψ.coeff k ≠ 0` an (S6b) realizer `t_k ∈ C` at parent weight `h·(g−k)` and
digit scalar `ψ_k` is obtained UNCONDITIONALLY from `hS6b` — the weight `h·(g−k)` clears the (S6b)
threshold `wPrev Φ` by the hypothesis `hthr` (which is (I-aug) at the use site), and `ψ_k ≠ 0` is a
unit of the CURRENT field `K` (no `resUnits = ⊤` needed). Absent slots carry `t_k = 0`.

moves_ref: D.5 the DISPLAYED standard lift exists; MOVES ~2106-2130.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L3_liftExists {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hmon : ψ.Monic) (hg : ψ.natDegree = g) (hthr : ∀ k : ℕ, k < g → σ.wPrev σ.Φ < (σ.h : ℤ) * ((g : ℤ) - (k : ℤ))) : ∃ Φhat, IsStandardLift σ ψ g Φhat := by
  classical
  -- The realizer function: for `k < g` with `ψ_k ≠ 0`, an (S6b) realizer at parent weight
  -- `h·(g−k)` (above the threshold `wPrev Φ` by `hthr`) with digit scalar `ψ_k ∈ Kˣ`; else `0`.
  set tt : ℕ → Polynomial ℤ_[p] := fun k =>
    if h : k < g ∧ ψ.coeff k ≠ 0 then
      (σ.hS6b ((σ.h : ℤ) * ((g : ℤ) - (k : ℤ))) (Units.mk0 (ψ.coeff k) h.2) (hthr k h.1)).choose
    else 0
    with htt_def
  refine ⟨σ.Φ ^ (σ.e * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k), hmon, hg, tt, ?_, ?_, rfl⟩
  · -- Absent slots: `ψ_k = 0 ⟹ t_k = 0`.
    intro k hk0
    have hcond : ¬ (k < g ∧ ψ.coeff k ≠ 0) := fun h => h.2 hk0
    simp only [htt_def, dif_neg hcond]
  · -- Present slots: unpack the (S6b) realizer.
    intro k hkg hkne
    have hcond : k < g ∧ ψ.coeff k ≠ 0 := ⟨hkg, hkne⟩
    have htt : tt k =
        (σ.hS6b ((σ.h : ℤ) * ((g : ℤ) - (k : ℤ))) (Units.mk0 (ψ.coeff k) hkne) (hthr k hkg)).choose := by
      simp only [htt_def, dif_pos hcond]
    obtain ⟨hBne, hBmem, hBw, hBR⟩ :=
      (σ.hS6b ((σ.h : ℤ) * ((g : ℤ) - (k : ℤ))) (Units.mk0 (ψ.coeff k) hkne) (hthr k hkg)).choose_spec
    rw [htt]
    refine ⟨hBne, hBmem, hBw, ?_⟩
    have hexp : (- σ.t * ((σ.h : ℤ) * ((g : ℤ) - (k : ℤ))))
        = (- σ.t * (σ.h : ℤ) * ((g : ℤ) - (k : ℤ))) := by ring
    rw [hBR, Units.val_mk0, hexp]

end LeanUrat.Moves
