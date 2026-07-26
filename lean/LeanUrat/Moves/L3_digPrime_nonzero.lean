/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L0_GRg

/-!
# Moves/L3 — `dig'(B) ≠ 0` for `B ∈ Ĉ∖0` (MOVES §D.6, ~2149-2150)

The residue digit `dig'_{z̄}(B) = R(B)` evaluated at the root `z̄ ∈ F` of `ψ` is nonzero for
`B ∈ Ĉ∖0` (`deg B < e·g·deg Φ`).

Proof. `R(B) ≠ 0` has support in a window of width `< g` (`L2_widthBound`), so by `L0_GRg` it is an
anchored polynomial `R(B) = z^a · toLaurent Ranch` with `Ranch.natDegree < g = deg ψ` and
`Ranch ≠ 0`. Evaluating: `dig'(B) = z̄^a · Ranch(z̄)`. The anchor `z̄^a` is a unit, so nonzero;
and `Ranch(z̄) ≠ 0` because `ψ` is irreducible over `K` with `deg Ranch < deg ψ` and `Ranch ≠ 0`,
so `ψ ∤ Ranch`, hence `IsCoprime ψ Ranch` (`Polynomial ↥K` is a PID); a Bézout identity
`u·ψ + v·Ranch = 1` evaluated at `z̄` (where `ψ(z̄) = 0`) would give `0 = 1` if also `Ranch(z̄) = 0`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L3_digPrime_nonzero {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) : σ.digPrime zbar B ≠ 0 := by
  -- `g ≥ 1` since `ψ` is irreducible.
  have hg1 : 1 ≤ g := by rw [← hg]; exact hψ.natDegree_pos
  -- `R(B) ≠ 0`.
  have hRne : σ.R B ≠ 0 := σ.hRne B hB
  -- Width bound + anchor: `R(B) = T a · toLaurent Ranch` with `deg Ranch < g`.
  obtain ⟨a, hwin⟩ := L2_widthBound σ g hg1 B hB hBdeg
  obtain ⟨Ranch, hdeg, hReq⟩ := L0_GRg hRne a g hwin
  -- `Ranch ≠ 0`.
  have hRanch0 : Ranch ≠ 0 := by
    intro h
    apply hRne
    rw [hReq, h, map_zero, mul_zero]
  -- Unfold the digit and split off the anchor unit.
  simp only [Stage.digPrime]
  rw [hReq, map_mul, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_toLaurent]
  apply mul_ne_zero
  · exact (zbar ^ a).ne_zero
  · -- `Ranch(z̄) ≠ 0`.
    intro hcontra
    -- `ψ ∤ Ranch` from the degree bound.
    have hndvd : ¬ ψ ∣ Ranch := by
      rintro ⟨q, hq⟩
      have hq0 : q ≠ 0 := by
        rintro rfl; rw [mul_zero] at hq; exact hRanch0 hq
      have hdegmul : Ranch.natDegree = ψ.natDegree + q.natDegree := by
        rw [hq]; exact Polynomial.natDegree_mul hψ.ne_zero hq0
      omega
    -- Irreducible + not-dvd ⟹ coprime (PID).
    have hcop : IsCoprime ψ Ranch := (hψ.isCoprime_or_dvd Ranch).resolve_right hndvd
    obtain ⟨u, v, huv⟩ := hcop
    -- Evaluate the Bézout identity at `z̄`: `0 = 1`.
    have hev := congrArg (Polynomial.eval₂ σ.K.subtype (zbar : F)) huv
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul,
      Polynomial.eval₂_one, hzbar, hcontra, mul_zero, mul_zero, add_zero] at hev
    exact zero_ne_one hev

end LeanUrat.Moves
