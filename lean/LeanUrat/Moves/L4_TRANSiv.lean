/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L4 — TRANS(iv): unit survival of the outgoing key `Φ` (MOVES D.7(iv), ~2202-2212)

The outgoing key `Φ` joins the next stage's representative list `U'`. Its residue digit
`dig'_{z̄}(Φ) = R(Φ)` evaluated at the root `z̄ ∈ Fˣ` is nonzero. Unlike a general
representative `ũ ∈ reps` (handled by `L3_digPrime_nonzero`, which needs the width bound
`deg ũ < e·g·deg Φ`), the key has a PINNED residual `R(Φ) = z^s` (D.3(b), the `σ.hRΦ` law):
a pure monomial unit. Evaluating at `z̄` gives `z̄^s`, a power of the unit `z̄`, hence nonzero.
This needs no degree bound (it works even when `e·g = 1`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L4_TRANSiv {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (hΦdeg : 0 < σ.Φ.natDegree) : σ.digPrime zbar σ.Φ ≠ 0 := by
  -- `dig'(Φ) = R(Φ) evaluated at z̄ = z̄^s`, a unit power, hence nonzero.
  simp only [Stage.digPrime]
  rw [σ.hRΦ, LaurentPolynomial.eval₂_T]
  exact (zbar ^ σ.s).ne_zero

end LeanUrat.Moves
