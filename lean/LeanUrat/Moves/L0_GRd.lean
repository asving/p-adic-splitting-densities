/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L0_GRd — `dig'(monomial) ∈ F'ˣ` (D.6; MOVES ~2149-2151)

A monomial unit `x = C c · T k` (`c ∈ Kˣ`) evaluates to a nonzero element under any field
homomorphism `φ : K →+* F` at a unit `zbar : Fˣ`: `eval₂ φ zbar x = φ c · zbar^k ≠ 0`.
-/

set_option linter.style.longLine false
set_option linter.style.header false

open LeanUrat.Moves

theorem L0_GRd {K F : Type*} [Field K] [Field F] (φ : K →+* F) (zbar : Fˣ) {x : LaurentPolynomial K} (hx : IsMonomialUnit x) : LaurentPolynomial.eval₂ φ zbar x ≠ 0 := by
  obtain ⟨c, k, rfl⟩ := hx
  rw [LaurentPolynomial.eval₂_C_mul_T]
  exact mul_ne_zero ((map_ne_zero_iff φ φ.injective).mpr c.ne_zero) (zbar ^ k).ne_zero
