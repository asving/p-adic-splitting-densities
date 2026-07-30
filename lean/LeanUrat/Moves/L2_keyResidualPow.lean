/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L2_keyResidualPow — the key-residual power identity (§B2 D.3(b))

`R(Φ^j) = z^{s·j} = T (s·j)`: the literal monomial identity for the residual of a power of
the stage key. Proof: `R` is multiplicative on nonzero elements (`hRmul`) and `R Φ = T s`
(`hRΦ`), so induction on `j` gives `R(Φ^j) = (R Φ)^j = (T s)^j = T (s·j)`; the base case needs
`R 1 = 1`, which follows because `R 1` is a nonzero idempotent of the Laurent domain `↥K[z^{±1}]`
and so left-cancels to `1`.

moves_ref: D.3(b) R(Φ)=z^s literal monomial identity; MOVES ~2027-2039.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L2_keyResidualPow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (j : ℕ) : σ.R (σ.Φ ^ j) = LaurentPolynomial.T (σ.s * j) := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  -- `R 1 = 1`: `R 1 = R(1·1) = R 1 · R 1` is a nonzero idempotent, so left-cancels to `1`.
  have hR1 : σ.R 1 = 1 := by
    have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    have he : σ.R 1 * 1 = σ.R 1 * σ.R 1 := by rw [mul_one, ← h]
    exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) he).symm
  induction j with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero, LaurentPolynomial.T_zero]
    exact hR1
  | succ n ih =>
    have hpow : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦne
    rw [pow_succ, σ.hRmul _ _ hpow hΦne, ih, σ.hRΦ, ← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring

end LeanUrat.Moves
