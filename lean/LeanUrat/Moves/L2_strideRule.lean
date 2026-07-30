/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L2_strideRule — the stride rule `R(B·Φ^j) = R(B)·z^{js}` (D.3(c))

`moves_ref`: D.3(c) stride rule `R(B_j Φ^j) = dig(B_j)·z^{js}`, MOVES ~2041-2049.

`R` is multiplicative on nonzero factors (`hRmul`), so `R(B·Φ^j) = R(B)·R(Φ^j)`; the key
residual power `R(Φ^j) = T(s·j)` follows from `hRΦ : R Φ = T s` by induction, using that
`T : ℤ → L₀` is a monoid hom (`T_add`, `T_zero`). `L2.keyResidualPow` (the standalone form of
this identity) is not imported here, so it is reproved as the private lemma `R_keyPow`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

/-- `R 1 = 1`: `R 1` is a nonzero idempotent in the domain `↥K[z^{±1}]`. -/
private lemma R_one {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have he : σ.R 1 * 1 = σ.R 1 * σ.R 1 := by rw [mul_one, ← h]
  exact (mul_left_cancel₀ (σ.hRne 1 one_ne_zero) he).symm

/-- `R(Φ^j) = z^{js} = T(s·j)` (D.3(b) power form; the not-yet-on-disk `L2.keyResidualPow`). -/
private lemma R_keyPow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (j : ℕ) : σ.R (σ.Φ ^ j) = LaurentPolynomial.T (σ.s * j) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero]
    rw [R_one σ, LaurentPolynomial.T_zero]
  | succ n ih =>
    have hΦn : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦ
    rw [pow_succ, σ.hRmul (σ.Φ ^ n) σ.Φ hΦn hΦ, ih, σ.hRΦ, ← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring

theorem L2_strideRule {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC σ.Φ B) (j : ℕ) : σ.R (B * σ.Φ ^ j) = σ.R B * LaurentPolynomial.T (σ.s * j) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
  rw [σ.hRmul B (σ.Φ ^ j) hB hΦj, R_keyPow σ j]

end LeanUrat.Moves
