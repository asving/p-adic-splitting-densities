import Mathlib
import LeanUrat.Moves.Defs

namespace LeanUrat.Moves

open Polynomial

theorem L0_GRe {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) : σ.R (f ^ n) = (σ.R f) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    -- goal: σ.R 1 = 1
    have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    have hne : σ.R 1 ≠ 0 := σ.hRne 1 one_ne_zero
    have heq : σ.R 1 * 1 = σ.R 1 * σ.R 1 := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hne heq).symm
  | succ k ih =>
    have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
    rw [pow_succ, σ.hRmul (f ^ k) f hfk hf, ih, ← pow_succ]

end LeanUrat.Moves
