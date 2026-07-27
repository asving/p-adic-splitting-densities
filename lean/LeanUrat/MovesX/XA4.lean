/-
Unit XA.4 t1Arith  [E-phase: stated, body sorry]
moves_ref: T1 column bracket "[e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]".
deps: none (Defs only, for the namespace). difficulty: EASY.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) :
    e + h ≤ e * h * ell + 1 ∧ h * (ell - 1) ≤ e * h * ell + 1 - e - h ∧
    1 ≤ ell * (e * h * ell + 1 - e - h) := by
  -- F1: e + h ≤ ehℓ  (from (e-1)(h-1) ≥ 0 and ℓ ≥ 2). Gives conjunct 1 and the
  --     positivity core of conjunct 3.
  have F1 : e + h ≤ e * h * ell := by nlinarith [he, hh, hl, Nat.mul_le_mul he hh]
  -- F2: hℓ + e ≤ ehℓ + 1  (from (e-1)(hℓ-1) ≥ 0). Gives conjunct 2 once ℓ-1 is
  --     turned into a genuine (untruncated) subtraction.
  have F2 : h * ell + e ≤ e * h * ell + 1 := by
    nlinarith [he, hh, hl, Nat.mul_le_mul he (le_refl (h * ell))]
  have hsub : h * (ell - 1) = h * ell - h := by rw [Nat.mul_sub, Nat.mul_one]
  refine ⟨by omega, by omega, ?_⟩
  have hpos := Nat.mul_pos (show 0 < ell by omega) (show 0 < e * h * ell + 1 - e - h by omega)
  omega

end LeanUrat.MovesX
