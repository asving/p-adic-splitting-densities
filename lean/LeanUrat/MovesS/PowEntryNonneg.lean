/-
Unit U-23b `pow_entry_nonneg` (easy) — entrywise nonnegativity of powers.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem pow_entry_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (hA : ∀ i j, 0 ≤ A i j) :
    ∀ (k : ℕ) (i j : ι), 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (ih i l) (hA l j)

end LeanUrat.MovesS
