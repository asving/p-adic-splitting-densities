/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Scaffold/O12/Substochastic — Theorem 4 backup [BP_II units II-S1..S3]

Movement II substochastic backup (blueprint `lean/blueprints/BP_II.md` §1.5).

This file carries **unit II-S1**: `det_one_sub_ne_zero` — a nonnegative matrix `M`
with row sums ≤ 1 − ε (ε > 0) has `det (1 − M) ≠ 0`, by strict diagonal dominance
(Gershgorin, Mathlib `det_ne_zero_of_sum_row_lt_diag`). Units II-S2..S3
(`det_one_sub_pos`, `bn_substochastic_margin`) extend this module.
-/

namespace LeanUrat.Scaffold

/-- Theorem 4, nonvanishing: nonnegative M with row sums ≤ 1 − ε has det(1 − M) ≠ 0
(strict diagonal dominance; Mathlib `Matrix.det_ne_zero_of_sum_row_lt_diag`). -/
theorem det_one_sub_ne_zero {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ}
    (hε : 0 < ε) (h0 : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j ≤ 1 - ε) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - M).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hMii_le : M i i ≤ ∑ j, M i j :=
    Finset.single_le_sum (fun j _ => h0 i j) (Finset.mem_univ i)
  have hoff : ∀ j ∈ Finset.univ.erase i,
      ‖((1 : Matrix (Fin k) (Fin k) ℝ) - M) i j‖ = M i j := by
    intro j hj
    rw [Matrix.sub_apply, Matrix.one_apply_ne' (Finset.ne_of_mem_erase hj), zero_sub,
      norm_neg, Real.norm_of_nonneg (h0 i j)]
  calc ∑ j ∈ Finset.univ.erase i, ‖((1 : Matrix (Fin k) (Fin k) ℝ) - M) i j‖
      = ∑ j ∈ Finset.univ.erase i, M i j := Finset.sum_congr rfl hoff
    _ = (∑ j, M i j) - M i i := Finset.sum_erase_eq_sub (Finset.mem_univ i)
    _ < 1 - M i i := by linarith [hrow i]
    _ = ‖((1 : Matrix (Fin k) (Fin k) ℝ) - M) i i‖ := by
        rw [Matrix.sub_apply, Matrix.one_apply_eq,
          Real.norm_of_nonneg (by linarith [hMii_le.trans (hrow i)])]

end LeanUrat.Scaffold
