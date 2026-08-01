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

/-- Theorem 4, positivity: t ↦ det(1 − tM) is continuous, nonzero on [0,1], = 1 at
t = 0 ⟹ positive at t = 1. -/
theorem det_one_sub_pos {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ}
    (hε : 0 < ε) (h0 : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j ≤ 1 - ε) :
    0 < ((1 : Matrix (Fin k) (Fin k) ℝ) - M).det := by
  -- Shrink ε to ε' := min ε 1, so that 0 ≤ 1 − ε' (needed for scaling by t ∈ [0,1]).
  set ε' : ℝ := min ε 1 with hε'def
  have hε' : 0 < ε' := lt_min hε one_pos
  have h1ε' : 0 ≤ 1 - ε' := by
    have := min_le_right ε 1; linarith
  have hrow' : ∀ i, ∑ j, M i j ≤ 1 - ε' := fun i => by
    have := min_le_left ε 1; linarith [hrow i]
  -- The path t ↦ det (1 − t • M).
  set f : ℝ → ℝ := fun t => ((1 : Matrix (Fin k) (Fin k) ℝ) - t • M).det with hfdef
  have hcont : Continuous f :=
    (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
  -- Nonvanishing on [0,1] via II-S1 at the shrunk margin ε'.
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht
    refine det_one_sub_ne_zero hε' (fun i j => ?_) (fun i => ?_)
    · exact mul_nonneg ht.1 (h0 i j)
    · calc ∑ j, (t • M) i j = t * ∑ j, M i j := by
            simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        _ ≤ t * (1 - ε') := mul_le_mul_of_nonneg_left (hrow' i) ht.1
        _ ≤ 1 * (1 - ε') := mul_le_mul_of_nonneg_right ht.2 h1ε'
        _ = 1 - ε' := one_mul _
  -- Endpoints of the path.
  have hf0 : f 0 = 1 := by simp [hfdef]
  have hf1 : f 1 = ((1 : Matrix (Fin k) (Fin k) ℝ) - M).det := by simp [hfdef]
  -- IVT: were det (1 − M) ≤ 0, the path would cross 0 inside [0,1].
  by_contra hle
  have h10 : f 1 ≤ 0 := by rw [hf1]; exact not_lt.mp hle
  obtain ⟨t, ht, hft⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
      ⟨h10, by rw [hf0]; norm_num⟩
  exact hne t ht hft

end LeanUrat.Scaffold
