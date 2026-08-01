/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Bookings

/-!
# Scaffold/O12/Substochastic — Theorem 4 backup [BP_II units II-S1..S3]

Movement II substochastic backup (blueprint `lean/blueprints/BP_II.md` §1.5).

This file carries **unit II-S1**: `det_one_sub_ne_zero` — a nonnegative matrix `M`
with row sums ≤ 1 − ε (ε > 0) has `det (1 − M) ≠ 0`, by strict diagonal dominance
(Gershgorin, Mathlib `det_ne_zero_of_sum_row_lt_diag`) — **unit II-S2**
(`det_one_sub_pos`), and **unit II-S3** (`bn_substochastic_margin`: the scalar
kernel value at any prime power is ≤ 1 − ε per booking, ε = 3/4, 7/8, 7/8, 6/7).
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

/-! ## Unit II-S3: the 𝔅_n margins (blueprint §1.5, Theorem 4 closing)

Kernel value = 1 − Φ value, so the bound is Corollary D's margins (the II-G4
mechanism) fired directly through the landed `marginO1/O2/O3` shapes via
`eval_ratio` on the explicit kernel ratios. -/

open LeanUrat.MovesU (eval_ratio marginO1 marginO2 marginO3)

/-- Instantiation at 𝔅_n: the scalar kernel value at any prime power is ≤ 1 − ε with
ε = 3/4, 7/8, 6/7 per booking (Corollary D margins) — the hypothesis holds if a finer
state set ever replaces the scalar kernel. -/
theorem bn_substochastic_margin (b : Booking) {e : ℕ} (he : 2 ≤ e) {x : ℚ} (hx : 2 ≤ x) :
    (b.kernel e).eval (RingHom.id ℚ) x
      ≤ 1 - (match b with | .O1 => (3:ℚ)/4 | .O2 => 7/8 | .O2r => 7/8 | .O3 => 6/7) := by
  have hE3 : 3 ≤ blockE e := blockE_ge_three he
  have hne : ¬ e ≤ 1 := by omega
  have hx0 : (0 : ℚ) < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxE : (0 : ℚ) < x ^ blockE e := by positivity
  have hxEne : Polynomial.eval x (Polynomial.X ^ blockE e : Polynomial ℚ) ≠ 0 := by
    simpa using ne_of_gt hxE
  cases b with
  | O1 =>
    show (Booking.O1.kernel e).eval (RingHom.id ℚ) x ≤ 1 - (3:ℚ)/4
    have hker : Booking.O1.kernel e
        = algebraMap (Polynomial ℚ) Qq Polynomial.X
          / algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e) := by
      unfold Booking.kernel
      rw [if_neg hne]
      simp only [qX, map_pow, div_eq_mul_inv]
    have heval : (Booking.O1.kernel e).eval (RingHom.id ℚ) x = x / x ^ blockE e := by
      rw [hker, eval_ratio hxEne]
      simp
    -- `x / x^E = (x^{E−1})⁻¹`, then the (O1) margin at `m = E − 1 ≥ 2`.
    have hsplit : x ^ blockE e = x * x ^ (blockE e - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hfrac : x / x ^ blockE e = (x ^ (blockE e - 1))⁻¹ := by
      rw [hsplit, ← div_div, div_self hxne, one_div]
    have hm := marginO1 hx (two_le_blockE_sub_one he)
    rw [heval, hfrac]
    linarith
  | O2 =>
    show (Booking.O2.kernel e).eval (RingHom.id ℚ) x ≤ 1 - (7:ℚ)/8
    have hker : Booking.O2.kernel e
        = algebraMap (Polynomial ℚ) Qq 1
          / algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e) := by
      unfold Booking.kernel
      rw [if_neg hne]
      simp only [qX, map_one, map_pow, one_div]
    have heval : (Booking.O2.kernel e).eval (RingHom.id ℚ) x = 1 / x ^ blockE e := by
      rw [hker, eval_ratio hxEne]
      simp
    have hm := marginO2 hx hE3
    rw [heval, one_div]
    linarith
  | O2r =>
    show (Booking.O2r.kernel e).eval (RingHom.id ℚ) x ≤ 1 - (7:ℚ)/8
    have hker : Booking.O2r.kernel e
        = algebraMap (Polynomial ℚ) Qq 1
          / algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e) := by
      unfold Booking.kernel
      rw [if_neg hne]
      simp only [qX, map_one, map_pow, one_div]
    have heval : (Booking.O2r.kernel e).eval (RingHom.id ℚ) x = 1 / x ^ blockE e := by
      rw [hker, eval_ratio hxEne]
      simp
    have hm := marginO2 hx hE3
    rw [heval, one_div]
    linarith
  | O3 =>
    show (Booking.O3.kernel e).eval (RingHom.id ℚ) x ≤ 1 - (6:ℚ)/7
    have hden : (0 : ℚ) < x ^ blockE e - 1 := by
      have h8 : (8 : ℚ) ≤ x ^ blockE e := by
        calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ blockE e := pow_le_pow_right₀ (by norm_num) hE3
        _ ≤ x ^ blockE e := by gcongr
      linarith
    have hdenne :
        Polynomial.eval x (Polynomial.X ^ blockE e - 1 : Polynomial ℚ) ≠ 0 := by
      simpa using ne_of_gt hden
    have hker : Booking.O3.kernel e
        = algebraMap (Polynomial ℚ) Qq (Polynomial.X - 1)
          / algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ blockE e - 1) := by
      unfold Booking.kernel
      rw [if_neg hne]
      simp only [qX, map_sub, map_one, map_pow, div_eq_mul_inv]
    have heval : (Booking.O3.kernel e).eval (RingHom.id ℚ) x
        = (x - 1) / (x ^ blockE e - 1) := by
      rw [hker, eval_ratio hdenne]
      simp
    have hm := marginO3 hx hE3
    rw [heval]
    linarith

end LeanUrat.Scaffold
