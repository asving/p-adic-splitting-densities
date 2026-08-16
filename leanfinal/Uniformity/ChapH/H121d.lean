/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H118
import Uniformity.ChapG.G14

/-!
# Uniformity.ChapH.H121d — the content-weighted β census

**Chapter H, NODE H.121d** [theorem] (AMENDMENT A-H.6 §5).  Placeholder header; filled at the
end of the unit.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Uniformity.Density.Menu

/-! ## 1. The arithmetic core: a coupled double geometric sum -/

/-- Every partial geometric sum is below the limit `(1 − t)⁻¹`. -/
private theorem geom_partial_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, t ^ i ≤ (1 - t)⁻¹ := by
  have hpos : (0:ℝ) < 1 - t := by linarith
  have key : ∀ j : ℕ, (∑ i ∈ Finset.range j, t ^ i) * (1 - t) = 1 - t ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have h1 : (∑ i ∈ Finset.range n, t ^ i) * (1 - t) ≤ 1 := by
    rw [key n]
    have : (0:ℝ) ≤ t ^ n := pow_nonneg ht0 n
    linarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  linarith

/-- The tail of a geometric sum with ratio `Q^(−p)`, from `e` up. -/
private theorem geom_tail_le (Q : ℕ) (hQ : 2 ≤ Q) (p e n : ℕ) (hp : 1 ≤ p) :
    ∑ D ∈ Finset.Ico e n, ((Q:ℝ) ^ (p * D))⁻¹
      ≤ ((Q:ℝ) ^ (p * e))⁻¹ * (1 - ((Q:ℝ) ^ p)⁻¹)⁻¹ := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < (Q:ℝ) := by linarith
  have hpp : (1:ℝ) < (Q:ℝ) ^ p := by
    calc (1:ℝ) < (Q:ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (Q:ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp
  set t : ℝ := ((Q:ℝ) ^ p)⁻¹ with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by
    rw [ht, inv_lt_one_iff₀]
    exact Or.inr hpp
  have hterm : ∀ i : ℕ, ((Q:ℝ) ^ (p * (e + i)))⁻¹ = ((Q:ℝ) ^ (p * e))⁻¹ * t ^ i := by
    intro i
    rw [ht, Nat.mul_add, pow_add, mul_inv, inv_pow, ← pow_mul]
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ Finset.range (n - e), ((Q:ℝ) ^ (p * (e + i)))⁻¹
      = ∑ i ∈ Finset.range (n - e), ((Q:ℝ) ^ (p * e))⁻¹ * t ^ i :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ((Q:ℝ) ^ (p * e))⁻¹ * ∑ i ∈ Finset.range (n - e), t ^ i := by
        rw [Finset.mul_sum]
    _ ≤ ((Q:ℝ) ^ (p * e))⁻¹ * (1 - t)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (geom_partial_le t ht0 ht1 _) (by positivity)

/-- **The coupled double geometric sum.**  Exactly the shape the census assembles to: the
slope `k` runs from `1`, the content `D` runs from `2k + 1` (which is the structural constraint
`D ≥ 2k + 1` proved in §3), and the summand is the per-cell digit count times `Q^D`.  The
closed value is `1/(Q+1)`, so the bound `1/3` is TIGHT at `Q = 2` (which is why the `z ≠ 0`
count `Q − 1` and the EXACT-digit factor `Q − 1` on the top coefficient are both indispensable:
either one relaxed to `Q` overshoots `1/3` at `Q = 2`). -/
private theorem census_geom_le (Q : ℕ) (hQ : 2 ≤ Q) (N : ℕ) :
    ∑ k ∈ Finset.Ico 1 N, ∑ D ∈ Finset.Ico (2 * k + 1) N,
        ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹ ≤ 1 / 3 := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < (Q:ℝ) := by linarith
  have hQ1 : (0:ℝ) < (Q:ℝ) - 1 := by linarith
  have hQ2 : (0:ℝ) < (Q:ℝ) ^ 2 - 1 := by nlinarith
  set A : ℝ := (1 - ((Q:ℝ) ^ 2)⁻¹)⁻¹ with hA
  set B : ℝ := (1 - ((Q:ℝ) ^ 1)⁻¹)⁻¹ with hB
  have hQ0' : (Q:ℝ) ≠ 0 := ne_of_gt hQ0
  have hAv : A = (Q:ℝ) ^ 2 / ((Q:ℝ) ^ 2 - 1) := by
    have hstep : (1 - ((Q:ℝ) ^ 2)⁻¹) = ((Q:ℝ) ^ 2 - 1) / (Q:ℝ) ^ 2 := by field_simp
    rw [hA, hstep, inv_div]
  have hBv : B = (Q:ℝ) / ((Q:ℝ) - 1) := by
    have hstep : (1 - ((Q:ℝ) ^ 1)⁻¹) = ((Q:ℝ) - 1) / (Q:ℝ) := by
      rw [pow_one]; field_simp
    rw [hB, hstep, inv_div]
  have hA0 : 0 ≤ A := by rw [hAv]; positivity
  -- the inner (content) sum, per slope
  have hinner : ∀ k : ℕ, ∑ D ∈ Finset.Ico (2 * k + 1) N,
        ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹
      ≤ ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹ := by
    intro k
    have hc0 : (0:ℝ) ≤ ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) := by positivity
    have hsplit : (Q:ℝ) ^ (2 * (2 * k + 1)) = (Q:ℝ) ^ (3 * k) * (Q:ℝ) ^ (k + 2) := by
      rw [← pow_add]; congr 1; omega
    have hpow : (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * (2 * k + 1)))⁻¹ = ((Q:ℝ) ^ (k + 2))⁻¹ := by
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hQ0 (3 * k))),
        one_mul]
    calc ∑ D ∈ Finset.Ico (2 * k + 1) N,
          ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹
        = (((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k))
            * ∑ D ∈ Finset.Ico (2 * k + 1) N, ((Q:ℝ) ^ (2 * D))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k))
            * (((Q:ℝ) ^ (2 * (2 * k + 1)))⁻¹ * A) :=
          mul_le_mul_of_nonneg_left (geom_tail_le Q hQ 2 (2 * k + 1) N (by omega)) hc0
      _ = ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹ := by
          rw [← hpow]; ring
  -- the outer (slope) sum
  have houter : ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹
      = (((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹)
          * ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) ^ (1 * k))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, mul_inv, one_mul]
    ring
  have hc1 : (0:ℝ) ≤ ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹ := by positivity
  calc ∑ k ∈ Finset.Ico 1 N, ∑ D ∈ Finset.Ico (2 * k + 1) N,
        ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹
      ≤ ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹ :=
        Finset.sum_le_sum fun k _ => hinner k
    _ = (((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹)
          * ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) ^ (1 * k))⁻¹ := houter
    _ ≤ (((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹) * (((Q:ℝ) ^ (1 * 1))⁻¹ * B) :=
        mul_le_mul_of_nonneg_left (geom_tail_le Q hQ 1 1 N (by omega)) hc1
    _ = 1 / ((Q:ℝ) + 1) := by
        rw [hAv, hBv]
        field_simp
        ring
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)

/-! ## 2. The cubic recentring, coefficient by coefficient

At `m = 3` the recentring `x ↦ π^k (y + w)` of `f = X³ + a₂X² + a₁X + a₀` is computed once and
for all.  Writing `W := π^k · w` for the (valuation-`k`) CENTRE, the four coefficients are

    b₀ = a₀ + a₁W + a₂W² + W³,   b₁ = π^k·(a₁ + 2a₂W + 3W²),
    b₂ = π^(2k)·(a₂ + 3W),       b₃ = π^(3k),

i.e. `b_j = π^(jk) · t_j` with `t_j` the coefficients of the plain Taylor shift by `W`.  The
`π^(jk)` is H.112's ghost divisibility made explicit; the `t_j` are what the census counts. -/

section Cubic

variable {O : Type*} [CommRing O]

open Polynomial

/-- The cubic recentring, expanded. -/
private theorem comp_cubic_eq (a : Fin 3 → O) (u w : O) :
    (monicPoly a).comp (C u * (X + C w))
      = C (a 0 + a 1 * (u * w) + a 2 * (u * w) ^ 2 + (u * w) ^ 3)
        + C (u * (a 1 + 2 * a 2 * (u * w) + 3 * (u * w) ^ 2)) * X
        + C (u ^ 2 * (a 2 + 3 * (u * w))) * X ^ 2
        + C (u ^ 3) * X ^ 3 := by
  simp only [monicPoly, Fin.sum_univ_three, add_comp, mul_comp, pow_comp, C_comp, X_comp,
    C_add, C_mul, C_pow, map_ofNat, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, mul_one]
  ring

private theorem comp_cubic_coeff_zero (a : Fin 3 → O) (u w : O) :
    ((monicPoly a).comp (C u * (X + C w))).coeff 0
      = a 0 + a 1 * (u * w) + a 2 * (u * w) ^ 2 + (u * w) ^ 3 := by
  rw [comp_cubic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num

private theorem comp_cubic_coeff_one (a : Fin 3 → O) (u w : O) :
    ((monicPoly a).comp (C u * (X + C w))).coeff 1
      = u * (a 1 + 2 * a 2 * (u * w) + 3 * (u * w) ^ 2) := by
  rw [comp_cubic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num

private theorem comp_cubic_coeff_two (a : Fin 3 → O) (u w : O) :
    ((monicPoly a).comp (C u * (X + C w))).coeff 2
      = u ^ 2 * (a 2 + 3 * (u * w)) := by
  rw [comp_cubic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num

end Cubic

end Uniformity.Density.Induction
