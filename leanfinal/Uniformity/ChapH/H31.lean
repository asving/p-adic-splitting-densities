/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H31 — the height-sum bound

**Chapter H, NODE H.31** (`blueprint/CHAP-H_general_induction.md` §6). *The height-sum bound.*
For `2 ≤ Q` and every `n`, in `ℝ`:

`Σ_{H<n} Q^(−H/2) ≤ (1 − 2^(−1/2))⁻¹ ≈ 3.4142`.

The `Q`-dependence is discharged by monotonicity of `x ↦ x^(1/2)`: the ratio `Q^(−1/2)` is at
most `2^(−1/2)`, so the `Q = 2` bound dominates every `Q ≥ 2`.

DEPENDS: none (pure real arithmetic; ENV-H1).

**SOURCE.** `EFF.GENIND.189` (`ANNEX-LEMMA GENIND-C2`'s (C2.4), verbatim:
*"`Σ_{H≥0}Q^{-H/2} ≤ (1-2^{-1/2})^{-1}`"* because `Q ≥ 2`), with the spec's audit *"≈ 3.414 ✓"*;
`EFF.GENIND.198` (C2Q's closing, the same sum).

**TIGHTNESS.** At `Q = 2` the bound is attained in the limit, so the non-strict partial-sum form
is the correct statement.

**RE-PLAN NOT TAKEN.** The blueprint sanctioned replacing `(1 − 2^(−1/2))⁻¹` by the explicit
constant `4` if the `rpow` bookkeeping fought back. It did not: the exact constant is proved, so
downstream consumers (H.72, H.71) get the sharp `N`-independent constant rather than `4`.

**PROOF.** Write `s := (Q^(1/2))⁻¹` and `r := (2^(1/2))⁻¹`. Termwise,
`((Q^H)⁻¹)^(1/2) = s^H` by `Real.rpow_natCast`, `Real.inv_rpow` and `Real.rpow_mul`. Then
`0 ≤ s ≤ r < 1` (monotonicity of `rpow` in the base, plus `1 < 2^(1/2)`). The partial geometric
sum is bounded by `(1 − s)⁻¹` via the induction `(1 − s)·Σ_{k<m} s^k = 1 − s^m` together with
`s^m ≥ 0`, and `(1 − s)⁻¹ ≤ (1 − r)⁻¹` by antitonicity of the inverse on `0 < 1 − r ≤ 1 − s`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- *The height-sum bound.* For `Q ≥ 2`, every partial sum of `Σ_H Q^(−H/2)` is at most the
`Q`-independent constant `(1 − 2^(−1/2))⁻¹ ≈ 3.4142`. -/
theorem height_geom_partial_le (Q : ℕ) (hQ : 2 ≤ Q) (n : ℕ) :
    ∑ H ∈ Finset.range n, ((Q : ℝ) ^ (H : ℝ))⁻¹ ^ ((1:ℝ)/2)
      ≤ (1 - ((2:ℝ) ^ ((1:ℝ)/2))⁻¹)⁻¹ := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := by linarith
  have hQpos : (0:ℝ) < (Q:ℝ) := by linarith
  set s : ℝ := ((Q:ℝ) ^ ((1:ℝ)/2))⁻¹ with hsdef
  set r : ℝ := ((2:ℝ) ^ ((1:ℝ)/2))⁻¹ with hrdef
  -- the summand is exactly `s ^ H`: all of the `rpow` bookkeeping happens here
  have hterm : ∀ H : ℕ, ((Q : ℝ) ^ (H : ℝ))⁻¹ ^ ((1:ℝ)/2) = s ^ H := by
    intro H
    rw [hsdef, ← Real.rpow_natCast ((((Q:ℝ) ^ ((1:ℝ)/2)))⁻¹) H,
      Real.inv_rpow (Real.rpow_nonneg hQ0 _), Real.inv_rpow (Real.rpow_nonneg hQ0 _),
      ← Real.rpow_mul hQ0, ← Real.rpow_mul hQ0, mul_comm]
  have h2half : (0:ℝ) < (2:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2lt : (1:ℝ) < (2:ℝ) ^ ((1:ℝ)/2) :=
    (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, by norm_num⟩)
  -- `0 ≤ s ≤ r < 1`, the `Q ≥ 2` input
  have hs_le_r : s ≤ r := by
    rw [hsdef, hrdef]
    exact inv_anti₀ h2half (Real.rpow_le_rpow (by norm_num) hQR (by norm_num))
  have hs0 : (0:ℝ) ≤ s := by rw [hsdef]; positivity
  have hr1 : r < 1 := by rw [hrdef]; exact inv_lt_one_of_one_lt₀ h2lt
  have hs1 : s < 1 := lt_of_le_of_lt hs_le_r hr1
  have hspos : (0:ℝ) < 1 - s := by linarith
  have hrpos : (0:ℝ) < 1 - r := by linarith
  have hne : (1:ℝ) - s ≠ 0 := ne_of_gt hspos
  have hid : ∀ m : ℕ, (1 - s) * ∑ k ∈ Finset.range m, s ^ k = 1 - s ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  have hgeom : ∑ k ∈ Finset.range n, s ^ k ≤ (1 - s)⁻¹ := by
    have hsm : (0:ℝ) ≤ s ^ n := pow_nonneg hs0 n
    have h2 : (1 - s) * ∑ k ∈ Finset.range n, s ^ k ≤ 1 := by rw [hid n]; linarith
    calc ∑ k ∈ Finset.range n, s ^ k
        = (1 - s)⁻¹ * ((1 - s) * ∑ k ∈ Finset.range n, s ^ k) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ ≤ (1 - s)⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 - s)⁻¹ := by ring
  calc ∑ H ∈ Finset.range n, ((Q : ℝ) ^ (H : ℝ))⁻¹ ^ ((1:ℝ)/2)
      = ∑ H ∈ Finset.range n, s ^ H := Finset.sum_congr rfl fun H _ => hterm H
    _ ≤ (1 - s)⁻¹ := hgeom
    _ ≤ (1 - r)⁻¹ := inv_anti₀ hrpos (by linarith)

section AxCheck
#print axioms Uniformity.Density.Induction.height_geom_partial_le
end AxCheck

end Uniformity.Density.Induction
