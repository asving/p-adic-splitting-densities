/-
Unit U-23d `e0_inv_nonneg` (medium) — consumer [4]/SQ.2 only.
moves_ref: "the Neumann series converges, and (I − A(q₀))^{−1} ≥ 0".
sketch: `(1-A)⁻¹ = Σ_{m<k} A^m + (1-A)⁻¹ A^k` (U-23a); nonneg partial sums
(U-23b); remainder → 0 (U-23c); closed limit.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.NeumannPartial
import LeanUrat.MovesS.PowEntryNonneg
import LeanUrat.MovesS.PowEntryTendsto

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem e0_inv_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (h : EscapeE0 A) :
    ∀ i j : ι, 0 ≤ (1 - A)⁻¹ i j := by
  intro i j
  by_cases hu : IsUnit (1 - A).det
  · -- Invertible case: run the Neumann-series argument.
    -- Left-cancelling `neumann_partial` by the inverse:
    --   ∑_{m<k} Aᵐ = (1-A)⁻¹ - (1-A)⁻¹ Aᵏ.
    have key : ∀ k, (∑ m ∈ Finset.range k, A ^ m) = (1 - A)⁻¹ - (1 - A)⁻¹ * A ^ k := by
      intro k
      have hnp : (1 - A) * (∑ m ∈ Finset.range k, A ^ m) = 1 - A ^ k :=
        neumann_partial A k
      have hBmul : (1 - A)⁻¹ * (1 - A) = 1 := Matrix.nonsing_inv_mul (1 - A) hu
      have hcancel : (1 - A)⁻¹ * ((1 - A) * (∑ m ∈ Finset.range k, A ^ m))
          = (1 - A)⁻¹ * (1 - A ^ k) := by rw [hnp]
      rw [← mul_assoc, hBmul, one_mul] at hcancel
      rw [hcancel, mul_sub, mul_one]
    -- Partial sums are entrywise nonnegative.
    have hg_nonneg : ∀ k, 0 ≤ (∑ m ∈ Finset.range k, A ^ m) i j := by
      intro k
      rw [Matrix.sum_apply]
      apply Finset.sum_nonneg
      intro m _
      exact pow_entry_nonneg h.nonneg m i j
    -- The remainder entry `((1-A)⁻¹ Aᵏ) i j` tends to 0.
    have hT : Filter.Tendsto (fun k => ((1 - A)⁻¹ * A ^ k) i j) Filter.atTop (nhds 0) := by
      have hsum : Filter.Tendsto (fun k => ∑ l : ι, (1 - A)⁻¹ i l * (A ^ k) l j)
          Filter.atTop (nhds (∑ l : ι, (1 - A)⁻¹ i l * 0)) := by
        apply tendsto_finsetSum
        intro l _
        exact (pow_entry_tendsto h l j).const_mul ((1 - A)⁻¹ i l)
      simp only [mul_zero, Finset.sum_const_zero] at hsum
      have heq : (fun k => ((1 - A)⁻¹ * A ^ k) i j)
          = (fun k => ∑ l : ι, (1 - A)⁻¹ i l * (A ^ k) l j) := by
        funext k; rw [Matrix.mul_apply]
      rw [heq]; exact hsum
    -- Hence the partial-sum entry tends to `(1-A)⁻¹ i j`.
    have hg_lim : Filter.Tendsto (fun k => (∑ m ∈ Finset.range k, A ^ m) i j)
        Filter.atTop (nhds ((1 - A)⁻¹ i j)) := by
      have heq2 : (fun k => (∑ m ∈ Finset.range k, A ^ m) i j)
          = (fun k => (1 - A)⁻¹ i j - ((1 - A)⁻¹ * A ^ k) i j) := by
        funext k; rw [key k, Matrix.sub_apply]
      rw [heq2]
      simpa only [sub_zero] using hT.const_sub ((1 - A)⁻¹ i j)
    exact ge_of_tendsto' hg_lim hg_nonneg
  · -- Non-invertible case: the inverse is the zero matrix by convention.
    rw [Matrix.nonsing_inv_apply_not_isUnit (1 - A) hu, Matrix.zero_apply]

end LeanUrat.MovesS
