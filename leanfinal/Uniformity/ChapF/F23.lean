/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Field.Basic

/-!
# Uniformity.ChapF.F23 — WM-FENCE, the FIXED-DATA character-triviality criterion

**Chapter F, NODE F.23** [lemma] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1 +
`[Finite K]`. Transcribed from `EFF.WELDMASTER.25`'s displayed pair: for a finite field
`K`, a unit `z : Kˣ` and `A : ℤ`, the absolute form
`(∀ i, z ^ (i * A) = 1) ↔ (orderOf z : ℤ) ∣ A` and the slot-grid form
`(∀ i, z ^ (e * i * A) = 1) ↔ (orderOf z : ℤ) ∣ e * A`.

**The F-4 scoping, carried in the statement (this is the node's contract).** Neither
display contains an existential quantifier over the fixed inputs: the criterion TESTS FIXED
DATA — it supplies NO freedom or existence theorem for varying `z`, `A`, the attained set,
or the representative. Any such variation a consumer needs must be proved by J-D0
independently (the corrected S6 clause); the DAG edge into WM-FENCE carries this scoping.

**Never conflate the criterion with the law.** `PERIM-μ` — the one-perimeter LAW that this
criterion's condition holds on all claimed order-≥2 faces — is HYP.86, **OUT of cone** (§3
row 9, `BLOCKED: OUT-OF-CONE`; the string occurs in zero of the twenty cone notes). What is
transcribed here is only the criterion, an iff about fixed data.

Were `axiom` stubs at stage 0e (two rows); PROVED here. The source's `F₅` witness
(`ord(2) = 4 ∤ 1`, `χ₁ = 2⁻¹ = 3 ≠ 1`) and the both-prime instances fire as gate
certificates at F.30 leg 1.
-/

namespace Uniformity.Density.Weld

/-- WM-FENCE, absolute form (`EFF.WELDMASTER.25`): the character `i ↦ z ^ (i * A)` is
trivial exactly when the order of `z` divides `A`. A criterion on FIXED `(z, A)` — no
existential over the inputs, hence no freedom or existence content. -/
theorem wmFence_absolute {K : Type*} [Field K] [Finite K] (z : Kˣ) (A : ℤ) :
    (∀ i : ℤ, z ^ (i * A) = 1) ↔ ((orderOf z : ℤ) ∣ A) := by
  constructor
  · intro h
    have h1 := h 1
    rw [one_mul] at h1
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  · intro h i
    have hA : z ^ A = 1 := orderOf_dvd_iff_zpow_eq_one.mp h
    rw [mul_comm, zpow_mul, hA, one_zpow]

/-- WM-FENCE, slot-grid form (`EFF.WELDMASTER.25`): the same criterion on the `e`-spaced
grid, i.e. the absolute form at `A' = e * A`. Same F-4 scoping: fixed data only. -/
theorem wmFence_slotGrid {K : Type*} [Field K] [Finite K] (z : Kˣ) (e A : ℤ) :
    (∀ i : ℤ, z ^ (e * i * A) = 1) ↔ ((orderOf z : ℤ) ∣ e * A) := by
  rw [← wmFence_absolute z (e * A)]
  constructor
  · intro h i
    rw [show i * (e * A) = e * i * A by rw [← mul_assoc, mul_comm i e]]
    exact h i
  · intro h i
    rw [show e * i * A = i * (e * A) by rw [mul_comm e i, mul_assoc]]
    exact h i

end Uniformity.Density.Weld
