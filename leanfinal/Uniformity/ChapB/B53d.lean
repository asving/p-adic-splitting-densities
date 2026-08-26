/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B53c

/-!
# Uniformity.ChapB.B53d — quotient-symmetric norm valuations

**Chapter B, NODE B.53, probe-complete quotient/norm API**
(`docs/in-progress/BLOCKERS_PLAN_2026-08-26.md`, nodes F2.1–F2.2).

This file packages the generic consequences of B.53a's quotient symmetry and B.53c's
determinant–length dictionary.

* `normA_ne_zero_of_normB_ne_zero` and `normB_ne_zero_of_normA_ne_zero` transfer a supplied
  nonzero scalar-membership certificate across `quotKeyEquiv`, in the two orientations, and
  deduce nonvanishing of the opposite generator's norm.
* `addVal_norm_symm` identifies the two norm valuations when both norms are nonzero.

The contract is deliberately membership-assisted: ramified exactness supplies scalar
membership; quotient symmetry transfers it. No bare implication between the two norms'
nonvanishing is asserted.

## Status

Sorry-free and axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Scalar-membership transfer in both orientations -/

/-- A nonzero scalar in the `AdjoinRoot φ`-side generator ideal transfers through
`quotKeyEquiv` and forces the `AdjoinRoot g`-side generator norm to be nonzero. -/
theorem normA_ne_zero_of_normB_ne_zero {φ g : Polynomial O}
    (hg : g.Monic) {c : O} (hc : c ≠ 0)
    (hmemB : algebraMap O (AdjoinRoot φ) c ∈ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) :
    Algebra.norm O (AdjoinRoot.mk g φ) ≠ 0 := by
  classical
  haveI : Module.Free O (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  have hrkA : Module.finrank O (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg).finrank]
    rfl
  have hmemA : algebraMap O (AdjoinRoot g) c ∈ Ideal.span {AdjoinRoot.mk g φ} := by
    have h2 : algebraMap O (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) c
        = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemB
    have h3 : algebraMap O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ}) c = 0 :=
      (quotKeyEquiv φ g).injective
        (by rw [(quotKeyEquiv φ g).commutes, h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmemA
  intro hzero
  have hnn : Algebra.norm O (algebraMap O (AdjoinRoot g) c) = 0 := by
    rw [hw, map_mul, hzero, zero_mul]
  rw [Algebra.norm_algebraMap, hrkA] at hnn
  exact (pow_ne_zero _ hc) hnn

/-- A nonzero scalar in the `AdjoinRoot g`-side generator ideal transfers through
`quotKeyEquiv` and forces the `AdjoinRoot φ`-side generator norm to be nonzero. -/
theorem normB_ne_zero_of_normA_ne_zero {φ g : Polynomial O}
    (hφ : φ.Monic) {c : O} (hc : c ≠ 0)
    (hmemA : algebraMap O (AdjoinRoot g) c ∈ Ideal.span {AdjoinRoot.mk g φ}) :
    Algebra.norm O (AdjoinRoot.mk φ (dev φ g 0)) ≠ 0 := by
  classical
  haveI : Module.Free O (AdjoinRoot φ) := Module.Free.of_basis (AdjoinRoot.powerBasis' hφ).basis
  haveI : Module.Finite O (AdjoinRoot φ) := (AdjoinRoot.powerBasis' hφ).finite
  have hrkB : Module.finrank O (AdjoinRoot φ) = φ.natDegree := by
    rw [(AdjoinRoot.powerBasis' hφ).finrank]
    rfl
  have hmemB : algebraMap O (AdjoinRoot φ) c
      ∈ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)} := by
    have h2 : algebraMap O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ}) c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmemA
    have h3 : algebraMap O
        (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) c = 0 := by
      rw [← (quotKeyEquiv φ g).commutes, h2, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmemB
  intro hzero
  have hnn : Algebra.norm O (algebraMap O (AdjoinRoot φ) c) = 0 := by
    rw [hw, map_mul, hzero, zero_mul]
  rw [Algebra.norm_algebraMap, hrkB] at hnn
  exact (pow_ne_zero _ hc) hnn

/-! ## Norm-valuation symmetry -/

/-- The norm valuations of the two quotient-symmetric generator evaluations agree for monic
positive-degree polynomials, provided both norms are nonzero. -/
theorem addVal_norm_symm (hπ : Irreducible π) {φ g : Polynomial O}
    (hφ : φ.Monic) (hg : g.Monic) (hdφ : 0 < φ.natDegree) (hdg : 0 < g.natDegree)
    (hnzA : Algebra.norm O (AdjoinRoot.mk g φ) ≠ 0)
    (hnzB : Algebra.norm O (AdjoinRoot.mk φ (dev φ g 0)) ≠ 0) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O (AdjoinRoot.mk g φ))
      = IsDiscreteValuationRing.addVal O
          (Algebra.norm O (AdjoinRoot.mk φ (dev φ g 0))) := by
  classical
  haveI : Module.Free O (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : Module.Free O (AdjoinRoot φ) := Module.Free.of_basis (AdjoinRoot.powerBasis' hφ).basis
  haveI : Module.Finite O (AdjoinRoot φ) := (AdjoinRoot.powerBasis' hφ).finite
  have hrkA : Module.finrank O (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg).finrank]
    rfl
  have hrkB : Module.finrank O (AdjoinRoot φ) = φ.natDegree := by
    rw [(AdjoinRoot.powerBasis' hφ).finrank]
    rfl
  have hrA : 0 < Module.finrank O (AdjoinRoot g) := by
    rw [hrkA]
    exact hdg
  have hrB : 0 < Module.finrank O (AdjoinRoot φ) := by
    rw [hrkB]
    exact hdφ
  rw [← length_quot_eq_addVal_norm hπ hrA hnzA,
    ← length_quot_eq_addVal_norm hπ hrB hnzB]
  exact (quotKeyEquiv φ g).toLinearEquiv.length_eq

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.normA_ne_zero_of_normB_ne_zero
#print axioms Uniformity.Density.Leaf.normB_ne_zero_of_normA_ne_zero
#print axioms Uniformity.Density.Leaf.addVal_norm_symm
end AxCheck
