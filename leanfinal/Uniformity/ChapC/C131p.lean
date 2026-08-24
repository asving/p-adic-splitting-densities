/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C06
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06

/-!
# Uniformity.ChapC.C131p — conversion utilities for the dv-graded engine v2

**Chapter C, NODES C.131p′–s′** (`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md`
§3.1–§3.4): the finite-infimum calculus in `ℕ∞`, coefficientwise flattening of
`stageHeight`, `dvHgt`, and `dvSupp`, and recovery of a displayed reduced development.

The positive hypothesis in `enat_nsmul_finset_inf` is essential: the empty infimum is `⊤`,
whereas `0 • ⊤ = 0`.  Addition needs no finiteness hypothesis because `⊤` is absorbing.
The nested-infimum identity is mathlib's `Finset.inf_sigma`, merely oriented in the direction
used by the conversion engine.

The final flattened `dvSupp` formula is an equality for the actual canonical development.
There is no cancellation or support-level approximation in its proof.

## Status

All four nodes land.  Zero `sorry`; axiom footprint Lean core only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131p

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

/-! ## C.131p′ — finite infima in `ℕ∞` -/

private theorem enat_nsmul_inf (n : ℕ) (a b : ℕ∞) :
    n • (a ⊓ b) = n • a ⊓ n • b := by
  rcases le_total a b with h | h
  · rw [inf_eq_left.2 h, inf_eq_left.2 (nsmul_le_nsmul_right h n)]
  · rw [inf_eq_right.2 h, inf_eq_right.2 (nsmul_le_nsmul_right h n)]

/-- **Cnv1.** A positive natural scalar commutes with a finite `ℕ∞`-infimum, including
the empty infimum. -/
theorem enat_nsmul_finset_inf {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) {n : ℕ}
    (hn : 0 < n) : n • s.inf f = s.inf (fun i ↦ n • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nsmul_eq_mul, hn.ne']
  | @insert a s ha ih =>
      rw [Finset.inf_insert, Finset.inf_insert, enat_nsmul_inf, ih]

private theorem enat_add_inf (c a b : ℕ∞) :
    c + (a ⊓ b) = (c + a) ⊓ (c + b) := by
  rcases le_total a b with h | h
  · rw [inf_eq_left.2 h, inf_eq_left.2 (add_le_add_right h c)]
  · rw [inf_eq_right.2 h, inf_eq_right.2 (add_le_add_right h c)]

/-- **Cnv2, left form.** Addition by an `ℕ∞` constant commutes with a finite infimum. -/
theorem enat_add_finset_inf {ι : Type*} (c : ℕ∞) (s : Finset ι) (f : ι → ℕ∞) :
    c + s.inf f = s.inf (fun i ↦ c + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.inf_insert, Finset.inf_insert, enat_add_inf, ih]

/-- **Cnv2, right form.** Right addition by a constant commutes with a finite infimum. -/
theorem enat_finset_inf_add {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) (c : ℕ∞) :
    s.inf f + c = s.inf (fun i ↦ f i + c) := by
  simpa [add_comm] using enat_add_finset_inf c s f

/-- **Cnv3.** A nested finite infimum is the infimum over the corresponding dependent
`Finset.sigma`. -/
theorem finset_inf_sigma {ι : Type*} {α : ι → Type*} (s : Finset ι)
    (t : (i : ι) → Finset (α i)) (f : (i : ι) × α i → ℕ∞) :
    s.inf (fun i ↦ (t i).inf fun a ↦ f ⟨i, a⟩) = (s.sigma t).inf f :=
  (Finset.inf_sigma s t f).symm

/-- **Cnv4.** A coefficient weight whose zero value is `⊤` has the same infimum over any
range containing the polynomial support as it does over the support itself. -/
theorem inf_range_eq_inf_support {R : Type*} [Semiring R] (p : Polynomial R) (N : ℕ)
    (hN : p.support ⊆ Finset.range N) (w : R → ℕ → ℕ∞)
    (hw : ∀ i, w 0 i = ⊤) :
    (Finset.range N).inf (fun i ↦ w (p.coeff i) i) =
      p.support.inf (fun i ↦ w (p.coeff i) i) := by
  apply le_antisymm
  · refine Finset.le_inf fun i hi ↦ ?_
    exact Finset.inf_le (hN hi)
  · refine Finset.le_inf fun i hi ↦ ?_
    by_cases hzero : p.coeff i = 0
    · rw [hzero, hw]
      exact le_top
    · exact Finset.inf_le (Polynomial.mem_support_iff.mpr hzero)

/-! ## C.131q′ — flatten `stageHeight` -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

private theorem key_natDegree_pos (F : KeyFrame O π) : 0 < F.key.natDegree := by
  rw [F.hdeg]
  exact Nat.mul_pos F.he₁ F.hf₁

/-- **Cnv5.** The Gauss valuation of a constant polynomial is its coefficient valuation. -/
theorem gaussVal_C_eq_addVal (c : O) :
    gaussVal (Polynomial.C c) = addVal O c := by
  simp [gaussVal]

/-- **Cnv6.** `stageHeight` flattened to the scalar coefficients of its input. -/
theorem stageHeight_eq_coeff_inf (F : KeyFrame O π) (A : Polynomial O) :
    F.stageHeight A =
      (Finset.range (A.natDegree + 1)).inf
        (fun a ↦ F.e₁ • addVal O (A.coeff a) + (F.h * a : ℕ∞)) := by
  rw [F.stageHeight_eq_inf]
  simp only [gaussVal_C_eq_addVal]

/-! ## C.131r′ — flatten `dvHgt` and `dvSupp` -/

/-- **Cnv7.** `dvHgt` flattened to the scalar coefficients of the relevant canonical digit. -/
theorem dvHgt_eq_coeff_inf (F : KeyFrame O π) (A : Polynomial O) (b : ℕ) :
    dvHgt F A b =
      (Finset.range ((dev F.key A b).natDegree + 1)).inf
        (fun a ↦ F.e₁ • addVal O ((dev F.key A b).coeff a) + (F.h * a : ℕ∞)) :=
  stageHeight_eq_coeff_inf F (dev F.key A b)

/-- The unnormalised intermediate form of Cnv8.  Keeping this public makes later consumers
able to choose either the structural or arithmetic presentation of the weight. -/
theorem dvSupp_eq_nested_inf' (F : KeyFrame O π) (A : Polynomial O) (u₂ e₂ : ℕ)
    (he₂ : 0 < e₂) :
    dvSupp F A u₂ e₂ =
      (Finset.range (A.natDegree + 1)).inf (fun b ↦
        (Finset.range ((dev F.key A b).natDegree + 1)).inf (fun a ↦
          e₂ • (F.e₁ • addVal O ((dev F.key A b).coeff a) + (F.h * a : ℕ∞)) +
            (u₂ * b : ℕ∞))) := by
  rw [dvSupp]
  apply Finset.inf_congr rfl
  intro b _
  rw [dvHgt_eq_coeff_inf, enat_nsmul_finset_inf _ _ he₂, enat_finset_inf_add]

private theorem weight_norm (e₁ e₂ h a u b : ℕ) (v : ℕ∞) :
    e₂ • (e₁ • v + (h * a : ℕ∞)) + (u * b : ℕ∞) =
      (e₁ * e₂) • v + (a * (e₂ * h) + b * u : ℕ∞) := by
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

/-- **Cnv8.** The cleared level support is the nested infimum of the two-index scalar weight. -/
theorem dvSupp_eq_nested_inf (F : KeyFrame O π) (A : Polynomial O) (u₂ e₂ : ℕ)
    (he₂ : 0 < e₂) :
    dvSupp F A u₂ e₂ =
      (Finset.range (A.natDegree + 1)).inf (fun b ↦
        (Finset.range ((dev F.key A b).natDegree + 1)).inf (fun a ↦
          (F.e₁ * e₂) • addVal O ((dev F.key A b).coeff a) +
            (a * (e₂ * F.h) + b * u₂ : ℕ∞))) := by
  rw [dvSupp_eq_nested_inf' F A u₂ e₂ he₂]
  apply Finset.inf_congr rfl
  intro b _
  apply Finset.inf_congr rfl
  intro a _
  exact weight_norm F.e₁ e₂ F.h a u₂ b _

/-! ## C.131s′ — recovery of a reduced displayed development -/

/-- **Cnv9, in-range clause.** Any displayed, degree-reduced `F.key`-development is the
canonical development coefficientwise throughout its reconstruction range. -/
theorem dev_reconstruct_reduced (F : KeyFrame O π) (A : Polynomial O)
    (digit : ℕ → Polynomial O) (B : ℕ)
    (hdeg : ∀ b, (digit b).degree < F.key.degree)
    (hsum : ∑ b ∈ Finset.range B, digit b * F.key ^ b = A) :
    ∀ b < B, dev F.key A b = digit b := by
  intro b hb
  exact (dev_unique F.hmonic (key_natDegree_pos F) hdeg hsum b hb).symm

/-- **Cnv9, tail clause.** Once an index is past the degree bound, the canonical development
coefficient vanishes. -/
theorem dev_reconstruct_reduced_tail (F : KeyFrame O π) (A : Polynomial O) (b : ℕ)
    (hpast : A.natDegree < b * F.key.natDegree) :
    dev F.key A b = 0 :=
  dev_eq_zero_of_lt F.hmonic (key_natDegree_pos F) A b hpast

end Uniformity.Density.Tower.C131p

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131p.enat_nsmul_finset_inf
#print axioms Uniformity.Density.Tower.C131p.enat_add_finset_inf
#print axioms Uniformity.Density.Tower.C131p.enat_finset_inf_add
#print axioms Uniformity.Density.Tower.C131p.finset_inf_sigma
#print axioms Uniformity.Density.Tower.C131p.inf_range_eq_inf_support
#print axioms Uniformity.Density.Tower.C131p.gaussVal_C_eq_addVal
#print axioms Uniformity.Density.Tower.C131p.stageHeight_eq_coeff_inf
#print axioms Uniformity.Density.Tower.C131p.dvHgt_eq_coeff_inf
#print axioms Uniformity.Density.Tower.C131p.dvSupp_eq_nested_inf'
#print axioms Uniformity.Density.Tower.C131p.dvSupp_eq_nested_inf
#print axioms Uniformity.Density.Tower.C131p.dev_reconstruct_reduced
#print axioms Uniformity.Density.Tower.C131p.dev_reconstruct_reduced_tail

end AxCheck
