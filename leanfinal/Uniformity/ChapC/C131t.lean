/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131a
import Uniformity.ChapC.C131k
import Uniformity.ChapC.C131p
import Uniformity.ChapC.C11
import Uniformity.ChapC.C44
import Uniformity.ChapB.B32a

/-!
# Uniformity.ChapC.C131t — weight-to-height conversion and strict exactness

**Chapter C, NODES C.131t′ + C.131x′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §3.5 and §3.9).

The first theorem identifies C.11's level-two height with the two-index weight of the
canonical reduced normal form.  Both finite ranges are converted to polynomial supports;
zero coefficients therefore contribute `⊤` on either presentation.

The second theorem is the strict ultrametric equality needed by the faithful band.  Its
strictness is additional information beyond the floor inequality: a coefficient attaining
the shallower weight cannot cancel against a coefficient of strictly greater weight.

## Status

Both nodes land.  Zero `sorry`; axiom footprint Lean core only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131t

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131k
open Uniformity.Density.Tower.C131p

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ}
variable {hpin : npHgt Polynomial.X F.key
  (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}

/-- **NODE C.131t′ (Cnv11).** C.11's level-two height is exactly the two-index weight of
the canonical reduced `F.key`-normal form. -/
theorem dv2Hgt_eq_WT_phiNF (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (A : Polynomial O) :
    dv2Hgt (T.levelDatum hπ) A = WT T (xNF F A) := by
  rw [dv2Hgt]
  change dvSupp F A T.u₂ T.e₂ = _
  rw [dvSupp_eq_nested_inf F A T.u₂ T.e₂ T.he₂]
  change
    (Finset.range (A.natDegree + 1)).inf (fun b ↦
      (Finset.range ((dev F.key A b).natDegree + 1)).inf (fun a ↦
        wtCoeff T ((dev F.key A b).coeff a) a b)) = _
  have hinner : ∀ b,
      (Finset.range ((dev F.key A b).natDegree + 1)).inf (fun a ↦
          wtCoeff T ((dev F.key A b).coeff a) a b) =
        ((xNF F A).coeff b).support.inf (fun a ↦
          wtCoeff T (((xNF F A).coeff b).coeff a) a b) := by
    intro b
    rw [xNF_coeff, xDigit_eq_dev]
    exact inf_range_eq_inf_support (dev F.key A b) _
      Polynomial.supp_subset_range_natDegree_succ (fun c a ↦ wtCoeff T c a b)
      (fun a ↦ wtCoeff_zero T a b)
  simp_rw [hinner]
  classical
  have houter : (xNF F A).support ⊆ Finset.range (A.natDegree + 1) := by
    intro b hb
    rw [Finset.mem_range]
    by_contra hlt
    have hbnot : b ∉ Finset.range (A.natDegree + 1) := by
      simpa [Finset.mem_range] using hlt
    have hz : (xNF F A).coeff b = 0 := by
      simp [xNF, finsetSum_coeff, hbnot]
    exact (Polynomial.mem_support_iff.mp hb) hz
  unfold WT
  exact inf_range_eq_inf_support (xNF F A) (A.natDegree + 1) houter
    (fun P b ↦ P.support.inf fun a ↦ wtCoeff T (P.coeff a) a b) (by simp)

private theorem wtCoeff_add_eq_left_of_lt (T : TowerDatum F H₀ hpin)
    (x y : O) (a b : ℕ) (h : wtCoeff T x a b < wtCoeff T y a b) :
    wtCoeff T (x + y) a b = wtCoeff T x a b := by
  let k : ℕ∞ := (a * (T.e₂ * F.h) + b * T.u₂ : ℕ)
  have hk : k ≠ ⊤ := ENat.coe_ne_top _
  have hmul : (F.e₁ * T.e₂) • addVal O x < (F.e₁ * T.e₂) • addVal O y := by
    exact (ENat.add_lt_add_iff_right hk).mp h
  have hv : addVal O x < addVal O y :=
    lt_of_nsmul_lt_nsmul_right (F.e₁ * T.e₂) hmul
  unfold wtCoeff
  exact congrArg (fun v : ℕ∞ ↦ (F.e₁ * T.e₂) • v + k)
    ((addVal O).map_add_eq_of_lt_left hv)

private theorem WT_add_eq_left_of_lt (T : TowerDatum F H₀ hpin)
    (P Q : Polynomial (Polynomial O)) (h : WT T P < WT T Q) :
    WT T (P + Q) = WT T P := by
  classical
  have hP : P.support.Nonempty := by
    rw [Polynomial.support_nonempty]
    intro hzero
    subst P
    rw [WT_zero] at h
    exact (not_lt_of_ge le_top) h
  rcases Finset.exists_mem_eq_inf P.support hP (fun b ↦
      (P.coeff b).support.inf fun a ↦ wtCoeff T ((P.coeff b).coeff a) a b) with
    ⟨b, hb, hbmin⟩
  have hPb : (P.coeff b).support.Nonempty :=
    Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hb)
  rcases Finset.exists_mem_eq_inf (P.coeff b).support hPb
      (fun a ↦ wtCoeff T ((P.coeff b).coeff a) a b) with ⟨a, ha, hamin⟩
  have hPa : WT T P = wtCoeff T ((P.coeff b).coeff a) a b := hbmin.trans hamin
  have hstrict :
      wtCoeff T ((P.coeff b).coeff a) a b < wtCoeff T ((Q.coeff b).coeff a) a b := by
    calc
      wtCoeff T ((P.coeff b).coeff a) a b = WT T P := hPa.symm
      _ < WT T Q := h
      _ ≤ wtCoeff T ((Q.coeff b).coeff a) a b := WT_le_wtCoeff T Q a b
  have hu : WT T (P + Q) ≤ WT T P := by
    calc
      WT T (P + Q) ≤ wtCoeff T (((P + Q).coeff b).coeff a) a b :=
        WT_le_wtCoeff T (P + Q) a b
      _ = wtCoeff T ((P.coeff b).coeff a + (Q.coeff b).coeff a) a b := by
        rw [Polynomial.coeff_add, Polynomial.coeff_add]
      _ = wtCoeff T ((P.coeff b).coeff a) a b :=
        wtCoeff_add_eq_left_of_lt T _ _ a b hstrict
      _ = WT T P := hPa.symm
  have hl : WT T P ≤ WT T (P + Q) := by
    simpa [min_eq_left h.le] using WT_add T P Q
  exact le_antisymm hu hl

/-- **NODE C.131x′ (Cnv15).** Adding a strictly deeper summand does not change level-two
height. -/
theorem dv2Hgt_add_eq_left_of_lt (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (A B : Polynomial O)
    (h : dv2Hgt (T.levelDatum hπ) A < dv2Hgt (T.levelDatum hπ) B) :
    dv2Hgt (T.levelDatum hπ) (A + B) = dv2Hgt (T.levelDatum hπ) A := by
  have hxNF : xNF F (A + B) = xNF F A + xNF F B := by
    apply Polynomial.ext
    intro b
    rw [xNF_coeff, Polynomial.coeff_add, xNF_coeff, xNF_coeff]
    simp only [xDigit_eq_dev]
    exact dev_add_of_monic F.hmonic A B b
  have hWT : WT T (xNF F A) < WT T (xNF F B) := by
    simpa only [← dv2Hgt_eq_WT_phiNF T hπ] using h
  rw [dv2Hgt_eq_WT_phiNF T hπ, hxNF, WT_add_eq_left_of_lt T _ _ hWT,
    ← dv2Hgt_eq_WT_phiNF T hπ]

end Uniformity.Density.Tower.C131t

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131t.dv2Hgt_eq_WT_phiNF
#print axioms Uniformity.Density.Tower.C131t.dv2Hgt_add_eq_left_of_lt

end AxCheck
