/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp0
import Uniformity.ChapC.C132rp3

/-!
# Uniformity.ChapC.C132kp1 — μ₃ residual divisibility

**[M3-KP1, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6):
translate μ₃-divisibility into divisibility of the normalized μ₃ residual, and prove the
converse in the monic degree-`≤ 8`, nonunit-residual scope forced by the remainder argument.

## Informal argument

Forward, a witness `a ∼μ₃ gq` gives equal normalized residuals.  The universal normalized
convolution/product law then writes `R(gq) = R(g)R(q)`, so `R(g) ∣ R(a)`.

Backward, divide by the monic polynomial: `a = r + gq`.  If `r` lies strictly above `gq`,
this is already the required initial equivalence.  Otherwise the strong graded-add law and
the graded product law force `R(g)` to divide the exact graded residual of `r`.  Since
`deg r < deg g ≤ 8` and the development key has degree four, `r` has only slots zero and
one; the parity-two μ₃ grade line sees at most one of them.  Thus the exact graded residual
of nonzero `r` is a nonzero constant, contradicting that `R(g)` is not a unit.

The predicate `S2Mu3Minimal` does not enter this node: the concrete degree/nonunit fences
give the stronger remainder contradiction directly.  Minimality is a downstream
consequence/consumer of this translation, rather than an assumption in either direction.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132kp1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Initial-equivalence transport -/

/-- Initial equivalence preserves the normalized μ₃ residual. -/
theorem s2Mu3NormRes_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2Mu3InitialEquiv h2 hq g h) :
    s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [(S2Mu3InitialEquiv_zero_left h2 hq).mp hgh]
  · have hg := S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hg0
    have hh := S2Mu3ExactGrade_of_initialEquiv h2 hq hg hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hgzero, -⟩
    · have habove : S2Mu3AboveGrade h2 hq (s2Mu3GradeOf h2 hq g) (g - h) := by
        show ((s2Mu3GradeOf h2 hq g : ℕ) : WithTop ℤ) < s2Hgt₃ h2 hq (g - h)
        rw [← hg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu3GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu3GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      rw [s2Mu3NormRes_of_exact h2 hq hg, s2Mu3NormRes_of_exact h2 hq hh, hadd]
    · exact absurd hgzero hg0

/-! ## Forward translation -/

/-- μ₃-divisibility universally implies divisibility of normalized μ₃ residuals. -/
theorem mu3NormRes_dvd_of_S2Mu3Dvd {g a : Polynomial O} (h : S2Mu3Dvd h2 hq g a) :
    s2Mu3NormRes h2 hq g ∣ s2Mu3NormRes h2 hq a := by
  obtain ⟨q, hq'⟩ := h
  have heq := s2Mu3NormRes_eq_of_initialEquiv h2 hq hq'
  rw [s2Mu3NormRes_mul h2 hq] at heq
  exact ⟨s2Mu3NormRes h2 hq q, heq⟩

/-! ## Low-degree residuals -/

/-- Below twice the degree-four development key, every μ₃ graded residual is constant. -/
theorem s2Mu3GradedRes_eq_C_of_natDegree_lt_eight {g : Polynomial O}
    (hdeg : g.natDegree < 8) (β : ℕ) :
    s2Mu3GradedRes h2 hq β g =
      Polynomial.C ((s2Mu3GradedRes h2 hq β g).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => rw [Polynomial.coeff_C_zero]
  | t + 1 =>
    rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero t), s2Mu3GradedRes_coeff]
    refine s2Mu3Coeff_eq_zero_of_dv2Pin_top h2 hq ?_
    rw [dv2Pin, dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num)]
    · exact Uniformity.Density.Tower.dv2Hgt_zero _
    · rw [s2Φ₂_natDegree h2 hq]
      omega

/-- A nonzero polynomial of degree below eight has unit normalized μ₃ residual. -/
theorem s2Mu3NormRes_isUnit_of_natDegree_lt_eight {g : Polynomial O} (hg : g ≠ 0)
    (hdeg : g.natDegree < 8) : IsUnit (s2Mu3NormRes h2 hq g) := by
  have hex := S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hg
  have hC := s2Mu3GradedRes_eq_C_of_natDegree_lt_eight h2 hq hdeg
    (s2Mu3GradeOf h2 hq g)
  have hne := s2Mu3GradedRes_ne_zero_of_exact h2 hq hex
  have hγ : (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g).coeff 0 ≠ 0 := by
    intro h0
    rw [hC, h0, map_zero] at hne
    exact hne rfl
  rw [s2Mu3NormRes_of_exact h2 hq hex, hC, Polynomial.natTrailingDegree_C,
    Function.iterate_zero_apply]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)

/-- Extracted μ₃ grades add on nonzero products. -/
private theorem s2Mu3GradeOf_mul {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2Mu3GradeOf h2 hq (g * z) = s2Mu3GradeOf h2 hq g + s2Mu3GradeOf h2 hq z := by
  exact s2Mu3GradeOf_eq_of_exact h2 hq
    (S2Mu3ExactGrade_mul h2 hq
      (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hg)
      (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hz))

/-! ## Backward translation -/

/-- In the monic degree-`≤ 8`, nonunit-residual scope, residual divisibility implies
μ₃-divisibility. -/
theorem S2Mu3Dvd_of_mu3NormRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 8) (hnu : ¬ IsUnit (s2Mu3NormRes h2 hq g))
    (hdvd : s2Mu3NormRes h2 hq g ∣ s2Mu3NormRes h2 hq a) :
    S2Mu3Dvd h2 hq g a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact S2Mu3Dvd_zero h2 hq g
  have hmod : a %ₘ g + g * (a /ₘ g) = a := Polynomial.modByMonic_add_div a g
  rcases eq_or_ne (a %ₘ g) 0 with hr0 | hr0
  · exact S2Mu3Dvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
  rcases eq_or_ne (a /ₘ g) 0 with hw0 | hw0
  · exfalso
    have ha : a %ₘ g = a := by
      rw [hw0, mul_zero, add_zero] at hmod
      exact hmod
    have hdega : a.natDegree < 8 := by
      have h1 := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      rw [ha] at h1
      omega
    exact hnu (isUnit_of_dvd_unit hdvd
      (s2Mu3NormRes_isUnit_of_natDegree_lt_eight h2 hq ha0 hdega))
  have hgw0 : g * (a /ₘ g) ≠ 0 := mul_ne_zero hmon.ne_zero hw0
  have hexr := S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hr0
  have hexgw := S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hgw0
  have hvr : s2Hgt₃ h2 hq (a %ₘ g)
      = ((s2Mu3GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ) := hexr
  have hvgw : s2Hgt₃ h2 hq (g * (a /ₘ g))
      = ((s2Mu3GradeOf h2 hq (g * (a /ₘ g)) : ℕ) : WithTop ℤ) := hexgw
  rcases Nat.lt_or_ge (s2Mu3GradeOf h2 hq (g * (a /ₘ g)))
      (s2Mu3GradeOf h2 hq (a %ₘ g)) with hlt | hge
  · have hltv : s2Hgt₃ h2 hq (g * (a /ₘ g)) < s2Hgt₃ h2 hq (a %ₘ g) := by
      rw [hvr, hvgw]
      exact_mod_cast hlt
    have hadd := s2Hgt₃_add_eq h2 hq (a %ₘ g) (g * (a /ₘ g)) (ne_of_gt hltv)
    rw [hmod] at hadd
    have hva : s2Hgt₃ h2 hq a = s2Hgt₃ h2 hq (g * (a /ₘ g)) := by
      rw [hadd]
      exact min_eq_right (le_of_lt hltv)
    refine ⟨a /ₘ g, Or.inl ⟨?_, hva⟩⟩
    rw [show a - g * (a /ₘ g) = a %ₘ g from sub_eq_of_eq_add hmod.symm, hva]
    exact hltv
  · exfalso
    have hψg : s2Mu3NormRes h2 hq g
        ∣ s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
      rcases (ge_iff_le.mp hge).lt_or_eq with hlt' | heq'
      · rw [s2Mu3GradedRes_zero_of_above h2 hq
          (show ((s2Mu3GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
              < s2Hgt₃ h2 hq (g * (a /ₘ g)) from by rw [hvgw]; exact_mod_cast hlt')]
        exact dvd_zero _
      · have hmul := s2Mu3GradedRes_mul_of_exact h2 hq
          (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hmon.ne_zero)
          (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hw0)
        have hsum := s2Mu3GradeOf_mul h2 hq hmon.ne_zero hw0
        rw [heq', hsum, hmul]
        have hrec : s2Mu3NormRes h2 hq g
            ∣ s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g :=
          ⟨Polynomial.X ^
              (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq g) g).natTrailingDegree,
            (s2Mu3NormRes_mul_X_pow_of_exact h2 hq
              (S2Mu3ExactGrade_s2Mu3GradeOf h2 hq hmon.ne_zero)).symm⟩
        exact Dvd.dvd.mul_left (hrec.mul_right _) _
    have hβr_le_a : ((s2Mu3GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
        ≤ s2Hgt₃ h2 hq a := by
      have hmin := s2Hgt₃_add_ge h2 hq (a %ₘ g) (g * (a /ₘ g))
      rw [hmod] at hmin
      refine le_trans ?_ hmin
      rw [hvr, hvgw]
      exact le_min le_rfl (by exact_mod_cast hge)
    have hψa : s2Mu3NormRes h2 hq g
        ∣ s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) a := by
      rcases hβr_le_a.lt_or_eq with hlt' | heq'
      · rw [s2Mu3GradedRes_zero_of_above h2 hq hlt']
        exact dvd_zero _
      · exact dvd_trans hdvd
          ⟨Polynomial.X ^
              (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) a).natTrailingDegree,
            (s2Mu3NormRes_mul_X_pow_of_exact h2 hq heq'.symm).symm⟩
    have h1 : ((s2Mu3GradeOf h2 hq (a %ₘ g) : ℕ) : ℕ∞)
        ≤ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
          (g * (a /ₘ g)) 21 2 := by
      rw [(S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hexgw]
      exact_mod_cast hge
    have haddres := s2Mu3GradedRes_add_of_le h2 hq
      (le_of_eq ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mp hexr).symm) h1
    rw [hmod] at haddres
    have hψr : s2Mu3NormRes h2 hq g
        ∣ s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) (a %ₘ g) := by
      have hsub : s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) (a %ₘ g)
          = s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) a
            - s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
        rw [haddres]
        ring
      rw [hsub]
      exact dvd_sub hψa hψg
    have hdegr : (a %ₘ g).natDegree < 8 := by
      have h2' := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      omega
    have hC := s2Mu3GradedRes_eq_C_of_natDegree_lt_eight h2 hq hdegr
      (s2Mu3GradeOf h2 hq (a %ₘ g))
    have hne := s2Mu3GradedRes_ne_zero_of_exact h2 hq hexr
    have hγ :
        (s2Mu3GradedRes h2 hq (s2Mu3GradeOf h2 hq (a %ₘ g)) (a %ₘ g)).coeff 0 ≠ 0 := by
      intro h0
      rw [hC, h0, map_zero] at hne
      exact hne rfl
    rw [hC] at hψr
    exact hnu (isUnit_of_dvd_unit hψr
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)))

/-! ## Packaged equivalence -/

/-- The μ₃-divisibility/residual-divisibility equivalence in its honest monic scope. -/
theorem S2Mu3Dvd_iff_mu3NormRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 8) (hnu : ¬ IsUnit (s2Mu3NormRes h2 hq g)) :
    S2Mu3Dvd h2 hq g a ↔ s2Mu3NormRes h2 hq g ∣ s2Mu3NormRes h2 hq a :=
  ⟨mu3NormRes_dvd_of_S2Mu3Dvd h2 hq,
    S2Mu3Dvd_of_mu3NormRes_dvd h2 hq hmon hdeg hnu⟩

end S2

end Uniformity.Density.Tower.C132kp1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp1.s2Mu3NormRes_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C132kp1.mu3NormRes_dvd_of_S2Mu3Dvd
#print axioms Uniformity.Density.Tower.C132kp1.s2Mu3GradedRes_eq_C_of_natDegree_lt_eight
#print axioms Uniformity.Density.Tower.C132kp1.s2Mu3NormRes_isUnit_of_natDegree_lt_eight
#print axioms Uniformity.Density.Tower.C132kp1.S2Mu3Dvd_of_mu3NormRes_dvd
#print axioms Uniformity.Density.Tower.C132kp1.S2Mu3Dvd_iff_mu3NormRes_dvd

end AxCheck
