/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp9

/-!
# Uniformity.ChapC.C132rp10 — the μ₃ residual-existence route is blocked

**[M3-RP10, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6).

The two-element-field part of the advertised numeral reuse does go through: every admissible
monic degree-one residual is `X + 1`.  The intended recipe polynomial

`Φ₂² - 2⁴ Φ'`

is also monic of degree eight.  However, M3-RP9's literal recipe theorem cannot prove its
μ₃ residual.  That theorem requires its correction term to have exact μ₃ grade `21` and
degree below `4`, while `s2Mu3_recipe_grade_twenty_one_vacuous` proves those hypotheses
inconsistent.  In particular it refutes the intended correction `2⁴ Φ'`.

Consequently this file records the successful collapse and degree-eight polynomial
bookkeeping, then lands the exact **BLOCKED-BECAUSE** certificate.  It does not invent a
replacement recipe statement or a fresh direct residual computation; either would cross this
row's `REUSE-WITH-NUMERALS` boundary.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp10

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp0
open Uniformity.Density.Tower.C132rp1 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132rp9

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- Every admissible monic linear residual over the two-element stage field is `X + 1`.
This is the public-μ₃ spelling of C130rp11's two-element-field collapse. -/
theorem s2Mu3_unique_admissible_linear (p : Polynomial ((s2DepthTwo h2 hq).fld 2))
    (hp : p.Monic) (hdeg : p.natDegree = 1) (hc : p.coeff 0 ≠ 0) :
    p = Polynomial.X + 1 := by
  obtain ⟨a, b, hab⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
  have hb : p.coeff 0 = b := by rw [hab]; simp
  have ha : p.coeff 1 = a := by rw [hab]; simp
  have ha1 : a = 1 := by
    have hlead : p.coeff p.natDegree = 1 := hp
    rw [hdeg, ha] at hlead
    exact hlead
  have hb1 : b = 1 := s2Fld₂_eq_one_of_ne_zero h2 hq (hb ▸ hc)
  rw [hab, ha1, hb1, map_one, one_mul]

/-- `X + 1` is an irreducible degree-one polynomial over the μ₃ residual field. -/
theorem s2Mu3_X_add_one_irreducible :
    Irreducible (Polynomial.X + 1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) := by
  letI : Field ((s2DepthTwo h2 hq).fld 2) := (s2DepthTwo h2 hq).fldField 2
  refine Polynomial.irreducible_of_degree_eq_one ?_
  rw [show (1 : Polynomial ((s2DepthTwo h2 hq).fld 2)) = Polynomial.C 1 from (map_one _).symm]
  exact Polynomial.degree_X_add_C 1

/-- The intended correction term `2⁴ Φ'` has degree strictly below `Φ₂`. -/
private theorem correction_natDegree_lt_key :
    (Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree <
      (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree := by
  rw [s2Φ₂_natDegree h2 hq]
  exact s2Mu3_chainNormBelow_tooth_degree h2 hq

/-- The intended recipe polynomial `Φ₂² - 2⁴ Φ'` is monic. -/
theorem s2Mu3_gEight_monic :
    ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 -
      Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1).Monic := by
  have hpow : ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2).Monic :=
    (s2Φ₂_monic h2 hq).pow 2
  apply hpow.sub_of_left
  exact Polynomial.degree_lt_degree (by
    rw [pow_two, Polynomial.natDegree_mul (s2Φ₂_monic h2 hq).ne_zero
      (s2Φ₂_monic h2 hq).ne_zero, s2Φ₂_natDegree h2 hq]
    have h := correction_natDegree_lt_key h2 hq
    rw [s2Φ₂_natDegree h2 hq] at h
    omega)

/-- The intended recipe polynomial has the required degree `8 = 2·1·deg(Φ₂)`. -/
theorem s2Mu3_gEight_natDegree :
    ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 -
      Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree = 8 := by
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · rw [pow_two, Polynomial.natDegree_mul (s2Φ₂_monic h2 hq).ne_zero
      (s2Φ₂_monic h2 hq).ne_zero, s2Φ₂_natDegree h2 hq]
  · have h := correction_natDegree_lt_key h2 hq
    rw [s2Φ₂_natDegree h2 hq] at h
    rw [pow_two, Polynomial.natDegree_mul (s2Φ₂_monic h2 hq).ne_zero
      (s2Φ₂_monic h2 hq).ne_zero, s2Φ₂_natDegree h2 hq]
    omega

/-- **BLOCKED-BECAUSE certificate:** there is no correction polynomial satisfying the
literal hypotheses needed to instantiate M3-RP9's μ₃ recipe theorem. -/
theorem s2Mu3_recipe_correction_input_impossible :
    ¬ ∃ khat : Polynomial O,
      S2Mu3ExactGrade h2 hq 21 khat ∧
        khat.natDegree < (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree := by
  rintro ⟨khat, hkhat, hdeg⟩
  apply s2Mu3_recipe_grade_twenty_one_vacuous h2 hq
    (by rw [s2Φ₂_natDegree h2 hq] at hdeg; exact hdeg)
  exact hkhat

/-- The blocker fires on the intended correction `2⁴ Φ'` itself.  Thus the monic
degree-eight polynomial above cannot be fed to the only landed recipe engine. -/
theorem s2Mu3_gEight_recipe_input_impossible :
    ¬ S2Mu3ExactGrade h2 hq 21
      (Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1) :=
  s2Mu3_chainNormBelow_tooth_not_exact h2 hq

end S2

end Uniformity.Density.Tower.C132rp10

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp10.s2Mu3_unique_admissible_linear
#print axioms Uniformity.Density.Tower.C132rp10.s2Mu3_X_add_one_irreducible
#print axioms Uniformity.Density.Tower.C132rp10.s2Mu3_gEight_monic
#print axioms Uniformity.Density.Tower.C132rp10.s2Mu3_gEight_natDegree
#print axioms Uniformity.Density.Tower.C132rp10.s2Mu3_recipe_correction_input_impossible
#print axioms Uniformity.Density.Tower.C132rp10.s2Mu3_gEight_recipe_input_impossible

end AxCheck
