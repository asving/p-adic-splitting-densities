/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp8
import Uniformity.ChapC.C130pk

/-!
# Uniformity.ChapC.C132rp9 — the literal μ₃ recipe premise is vacuous

**[M3-RP9, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6).

The requested literal `FGMNSourceLaws.normalized_recipe` occurrence has
`(e', f', u') = (2, 1, 21)`, hence asks that `khat 0` have exact μ₃ grade `21` and degree
strictly below `keyAt 2`, whose degree is `4`.  These two premises are incompatible.  Under
the degree fence the `Φ₂`-development has only its slot `0`; every exact outer grade is
therefore twice an inner natural grade and is even.  In particular it cannot be `21`.

Thus the literal recipe equality below is proved, but only by eliminating its impossible
premise.  This is a **BLOCKED-BECAUSE** result, not the non-vacuous numeral port advertised by
the campaign row.  The proposed tooth `16Φ'` also has degree below `4`, so the same theorem
proves that it does not have exact μ₃ grade `21`.  A-C.18 corrected the normalizer's index,
but cannot change this parity obstruction.

No corrected recipe statement is invented here.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp9

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp0
open Uniformity.Density.Tower.C132rp1 Uniformity.Density.Tower.C132rp2
open Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- **BLOCKED-BECAUSE certificate.** No polynomial of degree below the current key degree
`4` can have the odd exact μ₃ grade `21`. -/
theorem s2Mu3_recipe_grade_twenty_one_vacuous {g : Polynomial O}
    (hdeg : g.natDegree < 4) : ¬ S2Mu3ExactGrade h2 hq 21 g := by
  intro hg
  obtain ⟨s, hgate⟩ := exists_mu3SlotOnGrade_of_exact h2 hq hg
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (s2DepthTwoKeyAt h2 hq 2) g s = 0 :=
      dev_eq_zero_of_lt (s2Φ₂_monic h2 hq)
        (by rw [s2Φ₂_natDegree h2 hq]; norm_num) g s
        (by rw [s2Φ₂_natDegree h2 hq]; omega)
    have htop :
        dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g s = ⊤ := by
      rw [dv2Pin, hdev]
      exact Uniformity.Density.Tower.dv2Hgt_zero _
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  obtain ⟨m, -, hline⟩ := (s2Mu3SlotOnGrade_iff h2 hq).mp hgate
  rw [hs0] at hline
  omega

/-- The literal `(e',f',u') = (2,1,21)` normalized-recipe display.  It elaborates and is
logically true, but only because its required `khat 0` premise is impossible. -/
theorem s2Mu3_normalized_recipe (khat : ℕ → Polynomial O)
    (hkhat : ∀ t, t < 1 → S2Mu3ExactGrade h2 hq ((1 - t) * 21) (khat t))
    (hdeg : ∀ t, t < 1 → (khat t).natDegree <
      (s2DepthTwoKeyAt h2 hq 2 : Polynomial O).natDegree) :
    s2Mu3NormRes h2 hq
        ((s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (2 * 1) -
          ∑ t ∈ Finset.range 1,
            khat t * (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ (2 * t)) =
      Polynomial.X ^ 1 -
        ∑ t ∈ Finset.range 1,
          Polynomial.C ((s2Mu3GradedRes h2 hq ((1 - t) * 21) (khat t)).coeff 0) *
            Polynomial.X ^ t := by
  exfalso
  apply s2Mu3_recipe_grade_twenty_one_vacuous h2 hq
    (by rw [s2Φ₂_natDegree h2 hq] at hdeg; exact hdeg 0 (by omega))
  simpa using hkhat 0 (by omega)

/-- The proposed A-C.18 tooth has degree below `4`. -/
theorem s2Mu3_chainNormBelow_tooth_degree :
    (Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree < 4 := by
  rw [Polynomial.natDegree_C_mul (pow_ne_zero 4 h2.ne_zero)]
  have hk1 : ((s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree = 2 :=
    ((s2DepthTwoKeyChain h2 hq).keyAt_degree 1 ⟨by omega, by omega⟩).trans
      (s2DepthTwo_Dcum_one h2 hq)
  rw [hk1]
  omega

private theorem s2_towerNorm_one_twenty_one :
    (s2DepthTwo h2 hq).towerNorm 1 21 = (4, 0, ![1]) := by
  change (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).towerNorm 1 21 = (4, 0, ![1])
  rw [(s2Witness_values h2 hq 1 (s2Frame_pin h2 hq)).2.2.2.2.2.2]
  congr
  funext j
  fin_cases j
  rfl

/-- A-C.18's definition computes the corrected depth-two normalizer to the proposed tooth
whenever the calculus carries the landed key chain. -/
theorem s2Mu3_chainNormBelow_two_twenty_one
    (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt) :
    I.chainNormBelow 2 21 =
      Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1 := by
  rw [FGMNCalculus.chainNormBelow, FGMNCalculus.chainNorm,
    s2_towerNorm_one_twenty_one h2 hq, hkey]
  simp

/-- **Non-vacuity tooth refutation.** The corrected below-current normalizer polynomial
`2^4 Φ' = 16Φ'` cannot satisfy the literal exact-grade-`21` recipe premise. -/
theorem s2Mu3_chainNormBelow_tooth_not_exact :
    ¬ S2Mu3ExactGrade h2 hq 21
      (Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1) :=
  s2Mu3_recipe_grade_twenty_one_vacuous h2 hq
    (s2Mu3_chainNormBelow_tooth_degree h2 hq)

/-- The refutation restated on A-C.18's actual `chainNormBelow` definition. -/
theorem s2Mu3_chainNormBelow_not_exact
    (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt) :
    ¬ S2Mu3ExactGrade h2 hq 21 (I.chainNormBelow 2 21) := by
  rw [s2Mu3_chainNormBelow_two_twenty_one h2 hq I hkey]
  exact s2Mu3_chainNormBelow_tooth_not_exact h2 hq

end S2

end Uniformity.Density.Tower.C132rp9

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp9.s2Mu3_recipe_grade_twenty_one_vacuous
#print axioms Uniformity.Density.Tower.C132rp9.s2Mu3_normalized_recipe
#print axioms Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_tooth_degree
#print axioms Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_two_twenty_one
#print axioms Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_tooth_not_exact
#print axioms Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_not_exact

end AxCheck
