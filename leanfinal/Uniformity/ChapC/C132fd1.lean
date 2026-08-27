/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp9

/-!
# Uniformity.ChapC.C132fd1 — the μ₃ B-1 supply is blocked

**[M3-FD1, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row
M3-FD1).

For `0 < d ≤ 1`, arithmetic reduces the requested B-1 family to `d = 1`.  A-C.18 and
`C97.s2Witness_values` then compute the below-current normalizer exactly as

`chainNormBelow 2 21 = 2⁴ Φ' = 16 Φ'`.

Its degree is exactly `2`, hence strictly below the current key degree `4`, and it is
nonzero.  The advertised exact-grade-`21` leg, however, is false: C132rp9 proves that every
polynomial of degree below `4` has even μ₃ grade, and in particular proves that this very
normalizer is not of exact grade `21`.

Accordingly this node lands the two successful supply families and a named
**BLOCKED-BECAUSE** certificate for the exact-grade family.  It does not invent a replacement
grade or alter the normalizer/value definitions.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132fd1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp9

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. The `d = 1` reduction -/

/-- The whole `0 < d ≤ f'` family at the landed numeral `f' = 1` has the single member
`d = 1`. -/
theorem s2Mu3_B1_d_eq_one {d : ℕ} (hd : 0 < d) (hd1 : d ≤ 1) : d = 1 := by
  omega

/-! ## 2. The lower normalizer is exactly `16 Φ'` -/

/-- A-C.18's below-current normalizer, with C.97's exponent solve evaluated to the displayed
numeral `16`. -/
theorem s2Mu3_chainNormBelow_two_twenty_one_eq_sixteen
    (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt) :
    I.chainNormBelow 2 21 =
      Polynomial.C (16 : O) * (s2DepthTwoKeyChain h2 hq).keyAt 1 := by
  rw [s2Mu3_chainNormBelow_two_twenty_one h2 hq I hkey]
  norm_num

/-- The proposed tooth has exact polynomial degree `2`. -/
theorem s2Mu3_chainNormBelow_tooth_natDegree :
    (Polynomial.C (16 : O) * (s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree = 2 := by
  rw [Polynomial.natDegree_C_mul]
  · exact ((s2DepthTwoKeyChain h2 hq).keyAt_degree 1 ⟨by omega, by omega⟩).trans
      (s2DepthTwo_Dcum_one h2 hq)
  · have h16 : (16 : O) = (2 : O) ^ 4 := by norm_num
    rw [h16]
    exact pow_ne_zero 4 h2.ne_zero

/-- The proposed tooth is nonzero. -/
theorem s2Mu3_chainNormBelow_tooth_ne_zero :
    Polynomial.C (16 : O) * (s2DepthTwoKeyChain h2 hq).keyAt 1 ≠ 0 := by
  apply mul_ne_zero
  · apply Polynomial.C_ne_zero.mpr
    have h16 : (16 : O) = (2 : O) ^ 4 := by norm_num
    rw [h16]
    exact pow_ne_zero 4 h2.ne_zero
  · exact ((s2DepthTwoKeyChain h2 hq).keyAt_monic 1 ⟨by omega, by omega⟩).ne_zero

/-! ## 3. The successful degree and nonzero B-1 families -/

/-- The degree half of B-1: after `d = 1`, the normalizer has degree `2`, strictly below
the current key's degree `4`. -/
theorem s2Mu3_B1_degree_supply
    (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt) :
    ∀ d, 0 < d → d ≤ 1 →
      (I.chainNormBelow 2 (d * 21)).natDegree < (I.keyAt 2).natDegree := by
  intro d hd hd1
  have hd' := s2Mu3_B1_d_eq_one hd hd1
  subst d
  rw [one_mul, s2Mu3_chainNormBelow_two_twenty_one_eq_sixteen h2 hq I hkey,
    s2Mu3_chainNormBelow_tooth_natDegree h2 hq, hkey]
  rw [((s2DepthTwoKeyChain h2 hq).keyAt_degree 2 ⟨by omega, by omega⟩).trans
    (s2DepthTwo_Dcum_two h2 hq)]
  omega

/-- The nonzero half of B-1, again reduced to its only index `d = 1`. -/
theorem s2Mu3_B1_nonzero_supply
    (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt) :
    ∀ d, 0 < d → d ≤ 1 → I.chainNormBelow 2 (d * 21) ≠ 0 := by
  intro d hd hd1
  have hd' := s2Mu3_B1_d_eq_one hd hd1
  subst d
  rw [one_mul, s2Mu3_chainNormBelow_two_twenty_one_eq_sixteen h2 hq I hkey]
  exact s2Mu3_chainNormBelow_tooth_ne_zero h2 hq

/-! ## 4. BLOCKED-BECAUSE: the exact-grade family is false -/

/-- **BLOCKED-BECAUSE certificate.** The requested exact-grade B-1 family cannot be supplied:
its sole `d = 1` member is exactly the normalizer refuted by C132rp9. -/
theorem s2Mu3_B1_exact_grade_supply_impossible
    (I : FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)
    (hkey : I.keyAt = (s2DepthTwoKeyChain h2 hq).keyAt) :
    ¬ (∀ d, 0 < d → d ≤ 1 →
      S2Mu3ExactGrade h2 hq (d * 21) (I.chainNormBelow 2 (d * 21))) := by
  intro hsupply
  apply s2Mu3_chainNormBelow_not_exact h2 hq I hkey
  simpa using hsupply 1 one_pos le_rfl

end S2

end Uniformity.Density.Tower.C132fd1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_B1_d_eq_one
#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_chainNormBelow_two_twenty_one_eq_sixteen
#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_chainNormBelow_tooth_natDegree
#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_chainNormBelow_tooth_ne_zero
#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_B1_degree_supply
#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_B1_nonzero_supply
#print axioms Uniformity.Density.Tower.C132fd1.s2Mu3_B1_exact_grade_supply_impossible

end AxCheck
