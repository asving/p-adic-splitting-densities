/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e0

/-!
# Uniformity.ChapC.C136l2e1 — L2E-03--05: survival, root law, pair pricing

This file continues the frame-generic level-2 multiplicative engine of DWC §11.7.

* L2E-03 upgrades finite height survival for reduced products of `Ψ`-digits to a
  nonvanishing coherent `dv2Res` read.
* L2E-04 audits the proposed slot-carry/root product law against the landed normalized
  residual product, lands the clean unreduced law, and isolates the nontrivial-root
  obstruction in the proposed shape.
* L2E-05 ports the pair-line pricing and endpoint uniqueness interface to `dv2Pin`.

No declaration is specialized to the S2 datum or contains an S2 numeral.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136l2e1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## L2E-03 — digit survival and nonzero coherent read -/

/-- A finite exact level value below the level recipe degree has a nonzero coherent
`dv2Res` read.  The degree fence rules out divisibility of its level residual by `L.r`;
`AdjoinRoot.mk_eq_zero` then gives the desired nonvanishing. -/
private theorem dv2Res_ne_zero_of_natDegree_lt_keyDeg (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {A : Polynomial O} {k : ℕ}
    (hdeg : A.natDegree < L.keyDeg₂) (hA : dv2Hgt L A = (k : ℕ∞)) :
    dv2Res L A ≠ 0 := by
  classical
  have hne : (dvSideSet F A L.u L.ℓ).Nonempty :=
    C131y.dvSideSet_nonempty_of_dvSupp_eq_coe F A L.u L.hℓ hA
  have hon := dvOnSide_dvSideMin F A L.u L.ℓ hne
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 hon.2
  have hp : dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M : ℕ∞) := hM.symm
  let hex : ∃ (hne' : (dvSideSet F A L.u L.ℓ).Nonempty) (M' : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne') = (M' : ℕ∞) := ⟨hne, M, hp⟩
  rw [dv2Res, dif_pos hex]
  intro hzero
  exact (C134p1d.not_residual_dvd_of_natDegree_lt L hπ hdeg
    hex.choose hex.choose_spec.choose hex.choose_spec.choose_spec)
    (AdjoinRoot.mk_eq_zero.mp hzero)

/-- The residue-strengthened form of `Dv2ResSurv`.  Besides the two landed height/slot
prices, the reduced slot-zero product of any two finite `Ψ`-digits has nonzero coherent
read. -/
def Dv2ResSurvRead (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O)
    (u₂ ℓ₂ : ℕ) : Prop :=
  Dv2ResSurv L Ψ u₂ ℓ₂ ∧
    ∀ ⦃A B : Polynomial O⦄ ⦃Ha Hb : ℕ⦄,
      A.natDegree < Ψ.natDegree → B.natDegree < Ψ.natDegree →
      dv2Hgt L A = (Ha : ℕ∞) → dv2Hgt L B = (Hb : ℕ∞) →
      dv2Res L (dev Ψ (A * B) 0) ≠ 0

/-- ★ **L2E-03 — digit survival with a nonzero residue read.**  For a level test key,
the generic μ-key survival package upgrades to `Dv2ResSurvRead`: the exact reduced-product
height is finite, while its degree is below the test-key recipe degree, so the level
residual cannot be killed by `L.r`. -/
theorem dv2ResSurvRead_of_testKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ}
    (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂) :
    Dv2ResSurvRead L Ψ u₂ ℓ₂ := by
  have hsurv := dv2ResSurv_of_muKey L hπ hh hkey hKΨ hℓ₂ hfence
  refine ⟨hsurv, ?_⟩
  intro A B Ha Hb hA hB hHa hHb
  have hval : dv2Hgt L (dev Ψ (A * B) 0) = ((Ha + Hb : ℕ) : ℕ∞) :=
    (hsurv hA hB hHa hHb).1
  have hdegΨ : (dev Ψ (A * B) 0).natDegree < Ψ.natDegree :=
    natDegree_dev_lt hkey.1 hkey.2.1.1 (A * B) 0
  have hdeg : (dev Ψ (A * B) 0).natDegree < L.keyDeg₂ := by
    rwa [← hΨ.2.1]
  exact dv2Res_ne_zero_of_natDegree_lt_keyDeg L hπ hdeg hval

/-! ## L2E-04 — the slot-carry/twist root law -/

/-- Nonzero polynomials supply the dependent pin package used by the total `dv2Res`
definition. -/
private theorem exists_dv2Res_pin (L : LevelDatum F H₀ hpin) {A : Polynomial O}
    (hA : A ≠ 0) :
    ∃ (hne : (dvSideSet F A L.u L.ℓ).Nonempty) (M : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne) = (M : ℕ∞) := by
  have hne : (dvSideSet F A L.u L.ℓ).Nonempty := dvSideSet_nonempty F hA L.u L.hℓ
  have hon := dvOnSide_dvSideMin F A L.u L.ℓ hne
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 hon.2
  exact ⟨hne, M, hM.symm⟩

/-- The coherent level read is exactly multiplicative on unreduced nonzero products.
This is the `AdjoinRoot.mk` image of the landed level-1 mixed residual law; its inverse
twist already cancels the shift carry. -/
theorem dv2Res_mul (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {A B : Polynomial O} (hA : A ≠ 0) (hB : B ≠ 0) :
    dv2Res L (A * B) = dv2Res L A * dv2Res L B := by
  classical
  let hABpin := exists_dv2Res_pin L (mul_ne_zero hA hB)
  let hApin := exists_dv2Res_pin L hA
  let hBpin := exists_dv2Res_pin L hB
  rw [dv2Res, dif_pos hABpin, dv2Res, dif_pos hApin, dv2Res, dif_pos hBpin, ← map_mul]
  congr 1
  exact C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop
    (by rw [← Nat.mul_assoc]; exact L.hκ) hA hB
    hApin.choose hBpin.choose hABpin.choose
    hApin.choose_spec.choose_spec hBpin.choose_spec.choose_spec hABpin.choose_spec.choose_spec

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField
    (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- Diagnostic forced by the L2E-00 twist shape: on any short product for which reduction
is inactive, the asserted root factor must be one.  This isolates the remaining L2E-04
obligation after the landed clean multiplicativity of `dv2Res`. -/
private theorem root_cocycle_eq_one_of_twist_shape
    (hLaw : Dv2TwistProductLawStatement O) (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ : Polynomial O}
    (hΨ : IsTestKey L Ψ) (hkey : IsMuKey L Ψ) {KΨ : ℕ}
    (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {a b : Polynomial O} (ha : a.natDegree < Ψ.natDegree)
    (hb : b.natDegree < Ψ.natDegree) (hab : (a * b).natDegree < Ψ.natDegree)
    {ka kb : ℕ} (hka : dv2Hgt L a = (ka : ℕ∞))
    (hkb : dv2Hgt L b = (kb : ℕ∞)) :
    AdjoinRoot.root L.r ^ L.cocycle ka kb = 1 := by
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, dv2Hgt, dvSupp_zero_eq_top F L.u L.hℓ] at hka
    exact ENat.coe_ne_top ka hka.symm
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, dv2Hgt, dvSupp_zero_eq_top F L.u L.hℓ] at hkb
    exact ENat.coe_ne_top kb hkb.symm
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hmod : dev Ψ (a * b) 0 = a * b := by
    rw [dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff hkey.1).mpr (by
      rw [Polynomial.degree_eq_natDegree hab0,
        Polynomial.degree_eq_natDegree hkey.1.ne_zero]
      exact_mod_cast hab)
  have hshape := hLaw π F hπ hh H₀ hpin L Ψ hkey KΨ hKΨ u₂ ℓ₂ hℓ₂ hfence
    a b ha hb ka kb hka hkb
  have hclean := dv2Res_mul L hπ hh ha0 hb0
  rw [hmod, hclean] at hshape
  have hda : a.natDegree < L.keyDeg₂ := by rwa [← hΨ.2.1]
  have hdb : b.natDegree < L.keyDeg₂ := by rwa [← hΨ.2.1]
  have hra : dv2Res L a ≠ 0 := dv2Res_ne_zero_of_natDegree_lt_keyDeg L hπ hda hka
  have hrb : dv2Res L b ≠ 0 := dv2Res_ne_zero_of_natDegree_lt_keyDeg L hπ hdb hkb
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  letI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  letI : Field (AdjoinRoot L.r) := AdjoinRoot.instField
  apply mul_right_cancel₀ (mul_ne_zero hra hrb)
  simpa using hshape.symm

/-! ## L2E-05 — pair convolution pricing -/

/-- Off the level-2 side, a slot prices at least one integral step above the finite
support line. -/
private theorem succ_dv2Supp_le_of_not_dv2OnSide (L : LevelDatum F H₀ hpin)
    {Ψ f : Polynomial O} (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {S : ℕ}
    (hS : dv2Supp L Ψ f u₂ ℓ₂ = (S : ℕ∞)) {j : ℕ}
    (hoff : ¬ Dv2OnSide L Ψ f u₂ ℓ₂ j) :
    ((S + 1 : ℕ) : ℕ∞) ≤ ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞) := by
  rcases eq_or_ne (dv2Pin L Ψ f j) ⊤ with htop | hfin
  · rw [htop, C118a.smul_top_pos hℓ₂, top_add]
    exact le_top
  · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hfin
    have hlt : S < ℓ₂ * H + u₂ * j :=
      lt_dv2Weight L hΨm hΨd hℓ₂ hS hH.symm hoff
    rw [← hH, nsmul_eq_mul]
    exact_mod_cast hlt

/-- ★ **L2E-05a — pair-line lower price.**  Two arbitrary level-2 slots clear the sum
of their factors' finite support lines. -/
theorem dv2PairLine_le (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv2Supp L Ψ g u₂ ℓ₂ = (Sg : ℕ∞))
    (hSz : dv2Supp L Ψ z u₂ ℓ₂ = (Sz : ℕ∞)) (j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞)
      ≤ ℓ₂ • (dv2Pin L Ψ g j + dv2Pin L Ψ z i)
        + ((u₂ * (j + i) : ℕ) : ℕ∞) := by
  have hg := dv2Supp_le_term L hΨm hΨd g u₂ hℓ₂ j
  have hz := dv2Supp_le_term L hΨm hΨd z u₂ hℓ₂ i
  rw [hSg] at hg
  rw [hSz] at hz
  calc
    ((Sg + Sz : ℕ) : ℕ∞) = (Sg : ℕ∞) + (Sz : ℕ∞) := by push_cast; ring
    _ ≤ (ℓ₂ • dv2Pin L Ψ g j + (u₂ * j : ℕ∞))
          + (ℓ₂ • dv2Pin L Ψ z i + (u₂ * i : ℕ∞)) := add_le_add hg hz
    _ = ℓ₂ • (dv2Pin L Ψ g j + dv2Pin L Ψ z i)
          + ((u₂ * (j + i) : ℕ) : ℕ∞) := by
        rw [nsmul_add]
        push_cast
        ring

/-- ★ **L2E-05b — strict pair-line price.**  If a pair is not simultaneously on the
two factor sides, its price is at least one step above the sum line. -/
theorem dv2PairLine_lt (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv2Supp L Ψ g u₂ ℓ₂ = (Sg : ℕ∞))
    (hSz : dv2Supp L Ψ z u₂ ℓ₂ = (Sz : ℕ∞)) {j i : ℕ}
    (hbad : ¬ (Dv2OnSide L Ψ g u₂ ℓ₂ j ∧ Dv2OnSide L Ψ z u₂ ℓ₂ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞)
      ≤ ℓ₂ • (dv2Pin L Ψ g j + dv2Pin L Ψ z i)
        + ((u₂ * (j + i) : ℕ) : ℕ∞) := by
  rcases not_and_or.mp hbad with hoff | hoff
  · have hg := succ_dv2Supp_le_of_not_dv2OnSide L hΨm hΨd hℓ₂ hSg hoff
    have hz := dv2Supp_le_term L hΨm hΨd z u₂ hℓ₂ i
    rw [hSz] at hz
    calc
      ((Sg + Sz + 1 : ℕ) : ℕ∞) = ((Sg + 1 : ℕ) : ℕ∞) + (Sz : ℕ∞) := by
        push_cast; ring
      _ ≤ (ℓ₂ • dv2Pin L Ψ g j + (u₂ * j : ℕ∞))
            + (ℓ₂ • dv2Pin L Ψ z i + (u₂ * i : ℕ∞)) := add_le_add hg hz
      _ = ℓ₂ • (dv2Pin L Ψ g j + dv2Pin L Ψ z i)
            + ((u₂ * (j + i) : ℕ) : ℕ∞) := by
          rw [nsmul_add]
          push_cast
          ring
  · have hg := dv2Supp_le_term L hΨm hΨd g u₂ hℓ₂ j
    have hz := succ_dv2Supp_le_of_not_dv2OnSide L hΨm hΨd hℓ₂ hSz hoff
    rw [hSg] at hg
    calc
      ((Sg + Sz + 1 : ℕ) : ℕ∞) = (Sg : ℕ∞) + ((Sz + 1 : ℕ) : ℕ∞) := by
        push_cast; ring
      _ ≤ (ℓ₂ • dv2Pin L Ψ g j + (u₂ * j : ℕ∞))
            + (ℓ₂ • dv2Pin L Ψ z i + (u₂ * i : ℕ∞)) := add_le_add hg hz
      _ = ℓ₂ • (dv2Pin L Ψ g j + dv2Pin L Ψ z i)
            + ((u₂ * (j + i) : ℕ) : ℕ∞) := by
          rw [nsmul_add]
          push_cast
          ring

/-- ★ **L2E-05c — endpoint uniqueness adapter.**  At the sum of the chosen left
endpoints, an on-side convolution pair is the endpoint pair itself. -/
theorem dv2Pair_endpoint_unique (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {g z : Polynomial O} {u₂ ℓ₂ j i : ℕ}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hsum : j + i = dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz)
    (hj : Dv2OnSide L Ψ g u₂ ℓ₂ j) (hi : Dv2OnSide L Ψ z u₂ ℓ₂ i) :
    j = dv2SideMin L Ψ g u₂ ℓ₂ hng ∧ i = dv2SideMin L Ψ z u₂ ℓ₂ hnz :=
  dv2OnSide_endpoint_unique L hΨm hΨd hng hnz hsum hj hi

end Uniformity.Density.Tower.C136l2e1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136l2e1.Dv2ResSurvRead
#print axioms Uniformity.Density.Tower.C136l2e1.dv2ResSurvRead_of_testKey
#print axioms Uniformity.Density.Tower.C136l2e1.dv2Res_mul
#print axioms Uniformity.Density.Tower.C136l2e1.dv2PairLine_le
#print axioms Uniformity.Density.Tower.C136l2e1.dv2PairLine_lt
#print axioms Uniformity.Density.Tower.C136l2e1.dv2Pair_endpoint_unique

end AxCheck
