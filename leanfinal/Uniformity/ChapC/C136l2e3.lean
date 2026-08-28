/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e2
import Uniformity.ChapC.C134f13a
import Uniformity.ChapC.C136d0

/-!
# Uniformity.ChapC.C136l2e3 — closing the shared level-2 engine

This file is the L2E-09--11 landing unit from DWC §11.7.  It uses the corrected normalized
law from `C136l2e2`: `dv2Res` products have no root factor.  The cocycle belongs only to
the absolute full read.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136l2e3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e1 Uniformity.Density.Tower.C136l2e2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

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

private theorem dv2SideMin_congr (L : LevelDatum F H₀ hpin) {Ψ f g : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hfg : f = g)
    (hnef : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hneg : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ f u₂ ℓ₂ hnef = dv2SideMin L Ψ g u₂ ℓ₂ hneg := by
  subst g
  rfl

private theorem dv2SideDeg_congr (L : LevelDatum F H₀ hpin) {Ψ f g : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hfg : f = g)
    (hnef : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hneg : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) :
    dv2SideDeg L Ψ f u₂ ℓ₂ hnef = dv2SideDeg L Ψ g u₂ ℓ₂ hneg := by
  subst g
  rfl

/-! ## L2E-09 — coefficientwise residual product -/

/-- In-range coefficient of the signed level-2 residual polynomial. -/
theorem dv2ResPoly_coeff_of_le (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {t : ℕ}
    (ht : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne) :
    (dv2ResPoly L Ψ f u₂ ℓ₂ hne).coeff t =
      dv2Res L (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) := by
  rw [dv2ResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (Nat.lt_succ_of_le ht)]

/-- Beyond-range coefficient of the signed level-2 residual polynomial. -/
theorem dv2ResPoly_coeff_of_gt (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {t : ℕ}
    (ht : dv2SideDeg L Ψ f u₂ ℓ₂ hne < t) :
    (dv2ResPoly L Ψ f u₂ ℓ₂ hne).coeff t = 0 := by
  rw [dv2ResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg (by omega)]

/-- **L2E-09 coefficientwise assembly carrier.**  Once the displayed fixed-grade read
of the development convolution is available, the signed `dv2ResPoly` is multiplicative.
The premise is deliberately stated at the exact remaining interface: normalized
`dv2Res` is an own-height read, so it is not supplied by mere height survival. -/
theorem dv2ResPoly_mul_of_coeff_convolution (L : LevelDatum F H₀ hpin)
    {Ψ g z : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty)
    (hdeg : dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz =
      dv2SideDeg L Ψ g u₂ ℓ₂ hng + dv2SideDeg L Ψ z u₂ ℓ₂ hnz)
    (hconv : ∀ t, t ≤ dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz →
      dv2Res L (dev Ψ (g * z)
        (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz + t * ℓ₂)) =
      ∑ t₁ ∈ Finset.range (t + 1),
        (if t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng then
          dv2Res L (dev Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)) else 0) *
        (if t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz then
          dv2Res L (dev Ψ z
            (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂)) else 0)) :
    dv2ResPoly L Ψ (g * z) u₂ ℓ₂ hngz =
      dv2ResPoly L Ψ g u₂ ℓ₂ hng * dv2ResPoly L Ψ z u₂ ℓ₂ hnz := by
  classical
  apply Polynomial.ext
  intro t
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases ht : t ≤ dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz
  · rw [dv2ResPoly_coeff_of_le L hngz ht, hconv t ht]
    refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
    have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
    by_cases hg₁ : t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng
    · rw [dv2ResPoly_coeff_of_le L hng hg₁, if_pos hg₁]
      by_cases hz₁ : t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz
      · rw [dv2ResPoly_coeff_of_le L hnz hz₁, if_pos hz₁]
      · rw [dv2ResPoly_coeff_of_gt L hnz (by omega), if_neg hz₁]
    · rw [dv2ResPoly_coeff_of_gt L hng (by omega), if_neg hg₁]
      simp
  · rw [dv2ResPoly_coeff_of_gt L hngz (by omega)]
    symm
    refine Finset.sum_eq_zero fun t₁ ht₁ => ?_
    have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
    rcases Nat.lt_or_ge (dv2SideDeg L Ψ g u₂ ℓ₂ hng) t₁ with hg₁ | hg₁
    · rw [dv2ResPoly_coeff_of_gt L hng hg₁, zero_mul]
    · have hz₁ : dv2SideDeg L Ψ z u₂ ℓ₂ hnz < t - t₁ := by
        rw [hdeg] at ht
        omega
      rw [dv2ResPoly_coeff_of_gt L hnz hz₁, mul_zero]

/-! ## L2E-10 — complement specialization -/

/-- The signed complement scalar is nonzero.  This is the direct `AdjoinRoot.mk_eq_zero`
image of F1.2's residual nondivisibility clause. -/
theorem γg_ne_zero (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) : γg L f ≠ 0 := by
  classical
  let g := f /ₘ blockFactor L f
  have hg : g ≠ 0 := by
    dsimp [g]
    intro h0
    apply C134frt.quotient_dvSupp_ne_top L hπ hh hctx
    rw [h0]
    exact dvSupp_zero_eq_top F L.u L.hℓ
  have hne : (dvSideSet F g L.u L.ℓ).Nonempty := dvSideSet_nonempty F hg L.u L.hℓ
  have hon := dvOnSide_dvSideMin F g L.u L.ℓ hne
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 hon.2
  have hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M : ℕ∞) := hM.symm
  let hex : ∃ (hne' : (dvSideSet F g L.u L.ℓ).Nonempty) (M' : ℕ),
      dvHgt F g (dvSideMin F g L.u L.ℓ hne') = (M' : ℕ∞) := ⟨hne, M, hp⟩
  rw [γg, show f /ₘ blockFactor L f = g by rfl, dv2Res, dif_pos hex]
  intro hzero
  exact ((C134f12c.block_complement_notdvd L hπ hh hctx).2.1
    hex.choose hex.choose_spec.choose hex.choose_spec.choose_spec)
    (AdjoinRoot.mk_eq_zero.mp hzero)

/-- A factor not μ-divisible by the level-2 key has exactly one outer-side abscissa.
This is the strict form of `C134dv2g.dv2Supp_collapse_of_not_muDvd` needed by both the
complement residual specialization and the readable-side adapter. -/
theorem dv2SideSet_eq_singleton_zero_of_not_muDvd (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g) :
    dv2SideSet L Ψ g u₂ ℓ₂ = {0} := by
  classical
  have hg : g ≠ 0 := fun h0 => hnd (by rw [h0]; exact muDvd_zero L)
  have hSne : dvSupp F g L.u L.ℓ ≠ ⊤ := dvSupp_ne_top_of_ne_zero F L.u L.ℓ hg
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 hSne
  have hcollapse := dv2Supp_collapse_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd
  have hpin0 : dv2Pin L Ψ g 0 = dvSupp F g L.u L.ℓ := by
    show dvSupp F (dev Ψ g 0) L.u L.ℓ = dvSupp F g L.u L.ℓ
    rw [dev_zero_pin]
    exact dvSupp_modByKey_eq_of_not_muDvd L hkey hnd
  apply Finset.ext
  intro j
  simp only [Finset.mem_singleton]
  constructor
  · intro hj
    have hon : Dv2OnSide L Ψ g u₂ ℓ₂ j := dv2OnSide_of_mem_dv2SideSet L hj
    obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hon.2
    have hfloor := dvSupp_le_dev_add L hπ hh hkey hKΨ g j
    have hpinj : dvSupp F (dev Ψ g j) L.u L.ℓ = (Hj : ℕ∞) := hHj.symm
    rw [← hSg, hpinj] at hfloor
    have hfloorNat : Sg ≤ Hj + j * KΨ := by exact_mod_cast hfloor
    have hline : ℓ₂ * Sg = ℓ₂ * Hj + u₂ * j := by
      have h := hon.1
      rw [hcollapse, ← hSg, ← hHj] at h
      push_cast [nsmul_eq_mul] at h
      exact_mod_cast h
    by_contra hj0
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hle0 : u₂ * j ≤ ℓ₂ * (j * KΨ) := by
      have hmul : ℓ₂ * Sg ≤ ℓ₂ * (Hj + j * KΨ) :=
        Nat.mul_le_mul_left ℓ₂ hfloorNat
      rw [hline, Nat.mul_add] at hmul
      omega
    have hle : u₂ * j ≤ (ℓ₂ * KΨ) * j := by
      calc u₂ * j ≤ ℓ₂ * (j * KΨ) := hle0
        _ = (ℓ₂ * KΨ) * j := by ring
    have hlt : (ℓ₂ * KΨ) * j < u₂ * j := Nat.mul_lt_mul_of_pos_right hfence hjpos
    omega
  · rintro rfl
    refine mem_dv2SideSet_of_dv2OnSide L hkey.1 hkey.2.1.1 ?_
    constructor
    · rw [hcollapse, hpin0]
      simp
    · rw [hpin0]
      exact hSne

/-- The complement side starts and ends at zero. -/
theorem dv2SideMin_eq_zero_of_not_muDvd (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g)
    (hne : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ g u₂ ℓ₂ hne = 0 := by
  let hset := dv2SideSet_eq_singleton_zero_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd
  have hmem0 : 0 ∈ dv2SideSet L Ψ g u₂ ℓ₂ := by rw [hset]; simp
  exact Nat.eq_zero_of_le_zero (Finset.min'_le _ 0 hmem0)

/-- The complement contributes zero outer residual degree. -/
theorem dv2SideMax_eq_zero_of_not_muDvd (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g)
    (hne : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) :
    dv2SideMax L Ψ g u₂ ℓ₂ hne = 0 := by
  change (dv2SideSet L Ψ g u₂ ℓ₂).max' hne = 0
  let j := (dv2SideSet L Ψ g u₂ ℓ₂).max' hne
  have hj : j ∈ dv2SideSet L Ψ g u₂ ℓ₂ := Finset.max'_mem _ _
  rw [dv2SideSet_eq_singleton_zero_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd] at hj
  simpa [j] using hj

/-- The complement contributes zero outer residual degree. -/
theorem dv2SideDeg_eq_zero_of_not_muDvd (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hπ : Irreducible π) (hh : 0 < F.h)
    (hkey : IsMuKey L Ψ) {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞))
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hfence : ℓ₂ * KΨ < u₂)
    {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g)
    (hne : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty) :
    dv2SideDeg L Ψ g u₂ ℓ₂ hne = 0 := by
  have hmin := dv2SideMin_eq_zero_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd hne
  have hmax := dv2SideMax_eq_zero_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd hne
  rw [dv2SideDeg, hmin, hmax]
  simp

/-! ## L2E-11 — signed and depth-three adapters -/

/-- F1.5's exact radical conclusion follows formally from any nonzero scalar identity of
the F1.4 shape.  This isolates the only missing input to the signed F1.5 row. -/
theorem dv2ResPoly_radical_eq_of_scalar (L : LevelDatum F H₀ hpin)
    {f Ψ : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {c : AdjoinRoot L.r} (hc : c ≠ 0)
    (hscalar : dv2ResPoly L Ψ f u₂ ℓ₂ hne =
      Polynomial.C c * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne') :
    (dv2ResPoly L Ψ f u₂ ℓ₂ hne).natDegree =
        (dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPoly L Ψ f u₂ ℓ₂ hne ↔
        q ∣ dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne') := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  have hunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero).mpr hc)
  constructor
  · by_cases hQ : dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne' = 0
    · rw [hQ, mul_zero] at hscalar
      rw [hscalar, hQ]
    · rw [hscalar, Polynomial.natDegree_mul hunit.ne_zero hQ,
        Polynomial.natDegree_C, zero_add]
  · intro q _hqmonic _hqirr
    rw [hscalar, hunit.dvd_mul_left]

/-- ★ **F1.6 / C.64, signed conclusion byte-for-byte**, with the standing nondegenerate
frame binder `hh` inherited from the F-row suppliers.  The block split and the singleton
complement side reduce both equalities to L2E-07 additivity. -/
theorem mult₂_readable (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hh : 0 < F.h) {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hctx : BlockContext L f) (_hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ f u₂ ℓ₂ hne = dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' ∧
    dv2SideDeg L Ψ f u₂ ℓ₂ hne = dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne' := by
  let b := blockFactor L f
  let g := f /ₘ blockFactor L f
  have hkey : IsMuKey L Ψ := C134p1d.isMuKey_of_isTestKey L hπ hh hΨ
  have hKΨ : dvSupp F Ψ L.u L.ℓ = ((L.ℓ * L.seam : ℕ) : ℕ∞) :=
    C134f13a.dvSupp_testKey L hΨ
  have hcomp : ¬ MuDvd L Ψ g := by
    dsimp [g]
    exact C134p1.block_complement_not_muDvd L hπ hh hΨ hctx
  have hspec := C134cfs.blockFactor_spec L hπ hh hctx
  have hb : b ≠ 0 := by simpa [b] using hspec.1.1.ne_zero
  have hsplit : b * g = f := by
    dsimp [b, g]
    have h := Polynomial.modByMonic_add_div f (blockFactor L f)
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hspec.1.1).mpr hspec.2.1, zero_add] at h
  have hg : g ≠ 0 := fun h0 => hcomp (by rw [h0]; exact muDvd_zero L)
  have hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty :=
    dv2SideSet_nonempty_of_ne_zero L hkey.1 hkey.2.1.1 hℓ₂ hg
  have hnb : (dv2SideSet L Ψ b u₂ ℓ₂).Nonempty := by simpa [b] using hne'
  have hnbg : (dv2SideSet L Ψ (b * g) u₂ ℓ₂).Nonempty := by
    rw [hsplit]
    exact hne
  have hSurv : Dv2ResSurv L Ψ u₂ ℓ₂ :=
    dv2ResSurv_of_muKey L hπ hh hkey hKΨ hℓ₂ hseam
  have hming : dv2SideMin L Ψ g u₂ ℓ₂ hng = 0 :=
    dv2SideMin_eq_zero_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hseam hcomp hng
  have hmaxg : dv2SideMax L Ψ g u₂ ℓ₂ hng = 0 :=
    dv2SideMax_eq_zero_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hseam hcomp hng
  have hminmul := dv2SideMin_mul L hkey.1 hkey.2.1.1 hℓ₂ hSurv hb hg hnb hng hnbg
  have hmaxmul := dv2SideMax_mul L hkey.1 hkey.2.1.1 hℓ₂ hSurv hb hg hnb hng hnbg
  have hdegmul : dv2SideDeg L Ψ (b * g) u₂ ℓ₂ hnbg = dv2SideDeg L Ψ b u₂ ℓ₂ hnb := by
    rw [dv2SideDeg, dv2SideDeg, hminmul, hmaxmul, hming, hmaxg]
    simp
  constructor
  · calc
      dv2SideMin L Ψ f u₂ ℓ₂ hne
          = dv2SideMin L Ψ (b * g) u₂ ℓ₂ hnbg :=
              dv2SideMin_congr L hsplit.symm hne hnbg
      _ = dv2SideMin L Ψ b u₂ ℓ₂ hnb + dv2SideMin L Ψ g u₂ ℓ₂ hng := hminmul
      _ = dv2SideMin L Ψ b u₂ ℓ₂ hnb := by rw [hming, add_zero]
      _ = dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' := by simp [b]
  · calc
      dv2SideDeg L Ψ f u₂ ℓ₂ hne
          = dv2SideDeg L Ψ (b * g) u₂ ℓ₂ hnbg :=
              dv2SideDeg_congr L hsplit.symm hne hnbg
      _ = dv2SideDeg L Ψ b u₂ ℓ₂ hnb := hdegmul
      _ = dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne' := by simp [b]

/-!
## Exact open goals after the corrected-shape audit

L2E-09 reduces, after the landed endpoint/degree laws, to the `hconv` premise of
`dv2ResPoly_mul_of_coeff_convolution`.  Expanding one coefficient with
`C132rp5.dev_mul_conv_split_monic` leaves the fixed-grade read goal

```lean
dv2Res L (mainDiagonal + carryDiagonal) =
  ∑ t₁ ∈ Finset.range (t + 1), dv2Res L factorDigit₁ * dv2Res L factorDigit₂
```

at the product line's prescribed grade.  `C136l2e1.dv2Res_mul` proves multiplication of
individual nonzero factors, but the total `dv2Res` normalizes at the input's own height;
it supplies no equal-grade sum law when the main-diagonal initial forms cancel.

For F1.4/C.39, the corrected normalized complement product has scalar `γg L f`.  The
signed byte-for-byte target adds

```lean
(AdjoinRoot.root L.r) ^
  L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne') (complementConst L f)
```

and cancellation against the nonzero scalar (`γg_ne_zero`) and nonzero block residual
leaves exactly

```lean
(AdjoinRoot.root L.r) ^
  L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne') (complementConst L f) = 1
```

There is no landed supplier for this identity; adding the factor to normalized `dv2Res`
would contradict the corrected L2E1/L2E2 shape lock.  Consequently F1.5's exact signed
row stops only at its F1.4 scalar premise, isolated by `dv2ResPoly_radical_eq_of_scalar`.

D3-03 is not an instance of the present `LevelDatum` engine: `C136d0.Dv3ResSurv` has
inner height `dv2Supp L Ψ₂ u₂ ℓ₂`, with arbitrary `(Ψ₂,u₂,ℓ₂)`, whereas every theorem
above reads the bundled `dvSupp F _ L.u L.ℓ`.  No depth-three `LevelDatum` adapter is
landed.  D3-10 therefore also remains at that missing adapter plus the fixed-grade
`hconv` goal above.
-/

end Uniformity.Density.Tower.C136l2e3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136l2e3.dv2ResPoly_coeff_of_le
#print axioms Uniformity.Density.Tower.C136l2e3.dv2ResPoly_coeff_of_gt
#print axioms Uniformity.Density.Tower.C136l2e3.dv2ResPoly_mul_of_coeff_convolution
#print axioms Uniformity.Density.Tower.C136l2e3.γg_ne_zero
#print axioms Uniformity.Density.Tower.C136l2e3.dv2SideSet_eq_singleton_zero_of_not_muDvd
#print axioms Uniformity.Density.Tower.C136l2e3.dv2SideMin_eq_zero_of_not_muDvd
#print axioms Uniformity.Density.Tower.C136l2e3.dv2SideMax_eq_zero_of_not_muDvd
#print axioms Uniformity.Density.Tower.C136l2e3.dv2SideDeg_eq_zero_of_not_muDvd
#print axioms Uniformity.Density.Tower.C136l2e3.dv2ResPoly_radical_eq_of_scalar
#print axioms Uniformity.Density.Tower.C136l2e3.mult₂_readable

end AxCheck
