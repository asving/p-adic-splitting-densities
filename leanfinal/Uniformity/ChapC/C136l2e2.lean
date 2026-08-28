/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e1

/-!
# Uniformity.ChapC.C136l2e2 — corrected shapes and L2E-06--08

This file continues the frame-generic shared level-2 multiplicative engine of DWC §11.7.

* L2E-00 is corrected after the L2E1 audit: the coherent `dv2Res` product law has no
  root factor, while the carry shape is reserved for the absolute `dv2FullRead`.
* L2E-06 proves the generic nonzero `dv2Supp` product equality.
* L2E-07 proves additivity of both side endpoints and of `dv2SideDeg`.
* L2E-08 proves addition of the finite product-side-minimum pin heights and records the
  exact normalizer carry.

No declaration is specialized to the S2 datum or contains an S2 numeral.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136l2e2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0
open Uniformity.Density.Tower.C136l2e1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Corrected L2E-00 shapes (2026-08-28) -/

/-- ★ **Corrected L2E-00 normalized shape (2026-08-28).**  This declaration supersedes
`C136l2e0.Dv2SlotCarryLawStatement`.  The coherent read `dv2Res` already contains the
inverse shift normalizer, so its unreduced nonzero product law is clean: there is no root
factor and no separate carry premise. -/
def Dv2SlotCarryLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀), ∀ (L : LevelDatum F H₀ hpin),
  ∀ A B : Polynomial O, A ≠ 0 → B ≠ 0 →
    dv2Res L (A * B) = dv2Res L A * dv2Res L B

/-- ★ **Corrected L2E-00 absolute-read carry shape (2026-08-28).**  The old
`C136l2e0.Dv2TwistProductLawStatement`, which put a cocycle factor on normalized
`dv2Res`, is superseded.  A root-power carry belongs only to the absolute full read. -/
def Dv2FullReadCarryLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀), ∀ (L : LevelDatum F H₀ hpin),
  ∀ (A B : Polynomial O) (ka kb δ : ℕ),
    (ka : ℕ∞) ≤ dv2Hgt L A → (kb : ℕ∞) ≤ dv2Hgt L B →
    L.shift ka + L.shift kb = L.shift (ka + kb) + L.ℓ * δ →
    dv2FullRead L (ka + kb) (A * B)
      = AdjoinRoot.root L.r ^ δ * (dv2FullRead L ka A * dv2FullRead L kb B)

/-- The corrected normalized shape is inhabited by the landed residual foundation
`C136l2e1.dv2Res_mul`. -/
theorem dv2SlotCarryLaw : Dv2SlotCarryLawStatement O := by
  intro π F hπ hh H₀ hpin L A B hA hB
  exact dv2Res_mul L hπ hh hA hB

/-! ## L2E-06 — generic level-2 support multiplication -/

/-- ★ **L2E-06 — generic level-2 support product.**  The endpoint-only theorem of
`C132nv2` becomes an unconditional endpoint interface for nonzero factors: nonvanishing
supplies both side sets, and their chosen finite pin heights discharge its dependent
premises. -/
theorem dv2Supp_mul (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hg : g ≠ 0) (hz : z ≠ 0) :
    dv2Supp L Ψ (g * z) u₂ ℓ₂ = dv2Supp L Ψ g u₂ ℓ₂ + dv2Supp L Ψ z u₂ ℓ₂ := by
  have hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty :=
    dv2SideSet_nonempty_of_ne_zero L hΨm hΨd hℓ₂ hg
  have hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty :=
    dv2SideSet_nonempty_of_ne_zero L hΨm hΨd hℓ₂ hz
  obtain ⟨Hg, hHg⟩ := exists_dv2SideMin_height L g u₂ ℓ₂ hng
  obtain ⟨Hz, hHz⟩ := exists_dv2SideMin_height L z u₂ ℓ₂ hnz
  exact dv2Supp_mul_eq_add_of_endpoint_le L hΨm hΨd hℓ₂ hSurv hng hnz hHg hHz

/-! ## L2E-07 — exact level-2 side geometry -/

/-- The finite-sum ultrametric for `dv2Hgt`, in the weighted form used by the strict
no-pair convolution argument. -/
private theorem le_weight_dv2Hgt_sum (L : LevelDatum F H₀ hpin) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    {ι : Type*} (s : Finset ι) (G : ι → Polynomial O) {c d : ℕ∞}
    (hall : ∀ p ∈ s, c ≤ ℓ₂ • dv2Hgt L (G p) + d) :
    c ≤ ℓ₂ • dv2Hgt L (∑ p ∈ s, G p) + d := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, dv2Hgt_zero, C118a.smul_top_pos hℓ₂, top_add]
      exact le_top
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      have hmono : Monotone (fun x : ℕ∞ => ℓ₂ • x + d) :=
        fun _ _ hxy => add_le_add (nsmul_le_nsmul_right hxy ℓ₂) le_rfl
      calc
        c ≤ min (ℓ₂ • dv2Hgt L (G a) + d) (ℓ₂ • dv2Hgt L (∑ p ∈ t, G p) + d) :=
          le_min (hall a (Finset.mem_cons_self a t))
            (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))
        _ = ℓ₂ • min (dv2Hgt L (G a)) (dv2Hgt L (∑ p ∈ t, G p)) + d :=
          (hmono.map_min).symm
        _ ≤ ℓ₂ • dv2Hgt L (G a + ∑ p ∈ t, G p) + d :=
          hmono (min_dv2Hgt_le_dv2Hgt_add L _ _)

/-- The level-2 strict no-pair price.  If no pair of factor-side slots adds to `J`,
then the `J`-th product pin lies at least one integral step above the sum support line. -/
theorem dv2Line_succ_le_of_no_pair (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O} {Sg Sz J : ℕ}
    (hSg : dv2Supp L Ψ g u₂ ℓ₂ = (Sg : ℕ∞))
    (hSz : dv2Supp L Ψ z u₂ ℓ₂ = (Sz : ℕ∞))
    (hno : ∀ j i : ℕ, j + i = J →
      ¬ (Dv2OnSide L Ψ g u₂ ℓ₂ j ∧ Dv2OnSide L Ψ z u₂ ℓ₂ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ℓ₂ • dv2Pin L Ψ (g * z) J + (u₂ * J : ℕ∞) := by
  classical
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hzN : z.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i) := by
      rw [sum_dev_eq hΨm hΨd g hgN, sum_dev_eq hΨm hΨd z hzN]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]
      ring
  have hdev : dv2Pin L Ψ (g * z) J
      = dv2Hgt L (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) J) := by
    rw [dv2Pin]
    congr 1
    conv_lhs => rw [hrep]
    exact dev_finsetSum hΨm _ _ J
  rw [hdev]
  refine le_weight_dv2Hgt_sum L hℓ₂ _ _ fun p _ => ?_
  have hbad : ¬ (p.1 + p.2 = J ∧ Dv2OnSide L Ψ g u₂ ℓ₂ p.1 ∧
      Dv2OnSide L Ψ z u₂ ℓ₂ p.2) := by
    rintro ⟨hsum, hp, hq⟩
    exact hno p.1 p.2 hsum ⟨hp, hq⟩
  exact lt_line_dev2_term L hΨm hΨd hℓ₂ hSurv hSg hSz hbad

/-- ★ **L2E-07a — exact left endpoint.**  The existing endpoint construction gives
the forward inequality.  The reverse inequality is forced by the strict no-pair price:
a product-side point left of the sum cannot contain an on-side convolution pair. -/
theorem dv2SideMin_mul (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz
      = dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz := by
  obtain ⟨Hg, hHg⟩ := exists_dv2SideMin_height L g u₂ ℓ₂ hng
  obtain ⟨Hz, hHz⟩ := exists_dv2SideMin_height L z u₂ ℓ₂ hnz
  have hle : dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz
      ≤ dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz :=
    dv2SideMin_mul_le L hΨm hΨd hℓ₂ hSurv hng hnz hHg hHz hngz
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hSg : dv2Supp L Ψ g u₂ ℓ₂
      = ((ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHg (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng)
  have hSz : dv2Supp L Ψ z u₂ ℓ₂
      = ((ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHz (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz)
  have hW : dv2Supp L Ψ (g * z) u₂ ℓ₂
      = ((ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) : ℕ) : ℕ∞) := by
    rw [dv2Supp_mul L hΨm hΨd hℓ₂ hSurv hg hz, hSg, hSz]
    push_cast
    ring
  have hJon := dv2OnSide_dv2SideMin L (g * z) u₂ ℓ₂ hngz
  have hno : ∀ j i : ℕ, j + i = dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz →
      ¬ (Dv2OnSide L Ψ g u₂ ℓ₂ j ∧ Dv2OnSide L Ψ z u₂ ℓ₂ i) := by
    rintro j i hsum ⟨hj, hi⟩
    have hjle := dv2SideMin_le_of_dv2OnSide L hΨm hΨd hng hj
    have hile := dv2SideMin_le_of_dv2OnSide L hΨm hΨd hnz hi
    change dv2SideMin L Ψ g u₂ ℓ₂ hng ≤ j at hjle
    change dv2SideMin L Ψ z u₂ ℓ₂ hnz ≤ i at hile
    omega
  have hs := dv2Line_succ_le_of_no_pair L hΨm hΨd hℓ₂ hSurv hSg hSz hno
  rw [hJon.1] at hW
  change
    ((ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
        + (ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) + 1 : ℕ) : ℕ∞)
      ≤ ℓ₂ • dv2Pin L Ψ (g * z)
          (C132nv2.dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz)
        + ((u₂ * C132nv2.dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz : ℕ) : ℕ∞) at hs
  have hs' :
      ((ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) + 1 : ℕ) : ℕ∞)
        ≤ ((ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) : ℕ) : ℕ∞) :=
    hs.trans_eq hW
  have hnat :
      ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) + 1
        ≤ ℓ₂ * Hg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) := by
    exact_mod_cast hs'
  omega

/-- At a convolution-unique pair of on-side slots, the corresponding product pin has
height at most the sum of the two finite factor heights.  Strict pricing makes every
other convolution term at least one step higher. -/
private theorem dv2Pin_mul_pair_le (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O} {jg jz Hg Hz : ℕ}
    (hjg : Dv2OnSide L Ψ g u₂ ℓ₂ jg) (hjz : Dv2OnSide L Ψ z u₂ ℓ₂ jz)
    (hHg : dv2Pin L Ψ g jg = (Hg : ℕ∞)) (hHz : dv2Pin L Ψ z jz = (Hz : ℕ∞))
    (huniq : ∀ j i : ℕ, j + i = jg + jz →
      Dv2OnSide L Ψ g u₂ ℓ₂ j → Dv2OnSide L Ψ z u₂ ℓ₂ i → j = jg ∧ i = jz) :
    dv2Pin L Ψ (g * z) (jg + jz) ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  classical
  have hSg : dv2Supp L Ψ g u₂ ℓ₂ = ((ℓ₂ * Hg + u₂ * jg : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHg hjg
  have hSz : dv2Supp L Ψ z u₂ ℓ₂ = ((ℓ₂ * Hz + u₂ * jz : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHz hjz
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hzN : z.natDegree < N * Ψ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨd)
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ g j * Ψ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ z i * Ψ ^ i) := by
      rw [sum_dev_eq hΨm hΨd g hgN, sum_dev_eq hΨm hΨd z hzN]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]
      ring
  have hjgle : jg ≤ g.natDegree := by
    have hm := mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hjg
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
  have hjzle : jz ≤ z.natDegree := by
    have hm := mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hjz
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
  have hp0 : ((jg, jz) : ℕ × ℕ) ∈ Finset.range N ×ˢ Finset.range N := by
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩ <;> omega
  have hT0 : dev Ψ (dev Ψ g jg * dev Ψ z jz * Ψ ^ (jg + jz)) (jg + jz)
      = dev Ψ (dev Ψ g jg * dev Ψ z jz) 0 := by
    have h := dev_mul_pow hΨm (jg + jz) (dev Ψ g jg * dev Ψ z jz) 0
    rwa [Nat.add_zero] at h
  have hsplit : dev Ψ (g * z) (jg + jz)
      = dev Ψ (dev Ψ g jg * dev Ψ z jz) 0
        + ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
            dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz) := by
    have hdev : dev Ψ (g * z) (jg + jz)
        = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz) := by
      conv_lhs => rw [hrep]
      exact dev_finsetSum hΨm _ _ (jg + jz)
    rw [hdev, ← hT0]
    exact (Finset.add_sum_erase _ _ hp0).symm
  have hallR : ∀ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      (((ℓ₂ * (Hg + Hz) + u₂ * (jg + jz) + 1 : ℕ) : ℕ∞)
        ≤ ℓ₂ • dv2Hgt L
            (dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz))
          + (u₂ * (jg + jz) : ℕ∞)) := by
    intro p hp
    have hbad : ¬ (p.1 + p.2 = jg + jz ∧ Dv2OnSide L Ψ g u₂ ℓ₂ p.1 ∧
        Dv2OnSide L Ψ z u₂ ℓ₂ p.2) := by
      rintro ⟨hsum, h1, h2⟩
      obtain ⟨e1, e2⟩ := huniq p.1 p.2 hsum h1 h2
      exact (Finset.mem_erase.1 hp).1 (Prod.ext_iff.2 ⟨e1, e2⟩)
    refine le_trans (le_of_eq ?_) (lt_line_dev2_term L hΨm hΨd hℓ₂ hSurv hSg hSz hbad)
    push_cast
    ring
  have hRw := le_weight_dv2Hgt_sum L hℓ₂ _ _ hallR
  have hR : ((Hg + Hz : ℕ) : ℕ∞) + 1
      ≤ dv2Hgt L (∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
          dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz)) :=
    succ_le_of_weight_succ_le hRw
  have hAdeg : (dev Ψ g jg).natDegree < Ψ.natDegree := by
    rcases eq_or_ne (dev Ψ g jg) 0 with h0 | hne
    · rw [h0, natDegree_zero]
      exact hΨd
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨm hΨd g jg)
  have hBdeg : (dev Ψ z jz).natDegree < Ψ.natDegree := by
    rcases eq_or_ne (dev Ψ z jz) 0 with h0 | hne
    · rw [h0, natDegree_zero]
      exact hΨd
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨm hΨd z jz)
  have hval : dv2Hgt L (dev Ψ (dev Ψ g jg * dev Ψ z jz) 0)
      = ((Hg + Hz : ℕ) : ℕ∞) := (hSurv hAdeg hBdeg hHg hHz).1
  rw [dv2Pin, hsplit]
  set T := dev Ψ (dev Ψ g jg * dev Ψ z jz) 0 with hT
  set R := ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) (jg + jz) with hRdef
  rcases eq_or_ne (dv2Hgt L T) (dv2Hgt L R) with heq | hne
  · exfalso
    have hcontra : ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
      calc
        ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ dv2Hgt L R := hR
        _ = dv2Hgt L T := heq.symm
        _ = ((Hg + Hz : ℕ) : ℕ∞) := hval
    rw [show ((Hg + Hz : ℕ) : ℕ∞) + 1 = ((Hg + Hz + 1 : ℕ) : ℕ∞) by
      push_cast
      ring] at hcontra
    exact absurd (by exact_mod_cast hcontra : Hg + Hz + 1 ≤ Hg + Hz) (by omega)
  · rw [dv2Hgt_add_eq L hne, hval]
    exact min_le_left _ _

/-- A convolution-unique on-side pair has exactly the added finite height in the product
pin.  The lower inequality is the product support line; the upper inequality is the
strict-convolution calculation above. -/
theorem dv2Pin_mul_pair (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    {jg jz Hg Hz : ℕ}
    (hjg : Dv2OnSide L Ψ g u₂ ℓ₂ jg) (hjz : Dv2OnSide L Ψ z u₂ ℓ₂ jz)
    (hHg : dv2Pin L Ψ g jg = (Hg : ℕ∞)) (hHz : dv2Pin L Ψ z jz = (Hz : ℕ∞))
    (huniq : ∀ j i : ℕ, j + i = jg + jz →
      Dv2OnSide L Ψ g u₂ ℓ₂ j → Dv2OnSide L Ψ z u₂ ℓ₂ i → j = jg ∧ i = jz) :
    dv2Pin L Ψ (g * z) (jg + jz) = ((Hg + Hz : ℕ) : ℕ∞) := by
  have hup := dv2Pin_mul_pair_le L hΨm hΨd hℓ₂ hSurv hjg hjz hHg hHz huniq
  have hSg : dv2Supp L Ψ g u₂ ℓ₂ = ((ℓ₂ * Hg + u₂ * jg : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHg hjg
  have hSz : dv2Supp L Ψ z u₂ ℓ₂ = ((ℓ₂ * Hz + u₂ * jz : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHz hjz
  have hW : dv2Supp L Ψ (g * z) u₂ ℓ₂
      = ((ℓ₂ * (Hg + Hz) + u₂ * (jg + jz) : ℕ) : ℕ∞) := by
    rw [dv2Supp_mul L hΨm hΨd hℓ₂ hSurv hg hz, hSg, hSz]
    push_cast
    ring
  have hlow := dv2Supp_le_term L hΨm hΨd (g * z) u₂ hℓ₂ (jg + jz)
  rw [hW] at hlow
  have hpin_ne : dv2Pin L Ψ (g * z) (jg + jz) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hup
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hpin_ne
  have hcle : c ≤ Hg + Hz := by
    rw [← hc] at hup
    exact_mod_cast hup
  have hcge : Hg + Hz ≤ c := by
    rw [← hc, nsmul_eq_mul] at hlow
    have hnat : ℓ₂ * (Hg + Hz) + u₂ * (jg + jz) ≤ ℓ₂ * c + u₂ * (jg + jz) := by
      exact_mod_cast hlow
    exact Nat.le_of_mul_le_mul_left (by omega) hℓ₂
  rw [← hc]
  exact_mod_cast (show c = Hg + Hz by omega)

/-- ★ **L2E-07b — exact right endpoint.**  The sum of factor maxima survives by
the unique-pair calculation.  A hypothetical larger product-side point has no on-side
factor pair and is ruled out by the same strict no-pair contradiction as the minimum. -/
theorem dv2SideMax_mul (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty) :
    dv2SideMax L Ψ (g * z) u₂ ℓ₂ hngz
      = dv2SideMax L Ψ g u₂ ℓ₂ hng + dv2SideMax L Ψ z u₂ ℓ₂ hnz := by
  classical
  have hjgON : Dv2OnSide L Ψ g u₂ ℓ₂ (dv2SideMax L Ψ g u₂ ℓ₂ hng) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.max'_mem _ hng)
  have hjzON : Dv2OnSide L Ψ z u₂ ℓ₂ (dv2SideMax L Ψ z u₂ ℓ₂ hnz) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.max'_mem _ hnz)
  obtain ⟨Hg, hHg⟩ := ENat.ne_top_iff_exists.1 hjgON.2
  obtain ⟨Hz, hHz⟩ := ENat.ne_top_iff_exists.1 hjzON.2
  have huniq : ∀ j i : ℕ,
      j + i = dv2SideMax L Ψ g u₂ ℓ₂ hng + dv2SideMax L Ψ z u₂ ℓ₂ hnz →
      Dv2OnSide L Ψ g u₂ ℓ₂ j → Dv2OnSide L Ψ z u₂ ℓ₂ i →
      j = dv2SideMax L Ψ g u₂ ℓ₂ hng ∧ i = dv2SideMax L Ψ z u₂ ℓ₂ hnz := by
    intro j i hsum hj hi
    have hjle : j ≤ dv2SideMax L Ψ g u₂ ℓ₂ hng :=
      Finset.le_max' _ j (mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hj)
    have hile : i ≤ dv2SideMax L Ψ z u₂ ℓ₂ hnz :=
      Finset.le_max' _ i (mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hi)
    omega
  have hpair := dv2Pin_mul_pair L hΨm hΨd hℓ₂ hSurv hg hz hjgON hjzON hHg.symm hHz.symm huniq
  have hSg : dv2Supp L Ψ g u₂ ℓ₂
      = ((ℓ₂ * Hg + u₂ * dv2SideMax L Ψ g u₂ ℓ₂ hng : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHg.symm hjgON
  have hSz : dv2Supp L Ψ z u₂ ℓ₂
      = ((ℓ₂ * Hz + u₂ * dv2SideMax L Ψ z u₂ ℓ₂ hnz : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hHz.symm hjzON
  have hW : dv2Supp L Ψ (g * z) u₂ ℓ₂
      = ((ℓ₂ * Hg + u₂ * dv2SideMax L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMax L Ψ z u₂ ℓ₂ hnz) : ℕ) : ℕ∞) := by
    rw [dv2Supp_mul L hΨm hΨd hℓ₂ hSurv hg hz, hSg, hSz]
    push_cast
    ring
  have hONsum : Dv2OnSide L Ψ (g * z) u₂ ℓ₂
      (dv2SideMax L Ψ g u₂ ℓ₂ hng + dv2SideMax L Ψ z u₂ ℓ₂ hnz) := by
    refine ⟨?_, ?_⟩
    · rw [hW, hpair, nsmul_eq_mul]
      push_cast
      ring
    · rw [hpair]
      exact ENat.coe_ne_top _
  have hge : dv2SideMax L Ψ g u₂ ℓ₂ hng + dv2SideMax L Ψ z u₂ ℓ₂ hnz
      ≤ dv2SideMax L Ψ (g * z) u₂ ℓ₂ hngz :=
    Finset.le_max' _ _ (mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hONsum)
  refine le_antisymm ?_ hge
  by_contra hlt
  push Not at hlt
  have hJon : Dv2OnSide L Ψ (g * z) u₂ ℓ₂ (dv2SideMax L Ψ (g * z) u₂ ℓ₂ hngz) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.max'_mem _ hngz)
  have hno : ∀ j i : ℕ, j + i = dv2SideMax L Ψ (g * z) u₂ ℓ₂ hngz →
      ¬ (Dv2OnSide L Ψ g u₂ ℓ₂ j ∧ Dv2OnSide L Ψ z u₂ ℓ₂ i) := by
    rintro j i hsum ⟨hj, hi⟩
    have hjle : j ≤ dv2SideMax L Ψ g u₂ ℓ₂ hng :=
      Finset.le_max' _ j (mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hj)
    have hile : i ≤ dv2SideMax L Ψ z u₂ ℓ₂ hnz :=
      Finset.le_max' _ i (mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hi)
    omega
  have hs := dv2Line_succ_le_of_no_pair L hΨm hΨd hℓ₂ hSurv hSg hSz hno
  rw [hJon.1] at hW
  have hs' :
      ((ℓ₂ * Hg + u₂ * dv2SideMax L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMax L Ψ z u₂ ℓ₂ hnz) + 1 : ℕ) : ℕ∞)
        ≤ ((ℓ₂ * Hg + u₂ * dv2SideMax L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMax L Ψ z u₂ ℓ₂ hnz) : ℕ) : ℕ∞) :=
    hs.trans_eq hW
  have hnat :
      ℓ₂ * Hg + u₂ * dv2SideMax L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMax L Ψ z u₂ ℓ₂ hnz) + 1
        ≤ ℓ₂ * Hg + u₂ * dv2SideMax L Ψ g u₂ ℓ₂ hng
          + (ℓ₂ * Hz + u₂ * dv2SideMax L Ψ z u₂ ℓ₂ hnz) := by
    exact_mod_cast hs'
  omega

/-- Two level-2 on-side abscissae are congruent modulo the denominator of the outer
slope. -/
private theorem dv2OnSide_modEq (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hcop : Nat.Coprime u₂ ℓ₂) {f : Polynomial O} {j j' : ℕ}
    (hj : Dv2OnSide L Ψ f u₂ ℓ₂ j) (hj' : Dv2OnSide L Ψ f u₂ ℓ₂ j') :
    j ≡ j' [MOD ℓ₂] := by
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hj.2
  obtain ⟨H', hH'⟩ := ENat.ne_top_iff_exists.1 hj'.2
  have hweight : ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)
      = ℓ₂ • dv2Pin L Ψ f j' + (u₂ * j' : ℕ∞) := hj.1.symm.trans hj'.1
  rw [← hH, ← hH', weight_read, weight_read] at hweight
  have key : ℓ₂ * H + u₂ * j = ℓ₂ * H' + u₂ * j' := by
    exact_mod_cast hweight
  have keyZ : (ℓ₂ : ℤ) * (H : ℤ) + (u₂ : ℤ) * (j : ℤ)
      = (ℓ₂ : ℤ) * (H' : ℤ) + (u₂ : ℤ) * (j' : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key
  have hdvd : (ℓ₂ : ℤ) ∣ (u₂ : ℤ) * ((j' : ℤ) - (j : ℤ)) :=
    ⟨(H : ℤ) - (H' : ℤ), by linarith⟩
  have hcop' : IsCoprime (ℓ₂ : ℤ) (u₂ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact Nat.modEq_iff_dvd.mpr (hcop'.dvd_of_dvd_mul_left hdvd)

/-- The horizontal span of a level-2 side is exactly `ℓ₂` times its signed
`dv2SideDeg`; in particular the division in the definition is exact. -/
private theorem dv2SideSpan_eq (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    {f : Polynomial O} {u₂ ℓ₂ : ℕ} (hcop : Nat.Coprime u₂ ℓ₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) :
    dv2SideMax L Ψ f u₂ ℓ₂ hne - dv2SideMin L Ψ f u₂ ℓ₂ hne
      = ℓ₂ * dv2SideDeg L Ψ f u₂ ℓ₂ hne := by
  have hminON : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hne)
  have hmaxON : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMax L Ψ f u₂ ℓ₂ hne) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.max'_mem _ hne)
  have hle : dv2SideMin L Ψ f u₂ ℓ₂ hne ≤ dv2SideMax L Ψ f u₂ ℓ₂ hne :=
    Finset.min'_le _ _ (Finset.max'_mem _ hne)
  have hdvd : ℓ₂ ∣ dv2SideMax L Ψ f u₂ ℓ₂ hne - dv2SideMin L Ψ f u₂ ℓ₂ hne :=
    (Nat.modEq_iff_dvd' hle).mp (dv2OnSide_modEq L hcop hminON hmaxON)
  rw [dv2SideDeg, Nat.mul_div_cancel' hdvd]

/-- ★ **L2E-07c — exact side degree.**  Additivity of both endpoints and exact
`ℓ₂`-spacing of side abscissae imply additivity of `dv2SideDeg`. -/
theorem dv2SideDeg_mul (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hcop : Nat.Coprime u₂ ℓ₂) (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty) :
    dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz
      = dv2SideDeg L Ψ g u₂ ℓ₂ hng + dv2SideDeg L Ψ z u₂ ℓ₂ hnz := by
  have hmin := dv2SideMin_mul L hΨm hΨd hℓ₂ hSurv hg hz hng hnz hngz
  have hmax := dv2SideMax_mul L hΨm hΨd hℓ₂ hSurv hg hz hng hnz hngz
  have hlg := dv2SideSpan_eq L hcop hng
  have hlz := dv2SideSpan_eq L hcop hnz
  have hlgz := dv2SideSpan_eq L hcop hngz
  have hmm_g : dv2SideMin L Ψ g u₂ ℓ₂ hng ≤ dv2SideMax L Ψ g u₂ ℓ₂ hng :=
    Finset.min'_le _ _ (Finset.max'_mem _ hng)
  have hmm_z : dv2SideMin L Ψ z u₂ ℓ₂ hnz ≤ dv2SideMax L Ψ z u₂ ℓ₂ hnz :=
    Finset.min'_le _ _ (Finset.max'_mem _ hnz)
  have hkey : ℓ₂ * dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz
      = ℓ₂ * dv2SideDeg L Ψ g u₂ ℓ₂ hng + ℓ₂ * dv2SideDeg L Ψ z u₂ ℓ₂ hnz := by
    omega
  have hkey' : ℓ₂ * dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz
      = ℓ₂ * (dv2SideDeg L Ψ g u₂ ℓ₂ hng + dv2SideDeg L Ψ z u₂ ℓ₂ hnz) := by
    rw [hkey, Nat.mul_add]
  exact Nat.eq_of_mul_eq_mul_left hℓ₂ hkey'

/-! ## L2E-08 — finite pin-height addition at the product side minimum -/

/-- ★ **L2E-08a — pin-height addition.**  At the exact product side minimum, finite
factor pin heights add.  L2E-07 supplies the minimum identity and endpoint uniqueness
supplies the convolution-unique pair required by `dv2Pin_mul_pair`. -/
theorem dv2Pin_dv2SideMin_mul (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty) {Mg Mz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞)) :
    dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz)
      = ((Mg + Mz : ℕ) : ℕ∞) := by
  rw [dv2SideMin_mul L hΨm hΨd hℓ₂ hSurv hg hz hng hnz hngz]
  exact dv2Pin_mul_pair L hΨm hΨd hℓ₂ hSurv hg hz
    (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng)
    (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz) hpg hpz
    (fun j i hsum hj hi => dv2Pair_endpoint_unique L hΨm hΨd hng hnz hsum hj hi)

/-- ★ **L2E-08b — pin addition with exact normalizer carry accounting.**  The first
component is the finite product-pin equality.  The second records exactly the carry
measured by `L.cocycle`; it is bookkeeping for absolute full reads only and does not
insert a root factor into normalized `dv2Res`. -/
theorem dv2Pin_dv2SideMin_mul_with_carry (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty) {Mg Mz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞)) :
    dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz)
        = ((Mg + Mz : ℕ) : ℕ∞) ∧
      L.ℓ * L.cocycle Mg Mz = L.shift Mg + L.shift Mz - L.shift (Mg + Mz) := by
  exact ⟨dv2Pin_dv2SideMin_mul L hΨm hΨd hℓ₂ hSurv hg hz hng hnz hngz hpg hpz,
    (L.cocycle_mem Mg Mz).1⟩

end Uniformity.Density.Tower.C136l2e2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136l2e2.Dv2SlotCarryLawStatement
#print axioms Uniformity.Density.Tower.C136l2e2.Dv2FullReadCarryLawStatement
#print axioms Uniformity.Density.Tower.C136l2e2.dv2SlotCarryLaw
#print axioms Uniformity.Density.Tower.C136l2e2.dv2Supp_mul
#print axioms Uniformity.Density.Tower.C136l2e2.dv2Line_succ_le_of_no_pair
#print axioms Uniformity.Density.Tower.C136l2e2.dv2SideMin_mul
#print axioms Uniformity.Density.Tower.C136l2e2.dv2Pin_mul_pair
#print axioms Uniformity.Density.Tower.C136l2e2.dv2SideMax_mul
#print axioms Uniformity.Density.Tower.C136l2e2.dv2SideDeg_mul
#print axioms Uniformity.Density.Tower.C136l2e2.dv2Pin_dv2SideMin_mul
#print axioms Uniformity.Density.Tower.C136l2e2.dv2Pin_dv2SideMin_mul_with_carry

end AxCheck
