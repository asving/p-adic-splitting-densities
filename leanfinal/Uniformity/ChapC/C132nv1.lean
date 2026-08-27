/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130s2
import Uniformity.ChapC.C132nv0

/-!
# Uniformity.ChapC.C132nv1 — the μ₃ value table `s2Hgt₃` (μ₃ campaign, node M3-NV1)

**[M3-NV1, 2026-08-26]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV1):
the first NUMERAL instantiation of the M3-NV0 `dv2Supp` bank, at the S2 depth-two occurrence.
`s2Hgt₃ g := toZ (dv2Supp L Φ₂ g 21 2)`, where `L := (s2Tower h2 hq).levelDatum h2` is the
SAME level datum `s2Hgt₂` reads (`C130s6.s2Hgt₂_eq_dv2Hgt`), and `Φ₂ := s2DepthTwoKeyAt h2 hq 2`
is CC-2's promoted level-2 key (`C130s2.lean:181-182`, `= composedKey (s2Tower h2 hq)`).

Read as a table: `s2Hgt₃` is the μ₃ analogue of `s2Hgt₂` (`C130s6`'s level-2 VALUE table),
one further level up the tower — its inner `dv2Hgt`-reads are literally `s2Hgt₂`'s reads (the
anti-drift fact `s2Hgt₂_eq_dv2Hgt` is what lets the `Φ₂`-value tooth below cite `s2Hgt₂_one`
rather than re-deriving the frame-level computation).

## Pins landed here

Zero (`s2Hgt₃_zero`), finiteness off zero (`s2Hgt₃_ne_top`), the ultrametric
inequality/equality (`s2Hgt₃_add_ge`/`s2Hgt₃_add_eq`), the tower-height tooth
`s2Hgt₃ Φ₂ = 21 = u₃` (`s2Hgt₃_Φ₂`, the μ₃ analogue of `C130s6.s2Hgt₂_key`), and the
field-shape anti-drift pin `s2Hgt₃_eq_dv2Supp` (the table IS `dv2Supp` at the S2 numerals —
nothing fresh invented, mirroring `s2Hgt₂_eq_dvSupp`).

**DEPENDS.** C132nv0 (the generic `dv2Supp` bank) · C130s2 (`s2Tower`, `s2Frame`,
`s2DepthTwoKeyAt`, `s2DepthTwoKeyAt_two`, `s2Bridge_Dcum`, `s2DepthTwo_Dcum_two`) · C130s6
(`toZ` and its laws, `s2Hgt₂`, `s2Hgt₂_one`, `s2Hgt₂_eq_dv2Hgt`) · C.47 (`composedKey_monic`)
· C.53b (`composedKey_natDegree_D₂`) · C.44 (`TowerDatum.levelDatum`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C132nv0
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. Plumbing: `Φ₂`'s monicity and degree, read off the promoted CC-2 chain -/

/-- `Φ₂ := s2DepthTwoKeyAt h2 hq 2` is monic — the frame-key monicity for the promoted
CC-2 level-2 slot, read through `s2DepthTwoKeyAt_two` and C.47's `composedKey_monic`. -/
theorem s2Φ₂_monic : (s2DepthTwoKeyAt h2 hq 2).Monic := by
  rw [s2DepthTwoKeyAt_two h2 hq]
  exact composedKey_monic (s2Tower h2 hq)

/-- `deg Φ₂ = 4`, read through C.53b's `composedKey_natDegree_D₂` and CC-2's own bridge
`s2Bridge_Dcum`/`s2DepthTwo_Dcum_two` — no new degree fact, only the promoted chain's. -/
theorem s2Φ₂_natDegree : (s2DepthTwoKeyAt h2 hq 2).natDegree = 4 := by
  rw [s2DepthTwoKeyAt_two h2 hq, composedKey_natDegree_D₂ (s2Tower h2 hq) h2,
    ← s2Bridge_Dcum h2 hq, s2DepthTwo_Dcum_two h2 hq]

/-! ## 2. The VALUE table `s2Hgt₃` and its shape/zero/finiteness/add laws -/

/-- **the S2 μ₃ VALUE table**: the corpus's `e₃`-cleared μ₃ support at the S2 side
`(u₃, ℓ₃) = (21, 2)`, developed in the promoted level-2 key `Φ₂`, at the level datum
`s2Hgt₂` itself reads. -/
noncomputable def s2Hgt₃ (g : Polynomial O) : WithTop ℤ :=
  toZ (dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2)

/-- Anti-drift pin (the "field shape" tooth): the table IS `dv2Supp` at the S2 numerals —
nothing fresh, mirroring `C130s6.s2Hgt₂_eq_dvSupp` one level up. -/
theorem s2Hgt₃_eq_dv2Supp (g : Polynomial O) :
    s2Hgt₃ h2 hq g
      = toZ (dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2) := rfl

/-- the `hgt_zero` field at μ₃ (mirror of `s2Hgt₂_zero`). -/
theorem s2Hgt₃_zero : s2Hgt₃ h2 hq (0 : Polynomial O) = ⊤ := by
  rw [s2Hgt₃, dv2Supp_zero_eq_top _ _ _ (by norm_num), toZ_top]

/-- every nonzero polynomial has finite μ₃ height (mirror of `s2Hgt₂_ne_top`). -/
theorem s2Hgt₃_ne_top {g : Polynomial O} (hg : g ≠ 0) : s2Hgt₃ h2 hq g ≠ ⊤ := by
  rw [s2Hgt₃, ne_eq, toZ_eq_top_iff]
  exact dv2Supp_ne_top_of_ne_zero _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) _ _ hg

/-- the μ₃ ultrametric inequality (mirror of `s2Hgt₂_add_ge`). -/
theorem s2Hgt₃_add_ge (g g' : Polynomial O) :
    min (s2Hgt₃ h2 hq g) (s2Hgt₃ h2 hq g') ≤ s2Hgt₃ h2 hq (g + g') := by
  rw [s2Hgt₃, s2Hgt₃, s2Hgt₃, ← toZ_min]
  exact toZ_le_toZ_iff.mpr (min_dv2Supp_le_dv2Supp_add _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) g g')

/-- the μ₃ ultrametric equality off ties (mirror of `s2Hgt₂_add_eq`). -/
theorem s2Hgt₃_add_eq (g g' : Polynomial O) (hne : s2Hgt₃ h2 hq g ≠ s2Hgt₃ h2 hq g') :
    s2Hgt₃ h2 hq (g + g') = min (s2Hgt₃ h2 hq g) (s2Hgt₃ h2 hq g') := by
  have hne' : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
      ≠ dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g' 21 2 :=
    fun heq => hne (congrArg toZ heq)
  rw [s2Hgt₃, s2Hgt₃, s2Hgt₃, ← toZ_min]
  exact congrArg toZ (dv2Supp_add_eq _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) hne')

/-! ## 3. The tower-height tooth `s2Hgt₃ Φ₂ = 21 = u₃`

Mirror of `C130s6.s2Hgt₂_key`: `Φ₂`'s own development in itself has `dev = 0` at `j = 0`,
`dev = 1` at `j = 1`, and `dev = 0` past `j = 1` (since `Φ₂` is monic of positive degree, the
`j = 1` remainder `1 %ₘ Φ₂ = 1` and every later quotient is `1 /ₘ Φ₂ = 0`). -/

private theorem Φ₂_one_mod : (1 : Polynomial O) %ₘ (s2DepthTwoKeyAt h2 hq 2) = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, s2Φ₂_natDegree h2 hq]; norm_num))

private theorem Φ₂_one_div : (1 : Polynomial O) /ₘ (s2DepthTwoKeyAt h2 hq 2) = 0 :=
  (Polynomial.divByMonic_eq_zero_iff (s2Φ₂_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, s2Φ₂_natDegree h2 hq]; norm_num))

private theorem Φ₂_dev0 :
    dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2) 0 = 0 := by
  have h := dev_mul_pow_of_lt (s2Φ₂_monic h2 hq) 1 1 0 Nat.one_pos
  rwa [one_mul, pow_one] at h

private theorem Φ₂_dev1 :
    dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2) 1 = 1 := by
  have h := dev_mul_pow (s2Φ₂_monic h2 hq) 1 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul, pow_one] at h
  rw [h]
  exact Φ₂_one_mod h2 hq

private theorem Φ₂_dev2 :
    dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2) 2 = 0 := by
  have h := dev_mul_pow (s2Φ₂_monic h2 hq) 1 (1 : Polynomial O) 1
  rw [show (1 : ℕ) + 1 = 2 from rfl, one_mul, pow_one] at h
  rw [h]
  show ((1 : Polynomial O) /ₘ (s2DepthTwoKeyAt h2 hq 2)) %ₘ (s2DepthTwoKeyAt h2 hq 2) = 0
  rw [Φ₂_one_div h2 hq, Polynomial.zero_modByMonic]

private theorem Φ₂_dev3 :
    dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2) 3 = 0 := by
  have h := dev_mul_pow (s2Φ₂_monic h2 hq) 1 (1 : Polynomial O) 2
  rw [show (1 : ℕ) + 2 = 3 from rfl, one_mul, pow_one] at h
  rw [h]
  show dev (s2DepthTwoKeyAt h2 hq 2) ((1 : Polynomial O) /ₘ (s2DepthTwoKeyAt h2 hq 2)) 1 = 0
  rw [Φ₂_one_div h2 hq]
  exact dev_of_zero _ 1

private theorem Φ₂_dev4 :
    dev (s2DepthTwoKeyAt h2 hq 2) (s2DepthTwoKeyAt h2 hq 2) 4 = 0 := by
  have h := dev_mul_pow (s2Φ₂_monic h2 hq) 1 (1 : Polynomial O) 3
  rw [show (1 : ℕ) + 3 = 4 from rfl, one_mul, pow_one] at h
  rw [h]
  show dev (s2DepthTwoKeyAt h2 hq 2) ((1 : Polynomial O) /ₘ (s2DepthTwoKeyAt h2 hq 2)) 2 = 0
  rw [Φ₂_one_div h2 hq]
  exact dev_of_zero _ 2

/-- `Φ₂`'s own μ₂ read at `1` is `0` — literally `s2Hgt₂`'s `h(1) = 0` tooth, transported
across the `s2Hgt₂_eq_dv2Hgt` anti-drift pin (no fresh frame-level computation). -/
private theorem Φ₂_dv2Hgt_one :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [← s2Hgt₂_eq_dv2Hgt h2 hq, s2Hgt₂_one h2 hq]
  exact (C130s6.toZ_coe 0).symm

/-- `Φ₂`'s own μ₂ read at `0` is `⊤` (mirror of `dvSupp_zero_eq_top` at the level datum's
underlying `dvSupp`). -/
private theorem Φ₂_dv2Hgt_zero :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2) (0 : Polynomial O) = (⊤ : ℕ∞) := by
  rw [dv2Hgt]
  exact dvSupp_zero_eq_top _ _ ((s2Tower h2 hq).levelDatum h2).hℓ

/-- ★ **the tower-height tooth**: `s2Hgt₃ Φ₂ = 21 = u₃`, the μ₃ analogue of
`C130s6.s2Hgt₂_key`'s `h(Φ′) = 5 = u₂`. -/
theorem s2Hgt₃_Φ₂ : s2Hgt₃ h2 hq (s2DepthTwoKeyAt h2 hq 2) = ((21 : ℤ) : WithTop ℤ) := by
  have hval : dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 = ((21 : ℕ) : ℕ∞) := by
    rw [dv2Supp, s2Φ₂_natDegree h2 hq, show Finset.range (4 + 1) = {0, 1, 2, 3, 4} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_insert,
      Finset.inf_singleton, dv2Pin, dv2Pin, dv2Pin, dv2Pin, dv2Pin, Φ₂_dev0 h2 hq,
      Φ₂_dev1 h2 hq, Φ₂_dev2 h2 hq, Φ₂_dev3 h2 hq, Φ₂_dev4 h2 hq, Φ₂_dv2Hgt_one h2 hq,
      Φ₂_dv2Hgt_zero h2 hq]
    simp
  rw [s2Hgt₃, hval, toZ_coe]
  norm_num

end Uniformity.Density.Tower.C132nv1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv1.s2Φ₂_monic
#print axioms Uniformity.Density.Tower.C132nv1.s2Φ₂_natDegree
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃_eq_dv2Supp
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃_zero
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃_ne_top
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃_add_ge
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃_add_eq
#print axioms Uniformity.Density.Tower.C132nv1.s2Hgt₃_Φ₂

end AxCheck
