/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RungPacks
import Uniformity.ChapC.C47
import Uniformity.ChapC.C130a

/-!
# Uniformity.ChapI.I10SpineAdapter — UNIT D3AD (spine): `LevelDatum` per truncation from `DeepTower`

The D3-03 depth-adapter row of the `LevelSiteBank` remainder (verdict_SCS §"leftover",
verdict_RUNG §4): RUNG's per-rung carrier packs (`I10RungPacks`) live at a C.09
`LevelDatum`, while the site bank and the deep-witness campaign hand us a C.83
`DeepTower` (per truncation `core.T.trunc j hj`).  This file is the glue.

## The per-field correspondence (charge 1's scope adjudication)

A `LevelDatum F H₀ hpin` is EXACTLY the tower's stage-2 data, read through the LANDED
C.42/C.44 depth-2 bridge — no field is new and none is weakened:

| `LevelDatum` field | tower supply (truncation-invariant) |
|---|---|
| `u` | `T.u 2` |
| `ℓ` | `T.e 2` |
| `r` | `towerLabel` of the stage-2 `TowerDatum` whose `ψ₂ = (T.ψ 1).map T.base` (the η-twist enters via C.44; consumes `hπ`) |
| `hℓ` | `T.he 2` |
| `hcop` | `T.hcop 2` |
| `hκ` | `T.hfloor 1` + the frame pins `he1/hf1/hu1` (+ one `mul_assoc`) |
| `hrmonic/hrirr/hr0/hrdeg` | `T.hψ 1` transported along the GC-7 iterate witness `T.base`, then `towerLabel_spec` |

The route is `DeepTower --(stage-2 fields)--> TowerDatum --(C.44 levelDatum)--> LevelDatum`,
so the label twist, its four properties, and the canonical test key (`composedKey`, C.47)
are all consumed from landed nodes, never re-derived.

## Honest scope fence (the rungs-≥ 3 obstruction, recorded)

`LevelDatum` is FRAME-anchored: its `r` lives over `F.stageField H₀ hpin` and its `hκ`
reads `F.e₁·F.f₁·F.h`.  A `DeepTower` carries NO `KeyFrame` at stages ≥ 2 (no key
polynomial over `O` there — exactly the `Rres_exists` research content), so there is no
j-indexed family of `LevelDatum`s covering the HIGHER rungs; those enter the carrier
machinery only through RUNG's `RungLift`/`towerPacks` interface (its §2.3 adjudication).
What IS produced per truncation is the rung-2 datum — truncation-INVARIANT
(`levelDatumOf_trunc`), which is precisely the shape `rung2Carrier` consumes and the
shape the bank instantiates at each `core.T.trunc j hj`.

## Charge 3 — the B-1 rung-2 slope inequality is the tower's own floor chain

`levelDatumOf_b1`: at the adapter's output the RE-SIGNED B-1 floor
`ℓ₂·(L.ℓ·L.seam) < u₂` with the next-rung slopes `(u₂, ℓ₂) := (T.u 3, T.e 3)` is EXACTLY
`T.hfloor 2` (the datum field `u_{i+1} > e_{i+1}·E_i` at `i = 2`), since
`L.ℓ·L.seam = T.Econst 2` (`levelDatumOf_kgrade`).  This is where the keystone's
`+1`-strictness thresholds live (S2: `85 = 2·42+1 > 84 = 2·(2·1·21)`); per C.83's S12.1
carve-out it is a HYPOTHESIS of the tower datum, honestly inherited, not re-derived.

## What lands

* §1 `towerDatumOf` / `levelDatumOf` + field pins + truncation coherence (`rfl`-level).
* §2 the canonical key: `isTestKey_composedKey` at the adapter's datum (C.47 consumed).
* §3 ★ the instantiation: `towerRung2Carrier`/`towerRung2Key`/`towerRung2Pack` and the
  per-truncation `truncRung2Pack` — RUNG's rung-2 pack at EVERY tower truncation with
  `3 ≤ j`, slopes the tower's own `(T.u 3, T.e 3)`, key the composed key, B-1 from
  `hfloor` — plus `truncRung2_wcoeff_mul` (the convolution firing there) and the
  `PackAt` bundling `towerPackAt` (the `towerPacks` base point at the adapter).
* §4 the arising layer: `arisingLevelDatum`/`arisingRung2Pack`/`arising_rung2_wcoeff_mul`
  at an `ArisingCore` (`core.finite` discharges the residue-field finiteness; the two
  honest hypotheses that remain are `0 < core.F.h` and the depth bound `3 ≤ j`).

Uniformity: no `residueCard`, no S2 numeral, no keystone datum anywhere in this file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10spine

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.I10wcc
open Uniformity.Density.Tower.I10rung

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-! ## §0 — private plumbing (the standing local-twin convention; 4th corpus repetition
of `isKey_X`/`localFieldStageField`, flagged for the future dedup pass) -/

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-! ## §1 — the spine identification: stage-2 tower data IS a `TowerDatum`, hence a `LevelDatum` -/

/-- The stage-2 residual of the tower, moved to the concrete stage field along the GC-7
iterate witness `T.base`. -/
noncomputable def spineResidual (T : DeepTower F H₀ hpin r) :
    Polynomial (F.stageField H₀ hpin) :=
  (T.ψ 1).map (T.base : T.fld 1 →+* F.stageField H₀ hpin)

/-- The four `hψ` laws transport along `T.base` (a ring equivalence: monicity along the
hom, irreducibility along the induced polynomial-ring equivalence, degree and constant
term by injectivity). -/
theorem spineResidual_spec (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) :
    (spineResidual T).Monic ∧ Irreducible (spineResidual T) ∧
      (spineResidual T).natDegree = T.f 2 ∧ (spineResidual T).coeff 0 ≠ 0 := by
  obtain ⟨hmon, hirr, hdeg, h0⟩ := T.hψ 1 le_rfl (by omega : 1 < r)
  have hinj : Function.Injective (T.base : T.fld 1 →+* F.stageField H₀ hpin) :=
    T.base.injective
  refine ⟨hmon.map _, ?_, ?_, ?_⟩
  · have hEq : spineResidual T = Polynomial.mapEquiv T.base (T.ψ 1) := rfl
    rw [hEq]
    exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv T.base)).mpr hirr
  · rw [spineResidual, Polynomial.natDegree_map_eq_of_injective hinj]
    exact hdeg
  · rw [spineResidual, Polynomial.coeff_map]
    exact fun h => h0 (hinj (h.trans (map_zero _).symm))

/-- **The spine identification, stage 2**: a depth-`r ≥ 2` tower's second stage is a
C.42 `TowerDatum` — every field a tower field (properness `hproper 2`, coprimality
`hcop 2`, the node floor from `hfloor 1` + the frame pins). -/
noncomputable def towerDatumOf (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) :
    TowerDatum F H₀ hpin where
  e₂ := T.e 2
  f₂ := T.f 2
  u₂ := T.u 2
  ψ₂ := spineResidual T
  he₂ := T.he 2 (by omega) h2
  hf₂ := T.hf 2 (by omega) h2
  hcomp := T.hproper 2 le_rfl h2
  hcop := T.hcop 2 le_rfl h2
  hfloor := by
    have h := T.hfloor 1 le_rfl (by omega : 1 < r)
    rw [T.he1, T.hf1, T.hu1] at h
    rw [mul_assoc]
    exact h
  hψmonic := (spineResidual_spec T h2).1
  hψirr := (spineResidual_spec T h2).2.1
  hψdeg := (spineResidual_spec T h2).2.2.1
  hψ0 := (spineResidual_spec T h2).2.2.2

@[simp] theorem towerDatumOf_e₂ (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) :
    (towerDatumOf T h2).e₂ = T.e 2 := rfl

@[simp] theorem towerDatumOf_f₂ (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) :
    (towerDatumOf T h2).f₂ = T.f 2 := rfl

@[simp] theorem towerDatumOf_u₂ (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) :
    (towerDatumOf T h2).u₂ = T.u 2 := rfl

@[simp] theorem towerDatumOf_ψ₂ (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) :
    (towerDatumOf T h2).ψ₂ = spineResidual T := rfl

/-- Truncation coherence at the `TowerDatum` level: `trunc` changes no data, so the
stage-2 datum of a truncation IS the tower's (RUNG's defeq gotcha does not bite — the
two structure literals are definitionally equal, proofs by irrelevance). -/
theorem towerDatumOf_trunc (T : DeepTower F H₀ hpin r) (j : ℕ) (hj : j ≤ r)
    (h2 : 2 ≤ j) :
    towerDatumOf (T.trunc j hj) h2 = towerDatumOf T (h2.trans hj) := rfl

/-- ★ **THE D3-03 SPINE ADAPTER**: the C.09 `LevelDatum` of a depth-`r ≥ 2` tower —
the stage-2 data through the LANDED C.44 bridge (`TowerDatum.levelDatum`), so the
residual is the η-twisted `towerLabel`, exactly what every §5 consumer reads. -/
noncomputable def levelDatumOf (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) : LevelDatum F H₀ hpin :=
  (towerDatumOf T h2).levelDatum hπ

@[simp] theorem levelDatumOf_u (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) : (levelDatumOf T h2 hπ).u = T.u 2 := rfl

@[simp] theorem levelDatumOf_ℓ (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) : (levelDatumOf T h2 hπ).ℓ = T.e 2 := rfl

theorem levelDatumOf_r (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) : (levelDatumOf T h2 hπ).r = towerLabel (towerDatumOf T h2) := rfl

/-- the residual's degree is the tower's own stage-2 residual degree. -/
theorem levelDatumOf_r_natDegree (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) : (levelDatumOf T h2 hπ).r.natDegree = T.f 2 :=
  (towerLabel_spec (towerDatumOf T h2) hπ).2.2.1

/-- the datum's key degree in tower data: `D″ = (e₁f₁)·e₂·f₂`. -/
theorem levelDatumOf_keyDeg₂ (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) :
    (levelDatumOf T h2 hπ).keyDeg₂ = (F.e₁ * F.f₁) * T.e 2 * T.f 2 := by
  show (F.e₁ * F.f₁) * (levelDatumOf T h2 hπ).ℓ * (levelDatumOf T h2 hπ).r.natDegree = _
  rw [levelDatumOf_r_natDegree T h2 hπ, levelDatumOf_ℓ T h2 hπ]

/-- the datum's key degree IS the tower's own ladder numeral `D₂ = Dcum 2`. -/
theorem levelDatumOf_keyDeg₂_Dcum (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) :
    (levelDatumOf T h2 hπ).keyDeg₂ = T.Dcum 2 := by
  rw [levelDatumOf_keyDeg₂ T h2 hπ, DeepTower.Dcum,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton, T.he1, T.hf1]
  ring

/-- the datum's seam in tower data: `T₂ = f₂·u₂`. -/
theorem levelDatumOf_seam (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) : (levelDatumOf T h2 hπ).seam = T.f 2 * T.u 2 := by
  show (levelDatumOf T h2 hπ).r.natDegree * (levelDatumOf T h2 hπ).u = _
  rw [levelDatumOf_r_natDegree T h2 hπ, levelDatumOf_u T h2 hπ]

/-- ★ the rung-2 key grade `L.ℓ·L.seam` IS the tower's side constant `E₂ = Econst 2` —
the identification that makes the B-1 floor the tower's own `hfloor`. -/
theorem levelDatumOf_kgrade (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) :
    (levelDatumOf T h2 hπ).ℓ * (levelDatumOf T h2 hπ).seam = T.Econst 2 := by
  rw [levelDatumOf_ℓ T h2 hπ, levelDatumOf_seam T h2 hπ, DeepTower.Econst, mul_assoc]

/-- Truncation coherence at the `LevelDatum` level: the adapter's datum is
truncation-INVARIANT — every truncation `j ≥ 2` hands the carrier machinery the same
level datum. -/
theorem levelDatumOf_trunc (T : DeepTower F H₀ hpin r) (j : ℕ) (hj : j ≤ r)
    (h2 : 2 ≤ j) (hπ : Irreducible π) :
    levelDatumOf (T.trunc j hj) h2 hπ = levelDatumOf T (h2.trans hj) hπ :=
  congrArg (fun T' => T'.levelDatum hπ) (towerDatumOf_trunc T j hj h2)

/-- ★ **Charge 3 — the B-1 rung-2 slope inequality holds at the adapter's output**:
with the next-rung slopes `(u₂, ℓ₂) := (T.u 3, T.e 3)`, RUNG's `hstrict` is EXACTLY the
tower's own floor-chain field `hfloor 2` (`u₃ > e₃·E₂`, S12.1's carve-out — the datum's
`+1`-strictness, where the keystone thresholds live). -/
theorem levelDatumOf_b1 (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) (h3 : 3 ≤ r)
    (hπ : Irreducible π) :
    T.e 3 * ((levelDatumOf T h2 hπ).ℓ * (levelDatumOf T h2 hπ).seam) < T.u 3 := by
  rw [levelDatumOf_kgrade T h2 hπ]
  exact T.hfloor 2 (by omega) (by omega)

/-! ## §2 — the canonical key at the adapter's datum (C.47 consumed) -/

/-- The composed key `Φ₂` of the stage-2 tower datum is a test key for the adapter's
level datum — C.47's `composedKey_isTestKey`, consumed verbatim. -/
theorem isTestKey_composedKey (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) (hh : 1 ≤ F.h) [Finite (ResidueField O)] :
    IsTestKey (levelDatumOf T h2 hπ) (composedKey (towerDatumOf T h2)) :=
  composedKey_isTestKey (towerDatumOf T h2) hπ hh

/-! ## §3 — ★ the instantiation: RUNG's rung-2 pack at the tower, and at every truncation -/

/-- ★ the rung-2 weighted carrier at the tower's own level datum. -/
noncomputable def towerRung2Carrier (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r)
    (hπ : Irreducible π) (hh : 0 < F.h) :
    WeightedCarrier O (AdjoinRoot (levelDatumOf T h2 hπ).r) :=
  rung2Carrier (levelDatumOf T h2 hπ) hπ hh

/-- ★ the rung-2 key pack at the tower's own level datum, key = the composed key,
outer slopes = the tower's OWN stage-3 slopes, strictness = the tower's own floor. -/
noncomputable def towerRung2Key (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) (h3 : 3 ≤ r)
    (hπ : Irreducible π) (hh : 0 < F.h) [Finite (ResidueField O)] :
    CarrierKey (towerRung2Carrier T h2 hπ hh) (T.u 3) (T.e 3) :=
  rung2Key (levelDatumOf T h2 hπ) hπ hh (isTestKey_composedKey T h2 hπ hh)
    (T.he 3 (by omega) h3) (levelDatumOf_b1 T h2 h3 hπ)

/-- ★★ **the rung-2 pack at the tower** — carrier + key + exact-grade nonvanishing,
every input the tower's own datum. -/
noncomputable def towerRung2Pack (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) (h3 : 3 ≤ r)
    (hπ : Irreducible π) (hh : 0 < F.h) [Finite (ResidueField O)] :
    RungPack O (AdjoinRoot (levelDatumOf T h2 hπ).r) (T.u 3) (T.e 3) :=
  rung2Pack (levelDatumOf T h2 hπ) hπ hh (isTestKey_composedKey T h2 hπ hh)
    (T.he 3 (by omega) h3) (levelDatumOf_b1 T h2 h3 hπ)

/-- ★ **the depth-adapter row's discharge shape**: the rung-2 pack at EVERY truncation
`j` of the tower with `3 ≤ j ≤ r` — the bank's per-truncation instantiation point. -/
noncomputable def truncRung2Pack (T : DeepTower F H₀ hpin r) (j : ℕ) (hj : j ≤ r)
    (h2 : 2 ≤ j) (h3 : 3 ≤ j) (hπ : Irreducible π) (hh : 0 < F.h)
    [Finite (ResidueField O)] :
    RungPack O (AdjoinRoot (levelDatumOf (T.trunc j hj) h2 hπ).r)
      ((T.trunc j hj).u 3) ((T.trunc j hj).e 3) :=
  towerRung2Pack (T.trunc j hj) h2 h3 hπ hh

/-- ★ the weighted convolution law fires at every tower truncation's rung-2 pack. -/
theorem truncRung2_wcoeff_mul (T : DeepTower F H₀ hpin r) (j : ℕ) (hj : j ≤ r)
    (h2 : 2 ≤ j) (h3 : 3 ≤ j) (hπ : Irreducible π) (hh : 0 < F.h)
    [Finite (ResidueField O)] {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor (truncRung2Pack T j hj h2 h3 hπ hh).C
      (truncRung2Pack T j hj h2 h3 hπ hh).P β g)
    (hz : LineFloor (truncRung2Pack T j hj h2 h3 hπ hh).C
      (truncRung2Pack T j hj h2 h3 hπ hh).P β' z) (J : ℕ) :
    wcoeff (truncRung2Pack T j hj h2 h3 hπ hh).C (truncRung2Pack T j hj h2 h3 hπ hh).P
        (β + β') (g * z) J
      = ∑ i ∈ Finset.range (J + 1),
          wcoeff (truncRung2Pack T j hj h2 h3 hπ hh).C
              (truncRung2Pack T j hj h2 h3 hπ hh).P β g i
            * wcoeff (truncRung2Pack T j hj h2 h3 hπ hh).C
                (truncRung2Pack T j hj h2 h3 hπ hh).P β' z (J - i) :=
  wcoeff_mul _ _ hg hz J

/-- ★ the `towerPacks` BASE POINT at the adapter: the tower's rung-2 pack bundled with
its ring and slopes (the recursion motive of RUNG's induction wrapper) — an arising
tower's own rungs now feed the iterated carrier machinery given per-rung `LiftAt`s. -/
noncomputable def towerPackAt (T : DeepTower F H₀ hpin r) (h2 : 2 ≤ r) (h3 : 3 ≤ r)
    (hπ : Irreducible π) (hh : 0 < F.h) [Finite (ResidueField O)] : PackAt O :=
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible (levelDatumOf T h2 hπ).r) := ⟨(levelDatumOf T h2 hπ).hrirr⟩
  letI : Field (AdjoinRoot (levelDatumOf T h2 hπ).r) := AdjoinRoot.instField
  ⟨AdjoinRoot (levelDatumOf T h2 hπ).r, T.u 3, T.e 3, towerRung2Pack T h2 h3 hπ hh⟩

/-! ## §4 — the arising layer: the adapter at an `ArisingCore`'s truncations -/

section Arising

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Kt : Type uKt} [Field Kt] {Lx : Type uL} [Field Lx] [Algebra Kt Lx] {n : ℕ}

/-- the adapter's level datum at an arising core's truncation `j ≥ 2`. -/
noncomputable def arisingLevelDatum (core : ArisingCore (O := O) Kt Lx n) (j : ℕ)
    (hj : j ≤ core.r) (h2 : 2 ≤ j) : LevelDatum core.F core.H₀ core.hpin :=
  levelDatumOf (core.T.trunc j hj) h2 core.hπ

/-- the arising datum is truncation-invariant (all `j` hand the machinery ONE datum). -/
theorem arisingLevelDatum_eq (core : ArisingCore (O := O) Kt Lx n) {j j' : ℕ}
    (hj : j ≤ core.r) (hj' : j' ≤ core.r) (h2 : 2 ≤ j) (h2' : 2 ≤ j') :
    arisingLevelDatum core j hj h2 = arisingLevelDatum core j' hj' h2' := by
  rw [arisingLevelDatum, arisingLevelDatum, levelDatumOf_trunc, levelDatumOf_trunc]

/-- ★ **rung-2 packs at EVERY arising tower truncation** — the depth-adapter row fired
at the campaign's own carrier: the core supplies `π`, the frame, the tower, and the
residue-field finiteness; the honest remainders are `0 < core.F.h` and depth `3 ≤ j`. -/
noncomputable def arisingRung2Pack (core : ArisingCore (O := O) Kt Lx n) (j : ℕ)
    (hj : j ≤ core.r) (h2 : 2 ≤ j) (h3 : 3 ≤ j) (hh : 0 < core.F.h) :
    RungPack O (AdjoinRoot (arisingLevelDatum core j hj h2).r)
      ((core.T.trunc j hj).u 3) ((core.T.trunc j hj).e 3) :=
  haveI := core.finite
  towerRung2Pack (core.T.trunc j hj) h2 h3 core.hπ hh

/-- ★ the convolution law at every arising truncation's rung-2 pack. -/
theorem arising_rung2_wcoeff_mul (core : ArisingCore (O := O) Kt Lx n) (j : ℕ)
    (hj : j ≤ core.r) (h2 : 2 ≤ j) (h3 : 3 ≤ j) (hh : 0 < core.F.h)
    {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor (arisingRung2Pack core j hj h2 h3 hh).C
      (arisingRung2Pack core j hj h2 h3 hh).P β g)
    (hz : LineFloor (arisingRung2Pack core j hj h2 h3 hh).C
      (arisingRung2Pack core j hj h2 h3 hh).P β' z) (J : ℕ) :
    wcoeff (arisingRung2Pack core j hj h2 h3 hh).C (arisingRung2Pack core j hj h2 h3 hh).P
        (β + β') (g * z) J
      = ∑ i ∈ Finset.range (J + 1),
          wcoeff (arisingRung2Pack core j hj h2 h3 hh).C
              (arisingRung2Pack core j hj h2 h3 hh).P β g i
            * wcoeff (arisingRung2Pack core j hj h2 h3 hh).C
                (arisingRung2Pack core j hj h2 h3 hh).P β' z (J - i) :=
  wcoeff_mul _ _ hg hz J

end Arising

end Uniformity.Density.Tower.I10spine

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10spine.towerDatumOf
#print axioms Uniformity.Density.Tower.I10spine.levelDatumOf
#print axioms Uniformity.Density.Tower.I10spine.levelDatumOf_trunc
#print axioms Uniformity.Density.Tower.I10spine.levelDatumOf_kgrade
#print axioms Uniformity.Density.Tower.I10spine.levelDatumOf_b1
#print axioms Uniformity.Density.Tower.I10spine.isTestKey_composedKey
#print axioms Uniformity.Density.Tower.I10spine.towerRung2Carrier
#print axioms Uniformity.Density.Tower.I10spine.towerRung2Key
#print axioms Uniformity.Density.Tower.I10spine.towerRung2Pack
#print axioms Uniformity.Density.Tower.I10spine.truncRung2Pack
#print axioms Uniformity.Density.Tower.I10spine.truncRung2_wcoeff_mul
#print axioms Uniformity.Density.Tower.I10spine.towerPackAt
#print axioms Uniformity.Density.Tower.I10spine.arisingLevelDatum
#print axioms Uniformity.Density.Tower.I10spine.arisingRung2Pack
#print axioms Uniformity.Density.Tower.I10spine.arising_rung2_wcoeff_mul

end AxCheck
