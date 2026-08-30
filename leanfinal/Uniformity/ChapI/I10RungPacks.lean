/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10WeightedCarrier
import Uniformity.ChapC.C136f14f
import Uniformity.ChapC.C136f14c
import Uniformity.ChapC.C14

/-!
# Uniformity.ChapI.I10RungPacks — UNIT RUNG: per-rung carrier packs up the tower

WCC (`I10WeightedCarrier`) landed the abstract `WeightedCarrier`/`CarrierKey` packs and
the general weighted convolution law `wcoeff_mul`; the `LevelSiteBank` remainder became
per-rung pack instantiation.  This file instantiates and iterates:

* §1 the normalizer exponent: `L.cocycle` (C28) is a COBOUNDARY over ℕ — the exponent
  `normExp L m = (s(m) + (ℓ−1)s(1)·m)/ℓ` satisfies
  `normExp a + normExp b = normExp (a+b) + cocycle a b`.
* §2 ★ **the rung-2 carrier** at a general `LevelDatum`: `supp := dv2Hgt L`,
  `read := root^{normExp} · dv2FullRead` — the twist absorbs the carry cocycle of the
  landed absolute carry law (`C136f14c.dv2FullReadCarryLaw`), making the read exactly
  multiplicative; every other field is a landed f14/l2e/mh3 lemma.
* §3 ★ **the rung-2 key pack** at any test key (`IsTestKey`, C13): key lifting at rung 2
  is the LANDED `dv2FullRead_testKey` (the root relation), the D3AD support laws are
  C134dv2g's survival core through `isMuKey_of_isTestKey` (P1), and nonvacuity is
  `exists_testKey` (C14).  `wcoeff_mul` then fires at rung 2 of a general tower —
  the level-2→3 weighted convolution, uniform in `q` and the frame
  (`rung2_wcoeff_mul`), the general-tower counterpart one level down of the S2-pinned
  `s2Mu4Coeff_mul`.
* §4 `RungPack`: carrier + key + the exact-grade nonvanishing `exact_ne` (with the FGMN
  key-degree fence); rung 2 instance via `dv2FullRead_ne_zero_of_exact`.
* §5–§6 **the iteration**: from a pack, the next-level carrier
  `nextCarrier : WeightedCarrier O (Polynomial K)` exists UNCONDITIONALLY
  (`supp' := nextSupp` the line infimum, `read' := nextRead` the `wcoeff` generating
  polynomial; `supp_mul` = the new `lineFloor_mul` pricing + the `exact_ne`-driven upper
  bound).  ★ FINDING: `CarrierKey (nextCarrier R) u' ℓ'` is PROVABLY EMPTY
  (`supp_key` + `exact_ne` contradict `read_key`) — the pass to a quotient of
  `Polynomial K` (the next letter's ring) is structurally forced, not a convenience.
* §7 **the conditional step and the induction wrapper**: `pushCarrier` along any ring
  hom is a carrier; `RungLift` (hom + key pack + pushed nonvanishing — exactly the
  `Rres_exists`/`graded_scalar_nonzero` genre, adjudicated NOT a field of the
  realization's chain data, hence honestly a named per-rung obligation) steps a pack
  one rung; `towerPacks` recurses: packs at all rungs from base + step, with the
  convolution law firing at every rung (`towerPacks_wcoeff_mul`).

Uniformity: no `residueCard`, no S2 numeral, no keystone datum anywhere in this file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10rung

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132rp5
open Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0
open Uniformity.Density.Tower.C136f14b (dv2FullRead_ne_zero_of_exact)
open Uniformity.Density.Tower.I10wcc

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## §0 — private plumbing (the standing local-twin convention) -/

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

/-! ## §1 — the shift twins and the normalizer exponent

`shift_spec`/`shift_unique`/`shift_add_exact` are private in C28/C136f14b/C136f14f;
local twins (third repetition in the corpus — flagged for a future dedup pass). -/

private theorem shift_spec (L : LevelDatum F H₀ hpin) (m : ℕ) :
    L.shift m < L.ℓ ∧ L.shift m * L.u ≡ m [MOD L.ℓ] := by
  have hex : ∃ b ∈ (↑(Finset.range L.ℓ) : Set ℕ), b * L.u % L.ℓ = m % L.ℓ :=
    (Uniformity.Density.Induction.class_sep_bij L.hcop).surjOn (by
      simpa only [Finset.coe_range, Set.mem_Iio] using Nat.mod_lt m L.hℓ)
  have hnone : (List.range L.ℓ).find? (fun b => (b * L.u) % L.ℓ == m % L.ℓ) ≠ none := by
    intro hn
    obtain ⟨b, hb, hcong⟩ := hex
    simp only [Finset.coe_range, Set.mem_Iio] at hb
    exact (List.find?_eq_none.mp hn b (List.mem_range.mpr hb)) (by simpa using hcong)
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hnone
  have hval : L.shift m = c := by rw [LevelDatum.shift, hc]; rfl
  refine ⟨hval ▸ List.mem_range.mp (List.mem_of_find?_eq_some hc), ?_⟩
  have hp := List.find?_some hc
  simp only [beq_iff_eq] at hp
  rw [hval]
  exact hp

private theorem shift_unique (L : LevelDatum F H₀ hpin) {m b : ℕ}
    (hb : b < L.ℓ) (hcong : b * L.u ≡ m [MOD L.ℓ]) : b = L.shift m := by
  obtain ⟨hlt, hsp⟩ := shift_spec L m
  exact Uniformity.Density.Induction.class_sep L.hcop hb hlt (hcong.trans hsp.symm)

/-- The exact (non-truncated) cocycle identity `s(a) + s(b) = s(a+b) + ℓ·c₁(a,b)`
(local twin of C136f14f's private `shift_add_exact`). -/
private theorem shift_add_exact (L : LevelDatum F H₀ hpin) (a b : ℕ) :
    L.shift a + L.shift b = L.shift (a + b) + L.ℓ * L.cocycle a b := by
  obtain ⟨-, hac⟩ := shift_spec L a
  obtain ⟨-, hbc⟩ := shift_spec L b
  have hsum : (L.shift a + L.shift b) % L.ℓ = L.shift (a + b) := by
    refine shift_unique L (Nat.mod_lt _ L.hℓ) ?_
    calc ((L.shift a + L.shift b) % L.ℓ) * L.u
        ≡ (L.shift a + L.shift b) * L.u [MOD L.ℓ] := (Nat.mod_modEq _ L.ℓ).mul_right L.u
      _ = L.shift a * L.u + L.shift b * L.u := by ring
      _ ≡ a + b [MOD L.ℓ] := hac.add hbc
  have hdm := Nat.div_add_mod (L.shift a + L.shift b) L.ℓ
  have hc := (L.cocycle_mem a b).1
  omega

/-- ★ **The normalizer exponent**: the ℕ-valued coboundary of the C28 shift cocycle,
`w(m) = (s(m) + (ℓ−1)·s(1)·m)/ℓ`.  Twisting the absolute read by `root^{w(m)}` turns
the weighted carry law into exact multiplicativity (`normExp_add`). -/
noncomputable def normExp (L : LevelDatum F H₀ hpin) (m : ℕ) : ℕ :=
  (L.shift m + (L.ℓ - 1) * L.shift 1 * m) / L.ℓ

/-- The division in `normExp` is exact (induction on `m` from the exact cocycle
identity at `(m, 1)`; no coprimality input beyond C28's own). -/
private theorem normExp_dvd (L : LevelDatum F H₀ hpin) (m : ℕ) :
    L.ℓ ∣ L.shift m + (L.ℓ - 1) * L.shift 1 * m := by
  have hd1 : (L.ℓ - 1) * L.shift 1 + L.shift 1 = L.ℓ * L.shift 1 := by
    have h1 : L.shift 1 ≤ L.ℓ * L.shift 1 := Nat.le_mul_of_pos_left _ L.hℓ
    have h2 : (L.ℓ - 1) * L.shift 1 = L.ℓ * L.shift 1 - L.shift 1 :=
      Nat.sub_one_mul L.ℓ (L.shift 1)
    omega
  induction m with
  | zero =>
      refine ⟨L.cocycle 0 0, ?_⟩
      have h := shift_add_exact L 0 0
      simp only [Nat.add_zero] at h
      omega
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      have hex := shift_add_exact L n 1
      have hsucc : (L.ℓ - 1) * L.shift 1 * (n + 1)
          = (L.ℓ - 1) * L.shift 1 * n + (L.ℓ - 1) * L.shift 1 := Nat.mul_succ _ n
      have hmul : L.ℓ * (k + L.shift 1) = L.ℓ * k + L.ℓ * L.shift 1 :=
        Nat.mul_add L.ℓ k (L.shift 1)
      have hX : L.shift (n + 1) + (L.ℓ - 1) * L.shift 1 * (n + 1)
          = L.ℓ * (k + L.shift 1) - L.ℓ * L.cocycle n 1 := by omega
      rw [hX]
      exact Nat.dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

/-- ★ the coboundary identity: `w(a) + w(b) = w(a+b) + c₁(a,b)`. -/
private theorem normExp_add (L : LevelDatum F H₀ hpin) (a b : ℕ) :
    normExp L a + normExp L b = normExp L (a + b) + L.cocycle a b := by
  obtain ⟨ka, hka⟩ := normExp_dvd L a
  obtain ⟨kb, hkb⟩ := normExp_dvd L b
  obtain ⟨kab, hkab⟩ := normExp_dvd L (a + b)
  have ea : normExp L a = ka := by
    rw [normExp, hka, Nat.mul_div_cancel_left _ L.hℓ]
  have eb : normExp L b = kb := by
    rw [normExp, hkb, Nat.mul_div_cancel_left _ L.hℓ]
  have eab : normExp L (a + b) = kab := by
    rw [normExp, hkab, Nat.mul_div_cancel_left _ L.hℓ]
  rw [ea, eb, eab]
  have hex := shift_add_exact L a b
  have hd : (L.ℓ - 1) * L.shift 1 * (a + b)
      = (L.ℓ - 1) * L.shift 1 * a + (L.ℓ - 1) * L.shift 1 * b :=
    Nat.mul_add _ a b
  have h1 : L.ℓ * (ka + kb) = L.ℓ * ka + L.ℓ * kb := Nat.mul_add L.ℓ ka kb
  have h2 : L.ℓ * (kab + L.cocycle a b) = L.ℓ * kab + L.ℓ * L.cocycle a b :=
    Nat.mul_add L.ℓ kab (L.cocycle a b)
  exact Nat.eq_of_mul_eq_mul_left L.hℓ (by omega)

/-! ## §2 — ★ the rung-2 carrier at a general level datum -/

/-- ★ **The rung-2 read**: the absolute level-2 read (`dv2FullRead`, C136l2e0) twisted
by the normalizer exponent — the weights of the L2E4 refutation live inside the read,
re-normalized by the coboundary so the carry law becomes exact multiplicativity. -/
noncomputable def rung2Read (L : LevelDatum F H₀ hpin) (m : ℕ) (f : Polynomial O) :
    AdjoinRoot L.r :=
  AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m f

/-- ★ **The rung-2 weighted carrier at a general tower level datum** — every field a
landed lemma: grading `dv2Hgt` (multiplicative by Theorem M at the level pair `L.hκ`),
read laws from C136l2e0, the carry law from C136f14c through the §1 coboundary. -/
noncomputable def rung2Carrier (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) : WeightedCarrier O (AdjoinRoot L.r) where
  supp := dv2Hgt L
  read := rung2Read L
  supp_zero := C132nv2.dv2Hgt_zero L
  supp_mul := by
    intro g z
    rcases eq_or_ne g 0 with rfl | hg
    · rw [zero_mul, C132nv2.dv2Hgt_zero L, top_add]
    rcases eq_or_ne z 0 with rfl | hz
    · rw [mul_zero, C132nv2.dv2Hgt_zero L, add_top]
    · exact C133mh3.dvSupp_mul hπ hh H₀ hpin L.hℓ
        (by rw [← mul_assoc]; exact L.hκ) hg hz
  min_supp_le_add := C132nv2.min_dv2Hgt_le_dv2Hgt_add L
  read_zero := by
    intro m
    show AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m 0 = 0
    rw [dv2FullRead_eq_zero_of_lt L hπ
      (by rw [C132nv2.dv2Hgt_zero L]; exact ENat.coe_lt_top m), mul_zero]
  read_add := by
    intro m g z hga hzb
    show AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m (g + z)
      = AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m g
        + AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m z
    rw [dv2FullRead_add_of_le L hπ hga hzb, mul_add]
  read_above := by
    intro m g h
    show AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m g = 0
    rw [dv2FullRead_eq_zero_of_lt L hπ h, mul_zero]
  read_mul := by
    intro m₁ m₂ g z hg hz
    have hcarry := C136f14c.dv2FullReadCarryLaw (O := O) π F hπ hh H₀ hpin L g z
      m₁ m₂ (L.cocycle m₁ m₂) (le_of_eq hg.symm) (le_of_eq hz.symm)
      (shift_add_exact L m₁ m₂)
    show AdjoinRoot.root L.r ^ normExp L (m₁ + m₂) * dv2FullRead L (m₁ + m₂) (g * z)
      = AdjoinRoot.root L.r ^ normExp L m₁ * dv2FullRead L m₁ g
        * (AdjoinRoot.root L.r ^ normExp L m₂ * dv2FullRead L m₂ z)
    rw [hcarry, ← mul_assoc, ← pow_add,
      show normExp L (m₁ + m₂) + L.cocycle m₁ m₂ = normExp L m₁ + normExp L m₂ from
        (normExp_add L m₁ m₂).symm,
      pow_add]
    ring

/-! ## §3 — ★ the rung-2 key pack: key lifting at rung 2 is landed content -/

/-- ★ **The rung-2 key pack** at any test key: the root relation is the LANDED
`dv2FullRead_testKey` (the key's full residual symbol dies at the level letter — the
`Rres_exists` content at rung 2), the D3AD support interface is C134dv2g's survival core
through P1 (`isMuKey_of_isTestKey`), and the `+1` strictness is the engine-honest
outer floor `ℓ₂·(L.ℓ·L.seam) < u₂` (the RE-SIGNED B-1 slope inequality). -/
noncomputable def rung2Key (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hstrict : ℓ₂ * (L.ℓ * L.seam) < u₂) :
    CarrierKey (rung2Carrier L hπ hh) u₂ ℓ₂ where
  key := Ψ
  kgrade := L.ℓ * L.seam
  monic := hΨ.1
  deg_pos := C134p1d.natDegree_pos_of_isTestKey L hΨ
  supp_key := dv2Hgt_testKey L hΨ
  read_key := by
    show AdjoinRoot.root L.r ^ normExp L (L.ℓ * L.seam)
      * dv2FullRead L (L.ℓ * L.seam) Ψ = 0
    rw [dv2FullRead_testKey L hπ hΨ, mul_zero]
  ell_pos := hℓ₂
  strict := hstrict
  supp_mod := by
    intro a b ha hb
    exact dvSupp_mul_modByKey_eq L hπ hh
      (C134p1d.isMuKey_of_isTestKey L hπ hh hΨ) ha hb
  supp_quot := by
    intro a b ha hb
    have h := dvSupp_add_le_key_quot_add L hπ hh
      (C134p1d.isMuKey_of_isTestKey L hπ hh hΨ) ha hb
    rwa [show dvSupp F Ψ L.u L.ℓ = ((L.ℓ * L.seam : ℕ) : ℕ∞) from
      dv2Hgt_testKey L hΨ] at h

/-- The rung-2 key pack is INHABITED at every level datum over a finite residue field
(`exists_testKey`, C.14) — no S2 pin needed for nonvacuity. -/
theorem rung2Key_nonempty [Finite (ResidueField O)] (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hstrict : ℓ₂ * (L.ℓ * L.seam) < u₂) :
    Nonempty (CarrierKey (rung2Carrier L hπ hh) u₂ ℓ₂) := by
  obtain ⟨Ψ, hΨ⟩ := exists_testKey L hπ hh
  exact ⟨rung2Key L hπ hh hΨ hℓ₂ hstrict⟩

/-- ★★ **The weighted convolution law at rung 2 of a GENERAL tower** — the first
general-tower rung pack beyond the base: `wcoeff_mul` fired at the rung-2 carrier/key,
uniform in `q` and the frame.  This is the general-tower counterpart, one level down,
of the S2-pinned keystone `C136l2e4.s2Mu4Coeff_mul`. -/
theorem rung2_wcoeff_mul (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hstrict : ℓ₂ * (L.ℓ * L.seam) < u₂) {β β' : ℕ}
    {g z : Polynomial O}
    (hg : LineFloor (rung2Carrier L hπ hh) (rung2Key L hπ hh hΨ hℓ₂ hstrict) β g)
    (hz : LineFloor (rung2Carrier L hπ hh) (rung2Key L hπ hh hΨ hℓ₂ hstrict) β' z)
    (J : ℕ) :
    wcoeff (rung2Carrier L hπ hh) (rung2Key L hπ hh hΨ hℓ₂ hstrict) (β + β') (g * z) J
      = ∑ j ∈ Finset.range (J + 1),
          wcoeff (rung2Carrier L hπ hh) (rung2Key L hπ hh hΨ hℓ₂ hstrict) β g j
            * wcoeff (rung2Carrier L hπ hh) (rung2Key L hπ hh hΨ hℓ₂ hstrict) β' z (J - j) :=
  wcoeff_mul _ _ hg hz J

/-! ## §4 — the rung pack: carrier + key + exact-grade nonvanishing -/

/-- ★ **A rung pack**: a weighted carrier with a key pack and the exact-grade read
NONVANISHING under the FGMN key-degree fence (`graded_scalar_nonzero` genre — the fence
is essential, FGMN Thm 4.1/Cor 4.9(1)).  `exact_ne` is what the iteration consumes on
development coefficients (whose degrees clear the fence automatically). -/
structure RungPack (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type*) [CommRing K] (u ℓ : ℕ) where
  /-- the weighted carrier. -/
  C : WeightedCarrier O K
  /-- the key pack. -/
  P : CarrierKey C u ℓ
  /-- exact-grade nonvanishing below the key degree. -/
  exact_ne : ∀ {m : ℕ} {g : Polynomial O}, g.natDegree < P.key.natDegree →
    C.supp g = (m : ℕ∞) → C.read m g ≠ 0

/-- Local twin of C136f14f's private `root_ne_zero`: the level letter is nonzero. -/
private theorem root_ne_zero (L : LevelDatum F H₀ hpin) :
    (AdjoinRoot.root L.r : AdjoinRoot L.r) ≠ 0 := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  intro h0
  have hdvd : L.r ∣ Polynomial.X := by
    rw [← AdjoinRoot.mk_X (f := L.r)] at h0
    exact AdjoinRoot.mk_eq_zero.mp h0
  obtain ⟨q, hq⟩ := hdvd
  have hr0 : L.r ≠ 0 := L.hrmonic.ne_zero
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact Polynomial.X_ne_zero hq
  have hdeg1 : (Polynomial.X : Polynomial (F.stageField H₀ hpin)).natDegree
      = L.r.natDegree + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul hr0 hq0]
  rw [Polynomial.natDegree_X] at hdeg1
  have h00 : L.r.coeff 0 * q.coeff 0 = 0 := by
    rw [← Polynomial.mul_coeff_zero, ← hq, Polynomial.coeff_X_zero]
  have hqdeg : q.natDegree = 0 := by
    have := L.hrdeg
    omega
  obtain ⟨cq, hcq⟩ := Polynomial.natDegree_eq_zero.mp hqdeg
  have hqc : q.coeff 0 ≠ 0 := by
    rw [← hcq, Polynomial.coeff_C_zero]
    intro h
    rw [h, map_zero] at hcq
    exact hq0 hcq.symm
  rcases mul_eq_zero.mp h00 with h | h
  · exact L.hr0 h
  · exact hqc h

/-- Rung-2 exact-grade nonvanishing: the twisted read of a nonzero polynomial short of
the key degree is nonzero at its exact grade (`dv2FullRead_ne_zero_of_exact`, C136f14b,
with the letter power a unit in the level field). -/
private theorem rung2_exact_ne (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) {m : ℕ} {g : Polynomial O}
    (hdeg : g.natDegree < Ψ.natDegree) (hsupp : dv2Hgt L g = (m : ℕ∞)) :
    rung2Read L m g ≠ 0 := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  letI : Field (AdjoinRoot L.r) := AdjoinRoot.instField
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [C132nv2.dv2Hgt_zero L] at hsupp
    simp at hsupp
  have hdeg' : g.natDegree < L.keyDeg₂ := by
    rw [← hΨ.2.1]; exact hdeg
  exact mul_ne_zero (pow_ne_zero _ (root_ne_zero L))
    (dv2FullRead_ne_zero_of_exact L hπ hg0 hdeg' hsupp)

/-- ★ **The rung-2 pack** — carrier, key, and nonvanishing, all from landed content. -/
noncomputable def rung2Pack (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hstrict : ℓ₂ * (L.ℓ * L.seam) < u₂) :
    RungPack O (AdjoinRoot L.r) u₂ ℓ₂ where
  C := rung2Carrier L hπ hh
  P := rung2Key L hπ hh hΨ hℓ₂ hstrict
  exact_ne := fun hdeg hsupp => rung2_exact_ne L hπ hΨ hdeg hsupp

/-! ## §5 — the iteration vocabulary: the next support and the next read -/

/-- an `ℕ∞` value above every natural is `⊤`. -/
private theorem eq_top_of_forall_nat_le {x : ℕ∞} (h : ∀ n : ℕ, (n : ℕ∞) ≤ x) : x = ⊤ := by
  rcases eq_or_ne x ⊤ with hx | hx
  · exact hx
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hx
    have hk1 := h (k + 1)
    rw [← hk] at hk1
    exact absurd (by exact_mod_cast hk1 : k + 1 ≤ k) (by omega)

section Iterate

variable {K : Type*} [CommRing K]
variable (C : WeightedCarrier O K) {u ℓ : ℕ} (P : CarrierKey C u ℓ)

/-- local guard twins of WCC's private unfoldings. -/
private theorem wcoeff_of_guard {β J : ℕ} {f : Polynomial O}
    (h1 : u * J ≤ β) (h2 : ℓ ∣ (β - u * J)) :
    wcoeff C P β f J = C.read ((β - u * J) / ℓ) (dev P.key f J) := if_pos ⟨h1, h2⟩

private theorem wcoeff_of_not_guard {β J : ℕ} {f : Polynomial O}
    (h : ¬ (u * J ≤ β ∧ ℓ ∣ (β - u * J))) : wcoeff C P β f J = 0 := if_neg h

private theorem natDegree_dev_lt (f : Polynomial O) (j : ℕ) :
    (dev P.key f j).natDegree < P.key.natDegree := by
  rcases eq_or_ne (dev P.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    exact P.deg_pos
  · exact Polynomial.natDegree_lt_natDegree h0 (degree_dev_lt P.monic P.deg_pos f j)

private theorem natDegree_quot_lt {a b : Polynomial O}
    (ha : a.natDegree < P.key.natDegree) (hb : b.natDegree < P.key.natDegree) :
    ((a * b) /ₘ P.key).natDegree < P.key.natDegree := by
  rw [Polynomial.natDegree_divByMonic _ P.monic]
  have h := Polynomial.natDegree_mul_le (p := a) (q := b)
  omega

private theorem dev_key_mul_one {a b : Polynomial O}
    (ha : a.natDegree < P.key.natDegree) (hb : b.natDegree < P.key.natDegree) :
    dev P.key (a * b) 1 = (a * b) /ₘ P.key := by
  have hunfold : dev P.key (a * b) 1 = dev P.key ((a * b) /ₘ P.key) 0 := rfl
  rw [hunfold, C130nv2.dev_zero_pin]
  rcases eq_or_ne ((a * b) /ₘ P.key) 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · exact (Polynomial.modByMonic_eq_self_iff P.monic).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
            Polynomial.degree_eq_natDegree P.monic.ne_zero]
          exact_mod_cast natDegree_quot_lt C P ha hb)

include P in
private theorem u_pos : 0 < u := lt_of_le_of_lt (Nat.zero_le _) P.strict

/-- **The next-level support**: the infimum of the key-development line values — the
`dv2Supp`/`dv3Supp` shape abstracted (ℕ-indexed infimum; past-degree slots price `⊤`). -/
noncomputable def nextSupp (f : Polynomial O) : ℕ∞ :=
  ⨅ j : ℕ, (ℓ : ℕ∞) * C.supp (dev P.key f j) + ((u * j : ℕ) : ℕ∞)

/-- WCC's `LineFloor` is exactly the coordinate form of `≤ nextSupp`. -/
theorem lineFloor_iff_le_nextSupp {β : ℕ} {f : Polynomial O} :
    LineFloor C P β f ↔ (β : ℕ∞) ≤ nextSupp C P f :=
  le_iInf_iff.symm

/-- **The next-level read**: the generating polynomial of the `wcoeff` family — the
next-level residual polynomial before the pass to the next letter's ring. -/
noncomputable def nextRead (m : ℕ) (f : Polynomial O) : Polynomial K :=
  ∑ j ∈ Finset.range (m + 1), Polynomial.C (wcoeff C P m f j) * Polynomial.X ^ j

/-- coefficient extraction: `nextRead` has coefficients exactly `wcoeff` (the range
truncation is invisible — off-range slots fail the line guard since `0 < u`). -/
theorem nextRead_coeff (m : ℕ) (f : Polynomial O) (J : ℕ) :
    (nextRead C P m f).coeff J = wcoeff C P m f J := by
  rw [nextRead, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hJ : J ∈ Finset.range (m + 1)
  · rw [if_pos hJ]
  · rw [if_neg hJ]
    symm
    refine wcoeff_of_not_guard C P fun h => ?_
    rw [Finset.mem_range] at hJ
    have hJm : J ≤ u * J := Nat.le_mul_of_pos_left J (u_pos C P)
    omega

/-- a line floor reads in `ℕ` at any abscissa with finite support value
(local twin of WCC's private `lineFloor_nat`). -/
private theorem lineFloor_nat {β : ℕ} {f : Polynomial O} (hf : LineFloor C P β f)
    {j A : ℕ} (hA : C.supp (dev P.key f j) = (A : ℕ∞)) : β ≤ ℓ * A + u * j := by
  have h := hf j
  rw [hA] at h
  exact_mod_cast h

/-- the factor grade floor at an on-guard slot (local twin of WCC's private
`wcoeff_grade_floor`). -/
private theorem grade_floor {β : ℕ} {f : Polynomial O} (hf : LineFloor C P β f)
    {j : ℕ} (h2 : ℓ ∣ (β - u * j)) :
    (((β - u * j) / ℓ : ℕ) : ℕ∞) ≤ C.supp (dev P.key f j) := by
  rcases eq_or_ne (C.supp (dev P.key f j)) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hA]
  have hnat := lineFloor_nat C P hf hA.symm
  obtain ⟨k, hk⟩ := h2
  rw [hk, Nat.mul_div_cancel_left _ P.ell_pos]
  have hkA : ℓ * k ≤ ℓ * A := by omega
  exact_mod_cast Nat.le_of_mul_le_mul_left hkA P.ell_pos

-- line-value floors pass to finite sums (the `le_weight_dv2Hgt_sum` pattern of
-- C136l2e2, at the abstract carrier).
include P in
private theorem le_line_finsetSum {ι : Type*} (s : Finset ι) (G : ι → Polynomial O)
    {c d : ℕ∞} (hall : ∀ p ∈ s, c ≤ (ℓ : ℕ∞) * C.supp (G p) + d) :
    c ≤ (ℓ : ℕ∞) * C.supp (∑ p ∈ s, G p) + d := by
  classical
  have htop : (ℓ : ℕ∞) * ⊤ = ⊤ := WithTop.mul_top (Nat.cast_ne_zero.mpr P.ell_pos.ne')
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, C.supp_zero, htop, top_add]
      exact le_top
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      have hmono : Monotone (fun x : ℕ∞ => (ℓ : ℕ∞) * x + d) :=
        fun _ _ hxy => add_le_add (mul_le_mul' le_rfl hxy) le_rfl
      calc c ≤ min ((ℓ : ℕ∞) * C.supp (G a) + d)
              ((ℓ : ℕ∞) * C.supp (∑ p ∈ t, G p) + d) :=
            le_min (hall a (Finset.mem_cons_self a t))
              (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))
        _ = (ℓ : ℕ∞) * min (C.supp (G a)) (C.supp (∑ p ∈ t, G p)) + d :=
            (hmono.map_min).symm
        _ ≤ (ℓ : ℕ∞) * C.supp (G a + ∑ p ∈ t, G p) + d :=
            hmono (C.min_supp_le_add _ _)

/-- the line floors of the two factors price every antidiagonal main pair. -/
private theorem pair_floor {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) {J j : ℕ} (hj : j ≤ J) :
    ((β + β' : ℕ) : ℕ∞)
      ≤ (ℓ : ℕ∞) * (C.supp (dev P.key g j) + C.supp (dev P.key z (J - j)))
        + ((u * J : ℕ) : ℕ∞) := by
  have hxy : u * j + u * (J - j) = u * J := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj]
  calc ((β + β' : ℕ) : ℕ∞) = (β : ℕ∞) + (β' : ℕ∞) := by push_cast; rfl
    _ ≤ ((ℓ : ℕ∞) * C.supp (dev P.key g j) + ((u * j : ℕ) : ℕ∞))
        + ((ℓ : ℕ∞) * C.supp (dev P.key z (J - j)) + ((u * (J - j) : ℕ) : ℕ∞)) :=
      add_le_add (hg j) (hz (J - j))
    _ = (ℓ : ℕ∞) * (C.supp (dev P.key g j) + C.supp (dev P.key z (J - j)))
        + (((u * j : ℕ) : ℕ∞) + ((u * (J - j) : ℕ) : ℕ∞)) := by
      rw [mul_add, add_add_add_comm]
    _ = _ := by rw [← Nat.cast_add, hxy]

/-- the carry-diagonal floor: quotient terms clear the product line through
`supp_quot` and `ℓ·kgrade ≤ u`. -/
private theorem carry_floor {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) {J j : ℕ} (hj : j + 1 ≤ J) :
    ((β + β' : ℕ) : ℕ∞)
      ≤ (ℓ : ℕ∞) * C.supp (dev P.key (dev P.key g j * dev P.key z (J - 1 - j)) 1)
        + ((u * J : ℕ) : ℕ∞) := by
  rw [dev_key_mul_one C P (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - 1 - j))]
  have hq := P.supp_quot (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - 1 - j))
  have hxy : u * j + u * (J - 1 - j) = u * (J - 1) := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega : j ≤ J - 1)]
  have hnat : ℓ * P.kgrade + u * (J - 1) ≤ u * J := by
    have hs := P.strict
    have hu : u * (J - 1) + u = u * J := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  calc ((β + β' : ℕ) : ℕ∞) = (β : ℕ∞) + (β' : ℕ∞) := by push_cast; rfl
    _ ≤ ((ℓ : ℕ∞) * C.supp (dev P.key g j) + ((u * j : ℕ) : ℕ∞))
        + ((ℓ : ℕ∞) * C.supp (dev P.key z (J - 1 - j)) + ((u * (J - 1 - j) : ℕ) : ℕ∞)) :=
      add_le_add (hg j) (hz (J - 1 - j))
    _ = (ℓ : ℕ∞) * (C.supp (dev P.key g j) + C.supp (dev P.key z (J - 1 - j)))
        + ((u * (J - 1) : ℕ) : ℕ∞) := by
      rw [mul_add, add_add_add_comm, ← Nat.cast_add, hxy]
    _ ≤ (ℓ : ℕ∞) * ((P.kgrade : ℕ∞)
          + C.supp ((dev P.key g j * dev P.key z (J - 1 - j)) /ₘ P.key))
        + ((u * (J - 1) : ℕ) : ℕ∞) :=
      add_le_add (mul_le_mul' le_rfl hq) le_rfl
    _ = (ℓ : ℕ∞) * C.supp ((dev P.key g j * dev P.key z (J - 1 - j)) /ₘ P.key)
        + ((ℓ * P.kgrade + u * (J - 1) : ℕ) : ℕ∞) := by
      rw [mul_add]
      push_cast
      ring
    _ ≤ _ := add_le_add le_rfl (Nat.cast_le.mpr hnat)

/-- ★ **the line-floor product law** (WCC's anticipated `lineFloor_mul`): pointwise
line floors multiply — the supermultiplicativity of the next-level support. -/
theorem lineFloor_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) :
    LineFloor C P (β + β') (g * z) := by
  intro J
  rw [dev_mul_conv_split_monic P.monic P.deg_pos g z J]
  set M := ∑ j ∈ Finset.range (J + 1), (dev P.key g j * dev P.key z (J - j)) %ₘ P.key
    with hM
  set Cr := ∑ j ∈ Finset.range J, dev P.key (dev P.key g j * dev P.key z (J - 1 - j)) 1
    with hCr
  have hmono : Monotone (fun x : ℕ∞ => (ℓ : ℕ∞) * x + ((u * J : ℕ) : ℕ∞)) :=
    fun _ _ hxy => add_le_add (mul_le_mul' le_rfl hxy) le_rfl
  have hA : ((β + β' : ℕ) : ℕ∞) ≤ (ℓ : ℕ∞) * C.supp M + ((u * J : ℕ) : ℕ∞) := by
    refine le_line_finsetSum C P _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [P.supp_mod (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - j))]
    exact pair_floor C P hg hz (by omega)
  have hB : ((β + β' : ℕ) : ℕ∞) ≤ (ℓ : ℕ∞) * C.supp Cr + ((u * J : ℕ) : ℕ∞) := by
    refine le_line_finsetSum C P _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact carry_floor C P hg hz (by omega)
  calc ((β + β' : ℕ) : ℕ∞)
      ≤ min ((ℓ : ℕ∞) * C.supp M + ((u * J : ℕ) : ℕ∞))
          ((ℓ : ℕ∞) * C.supp Cr + ((u * J : ℕ) : ℕ∞)) := le_min hA hB
    _ = (ℓ : ℕ∞) * min (C.supp M) (C.supp Cr) + ((u * J : ℕ) : ℕ∞) :=
        (hmono.map_min).symm
    _ ≤ (ℓ : ℕ∞) * C.supp (M + Cr) + ((u * J : ℕ) : ℕ∞) :=
        hmono (C.min_supp_le_add _ _)

/-- the ≥ half of the next-support product law, in full `ℕ∞` generality. -/
theorem le_nextSupp_mul (g z : Polynomial O) :
    nextSupp C P g + nextSupp C P z ≤ nextSupp C P (g * z) := by
  have key : ∀ a b : ℕ, (a : ℕ∞) ≤ nextSupp C P g → (b : ℕ∞) ≤ nextSupp C P z →
      ((a + b : ℕ) : ℕ∞) ≤ nextSupp C P (g * z) := fun a b ha hb =>
    (lineFloor_iff_le_nextSupp C P).mp (lineFloor_mul C P
      ((lineFloor_iff_le_nextSupp C P).mpr ha) ((lineFloor_iff_le_nextSupp C P).mpr hb))
  rcases eq_or_ne (nextSupp C P g) ⊤ with hgT | hgT
  · have htop : nextSupp C P (g * z) = ⊤ :=
      eq_top_of_forall_nat_le fun n => by
        have h := key n 0 (by rw [hgT]; exact le_top) (by simp)
        simpa using h
    rw [hgT, top_add, htop]
  rcases eq_or_ne (nextSupp C P z) ⊤ with hzT | hzT
  · have htop : nextSupp C P (g * z) = ⊤ :=
      eq_top_of_forall_nat_le fun n => by
        have h := key 0 n (by simp) (by rw [hzT]; exact le_top)
        simpa using h
    rw [hzT, add_top, htop]
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 hgT
  obtain ⟨Sz, hSz⟩ := ENat.ne_top_iff_exists.1 hzT
  rw [← hSg, ← hSz, ← Nat.cast_add]
  exact key Sg Sz (le_of_eq hSg) (le_of_eq hSz)

end Iterate

/-! ## §6 — the next carrier assembles (unconditional given a pack) -/

section NextCarrier

variable {K : Type*} [CommRing K]

/-- exact-grade nonvanishing of the NEXT read, from the pack's `exact_ne` (no fence
needed on `f`: the inner reads are development coefficients, which clear the key-degree
fence automatically).  Consumes the free `ℕ∞` attainment of a finite infimum. -/
theorem nextRead_ne_zero_of_exact {u ℓ : ℕ} (R : RungPack O K u ℓ) {β : ℕ}
    {f : Polynomial O} (hf : nextSupp R.C R.P f = (β : ℕ∞)) :
    nextRead R.C R.P β f ≠ 0 := by
  have hβ1 : ¬ (((β + 1 : ℕ) : ℕ∞) ≤ nextSupp R.C R.P f) := by
    intro h
    rw [hf] at h
    have : β + 1 ≤ β := by exact_mod_cast h
    omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (ℓ : ℕ∞) * R.C.supp (dev R.P.key f j)
      + ((u * j : ℕ) : ℕ∞) < ((β + 1 : ℕ) : ℕ∞) := by
    by_contra hc
    push Not at hc
    exact hβ1 (le_iInf hc)
  have hfl : (β : ℕ∞) ≤ (ℓ : ℕ∞) * R.C.supp (dev R.P.key f j)
      + ((u * j : ℕ) : ℕ∞) := by
    conv_lhs => rw [← hf]
    exact iInf_le _ j
  have htop : (ℓ : ℕ∞) * ⊤ = ⊤ :=
    WithTop.mul_top (Nat.cast_ne_zero.mpr R.P.ell_pos.ne')
  rcases eq_or_ne (R.C.supp (dev R.P.key f j)) ⊤ with hT | hT
  · rw [hT, htop, top_add] at hj
    exact absurd hj (not_lt.mpr le_top)
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hA] at hj hfl
  have hnat1 : ℓ * A + u * j < β + 1 := by exact_mod_cast hj
  have hnat2 : β ≤ ℓ * A + u * j := by exact_mod_cast hfl
  intro h0
  have hc : wcoeff R.C R.P β f j = 0 := by
    rw [← nextRead_coeff R.C R.P β f j, h0, Polynomial.coeff_zero]
  have hg1 : u * j ≤ β := by omega
  have hg2 : ℓ ∣ (β - u * j) := ⟨A, by omega⟩
  rw [wcoeff_of_guard R.C R.P hg1 hg2] at hc
  have hdivA : (β - u * j) / ℓ = A := by
    rw [show β - u * j = ℓ * A from by omega, Nat.mul_div_cancel_left _ R.P.ell_pos]
  rw [hdivA] at hc
  exact R.exact_ne (natDegree_dev_lt R.C R.P f j) hA.symm hc

/-- the next support of `0` is `⊤`. -/
theorem nextSupp_zero_p {u ℓ : ℕ} (R : RungPack O K u ℓ) :
    nextSupp R.C R.P (0 : Polynomial O) = ⊤ := by
  have htop : (ℓ : ℕ∞) * ⊤ = ⊤ :=
    WithTop.mul_top (Nat.cast_ne_zero.mpr R.P.ell_pos.ne')
  have hterm : ∀ j : ℕ,
      (ℓ : ℕ∞) * R.C.supp (dev R.P.key 0 j) + ((u * j : ℕ) : ℕ∞) = ⊤ := fun j => by
    rw [C131w.dev_zero', R.C.supp_zero, htop, top_add]
  simp only [nextSupp]
  rw [iInf_congr hterm]
  exact iInf_top

/-- the next support is ultrametric. -/
theorem min_nextSupp_le_add {u ℓ : ℕ} (R : RungPack O K u ℓ) (g z : Polynomial O) :
    min (nextSupp R.C R.P g) (nextSupp R.C R.P z) ≤ nextSupp R.C R.P (g + z) := by
  refine le_iInf fun j => ?_
  have hmono : Monotone (fun x : ℕ∞ => (ℓ : ℕ∞) * x + ((u * j : ℕ) : ℕ∞)) :=
    fun _ _ hxy => add_le_add (mul_le_mul' le_rfl hxy) le_rfl
  calc min (nextSupp R.C R.P g) (nextSupp R.C R.P z)
      ≤ min ((ℓ : ℕ∞) * R.C.supp (dev R.P.key g j) + ((u * j : ℕ) : ℕ∞))
          ((ℓ : ℕ∞) * R.C.supp (dev R.P.key z j) + ((u * j : ℕ) : ℕ∞)) :=
        min_le_min (iInf_le _ j) (iInf_le _ j)
    _ = (ℓ : ℕ∞) * min (R.C.supp (dev R.P.key g j)) (R.C.supp (dev R.P.key z j))
        + ((u * j : ℕ) : ℕ∞) := (hmono.map_min).symm
    _ ≤ (ℓ : ℕ∞) * R.C.supp (dev R.P.key g j + dev R.P.key z j)
        + ((u * j : ℕ) : ℕ∞) := hmono (R.C.min_supp_le_add _ _)
    _ = (ℓ : ℕ∞) * R.C.supp (dev R.P.key (g + z) j) + ((u * j : ℕ) : ℕ∞) := by
        rw [dev_add_of_monic R.P.monic]

/-- the next read of `0` vanishes. -/
theorem nextRead_zero_p {u ℓ : ℕ} (R : RungPack O K u ℓ) (m : ℕ) :
    nextRead R.C R.P m (0 : Polynomial O) = 0 := by
  refine Polynomial.ext fun J => ?_
  rw [nextRead_coeff, Polynomial.coeff_zero]
  by_cases hgu : u * J ≤ m ∧ ℓ ∣ (m - u * J)
  · rw [wcoeff_of_guard R.C R.P hgu.1 hgu.2, C131w.dev_zero', R.C.read_zero]
  · exact wcoeff_of_not_guard R.C R.P hgu

/-- the next read is additive at a common cleared floor. -/
theorem nextRead_add {u ℓ : ℕ} (R : RungPack O K u ℓ) {m : ℕ} {g z : Polynomial O}
    (hg : (m : ℕ∞) ≤ nextSupp R.C R.P g) (hz : (m : ℕ∞) ≤ nextSupp R.C R.P z) :
    nextRead R.C R.P m (g + z) = nextRead R.C R.P m g + nextRead R.C R.P m z := by
  have hfg : LineFloor R.C R.P m g := (lineFloor_iff_le_nextSupp R.C R.P).mpr hg
  have hfz : LineFloor R.C R.P m z := (lineFloor_iff_le_nextSupp R.C R.P).mpr hz
  refine Polynomial.ext fun J => ?_
  rw [Polynomial.coeff_add, nextRead_coeff, nextRead_coeff, nextRead_coeff]
  by_cases hgu : u * J ≤ m ∧ ℓ ∣ (m - u * J)
  · rw [wcoeff_of_guard R.C R.P hgu.1 hgu.2, wcoeff_of_guard R.C R.P hgu.1 hgu.2,
      wcoeff_of_guard R.C R.P hgu.1 hgu.2, dev_add_of_monic R.P.monic,
      R.C.read_add (grade_floor R.C R.P hfg hgu.2) (grade_floor R.C R.P hfz hgu.2)]
  · rw [wcoeff_of_not_guard R.C R.P hgu, wcoeff_of_not_guard R.C R.P hgu,
      wcoeff_of_not_guard R.C R.P hgu, add_zero]

/-- the next read vanishes strictly below the next support. -/
theorem nextRead_above {u ℓ : ℕ} (R : RungPack O K u ℓ) {m : ℕ} {f : Polynomial O}
    (h : (m : ℕ∞) < nextSupp R.C R.P f) : nextRead R.C R.P m f = 0 := by
  refine Polynomial.ext fun J => ?_
  rw [nextRead_coeff, Polynomial.coeff_zero]
  by_cases hgu : u * J ≤ m ∧ ℓ ∣ (m - u * J)
  · rw [wcoeff_of_guard R.C R.P hgu.1 hgu.2]
    refine R.C.read_above ?_
    have hterm : (m : ℕ∞) < (ℓ : ℕ∞) * R.C.supp (dev R.P.key f J)
        + ((u * J : ℕ) : ℕ∞) := h.trans_le (iInf_le _ J)
    rcases eq_or_ne (R.C.supp (dev R.P.key f J)) ⊤ with hT | hT
    · rw [hT]
      exact ENat.coe_lt_top _
    obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
    rw [← hA] at hterm ⊢
    have hnat : m < ℓ * A + u * J := by exact_mod_cast hterm
    obtain ⟨c, hc⟩ := hgu.2
    have hdiv : (m - u * J) / ℓ = c := by
      rw [hc, Nat.mul_div_cancel_left _ R.P.ell_pos]
    rw [hdiv]
    have hcA : c < A := by
      have h1 : ℓ * c < ℓ * A := by omega
      exact Nat.lt_of_mul_lt_mul_left h1
    exact_mod_cast hcA
  · exact wcoeff_of_not_guard R.C R.P hgu

/-- ★ the next read is multiplicative at exact grades — `wcoeff_mul` coefficientwise,
i.e. the convolution law IS polynomial multiplication of the generating reads. -/
theorem nextRead_mul {u ℓ : ℕ} (R : RungPack O K u ℓ) {m₁ m₂ : ℕ}
    {g z : Polynomial O} (hg : nextSupp R.C R.P g = (m₁ : ℕ∞))
    (hz : nextSupp R.C R.P z = (m₂ : ℕ∞)) :
    nextRead R.C R.P (m₁ + m₂) (g * z)
      = nextRead R.C R.P m₁ g * nextRead R.C R.P m₂ z := by
  have hfg : LineFloor R.C R.P m₁ g :=
    (lineFloor_iff_le_nextSupp R.C R.P).mpr (le_of_eq hg.symm)
  have hfz : LineFloor R.C R.P m₂ z :=
    (lineFloor_iff_le_nextSupp R.C R.P).mpr (le_of_eq hz.symm)
  refine Polynomial.ext fun J => ?_
  rw [nextRead_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [nextRead_coeff]
  exact wcoeff_mul R.C R.P hfg hfz J

/-- ★ the next-support product law (both halves; the ≤ half via `exact_ne` and
no-zero-divisors, the ≥ half via `lineFloor_mul`). -/
theorem nextSupp_mul {u ℓ : ℕ} (R : RungPack O K u ℓ) [NoZeroDivisors K]
    (g z : Polynomial O) :
    nextSupp R.C R.P (g * z) = nextSupp R.C R.P g + nextSupp R.C R.P z := by
  refine le_antisymm ?_ (le_nextSupp_mul R.C R.P g z)
  rcases eq_or_ne (nextSupp R.C R.P g) ⊤ with hgT | hgT
  · rw [hgT, top_add]; exact le_top
  rcases eq_or_ne (nextSupp R.C R.P z) ⊤ with hzT | hzT
  · rw [hzT, add_top]; exact le_top
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 hgT
  obtain ⟨Sz, hSz⟩ := ENat.ne_top_iff_exists.1 hzT
  rw [← hSg, ← hSz, ← Nat.cast_add]
  have hne : nextRead R.C R.P (Sg + Sz) (g * z) ≠ 0 := by
    rw [nextRead_mul R hSg.symm hSz.symm]
    exact mul_ne_zero (nextRead_ne_zero_of_exact R hSg.symm)
      (nextRead_ne_zero_of_exact R hSz.symm)
  obtain ⟨J, hJ⟩ : ∃ J, wcoeff R.C R.P (Sg + Sz) (g * z) J ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Polynomial.ext fun J => by
      rw [nextRead_coeff, hc J, Polynomial.coeff_zero])
  by_cases hgu : u * J ≤ Sg + Sz ∧ ℓ ∣ (Sg + Sz - u * J)
  swap
  · exact absurd (wcoeff_of_not_guard R.C R.P hgu) hJ
  rw [wcoeff_of_guard R.C R.P hgu.1 hgu.2] at hJ
  have hle : R.C.supp (dev R.P.key (g * z) J)
      ≤ (((Sg + Sz - u * J) / ℓ : ℕ) : ℕ∞) := by
    by_contra hlt
    rw [not_le] at hlt
    exact hJ (R.C.read_above hlt)
  refine le_trans (iInf_le _ J) ?_
  obtain ⟨c, hc⟩ := hgu.2
  have hdiv : (Sg + Sz - u * J) / ℓ = c := by
    rw [hc, Nat.mul_div_cancel_left _ R.P.ell_pos]
  rw [hdiv] at hle
  calc (ℓ : ℕ∞) * R.C.supp (dev R.P.key (g * z) J) + ((u * J : ℕ) : ℕ∞)
      ≤ (ℓ : ℕ∞) * ((c : ℕ) : ℕ∞) + ((u * J : ℕ) : ℕ∞) :=
        add_le_add (mul_le_mul' le_rfl hle) le_rfl
    _ = ((ℓ * c + u * J : ℕ) : ℕ∞) := by push_cast; ring
    _ = ((Sg + Sz : ℕ) : ℕ∞) := by
        congr 1
        omega

/-- ★★ **THE ITERATED CARRIER** — unconditional: every rung pack generates the
next-level weighted carrier at the POLYNOMIAL ring over its read target. -/
noncomputable def nextCarrier {u ℓ : ℕ} (R : RungPack O K u ℓ) [NoZeroDivisors K] :
    WeightedCarrier O (Polynomial K) where
  supp := nextSupp R.C R.P
  read := nextRead R.C R.P
  supp_zero := nextSupp_zero_p R
  supp_mul := nextSupp_mul R
  min_supp_le_add := min_nextSupp_le_add R
  read_zero := nextRead_zero_p R
  read_add := fun hg hz => nextRead_add R hg hz
  read_above := fun h => nextRead_above R h
  read_mul := fun h1 h2 => nextRead_mul R h1 h2

/-- ★ **FINDING — the quotient is forced**: the iterated carrier at the bare polynomial
ring admits NO key pack: `supp_key` (exact grade) + the pack's `exact_ne` contradict
`read_key = 0`.  Key lifting therefore MUST pass to a proper quotient of
`Polynomial K` (the next letter's ring) — the structural reason WCC's "iterated
carrier" leg was blocked on key lifting by content. -/
theorem carrierKey_nextCarrier_isEmpty {u ℓ : ℕ} (R : RungPack O K u ℓ)
    [NoZeroDivisors K] (u' ℓ' : ℕ) :
    IsEmpty (CarrierKey (nextCarrier R) u' ℓ') := by
  refine ⟨fun P' => ?_⟩
  exact nextRead_ne_zero_of_exact R P'.supp_key P'.read_key

end NextCarrier

/-! ## §7 — the conditional step and the induction wrapper -/

section Step

variable {K : Type*} [CommRing K]

/-- Any weighted carrier pushes forward along any ring hom (the read laws are
hom-stable; the support is untouched). -/
def pushCarrier (C : WeightedCarrier O K) {K' : Type*} [CommRing K']
    (φ : K →+* K') : WeightedCarrier O K' where
  supp := C.supp
  read m f := φ (C.read m f)
  supp_zero := C.supp_zero
  supp_mul := C.supp_mul
  min_supp_le_add := C.min_supp_le_add
  read_zero := fun m => by rw [C.read_zero, map_zero]
  read_add := fun hg hz => by rw [C.read_add hg hz, map_add]
  read_above := fun h => by rw [C.read_above h, map_zero]
  read_mul := fun h1 h2 => by rw [C.read_mul h1 h2, map_mul]

/-- ★ **The per-rung lift obligation** (the `Rres_exists` genre, with its pinned Lean
shape): a ring hom out of the iterated carrier's polynomial ring (the pass to the next
letter's ring — forced by `carrierKey_nextCarrier_isEmpty`), a key pack THERE (whose
`read_key = 0` is exactly "the next letter is a root of the key's residual
polynomial"), and the pushed exact-grade nonvanishing (FGMN's `graded_scalar_nonzero`
clause at the new rung).  Adjudication (charge 2): this data is NOT a field of the
realization's chain data — `FGMNSourceData/Laws` (C130fg) carry letters, residuals,
`carried_key_residual` (`= 1`, for the CARRIED key) and the `PrevGrade`-fenced
`graded_mul` only — so it is an honest named obligation, not derivable tower structure. -/
structure RungLift {u ℓ : ℕ} (R : RungPack O K u ℓ) [NoZeroDivisors K]
    (K' : Type*) [CommRing K'] (u' ℓ' : ℕ) where
  /-- the pass to the next letter's ring. -/
  φ : Polynomial K →+* K'
  /-- the next key pack at the pushed carrier. -/
  P' : CarrierKey (pushCarrier (nextCarrier R) φ) u' ℓ'
  /-- pushed exact-grade nonvanishing below the next key degree. -/
  exact_ne' : ∀ {m : ℕ} {g : Polynomial O}, g.natDegree < P'.key.natDegree →
    (pushCarrier (nextCarrier R) φ).supp g = (m : ℕ∞) →
    (pushCarrier (nextCarrier R) φ).read m g ≠ 0

/-- ★ **The iteration step**: a rung pack plus its lift is a rung pack one level up. -/
noncomputable def RungLift.pack {u ℓ : ℕ} {R : RungPack O K u ℓ} [NoZeroDivisors K]
    {K' : Type*} [CommRing K'] {u' ℓ' : ℕ} (Λ : RungLift R K' u' ℓ') :
    RungPack O K' u' ℓ' where
  C := pushCarrier (nextCarrier R) Λ.φ
  P := Λ.P'
  exact_ne := fun hdeg hsupp => Λ.exact_ne' hdeg hsupp

end Step

/-! ### the induction wrapper: packs at all rungs from base + step -/

universe v

variable (O) in
/-- A rung pack with its ring and slopes bundled (the recursion motive). -/
structure PackAt where
  /-- the read target ring at this rung. -/
  K : Type v
  /-- its ring structure. -/
  [ring : CommRing K]
  /-- no zero divisors (consumed by the next iteration). -/
  [nzd : NoZeroDivisors K]
  /-- the outer slope numerator. -/
  u : ℕ
  /-- the outer slope denominator. -/
  ℓ : ℕ
  /-- the pack. -/
  pack : RungPack O K u ℓ

attribute [instance] PackAt.ring PackAt.nzd

variable (O) in
/-- A lift of a bundled pack: the next ring, slopes, and the `RungLift` data. -/
structure LiftAt (Q : PackAt.{v} O) where
  /-- the next rung's ring. -/
  K' : Type v
  /-- its ring structure. -/
  [ring' : CommRing K']
  /-- no zero divisors at the next rung. -/
  [nzd' : NoZeroDivisors K']
  /-- the next outer slopes. -/
  u' : ℕ
  /-- the next outer slope denominator. -/
  ℓ' : ℕ
  /-- the per-rung lift obligation. -/
  lift : RungLift Q.pack K' u' ℓ'

attribute [instance] LiftAt.ring' LiftAt.nzd'

/-- the bundled step. -/
noncomputable def LiftAt.next {Q : PackAt.{v} O} (Λ : LiftAt O Q) : PackAt.{v} O :=
  ⟨Λ.K', Λ.u', Λ.ℓ', Λ.lift.pack⟩

/-- ★ **Packs at all rungs from base + step**: the induction wrapper — a base pack and
a per-rung lift supplier generate the full tower of rung packs. -/
noncomputable def towerPacks (Q₀ : PackAt.{v} O)
    (step : ∀ Q : PackAt.{v} O, LiftAt O Q) : ℕ → PackAt.{v} O
  | 0 => Q₀
  | n + 1 => (step (towerPacks Q₀ step n)).next

@[simp] theorem towerPacks_zero (Q₀ : PackAt.{v} O)
    (step : ∀ Q : PackAt.{v} O, LiftAt O Q) : towerPacks Q₀ step 0 = Q₀ := rfl

@[simp] theorem towerPacks_succ (Q₀ : PackAt.{v} O)
    (step : ∀ Q : PackAt.{v} O, LiftAt O Q) (n : ℕ) :
    towerPacks Q₀ step (n + 1) = (step (towerPacks Q₀ step n)).next := rfl

/-- ★ the convolution law fires at EVERY rung of the tower of packs. -/
theorem towerPacks_wcoeff_mul (Q₀ : PackAt.{v} O)
    (step : ∀ Q : PackAt.{v} O, LiftAt O Q) (n : ℕ) {β β' : ℕ}
    {g z : Polynomial O}
    (hg : LineFloor (towerPacks Q₀ step n).pack.C (towerPacks Q₀ step n).pack.P β g)
    (hz : LineFloor (towerPacks Q₀ step n).pack.C (towerPacks Q₀ step n).pack.P β' z)
    (J : ℕ) :
    wcoeff (towerPacks Q₀ step n).pack.C (towerPacks Q₀ step n).pack.P (β + β')
        (g * z) J
      = ∑ j ∈ Finset.range (J + 1),
          wcoeff (towerPacks Q₀ step n).pack.C (towerPacks Q₀ step n).pack.P β g j
            * wcoeff (towerPacks Q₀ step n).pack.C (towerPacks Q₀ step n).pack.P β' z
                (J - j) :=
  wcoeff_mul _ _ hg hz J

end Uniformity.Density.Tower.I10rung

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10rung.rung2Carrier
#print axioms Uniformity.Density.Tower.I10rung.rung2Key
#print axioms Uniformity.Density.Tower.I10rung.rung2Key_nonempty
#print axioms Uniformity.Density.Tower.I10rung.rung2_wcoeff_mul
#print axioms Uniformity.Density.Tower.I10rung.rung2Pack
#print axioms Uniformity.Density.Tower.I10rung.lineFloor_mul
#print axioms Uniformity.Density.Tower.I10rung.nextCarrier
#print axioms Uniformity.Density.Tower.I10rung.carrierKey_nextCarrier_isEmpty
#print axioms Uniformity.Density.Tower.I10rung.RungLift.pack
#print axioms Uniformity.Density.Tower.I10rung.towerPacks
#print axioms Uniformity.Density.Tower.I10rung.towerPacks_wcoeff_mul

end AxCheck
