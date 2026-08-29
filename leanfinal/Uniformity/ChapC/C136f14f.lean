/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136f14e
import Uniformity.ChapC.C134p1
import Uniformity.ChapC.C134frt
import Uniformity.ChapC.C134f12c

/-!
# Uniformity.ChapC.C136f14f — UNIT HCONV: the digit-split convolution supplier
[HCONV 2026-08-29]

The last F1.4/F1.5 leg (F14C §2.1): the `hconv` premise of
`C136f14c.dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution`, PROVED frame-generically.

## The theorem

★★ `dv2FullRead_dev_mul_conv_split` — at every in-range lattice slot `t` of the product
side, the anchored absolute read of the product digit,

`dv2FullRead L (Mgz − t·u₂) (dev Ψ (g·z) (min₂(g·z) + t·ℓ₂))`,

equals the guarded weighted antidiagonal of the factors' anchored coefficients with the
explicit normalizer-cocycle weights `root^{c₁(Mg − t₁·u₂, Mz − (t−t₁)·u₂)}` — byte-shaped
as the assembler's premise, so F14C's weighted convolution law fires generically.

## The proof (the level-2 transcription of C133mh9's level-1 [MH9M] pattern)

Expand `g·z` into the full outer `Ψ`-convolution square (`sum_dev_eq`, as in
`C136l2e2.dv2Line_succ_le_of_no_pair`).  The anchored read is additive over the square at
the slot's value line (`le_line_dev2_term` prices every term at or above the line;
`dv2FullRead_add_of_le` iterated).  Every term that is NOT an exact-slot on-side pair —
off-line main terms AND the entire carry diagonal — prices strictly above the line
(`lt_line_dev2_term`) and its read dies (`dv2FullRead_eq_zero_of_lt`).  The surviving
good pairs are exactly the on-side lattice antidiagonal (the `ℓ₂`-congruence of on-side
abscissae); each one reduces by `dev_mul_pow` to a slot-`0` digit product, is
reduction-absorbed (`C136f14b.dv2FullRead_dev_zero`), and then the landed absolute-read
carry law `C136f14c.dv2FullReadCarryLaw` prices it as
`root^{c₁(ka,kb)} · read(A) · read(B)` — the exact slot weight.  Off-side lattice slots
on the assembler side contribute `0` by the guard
(`dv2ResPolyAnch_coeff_eq_zero_of_not_onSide`), matching the strict kill.

## Fired consequences — the F1.4/F1.5 rows CLOSE

* ★ `dv2ResPolyAnch_mul_eq_weightedConv` — F14C's assembler fired: the anchored carrier
  of a product IS the weighted convolution carrier, frame-generically.
* ★ `dv2ResPolyTw_scalar_of_split_geometry` — A24F's conditional C.39 with the
  proof-bearing `hconv` premise DISCHARGED and the derivable side-geometry legs
  (`hM`, `hdeg`, `hfS`, `hngz`, `hpgz`) derived; remaining premises: the C.36/C.37
  complement-geometry legs (`hsplit`, `hpz`, `hzdeg`, `hγ`) + survival/fences.
* ★★ `dv2ResPolyTw_scalar` — **THE SIGNED C.39** (leanspec post-A-C.24″, conclusion and
  hypothesis block byte-as-is, modulo the standing recorded binder delta `hh : 0 < F.h`
  — the F1.1/F1.2/F1.3/F1.8 precedent).  Every carried leg is DERIVED from the landed
  complement engine: survival from `IsTestKey` + the seam fence
  (`isMuKey_of_isTestKey` + `dvSupp_testKey` + `dv2ResSurv_of_muKey`), the exact split
  from `blockFactor_spec`, the complement point side from P2's `¬ MuDvd` through the
  abscissa-0 collapse, and the complement read through the absorber.
* ★★ `dv2ResPolyTw_radical_eq` — **THE SIGNED C.38** (same convention): the scalar is a
  unit (`γ̂_g ≠ 0` by F1.2's residual clause through the shift identity; `root ≠ 0`),
  so A24C's twisted adapter fires.

Axiom footprint: the supplier and the two generic products are Lean-core; the two
SIGNED rows inherit exactly `Uniformity.Density.Tower.exists_dvDissection` (the C.33
dissection cite) through the landed F1.1 block chain (`C134cfs.blockFactor_spec`) —
the standing footprint of the whole F1 family.

The A24A/L2E4 caution is respected: no UNWEIGHTED law is stated anywhere; every slot
carries its own explicit cocycle weight, and the off-side channel is killed on both
sides (strict pricing on the left, the anchored guard on the right).

No landed or leanspec file is edited; nothing here is S2-special.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136f14f

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0 Uniformity.Density.Tower.C136l2e1
open Uniformity.Density.Tower.C136l2e2 Uniformity.Density.Tower.C136l2e3
open Uniformity.Density.Tower.C136f14b Uniformity.Density.Tower.C136f14c
open Uniformity.Density.Tower.C136f14d Uniformity.Density.Tower.C136f14e

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 0 — private plumbing (the standing local-twin convention) -/

private theorem inner_floor (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  rw [← mul_assoc]
  exact L.hκ

/-- Local twin of C28's private `shift_spec`. -/
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

/-- Local twin of C28's private `shift_unique`. -/
private theorem shift_unique (L : LevelDatum F H₀ hpin) {m b : ℕ}
    (hb : b < L.ℓ) (hcong : b * L.u ≡ m [MOD L.ℓ]) : b = L.shift m := by
  obtain ⟨hlt, hsp⟩ := shift_spec L m
  exact Uniformity.Density.Induction.class_sep L.hcop hb hlt (hcong.trans hsp.symm)

/-- The exact (non-truncated) normalizer-cocycle identity:
`s(a) + s(b) = s(a+b) + ℓ·c₁(a,b)` — the carry premise of the absolute carry law,
supplied at every pair of grades. -/
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

/-- Nonstrict weight-to-height extraction (companion of C130nv2's
`succ_le_of_weight_succ_le`). -/
private theorem le_height_of_weight_le {ℓ u J c : ℕ} (hℓ : 0 < ℓ) {x : ℕ∞}
    (h : ((ℓ * c + u * J : ℕ) : ℕ∞) ≤ ℓ • x + (u * J : ℕ∞)) : ((c : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← ha] at h ⊢
  rw [weight_read] at h
  have hnat : ℓ * c + u * J ≤ ℓ * a + u * J := by exact_mod_cast h
  have hca : c ≤ a := Nat.le_of_mul_le_mul_left (by omega) hℓ
  exact_mod_cast hca

/-- Strict weight-to-height extraction, `<`-form. -/
private theorem lt_height_of_weight_succ_le {ℓ u J c : ℕ} {x : ℕ∞}
    (h : ((ℓ * c + u * J + 1 : ℕ) : ℕ∞) ≤ ℓ • x + (u * J : ℕ∞)) :
    ((c : ℕ) : ℕ∞) < x := by
  have h1 := succ_le_of_weight_succ_le h
  have h2 : ((c : ℕ) : ℕ∞) < ((c : ℕ) : ℕ∞) + 1 := by
    rw [show ((c : ℕ) : ℕ∞) + 1 = ((c + 1 : ℕ) : ℕ∞) by push_cast; rfl]
    exact_mod_cast Nat.lt_succ_self c
  exact lt_of_lt_of_le h2 h1

/-- Local twin of C136f14b's private `dv2OnSide_modEq'`. -/
private theorem dv2OnSide_modEq' (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hcop : Nat.Coprime u₂ ℓ₂) {f : Polynomial O} {j j' : ℕ}
    (hj : Dv2OnSide L Ψ f u₂ ℓ₂ j) (hj' : Dv2OnSide L Ψ f u₂ ℓ₂ j') :
    j ≡ j' [MOD ℓ₂] := by
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hj.2
  obtain ⟨H', hH'⟩ := ENat.ne_top_iff_exists.1 hj'.2
  have hweight : ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)
      = ℓ₂ • dv2Pin L Ψ f j' + (u₂ * j' : ℕ∞) := hj.1.symm.trans hj'.1
  rw [← hH, ← hH', weight_read, weight_read] at hweight
  have key : ℓ₂ * H + u₂ * j = ℓ₂ * H' + u₂ * j' := by exact_mod_cast hweight
  have keyZ : (ℓ₂ : ℤ) * (H : ℤ) + (u₂ : ℤ) * (j : ℤ)
      = (ℓ₂ : ℤ) * (H' : ℤ) + (u₂ : ℤ) * (j' : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key
  have hdvd : (ℓ₂ : ℤ) ∣ (u₂ : ℤ) * ((j' : ℤ) - (j : ℤ)) :=
    ⟨(H : ℤ) - (H' : ℤ), by linarith⟩
  have hcop' : IsCoprime (ℓ₂ : ℤ) (u₂ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact Nat.modEq_iff_dvd.mpr (hcop'.dvd_of_dvd_mul_left hdvd)

/-- Local twin of C136f14b's private `dv2SideSpan_eq'`. -/
private theorem dv2SideSpan_eq' (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
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
    (Nat.modEq_iff_dvd' hle).mp (dv2OnSide_modEq' L hcop hminON hmaxON)
  rw [dv2SideDeg, Nat.mul_div_cancel' hdvd]

/-- Local twin of C136f14b's private `lattice_line_floor`: through the side degree, the
side line stays at nonnegative grades. -/
private theorem lattice_line_floor (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne) :
    t * u₂ ≤ M₂ := by
  have hminON : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hne)
  have hmaxON : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMax L Ψ f u₂ ℓ₂ hne) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.max'_mem _ hne)
  obtain ⟨Hmax, hHmax⟩ := ENat.ne_top_iff_exists.1 hmaxON.2
  have hW1 : dv2Supp L Ψ f u₂ ℓ₂
      = ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne : ℕ) : ℕ∞) := by
    rw [hminON.1, hp₂]
    push_cast [nsmul_eq_mul]
    ring
  have hW2 : dv2Supp L Ψ f u₂ ℓ₂
      = ((ℓ₂ * Hmax + u₂ * dv2SideMax L Ψ f u₂ ℓ₂ hne : ℕ) : ℕ∞) := by
    rw [hmaxON.1, ← hHmax]
    push_cast [nsmul_eq_mul]
    ring
  have hkey : ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne
      = ℓ₂ * Hmax + u₂ * dv2SideMax L Ψ f u₂ ℓ₂ hne := by
    have h := hW1.symm.trans hW2
    exact_mod_cast h
  have hle : dv2SideMin L Ψ f u₂ ℓ₂ hne ≤ dv2SideMax L Ψ f u₂ ℓ₂ hne :=
    Finset.min'_le _ _ (Finset.max'_mem _ hne)
  have hspan : dv2SideMax L Ψ f u₂ ℓ₂ hne
      = dv2SideMin L Ψ f u₂ ℓ₂ hne + ℓ₂ * dv2SideDeg L Ψ f u₂ ℓ₂ hne := by
    have h := dv2SideSpan_eq' L hcop hne
    omega
  rw [hspan] at hkey
  have hexp : u₂ * (dv2SideMin L Ψ f u₂ ℓ₂ hne + ℓ₂ * dv2SideDeg L Ψ f u₂ ℓ₂ hne)
      = u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne
        + ℓ₂ * (dv2SideDeg L Ψ f u₂ ℓ₂ hne * u₂) := by ring
  rw [hexp] at hkey
  have h2 : ℓ₂ * M₂ = ℓ₂ * (Hmax + dv2SideDeg L Ψ f u₂ ℓ₂ hne * u₂) := by
    have h3 : ℓ₂ * (Hmax + dv2SideDeg L Ψ f u₂ ℓ₂ hne * u₂)
        = ℓ₂ * Hmax + ℓ₂ * (dv2SideDeg L Ψ f u₂ ℓ₂ hne * u₂) := by ring
    omega
  have hM := Nat.eq_of_mul_eq_mul_left hℓ₂ h2
  have hmono : t * u₂ ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne * u₂ := Nat.mul_le_mul_right u₂ ht
  omega

/-- An on-side lattice slot lies within the side window: `a ≤ dv2SideDeg`. -/
private theorem lattice_le_sideDeg (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hcop : Nat.Coprime u₂ ℓ₂) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {a : ℕ}
    (hon : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne + a * ℓ₂)) :
    a ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne := by
  have hmem := mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hon
  have hle : dv2SideMin L Ψ f u₂ ℓ₂ hne + a * ℓ₂ ≤ dv2SideMax L Ψ f u₂ ℓ₂ hne :=
    Finset.le_max' _ _ hmem
  have hspan := dv2SideSpan_eq' L hcop hne
  have h1 : ℓ₂ * a ≤ ℓ₂ * dv2SideDeg L Ψ f u₂ ℓ₂ hne := by
    have hcomm : ℓ₂ * a = a * ℓ₂ := Nat.mul_comm _ _
    omega
  exact Nat.le_of_mul_le_mul_left h1 hℓ₂

/-- A polynomial with a nonempty level-2 side is nonzero. -/
private theorem ne_zero_of_dv2SideSet_nonempty (L : LevelDatum F H₀ hpin)
    {Ψ f : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : f ≠ 0 := by
  rintro rfl
  obtain ⟨j, hj⟩ := hne
  refine (dv2OnSide_of_mem_dv2SideSet L hj).2 ?_
  show dv2Hgt L (dev Ψ (0 : Polynomial O) j) = ⊤
  rw [dev_of_zero]
  exact dv2Hgt_zero L

/-- An on-side digit is nonzero. -/
private theorem dev_ne_zero_of_dv2OnSide (L : LevelDatum F H₀ hpin)
    {Ψ f : Polynomial O} {u₂ ℓ₂ j : ℕ}
    (hon : Dv2OnSide L Ψ f u₂ ℓ₂ j) : dev Ψ f j ≠ 0 := by
  intro h0
  refine hon.2 ?_
  show dv2Hgt L (dev Ψ f j) = ⊤
  rw [h0]
  exact dv2Hgt_zero L

/-- Finite-sum floor for `dv2Hgt` (unweighted twin of C136l2e2's private
`le_weight_dv2Hgt_sum`). -/
private theorem le_dv2Hgt_finsetSum (L : LevelDatum F H₀ hpin) {ι : Type*}
    (s : Finset ι) (G : ι → Polynomial O) {k : ℕ}
    (hall : ∀ p ∈ s, (k : ℕ∞) ≤ dv2Hgt L (G p)) :
    (k : ℕ∞) ≤ dv2Hgt L (∑ p ∈ s, G p) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, dv2Hgt_zero]
      exact le_top
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      refine le_trans (le_min (hall a (Finset.mem_cons_self a t))
        (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))) ?_
      exact min_dv2Hgt_le_dv2Hgt_add L _ _

/-- Finite-sum additivity of the anchored absolute read at a common height floor. -/
private theorem dv2FullRead_finsetSum (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {ι : Type*} (s : Finset ι) (G : ι → Polynomial O) {k : ℕ}
    (hall : ∀ p ∈ s, (k : ℕ∞) ≤ dv2Hgt L (G p)) :
    dv2FullRead L k (∑ p ∈ s, G p) = ∑ p ∈ s, dv2FullRead L k (G p) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact dv2FullRead_eq_zero_of_lt L hπ (by
        rw [dv2Hgt_zero]
        exact ENat.coe_lt_top k)
  | cons a t hat ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        dv2FullRead_add_of_le L hπ (hall a (Finset.mem_cons_self a t))
          (le_dv2Hgt_finsetSum L t G fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp))),
        ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp))]

/-! ## Part 1 — the good-pair term -/

/-- **The good-pair evaluation**: at a pair of on-side lattice slots, the slot-`0`
reduced digit-product read at the added exact grades is the cocycle-weighted product of
the two per-slot anchored reads.  The chain: the reduction absorber
(`dv2FullRead_dev_zero`), then the landed absolute carry law (`dv2FullReadCarryLaw`)
with the exact shift identity `s(ka) + s(kb) = s(ka+kb) + ℓ·c₁(ka,kb)`. -/
private theorem good_pair_read (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hΨd : 0 < Ψ.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂)
    {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    {Mg Mz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞))
    {a b : ℕ}
    (hona : Dv2OnSide L Ψ g u₂ ℓ₂ (dv2SideMin L Ψ g u₂ ℓ₂ hng + a * ℓ₂))
    (honb : Dv2OnSide L Ψ z u₂ ℓ₂ (dv2SideMin L Ψ z u₂ ℓ₂ hnz + b * ℓ₂)) :
    dv2FullRead L ((Mg - a * u₂) + (Mz - b * u₂))
        (dev Ψ (dev Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng + a * ℓ₂)
          * dev Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz + b * ℓ₂)) 0)
      = AdjoinRoot.root L.r ^ L.cocycle (Mg - a * u₂) (Mz - b * u₂)
        * (dv2FullRead L (Mg - a * u₂)
            (dev Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng + a * ℓ₂))
          * dv2FullRead L (Mz - b * u₂)
            (dev Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz + b * ℓ₂))) := by
  classical
  have hΨm : Ψ.Monic := hΨ.1
  set A := dev Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng + a * ℓ₂) with hAdef
  set B := dev Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz + b * ℓ₂) with hBdef
  have hA0 : A ≠ 0 := dev_ne_zero_of_dv2OnSide L hona
  have hB0 : B ≠ 0 := dev_ne_zero_of_dv2OnSide L honb
  obtain ⟨hau, hpina⟩ := dv2Pin_lattice_of_onSide L hℓ₂ hng hpg hona
  obtain ⟨hbu, hpinb⟩ := dv2Pin_lattice_of_onSide L hℓ₂ hnz hpz honb
  have hka : dv2Hgt L A = ((Mg - a * u₂ : ℕ) : ℕ∞) := hpina
  have hkb : dv2Hgt L B = ((Mz - b * u₂ : ℕ) : ℕ∞) := hpinb
  have hAdeg : A.natDegree < Ψ.natDegree :=
    natDegree_lt_natDegree hA0 (degree_dev_lt hΨm hΨd g _)
  have hBdeg : B.natDegree < Ψ.natDegree :=
    natDegree_lt_natDegree hB0 (degree_dev_lt hΨm hΨd z _)
  -- the product's exact inner height
  have hAB : dv2Hgt L (A * B) = (((Mg - a * u₂) + (Mz - b * u₂) : ℕ) : ℕ∞) := by
    change dvSupp F (A * B) L.u L.ℓ = _
    change dvSupp F A L.u L.ℓ = _ at hka
    change dvSupp F B L.u L.ℓ = _ at hkb
    rw [C133mh3.dvSupp_mul hπ hh H₀ hpin L.hℓ (inner_floor L) hA0 hB0, hka, hkb,
      ← Nat.cast_add]
  -- the reduced slot-0 digit has the same exact height
  have hdev0 : dv2Hgt L (dev Ψ (A * B) 0)
      = (((Mg - a * u₂) + (Mz - b * u₂) : ℕ) : ℕ∞) := (hSurv hAdeg hBdeg hka hkb).1
  -- the reduction absorber
  have habs : dv2FullRead L ((Mg - a * u₂) + (Mz - b * u₂)) (dev Ψ (A * B) 0)
      = dv2FullRead L ((Mg - a * u₂) + (Mz - b * u₂)) (A * B) := by
    refine dv2FullRead_dev_zero L hπ hh hΨ (A * B) (le_of_eq hAB.symm) ?_
    rcases eq_or_ne ((A * B) /ₘ Ψ) 0 with hq0 | hq0
    · rw [hq0, mul_zero, dv2Hgt_zero]
      exact le_top
    · have hdiv : (A * B) %ₘ Ψ + Ψ * ((A * B) /ₘ Ψ) = A * B :=
        Polynomial.modByMonic_add_div (A * B) Ψ
      have hqid : Ψ * ((A * B) /ₘ Ψ) = A * B + -((A * B) %ₘ Ψ) := by
        rw [← sub_eq_add_neg, eq_sub_iff_add_eq, add_comm]
        exact hdiv
      rw [hqid]
      refine le_trans (le_min (le_of_eq hAB.symm) ?_)
        (min_dv2Hgt_le_dv2Hgt_add L (A * B) (-((A * B) %ₘ Ψ)))
      show (((Mg - a * u₂) + (Mz - b * u₂) : ℕ) : ℕ∞)
        ≤ dvSupp F (-((A * B) %ₘ Ψ)) L.u L.ℓ
      rw [dvSupp_neg, show (A * B) %ₘ Ψ = dev Ψ (A * B) 0 from
        (dev_zero_pin Ψ (A * B)).symm]
      exact le_of_eq hdev0.symm
  -- the landed absolute carry law with the exact cocycle carry
  have hcarry := dv2FullReadCarryLaw (O := O) π F hπ hh H₀ hpin L A B
    (Mg - a * u₂) (Mz - b * u₂) (L.cocycle (Mg - a * u₂) (Mz - b * u₂))
    (le_of_eq hka.symm) (le_of_eq hkb.symm)
    (shift_add_exact L (Mg - a * u₂) (Mz - b * u₂))
  rw [habs]
  exact hcarry

/-! ## Part 2 — ★★ the digit-split convolution supplier -/

/-- ★★ **UNIT HCONV — the digit-split convolution supplier** (F14C §2.1, proved).
Byte-shaped as the `hconv` premise of
`C136f14c.dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution`: for every in-range
lattice slot `t` of the product side, the anchored absolute read of the product digit
equals the guarded weighted antidiagonal of the factors' anchored coefficients, with the
explicit per-slot normalizer-cocycle weights. -/
theorem dv2FullRead_dev_mul_conv_split (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hΨd : 0 < Ψ.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty)
    {Mg Mz Mgz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞))
    (hpgz : dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz) = (Mgz : ℕ∞)) :
    ∀ t, t ≤ dv2SideDeg L Ψ (g * z) u₂ ℓ₂ hngz →
      dv2FullRead L (Mgz - t * u₂)
          (dev Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz + t * ℓ₂)) =
        ∑ t₁ ∈ Finset.range (t + 1),
          if t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng ∧
              t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz then
            AdjoinRoot.root L.r ^
                L.cocycle (Mg - t₁ * u₂) (Mz - (t - t₁) * u₂) *
              ((dv2ResPolyAnch L Ψ g u₂ ℓ₂ hng Mg hpg).coeff t₁ *
                (dv2ResPolyAnch L Ψ z u₂ ℓ₂ hnz Mz hpz).coeff (t - t₁))
          else 0 := by
  classical
  intro t ht
  have hΨm : Ψ.Monic := hΨ.1
  have hg : g ≠ 0 := ne_zero_of_dv2SideSet_nonempty L hng
  have hz : z ≠ 0 := ne_zero_of_dv2SideSet_nonempty L hnz
  set J := dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz + t * ℓ₂ with hJdef
  -- the product side geometry
  have hminmul : dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz
      = dv2SideMin L Ψ g u₂ ℓ₂ hng + dv2SideMin L Ψ z u₂ ℓ₂ hnz :=
    dv2SideMin_mul L hΨm hΨd hℓ₂ hSurv hg hz hng hnz hngz
  have hpinmul : dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz)
      = ((Mg + Mz : ℕ) : ℕ∞) :=
    dv2Pin_dv2SideMin_mul L hΨm hΨd hℓ₂ hSurv hg hz hng hnz hngz hpg hpz
  have hMgz : Mgz = Mg + Mz := by
    have h := hpgz.symm.trans hpinmul
    exact_mod_cast h
  have hfloor_t : t * u₂ ≤ Mgz := lattice_line_floor L hℓ₂ hcop hngz hpgz ht
  -- the factor support values
  have hSg : dv2Supp L Ψ g u₂ ℓ₂
      = ((ℓ₂ * Mg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hpg (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng)
  have hSz : dv2Supp L Ψ z u₂ ℓ₂
      = ((ℓ₂ * Mz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz : ℕ) : ℕ∞) :=
    dv2Supp_eq_of_dv2OnSide L hpz (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz)
  -- the value line at slot t
  have hline : ℓ₂ * Mg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
        + (ℓ₂ * Mz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz)
      = ℓ₂ * (Mgz - t * u₂) + u₂ * J := by
    have e1 : u₂ * J
        = u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz
          + ℓ₂ * (t * u₂) := by
      rw [hJdef, hminmul]
      ring
    have e2 : ℓ₂ * (Mgz - t * u₂) = ℓ₂ * Mgz - ℓ₂ * (t * u₂) :=
      Nat.mul_sub_left_distrib ℓ₂ Mgz (t * u₂)
    have e3 : ℓ₂ * Mgz = ℓ₂ * Mg + ℓ₂ * Mz := by
      rw [hMgz]
      ring
    have e4 : ℓ₂ * (t * u₂) ≤ ℓ₂ * Mgz := Nat.mul_le_mul le_rfl hfloor_t
    omega
  -- the convolution square
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
  set S := Finset.range N ×ˢ Finset.range N with hSdef
  have hdev : dev Ψ (g * z) J
      = ∑ p ∈ S, dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) J := by
    conv_lhs => rw [hrep]
    exact dev_finsetSum hΨm _ _ J
  -- every convolution term prices at or above the slot's value line
  have hall : ∀ p ∈ S,
      ((Mgz - t * u₂ : ℕ) : ℕ∞) ≤ dv2Hgt L
        (dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) J) := by
    intro p _
    have h := le_line_dev2_term L hΨm hΨd hℓ₂ hSurv hSg hSz J p.1 p.2
    rw [show ℓ₂ * Mg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
        + (ℓ₂ * Mz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz)
        = ℓ₂ * (Mgz - t * u₂) + u₂ * J from hline] at h
    exact le_height_of_weight_le hℓ₂ h
  rw [hdev, dv2FullRead_finsetSum L hπ S _ hall]
  -- the strict kill of every non-good term
  have hbad_zero : ∀ p ∈ S,
      ¬ (p.1 + p.2 = J ∧ Dv2OnSide L Ψ g u₂ ℓ₂ p.1 ∧ Dv2OnSide L Ψ z u₂ ℓ₂ p.2) →
      dv2FullRead L (Mgz - t * u₂)
        (dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) J) = 0 := by
    intro p _ hbad
    refine dv2FullRead_eq_zero_of_lt L hπ ?_
    have h := lt_line_dev2_term L hΨm hΨd hℓ₂ hSurv hSg hSz
      (J := J) (j := p.1) (i := p.2) hbad
    rw [show ℓ₂ * Mg + u₂ * dv2SideMin L Ψ g u₂ ℓ₂ hng
        + (ℓ₂ * Mz + u₂ * dv2SideMin L Ψ z u₂ ℓ₂ hnz) + 1
        = ℓ₂ * (Mgz - t * u₂) + u₂ * J + 1 from by rw [hline]] at h
    exact lt_height_of_weight_succ_le h
  rw [← Finset.sum_filter_add_sum_filter_not S
    (fun p => p.1 + p.2 = J ∧ Dv2OnSide L Ψ g u₂ ℓ₂ p.1 ∧ Dv2OnSide L Ψ z u₂ ℓ₂ p.2)
    (fun p => dv2FullRead L (Mgz - t * u₂)
      (dev Ψ (dev Ψ g p.1 * dev Ψ z p.2 * Ψ ^ (p.1 + p.2)) J)),
    Finset.sum_eq_zero (fun p hp =>
      hbad_zero p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2),
    add_zero]
  -- the good set is the on-side lattice antidiagonal
  have himg : S.filter (fun p => p.1 + p.2 = J ∧ Dv2OnSide L Ψ g u₂ ℓ₂ p.1
        ∧ Dv2OnSide L Ψ z u₂ ℓ₂ p.2)
      = ((Finset.range (t + 1)).filter (fun t₁ =>
          Dv2OnSide L Ψ g u₂ ℓ₂ (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)
          ∧ Dv2OnSide L Ψ z u₂ ℓ₂
            (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂))).image
        (fun t₁ => (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂,
          dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpS, hsum, hON1, hON2⟩ := Finset.mem_filter.mp hp
      have hminle1 : dv2SideMin L Ψ g u₂ ℓ₂ hng ≤ p.1 :=
        dv2SideMin_le_of_dv2OnSide L hΨm hΨd hng hON1
      have hminle2 : dv2SideMin L Ψ z u₂ ℓ₂ hnz ≤ p.2 :=
        dv2SideMin_le_of_dv2OnSide L hΨm hΨd hnz hON2
      obtain ⟨a, hadef⟩ := (Nat.modEq_iff_dvd' hminle1).mp
        (dv2OnSide_modEq' L hcop (dv2OnSide_dv2SideMin L g u₂ ℓ₂ hng) hON1)
      obtain ⟨b, hbdef⟩ := (Nat.modEq_iff_dvd' hminle2).mp
        (dv2OnSide_modEq' L hcop (dv2OnSide_dv2SideMin L z u₂ ℓ₂ hnz) hON2)
      have hp1eq : p.1 = dv2SideMin L Ψ g u₂ ℓ₂ hng + a * ℓ₂ := by
        have hcomm : ℓ₂ * a = a * ℓ₂ := Nat.mul_comm _ _
        omega
      have hp2eq : p.2 = dv2SideMin L Ψ z u₂ ℓ₂ hnz + b * ℓ₂ := by
        have hcomm : ℓ₂ * b = b * ℓ₂ := Nat.mul_comm _ _
        omega
      have hsum' : p.1 + p.2 = dv2SideMin L Ψ g u₂ ℓ₂ hng
          + dv2SideMin L Ψ z u₂ ℓ₂ hnz + t * ℓ₂ := by
        rw [hsum, hJdef, hminmul]
      have hab : a + b = t := by
        have h1 : (a + b) * ℓ₂ = t * ℓ₂ := by
          have e3 : (a + b) * ℓ₂ = a * ℓ₂ + b * ℓ₂ := Nat.add_mul a b ℓ₂
          omega
        exact Nat.eq_of_mul_eq_mul_right hℓ₂ h1
      refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩, ?_⟩
      · rw [← hp1eq]
        exact hON1
      · rw [show t - a = b from by omega, ← hp2eq]
        exact hON2
      · rw [show t - a = b from by omega]
        exact (Prod.ext_iff.mpr ⟨hp1eq.symm, hp2eq.symm⟩)
    · intro hp
      obtain ⟨t₁, ht₁, hpe⟩ := Finset.mem_image.mp hp
      obtain ⟨ht₁r, hON1, hON2⟩ := Finset.mem_filter.mp ht₁
      have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁r)
      subst hpe
      have h1 : dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂ ≤ g.natDegree := by
        have hm := mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hON1
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
      have h2 : dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂ ≤ z.natDegree := by
        have hm := mem_dv2SideSet_of_dv2OnSide L hΨm hΨd hON2
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_, hON1, hON2⟩
      show dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂
        + (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂) = J
      rw [hJdef, hminmul]
      have e3 : t₁ * ℓ₂ + (t - t₁) * ℓ₂ = t * ℓ₂ := by
        rw [← Nat.add_mul]
        congr 1
        omega
      omega
  rw [himg, Finset.sum_image (fun a₁ h₁ a₂ h₂ hab => by
    rw [Prod.mk.injEq] at hab
    have h1 := hab.1
    have e1 : a₁ * ℓ₂ = a₂ * ℓ₂ := by omega
    exact Nat.eq_of_mul_eq_mul_right hℓ₂ e1)]
  -- evaluate the good terms and extend by the guard zeros
  refine Eq.trans (Finset.sum_congr rfl fun t₁ ht₁ => ?_)
    (Finset.sum_subset (Finset.filter_subset _ _) fun t₁ ht₁r ht₁f => ?_)
  · -- the good term
    obtain ⟨ht₁r, hON1, hON2⟩ := Finset.mem_filter.mp ht₁
    have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁r)
    have hJt : (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)
        + (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂) = J := by
      rw [hJdef, hminmul]
      have e3 : t₁ * ℓ₂ + (t - t₁) * ℓ₂ = t * ℓ₂ := by
        rw [← Nat.add_mul]
        congr 1
        omega
      omega
    have ha' : t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng :=
      lattice_le_sideDeg L hΨm hΨd hℓ₂ hcop hng hON1
    have hb' : t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz :=
      lattice_le_sideDeg L hΨm hΨd hℓ₂ hcop hnz hON2
    obtain ⟨hau, -⟩ := dv2Pin_lattice_of_onSide L hℓ₂ hng hpg hON1
    obtain ⟨hbu, -⟩ := dv2Pin_lattice_of_onSide L hℓ₂ hnz hpz hON2
    have hk : Mgz - t * u₂ = (Mg - t₁ * u₂) + (Mz - (t - t₁) * u₂) := by
      have e1 : t * u₂ = t₁ * u₂ + (t - t₁) * u₂ := by
        rw [← Nat.add_mul]
        congr 1
        omega
      omega
    show dv2FullRead L (Mgz - t * u₂)
        (dev Ψ (dev Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)
          * dev Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂)
          * Ψ ^ ((dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)
            + (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂))) J) = _
    rw [hJt]
    have hdmp := dev_mul_pow hΨm J
      (dev Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)
        * dev Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂)) 0
    rw [Nat.add_zero] at hdmp
    rw [hdmp, hk, if_pos ⟨ha', hb'⟩,
      dv2ResPolyAnch_coeff_of_le L hng hpg ha',
      dv2ResPolyAnch_coeff_of_le L hnz hpz hb']
    exact good_pair_read L hπ hh hΨ hΨd hℓ₂ hSurv hng hnz hpg hpz hON1 hON2
  · -- the guard zeros off the on-side lattice
    have hnot : ¬ (Dv2OnSide L Ψ g u₂ ℓ₂ (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)
        ∧ Dv2OnSide L Ψ z u₂ ℓ₂ (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂)) := by
      intro hcon
      exact ht₁f (Finset.mem_filter.mpr ⟨ht₁r, hcon⟩)
    by_cases hguard : t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng
        ∧ t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz
    · rw [if_pos hguard]
      rcases not_and_or.mp hnot with hoff | hoff
      · rw [dv2ResPolyAnch_coeff_eq_zero_of_not_onSide L hπ hΨm hΨd hℓ₂ hcop hng hpg
          hguard.1 hoff, zero_mul, mul_zero]
      · rw [dv2ResPolyAnch_coeff_eq_zero_of_not_onSide L hπ hΨm hΨd hℓ₂ hcop hnz hpz
          hguard.2 hoff, mul_zero, mul_zero]
    · rw [if_neg hguard]

/-! ## Part 3 — ★ the fired consequences -/

/-- ★ **F14C's assembler fired, frame-generically**: the anchored carrier of a product
IS the honest weighted convolution carrier. -/
theorem dv2ResPolyAnch_mul_eq_weightedConv (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂) {g z : Polynomial O}
    (hng : (dv2SideSet L Ψ g u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ z u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (g * z) u₂ ℓ₂).Nonempty)
    {Mg Mz Mgz : ℕ}
    (hpg : dv2Pin L Ψ g (dv2SideMin L Ψ g u₂ ℓ₂ hng) = (Mg : ℕ∞))
    (hpz : dv2Pin L Ψ z (dv2SideMin L Ψ z u₂ ℓ₂ hnz) = (Mz : ℕ∞))
    (hpgz : dv2Pin L Ψ (g * z) (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz) = (Mgz : ℕ∞)) :
    dv2ResPolyAnch L Ψ (g * z) u₂ ℓ₂ hngz Mgz hpgz
      = dv2ResPolyAnchWeightedConv L Ψ g z u₂ ℓ₂ hng hnz Mg Mz hpg hpz := by
  have hg : g ≠ 0 := ne_zero_of_dv2SideSet_nonempty L hng
  have hz : z ≠ 0 := ne_zero_of_dv2SideSet_nonempty L hnz
  exact dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution L hng hnz hngz hpg hpz hpgz
    (dv2SideDeg_mul L hΨ.1 hΨd hℓ₂ hcop hSurv hg hz hng hnz hngz)
    (dv2FullRead_dev_mul_conv_split L hπ hh hΨ hΨd hℓ₂ hcop hSurv hng hnz hngz
      hpg hpz hpgz)

/-- ★ **The A24F conditional C.39 with the proof-bearing premise DISCHARGED and the
derivable side-geometry legs derived.**  The remaining premises are exactly the
C.36/C.37 complement-geometry legs (`hsplit`, `hpz`, `hzdeg`, `hγ`) plus the standing
survival/fence hypotheses; `hconv` (F14C §2.1), `hngz`, `hpgz`, `hM`, `hdeg`, and `hfS`
are supplied from the theorems above. -/
theorem dv2ResPolyTw_scalar_of_split_geometry (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ f : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hSurv : Dv2ResSurv L Ψ u₂ ℓ₂)
    (hsplit : blockFactor L f * (f /ₘ blockFactor L f) = f)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
        (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞))
    (hpz : dv2Pin L Ψ (f /ₘ blockFactor L f)
        (dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz)
        = ((complementConst L f : ℕ) : ℕ∞))
    (hzdeg : dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz = 0)
    (hγ : dv2FullRead L (complementConst L f)
        (dev Ψ (f /ₘ blockFactor L f)
          (dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz))
        = γgAnch L f) :
    dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = Polynomial.C (γgAnch L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
                (complementConst L f)))
          * dv2ResPolyTw L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂' := by
  have hΨm : Ψ.Monic := hΨ.1
  have hgB : blockFactor L f ≠ 0 := ne_zero_of_dv2SideSet_nonempty L hne'
  have hzC : f /ₘ blockFactor L f ≠ 0 := ne_zero_of_dv2SideSet_nonempty L hnz
  -- transport the product side data along the exact split
  have hngz : (dv2SideSet L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂).Nonempty := by
    rw [hsplit]
    exact hne
  have hpgz : dv2Pin L Ψ (blockFactor L f * (f /ₘ blockFactor L f))
      (dv2SideMin L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz)
      = (M₂ : ℕ∞) :=
    (dv2Pin_sideMin_congr L hsplit hngz hne).trans hp₂
  -- the derivable side-geometry legs
  have hM : M₂ = M₂' + complementConst L f := by
    have h := hpgz.symm.trans
      (dv2Pin_dv2SideMin_mul L hΨm hΨd hℓ₂ hSurv hgB hzC hne' hnz hngz hp₂' hpz)
    exact_mod_cast h
  have hdeg : dv2SideDeg L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz
      = dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne'
        + dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz :=
    dv2SideDeg_mul L hΨm hΨd hℓ₂ hcop hSurv hgB hzC hne' hnz hngz
  have hfS : dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne' * u₂ ≤ M₂' :=
    lattice_line_floor L hℓ₂ hcop hne' hp₂' le_rfl
  -- fire the A24F conditional with the supplier
  exact dv2ResPolyTw_scalar_of_conv_split L hsplit hne hne' hnz hngz hp₂ hp₂' hpz hpgz
    hM hdeg hzdeg hfS hγ
    (dv2FullRead_dev_mul_conv_split L hπ hh hΨ hΨd hℓ₂ hcop hSurv hne' hnz hngz
      hp₂' hpz hpgz)

/-! ## Part 4 — the complement point-side package (C.36-genre, from the landed
`¬ MuDvd` complement engine) -/

/-- At a not-μ-divisible polynomial, EVERY level-2 on-side abscissa is `0`: the level-2
side collapses to a point (the strict outer fence beats the digit floor at every
positive abscissa). -/
private theorem onSide_eq_zero_of_not_muDvd (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ : Polynomial O} (hkey : IsMuKey L Ψ)
    {KΨ : ℕ} (hKΨ : dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞)) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hfence : ℓ₂ * KΨ < u₂) {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g)
    {j : ℕ} (hj : Dv2OnSide L Ψ g u₂ ℓ₂ j) : j = 0 := by
  by_contra hj0
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hg0 : g ≠ 0 := fun h0 => hnd (by rw [h0]; exact muDvd_zero L)
  have hSg' : dvSupp F g L.u L.ℓ ≠ ⊤ := dvSupp_ne_top_of_ne_zero F L.u L.ℓ hg0
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 hSg'
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hj.2
  have hcoll := dv2Supp_collapse_of_not_muDvd L hπ hh hkey hKΨ hℓ₂ hfence hnd
  have hSg'' : dvSupp F g L.u L.ℓ = ((Sg : ℕ) : ℕ∞) := hSg.symm
  have hline : ℓ₂ * Sg = ℓ₂ * Hj + u₂ * j := by
    have h := hcoll.symm.trans hj.1
    rw [hSg'', ← hHj, weight_read] at h
    have hL : ℓ₂ • ((Sg : ℕ) : ℕ∞) = ((ℓ₂ * Sg : ℕ) : ℕ∞) := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [hL] at h
    exact_mod_cast h
  have hfloor := dvSupp_le_dev_add L hπ hh hkey hKΨ g j
  have hpinj : dvSupp F (dev Ψ g j) L.u L.ℓ = ((Hj : ℕ) : ℕ∞) := hHj.symm
  rw [hSg'', hpinj] at hfloor
  have hnat : Sg ≤ Hj + j * KΨ := by exact_mod_cast hfloor
  have h4 : ℓ₂ * Sg ≤ ℓ₂ * (Hj + j * KΨ) := Nat.mul_le_mul le_rfl hnat
  have e1 : ℓ₂ * (Hj + j * KΨ) = ℓ₂ * Hj + ℓ₂ * KΨ * j := by ring
  have e3 : ℓ₂ * KΨ * j < u₂ * j := mul_lt_mul_of_pos_right hfence hjpos
  omega

/-- The anchored read of a not-μ-divisible polynomial looks through its `Ψ`-digit
reduction at its exact level height (the complement instance of the §5-risk absorber:
`dvSupp_modByKey_eq_of_not_muDvd` supplies the remainder floor in place of survival). -/
private theorem read_dev_zero_of_not_muDvd (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hkey : IsMuKey L Ψ) {g : Polynomial O} (hnd : ¬ MuDvd L Ψ g) {c : ℕ}
    (hc : dv2Hgt L g = (c : ℕ∞)) :
    dv2FullRead L c (dev Ψ g 0) = dv2FullRead L c g := by
  refine dv2FullRead_dev_zero L hπ hh hΨ g (le_of_eq hc.symm) ?_
  rcases eq_or_ne (g /ₘ Ψ) 0 with hq0 | hq0
  · rw [hq0, mul_zero, dv2Hgt_zero]
    exact le_top
  · have hdiv : g %ₘ Ψ + Ψ * (g /ₘ Ψ) = g := Polynomial.modByMonic_add_div g Ψ
    have hqid : Ψ * (g /ₘ Ψ) = g + -(g %ₘ Ψ) := by
      rw [← sub_eq_add_neg, eq_sub_iff_add_eq, add_comm]
      exact hdiv
    rw [hqid]
    refine le_trans (le_min (le_of_eq hc.symm) ?_)
      (min_dv2Hgt_le_dv2Hgt_add L g (-(g %ₘ Ψ)))
    show (c : ℕ∞) ≤ dvSupp F (-(g %ₘ Ψ)) L.u L.ℓ
    rw [dvSupp_neg, dvSupp_modByKey_eq_of_not_muDvd L hkey hnd]
    exact le_of_eq hc.symm

/-! ## Part 5 — the complement scalar is a unit (F1.2's residual leg through the shifted
full read) -/

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

private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1
    (dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

/-- Local twin of C136f14d's private `root_ne_zero`. -/
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

/-- ★ **The complement's anchored read is nonzero** — F1.2's residual-nondivisibility
clause (`C134f12c.quotient_residual_notdvd`) through the shift identity
`dv2FullReadPoly_eq_shift`: neither the level residual nor the anchor power `X^δ` is
divisible by `L.r`. -/
private theorem γgAnch_ne_zero (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    γgAnch L f ≠ 0 := by
  classical
  have hg0 : f /ₘ blockFactor L f ≠ 0 := by
    intro h0
    apply C134frt.quotient_dvSupp_ne_top L hπ hh hctx
    rw [h0]
    exact C130s6.dvSupp_zero_eq_top F L.u L.hℓ
  have hne : (dvSideSet F (f /ₘ blockFactor L f) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hg0 L.u L.hℓ
  obtain ⟨M, hp⟩ := exists_pin F hne
  have hgt : dv2Hgt L (f /ₘ blockFactor L f) = ((complementConst L f : ℕ) : ℕ∞) := by
    show dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ = _
    exact (ENat.coe_toNat (C134frt.quotient_dvSupp_ne_top L hπ hh hctx)).symm
  have hshift := dv2FullReadPoly_eq_shift L hπ hgt hne hp
  show dv2FullRead L (complementConst L f) (f /ₘ blockFactor L f) ≠ 0
  rw [dv2FullRead, hshift]
  intro hzero
  have hdvd : L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f) L.u L.ℓ hne M hp
      * Polynomial.X ^ ((dvSideMin F (f /ₘ blockFactor L f) L.u L.ℓ hne
        - L.shift (complementConst L f)) / L.ℓ) :=
    AdjoinRoot.mk_eq_zero.mp hzero
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hprime : Prime L.r := UniqueFactorizationMonoid.irreducible_iff_prime.mp L.hrirr
  rcases hprime.2.2 _ _ hdvd with h | h
  · exact (C134f12c.quotient_residual_notdvd L hπ hh hctx hne M hp) h
  · have hX : L.r ∣ Polynomial.X := hprime.dvd_of_dvd_pow h
    obtain ⟨c, hc⟩ := hX
    rcases (Polynomial.irreducible_X (R := F.stageField H₀ hpin)).isUnit_or_isUnit hc
      with hup | huc
    · exact L.hrirr.1 hup
    · obtain ⟨r', hr', hcr⟩ := Polynomial.isUnit_iff.mp huc
      apply L.hr0
      have hcoeff : (Polynomial.X : Polynomial (F.stageField H₀ hpin)).coeff 0
          = L.r.coeff 0 * r' := by
        rw [hc, ← hcr, Polynomial.coeff_mul_C]
      rw [Polynomial.coeff_X_zero] at hcoeff
      rcases mul_eq_zero.mp hcoeff.symm with h0 | h0
      · exact h0
      · exact absurd h0 hr'.ne_zero

/-! ## Part 6 — ★★ the SIGNED C.39 and C.38 rows (byte-as-is from leanspec post-A-C.24″,
modulo the standing recorded binder delta `hh : 0 < F.h` — the F1.1/F1.2/F1.3/F1.8
precedent, `C134cfs.lean`/`C134f12c.lean`/`C134f13a.lean` headers) -/

set_option linter.unusedVariables false in
/-- ★★ **THE SIGNED C.39 `dv2ResPolyTw_scalar`** (leanspec `ChapC.lean` NODE C.39,
conclusion byte-as-is; the one binder delta beyond the signed list is `hh : 0 < F.h`,
per the standing F1-family convention).  EFF.HE6R1.39's display over the twisted
carrier: ONE constant per side, the PIN-HEIGHT exponent, the scalar
`γ̂_g · root^{c₁(pinHeight, c_g)}` byte-kept from the source.  All previously carried
legs are DERIVED: the digit-split convolution supplier is Part 2's theorem; the
survival package comes from `IsTestKey` + the seam fence; the complement point-side
geometry comes from P2's `¬ MuDvd` through the abscissa-0 collapse.  `hnd` is carried
byte-as-is but unused, exactly as in the landed C.37 (`C134f13a.dv2Supp_translation`):
the complement engine proves its clauses unconditionally, so the proof is strictly
stronger than the signed statement requires. -/
theorem dv2ResPolyTw_scalar (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hh : 0 < F.h)
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
        (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞)) :
    dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = Polynomial.C (γgAnch L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
                (complementConst L f)))
          * dv2ResPolyTw L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂' := by
  have hΨm : Ψ.Monic := hΨ.1
  have hΨd : 0 < Ψ.natDegree := by
    rw [hΨ.2.1]
    show 0 < F.e₁ * F.f₁ * L.ℓ * L.r.natDegree
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos F.he₁ F.hf₁) L.hℓ) L.hrdeg
  have hkeyμ : IsMuKey L Ψ := C134p1d.isMuKey_of_isTestKey L hπ hh hΨ
  have hKΨ : dvSupp F Ψ L.u L.ℓ = ((L.ℓ * L.seam : ℕ) : ℕ∞) :=
    C134f13a.dvSupp_testKey L hΨ
  have hSurv : Dv2ResSurv L Ψ u₂ ℓ₂ := dv2ResSurv_of_muKey L hπ hh hkeyμ hKΨ hℓ₂ hseam
  have hcomp : ¬ MuDvd L Ψ (f /ₘ blockFactor L f) :=
    C134p1.block_complement_not_muDvd L hπ hh hΨ hctx
  have hg0 : f /ₘ blockFactor L f ≠ 0 := by
    intro h0
    apply C134frt.quotient_dvSupp_ne_top L hπ hh hctx
    rw [h0]
    exact C130s6.dvSupp_zero_eq_top F L.u L.hℓ
  have hsplit : blockFactor L f * (f /ₘ blockFactor L f) = f := by
    have hmon : (blockFactor L f).Monic := (C134cfs.hasLabel_blockFactor L hπ hh hctx).1
    have hmod : f %ₘ blockFactor L f = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hmon).mpr (C134cfs.blockFactor_dvd L hπ hh hctx)
    have hdiv := Polynomial.modByMonic_add_div f (blockFactor L f)
    rw [hmod, zero_add] at hdiv
    exact hdiv
  have hnz : (dv2SideSet L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂).Nonempty :=
    dv2SideSet_nonempty_of_ne_zero L hΨm hΨd hℓ₂ hg0
  have hgtc : dv2Hgt L (f /ₘ blockFactor L f) = ((complementConst L f : ℕ) : ℕ∞) := by
    show dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ = _
    exact (ENat.coe_toNat (C134frt.quotient_dvSupp_ne_top L hπ hh hctx)).symm
  have hmin0 : dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz = 0 :=
    onSide_eq_zero_of_not_muDvd L hπ hh hkeyμ hKΨ hℓ₂ hseam hcomp
      (dv2OnSide_dv2SideMin L (f /ₘ blockFactor L f) u₂ ℓ₂ hnz)
  have hpz : dv2Pin L Ψ (f /ₘ blockFactor L f)
      (dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz)
      = ((complementConst L f : ℕ) : ℕ∞) := by
    rw [hmin0]
    show dv2Hgt L (dev Ψ (f /ₘ blockFactor L f) 0) = _
    show dvSupp F (dev Ψ (f /ₘ blockFactor L f) 0) L.u L.ℓ = _
    rw [dev_zero_pin, dvSupp_modByKey_eq_of_not_muDvd L hkeyμ hcomp]
    exact (ENat.coe_toNat (C134frt.quotient_dvSupp_ne_top L hπ hh hctx)).symm
  have hzdeg : dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz = 0 := by
    have hmax0 : dv2SideMax L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz = 0 :=
      onSide_eq_zero_of_not_muDvd L hπ hh hkeyμ hKΨ hℓ₂ hseam hcomp
        (dv2OnSide_of_mem_dv2SideSet L (Finset.max'_mem _ hnz))
    show (dv2SideMax L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz
      - dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz) / ℓ₂ = 0
    rw [hmax0, hmin0]
    simp
  have hγ : dv2FullRead L (complementConst L f)
      (dev Ψ (f /ₘ blockFactor L f)
        (dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz)) = γgAnch L f := by
    rw [hmin0]
    exact read_dev_zero_of_not_muDvd L hπ hh hΨ hkeyμ hcomp hgtc
  exact dv2ResPolyTw_scalar_of_split_geometry L hπ hh hΨ hΨd hℓ₂ hcop hSurv hsplit
    hne hne' hnz hp₂ hp₂' hpz hzdeg hγ

/-- ★★ **THE SIGNED C.38 `dv2ResPolyTw_radical_eq`** (leanspec `ChapC.lean` NODE C.38,
conclusion byte-as-is; the same recorded `hh` binder delta): equal degree and identical
monic irreducible divisors across the block projection, from the signed C.39 scalar and
its nonvanishing (`γ̂_g ≠ 0` by F1.2's residual clause, `root ≠ 0` in the stage tower). -/
theorem dv2ResPolyTw_radical_eq (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hh : 0 < F.h)
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
        (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞)) :
    (dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree
        = (dv2ResPolyTw L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
        ↔ q ∣ dv2ResPolyTw L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂') := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  haveI : Fact (Irreducible L.r) := ⟨L.hrirr⟩
  letI : Field (AdjoinRoot L.r) := AdjoinRoot.instField
  refine dv2ResPolyTw_radical_eq_of_scalar L hne hne' hp₂ hp₂'
    (mul_ne_zero (γgAnch_ne_zero L hπ hh hctx) (pow_ne_zero _ (root_ne_zero L)))
    (dv2ResPolyTw_scalar L hπ hh hΨ hctx hnd hℓ₂ hcop hseam hne hne' hp₂ hp₂')

end Uniformity.Density.Tower.C136f14f

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136f14f.dv2FullRead_dev_mul_conv_split
#print axioms Uniformity.Density.Tower.C136f14f.dv2ResPolyAnch_mul_eq_weightedConv
#print axioms Uniformity.Density.Tower.C136f14f.dv2ResPolyTw_scalar_of_split_geometry
#print axioms Uniformity.Density.Tower.C136f14f.dv2ResPolyTw_scalar
#print axioms Uniformity.Density.Tower.C136f14f.dv2ResPolyTw_radical_eq

end AxCheck
