/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136f14
import Uniformity.ChapC.C134p1d

/-!
# Uniformity.ChapC.C136f14b — UNIT A24B: the guarded/anchored classical level-2
residual polynomial [A24B 2026-08-28]

The A-C.24′ carrier repair (A24A §4's redesign draft, decided by the S2 numeric battery
`verification/a24b_anchor_battery.py`): the CLASSICAL level-2 residual polynomial —
guarded (off-side junk-`0`, C.26's level-2 analogue) and anchored (per-slot fixed-grade
read at the side line, C.25's level-2 analogue) — beside the landed bare `dv2ResPoly`
(C.38a (g)), which stays untouched.

## The carrier

* `dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂` — coefficient `t` is the anchored absolute
  read `dv2FullRead L (M₂ - t*u₂) (dev Ψ f (min₂ + t*ℓ₂))`: the digit at lattice slot
  `min₂ + t·ℓ₂`, read at the side LINE height `M₂ - t·u₂` (C.25's `twistRead (M₀ - t*u)`
  one level up, with `dv2FullRead` as the reading instrument).

## The bank

* `dv2ResPolyAnch_coeff_of_le` / `_coeff_of_gt` / `natDegree_dv2ResPolyAnch_le` —
  coefficient extraction and the degree fence.
* `dv2ResPolyAnch_coeff_zero` — well-definedness at the anchor: the constant coefficient
  is the full read of the side-min digit at its exact pin height.
* ★ `dv2ResPolyAnch_coeff_eq_zero_of_not_onSide` — THE GUARD: an off-side lattice slot
  contributes `0` (the property whose absence refutes every constant-scalar law over the
  bare carrier — A24A's `dv2ResPoly_scalar_shape_digit_kill` channel, and the battery's
  Part B′ live instances).
* `dv2Pin_lattice_of_onSide` — on-side lattice slots have EXACTLY the line pin
  `M₂ - t·u₂` (the anchored coefficient is then the digit's own exact-height read).
* `dv2FullRead_dev_add` / `dv2ResPolyAnch_add` — additivity: coefficientwise at a common
  support-line floor, and polynomial-level at matched side data.
* ★ `dv2FullReadPoly_eq_shift` — the public level-2 twin of `C134p1d`'s private
  `lineRes_eq_shift`: at an exact finite level height, the fence-free full-read
  polynomial IS the level residual polynomial shifted by the anchor offset,
  `dv2FullReadPoly L k z = dvResPoly(z) · X^((jmin − shift k)/ℓ)`.
* ★★ `dv2FullRead_mul_testKey` — the mod-`Ψ` kill: the full read of `Ψ·q` at any height
  at or below its level value is `0` (below: the landed vanishing; at: the shifted
  residual factors through `dvResPoly_mul_gen` and `dvResPoly_testKey`, and
  `AdjoinRoot.mk L.r` kills the `L.r` factor).
* ★★ `dv2FullRead_modByMonic` + `dv2FullRead_dev_zero` — **the §5-risk absorber**: the
  anchored read is reduction-stable, `dv2FullRead L k (dev Ψ f 0) = dv2FullRead L k f`
  at any common height floor.  This is the property the battery certified (0 violations)
  and that the BARE per-slot read provably lacks at μ-value ties (the anchor shifts; the
  battery realized 120 + 15 shift events, all with a nontrivial would-be root exponent).
* `dv2FullRead_ne_zero_of_exact` — anchored nonvanishing below the recipe degree
  (the anchored twin of `C136f14.dv2Res_ne_zero_of_ne_zero_of_natDegree_lt`).
* ★ `dv2ResPolyAnch_coeff_of_onSide` — the on-side dictionary: the anchored coefficient
  is `root^δₜ · dv2Res(digit)` with the SLOT-DEPENDENT anchor offset
  `δₜ = (jmin(digit) − shift(M₂ − t·u₂))/ℓ` — the exact reason no constant scalar can
  relate the bare carrier across a product, and the shape in which the source's PE3 F-1
  root powers re-enter faithfully.

**Flagged for human review** (trust boundary — new statements): `dv2ResPolyAnch` (the
carrier definition), `dv2FullReadPoly_eq_shift`, `dv2FullRead_modByMonic`.

No landed or leanspec file is edited; nothing here is S2-special; the bare `dv2ResPoly`
and its landed consumers are untouched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136f14b

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0 Uniformity.Density.Tower.C136l2e3

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 0 — private plumbing (the standing local-twin convention) -/

private theorem inner_floor (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  rw [← mul_assoc]
  exact L.hκ

private theorem u_pos (L : LevelDatum F H₀ hpin) : 0 < L.u :=
  lt_of_le_of_lt (Nat.zero_le _) L.hκ

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

private theorem dvResPoly_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dvSideSet F x u ℓ).Nonempty) (hney : (dvSideSet F y u ℓ).Nonempty)
    {Mx My : ℕ} (hpx : dvHgt F x (dvSideMin F x u ℓ hnex) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hney) = (My : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hnex Mx hpx =
      dvResPoly F H₀ hpin y u ℓ hney My hpy := by
  subst hxy
  have hM : Mx = My := by exact_mod_cast hpx.symm.trans hpy
  subst hM
  rfl

/-- The support at the left endpoint pin: `W(z) = ℓ·M + u·jmin` as a `ℕ`-numeral
(local twin of C134p1d's private `dvSupp_eq_line`). -/
private theorem dvSupp_eq_line {u ℓ : ℕ} {z : Polynomial O}
    (hne : (dvSideSet F z u ℓ).Nonempty) {Mz : ℕ}
    (hpz : dvHgt F z (dvSideMin F z u ℓ hne) = (Mz : ℕ∞)) :
    dvSupp F z u ℓ = ((ℓ * Mz + u * dvSideMin F z u ℓ hne : ℕ) : ℕ∞) := by
  have hon : DvOnSide F z u ℓ (dvSideMin F z u ℓ hne) :=
    dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)
  rw [hon.1, hpz]
  push_cast [nsmul_eq_mul]
  ring

private theorem nat_of_line_le {ℓ u j H V : ℕ}
    (h : ((V : ℕ) : ℕ∞) ≤ ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)) :
    V ≤ ℓ * H + u * j := by
  have hcast : ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)
      = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  rw [hcast] at h
  exact_mod_cast h

private theorem nat_of_line_lt {ℓ u j H V : ℕ}
    (h : ((V : ℕ) : ℕ∞) < ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)) :
    V < ℓ * H + u * j := by
  have hcast : ℓ • ((H : ℕ) : ℕ∞) + (u : ℕ∞) * (j : ℕ∞)
      = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  rw [hcast] at h
  exact_mod_cast h

/-- Local twin of C28's private `shift_spec`: `s(m) < ℓ` and `s(m)·u ≡ m (mod ℓ)`
(the search body is proved to succeed through H.51's mod-`ℓ` bijection). -/
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

/-- Local twin of C28's private `shift_unique` (H.51(a) `class_sep` at `(u, ℓ)`). -/
private theorem shift_unique (L : LevelDatum F H₀ hpin) {m b : ℕ}
    (hb : b < L.ℓ) (hcong : b * L.u ≡ m [MOD L.ℓ]) : b = L.shift m := by
  obtain ⟨hlt, hsp⟩ := shift_spec L m
  exact Uniformity.Density.Induction.class_sep L.hcop hb hlt (hcong.trans hsp.symm)

private theorem mem_dvSideSet_of_dvOnSide' {z : Polynomial O} {u ℓ j : ℕ}
    (h : DvOnSide F z u ℓ j) : j ∈ dvSideSet F z u ℓ := by
  classical
  have hj : j ≤ z.natDegree := by
    by_contra hlt
    exact h.2 (C131y.dvHgt_eq_top_of_natDegree_lt F z (lt_of_not_ge hlt))
  simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hj, h⟩

/-- The read of an off-side line slot vanishes (local twin of C134p1d's private
`line_read_eq_zero_of_not_onSide`). -/
private theorem line_read_eq_zero_of_not_onSide (hπ : Irreducible π) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) {z : Polynomial O} {j₀ N₀ : ℕ}
    (hV : dvSupp F z u ℓ = ((ℓ * N₀ + u * j₀ : ℕ) : ℕ∞)) {t : ℕ} (ht : t * u ≤ N₀)
    (hoff : ¬ DvOnSide F z u ℓ (j₀ + t * ℓ)) :
    F.twistRead H₀ hpin (N₀ - t * u) (dev F.key z (j₀ + t * ℓ)) = 0 := by
  refine C130rp2.twistRead_eq_zero_of_lt F hπ H₀ hpin ?_
  rcases eq_or_ne (dvHgt F z (j₀ + t * ℓ)) ⊤ with htop | hne
  · have hgoal : F.stageHeight (dev F.key z (j₀ + t * ℓ)) = ⊤ := htop
    rw [hgoal]
    exact ENat.coe_lt_top _
  · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hne
    have hstrict : dvSupp F z u ℓ < ℓ • dvHgt F z (j₀ + t * ℓ) + (u * (j₀ + t * ℓ) : ℕ∞) :=
      lt_of_le_of_ne (C131y.dvSupp_le_term F z u hℓ (j₀ + t * ℓ))
        (fun heq => hoff ⟨heq, hne⟩)
    rw [hV, ← hH] at hstrict
    have hnat : ℓ * N₀ + u * j₀ < ℓ * H + u * (j₀ + t * ℓ) := nat_of_line_lt hstrict
    have hkey : ℓ * N₀ < ℓ * (H + u * t) := by
      have he : u * (j₀ + t * ℓ) = u * j₀ + ℓ * (u * t) := by ring
      have h2 : ℓ * (H + u * t) = ℓ * H + ℓ * (u * t) := by ring
      omega
    have hlt : N₀ < H + u * t := Nat.lt_of_mul_lt_mul_left hkey
    have hfin : N₀ - t * u < H := by
      have hc : t * u = u * t := Nat.mul_comm t u
      omega
    have hstage : F.stageHeight (dev F.key z (j₀ + t * ℓ)) = ((H : ℕ) : ℕ∞) := hH.symm
    rw [hstage]
    exact_mod_cast hfin

/-- Two level-2 on-side abscissae are congruent modulo the outer denominator (local
twin of C136l2e2's private `dv2OnSide_modEq`). -/
private theorem dv2OnSide_modEq' (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hcop : Nat.Coprime u₂ ℓ₂) {f : Polynomial O} {j j' : ℕ}
    (hj : Dv2OnSide L Ψ f u₂ ℓ₂ j) (hj' : Dv2OnSide L Ψ f u₂ ℓ₂ j') :
    j ≡ j' [MOD ℓ₂] := by
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hj.2
  obtain ⟨H', hH'⟩ := ENat.ne_top_iff_exists.1 hj'.2
  have hweight : ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)
      = ℓ₂ • dv2Pin L Ψ f j' + (u₂ * j' : ℕ∞) := hj.1.symm.trans hj'.1
  rw [← hH, ← hH'] at hweight
  have h1 : ℓ₂ • ((H : ℕ) : ℕ∞) + (u₂ * j : ℕ∞)
      = ((ℓ₂ * H + u₂ * j : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  have h2 : ℓ₂ • ((H' : ℕ) : ℕ∞) + (u₂ * j' : ℕ∞)
      = ((ℓ₂ * H' + u₂ * j' : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  rw [h1, h2] at hweight
  have key : ℓ₂ * H + u₂ * j = ℓ₂ * H' + u₂ * j' := by exact_mod_cast hweight
  have keyZ : (ℓ₂ : ℤ) * (H : ℤ) + (u₂ : ℤ) * (j : ℤ)
      = (ℓ₂ : ℤ) * (H' : ℤ) + (u₂ : ℤ) * (j' : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key
  have hdvd : (ℓ₂ : ℤ) ∣ (u₂ : ℤ) * ((j' : ℤ) - (j : ℤ)) :=
    ⟨(H : ℤ) - (H' : ℤ), by linarith⟩
  have hcop' : IsCoprime (ℓ₂ : ℤ) (u₂ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  exact Nat.modEq_iff_dvd.mpr (hcop'.dvd_of_dvd_mul_left hdvd)

/-- The horizontal span of a level-2 side is exactly `ℓ₂` times its side degree (local
twin of C136l2e2's private `dv2SideSpan_eq`). -/
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

/-- The lattice line floor: through the side degree, the line stays at nonnegative
heights — `t·u₂ ≤ M₂` for every in-range lattice index. -/
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

/-! ## Part 1 — the carrier -/

-- `hp₂` pins the level-2 side height `M₂` (GC-1's `sideMin` pin), exactly as `hpin₂`
-- does at C.25; it is a correctness side condition on the numeral, not body data.
set_option linter.unusedVariables false in
/-- ★ **The guarded/anchored classical level-2 residual polynomial** (A-C.24′'s carrier;
C.25 one level up).  Coefficient `t` is the anchored absolute read of the lattice digit
`dev Ψ f (min₂ + t·ℓ₂)` at the side LINE height `M₂ − t·u₂` — the level-2 analogue of
C.25's fixed-grade `twistRead (M₀ − t·u)`, with `dv2FullRead` as the instrument.  Unlike
the bare `dv2ResPoly` (C.38a (g), untouched), this carrier is GUARDED: off-side lattice
slots contribute `0` (`dv2ResPolyAnch_coeff_eq_zero_of_not_onSide`), and ANCHORED: its
reads are reduction-stable (`dv2FullRead_modByMonic`). -/
noncomputable def dv2ResPolyAnch (L : LevelDatum F H₀ hpin) (Ψ f : Polynomial O)
    (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) (M₂ : ℕ)
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    Polynomial (AdjoinRoot L.r) :=
  (Finset.range (dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1)).sum fun t =>
    Polynomial.C (dv2FullRead L (M₂ - t * u₂)
        (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)))
      * Polynomial.X ^ t

/-- In-range coefficient extraction. -/
theorem dv2ResPolyAnch_coeff_of_le (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t =
      dv2FullRead L (M₂ - t * u₂) (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) := by
  rw [dv2ResPolyAnch, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (Nat.lt_succ_of_le ht)]

/-- Beyond-range coefficient. -/
theorem dv2ResPolyAnch_coeff_of_gt (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) {t : ℕ}
    (ht : dv2SideDeg L Ψ f u₂ ℓ₂ hne < t) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t = 0 := by
  rw [dv2ResPolyAnch, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg (by omega)]

/-- The degree fence: the carrier's degree is at most the side degree. -/
theorem natDegree_dv2ResPolyAnch_le (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree
      ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun t ht => ?_
  exact dv2ResPolyAnch_coeff_of_gt L hne hp₂ ht

/-- **Well-definedness at the anchor**: the constant coefficient is the full read of the
side-min digit at exactly its pin height `M₂`. -/
theorem dv2ResPolyAnch_coeff_zero (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff 0 =
      dv2FullRead L M₂ (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne)) := by
  have h := dv2ResPolyAnch_coeff_of_le L hne hp₂ (Nat.zero_le _)
  simpa using h

/-! ## Part 2 — ★ the off-side junk-`0` guard, and the on-side exact pin -/

/-- On-side lattice slots carry EXACTLY the line pin: `dv2Pin (min₂ + t·ℓ₂) = M₂ − t·u₂`
(with `t·u₂ ≤ M₂`). -/
theorem dv2Pin_lattice_of_onSide (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) {t : ℕ}
    (hon : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) :
    t * u₂ ≤ M₂ ∧
      dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂) = ((M₂ - t * u₂ : ℕ) : ℕ∞) := by
  have hminON : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne) :=
    dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hne)
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hon.2
  have hW1 : dv2Supp L Ψ f u₂ ℓ₂
      = ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne : ℕ) : ℕ∞) := by
    rw [hminON.1, hp₂]
    push_cast [nsmul_eq_mul]
    ring
  have hW2 : dv2Supp L Ψ f u₂ ℓ₂
      = ((ℓ₂ * H + u₂ * (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂) : ℕ) : ℕ∞) := by
    rw [hon.1, ← hH]
    push_cast [nsmul_eq_mul]
    ring
  have hkey : ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne
      = ℓ₂ * H + u₂ * (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂) := by
    have h := hW1.symm.trans hW2
    exact_mod_cast h
  have hexp : u₂ * (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)
      = u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne + ℓ₂ * (t * u₂) := by ring
  rw [hexp] at hkey
  have h2 : ℓ₂ * M₂ = ℓ₂ * (H + t * u₂) := by
    have h3 : ℓ₂ * (H + t * u₂) = ℓ₂ * H + ℓ₂ * (t * u₂) := by ring
    omega
  have hM := Nat.eq_of_mul_eq_mul_left hℓ₂ h2
  refine ⟨by omega, ?_⟩
  rw [← hH]
  exact congrArg (fun n : ℕ => ((n : ℕ) : ℕ∞)) (by omega)

/-- ★ **THE GUARD** — the property the bare `dv2ResPoly` lacks (A24A §2): an in-range
lattice slot that is NOT on the level-2 side contributes coefficient `0` to the
guarded/anchored carrier, because its pin prices strictly above the side line and the
anchored read dies strictly below the pin (`dv2FullRead_eq_zero_of_lt`). -/
theorem dv2ResPolyAnch_coeff_eq_zero_of_not_onSide (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {Ψ f : Polynomial O} (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne)
    (hoff : ¬ Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t = 0 := by
  rw [dv2ResPolyAnch_coeff_of_le L hne hp₂ ht]
  have htu : t * u₂ ≤ M₂ := lattice_line_floor L hℓ₂ hcop hne hp₂ ht
  refine dv2FullRead_eq_zero_of_lt L hπ ?_
  show ((M₂ - t * u₂ : ℕ) : ℕ∞) < dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)
  rcases eq_or_ne (dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) ⊤ with htop | hfin
  · rw [htop]
    exact ENat.coe_lt_top _
  · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hfin
    have hminON : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne) :=
      dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hne)
    have hW1 : dv2Supp L Ψ f u₂ ℓ₂
        = ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne : ℕ) : ℕ∞) := by
      rw [hminON.1, hp₂]
      push_cast [nsmul_eq_mul]
      ring
    have hlt := lt_dv2Weight L hΨm hΨd hℓ₂ hW1 hH.symm hoff
    have hexp : u₂ * (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)
        = u₂ * dv2SideMin L Ψ f u₂ ℓ₂ hne + ℓ₂ * (t * u₂) := by ring
    rw [hexp] at hlt
    have h2 : ℓ₂ * M₂ < ℓ₂ * (H + t * u₂) := by
      have h3 : ℓ₂ * (H + t * u₂) = ℓ₂ * H + ℓ₂ * (t * u₂) := by ring
      omega
    have hM := Nat.lt_of_mul_lt_mul_left h2
    rw [← hH]
    exact_mod_cast (by omega : M₂ - t * u₂ < H)

/-! ## Part 3 — additivity -/

/-- Coefficientwise additivity at a common support-line floor: if both summands price at
or above the value line `V = ℓ₂·k + u₂·m`, the anchored read of the slot-`m` digit of the
sum splits. -/
theorem dv2FullRead_dev_add (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {Ψ : Polynomial O} (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {x y : Polynomial O} {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {V m k : ℕ}
    (hline : V = ℓ₂ * k + u₂ * m)
    (hVx : ((V : ℕ) : ℕ∞) ≤ dv2Supp L Ψ x u₂ ℓ₂)
    (hVy : ((V : ℕ) : ℕ∞) ≤ dv2Supp L Ψ y u₂ ℓ₂) :
    dv2FullRead L k (dev Ψ (x + y) m)
      = dv2FullRead L k (dev Ψ x m) + dv2FullRead L k (dev Ψ y m) := by
  have hfloor : ∀ z : Polynomial O, ((V : ℕ) : ℕ∞) ≤ dv2Supp L Ψ z u₂ ℓ₂ →
      ((k : ℕ) : ℕ∞) ≤ dv2Hgt L (dev Ψ z m) := by
    intro z hVz
    have hterm := dv2Supp_le_term L hΨm hΨd z u₂ hℓ₂ m
    have hV' := le_trans hVz hterm
    show ((k : ℕ) : ℕ∞) ≤ dv2Pin L Ψ z m
    rcases eq_or_ne (dv2Pin L Ψ z m) ⊤ with htop | hfin
    · rw [htop]
      exact le_top
    · obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hfin
      rw [← hH] at hV'
      have hnat : V ≤ ℓ₂ * H + u₂ * m := nat_of_line_le hV'
      have hk : k ≤ H := by
        have h1 : ℓ₂ * k ≤ ℓ₂ * H := by omega
        exact Nat.le_of_mul_le_mul_left h1 hℓ₂
      rw [← hH]
      exact_mod_cast hk
  rw [dev_add_of_monic hΨm]
  exact dv2FullRead_add_of_le L hπ (hfloor x hVx) (hfloor y hVy)

/-- Polynomial-level additivity at matched side data (the tie configuration): if `x`,
`y`, and `x + y` share the same side minimum, side degree, and pin `M₂`, the anchored
carriers add. -/
theorem dv2ResPolyAnch_add (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {Ψ : Polynomial O} (hΨm : Ψ.Monic) (hΨd : 0 < Ψ.natDegree)
    {x y : Polynomial O} {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hnex : (dv2SideSet L Ψ x u₂ ℓ₂).Nonempty)
    (hney : (dv2SideSet L Ψ y u₂ ℓ₂).Nonempty)
    (hnexy : (dv2SideSet L Ψ (x + y) u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hpx : dv2Pin L Ψ x (dv2SideMin L Ψ x u₂ ℓ₂ hnex) = (M₂ : ℕ∞))
    (hpy : dv2Pin L Ψ y (dv2SideMin L Ψ y u₂ ℓ₂ hney) = (M₂ : ℕ∞))
    (hpxy : dv2Pin L Ψ (x + y) (dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy) = (M₂ : ℕ∞))
    (hminx : dv2SideMin L Ψ x u₂ ℓ₂ hnex = dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy)
    (hminy : dv2SideMin L Ψ y u₂ ℓ₂ hney = dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy)
    (hdegx : dv2SideDeg L Ψ x u₂ ℓ₂ hnex = dv2SideDeg L Ψ (x + y) u₂ ℓ₂ hnexy)
    (hdegy : dv2SideDeg L Ψ y u₂ ℓ₂ hney = dv2SideDeg L Ψ (x + y) u₂ ℓ₂ hnexy) :
    dv2ResPolyAnch L Ψ (x + y) u₂ ℓ₂ hnexy M₂ hpxy
      = dv2ResPolyAnch L Ψ x u₂ ℓ₂ hnex M₂ hpx
        + dv2ResPolyAnch L Ψ y u₂ ℓ₂ hney M₂ hpy := by
  refine Polynomial.ext fun t => ?_
  rw [Polynomial.coeff_add]
  by_cases ht : t ≤ dv2SideDeg L Ψ (x + y) u₂ ℓ₂ hnexy
  · rw [dv2ResPolyAnch_coeff_of_le L hnexy hpxy ht,
      dv2ResPolyAnch_coeff_of_le L hnex hpx (by rw [hdegx]; exact ht),
      dv2ResPolyAnch_coeff_of_le L hney hpy (by rw [hdegy]; exact ht),
      hminx, hminy]
    have htu : t * u₂ ≤ M₂ :=
      lattice_line_floor L hℓ₂ hcop hnexy hpxy ht
    -- the common value line: both summands sit on the same side line as the sum
    have hVline : ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy
        = ℓ₂ * (M₂ - t * u₂) + u₂ * (dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy + t * ℓ₂) := by
      have e1 : u₂ * (dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy + t * ℓ₂)
          = u₂ * dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy + ℓ₂ * (t * u₂) := by ring
      have e2 : ℓ₂ * (M₂ - t * u₂) = ℓ₂ * M₂ - ℓ₂ * (t * u₂) :=
        Nat.mul_sub_left_distrib ℓ₂ M₂ (t * u₂)
      have e3 : ℓ₂ * (t * u₂) ≤ ℓ₂ * M₂ := Nat.mul_le_mul le_rfl htu
      omega
    have hVx : ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy : ℕ) : ℕ∞)
        ≤ dv2Supp L Ψ x u₂ ℓ₂ := by
      have hminON : Dv2OnSide L Ψ x u₂ ℓ₂ (dv2SideMin L Ψ x u₂ ℓ₂ hnex) :=
        dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hnex)
      have hW : dv2Supp L Ψ x u₂ ℓ₂
          = ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ x u₂ ℓ₂ hnex : ℕ) : ℕ∞) := by
        rw [hminON.1, hpx]
        push_cast [nsmul_eq_mul]
        ring
      rw [hW, hminx]
    have hVy : ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ (x + y) u₂ ℓ₂ hnexy : ℕ) : ℕ∞)
        ≤ dv2Supp L Ψ y u₂ ℓ₂ := by
      have hminON : Dv2OnSide L Ψ y u₂ ℓ₂ (dv2SideMin L Ψ y u₂ ℓ₂ hney) :=
        dv2OnSide_of_mem_dv2SideSet L (Finset.min'_mem _ hney)
      have hW : dv2Supp L Ψ y u₂ ℓ₂
          = ((ℓ₂ * M₂ + u₂ * dv2SideMin L Ψ y u₂ ℓ₂ hney : ℕ) : ℕ∞) := by
        rw [hminON.1, hpy]
        push_cast [nsmul_eq_mul]
        ring
      rw [hW, hminy]
    exact dv2FullRead_dev_add L hπ hΨm hΨd hℓ₂ hVline hVx hVy
  · rw [dv2ResPolyAnch_coeff_of_gt L hnexy hpxy (by omega),
      dv2ResPolyAnch_coeff_of_gt L hnex hpx (by omega),
      dv2ResPolyAnch_coeff_of_gt L hney hpy (by omega), add_zero]

/-! ## Part 4 — ★ the shift identity: the full read IS the shifted residual -/

/-- ★ **The level-2 shift identity** (the public twin of `C134p1d`'s private
`lineRes_eq_shift`, at the canonical anchor base `L.shift k`): at an exact finite level
height `k`, the fence-free full-read polynomial is the level residual polynomial shifted
by the anchor offset, `dv2FullReadPoly L k z = R(z) · X^((jmin − s(k))/ℓ)`. -/
theorem dv2FullReadPoly_eq_shift (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {z : Polynomial O} {k : ℕ} (hk : dv2Hgt L z = (k : ℕ∞))
    (hne : (dvSideSet F z L.u L.ℓ).Nonempty) {Mz : ℕ}
    (hpz : dvHgt F z (dvSideMin F z L.u L.ℓ hne) = (Mz : ℕ∞)) :
    dv2FullReadPoly L k z
      = dvResPoly F H₀ hpin z L.u L.ℓ hne Mz hpz
          * Polynomial.X ^ ((dvSideMin F z L.u L.ℓ hne - L.shift k) / L.ℓ) := by
  classical
  have hu : 0 < L.u := u_pos L
  change dvSupp F z L.u L.ℓ = (k : ℕ∞) at hk
  set jm := dvSideMin F z L.u L.ℓ hne with hjm
  set sd := dvSideDeg F z L.u L.ℓ hne with hsd
  -- the line equation at the side min
  have hlineK : L.ℓ * Mz + L.u * jm = k := by
    have h1 := (dvSupp_eq_line hne hpz).symm.trans hk
    exact_mod_cast h1
  -- the canonical anchor is the side-min residue class
  have hs_eq : jm % L.ℓ = L.shift k := by
    refine shift_unique L (Nat.mod_lt _ L.hℓ) ?_
    calc (jm % L.ℓ) * L.u
        ≡ jm * L.u [MOD L.ℓ] := (Nat.mod_modEq jm L.ℓ).mul_right L.u
      _ ≡ k [MOD L.ℓ] := by
          show jm * L.u % L.ℓ = k % L.ℓ
          rw [← hlineK, Nat.mul_add_mod, Nat.mul_comm jm L.u]
  have hsle : L.shift k ≤ jm := by
    rw [← hs_eq]
    exact Nat.mod_le jm L.ℓ
  set δ := (jm - L.shift k) / L.ℓ with hδdef
  have hδ : jm = L.shift k + δ * L.ℓ := by
    have hdvd : L.ℓ ∣ jm - L.shift k := by
      have := Nat.div_add_mod jm L.ℓ
      exact ⟨jm / L.ℓ, by omega⟩
    have h : δ * L.ℓ = jm - L.shift k := by
      rw [hδdef]
      exact Nat.div_mul_cancel hdvd
    omega
  set N₀ := Mz + L.u * δ with hN₀def
  have hN₀k : k = L.ℓ * N₀ + L.u * L.shift k := by
    have e1 : L.u * jm = L.u * L.shift k + L.ℓ * (L.u * δ) := by rw [hδ]; ring
    have e2 : L.ℓ * N₀ = L.ℓ * Mz + L.ℓ * (L.u * δ) := by rw [hN₀def]; ring
    omega
  -- the filter range is the line range
  have hset : (Finset.range (k + 1)).filter
      (fun t => (L.shift k + L.ℓ * t) * L.u ≤ k) = Finset.range (N₀ / L.u + 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    have e1 : (L.shift k + L.ℓ * t) * L.u
        = L.u * L.shift k + L.ℓ * (t * L.u) := by ring
    constructor
    · rintro ⟨-, hle⟩
      have h1 : L.ℓ * (t * L.u) ≤ L.ℓ * N₀ := by omega
      have h2 : t * L.u ≤ N₀ := Nat.le_of_mul_le_mul_left h1 L.hℓ
      exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hu).mpr h2)
    · intro ht
      have h2 : t * L.u ≤ N₀ := (Nat.le_div_iff_mul_le hu).mp (Nat.lt_succ_iff.mp ht)
      have htk : t < k + 1 := by
        have hℓ1 : 1 ≤ L.ℓ := L.hℓ
        have hu1 : 1 ≤ L.u := hu
        have : t ≤ t * L.u := Nat.le_mul_of_pos_right t hu
        have : t ≤ N₀ := le_trans this h2
        have : N₀ ≤ L.ℓ * N₀ := Nat.le_mul_of_pos_left N₀ L.hℓ
        omega
      have h3 : L.ℓ * (t * L.u) ≤ L.ℓ * N₀ := Nat.mul_le_mul le_rfl h2
      exact ⟨htk, by omega⟩
  -- the per-slot height identity along the line
  have hheight : ∀ t : ℕ, t * L.u ≤ N₀ →
      (k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ = N₀ - t * L.u := by
    intro t ht
    have e1 : (L.shift k + L.ℓ * t) * L.u
        = L.u * L.shift k + L.ℓ * (t * L.u) := by ring
    have e2 : L.ℓ * (N₀ - t * L.u) = L.ℓ * N₀ - L.ℓ * (t * L.u) :=
      Nat.mul_sub_left_distrib L.ℓ N₀ (t * L.u)
    have hexp : k - (L.shift k + L.ℓ * t) * L.u = L.ℓ * (N₀ - t * L.u) := by omega
    rw [hexp, Nat.mul_div_cancel_left _ L.hℓ]
  -- the endpoint span: `jmax = jm + ℓ·sd` and `u·sd ≤ Mz`
  have hmaxmem : dvSideMax F z L.u L.ℓ hne ∈ dvSideSet F z L.u L.ℓ := Finset.max'_mem _ _
  have hminle : jm ≤ dvSideMax F z L.u L.ℓ hne := Finset.min'_le _ _ hmaxmem
  have hlen : dvSideMax F z L.u L.ℓ hne - jm = L.ℓ * sd := by
    have h := dvSideLen_eq F L.hℓ L.hcop hne
    rw [dvSideLen] at h
    exact h
  have hjmax : dvSideMax F z L.u L.ℓ hne = jm + L.ℓ * sd := by omega
  have honmax := dvOnSide_of_mem_dvSideSet hmaxmem
  obtain ⟨Hmax, hHmax⟩ := ENat.ne_top_iff_exists.1 honmax.2
  have hmaxline : L.ℓ * Mz + L.u * jm
      = L.ℓ * Hmax + L.u * dvSideMax F z L.u L.ℓ hne := by
    have h1 : dvSupp F z L.u L.ℓ
        = ((L.ℓ * Hmax + L.u * dvSideMax F z L.u L.ℓ hne : ℕ) : ℕ∞) := by
      rw [honmax.1, ← hHmax]
      push_cast [nsmul_eq_mul]
      ring
    have h2 := (dvSupp_eq_line hne hpz).symm.trans h1
    exact_mod_cast h2
  have hMzfloor : L.u * sd ≤ Mz := by
    rw [hjmax] at hmaxline
    have hexp : L.u * (jm + L.ℓ * sd) = L.u * jm + L.ℓ * (L.u * sd) := by ring
    rw [hexp] at hmaxline
    have h2 : L.ℓ * Mz = L.ℓ * (Hmax + L.u * sd) := by
      have h3 : L.ℓ * (Hmax + L.u * sd) = L.ℓ * Hmax + L.ℓ * (L.u * sd) := by ring
      omega
    have := Nat.eq_of_mul_eq_mul_left L.hℓ h2
    omega
  have hTδ : δ + sd ≤ N₀ / L.u := by
    refine (Nat.le_div_iff_mul_le hu).mpr ?_
    have e1 : (δ + sd) * L.u = L.u * sd + L.u * δ := by ring
    omega
  have hδrange : δ ≤ N₀ / L.u := le_trans (Nat.le_add_right δ sd) hTδ
  -- the value pin at the anchor base, for the off-side reads
  have hV : dvSupp F z L.u L.ℓ = ((L.ℓ * N₀ + L.u * L.shift k : ℕ) : ℕ∞) := by
    rw [hk]
    exact_mod_cast congrArg (fun n : ℕ => ((n : ℕ) : ℕ∞)) hN₀k
  -- the residual degree fence
  have hRdeg : (dvResPoly F H₀ hpin z L.u L.ℓ hne Mz hpz).natDegree = sd :=
    (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne hpz).1
  -- assemble coefficientwise
  rw [dv2FullReadPoly, hset]
  refine Polynomial.ext fun s' => ?_
  rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, Polynomial.coeff_mul_X_pow']
  by_cases hsδ : δ ≤ s'
  · rw [if_pos hsδ]
    set t := s' - δ with htdef
    have hst : s' = δ + t := by omega
    by_cases hts : t ≤ sd
    · -- the on-window band: both sides read the same slot at the same height
      have hsT : s' < N₀ / L.u + 1 := by omega
      rw [if_pos hsT]
      have hRcoeff : (dvResPoly F H₀ hpin z L.u L.ℓ hne Mz hpz).coeff t
          = F.twistRead H₀ hpin (Mz - t * L.u) (dev F.key z (jm + t * L.ℓ)) := by
        rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
          if_pos (Nat.lt_succ_of_le hts)]
      rw [hRcoeff]
      have hslot : L.shift k + L.ℓ * s' = jm + t * L.ℓ := by
        calc L.shift k + L.ℓ * s'
            = L.shift k + L.ℓ * (δ + t) := by rw [← hst]
          _ = (L.shift k + δ * L.ℓ) + t * L.ℓ := by ring
          _ = jm + t * L.ℓ := by rw [← hδ]
      have hs'u : s' * L.u ≤ N₀ := (Nat.le_div_iff_mul_le hu).mp (Nat.lt_succ_iff.mp hsT)
      have hheight' : (k - (L.shift k + L.ℓ * s') * L.u) / L.ℓ = Mz - t * L.u := by
        rw [hheight s' hs'u]
        have e1 : s' * L.u = δ * L.u + t * L.u := by rw [hst]; ring
        have e2 : L.u * δ = δ * L.u := Nat.mul_comm _ _
        omega
      rw [hheight', hslot]
    · -- past the side's right endpoint: both sides vanish
      have hRzero : (dvResPoly F H₀ hpin z L.u L.ℓ hne Mz hpz).coeff t = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [hRdeg]
        omega
      rw [hRzero]
      by_cases hsT : s' < N₀ / L.u + 1
      · rw [if_pos hsT]
        have hs'u : s' * L.u ≤ N₀ := (Nat.le_div_iff_mul_le hu).mp (Nat.lt_succ_iff.mp hsT)
        have hoff : ¬ DvOnSide F z L.u L.ℓ (L.shift k + s' * L.ℓ) := by
          intro hon
          have hmem := mem_dvSideSet_of_dvOnSide' hon
          have hle : L.shift k + s' * L.ℓ ≤ dvSideMax F z L.u L.ℓ hne :=
            Finset.le_max' _ _ hmem
          rw [hjmax, hδ] at hle
          have e1 : s' * L.ℓ = δ * L.ℓ + t * L.ℓ := by rw [hst]; ring
          have e2 : L.ℓ * sd = sd * L.ℓ := Nat.mul_comm _ _
          have h3 : t * L.ℓ ≤ sd * L.ℓ := by omega
          have h4 : t ≤ sd := Nat.le_of_mul_le_mul_right h3 L.hℓ
          omega
        have hz := line_read_eq_zero_of_not_onSide (H₀ := H₀) (hpin := hpin) hπ L.hℓ
          hV hs'u hoff
        rw [hheight s' hs'u]
        have hslot : L.shift k + L.ℓ * s' = L.shift k + s' * L.ℓ := by ring
        rw [hslot]
        exact hz
      · rw [if_neg hsT]
  · -- left of the side's left endpoint: the slot is off-side, the shift power is unmet
    rw [if_neg hsδ]
    have hsT : s' < N₀ / L.u + 1 := by omega
    rw [if_pos hsT]
    have hs'u : s' * L.u ≤ N₀ := (Nat.le_div_iff_mul_le hu).mp (Nat.lt_succ_iff.mp hsT)
    have hoff : ¬ DvOnSide F z L.u L.ℓ (L.shift k + s' * L.ℓ) := by
      intro hon
      have hmem := mem_dvSideSet_of_dvOnSide' hon
      have hle : jm ≤ L.shift k + s' * L.ℓ := Finset.min'_le _ _ hmem
      rw [hδ] at hle
      have hlt : s' * L.ℓ < δ * L.ℓ :=
        (Nat.mul_lt_mul_right L.hℓ).mpr (lt_of_not_ge hsδ)
      omega
    have hz := line_read_eq_zero_of_not_onSide (H₀ := H₀) (hpin := hpin) hπ L.hℓ
      hV hs'u hoff
    rw [hheight s' hs'u]
    have hslot : L.shift k + L.ℓ * s' = L.shift k + s' * L.ℓ := by ring
    rw [hslot]
    exact hz

/-! ## Part 5 — ★★ the mod-`Ψ` kill and the §5-risk absorber -/

/-- ★★ **The mod-`Ψ` kill**: the anchored full read of any test-key multiple `Ψ·q`
vanishes at every height at or below its level value.  Strictly below is the landed
vanishing; at the exact value the shifted residual factors as `L.r · R(q) · X^δ`
(`dvResPoly_mul_gen` + `dvResPoly_testKey`) and `AdjoinRoot.mk L.r` kills it. -/
theorem dv2FullRead_mul_testKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) {q : Polynomial O}
    (hq : q ≠ 0) {k : ℕ} (hk : (k : ℕ∞) ≤ dv2Hgt L (Ψ * q)) :
    dv2FullRead L k (Ψ * q) = 0 := by
  have hΨm : Ψ.Monic := hΨ.1
  have hΨq0 : Ψ * q ≠ 0 := mul_ne_zero hΨm.ne_zero hq
  rcases hk.lt_or_eq with hlt | heq
  · exact dv2FullRead_eq_zero_of_lt L hπ hlt
  · have hgt : dv2Hgt L (Ψ * q) = (k : ℕ∞) := heq.symm
    have hnΨq : (dvSideSet F (Ψ * q) L.u L.ℓ).Nonempty :=
      dvSideSet_nonempty F hΨq0 L.u L.hℓ
    have hnΨ : (dvSideSet F Ψ L.u L.ℓ).Nonempty :=
      dvSideSet_nonempty F hΨm.ne_zero L.u L.hℓ
    have hnq : (dvSideSet F q L.u L.ℓ).Nonempty := dvSideSet_nonempty F hq L.u L.hℓ
    obtain ⟨MΨq, hpΨq⟩ := exists_pin F hnΨq
    obtain ⟨MΨ, hpΨ⟩ := exists_pin F hnΨ
    obtain ⟨Mq, hpq⟩ := exists_pin F hnq
    have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop (inner_floor L)
      hΨm.ne_zero hq hnΨ hnq hnΨq hpΨ hpq hpΨq
    have hshift := dv2FullReadPoly_eq_shift L hπ hgt hnΨq hpΨq
    rw [dv2FullRead, hshift, hmul, dvResPoly_testKey hπ L hΨ hnΨ MΨ hpΨ,
      mul_assoc, map_mul, AdjoinRoot.mk_self, zero_mul]

/-- ★★ **The §5-risk absorber — anchored reads are reduction-stable**: the full read of
`f %ₘ Ψ` at any height at or below both level values agrees with the full read of `f`.
This is the property the S2 battery certified (0 violations over every reduction event)
and the exact clause whose BARE analogue fails at μ-value ties (the battery's 135
realized anchor-shift events). -/
theorem dv2FullRead_modByMonic (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (f : Polynomial O) {k : ℕ}
    (hf : (k : ℕ∞) ≤ dv2Hgt L f)
    (hΨq : (k : ℕ∞) ≤ dv2Hgt L (Ψ * (f /ₘ Ψ))) :
    dv2FullRead L k (f %ₘ Ψ) = dv2FullRead L k f := by
  have hΨm : Ψ.Monic := hΨ.1
  have hdiv : f %ₘ Ψ + Ψ * (f /ₘ Ψ) = f := Polynomial.modByMonic_add_div f Ψ
  rcases eq_or_ne (f /ₘ Ψ) 0 with hq0 | hq0
  · rw [hq0, mul_zero, add_zero] at hdiv
    rw [hdiv]
  · have hrem : f %ₘ Ψ = f + -(Ψ * (f /ₘ Ψ)) := by
      have h := eq_sub_of_add_eq hdiv
      rw [h, sub_eq_add_neg]
    have hfloor : (k : ℕ∞) ≤ dv2Hgt L (f %ₘ Ψ) := by
      rw [hrem]
      refine le_trans (le_min hf ?_) (min_dv2Hgt_le_dv2Hgt_add L f (-(Ψ * (f /ₘ Ψ))))
      show (k : ℕ∞) ≤ dvSupp F (-(Ψ * (f /ₘ Ψ))) L.u L.ℓ
      rw [dvSupp_neg]
      exact hΨq
    calc dv2FullRead L k (f %ₘ Ψ)
        = dv2FullRead L k (f %ₘ Ψ) + dv2FullRead L k (Ψ * (f /ₘ Ψ)) := by
          rw [dv2FullRead_mul_testKey L hπ hh hΨ hq0 hΨq, add_zero]
      _ = dv2FullRead L k (f %ₘ Ψ + Ψ * (f /ₘ Ψ)) :=
          (dv2FullRead_add_of_le L hπ hfloor hΨq).symm
      _ = dv2FullRead L k f := by rw [hdiv]

/-- The slot-`0` reading of the absorber: the anchored read looks through the `Ψ`-digit
reduction (`dev Ψ f 0 = f %ₘ Ψ`). -/
theorem dv2FullRead_dev_zero (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    (hh : 0 < F.h) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (f : Polynomial O) {k : ℕ}
    (hf : (k : ℕ∞) ≤ dv2Hgt L f)
    (hΨq : (k : ℕ∞) ≤ dv2Hgt L (Ψ * (f /ₘ Ψ))) :
    dv2FullRead L k (dev Ψ f 0) = dv2FullRead L k f := by
  rw [dev_zero_pin]
  exact dv2FullRead_modByMonic L hπ hh hΨ f hf hΨq

/-- Anchored nonvanishing below the recipe degree (the anchored twin of
`C136f14.dv2Res_ne_zero_of_ne_zero_of_natDegree_lt`): at its exact level height, a
nonzero polynomial short of the recipe degree has a nonzero full read. -/
theorem dv2FullRead_ne_zero_of_exact (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A : Polynomial O} (hA : A ≠ 0) (hdeg : A.natDegree < L.keyDeg₂) {k : ℕ}
    (hk : dv2Hgt L A = (k : ℕ∞)) :
    dv2FullRead L k A ≠ 0 := by
  classical
  have hne : (dvSideSet F A L.u L.ℓ).Nonempty := dvSideSet_nonempty F hA L.u L.hℓ
  obtain ⟨M, hp⟩ := exists_pin F hne
  have hshift := dv2FullReadPoly_eq_shift L hπ hk hne hp
  rw [dv2FullRead, hshift]
  intro hzero
  have hdvd : L.r ∣ dvResPoly F H₀ hpin A L.u L.ℓ hne M hp
      * Polynomial.X ^ ((dvSideMin F A L.u L.ℓ hne - L.shift k) / L.ℓ) :=
    AdjoinRoot.mk_eq_zero.mp hzero
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hprime : Prime L.r := UniqueFactorizationMonoid.irreducible_iff_prime.mp L.hrirr
  rcases hprime.2.2 _ _ hdvd with h | h
  · exact (C134p1d.not_residual_dvd_of_natDegree_lt L hπ hdeg hne M hp) h
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

/-! ## Part 6 — ★ the on-side dictionary: anchored = root-power × bare -/

/-- ★ **The on-side dictionary**: at an on-side lattice slot, the anchored coefficient
is the bare coherent read TWISTED by the slot's own anchor offset,
`coeff t = root^δₜ · dv2Res(digit)` with `δₜ = (jmin(digit) − s(M₂ − t·u₂))/ℓ`.
The exponent is SLOT-DEPENDENT — which is exactly why no constant scalar can relate the
bare carrier across a product (A24A's two refutation channels), and the shape in which
PE3 F-1's root powers re-enter the anchored C.39′ faithfully. -/
theorem dv2ResPolyAnch_coeff_of_onSide (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {Ψ f : Polynomial O} {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne)
    (hon : Dv2OnSide L Ψ f u₂ ℓ₂ (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂))
    (hne₁ : (dvSideSet F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) L.u L.ℓ).Nonempty)
    {m₁ : ℕ}
    (hp₁ : dvHgt F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂))
        (dvSideMin F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) L.u L.ℓ hne₁)
      = (m₁ : ℕ∞)) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t
      = AdjoinRoot.root L.r
            ^ ((dvSideMin F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) L.u L.ℓ hne₁
                - L.shift (M₂ - t * u₂)) / L.ℓ)
          * dv2Res L (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) := by
  classical
  obtain ⟨htu, hpinj⟩ := dv2Pin_lattice_of_onSide L hℓ₂ hne hp₂ hon
  rw [dv2ResPolyAnch_coeff_of_le L hne hp₂ ht]
  have hgt : dv2Hgt L (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂))
      = ((M₂ - t * u₂ : ℕ) : ℕ∞) := hpinj
  have hshift := dv2FullReadPoly_eq_shift L hπ hgt hne₁ hp₁
  have hex : ∃ (hne' : (dvSideSet F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂))
        L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂))
        (dvSideMin F (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)) L.u L.ℓ hne')
        = (M₀ : ℕ∞) := ⟨hne₁, m₁, hp₁⟩
  rw [dv2FullRead, hshift, map_mul, map_pow, AdjoinRoot.mk_X, dv2Res, dif_pos hex,
    dvResPoly_congr F H₀ hpin rfl hex.choose hne₁
      hex.choose_spec.choose_spec hp₁, mul_comm]

end Uniformity.Density.Tower.C136f14b

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch
#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch_coeff_of_le
#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch_coeff_of_gt
#print axioms Uniformity.Density.Tower.C136f14b.natDegree_dv2ResPolyAnch_le
#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch_coeff_zero
#print axioms Uniformity.Density.Tower.C136f14b.dv2Pin_lattice_of_onSide
#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch_coeff_eq_zero_of_not_onSide
#print axioms Uniformity.Density.Tower.C136f14b.dv2FullRead_dev_add
#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch_add
#print axioms Uniformity.Density.Tower.C136f14b.dv2FullReadPoly_eq_shift
#print axioms Uniformity.Density.Tower.C136f14b.dv2FullRead_mul_testKey
#print axioms Uniformity.Density.Tower.C136f14b.dv2FullRead_modByMonic
#print axioms Uniformity.Density.Tower.C136f14b.dv2FullRead_dev_zero
#print axioms Uniformity.Density.Tower.C136f14b.dv2FullRead_ne_zero_of_exact
#print axioms Uniformity.Density.Tower.C136f14b.dv2ResPolyAnch_coeff_of_onSide

end AxCheck
