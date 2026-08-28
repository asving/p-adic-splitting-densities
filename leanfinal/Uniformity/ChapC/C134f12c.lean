/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C134frt
import Uniformity.ChapC.C130in
import Uniformity.ChapB.B04

/-!
# Uniformity.ChapC.C134f12c — `[F12C 2026-08-28]`: F1.2 clause 2 via the mixed law; the full
signed F1.2; F1.7 landed (UNIT F12C)

`runs/wave-c/verdict_FRT.md` landed F1.2's clauses 1+3 and the quotient bridge
(`C134frt.context_split_quotient : f /ₘ blockFactor L f = g₂ * Wf`) but recorded clause 2
BLOCKED — "transporting `g₂`'s non-`L.r`-divisibility through multiplication by the merely
point-sided `Wf`" — citing only the OLD product laws (`fgmn_dv_exact_mul`,
`fgmn_residual_mul`: both factors `IsDvPure` + degree fences).  The orchestrator dissented
(commit 00e397a5): the NEW unconditional mixed law `C133mh3.dvResPoly_mul_gen` (Theorem M
clause 3, τ = 1) requires ONLY `g ≠ 0`, `z ≠ 0` + side pins + the frame pack — no purity —
and the transport mechanism is exactly `C133mh14.residual_transport`'s: a point-sided
factor has `dvSideDeg = 0`, so its residual is a NONZERO CONSTANT (C.26's
`natDegree_dvResPoly`), hence a unit of `K[Z]`, and `L.r`-divisibility passes between
`R(g₂)` and `R(g₂)·R(Wf)` freely.  The dissent is correct; this file enacts it.

## What this file lands

* `notdvd_dvResPoly_mul_pointSided` — ★ **the transport lemma (charge step 1)**: for any
  `r`, if `g₂`'s residual is not `r`-divisible at every pin and `Wf` is point-sided, then
  the PRODUCT's residual is not `r`-divisible at every pin.  Mechanism:
  `C133mh3.dvResPoly_mul_gen` gives `R(g₂·Wf) = R(g₂)·R(Wf)`; `R(Wf)` is a unit
  (point side ⟹ degree 0 by C.26(ii), constant term ≠ 0 by C.26(iii)); unit
  cancellation runs `C133mh14.residual_transport`'s divisibility step in reverse.
* `quotient_residual_notdvd` — **clause 2 of the signed F1.2**, on
  `f /ₘ blockFactor L f`: the split from `C134frt.context_split_quotient` feeds the
  transport lemma through `dvResPoly_congr` (pin transport across the quotient identity).
* `block_complement_notdvd` — ★ **the FULL signed F1.2** (leanspec `ChapC.lean:1623-1631`,
  conclusion byte-as-is): clause 1 = `C134frt.testKey_dvd_iff_dvd_blockFactor`, clause 2 =
  `quotient_residual_notdvd`, clause 3 = `C134frt.quotient_dvSupp_ne_top`.  The one binder
  delta beyond the signed list is `hh : 0 < F.h`, the standing engine-frame-nondegeneracy
  entry (`verdict_CFS.md` "the one binder delta, stated once").
* `dv2_length_sum` — ★ **F1.7 (leanspec `ChapC.lean:2320-2328`), landed on RE-ATTEMPT,
  conclusion byte-as-is** (+ the same `hh` delta).  The CFS/FRT sweeps chained it behind
  F1.6 (blocked), but the SIGNED statement is about `blockFactor L f` ALONE and needs no
  translation identity: clause 1 (`dv2Pin … 0 ≠ ⊤`) is `dev Ψ (blockFactor L f) 0 =
  blockFactor L f %ₘ Ψ ≠ 0` (from `hnd`, `Ψ` monic) + `C130s6.dvSupp_ne_top_of_ne_zero`;
  clause 2 (`dv2Pin … (mult₂ L f) = 0`) is the monic-top digit `dev_top_eq_one`
  (`C130in`) at the landed degree law `C134cfs.blockDeg_eq`, then `C133mh9.dvSupp_one`;
  clause 3 (`dv2SideMax ≤ mult₂`) is digit vanishing past the degree
  (`dev_eq_zero_of_lt`, B.04) + `C130s6.dvSupp_zero_eq_top` against `Dv2OnSide`'s
  finiteness guard.

## Re-attempt record for F1.3–F1.6 (BLOCKED-BECAUSE; F1.8 out of scope)

See the documented section before the footer: the remaining blocks are LEVEL-TWO, and the
level-one mixed law does not touch them.

## Credited local plumbing

`isKey_X`, `localFieldStageField`, `floor_assoc`, `exists_pin`, `dvResPoly_congr` are
byte-identical local copies of `C133mh14.lean` Part-0 privates (unreachable across files;
same convention as `C134csx.lean`); `dv2OnSide_of_mem'` is the level-2 twin of
`C133mh14`'s `dvOnSide_of_mem'`.  No landed file edited.

## Cite discipline

The only non-Lean-core name in any footprint is the allowlisted C.33 dissection cite
`exists_dvDissection`, inherited through `C134csx.context_split` (via
`C134frt.context_split_quotient`) and the `C134cfs` block-spec projections exactly as in
FRT/CSX.  The transport lemma itself is Lean-core.  Sorry-free; no new axiom.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Tower.C134f12c

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-! ## Part 0 — private plumbing (credited local copies; see the module docstring) -/

/-- Local D9 reconstruction (source: `C133mh14.lean`'s private `isKey_X`). -/
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

/-- The strict floor `ℓ·(D′·h) < u`, re-associated from `LevelDatum.hκ` (source:
`C133mh14.lean`'s private `floor_assoc`). -/
private theorem floor_assoc {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  have h := L.hκ; rw [mul_assoc] at h; exact h

/-- Pin existence at the side minimum (source: `C133mh14.lean`'s private `exists_pin`,
routed through the public `dvOnSide_of_mem_dvSideSet`). -/
private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1
    (dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

/-- `dvResPoly` transports across an equality of polynomials (source: `C133mh14.lean`'s
private `dvResPoly_congr`, byte-identical). -/
private theorem dvResPoly_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dvSideSet F x u ℓ).Nonempty) (hney : (dvSideSet F y u ℓ).Nonempty)
    {Mx My : ℕ} (hpx : dvHgt F x (dvSideMin F x u ℓ hnex) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hney) = (My : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hnex Mx hpx = dvResPoly F H₀ hpin y u ℓ hney My hpy := by
  subst hxy
  have hM : Mx = My := by exact_mod_cast hpx.symm.trans hpy
  subst hM
  rfl

/-- Membership in `dv2SideSet` unpacks `Dv2OnSide` — the level-2 twin of `C133mh14.lean`'s
private `dvOnSide_of_mem'`. -/
private theorem dv2OnSide_of_mem' {F : KeyFrame O π} {H₀ hpin} {L : LevelDatum F H₀ hpin}
    {Ψ f : Polynomial O} {u₂ ℓ₂ j : ℕ} (hj : j ∈ dv2SideSet L Ψ f u₂ ℓ₂) :
    Dv2OnSide L Ψ f u₂ ℓ₂ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (Dv2OnSide L Ψ f u₂ ℓ₂) from hj)).2

/-! ## Part 1 — ★ the transport lemma (charge step 1): non-divisibility of the residual
passes UP through multiplication by a point-sided factor -/

/-- ★ **The point-sided complement transport (F1.2 clause 2's mechanism).**  If `g₂`'s level
residual is not `r`-divisible at every pin and `Wf` is merely POINT-SIDED at `(u, ℓ)`
(no purity, no degree fence — `Wf ≠ 0` suffices), then the residual of `g₂ * Wf` is not
`r`-divisible at every pin.  Route: the unconditional mixed law `C133mh3.dvResPoly_mul_gen`
(Theorem M clause 3, τ = 1) factors `R(g₂·Wf) = R(g₂)·R(Wf)`; the point side makes `R(Wf)`
a nonzero constant (C.26(ii)+(iii)), hence a unit of `K[Z]`; unit cancellation is
`C133mh14.residual_transport`'s divisibility step, run in reverse. -/
theorem notdvd_dvResPoly_mul_pointSided
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {r : Polynomial (F.stageField H₀ hpin)}
    {g₂ Wf : Polynomial O} (hg₂ : g₂ ≠ 0) (hW : Wf ≠ 0)
    (hWpt : ∀ hneW : (dvSideSet F Wf u ℓ).Nonempty, dvSideDeg F Wf u ℓ hneW = 0)
    (hg₂res : ∀ (hne₂ : (dvSideSet F g₂ u ℓ).Nonempty) (M₂ : ℕ)
      (hp₂ : dvHgt F g₂ (dvSideMin F g₂ u ℓ hne₂) = (M₂ : ℕ∞)),
      ¬ r ∣ dvResPoly F H₀ hpin g₂ u ℓ hne₂ M₂ hp₂) :
    ∀ (hne : (dvSideSet F (g₂ * Wf) u ℓ).Nonempty) (M : ℕ)
      (hp : dvHgt F (g₂ * Wf) (dvSideMin F (g₂ * Wf) u ℓ hne) = (M : ℕ∞)),
      ¬ r ∣ dvResPoly F H₀ hpin (g₂ * Wf) u ℓ hne M hp := by
  intro hne M hp hdvd
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  -- pins for the two factors
  have hng : (dvSideSet F g₂ u ℓ).Nonempty := dvSideSet_nonempty F hg₂ u hℓ
  obtain ⟨Mg, hpg⟩ := exists_pin F hng
  have hnW : (dvSideSet F Wf u ℓ).Nonempty := dvSideSet_nonempty F hW u hℓ
  obtain ⟨MW, hpW⟩ := exists_pin F hnW
  -- Theorem M clause 3 (τ = 1, unconditional): `R(g₂·Wf) = R(g₂)·R(Wf)`
  have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin hℓ hcop hfloor hg₂ hW
    hng hnW hne hpg hpW hp
  -- `R(Wf)` is a nonzero constant (C.26(ii)+(iii) at the point side), hence a unit
  have hWnd := natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hnW hpW
  have hW0 : (dvResPoly F H₀ hpin Wf u ℓ hnW MW hpW).natDegree = 0 := by
    rw [hWnd.1, hWpt hnW]
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hW0
  have hc0 : c ≠ 0 := fun h0 => hWnd.2 (by rw [← hc, h0, Polynomial.C_0, Polynomial.coeff_zero])
  obtain ⟨uw, huw⟩ : IsUnit (dvResPoly F H₀ hpin Wf u ℓ hnW MW hpW) := by
    rw [← hc]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  -- `r ∣ R(g₂)·R(Wf)` and `R(Wf)` a unit ⟹ `r ∣ R(g₂)`: contradiction with `hg₂res`
  have hdvd' : r ∣ dvResPoly F H₀ hpin g₂ u ℓ hng Mg hpg
      * dvResPoly F H₀ hpin Wf u ℓ hnW MW hpW := by
    rw [← hmul]; exact hdvd
  refine hg₂res hng Mg hpg ?_
  have hid : dvResPoly F H₀ hpin g₂ u ℓ hng Mg hpg
      = dvResPoly F H₀ hpin g₂ u ℓ hng Mg hpg * dvResPoly F H₀ hpin Wf u ℓ hnW MW hpW
        * (↑uw⁻¹ : Polynomial (F.stageField H₀ hpin)) := by
    rw [← huw, mul_assoc, Units.mul_inv, mul_one]
  rw [hid]
  exact hdvd'.mul_right _

/-! ## Part 2 — clause 2 of the signed F1.2, on the monic-division quotient -/

/-- **Clause 2 of the signed F1.2 `block_complement_notdvd`, landed as its own reusable
lemma**: the quotient's residual is not `L.r`-divisible at every pin.  Route:
`C134frt.context_split_quotient` (the FRT bridge) + `dvResPoly_congr` (pin transport
across `f /ₘ blockFactor L f = g₂ * Wf`) + the transport lemma above. -/
theorem quotient_residual_notdvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {f : Polynomial O} (hctx : BlockContext L f) :
    ∀ (hne' : (dvSideSet F (f /ₘ blockFactor L f) L.u L.ℓ).Nonempty) (M₀' : ℕ)
      (hp' : dvHgt F (f /ₘ blockFactor L f)
          (dvSideMin F (f /ₘ blockFactor L f) L.u L.ℓ hne') = (M₀' : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f) L.u L.ℓ hne' M₀' hp' := by
  obtain ⟨g₂, Wf, hq, hg₂mon, hWmon, hWpt, hg₂res⟩ :=
    C134frt.context_split_quotient L hπ hh hctx
  intro hne' M₀' hp' hdvd
  -- transport the given pin across `hq : f /ₘ blockFactor L f = g₂ * Wf`
  have hnGW : (dvSideSet F (g₂ * Wf) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F (mul_ne_zero hg₂mon.ne_zero hWmon.ne_zero) L.u L.hℓ
  obtain ⟨MGW, hpGW⟩ := exists_pin F hnGW
  rw [dvResPoly_congr F H₀ hpin hq hne' hnGW hp' hpGW] at hdvd
  exact notdvd_dvResPoly_mul_pointSided hπ hh H₀ hpin L.hℓ L.hcop (floor_assoc L)
    hg₂mon.ne_zero hWmon.ne_zero hWpt hg₂res hnGW MGW hpGW hdvd

/-! ## Part 3 — ★ the FULL signed F1.2 -/

/-- ★ **THE SIGNED F1.2 `block_complement_notdvd`** (leanspec `ChapC.lean:1623-1631`,
conclusion byte-as-is; the one binder delta beyond the signed list is `hh : 0 < F.h`, per
`verdict_CFS.md`'s standing convention).  Clause 1 = `C134frt.testKey_dvd_iff_dvd_blockFactor`;
clause 2 = `quotient_residual_notdvd` (this file); clause 3 = `C134frt.quotient_dvSupp_ne_top`. -/
theorem block_complement_notdvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    (∀ Ψ : Polynomial O, IsTestKey L Ψ → (Ψ ∣ blockFactor L f ↔ Ψ ∣ f)) ∧
    (∀ (hne' : (dvSideSet F (f /ₘ blockFactor L f) L.u L.ℓ).Nonempty) (M₀' : ℕ)
      (hp' : dvHgt F (f /ₘ blockFactor L f)
          (dvSideMin F (f /ₘ blockFactor L f) L.u L.ℓ hne') = (M₀' : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f) L.u L.ℓ hne' M₀' hp') ∧
    dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤ :=
  ⟨fun _ hΨ => C134frt.testKey_dvd_iff_dvd_blockFactor L hπ hh hctx hΨ,
   quotient_residual_notdvd L hπ hh hctx,
   C134frt.quotient_dvSupp_ne_top L hπ hh hctx⟩

/-! ## Part 4 — ★ F1.7 `dv2_length_sum`, landed on re-attempt -/

/-- ★ **THE SIGNED F1.7 `dv2_length_sum`** (leanspec `ChapC.lean:2320-2328`, conclusion
byte-as-is; `hh` delta as above).  The signed statement is about `blockFactor L f` ALONE, so
no translation identity (F1.3) is needed, contra the CFS/FRT chaining:
clause 1 — `dev Ψ (blockFactor L f) 0 = blockFactor L f %ₘ Ψ ≠ 0` since `¬ Ψ ∣ blockFactor L f`
(`hnd`) and `Ψ` is monic, then `C130s6.dvSupp_ne_top_of_ne_zero`;
clause 2 — the top `Ψ`-digit of the monic block of exact degree `mult₂ · deg Ψ`
(`C134cfs.blockDeg_eq` + `IsTestKey`'s degree conjunct) is `1` (`dev_top_eq_one`, C130in),
and the unit's cleared support is `0` (`C133mh9.dvSupp_one`);
clause 3 — any abscissa `j > mult₂` has `dev Ψ (blockFactor L f) j = 0`
(`dev_eq_zero_of_lt`, B.04), so its pin is `⊤` (`C130s6.dvSupp_zero_eq_top`), violating
`Dv2OnSide`'s finiteness guard; hence every on-side abscissa is `≤ mult₂` and so is the max. -/
theorem dv2_length_sum {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f) :
    dv2Pin L Ψ (blockFactor L f) 0 ≠ ⊤ ∧
    dv2Pin L Ψ (blockFactor L f) (mult₂ L f) = (0 : ℕ∞) ∧
    ∀ u₂ ℓ₂ : ℕ, 0 < ℓ₂ → ℓ₂ * L.seam < u₂ →
      ∀ hne : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty,
        dv2SideMax L Ψ (blockFactor L f) u₂ ℓ₂ hne ≤ mult₂ L f := by
  have hbfmon : (blockFactor L f).Monic := (C134cfs.hasLabel_blockFactor L hπ hh hctx).1
  have hbdeg : (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f :=
    C134cfs.blockDeg_eq L hπ hh hctx
  have hm2 : 0 < mult₂ L f := C134cfs.mult₂_pos L hπ hh hctx
  have hΨmon : Ψ.Monic := hΨ.1
  have hΨdeg : Ψ.natDegree = L.keyDeg₂ := hΨ.2.1
  have hΨd : 0 < Ψ.natDegree := by rw [hΨdeg]; exact keyDeg₂_pos L
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1: `dev Ψ (blockFactor L f) 0 = blockFactor L f %ₘ Ψ ≠ 0` since `¬ Ψ ∣ ⋯`
    have hne0 : dev Ψ (blockFactor L f) 0 ≠ 0 := fun h0 =>
      hnd ((Polynomial.modByMonic_eq_zero_iff_dvd hΨmon).mp h0)
    show dvSupp F (dev Ψ (blockFactor L f) 0) L.u L.ℓ ≠ ⊤
    exact C130s6.dvSupp_ne_top_of_ne_zero F L.u L.ℓ hne0
  · -- clause 2: the monic top digit is `1`, and the unit's cleared support is `0`
    have hdevtop : dev Ψ (blockFactor L f) (mult₂ L f) = 1 :=
      dev_top_eq_one hΨmon hΨd hbfmon hm2 (by rw [hbdeg, hΨdeg, mul_comm])
    show dvSupp F (dev Ψ (blockFactor L f) (mult₂ L f)) L.u L.ℓ = 0
    rw [hdevtop]
    exact C133mh9.dvSupp_one F L.u L.ℓ
  · -- clause 3: past `mult₂` the digit vanishes, so its pin is `⊤`, off the side
    intro u₂ ℓ₂ hℓ₂ hseam hne
    refine Finset.max'_le _ hne _ fun j hj => ?_
    by_contra hgt'
    have hgt : mult₂ L f < j := not_le.mp hgt'
    have harith : (blockFactor L f).natDegree < j * Ψ.natDegree := by
      rw [hbdeg, hΨdeg, mul_comm j L.keyDeg₂]
      exact mul_lt_mul_of_pos_left hgt (keyDeg₂_pos L)
    have hdev : dev Ψ (blockFactor L f) j = 0 :=
      dev_eq_zero_of_lt hΨmon hΨd _ j harith
    have htop : dv2Pin L Ψ (blockFactor L f) j = ⊤ := by
      show dvSupp F (dev Ψ (blockFactor L f) j) L.u L.ℓ = ⊤
      rw [hdev]
      exact C130s6.dvSupp_zero_eq_top F L.u L.hℓ
    exact (dv2OnSide_of_mem' hj).2 htop

/-! ## Re-attempt record — F1.3–F1.6 BLOCKED-BECAUSE (exact subgoals); F1.8 out of scope

None of the four signed statements below is declared as a `theorem`, `axiom`, or `sorry`,
per the C.33/C.34/C.40 convention.  Each was re-examined against the NEW landed pieces
(the mixed law `C133mh3.dvResPoly_mul_gen` and this file's transport); the remaining
blocks are LEVEL-TWO and the level-one mixed law does not touch them.

### F1.3 `dv2Supp_translation` (leanspec `ChapC.lean:1635-1641`) — BLOCKED

The F1.2 leg of FRT's block is now CLEARED (landed above).  What remains is exactly the
level-two multiplicative structure, and it is TWO missing statements, not one:

1. **A frame-generic `Dv2ResSurv L Ψ u₂ ℓ₂` discharge.**  The landed level-two product
   laws (`C132nv2.dv2Supp_mul_of_endpoint_le`, `dv2Supp_add_le_dv2Supp_mul`,
   `dv2OnSide_mul_endpoint`) all carry the survival hypothesis
   `Dv2ResSurv L Ψ u₂ ℓ₂` (`C132nv2.lean:227` — "reduction modulo `Ψ` preserves the
   product's `dv2Hgt` value at slot 0, and slot 1 sits strictly above the line").  Its
   only landed discharge is the S2 NUMERIC instance
   `C132nv4.s2_dv2ResSurv_at_21 : Dv2ResSurv ((s2Tower h2 hq).levelDatum h2)
   (s2DepthTwoKeyAt h2 hq 2) 21 2` — nothing frame-generic exists
   (`C132nv3b.lean`'s header: slot-1 "BLOCKED at `(5,2)`", discharged only via the μ₂
   normalized residual product at M3-NV3).
2. **The complement's `dv2`-profile collapse (`dv2Pin_mul_complement`, the no-interaction
   lemma — still unwritten, plan sizing 70-120 lines).**  Even GIVEN the product law,
   F1.3's right-hand side is `+ ℓ₂ • complementConst L f`, i.e. the complement
   `g := f /ₘ blockFactor L f` must contribute the CONSTANT
   `(dvSupp F g L.u L.ℓ).toNat` — which requires its level-two side data to collapse to
   the single abscissa `0` with pin value `complementConst L f`
   (`dv2Pin L Ψ g 0 = dvSupp F (g %ₘ Ψ) L.u L.ℓ` vs `dvSupp F g L.u L.ℓ`: relating these
   IS the interaction analysis; nothing landed relates `dvSupp` of `g %ₘ Ψ` to `dvSupp`
   of `g`).  This is `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`'s NV-chain
   continuation, genuinely new mathematics, out of this unit's combine-landed-pieces scope.

### F1.4 `dv2ResPoly_scalar` (leanspec `ChapC.lean:1714-1724`) — BLOCKED

Needs F1.3's translated pin (blocked above) plus the cocycle telescope on the per-slot
`dv2Res` reads — the same level-two digit analysis, one refinement deeper.  No
independent route: the conclusion equates `dv2ResPoly` values whose side data F1.3 would
supply.

### F1.5 `dv2ResPoly_radical_eq` (leanspec `ChapC.lean:1689-1699`) — BLOCKED

A unit-scalar cancellation over `K₂` applied to F1.4's identity (blocked).  Its degree
clause alone would still need F1.6's side-degree equality (blocked below).

### F1.6 `mult₂_readable` (leanspec `ChapC.lean:2307-2315`) — BLOCKED

The conclusion (`dv2SideMin`/`dv2SideDeg` agree between `f` and `blockFactor L f`) is
the translation identity read at the two minimizers: a constant vertical shift of the
level-2 polygon preserves the side data.  This is F1.3's mechanism verbatim; no route
avoids it.  (This file's F1.7 does NOT go through F1.6 — the signed F1.7 mentions only
`blockFactor L f`, whose polygon needs no translation.)

### F1.8 `level2_peel` — OUT OF SCOPE (per the charge)

Unchanged from `C40.lean`'s standing analysis, re-confirmed by FRT (2026-08-28): clause
(ii) needs C.61's `tier1_typeOf` at general `L.ℓ` (landed only at `ℓ = 1`); clause (iii)
sits on leanspec defect D13.  Orthogonal to both the split export and the mixed law.
-/

end Uniformity.Density.Tower.C134f12c

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134f12c.notdvd_dvResPoly_mul_pointSided
#print axioms Uniformity.Density.Tower.C134f12c.quotient_residual_notdvd
#print axioms Uniformity.Density.Tower.C134f12c.block_complement_notdvd
#print axioms Uniformity.Density.Tower.C134f12c.dv2_length_sum

end AxCheck
