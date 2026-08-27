/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C80 -- s2Tower (needed directly; not reached transitively — see MADJ_probe)
import Uniformity.ChapC.C132nv2
import Uniformity.ChapC.C132nv3b

/-!
# Uniformity.ChapC.C132nv4 — the `s2Hgt₃` product law at `(u₃,ℓ₃) = (21,2)` (μ₃ campaign, node M3-NV4)

**[M3-NV4, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV4):
assembles `s2Hgt₃ (g·h) = s2Hgt₃ g + s2Hgt₃ h`, the zero cases, and the endpoint-minimizer
corollaries, at the S2 instance `L := (s2Tower h2 hq).levelDatum h2`,
`Φ₂ := s2DepthTwoKeyAt h2 hq 2`, OUTER pair `(u₂, ℓ₂) = (21, 2)` (the numeral M3-NV1 fixes
for `s2Hgt₃`). This is the exact mechanism `leanfinal/scratch/MADJ_probe.lean` machine-pinned
(green): C132nv3b's two landed `Dv2ResSurv` clauses, both proved at `(21,2)`, assemble into
the survival package, which fires C132nv2's "NV-4 consumption shape" endpoint theorem, whose
carrier unfold IS the advertised product law.

**Precision (per `runs/wave-b/verdict_MADJ.md`)**: the outer pair is `(21,2)` EVERYWHERE in
this file. The `(u₂,ℓ₂) = (5,2)` read that appears inside `dv2Hgt L` (via C132nv3b) is the
INNER μ₂ layer — a different parameter slot on a different object; the two must never be
conflated, and this file never states anything at `(5,2)`.

## What lands

* `s2_dv2ResSurv_at_21` — the survival package `Dv2ResSurv L Φ₂ 21 2`, UNCONDITIONAL, built
  from C132nv3b's `dv2Hgt_dev_composedKey_mod_eq` (slot-0 equality) and
  `s2_dv2ResSurv_slot1_at_21` (slot-1 strict carry bound, the one that closes at `(21,2)`
  though NOT at `(5,2)` — see C132nv3b's own honesty note).
* `s2_dv2Supp_mul_at_21` — the endpoint product law for the raw `dv2Supp` table, firing
  C132nv2's `dv2Supp_mul_eq_add_of_endpoint_le` through the survival package above.
* `s2Hgt₃_mul` — the CARRIER form (the row's advertised statement): `s2Hgt₃ (g·z) =
  s2Hgt₃ g + s2Hgt₃ z`, read off `s2_dv2Supp_mul_at_21` through `toZ_add`.
* `s2Hgt₃_zero_mul` / `s2Hgt₃_mul_zero` — the zero cases, proved DIRECTLY (not via
  `s2Hgt₃_mul`: a zero factor has no nonempty `dv2SideSet`, so the conditional law above does
  not reach it) from `s2Hgt₃_zero` and `WithTop`'s `⊤`-absorbing addition.
* `s2_dv2OnSide_mul_endpoint_at_21` / `s2_dv2SideMin_mul_le_at_21` — the endpoint-minimizer
  corollaries (mirror of the old S2 level-two assembly shape, `C130nv3.lean:557-582`):
  C132nv2's generic `dv2OnSide_mul_endpoint`/`dv2SideMin_mul_le` fired at `Φ₂`, `(21,2)`,
  through the same survival package.

## What this node does NOT claim (honesty scope)

No UNCONDITIONAL (all-`g,z`) product law for `s2Hgt₃` — `s2_dv2Supp_mul_at_21`/`s2Hgt₃_mul`
keep the side-set-nonemptiness and finite-pin hypotheses exactly as the probe stated them
(`hng`, `hnz`, `hHg`, `hHz`); no `dv2SideSet_nonempty`-style unconditional existence fact is
derived here (that is not this node's job, per the orchestrator's brief). Nothing at `(5,2)`
is stated.

**DEPENDS.** C132nv2 (`Dv2ResSurv`, `dv2Supp`/`dv2SideSet`/`dv2SideMin`/`dv2Pin` bank,
`dv2Supp_mul_eq_add_of_endpoint_le`, `dv2OnSide_mul_endpoint`, `dv2SideMin_mul_le`) ·
C132nv3b (`dv2Hgt_dev_composedKey_mod_eq`, `s2_dv2ResSurv_slot1_at_21`) · C132nv1 (`s2Hgt₃`,
`s2Hgt₃_zero`, `s2Φ₂_monic`, `s2Φ₂_natDegree`) · C130nv (`toZ_add`) · C80 (`s2Tower`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no statement invented beyond the
row's sketch and the probe's machine pin.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2_dv2ResSurv_at_21`, `s2_dv2Supp_mul_at_21`, `s2Hgt₃_mul`, `s2Hgt₃_zero_mul`,
`s2Hgt₃_mul_zero`, `s2_dv2OnSide_mul_endpoint_at_21`, `s2_dv2SideMin_mul_le_at_21`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130nv (toZ_add)
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C132nv3b
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the survival package `Dv2ResSurv L Φ₂ 21 2`, UNCONDITIONAL -/

/-- ★ **The survival package at the outer pair `(21,2)`**: the two landed C132nv3b clauses
(slot-0 equality, slot-1 strict carry bound — both closing at `21`, unlike the blocked
`(5,2)` inner read) assemble directly into `Dv2ResSurv`. -/
theorem s2_dv2ResSurv_at_21 :
    Dv2ResSurv ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 := by
  intro A B Ha Hb hA hB hHa hHb
  exact ⟨dv2Hgt_dev_composedKey_mod_eq h2 hq hA hB hHa hHb,
    s2_dv2ResSurv_slot1_at_21 h2 hq hA hB hHa hHb⟩

/-! ## Part 2 — the endpoint product law for `dv2Supp`, at `(21,2)` -/

/-- ★ **The `dv2Supp` endpoint product law at `(21,2)`**: C132nv2's "NV-4 consumption shape"
endpoint theorem, fired through the survival package above. -/
theorem s2_dv2Supp_mul_at_21 {g z : Polynomial O}
    (hng : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2).Nonempty)
    (hnz : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 hnz) = (Hz : ℕ∞)) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2 =
      dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 +
        dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 :=
  dv2Supp_mul_eq_add_of_endpoint_le ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
    (s2_dv2ResSurv_at_21 h2 hq) hng hnz hHg hHz

/-! ## Part 3 — the carrier form: the `s2Hgt₃` product law (the row's advertised statement) -/

/-- ★ **NODE NV-4's row**: `s2Hgt₃ (g·z) = s2Hgt₃ g + s2Hgt₃ z`, the μ₃ analogue of
`C130nv3.s2Hgt₂_mul` one level up, given the survival-derived side-set/pin data. -/
theorem s2Hgt₃_mul {g z : Polynomial O}
    (hng : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2).Nonempty)
    (hnz : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 hnz) = (Hz : ℕ∞)) :
    s2Hgt₃ h2 hq (g * z) = s2Hgt₃ h2 hq g + s2Hgt₃ h2 hq z := by
  rw [s2Hgt₃, s2Hgt₃, s2Hgt₃, ← toZ_add]
  exact congrArg toZ (s2_dv2Supp_mul_at_21 h2 hq hng hnz hHg hHz)

/-! ## Part 4 — zero cases (unconditional; a zero factor has no nonempty `dv2SideSet`, so
these do NOT follow from `s2Hgt₃_mul` above and are proved directly). -/

/-- **zero case, left**: `s2Hgt₃ (0·z) = s2Hgt₃ 0 + s2Hgt₃ z` — the `⊤`-absorbing zero case
fires directly off `s2Hgt₃_zero`, no side-set fence needed. -/
theorem s2Hgt₃_zero_mul (z : Polynomial O) :
    s2Hgt₃ h2 hq ((0 : Polynomial O) * z) = s2Hgt₃ h2 hq 0 + s2Hgt₃ h2 hq z := by
  rw [zero_mul, s2Hgt₃_zero, top_add]

/-- **zero case, right**: `s2Hgt₃ (g·0) = s2Hgt₃ g + s2Hgt₃ 0` — the mirrored `⊤`-absorbing
case. -/
theorem s2Hgt₃_mul_zero (g : Polynomial O) :
    s2Hgt₃ h2 hq (g * (0 : Polynomial O)) = s2Hgt₃ h2 hq g + s2Hgt₃ h2 hq 0 := by
  rw [mul_zero, s2Hgt₃_zero, add_top]

/-! ## Part 5 — endpoint-minimizer corollaries at `(21,2)` (mirror of the old S2 level-two
assembly shape, `C130nv3.lean:557-582`, fired through the survival package above). -/

/-- **The endpoint is a product minimizer at `(21,2)`**: the sum of the chosen minimizers of
`g` and `z` is on the side of `g·z`. -/
theorem s2_dv2OnSide_mul_endpoint_at_21 {g z : Polynomial O}
    (hng : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2).Nonempty)
    (hnz : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 hnz) = (Hz : ℕ∞)) :
    Dv2OnSide ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 hng
        + dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 hnz) :=
  dv2OnSide_mul_endpoint ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
    (s2_dv2ResSurv_at_21 h2 hq) hng hnz hHg hHz

/-- **The product's chosen minimizer is bounded by the sum of the factors' minimizers, at
`(21,2)`.** -/
theorem s2_dv2SideMin_mul_le_at_21 {g z : Polynomial O}
    (hng : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2).Nonempty)
    (hnz : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z
      (dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 hnz) = (Hz : ℕ∞))
    (hne : (dv2SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (g * z) 21 2).Nonempty) :
    dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2 hne
      ≤ dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2 hng
        + dv2SideMin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 hnz :=
  dv2SideMin_mul_le ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
    (s2_dv2ResSurv_at_21 h2 hq) hng hnz hHg hHz hne

end Uniformity.Density.Tower.C132nv4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv4.s2_dv2ResSurv_at_21
#print axioms Uniformity.Density.Tower.C132nv4.s2_dv2Supp_mul_at_21
#print axioms Uniformity.Density.Tower.C132nv4.s2Hgt₃_mul
#print axioms Uniformity.Density.Tower.C132nv4.s2Hgt₃_zero_mul
#print axioms Uniformity.Density.Tower.C132nv4.s2Hgt₃_mul_zero
#print axioms Uniformity.Density.Tower.C132nv4.s2_dv2OnSide_mul_endpoint_at_21
#print axioms Uniformity.Density.Tower.C132nv4.s2_dv2SideMin_mul_le_at_21

end AxCheck
