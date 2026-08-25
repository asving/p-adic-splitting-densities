/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Uniformity.ChapC.C130nv5
import Uniformity.ChapC.C130s17

/-!
# Uniformity.ChapC.C130np0 — S2-source plan node NP-0

**S2-source plan node NP-0** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row NP-0
"points and evaluation"): construct, at the S2 tower with evaluation ambient
`E = FractionRing (Polynomial O)`, the point/evaluation side of SF1's re-typed
`SplitNodePointSource` (C130s17): the `Point`/`Pt` carrier and `point_exists`, `coeffHom`,
`coord`, `valueOn`, `pointHgt`, and the evaluation/value laws — each in its exact field
shape, `#print axioms` Lean-core.

## The one genuine design discovery of this node (read before consuming `valueOn`)

The interface's `slot_value` and `key_value` laws JOINTLY pin what the stage-1 valuation
must be, and it is NEITHER landed extension:

* `slot_value` at `i = 1` ties `pointHgt 1` to the stage-1 table (`s2Hgt₁`, NP-1) on
  `natDegree < Dcum 1 = 2`;
* `key_value` at the gauge-live index `i = 1` demands
  `pointHgt 1 x (keyAt 1) = u₂ = 5`, while `s2Hgt₁ (keyAt 1) = s2Hgt₁ (x² − 2) = 2` — so
  `valueOn 1` CANNOT be NV-6's `s2AddEVal₁` (the `s2Hgt₁` extension);
* the terminal table gives `s2Hgt₂ (C 2) = 4 ≠ 2 = s2Hgt₁ (C 2)` on the live slot — so
  `valueOn 1` cannot be `s2AddEVal₂` either.

The valuation that satisfies BOTH is the MacLane augmentation `[μ₁; Φ′ : 5]` — in the
landed carrier, the `(u, ℓ) = (5, 1)`-cleared development support

  `s2PHgt₁ A := toZ (dvSupp (s2Frame h2 hq) A 5 1)` ,

which agrees with `s2Hgt₁` on `natDegree < 2` (the development is a single coefficient,
`s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt`) and reads `5` on the frame key (`s2PHgt₁_key`).  This
file constructs it, proves its full valuation bank — the product law assembles from the
SAME generic NV-2 endpoint machinery and the SAME parameter-free NV-3 S2 survival core
(`s2_stageHeight_mul_modByMonic_le`), only the admissibility numerals change
(`1·2 < 5` for `2·2 < 5`) — packages it as an `AddValuation`, and extends it to
`E = FractionRing (Polynomial O)` exactly as NV-5/NV-6 did for the two table values
(mirror of C130nv5, with the same restriction PIN `s2AddEPVal₁_algebraMap`).

`valueOn` is then stage-indexed:
`valueOn i = s2AddEPVal₁` (the `[μ₁; Φ′ : 5]` extension) for `i ≤ 1`, and NV-6's landed
`s2AddEVal₂` (the `s2Hgt₂` extension) for `i ≥ 2`.  Both are genuine `AddValuation`s on
`E`, so all four `valueOn` laws (`value_zero/mul/add_ge/add_eq`) hold UNFENCED (∀ i), with
the `StageLive`-fenced field shapes as corollaries.

## Points, coordinates, and the evaluation laws

* `S2NPPoint := Unit` — the single canonical S2 evaluation point (plan §5.1: a point is a
  chosen valuation/evaluation pair; here the pair is canonical and the stage dependence
  lives in `valueOn`).  `coeffHom`/`coord` REUSE C130s17's SF-4 probe pair verbatim:
  `s2NPCoeffHom := s2EvalHom` (constants through `Polynomial.C`, injective —
  `s2EvalHom_injective`), `s2NPCoord _ := s2EvalCoord` (the rational-function variable).
* The BRIDGE (`s2NP_eval₂_eq_algebraMap`): at this pair, `eval₂ coeffHom (coord x)` IS the
  canonical embedding `algebraMap (Polynomial O) E` — so NV-6's restriction pins convert
  every point read into a landed polynomial value: `pointHgt 1 x A = s2PHgt₁ A` and
  `pointHgt 2 x A = s2Hgt₂ A`, for ALL `A` (`s2NPPointHgt_one`/`_two`), strictly stronger
  than the slot-fenced field shapes.
* `s2NPPt i x` — stage legality, packaging the VALUE EQUATIONS as plan §5.1 directs (no
  unproved `True`): at gauge-live `i` the exact key value `u_{i+1}`, at every `i` the key
  finiteness.  `point_exists` at the two live stages is then a THEOREM: at `i = 1` the
  key-value computation `s2PHgt₁ (Φ′) = 5 = u₂`; at `i = 2` terminal-key finiteness.
* Field-shaped laws proved here: `point_exists`, `pointHgt_eval` (`rfl`), all four
  `value_*` laws, `slot_value` (BOTH live levels, against the intended table
  `s2NPHgt = s2Hgt₁ / s2Hgt₂` — plan row NP-2's slot half, already dischargeable here),
  `key_value` (gauge level 1, NP-2's other half), and the finiteness half of `window`.
* Teeth: the EXACT slot U13's refuter fired on, now finite and stage-graded —
  `pointHgt 2 x (C 2) = 4` and `pointHgt 1 x (C 2) = 2` — and the key reads
  `pointHgt 1 x (keyAt 1) = 5`, `pointHgt 2 x (C 2) ≠ ⊤`.

## What this node does NOT deliver (named per plan row)

* `pointDig`/`slot_digit`/`dig_add` at the point: **NP-3** (needs RP-2's actual residual
  reads; a free copy of the digit table is explicitly disallowed by the plan).
* `thresholdZ`/`thresholdNat`/`threshold_nonneg` and the threshold half of `window`:
  **NP-4/NP-5** (no source occurrence names the inherited S2 threshold; choosing a
  convenient numeral would be circular — plan §5.1).  The finiteness half is here.
* `ambientLetter`/`psi_root`/`canonicalRead`/`arenaRead`/`towerRead`/`peelUnit`:
  **NP-6/NP-7/NP-8** (residue-ambient side, not evaluation).
* The `hgt`/`dig`/`Full`/`lift` STAGE-LAW banks: landed per level (C130nv + C130np1 at
  level 1, C130s6 at level 2); the `i`-indexed fencing is SG-0 assembly.
* No `SplitNodePointSource` instance is claimed — that is SG-0, after NP-4..NP-8.

**DEPENDS.** C130s17 (`SplitNodePointSource` — the target shapes; `s2EvalHom`,
`s2EvalCoord`, `s2RepositoryRealization`) · C130nv5 (`s2AddEVal₂` + `s2AddEVal₂_algebraMap`
— the stage-2 extension and PIN; the NV-5/NV-6 packaging pattern mirrored here) · C130nv3
(`stageHeight_dev_endpoint_le_of_surv`, `s2_stageHeight_mul_modByMonic_le` — the generic
endpoint theorem and the parameter-free S2 survival core) · C130nv2 (the generic `(u, ℓ)`
endpoint assembly bank, `s2_h_pos`, `s2_stageHeight_key`, `dev_one_of_natDegree_lt`,
`dev_zero_pin`) · C130s6 (`dvSupp` generic law bank, `s2Hgt₂` + teeth, `toZ` dictionary) ·
C130nv (`s2Hgt₁` + bank + teeth) · C130s2 (`s2DepthTwo`, key chain, `Dcum` numerals) ·
C.34 (`dvSideSet_nonempty`) · C.43/C.47 (`composedKey`, monicity, via the key chain) ·
mathlib (`AddValuation` laws incl. `map_add_of_distinct_val`,
`Valuation.extendToLocalization` + pin, `Polynomial.hom_eval₂`, `Polynomial.eval₂_C_X`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched;
new file only — no other unit's file edited.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Leaf.GateKit
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3 Uniformity.Density.Tower.C130nv5
open Uniformity.Density.Tower.C130s17

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — the stage-1 POINT valuation: the MacLane augmentation `[μ₁; Φ′ : 5]`

The `(5, 1)`-cleared development support.  On `natDegree < 2` the development is the single
coefficient `A` itself, so this value IS `s2Hgt₁` there; on the frame key it reads the
tower height `u₂ = 5`.  This is the UNIQUE normalization satisfying both the `slot_value`
tie to NP-1's level-one table and the `key_value` demand at the gauge-live index. -/

/-- **The stage-1 point value** — the `(u, ℓ) = (5, 1)`-cleared `Φ′`-development support,
i.e. the MacLane augmentation `[μ₁; Φ′ : 5]` of the level-one value, in E.10's `WithTop ℤ`
carrier. -/
noncomputable def s2PHgt₁ (A : Polynomial O) : WithTop ℤ :=
  toZ (dvSupp (s2Frame h2 hq) A 5 1)

/-- Anti-drift pin: `s2PHgt₁` IS `dvSupp` at `(5, 1)` — nothing fresh. -/
theorem s2PHgt₁_eq_dvSupp (A : Polynomial O) :
    s2PHgt₁ h2 hq A = toZ (dvSupp (s2Frame h2 hq) A 5 1) := rfl

/-- `value_zero` at the polynomial level. -/
theorem s2PHgt₁_zero : s2PHgt₁ h2 hq (0 : Polynomial O) = ⊤ := by
  rw [s2PHgt₁, dvSupp_zero_eq_top _ _ (by norm_num), toZ_top]

/-- Nonzero polynomials have finite stage-1 point value. -/
theorem s2PHgt₁_ne_top {A : Polynomial O} (hA : A ≠ 0) : s2PHgt₁ h2 hq A ≠ ⊤ := by
  rw [s2PHgt₁, ne_eq, toZ_eq_top_iff]
  exact dvSupp_ne_top_of_ne_zero (s2Frame h2 hq) 5 1 hA

/-- The finiteness iff. -/
theorem s2PHgt₁_eq_top_iff {A : Polynomial O} : s2PHgt₁ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro h
    by_contra hA
    exact s2PHgt₁_ne_top h2 hq hA h
  · rintro rfl
    exact s2PHgt₁_zero h2 hq

/-- The ultrametric inequality. -/
theorem s2PHgt₁_add_ge (A B : Polynomial O) :
    min (s2PHgt₁ h2 hq A) (s2PHgt₁ h2 hq B) ≤ s2PHgt₁ h2 hq (A + B) := by
  rw [s2PHgt₁, s2PHgt₁, s2PHgt₁, ← toZ_min]
  exact toZ_le_toZ_iff.mpr (min_dvSupp_le_dvSupp_add (s2Frame h2 hq) (by norm_num) A B)

/-! ### 1a. The small-degree dictionary: below the key degree, `dvSupp` is the bare
`ℓ`-cleared stage height — hence `s2PHgt₁ = s2Hgt₁` on the level-one slot range. -/

/-- **Small-degree read, generic in `(u, ℓ)`**: below the key degree the development is the
single coefficient `A`, so `dvSupp F A u ℓ = ℓ • dv(A)`. -/
theorem s2_dvSupp_of_natDegree_lt {u ℓ : ℕ} (hℓ : 0 < ℓ) {A : Polynomial O}
    (hA : A.natDegree < 2) :
    dvSupp (s2Frame h2 hq) A u ℓ = ℓ • (s2Frame h2 hq).stageHeight A := by
  have hkd : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [C35b.key_eq h2 hq]; exact s2Key_natDegree
  have hdeg : A.degree < ((s2Frame h2 hq).key : Polynomial O).degree := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    rw [Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero, hkd]
    exact_mod_cast hA
  have hmod : A %ₘ (s2Frame h2 hq).key = A :=
    (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).2 hdeg
  have hdev1 : dev (s2Frame h2 hq).key A 1 = 0 := by
    rw [dev_one_of_natDegree_lt (s2Frame h2 hq) (by rw [hkd]; omega)]
    exact (Polynomial.divByMonic_eq_zero_iff (s2Frame h2 hq).hmonic).2 hdeg
  rw [dvSupp_eq_inf_range (s2Frame h2 hq) hℓ A (M := 2) hA,
    show Finset.range 2 = {0, 1} by decide, Finset.inf_insert, Finset.inf_singleton,
    dvHgt, dvHgt, dev_zero_pin, hmod, hdev1, KeyFrame.stageHeight_zero,
    C118a.smul_top_pos hℓ, top_add, min_eq_left le_top, Nat.cast_zero, mul_zero, add_zero]

/-- ★ **The stage-1 SLOT DICTIONARY**: on the level-one slot range (`natDegree < Dcum 1 =
2`) the point value IS NP-1's level-one table value `s2Hgt₁` — the `slot_value` tie at
`i = 1`, in the strongest form. -/
theorem s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt {A : Polynomial O} (hA : A.natDegree < 2) :
    s2PHgt₁ h2 hq A = s2Hgt₁ h2 hq A := by
  rw [s2PHgt₁, s2_dvSupp_of_natDegree_lt h2 hq (by norm_num) hA, one_nsmul]
  exact (s2Hgt₁_eq_stageHeight h2 hq A).symm

/-- `value_one` in `AddValuation.of`'s exact `h1` shape. -/
theorem s2PHgt₁_one_eq_zero : s2PHgt₁ h2 hq (1 : Polynomial O) = 0 := by
  rw [s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt h2 hq
      (by rw [Polynomial.natDegree_one]; norm_num),
    s2Hgt₁_one h2 hq]
  rfl

/-- **tooth**: the stage-1 point value of the DVR constant `2` is the level-one value `2`
(NOT the terminal table's `4` — the stage grading is real). -/
theorem s2PHgt₁_C_two : s2PHgt₁ h2 hq (Polynomial.C (2 : O)) = ((2 : ℤ) : WithTop ℤ) := by
  rw [s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt h2 hq
      (by rw [Polynomial.natDegree_C]; norm_num),
    s2Hgt₁_C_two h2 hq]

/-! ### 1b. The key value: `s2PHgt₁ (Φ′) = 5 = u₂` — the augmentation reads the tower
height on its own key (the `key_value` computation at the gauge-live index). -/

/-- `stageHeight 1 = 0` at the S2 frame (local copy of C130s6's private helper). -/
private theorem sh_one' : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], C35b.sh_C h2 hq]
  simp

/-- `1 %ₘ Φ′ = 1` (degree `0 < 2`; local copy of C130s6's private helper). -/
private theorem one_mod_key' : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, C35b.key_eq h2 hq, C35b.s2Key_deg]; norm_num)

/-- `1 /ₘ Φ′ = 0` (degree `0 < 2`; local copy of C130s6's private helper). -/
private theorem one_div_key' : (1 : Polynomial O) /ₘ (s2Frame h2 hq).key = 0 :=
  (Polynomial.divByMonic_eq_zero_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, C35b.key_eq h2 hq, C35b.s2Key_deg]; norm_num)

/-- ★ **The key value**: `s2PHgt₁ (Φ′) = 5 = u₂` — the exact `key_value` read at the
gauge-live index (mirror of C130s6's `s2Hgt₂_key` computation, at side `(5, 1)`). -/
theorem s2PHgt₁_key :
    s2PHgt₁ h2 hq ((s2Frame h2 hq).key : Polynomial O) = ((5 : ℤ) : WithTop ℤ) := by
  have hdev0 : dev (s2Frame h2 hq).key ((s2Frame h2 hq).key) 0 = 0 := by
    have h := dev_mul_pow_of_lt (s2Frame h2 hq).hmonic 1 1 0 Nat.one_pos
    rwa [one_mul, pow_one] at h
  have hdev1 : dev (s2Frame h2 hq).key ((s2Frame h2 hq).key) 1 = 1 := by
    have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (1 : Polynomial O) 0
    rw [Nat.add_zero, one_mul, pow_one] at h
    rw [h]
    exact one_mod_key' h2 hq
  have hdev2 : dev (s2Frame h2 hq).key ((s2Frame h2 hq).key) 2 = 0 := by
    have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (1 : Polynomial O) 1
    rw [show (1 : ℕ) + 1 = 2 from rfl, one_mul, pow_one] at h
    rw [h]
    show ((1 : Polynomial O) /ₘ (s2Frame h2 hq).key) %ₘ (s2Frame h2 hq).key = 0
    rw [one_div_key' h2 hq, Polynomial.zero_modByMonic]
  have hdeg : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [(s2Frame h2 hq).hdeg, C35b.e1_eq h2 hq, C35b.f1_eq h2 hq]
  have hval : dvSupp (s2Frame h2 hq) ((s2Frame h2 hq).key) 5 1 = ((5 : ℕ) : ℕ∞) := by
    rw [dvSupp, hdeg, show Finset.range (2 + 1) = {0, 1, 2} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton, dvHgt, dvHgt, dvHgt,
      hdev0, hdev1, hdev2, sh_one' h2 hq, KeyFrame.stageHeight_zero,
      C118a.smul_top_pos (by norm_num), top_add, top_add, min_eq_right le_top,
      min_eq_left le_top]
    simp
  rw [s2PHgt₁, hval, toZ_coe]
  norm_num

/-! ## Part 2 — the `(5, 1)` product law

Assembled from the SAME generic NV-2 endpoint bank and the SAME parameter-free NV-3 S2
survival core as the landed `(5, 2)` law; only the admissibility numerals change
(`ℓ·dv(Φ′) = 1·2 < 5`, strictly, so the strict bank fires too). -/

/-- The endpoint survival at side `(5, 1)` (mirror of C130nv3's `s2_endpoint_dev_le`; the
survival core `s2_stageHeight_mul_modByMonic_le` carries no `(u, ℓ)` parameters). -/
theorem s2P_endpoint_dev_le {g z : Polynomial O}
    (hng : (dvSideSet (s2Frame h2 hq) g 5 1).Nonempty)
    (hnz : (dvSideSet (s2Frame h2 hq) z 5 1).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 1 hng) = (Hg : ℕ∞))
    (hHz : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 1 hnz) = (Hz : ℕ∞)) :
    (s2Frame h2 hq).stageHeight (dev (s2Frame h2 hq).key (g * z)
        (dvSideMin (s2Frame h2 hq) g 5 1 hng + dvSideMin (s2Frame h2 hq) z 5 1 hnz))
      ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  refine stageHeight_dev_endpoint_le_of_surv h2 (s2Frame h2 hq) (s2_h_pos h2 hq)
    (by norm_num) (s2_stageHeight_key h2 hq) (by norm_num) hng hnz hHg hHz ?_
  have hg0 : dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 1 hng) ≠ 0 := by
    intro h0
    have htop : dvHgt (s2Frame h2 hq) g (dvSideMin (s2Frame h2 hq) g 5 1 hng) = ⊤ := by
      show (s2Frame h2 hq).stageHeight
        (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 1 hng)) = ⊤
      rw [h0, (s2Frame h2 hq).stageHeight_zero]
    rw [hHg] at htop
    exact ENat.coe_ne_top Hg htop
  have hz0 : dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 1 hnz) ≠ 0 := by
    intro h0
    have htop : dvHgt (s2Frame h2 hq) z (dvSideMin (s2Frame h2 hq) z 5 1 hnz) = ⊤ := by
      show (s2Frame h2 hq).stageHeight
        (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 1 hnz)) = ⊤
      rw [h0, (s2Frame h2 hq).stageHeight_zero]
    rw [hHz] at htop
    exact ENat.coe_ne_top Hz htop
  have hkd : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [C35b.key_eq h2 hq]
    exact s2Key_natDegree
  have hdg : (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 1 hng)).natDegree ≤ 1 := by
    have h := natDegree_lt_natDegree hg0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos g _)
    rw [hkd] at h
    omega
  have hdz : (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 1 hnz)).natDegree ≤ 1 := by
    have h := natDegree_lt_natDegree hz0
      (degree_dev_lt (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos z _)
    rw [hkd] at h
    omega
  have hcore := s2_stageHeight_mul_modByMonic_le h2 hq _ _ hdg hdz
  have hg' : (s2Frame h2 hq).stageHeight
      (dev (s2Frame h2 hq).key g (dvSideMin (s2Frame h2 hq) g 5 1 hng)) = (Hg : ℕ∞) := hHg
  have hz' : (s2Frame h2 hq).stageHeight
      (dev (s2Frame h2 hq).key z (dvSideMin (s2Frame h2 hq) z 5 1 hnz)) = (Hz : ℕ∞) := hHz
  rw [hg', hz', ← Nat.cast_add] at hcore
  exact hcore

/-- ★ **The `(5, 1)` product law** — universal, no monic/pure/degree fence, all zero
cases (mirror of C130nv3's `s2_dvSupp_mul`). -/
theorem s2P_dvSupp_mul (g z : Polynomial O) :
    dvSupp (s2Frame h2 hq) (g * z) 5 1
      = dvSupp (s2Frame h2 hq) g 5 1 + dvSupp (s2Frame h2 hq) z 5 1 := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dvSupp_zero_eq_top (s2Frame h2 hq) 5 (by norm_num), top_add]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dvSupp_zero_eq_top (s2Frame h2 hq) 5 (by norm_num), add_top]
  have hng := dvSideSet_nonempty (s2Frame h2 hq) hg 5 (by norm_num : (0 : ℕ) < 1)
  have hnz := dvSideSet_nonempty (s2Frame h2 hq) hz 5 (by norm_num : (0 : ℕ) < 1)
  obtain ⟨Hg, hHg⟩ := exists_dvSideMin_height (s2Frame h2 hq) g 5 1 hng
  obtain ⟨Hz, hHz⟩ := exists_dvSideMin_height (s2Frame h2 hq) z 5 1 hnz
  exact dvSupp_mul_eq_add_of_endpoint_le h2 (s2_h_pos h2 hq) (by norm_num)
    (s2_stageHeight_key h2 hq) (by norm_num) hng hnz hHg hHz
    (s2P_endpoint_dev_le h2 hq hng hnz hHg hHz)

/-- ★ The product law in the carrier: `s2PHgt₁ (g·z) = s2PHgt₁ g + s2PHgt₁ z` for ALL
`g, z`. -/
theorem s2PHgt₁_mul (g z : Polynomial O) :
    s2PHgt₁ h2 hq (g * z) = s2PHgt₁ h2 hq g + s2PHgt₁ h2 hq z := by
  rw [s2PHgt₁, s2PHgt₁, s2PHgt₁, ← toZ_add, s2P_dvSupp_mul h2 hq]

/-! ## Part 3 — packaging and the fraction-field extension (mirror of C130nv5) -/

/-- The stage-1 point value packaged as a mathlib `AddValuation`. -/
noncomputable def s2PAddVal₁ : AddValuation (Polynomial O) (WithTop ℤ) :=
  AddValuation.of (s2PHgt₁ h2 hq) (s2PHgt₁_zero h2 hq) (s2PHgt₁_one_eq_zero h2 hq)
    (s2PHgt₁_add_ge h2 hq) (s2PHgt₁_mul h2 hq)

/-- Anti-drift pin: the packaged `AddValuation` evaluates to `s2PHgt₁`. -/
theorem s2PAddVal₁_apply (A : Polynomial O) : s2PAddVal₁ h2 hq A = s2PHgt₁ h2 hq A := rfl

/-- The multiplicative repackaging (`AddValuation.toValuation`, `Equiv.refl`). -/
noncomputable def s2PVal₁ : Valuation (Polynomial O) (Multiplicative (WithTop ℤ)ᵒᵈ) :=
  (s2PAddVal₁ h2 hq).toValuation

/-- Anti-drift pin. -/
theorem s2PVal₁_apply (A : Polynomial O) : s2PVal₁ h2 hq A = s2PAddVal₁ h2 hq A := rfl

/-- `s2PVal₁` vanishes only at `0` — via the shared `supp` ideal, never comparing the two
ambients' `0`/`⊤` literals directly (NV56's recorded trap). -/
theorem s2PVal₁_eq_zero_iff {A : Polynomial O} : s2PVal₁ h2 hq A = 0 ↔ A = 0 := by
  rw [← Valuation.mem_supp_iff]
  show A ∈ AddValuation.supp (s2PAddVal₁ h2 hq) ↔ A = 0
  rw [AddValuation.mem_supp_iff, s2PAddVal₁_apply]
  exact s2PHgt₁_eq_top_iff h2 hq

/-- The submonoid hypothesis `extendToLocalization` needs. -/
theorem s2PVal₁_hS :
    nonZeroDivisors (Polynomial O) ≤ (s2PVal₁ h2 hq).supp.primeCompl := by
  intro x hx
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hx
  exact fun h => hx (s2PVal₁_eq_zero_iff h2 hq |>.mp h)

/-- The stage-1 point valuation extended to `E = FractionRing (Polynomial O)`. -/
noncomputable def s2EPVal₁ :
    Valuation (FractionRing (Polynomial O)) (Multiplicative (WithTop ℤ)ᵒᵈ) :=
  (s2PVal₁ h2 hq).extendToLocalization (s2PVal₁_hS h2 hq) (FractionRing (Polynomial O))

/-- Converted back to an `AddValuation` on the fraction field — `valueOn 1`'s carrier. -/
noncomputable def s2AddEPVal₁ : AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  AddValuation.ofValuation (s2EPVal₁ h2 hq)

theorem s2AddEPVal₁_apply (x : FractionRing (Polynomial O)) :
    s2AddEPVal₁ h2 hq x = s2EPVal₁ h2 hq x := rfl

/-- ★ **The stage-1 restriction PIN**: the extended point valuation, restricted to
`Polynomial O` along the canonical embedding, IS `s2PHgt₁` — on the nose (mirror of
NV-6's pin). -/
theorem s2AddEPVal₁_algebraMap (A : Polynomial O) :
    s2AddEPVal₁ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = s2PHgt₁ h2 hq A := by
  rw [s2AddEPVal₁_apply]
  show (s2PVal₁ h2 hq).extendToLocalization (s2PVal₁_hS h2 hq) (FractionRing (Polynomial O))
      (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A) = s2PHgt₁ h2 hq A
  rw [Valuation.extendToLocalization_apply_map_apply, s2PVal₁_apply, s2PAddVal₁_apply]

/-! ## Part 4 — the point carrier and the evaluation

The single canonical S2 evaluation point: coefficient read = C130s17's SF-4 probe
`s2EvalHom` (injective), coordinate = the rational-function variable `s2EvalCoord`; the
stage dependence lives entirely in `valueOn`. -/

/-- **The `Point` field** (plan §5.1: a point represents the chosen valuation/evaluation
pair; here that pair is canonical, so a single point suffices — legality `s2NPPt` carries
the value equations). -/
def S2NPPoint : Type := Unit

/-- The canonical point. -/
def s2NPPointMk : S2NPPoint := ()

/-- **The `coeffHom` field**: C130s17's SF-4 probe coefficient read, verbatim (constants
through `Polynomial.C`; injective by `s2EvalHom_injective`). -/
noncomputable def s2NPCoeffHom : O →+* FractionRing (Polynomial O) := s2EvalHom

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- Anti-drift pin: `coeffHom` IS the SF-4 probe read. -/
theorem s2NPCoeffHom_eq : s2NPCoeffHom (O := O) = s2EvalHom := rfl

/-- **The `coord` field**: every point's coordinate is the rational-function variable —
C130s17's SF-4 probe coordinate, verbatim. -/
noncomputable def s2NPCoord : S2NPPoint → FractionRing (Polynomial O) :=
  fun _ => s2EvalCoord

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- ★ **The evaluation bridge**: at the probe pair, `eval₂ coeffHom (coord x)` IS the
canonical embedding `algebraMap (Polynomial O) E` — the equation that converts every point
read into a landed polynomial value through the NV-6 restriction pins. -/
theorem s2NP_eval₂_eq_algebraMap (x : S2NPPoint) (A : Polynomial O) :
    Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A
      = algebraMap (Polynomial O) (FractionRing (Polynomial O)) A := by
  show Polynomial.eval₂
      ((algebraMap (Polynomial O) (FractionRing (Polynomial O))).comp Polynomial.C)
      (algebraMap (Polynomial O) (FractionRing (Polynomial O)) Polynomial.X) A = _
  rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X]

/-- The stage-indexed valuation on `E`: the `[μ₁; Φ′ : 5]` extension at `i ≤ 1`, NV-6's
landed `s2Hgt₂` extension at `i ≥ 2`.  Both branches are genuine `AddValuation`s, so every
`valueOn` law below holds unfenced. -/
noncomputable def s2NPValuation (i : ℕ) :
    AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  if i ≤ 1 then s2AddEPVal₁ h2 hq else s2AddEVal₂ h2 hq

/-- **The `valueOn` field**: the stage valuation read, as a bare function. -/
noncomputable def s2NPValueOn (i : ℕ) : FractionRing (Polynomial O) → WithTop ℤ :=
  ⇑(s2NPValuation h2 hq i)

/-- Pin: at the gauge stage the read is the `[μ₁; Φ′ : 5]` extension. -/
theorem s2NPValueOn_one : s2NPValueOn h2 hq 1 = ⇑(s2AddEPVal₁ h2 hq) := rfl

/-- Pin: at the terminal stage the read is NV-6's landed `s2Hgt₂` extension. -/
theorem s2NPValueOn_two : s2NPValueOn h2 hq 2 = ⇑(s2AddEVal₂ h2 hq) := rfl

/-- **The `pointHgt` field**: the pointwise height IS the valued evaluation — defined,
not tabulated, so `pointHgt_eval` is `rfl` (CC-1's free-table prevention, kept). -/
noncomputable def s2NPPointHgt (i : ℕ) (x : S2NPPoint) (A : Polynomial O) : WithTop ℤ :=
  s2NPValueOn h2 hq i (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A)

/-- **The `pointHgt_eval` field, exact shape**: by construction. -/
theorem s2NP_pointHgt_eval : ∀ (i : ℕ) (x : S2NPPoint) (A : Polynomial O),
    s2NPPointHgt h2 hq i x A
      = s2NPValueOn h2 hq i (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) :=
  fun _ _ _ => rfl

/-! ### 4a. The `valueOn` laws — unfenced (∀ i), then in the exact field shapes -/

/-- `value_zero`, unfenced. -/
theorem s2NPValueOn_zero (i : ℕ) : s2NPValueOn h2 hq i 0 = ⊤ :=
  (s2NPValuation h2 hq i).map_zero

/-- `value_mul`, unfenced. -/
theorem s2NPValueOn_mul (i : ℕ) (a b : FractionRing (Polynomial O)) :
    s2NPValueOn h2 hq i (a * b) = s2NPValueOn h2 hq i a + s2NPValueOn h2 hq i b :=
  (s2NPValuation h2 hq i).map_mul a b

/-- `value_add_ge`, unfenced. -/
theorem s2NPValueOn_add_ge (i : ℕ) (a b : FractionRing (Polynomial O)) :
    min (s2NPValueOn h2 hq i a) (s2NPValueOn h2 hq i b) ≤ s2NPValueOn h2 hq i (a + b) :=
  (s2NPValuation h2 hq i).map_add a b

/-- `value_add_eq`, unfenced. -/
theorem s2NPValueOn_add_eq (i : ℕ) (a b : FractionRing (Polynomial O))
    (hne : s2NPValueOn h2 hq i a ≠ s2NPValueOn h2 hq i b) :
    s2NPValueOn h2 hq i (a + b) = min (s2NPValueOn h2 hq i a) (s2NPValueOn h2 hq i b) :=
  (s2NPValuation h2 hq i).map_add_of_distinct_val hne

/-- **The `value_zero` field, exact shape.** -/
theorem s2NP_value_zero : ∀ i, StageLive 2 i → s2NPValueOn h2 hq i 0 = ⊤ :=
  fun i _ => s2NPValueOn_zero h2 hq i

/-- **The `value_mul` field, exact shape.** -/
theorem s2NP_value_mul : ∀ i, StageLive 2 i → ∀ a b,
    s2NPValueOn h2 hq i (a * b) = s2NPValueOn h2 hq i a + s2NPValueOn h2 hq i b :=
  fun i _ => s2NPValueOn_mul h2 hq i

/-- **The `value_add_ge` field, exact shape.** -/
theorem s2NP_value_add_ge : ∀ i, StageLive 2 i → ∀ a b,
    min (s2NPValueOn h2 hq i a) (s2NPValueOn h2 hq i b) ≤ s2NPValueOn h2 hq i (a + b) :=
  fun i _ => s2NPValueOn_add_ge h2 hq i

/-- **The `value_add_eq` field, exact shape.** -/
theorem s2NP_value_add_eq : ∀ i, StageLive 2 i → ∀ a b,
    s2NPValueOn h2 hq i a ≠ s2NPValueOn h2 hq i b →
      s2NPValueOn h2 hq i (a + b) = min (s2NPValueOn h2 hq i a) (s2NPValueOn h2 hq i b) :=
  fun i _ => s2NPValueOn_add_eq h2 hq i

/-! ### 4b. The restriction dictionaries: point reads ARE landed polynomial values -/

/-- ★ **Stage-1 dictionary**: the point read at `i = 1` is the stage-1 point value
`s2PHgt₁`, for ALL `A` (bridge + the stage-1 restriction pin). -/
theorem s2NPPointHgt_one (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgt h2 hq 1 x A = s2PHgt₁ h2 hq A := by
  show s2AddEPVal₁ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2PHgt₁ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEPVal₁_algebraMap]

/-- ★ **Stage-2 dictionary**: the point read at `i = 2` is the landed terminal table
`s2Hgt₂`, for ALL `A` (bridge + NV-6's restriction pin) — strictly stronger than the
slot-fenced `slot_value` shape, and exactly the `grade_compat` shape for
`fgmn.nextValue := s2Hgt₂` (plan row FD-1). -/
theorem s2NPPointHgt_two (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgt h2 hq 2 x A = s2Hgt₂ h2 hq A := by
  show s2AddEVal₂ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₂ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₂_algebraMap]

/-! ## Part 5 — stage legality, `point_exists`, and the point laws -/

/-- **The `Pt` field**: stage legality of a point, packaging the VALUE EQUATIONS (plan
§5.1 — no unproved `True`): at a gauge-live stage the exact key value `u_{i+1}`; at every
stage the key finiteness (the `window` field's finiteness half). -/
def s2NPPt (i : ℕ) (x : S2NPPoint) : Prop :=
  (GaugeLive 2 i →
    s2NPPointHgt h2 hq i x ((s2RepositoryRealization h2 hq).keys.keyAt i)
      = ((s2DepthTwo h2 hq).u (i + 1) : WithTop ℤ))
  ∧ s2NPPointHgt h2 hq i x ((s2RepositoryRealization h2 hq).keys.keyAt i) ≠ ⊤

/-- The gauge-live key-value computation: `pointHgt 1 x (keyAt 1) = 5 = u₂`.  (`keyAt 1`
is definitionally the frame key; `u 2` is definitionally `5`.) -/
theorem s2NPPointHgt_keyAt_one (x : S2NPPoint) :
    s2NPPointHgt h2 hq 1 x ((s2RepositoryRealization h2 hq).keys.keyAt 1)
      = ((s2DepthTwo h2 hq).u 2 : WithTop ℤ) := by
  have h : s2NPPointHgt h2 hq 1 x ((s2Frame h2 hq).key) = ((5 : ℤ) : WithTop ℤ) :=
    (s2NPPointHgt_one h2 hq x _).trans (s2PHgt₁_key h2 hq)
  refine (show ((s2RepositoryRealization h2 hq).keys.keyAt 1) = (s2Frame h2 hq).key
    from rfl) ▸ h.trans ?_
  show ((5 : ℤ) : WithTop ℤ) = (((5 : ℕ) : ℤ) : WithTop ℤ)
  norm_num

/-- ★ **The `point_exists` field, exact shape**: both live stages carry a legal point —
at `i = 1` by the key-value computation, at `i = 2` by terminal-key finiteness. -/
theorem s2NP_point_exists :
    ∀ i, StageLive 2 i → Nonempty {x : S2NPPoint // s2NPPt h2 hq i x} := by
  intro i hi
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  · exact ⟨⟨s2NPPointMk, fun _ => s2NPPointHgt_keyAt_one h2 hq _,
      by rw [s2NPPointHgt_keyAt_one h2 hq]; exact WithTop.natCast_ne_top _⟩⟩
  · refine ⟨⟨s2NPPointMk, fun hg => absurd hg.2 (lt_irrefl 2), ?_⟩⟩
    rw [s2NPPointHgt_two h2 hq]
    exact s2Hgt₂_ne_top h2 hq
      (((s2RepositoryRealization h2 hq).keys.keyAt_monic 2
        (show StageLive 2 2 from ⟨by decide, by decide⟩)).ne_zero)

/-- ★ **The `key_value` field, exact shape**: read off the legality package. -/
theorem s2NP_key_value : ∀ i, GaugeLive 2 i → ∀ x : S2NPPoint, s2NPPt h2 hq i x →
    s2NPPointHgt h2 hq i x ((s2RepositoryRealization h2 hq).keys.keyAt i)
      = ((s2DepthTwo h2 hq).u (i + 1) : WithTop ℤ) :=
  fun _ hi _ hx => hx.1 hi

/-- **The finiteness half of the `window` field** (the threshold half is plan row
NP-4/NP-5: no source occurrence names the inherited S2 threshold yet; a convenient
numeral would be circular). -/
theorem s2NP_window_ne_top : ∀ i, StageLive 2 i → ∀ x : S2NPPoint, s2NPPt h2 hq i x →
    s2NPPointHgt h2 hq i x ((s2RepositoryRealization h2 hq).keys.keyAt i) ≠ ⊤ :=
  fun _ _ _ hx => hx.2

/-! ### 5a. The slot dictionary against the intended stage table -/

/-- The intended `hgt` table of the future node instance: NP-1's level-one `s2Hgt₁` at
`i ≤ 1`, the frontier-tied `s2Hgt₂` at `i ≥ 2` (so `hgt_two : s2NPHgt 2 = s2Hgt₂` is
`rfl`, per the `S2SourceFrontier` tie). -/
noncomputable def s2NPHgt (i : ℕ) : Polynomial O → WithTop ℤ :=
  if i ≤ 1 then s2Hgt₁ h2 hq else s2Hgt₂ h2 hq

/-- Pin: level one of the table is NP-1's `s2Hgt₁`. -/
theorem s2NPHgt_one : s2NPHgt h2 hq 1 = s2Hgt₁ h2 hq := rfl

/-- Pin: level two of the table is the frontier-tied `s2Hgt₂` (the `hgt_two` tie is
definitional). -/
theorem s2NPHgt_two : s2NPHgt h2 hq 2 = s2Hgt₂ h2 hq := rfl

/-- ★ **The `slot_value` field, exact shape, BOTH live levels** (plan row NP-2's slot
half, dischargeable already at NP-0 through the restriction dictionaries): on the slot
range the point read is the stage table — at `i = 1` by the small-degree dictionary
(`Dcum 1 = 2`), at `i = 2` unfenced. -/
theorem s2NP_slot_value :
    ∀ i (_hi : StageLive 2 i) (x : S2NPPoint), s2NPPt h2 hq i x →
      ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum i →
        s2NPPointHgt h2 hq i x A = s2NPHgt h2 hq i A := by
  intro i hi x _hx A _hA hdeg
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  · exact (s2NPPointHgt_one h2 hq x A).trans
      (s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt h2 hq
        (by rwa [s2DepthTwo_Dcum_one h2 hq] at hdeg))
  · exact s2NPPointHgt_two h2 hq x A

/-! ## Part 6 — teeth: the U13 slot, live and stage-graded

U13's refuter fired on `pointHgt i x (C 2)` — forced to `⊤` by char 2 of the single
ambient, against `slot_value` + `hgt_ne_top`.  At this construction the same slot is
FINITE at both live stages, agrees with the tables, and is honestly stage-graded
(`2` at level one, `4` at level two: the `e₂`-clearing is real). -/

/-- **tooth**: the terminal table on the U13 slot: `s2Hgt₂ (C 2) = 4` (derived from the
small-degree read at side `(5, 2)`; not previously landed as a named value). -/
theorem s2Hgt₂_C_two : s2Hgt₂ h2 hq (Polynomial.C (2 : O)) = ((4 : ℤ) : WithTop ℤ) := by
  have hsh : (s2Frame h2 hq).stageHeight (Polynomial.C (2 : O)) = ((2 : ℕ) : ℕ∞) := by
    refine toZ_inj ?_
    rw [← s2Hgt₁_eq_stageHeight h2 hq, s2Hgt₁_C_two h2 hq, toZ_coe]
    norm_num
  rw [s2Hgt₂, s2_dvSupp_of_natDegree_lt h2 hq (by norm_num)
      (by rw [Polynomial.natDegree_C]; norm_num), hsh,
    show (2 : ℕ) • ((2 : ℕ) : ℕ∞) = ((4 : ℕ) : ℕ∞) by rw [nsmul_eq_mul]; norm_num,
    toZ_coe]
  norm_num

/-- ★ **tooth (the U13 slot, stage 2)**: `pointHgt 2 x (C 2) = 4` — finite, equal to the
tied table, coexisting with `value_zero` and the slot laws: the char-2 refutation is dead
at this construction. -/
theorem s2NPPointHgt_two_C_two (x : S2NPPoint) :
    s2NPPointHgt h2 hq 2 x (Polynomial.C (2 : O)) = ((4 : ℤ) : WithTop ℤ) :=
  (s2NPPointHgt_two h2 hq x _).trans (s2Hgt₂_C_two h2 hq)

/-- **tooth (the U13 slot, stage 1)**: `pointHgt 1 x (C 2) = 2` — the level-one read;
together with the stage-2 tooth this exhibits the honest stage grading `4 = 2·2`. -/
theorem s2NPPointHgt_one_C_two (x : S2NPPoint) :
    s2NPPointHgt h2 hq 1 x (Polynomial.C (2 : O)) = ((2 : ℤ) : WithTop ℤ) :=
  (s2NPPointHgt_one h2 hq x _).trans (s2PHgt₁_C_two h2 hq)

/-- **tooth (the key contrast)**: the stage-1 point read of the frame key is `5 = u₂` —
NOT the level-one table value `2`: the point valuation is the augmentation, not the
table's Gauss stage.  (This is the computation that rules out `s2AddEVal₁` as
`valueOn 1`.) -/
theorem s2NPPointHgt_one_key (x : S2NPPoint) :
    s2NPPointHgt h2 hq 1 x ((s2Frame h2 hq).key) = ((5 : ℤ) : WithTop ℤ) :=
  (s2NPPointHgt_one h2 hq x _).trans (s2PHgt₁_key h2 hq)

end S2

end Uniformity.Density.Tower.C130np0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_eq_dvSupp
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_zero
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_ne_top
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_eq_top_iff
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_add_ge
#print axioms Uniformity.Density.Tower.C130np0.s2_dvSupp_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_one_eq_zero
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_C_two
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_key
#print axioms Uniformity.Density.Tower.C130np0.s2P_endpoint_dev_le
#print axioms Uniformity.Density.Tower.C130np0.s2P_dvSupp_mul
#print axioms Uniformity.Density.Tower.C130np0.s2PHgt₁_mul
#print axioms Uniformity.Density.Tower.C130np0.s2PAddVal₁
#print axioms Uniformity.Density.Tower.C130np0.s2PAddVal₁_apply
#print axioms Uniformity.Density.Tower.C130np0.s2PVal₁
#print axioms Uniformity.Density.Tower.C130np0.s2PVal₁_apply
#print axioms Uniformity.Density.Tower.C130np0.s2PVal₁_eq_zero_iff
#print axioms Uniformity.Density.Tower.C130np0.s2PVal₁_hS
#print axioms Uniformity.Density.Tower.C130np0.s2EPVal₁
#print axioms Uniformity.Density.Tower.C130np0.s2AddEPVal₁
#print axioms Uniformity.Density.Tower.C130np0.s2AddEPVal₁_apply
#print axioms Uniformity.Density.Tower.C130np0.s2AddEPVal₁_algebraMap
#print axioms Uniformity.Density.Tower.C130np0.S2NPPoint
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointMk
#print axioms Uniformity.Density.Tower.C130np0.s2NPCoeffHom
#print axioms Uniformity.Density.Tower.C130np0.s2NPCoeffHom_eq
#print axioms Uniformity.Density.Tower.C130np0.s2NPCoord
#print axioms Uniformity.Density.Tower.C130np0.s2NP_eval₂_eq_algebraMap
#print axioms Uniformity.Density.Tower.C130np0.s2NPValuation
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn_one
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn_two
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt
#print axioms Uniformity.Density.Tower.C130np0.s2NP_pointHgt_eval
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn_zero
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn_mul
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn_add_ge
#print axioms Uniformity.Density.Tower.C130np0.s2NPValueOn_add_eq
#print axioms Uniformity.Density.Tower.C130np0.s2NP_value_zero
#print axioms Uniformity.Density.Tower.C130np0.s2NP_value_mul
#print axioms Uniformity.Density.Tower.C130np0.s2NP_value_add_ge
#print axioms Uniformity.Density.Tower.C130np0.s2NP_value_add_eq
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt_one
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt_two
#print axioms Uniformity.Density.Tower.C130np0.s2NPPt
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt_keyAt_one
#print axioms Uniformity.Density.Tower.C130np0.s2NP_point_exists
#print axioms Uniformity.Density.Tower.C130np0.s2NP_key_value
#print axioms Uniformity.Density.Tower.C130np0.s2NP_window_ne_top
#print axioms Uniformity.Density.Tower.C130np0.s2NPHgt
#print axioms Uniformity.Density.Tower.C130np0.s2NPHgt_one
#print axioms Uniformity.Density.Tower.C130np0.s2NPHgt_two
#print axioms Uniformity.Density.Tower.C130np0.s2NP_slot_value
#print axioms Uniformity.Density.Tower.C130np0.s2Hgt₂_C_two
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt_two_C_two
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt_one_C_two
#print axioms Uniformity.Density.Tower.C130np0.s2NPPointHgt_one_key

end AxCheck
