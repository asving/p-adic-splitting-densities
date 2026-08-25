/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130np0
import Uniformity.ChapC.C130np4
import Uniformity.ChapC.C53b

/-!
# Uniformity.ChapC.C130np5 — S2-source plan node NP-5 (the window)

**S2-source plan node NP-5** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row NP-5:
"Prove both live window inequalities and finiteness"), depending on NP-2 (landed inside NP-0:
the slot/key value dictionary) and NP-4 (the threshold source, `C130np4.lean`).

## The computation that resolves the 5-vs-10 question (read before trusting the verdict)

NP-4 found TWO numerals at the S2 level-2 disk, both proved, neither adjudicated: `seam = 5`
(`EFF.HE6R1.18`'s own rational-cleared reading `T₂ = ℓd_rλ`) and `ℓ · seam = 10` (the SAME
quantity in chapter C's internal `ℓ`-cleared `dvSupp` convention), leaving open "which of `5`
or `10` … `NodePointSource.thresholdZ 2` for S2 should carry."  NP-4 explicitly deferred this to
"whichever node builds `pointHgt` concretely" — NP-0, now landed.  This node computes the
missing quantity — `d(Φ₂(ρ)) = pointHgt 2 x (keyAt 2)` under NP-0's own `pointHgt` — and reads
the answer off it directly, no numeral chosen by convenience:

* `keyAt 2 = composedKey (s2Tower h2 hq)` (`C130s2.s2DepthTwoKeyAt_two`), and NP-0's stage-2
  point read IS the landed terminal table on every input (`s2NPPointHgt_two`, unfenced): so
  `d(Φ₂(ρ)) = s2Hgt₂ (composedKey (s2Tower h2 hq))`.
* Computing this from C.47's THREE unconditional composed-key clauses (`composedKey_top_digit`,
  `composedKey_offLattice_digit`, `composedKey_slot_height`, all already landed, no new
  mathematics) plus `dev_eq_zero_of_lt` beyond the degree: the `Φ′`-development of `Φ₂` at the
  S2 tower datum `(e₂,f₂,u₂) = (2,1,5)` has exactly three live slots —
  height `5` at slot `0` (`composedKey_slot_height` at `t = 0`, `(f₂−0)u₂ = 5`), height `⊤`
  at slot `1` (off the `e₂ = 2`-lattice), height `0` at slot `2` (the top digit `1`) — and
  `⊤` everywhere past `natDegree = 4`.  Folding these into `dvSupp`'s inf at side `(u,ℓ) =
  (5,2)` (`ℓ • dvHgt j + u·j`) gives `min(2·5 + 0, 2·0 + 10) = min(10, 10) = 10`. **Hence
  `pointHgt 2 x (keyAt 2) = 10` exactly** (`s2Hgt₂_composedKey_s2Tower`) — independently
  cross-checked against C.42's already-landed, separately-named constant `TowerDatum.E₂`
  (`EFF.GENTOW1.07`: `"E₂ = e₂f₂u₂, the dv₂-height of every side term of Φ₂"`), whose S2 value
  is ALSO `10` (`s2Tower_data`, C.80) — two independent routes, same numeral.
* **The resolution**: `seam = 5 < 10 = d(Φ₂(ρ)) < ∞` — `(WINDOW)` HOLDS with `thresholdZ 2 :=
  seam`. `ℓ·seam = 10` FAILS — it is not strictly below `d(Φ₂(ρ)) = 10`, it EQUALS it
  (`not_ellSeam_lt_pointHgt_two`, a genuine refutation teeth-check, not an assertion). **The
  5-vs-10 question is resolved: `5` (the source's own, rational-cleared reading) is the correct
  avatar; `10` (the internal `ℓ`-cleared companion) is refuted as a threshold, even though it is
  exactly the internal-convention height the key itself attains.** This is the expected Montes
  shape: a key sits exactly ON the boundary of the disk it was built to occupy, so its own height
  under its own valuation equals the CLEARED companion of the threshold that admitted it, not the
  threshold itself.

## Level 1: what is proved, and what is honestly left open

At level 1, `d(Φ₁(ρ)) = pointHgt 1 x (keyAt 1) = u₂ = 5` (NP-0's `key_value` computation,
`s2NPPointHgt_keyAt_one`). The window needs SOME `thresholdZ 1 < 5`. NP-4 searched
`spec/EFF-T2*.md`, `spec/EFF-GENTOW5*.md`, `spec/EFF-GENHN*.md` and the tower-grammar blueprint
and found **no source occurrence** naming a level-1 threshold — level 1 is the base `KeyFrame`,
not built from any `LevelDatum` composition, so there is no "previous level" datum to derive one
from. This node independently confirms that gap cannot be filled by NP-4's own two computed
numerals either way: `seam = 5` is not `< 5`, and `ℓ·seam = 10` is not `< 5` — NEITHER of NP-4's
two avatars can serve as `thresholdZ 1`, regardless of which stage one imagines it "belongs to".
So the strict lower bound of level 1's window is **BLOCKED, honestly, exactly as NP-4 found**
(not a new blocker): no numeral is invented here. What IS proved at level 1: the finiteness
half (`s2NP_window_ne_top`, unconditional, already landed at NP-0), and the exact NECESSARY
constraint any future source-backed `thresholdZ 1` must satisfy (`level_one_threshold_lt_five`),
so that a later node inherits a bound, not a blank.

## What this node delivers

1. `s2Hgt₂_composedKey_s2Tower` / `s2NPPointHgt_keyAt_two` — the COMPUTED value `d(Φ₂(ρ)) = 10`.
2. `seam_lt_pointHgt_two` / `not_ellSeam_lt_pointHgt_two` — the 5-vs-10 resolution, both
   directions (the working avatar proved, the failing avatar refuted).
3. `s2_window_at_two` — the level-2 `window` field, in ITS exact shape, with `thresholdZ 2 :=
   seam` tied to NP-4's seam theorem (no numeral invented; the threshold used IS the
   source-pinned seam avatar, by NP-4's own dictionary).
4. `s2_window_finiteness_at_one` — the level-1 `window` field's finiteness half, in its exact
   shape.
5. `level_one_threshold_lt_five` — the honest, non-vacuous necessary bound at level 1, standing
   in for the still-missing source-backed numeral (BLOCKED, per NP-4, not invented here).

No `NodePointSource` instance is constructed, named, or claimed anywhere in this file — none
exists at S2 under the current signature (unit U13). This node supplies theorems in the exact
field shapes `NodePointSource.window` demands, at the two live stages, for the eventual SG-0
assembly.

**DEPENDS.** C130np0 (`S2NPPoint`, `s2NPPt`, `s2NPPointHgt`, `s2NPPointHgt_one/_two`,
`s2NPPointHgt_keyAt_one`, `s2NP_window_ne_top`, `s2NP_point_exists`) · C130np4 (`seam_s2Tower`,
`seam_s2Tower_intCast`, `ell_mul_seam_s2Tower`) · C.47 (`composedKey_top_digit`,
`composedKey_offLattice_digit`, `composedKey_slot_height`, `towerLabel_coeff_eq_zero_iff`) via
C.53b · C.42/C.44 (`TowerDatum`, `TowerDatum.levelDatum`, `TowerDatum.E₂`) · C.80 (`s2Tower`,
`s2Tower_data`) · C.35b (`key_eq`, `sh_C`) · C.97 (`s2Key_natDegree`) · B.04
(`dev_eq_zero_of_lt`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched; new
file only — no other unit's file edited. No `NodePointSource` instance claimed.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np4

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — small local helpers (private copies, per the established convention) -/

/-- `stageHeight 1 = 0` at the S2 frame (local copy; the same private helper NP-0 carries). -/
private theorem sh_one' : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], C35b.sh_C h2 hq]
  simp

/-- The frame key's degree is `2` (local copy of the route NP-0/C80 both use). -/
private theorem s2Frame_key_natDegree : (s2Frame h2 hq).key.natDegree = 2 := by
  rw [C35b.key_eq h2 hq]; exact s2Key_natDegree

/-! ## Part 1 — the composed key's `Φ′`-development at the S2 tower, and its height profile -/

/-- The composed key's degree is `4` (C.53b's general theorem, evaluated at the S2 numerals
via `s2Tower_data`). -/
theorem composedKey_s2Tower_natDegree' :
    (composedKey (s2Tower h2 hq)).natDegree = 4 := by
  rw [composedKey_natDegree_D₂ (s2Tower h2 hq) h2, (s2Tower_data h2 hq).2.2.2.1]

/-- The translated label's constant coefficient is nonzero (C.44's dictionary, plus the
S2 tower datum's own `hψ0`: `ψ₂ = X − 1`, so `ψ₂.coeff 0 = -1 ≠ 0`). -/
theorem towerLabel_s2Tower_coeff_zero_ne :
    (towerLabel (s2Tower h2 hq)).coeff 0 ≠ 0 := by
  rw [Ne, towerLabel_coeff_eq_zero_iff (s2Tower h2 hq) h2 0]
  exact (s2Tower h2 hq).hψ0

/-- ★ **Slot `0`, height `5`** — C.47's slot-height clause at `t = 0`: `(f₂−0)u₂ = 5`. -/
theorem stageHeight_dev_composedKey_s2Tower_zero :
    (s2Frame h2 hq).stageHeight
      (dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) 0) = ((5 : ℕ) : ℕ∞) := by
  have ht : (0 : ℕ) < (s2Tower h2 hq).f₂ := by
    rw [(s2Tower_data h2 hq).2.1]; norm_num
  have h := composedKey_slot_height (s2Tower h2 hq) h2 (t := 0) ht
    (towerLabel_s2Tower_coeff_zero_ne h2 hq)
  simpa [(s2Tower_data h2 hq).2.1, (s2Tower_data h2 hq).2.2.1] using h

/-- **Slot `1`, dev `0`** — off the `e₂ = 2`-lattice. -/
theorem dev_composedKey_s2Tower_one :
    dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) 1 = 0 := by
  have hb : (1 : ℕ) < (s2Tower h2 hq).e₂ * (s2Tower h2 hq).f₂ := by
    rw [(s2Tower_data h2 hq).1, (s2Tower_data h2 hq).2.1]; norm_num
  have hnd : ¬ (s2Tower h2 hq).e₂ ∣ (1 : ℕ) := by
    rw [(s2Tower_data h2 hq).1]; decide
  exact composedKey_offLattice_digit (s2Tower h2 hq) hb hnd

/-- **Slot `2`, dev `1`** — the top digit. -/
theorem dev_composedKey_s2Tower_two :
    dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) 2 = 1 :=
  composedKey_top_digit (s2Tower h2 hq)

/-- **Slots `≥ 3`, dev `0`** — beyond the composed key's own degree-4 development range. -/
theorem dev_composedKey_s2Tower_ge_three {j : ℕ} (hj : 3 ≤ j) :
    dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) j = 0 := by
  refine dev_eq_zero_of_lt (s2Frame h2 hq).hmonic
    (by rw [s2Frame_key_natDegree h2 hq]; norm_num) _ j ?_
  rw [composedKey_s2Tower_natDegree' h2 hq, s2Frame_key_natDegree h2 hq]
  omega

/-- The height profile at slot `0`: `5`. -/
theorem dvHgt_composedKey_s2Tower_zero :
    dvHgt (s2Frame h2 hq) (composedKey (s2Tower h2 hq)) 0 = ((5 : ℕ) : ℕ∞) :=
  stageHeight_dev_composedKey_s2Tower_zero h2 hq

/-- The height profile at slot `1`: `⊤`. -/
theorem dvHgt_composedKey_s2Tower_one :
    dvHgt (s2Frame h2 hq) (composedKey (s2Tower h2 hq)) 1 = ⊤ := by
  show (s2Frame h2 hq).stageHeight
    (dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) 1) = ⊤
  rw [dev_composedKey_s2Tower_one h2 hq]
  exact KeyFrame.stageHeight_zero _

/-- The height profile at slot `2`: `0`. -/
theorem dvHgt_composedKey_s2Tower_two :
    dvHgt (s2Frame h2 hq) (composedKey (s2Tower h2 hq)) 2 = 0 := by
  show (s2Frame h2 hq).stageHeight
    (dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) 2) = 0
  rw [dev_composedKey_s2Tower_two h2 hq]
  exact sh_one' h2 hq

/-- The height profile at every slot `≥ 3`: `⊤`. -/
theorem dvHgt_composedKey_s2Tower_ge_three {j : ℕ} (hj : 3 ≤ j) :
    dvHgt (s2Frame h2 hq) (composedKey (s2Tower h2 hq)) j = ⊤ := by
  show (s2Frame h2 hq).stageHeight
    (dev (s2Frame h2 hq).key (composedKey (s2Tower h2 hq)) j) = ⊤
  rw [dev_composedKey_s2Tower_ge_three h2 hq hj]
  exact KeyFrame.stageHeight_zero _

/-! ## Part 2 — the assembled value: `d(Φ₂(ρ)) = 10` -/

/-- ★ **The computed level-2 disk value**: `dvSupp (s2Frame h2 hq) (composedKey (s2Tower h2
hq)) 5 2 = 10` — folding the height profile above into the `(u,ℓ) = (5,2)` cleared inf. -/
theorem dvSupp_composedKey_s2Tower :
    dvSupp (s2Frame h2 hq) (composedKey (s2Tower h2 hq)) 5 2 = (10 : ℕ∞) := by
  rw [dvSupp, composedKey_s2Tower_natDegree' h2 hq,
    show Finset.range (4 + 1) = {0, 1, 2, 3, 4} from rfl]
  simp only [Finset.inf_insert, Finset.inf_singleton,
    dvHgt_composedKey_s2Tower_zero h2 hq, dvHgt_composedKey_s2Tower_one h2 hq,
    dvHgt_composedKey_s2Tower_two h2 hq,
    dvHgt_composedKey_s2Tower_ge_three h2 hq (show 3 ≤ 3 by norm_num),
    dvHgt_composedKey_s2Tower_ge_three h2 hq (show 3 ≤ 4 by norm_num)]
  decide

/-- ★ **`s2Hgt₂` at the composed key: `10`** — the terminal table's read on `keyAt 2` itself
(cross-checked against C.42's independently-landed `TowerDatum.E₂ = 10`, `s2Tower_data`). -/
theorem s2Hgt₂_composedKey_s2Tower :
    s2Hgt₂ h2 hq (composedKey (s2Tower h2 hq)) = ((10 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₂, dvSupp_composedKey_s2Tower h2 hq, show (10 : ℕ∞) = ((10 : ℕ) : ℕ∞) by norm_num,
    toZ_coe]
  norm_num

/-- `keyAt 2` IS the composed key, definitionally (mirror of NP-0's own level-1 pin). -/
theorem keyAt_two_eq_composedKey :
    (s2RepositoryRealization h2 hq).keys.keyAt 2 = composedKey (s2Tower h2 hq) := rfl

/-- ★ **The COMPUTED window value at level 2**: `d(Φ₂(ρ)) = pointHgt 2 x (keyAt 2) = 10`, for
every point `x` — unfenced, since `s2NPPointHgt_two` holds for ALL inputs. -/
theorem s2NPPointHgt_keyAt_two (x : S2NPPoint) :
    s2NPPointHgt h2 hq 2 x ((s2RepositoryRealization h2 hq).keys.keyAt 2)
      = ((10 : ℤ) : WithTop ℤ) := by
  rw [keyAt_two_eq_composedKey h2 hq]
  exact (s2NPPointHgt_two h2 hq x _).trans (s2Hgt₂_composedKey_s2Tower h2 hq)

/-- Independent cross-check: the SAME numeral, off C.42's separately-landed `TowerDatum.E₂`
(`EFF.GENTOW1.07`'s own name for "the `dv₂`-height of every side term of `Φ₂`"). -/
theorem s2NPPointHgt_keyAt_two_eq_E₂ (x : S2NPPoint) :
    s2NPPointHgt h2 hq 2 x ((s2RepositoryRealization h2 hq).keys.keyAt 2)
      = (((s2Tower h2 hq).E₂ : ℕ) : WithTop ℤ) := by
  rw [s2NPPointHgt_keyAt_two h2 hq x, (s2Tower_data h2 hq).2.2.2.2]
  norm_num

/-! ## Part 3 — the 5-vs-10 resolution -/

/-- ★ **`5` WORKS**: `seam < d(Φ₂(ρ))`, i.e. `5 < 10`. This is the strict half of the level-2
`window` with `thresholdZ 2 := seam` — NP-4's own numeral, no new one invented. -/
theorem seam_lt_pointHgt_two (x : S2NPPoint) :
    ((((s2Tower h2 hq).levelDatum h2).seam : ℤ) : WithTop ℤ) <
      s2NPPointHgt h2 hq 2 x ((s2RepositoryRealization h2 hq).keys.keyAt 2) := by
  rw [seam_s2Tower_intCast h2 hq, s2NPPointHgt_keyAt_two h2 hq x]
  exact_mod_cast (by norm_num : (5 : ℤ) < 10)

/-- ★ **`10` FAILS (teeth)**: `ℓ · seam` is NOT strictly below `d(Φ₂(ρ))` — it EQUALS it. This
is a genuine refutation, computed, not an assertion: the internal `ℓ`-cleared companion is
exactly the height the key attains, so it cannot serve as a threshold. -/
theorem not_ellSeam_lt_pointHgt_two (x : S2NPPoint) :
    ¬ ((((s2Tower h2 hq).levelDatum h2).ℓ * ((s2Tower h2 hq).levelDatum h2).seam : ℤ) :
        WithTop ℤ) <
      s2NPPointHgt h2 hq 2 x ((s2RepositoryRealization h2 hq).keys.keyAt 2) := by
  have h10 : (((s2Tower h2 hq).levelDatum h2).ℓ : ℤ)
      * (((s2Tower h2 hq).levelDatum h2).seam : ℤ) = 10 := by
    exact_mod_cast ell_mul_seam_s2Tower h2 hq
  rw [s2NPPointHgt_keyAt_two h2 hq x, h10]
  exact lt_irrefl _

/-! ## Part 4 — the level-2 `window` field, in its exact shape -/

/-- ★ **The level-2 `window` field**, with `thresholdZ 2 := seam` — the source-pinned avatar
NP-4 proved, tied here through the seam theorems, no numeral invented at this node. -/
theorem s2_window_at_two (x : S2NPPoint) (hx : s2NPPt h2 hq 2 x) :
    ((((s2Tower h2 hq).levelDatum h2).seam : ℤ) : WithTop ℤ) <
        s2NPPointHgt h2 hq 2 x ((s2RepositoryRealization h2 hq).keys.keyAt 2) ∧
      s2NPPointHgt h2 hq 2 x ((s2RepositoryRealization h2 hq).keys.keyAt 2) ≠ ⊤ :=
  ⟨seam_lt_pointHgt_two h2 hq x, s2NP_window_ne_top h2 hq 2 (by decide) x hx⟩

/-! ## Part 5 — level 1: finiteness (landed), and the honest necessary bound (not a numeral) -/

/-- **The level-1 `window` field's finiteness half**, in its exact shape (already landed at
NP-0; re-exposed here for NP-5's field-shape deliverable). -/
theorem s2_window_finiteness_at_one (x : S2NPPoint) (hx : s2NPPt h2 hq 1 x) :
    s2NPPointHgt h2 hq 1 x ((s2RepositoryRealization h2 hq).keys.keyAt 1) ≠ ⊤ :=
  s2NP_window_ne_top h2 hq 1 (by decide) x hx

/-- ★ **The honest necessary bound at level 1**: ANY threshold candidate `T` for which the
strict half of the level-1 window could hold must satisfy `T < 5` (since `d(Φ₁(ρ)) = u₂ = 5`
by NP-0's `key_value` computation). This is NOT a construction of `thresholdZ 1` — no source
occurrence names one (NP-4, confirmed independently above: neither `seam = 5` nor `ℓ·seam = 10`
is `< 5`, so NEITHER of NP-4's two avatars can serve at level 1 regardless of which stage one
imagines it belongs to). Recorded so a future node inherits a genuine constraint, not a blank. -/
theorem level_one_threshold_lt_five {T : ℤ} (x : S2NPPoint)
    (hwin : (T : WithTop ℤ) <
      s2NPPointHgt h2 hq 1 x ((s2RepositoryRealization h2 hq).keys.keyAt 1)) :
    T < 5 := by
  rw [s2NPPointHgt_keyAt_one h2 hq x,
    show (s2DepthTwo h2 hq).u 2 = 5 from (s2DepthTwo_stage2 h2 hq).2.2,
    show ((5 : ℕ) : WithTop ℤ) = ((5 : ℤ) : WithTop ℤ) by norm_num] at hwin
  exact WithTop.coe_lt_coe.mp hwin

/-- Teeth: NP-4's `seam` avatar cannot itself serve as `thresholdZ 1` (`5 ≮ 5`). -/
theorem not_seam_lt_pointHgt_one (x : S2NPPoint) :
    ¬ ((((s2Tower h2 hq).levelDatum h2).seam : ℤ) : WithTop ℤ) <
      s2NPPointHgt h2 hq 1 x ((s2RepositoryRealization h2 hq).keys.keyAt 1) := by
  rw [seam_s2Tower_intCast h2 hq, s2NPPointHgt_keyAt_one h2 hq x,
    show (s2DepthTwo h2 hq).u 2 = 5 from (s2DepthTwo_stage2 h2 hq).2.2]
  exact lt_irrefl _

/-- Teeth: NP-4's `ℓ·seam` avatar cannot serve as `thresholdZ 1` either (`10 ≮ 5`). -/
theorem not_ellSeam_lt_pointHgt_one (x : S2NPPoint) :
    ¬ ((((s2Tower h2 hq).levelDatum h2).ℓ * ((s2Tower h2 hq).levelDatum h2).seam : ℤ) :
        WithTop ℤ) <
      s2NPPointHgt h2 hq 1 x ((s2RepositoryRealization h2 hq).keys.keyAt 1) := by
  have h10 : (((s2Tower h2 hq).levelDatum h2).ℓ : ℤ)
      * (((s2Tower h2 hq).levelDatum h2).seam : ℤ) = 10 := by
    exact_mod_cast ell_mul_seam_s2Tower h2 hq
  rw [s2NPPointHgt_keyAt_one h2 hq x,
    show (s2DepthTwo h2 hq).u 2 = 5 from (s2DepthTwo_stage2 h2 hq).2.2, h10,
    show ((5 : ℕ) : WithTop ℤ) = ((5 : ℤ) : WithTop ℤ) by norm_num]
  intro h
  exact absurd (WithTop.coe_lt_coe.mp h) (by norm_num)

end S2

end Uniformity.Density.Tower.C130np5

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np5.sh_one'
#print axioms Uniformity.Density.Tower.C130np5.s2Frame_key_natDegree
#print axioms Uniformity.Density.Tower.C130np5.composedKey_s2Tower_natDegree'
#print axioms Uniformity.Density.Tower.C130np5.towerLabel_s2Tower_coeff_zero_ne
#print axioms Uniformity.Density.Tower.C130np5.stageHeight_dev_composedKey_s2Tower_zero
#print axioms Uniformity.Density.Tower.C130np5.dev_composedKey_s2Tower_one
#print axioms Uniformity.Density.Tower.C130np5.dev_composedKey_s2Tower_two
#print axioms Uniformity.Density.Tower.C130np5.dev_composedKey_s2Tower_ge_three
#print axioms Uniformity.Density.Tower.C130np5.dvHgt_composedKey_s2Tower_zero
#print axioms Uniformity.Density.Tower.C130np5.dvHgt_composedKey_s2Tower_one
#print axioms Uniformity.Density.Tower.C130np5.dvHgt_composedKey_s2Tower_two
#print axioms Uniformity.Density.Tower.C130np5.dvHgt_composedKey_s2Tower_ge_three
#print axioms Uniformity.Density.Tower.C130np5.dvSupp_composedKey_s2Tower
#print axioms Uniformity.Density.Tower.C130np5.s2Hgt₂_composedKey_s2Tower
#print axioms Uniformity.Density.Tower.C130np5.keyAt_two_eq_composedKey
#print axioms Uniformity.Density.Tower.C130np5.s2NPPointHgt_keyAt_two
#print axioms Uniformity.Density.Tower.C130np5.s2NPPointHgt_keyAt_two_eq_E₂
#print axioms Uniformity.Density.Tower.C130np5.seam_lt_pointHgt_two
#print axioms Uniformity.Density.Tower.C130np5.not_ellSeam_lt_pointHgt_two
#print axioms Uniformity.Density.Tower.C130np5.s2_window_at_two
#print axioms Uniformity.Density.Tower.C130np5.s2_window_finiteness_at_one
#print axioms Uniformity.Density.Tower.C130np5.level_one_threshold_lt_five
#print axioms Uniformity.Density.Tower.C130np5.not_seam_lt_pointHgt_one
#print axioms Uniformity.Density.Tower.C130np5.not_ellSeam_lt_pointHgt_one

end AxCheck
