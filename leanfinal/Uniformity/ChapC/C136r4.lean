/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136r2
import Uniformity.ChapC.C136r3
import Uniformity.ChapI.I10DeepExport

/-!
# Uniformity.ChapC.C136r4 — the deep-witness rows R6 + R7: the wired gauge fields and THE
DEPTH-FOUR SPLIT NODE + CHAIN REALIZATION [R67 2026-08-29]

**Rows R6 + R7** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4 — the
campaign's KEYSTONE row: the first depth-four `SplitNodePointSource` instance
(`s2SplitNodeFour`) at the R0 receiver/normalizer and the D3-19 key chain, wired at
construction (GCW-6), and the depth-four `ChainRealization` (`s2FourChainRealization`).

## The R34 named open, DECIDED (Part 0)

R34 (`C136r2`, module docstring) left open whether the DIRECT stage-table choice
(`pointHgt i` tied to the level's OWN table `s2Hgt_i`) satisfies the eventual `key_value`
law at the now-gauge-live levels 2/3.  Part 0 decides it NEGATIVELY, by machine: the landed
`C132rp10b.s2Hgt₃_g8` reads the level-3 key at `42 ≠ 85 = u₄`, so R3's dispatcher
`s2NPPointHgtFour` cannot serve as the node's point read.  The fix is exactly the "bespoke
fix analogous to `s2PHgt₁`'s discovery one level up" R34 anticipated — and it needs NO new
valuation: the SHIFTED dispatch (level `i` reads the landed level-`(i+1)` table) supplies
`key_value` at every gauge-live level through the three landed tower-height teeth
(`s2Hgt₃_Φ₂ = 21`, `s2Hgt₄_g8 = 85`, `s2Hgt₅_g16 = 171`), while `slot_value` holds because
each landed table's own laws serve as the node's stage tables one slot up.  The node's
stage-table row is therefore the AUGMENTED table bank
(`s2Hgt₁ / s2Hgt₃ / s2Hgt₄ / s2Hgt₅` at levels 1/2/3/4) — level 1 byte-parallel to the
depth-two witness (`s2PHgt₁` vs `s2Hgt₁`, NP-0's own discovery), levels 2–4 the same
mechanism at the landed μ₃/μ₄/μ₅ valuations.  R1/R2's banks are consumed exactly where
they were built for: the digit/Full/lift banks `s2Dig₃/₄/₅` (R1 Parts 1/2/4) run against
these tables verbatim, and the node's level-4 stage carrier IS R2's `s2SlotFourMu5`.

## What lands

* Part 0 — the R34 `key_value` decision (the refutation tooth + the shifted teeth).
* Part 1 — the shifted point-valuation dispatcher `s2NPValuationR7`/`s2NPValueOnR7`/
  `s2NPPointHgtR7` (branches: NP-0's `s2AddEPVal₁`, R3's `s2AddEVal₃`/`s2AddEVal₄`/
  `s2AddEVal₅` — every branch a landed `AddValuation`, so all `value_*` laws are free).
* Part 2 — the depth-four point package: legality `s2NPPtFour` (NP-0's value-equation
  pattern), `point_exists` at all four live stages, `key_value`, window finiteness.
* Part 3 — the augmented stage tables `s2R7Hgt`/`s2R7Dig`/`s2R7Full`, their laws (all from
  the landed per-level banks), the generic card-2 `lift`, and the four-datum threshold
  tables (R4's open structures `S2LevelOneThreshold`/`…TwoThresholdFour`/`…Three`/`…Four`
  as parameters — no invented numeral).
* Part 4 — **R6**: the wired gauge fields at depth four: `s2ArenaReadFour`/`s2PeelUnitFour`
  (FORCED — the terminal unit group is a singleton) and the law-satisfying
  `s2TowerReadFourWired := 1` chosen ONCE at construction (IFC4's licence, GCW-6: no
  unwired public witness), with the free-choice disclosure and live/junk export pins.
* Part 5 — ★★ **R7**: `s2SplitNodeFour`, the first depth-four `SplitNodePointSource`,
  conditional on exactly the four open threshold datums `w₁ w₂ w₃ w₄`; stage-table pins,
  the level-4 carrier pin to R2's `s2SlotFourMu5`, the one-field read audit.
* Part 6 — ★★ `s2FourChainRealization`: receiver R0, keys D3-19, normalizer R0, node R7.
* Part 7 — R34's second open CLOSED: the `.ofSplitNode` necessity mirrors at the
  gauge-live levels 2/3 (`s2LevelTwoThresholdFour_ofSplitNode`/`…Three…`); the level-4
  converse is NOT forced by the field list (window only bounds `T₄` by the node's OWN
  terminal key read) — the honest conditional form + the at-the-witness instance land.
* Part 8 — the R5 handoff DISCHARGED: `CanonicalGeneratorDescent` inhabited at the
  realization (every gauge-live level), the G4 `DeepLevelExport` conditional constructor
  (`ofLetterEq` fired at the witness, remaining input exactly the G3 site package + the
  letterZ tie — C0's charge), and the `ArisingCore`/`RealizedInput` packaging
  `s2FourArisingCoreOf`/`s2FourRealizedInputOf`, parametric in exactly the R8/R8r payload
  (`F₀`, `μ`, coprimality) — no payload is invented here (R8r's gate).

## Honesty scope

* Conditionality of the node/realization: exactly the FOUR open threshold datums
  (level 1: `C130sg.S2LevelOneThreshold`, NP-4/NP-5's honest STOP; levels 2–4: R4's
  `S2Level{Two,Three,Four}ThresholdFour`).  All four are Lean-nonempty (R4's disclosure
  teeth); their openness is WHICH numeral the source's inherited `T_i` is.
* The node's stage tables at levels 2–4 are the landed μ₃/μ₄/μ₅ tables — NOT R1's
  four-branch `s2NPHgtFour` (which Part 0 proves cannot serve): the two table banks agree
  in provenance but sit one slot apart; both facts are pinned below.
* NO `RealizedInput` instance with a concrete payload is landed: `F₀ = leaf²`'s
  key-freeness is R8's gated content (G9 RED per the DWR adjudication).  The packaging is
  parametric; the depth-four funnel is open at exactly that payload.
* The `DeepLevelExport` inhabitation is CONDITIONAL on the G3 site package (C0's row);
  what lands is the constructor application with every witness-side input discharged.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2NPPtFour`, `s2SplitNodeFour`, `s2FourChainRealization`, `s2FourArisingCoreOf`,
`s2FourRealizedInputOf`, the `.ofSplitNode` mirrors, and the Part-8 discharge statements.

Cite ledger: **empty** — every declaration rests on Lean/mathlib + the Lean-core
NP/NV/RP/KP/D3/D4/R0–R5 chain; `#print axioms` footer is the audit.

Verdict: `runs/wave-c/verdict_R67.md`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C136r4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d2
open Uniformity.Density.Tower.C136e0
open Uniformity.Density.Tower.C136d3 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3

universe uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — the R34 `key_value` open, DECIDED

The direct choice (R3's dispatcher, level's own table) FAILS at level 3, by the landed
μ₃ read of the level-3 key; the shifted teeth that replace it are the three landed
tower-height values. -/

/-- the depth-four chain's level-3 key is `g₈` (D3-19's chain read, re-exposed at the
projection). -/
theorem s2FourKeyAt_three : (s2DepthFourKeyChain h2 hq).keyAt 3 = g8 h2 hq := by
  show s2DepthFourKeyAt h2 hq 3 = g8 h2 hq
  rw [s2DepthFourKeyAt_of_le h2 hq (by omega)]
  exact s2DepthThreeKeyAt_three h2 hq

/-- The R3 dispatcher's level-3 read of the level-3 key is the landed `42`. -/
theorem s2NPPointHgtFour_three_keyAt (x : S2NPPoint) :
    s2NPPointHgtFour h2 hq 3 x ((s2DepthFourKeyChain h2 hq).keyAt 3)
      = ((42 : ℤ) : WithTop ℤ) := by
  rw [s2FourKeyAt_three h2 hq, s2NPPointHgtFour_three h2 hq x]
  exact s2Hgt₃_g8 h2 hq

/-- ★ **The R34 decision (refutation half)**: the direct stage-table choice does NOT
satisfy `key_value` at the gauge-live level 3 — `42 ≠ 85 = u₄`.  This is the machine
ground for the shifted dispatch below. -/
theorem s2R34_direct_choice_fails_key_value (x : S2NPPoint) :
    s2NPPointHgtFour h2 hq 3 x ((s2DepthFourKeyChain h2 hq).keyAt 3)
      ≠ (((s2DepthFour h2 hq).u 4 : ℕ) : WithTop ℤ) := by
  rw [s2NPPointHgtFour_three_keyAt h2 hq x]
  intro h
  rw [show (((s2DepthFour h2 hq).u 4 : ℕ) : WithTop ℤ) = (((85 : ℕ) : ℤ) : WithTop ℤ)
      from rfl] at h
  exact absurd (WithTop.coe_inj.mp h) (by norm_num)

/-! ## Part 1 — the shifted point-valuation dispatcher

Level `i` reads the landed level-`(i+1)` valuation: NP-0's `[μ₁; Φ′ ↦ 5]` augmentation at
`i = 1` (exactly the depth-two witness's own branch), R3's μ₃/μ₄/μ₅ fraction-field
extensions at `i = 2, 3, 4`.  Every branch is a genuine `AddValuation`, so the four
`value_*` node laws hold unfenced. -/

/-- the depth-four SHIFTED point-valuation dispatch (the node's `valueOn` carrier). -/
noncomputable def s2NPValuationR7 (i : ℕ) :
    AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  if i ≤ 1 then s2AddEPVal₁ h2 hq
  else if i ≤ 2 then s2AddEVal₃ h2 hq
  else if i ≤ 3 then s2AddEVal₄ h2 hq
  else s2AddEVal₅ h2 hq

/-- **the `valueOn` field, depth-four shifted shape.** -/
noncomputable def s2NPValueOnR7 (i : ℕ) : FractionRing (Polynomial O) → WithTop ℤ :=
  ⇑(s2NPValuationR7 h2 hq i)

theorem s2NPValueOnR7_one : s2NPValueOnR7 h2 hq 1 = ⇑(s2AddEPVal₁ h2 hq) := rfl
theorem s2NPValueOnR7_two : s2NPValueOnR7 h2 hq 2 = ⇑(s2AddEVal₃ h2 hq) := rfl
theorem s2NPValueOnR7_three : s2NPValueOnR7 h2 hq 3 = ⇑(s2AddEVal₄ h2 hq) := rfl
theorem s2NPValueOnR7_four : s2NPValueOnR7 h2 hq 4 = ⇑(s2AddEVal₅ h2 hq) := rfl

/-- **the `pointHgt` field, depth-four shifted shape**: defined (not tabulated), so
`pointHgt_eval` is `rfl` — NP-0's free-table prevention, kept. -/
noncomputable def s2NPPointHgtR7 (i : ℕ) (x : S2NPPoint) (A : Polynomial O) : WithTop ℤ :=
  s2NPValueOnR7 h2 hq i (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A)

/-- stage-1 restriction dictionary: the point read IS NP-0's augmentation `s2PHgt₁`. -/
theorem s2NPPointHgtR7_one (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtR7 h2 hq 1 x A = s2PHgt₁ h2 hq A := by
  show s2AddEPVal₁ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2PHgt₁ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEPVal₁_algebraMap]

/-- ★ stage-2 restriction dictionary (SHIFTED): the point read IS the landed μ₃ table. -/
theorem s2NPPointHgtR7_two (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtR7 h2 hq 2 x A = s2Hgt₃ h2 hq A := by
  show s2AddEVal₃ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₃ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₃_algebraMap]

/-- ★ stage-3 restriction dictionary (SHIFTED): the point read IS the landed μ₄ table. -/
theorem s2NPPointHgtR7_three (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtR7 h2 hq 3 x A = s2Hgt₄ h2 hq A := by
  show s2AddEVal₄ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₄ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₄_algebraMap]

/-- ★ stage-4 restriction dictionary (SHIFTED): the point read IS the landed μ₅ table. -/
theorem s2NPPointHgtR7_four (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtR7 h2 hq 4 x A = s2Hgt₅ h2 hq A := by
  show s2AddEVal₅ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₅ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₅_algebraMap]

/-! ## Part 2 — the key teeth and the depth-four point package -/

/-- key tooth, level 1: the point read of `keyAt 1 = Φ′` is `u₂ = 5` (NP-0's
`s2PHgt₁_key`). -/
theorem s2NPPointHgtR7_keyAt_one (x : S2NPPoint) :
    s2NPPointHgtR7 h2 hq 1 x ((s2DepthFourKeyChain h2 hq).keyAt 1)
      = (((s2DepthFour h2 hq).u 2 : ℕ) : WithTop ℤ) := by
  have hk : (s2DepthFourKeyChain h2 hq).keyAt 1 = (s2Frame h2 hq).key :=
    s2DepthFourKeyAt_one h2 hq
  rw [hk, s2NPPointHgtR7_one h2 hq x, s2PHgt₁_key h2 hq]
  show ((5 : ℤ) : WithTop ℤ) = (((5 : ℕ) : ℤ) : WithTop ℤ)
  norm_num

/-- ★ key tooth, level 2 (SHIFTED): the point read of `keyAt 2 = Φ₂` is `u₃ = 21`
(`C132nv1.s2Hgt₃_Φ₂`). -/
theorem s2NPPointHgtR7_keyAt_two (x : S2NPPoint) :
    s2NPPointHgtR7 h2 hq 2 x ((s2DepthFourKeyChain h2 hq).keyAt 2)
      = (((s2DepthFour h2 hq).u 3 : ℕ) : WithTop ℤ) := by
  have hk : (s2DepthFourKeyChain h2 hq).keyAt 2 = s2DepthTwoKeyAt h2 hq 2 := by
    show s2DepthFourKeyAt h2 hq 2 = s2DepthTwoKeyAt h2 hq 2
    rw [s2DepthFourKeyAt_of_le h2 hq (by omega)]
    exact s2DepthThreeKeyAt_two h2 hq
  rw [hk, s2NPPointHgtR7_two h2 hq x, s2Hgt₃_Φ₂ h2 hq]
  show ((21 : ℤ) : WithTop ℤ) = (((21 : ℕ) : ℤ) : WithTop ℤ)
  norm_num

/-- ★ key tooth, level 3 (SHIFTED): the point read of `keyAt 3 = g₈` is `u₄ = 85`
(`C136d0.s2Hgt₄_g8`). -/
theorem s2NPPointHgtR7_keyAt_three (x : S2NPPoint) :
    s2NPPointHgtR7 h2 hq 3 x ((s2DepthFourKeyChain h2 hq).keyAt 3)
      = (((s2DepthFour h2 hq).u 4 : ℕ) : WithTop ℤ) := by
  rw [s2FourKeyAt_three h2 hq, s2NPPointHgtR7_three h2 hq x, s2Hgt₄_g8 h2 hq]
  show ((85 : ℤ) : WithTop ℤ) = (((85 : ℕ) : ℤ) : WithTop ℤ)
  norm_num

/-- ★ key tooth, level 4 (terminal; SHIFTED): the point read of `keyAt 4 = g16` is the μ₅
refinement height `171` (`C136e0.s2Hgt₅_g16`) — the exact value R4's level-4 window
structure is bounded by. -/
theorem s2NPPointHgtR7_keyAt_four (x : S2NPPoint) :
    s2NPPointHgtR7 h2 hq 4 x ((s2DepthFourKeyChain h2 hq).keyAt 4)
      = ((171 : ℤ) : WithTop ℤ) := by
  have hk : (s2DepthFourKeyChain h2 hq).keyAt 4 = g16 h2 hq :=
    s2DepthFourKeyAt_four h2 hq
  rw [hk, s2NPPointHgtR7_four h2 hq x]
  exact s2Hgt₅_g16 h2 hq

/-- **the `Pt` field** (NP-0's value-equation package, depth four): at a gauge-live stage
the exact key value `u_{i+1}`; at every stage the key finiteness. -/
def s2NPPtFour (i : ℕ) (x : S2NPPoint) : Prop :=
  (GaugeLive 4 i →
    s2NPPointHgtR7 h2 hq i x ((s2DepthFourKeyChain h2 hq).keyAt i)
      = (((s2DepthFour h2 hq).u (i + 1) : ℕ) : WithTop ℤ))
  ∧ s2NPPointHgtR7 h2 hq i x ((s2DepthFourKeyChain h2 hq).keyAt i) ≠ ⊤

/-- ★ **the `point_exists` field, exact shape**: all four live stages carry a legal
point — at `i = 1, 2, 3` by the key teeth, at `i = 4` by terminal-key finiteness. -/
theorem s2NPFour_point_exists :
    ∀ i, StageLive 4 i → Nonempty {x : S2NPPoint // s2NPPtFour h2 hq i x} := by
  intro i hi
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  · exact ⟨⟨s2NPPointMk, fun _ => s2NPPointHgtR7_keyAt_one h2 hq _,
      by rw [s2NPPointHgtR7_keyAt_one h2 hq]; exact WithTop.natCast_ne_top _⟩⟩
  · exact ⟨⟨s2NPPointMk, fun _ => s2NPPointHgtR7_keyAt_two h2 hq _,
      by rw [s2NPPointHgtR7_keyAt_two h2 hq]; exact WithTop.natCast_ne_top _⟩⟩
  · exact ⟨⟨s2NPPointMk, fun _ => s2NPPointHgtR7_keyAt_three h2 hq _,
      by rw [s2NPPointHgtR7_keyAt_three h2 hq]; exact WithTop.natCast_ne_top _⟩⟩
  · refine ⟨⟨s2NPPointMk, fun hg => absurd hg.2 (lt_irrefl 4), ?_⟩⟩
    rw [s2NPPointHgtR7_keyAt_four h2 hq]
    exact WithTop.coe_ne_top

/-- **the `key_value` field, exact shape**: read off the legality package. -/
theorem s2NPFour_key_value : ∀ i, GaugeLive 4 i → ∀ x : S2NPPoint,
    s2NPPtFour h2 hq i x →
    s2NPPointHgtR7 h2 hq i x ((s2DepthFourKeyChain h2 hq).keyAt i)
      = (((s2DepthFour h2 hq).u (i + 1) : ℕ) : WithTop ℤ) :=
  fun _ hi _ hx => hx.1 hi

/-- the finiteness half of the `window` field, read off the legality package. -/
theorem s2NPFour_window_ne_top : ∀ i, StageLive 4 i → ∀ x : S2NPPoint,
    s2NPPtFour h2 hq i x →
    s2NPPointHgtR7 h2 hq i x ((s2DepthFourKeyChain h2 hq).keyAt i) ≠ ⊤ :=
  fun _ _ _ hx => hx.2

/-! ## Part 3 — the augmented stage tables and the threshold tables -/

/-- **the AUGMENTED stage `hgt` table**: `s2Hgt₁ / s2Hgt₃ / s2Hgt₄ / s2Hgt₅` at levels
`1 / 2 / 3 / 4` — the tables the shifted point reads restrict to on the slot ranges (see
the module docstring: R1's `s2NPHgtFour` sits one slot lower and cannot serve, Part 0). -/
noncomputable def s2R7Hgt (i : ℕ) : Polynomial O → WithTop ℤ :=
  if i ≤ 1 then s2Hgt₁ h2 hq
  else if i ≤ 2 then s2Hgt₃ h2 hq
  else if i ≤ 3 then s2Hgt₄ h2 hq
  else s2Hgt₅ h2 hq

theorem s2R7Hgt_one : s2R7Hgt h2 hq 1 = s2Hgt₁ h2 hq := rfl
theorem s2R7Hgt_two : s2R7Hgt h2 hq 2 = s2Hgt₃ h2 hq := rfl
theorem s2R7Hgt_three : s2R7Hgt h2 hq 3 = s2Hgt₄ h2 hq := rfl
theorem s2R7Hgt_four : s2R7Hgt h2 hq 4 = s2Hgt₅ h2 hq := rfl

/-- CONTRAST tooth (the R34 decision, table form): the augmented table genuinely differs
from R1's four-branch `s2NPHgtFour` at the level-3 key — `85 ≠ 42` — so the shift is
forced content, not a renaming. -/
theorem s2R7Hgt_three_ne_direct :
    s2R7Hgt h2 hq 3 (g8 h2 hq) ≠ s2NPHgtFour h2 hq 3 (g8 h2 hq) := by
  rw [s2R7Hgt_three h2 hq, s2NPHgtFour_three h2 hq, s2Hgt₄_g8 h2 hq, s2Hgt₃_g8 h2 hq]
  intro h
  exact absurd (WithTop.coe_inj.mp h) (by norm_num)

/-- **the AUGMENTED stage `dig` table**: `s2Dig₁` (NP-1) at level 1, R1's μ₃/μ₄/μ₅ digit
banks at levels 2/3/4 — each the bank built against the SAME table `s2R7Hgt` reads. -/
noncomputable def s2R7Dig (i : ℕ) : Polynomial O → (s2DepthFour h2 hq).fld i :=
  if i ≤ 1 then s2Dig₁ h2 hq
  else if i ≤ 2 then s2Dig₃ h2 hq
  else if i ≤ 3 then s2Dig₄ h2 hq
  else s2Dig₅ h2 hq

theorem s2R7Dig_one : s2R7Dig h2 hq 1 = s2Dig₁ h2 hq := rfl
theorem s2R7Dig_two : s2R7Dig h2 hq 2 = s2Dig₃ h2 hq := rfl
theorem s2R7Dig_three : s2R7Dig h2 hq 3 = s2Dig₄ h2 hq := rfl
theorem s2R7Dig_four : s2R7Dig h2 hq 4 = s2Dig₅ h2 hq := rfl

/-- **the `Full` table**: realizability of the height by a nonzero slot-range polynomial —
the unique lawful shape at every level (NP-1/CC-6's own pattern, uniformly). -/
def s2R7Full (i : ℕ) (k : ℤ) : Prop :=
  ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum i ∧
    s2R7Hgt h2 hq i A = (k : WithTop ℤ)

/-- pin: at the terminal level the `Full` table IS R2's μ₅ predicate. -/
theorem s2R7Full_four : s2R7Full h2 hq 4 = S2Full₅ h2 hq := rfl

/-- the depth-four stage fields all have exactly two elements (the constant residue
tower, `C80.card_K₁` — one statement serving every index). -/
theorem s2R7Fld_card (i : ℕ) : Nat.card ((s2DepthFour h2 hq).fld i) = 2 :=
  C80.card_K₁ h2 hq

/-- local copy of R1's private card-2 collapse: every nonzero element is `1`. -/
private theorem s2r4_eq_one_of_ne_zero {F : Type} [Field F] (hcard : Nat.card F = 2)
    {c : F} (hc : c ≠ 0) : c = 1 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : Fˣ) : F) := (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- ★ **the `lift` law at every live level, generically** (R1's card-2 argument, run once
against the augmented tables): the `Full` witness realizes every nonzero digit. -/
theorem s2R7_lift :
    ∀ i, StageLive 4 i → ∀ k : ℤ, s2R7Full h2 hq i k →
      ∀ c : (s2DepthFour h2 hq).fld i, c ≠ 0 →
      ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum i ∧
        s2R7Hgt h2 hq i A = (k : WithTop ℤ) ∧ s2R7Dig h2 hq i A = c := by
  intro i hi k hk c hc
  obtain ⟨A, hA0, hdeg, hgtA⟩ := hk
  refine ⟨A, hA0, hdeg, hgtA, ?_⟩
  rw [s2r4_eq_one_of_ne_zero (s2R7Fld_card h2 hq i) hc]
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  · exact s2Dig₁_of_ne_zero h2 hq hA0
  · exact s2Dig₃_of_ne_zero h2 hq hA0
  · exact s2Dig₄_of_ne_zero h2 hq hA0
  · exact s2Dig₅_of_ne_zero h2 hq hA0

/-- **the integer threshold table**: the FOUR open source datums, verbatim — level 1 the
landed `S2LevelOneThreshold` (NP-4/NP-5), levels 2–4 R4's mirrors.  No invented numeral;
no seam formula is assumed at the now-gauge-live level 2 (the seam reading is the
depth-TWO terminal datum — whether it is also the depth-four level-2 inherited threshold
is a faithfulness question the parametrization leaves open). -/
def s2R7ThresholdZ (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
    (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour) (i : ℕ) : ℤ :=
  if i ≤ 1 then w₁.T else if i ≤ 2 then w₂.T else if i ≤ 3 then w₃.T else w₄.T

/-- the natural-avatar threshold table. -/
def s2R7ThresholdNat (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
    (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour) (i : ℕ) : ℕ :=
  if i ≤ 1 then w₁.Tnat else if i ≤ 2 then w₂.Tnat else if i ≤ 3 then w₃.Tnat else w₄.Tnat

/-! ## Part 4 — R6: the wired gauge fields at depth four

The terminal field of the depth-four witness is the SAME two-element constant field, so
NP-8's forcing analysis transports verbatim: `arenaRead`/`peelUnit` are FORCED (the unit
group is a singleton); `towerRead` is genuinely free (`0 ≠ 1`) and is wired to the
law-satisfying value `1` ONCE, at construction — IFC4's licence, mandated at depth ≥ 4 by
the GCW-6 fence ("R7/R9 may not publish an unwired depth-four witness"). -/

/-- the depth-four terminal unit group is a singleton (NP-8's argument at `s2Fld₄_card`). -/
theorem s2FourUnit_eq_one (u : ((s2DepthFour h2 hq).fld 4)ˣ) : u = 1 := by
  haveI : Finite ((s2DepthFour h2 hq).fld 4) :=
    Nat.finite_of_card_ne_zero (by rw [s2R7Fld_card h2 hq 4]; norm_num)
  have hu : Nat.card ((s2DepthFour h2 hq).fld 4)ˣ = 1 := by
    rw [Nat.card_units, s2R7Fld_card h2 hq 4]
  haveI : Subsingleton ((s2DepthFour h2 hq).fld 4)ˣ :=
    (Nat.card_eq_one_iff_unique.mp hu).1
  exact Subsingleton.elim u 1

/-- **the `arenaRead` field**: the trivial monoid hom at every index — FORCED. -/
noncomputable def s2ArenaReadFour (i : ℕ) :
    MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) i) →*
      ((s2DepthFour h2 hq).fld 4)ˣ where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := fun _ _ => (mul_one (1 : ((s2DepthFour h2 hq).fld 4)ˣ)).symm

/-- pin: the arena read's value is the numeral `1`, everywhere. -/
theorem s2ArenaReadFour_apply {i : ℕ}
    (x : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) i)) :
    (s2ArenaReadFour h2 hq i x : (s2DepthFour h2 hq).fld 4) = 1 := rfl

/-- ★ the "free arena" defense: ANY candidate agrees with `s2ArenaReadFour` — forced. -/
theorem s2ArenaReadFour_forced (i : ℕ)
    (f : MonoidHom.ker (levelExponentHeight (s2DepthFour h2 hq) i) →*
      ((s2DepthFour h2 hq).fld 4)ˣ) :
    f = s2ArenaReadFour h2 hq i :=
  MonoidHom.ext fun x => (s2FourUnit_eq_one h2 hq (f x)).trans
    (s2FourUnit_eq_one h2 hq _).symm

/-- **the `peelUnit` field**: the constant `1` — forced by the same singleton. -/
noncomputable def s2PeelUnitFour : ℕ → ((s2DepthFour h2 hq).fld 4)ˣ := fun _ => 1

/-- pin: the peel unit's value is the numeral `1`, everywhere. -/
theorem s2PeelUnitFour_apply (i : ℕ) :
    (s2PeelUnitFour h2 hq i : (s2DepthFour h2 hq).fld 4) = 1 := rfl

/-- ★ the "free peel" defense: ANY candidate agrees with `s2PeelUnitFour` — forced. -/
theorem s2PeelUnitFour_forced (w : ℕ → ((s2DepthFour h2 hq).fld 4)ˣ) :
    w = s2PeelUnitFour h2 hq :=
  funext fun i => (s2FourUnit_eq_one h2 hq (w i)).trans
    (s2FourUnit_eq_one h2 hq _).symm

/-- ★ **R6 — the LAW-SATISFYING tower read, wired at construction** (IFC4's
`s2TowerReadWired` one tower deeper; the value the signed GC-13 law forces at ladder
points, chosen ONCE here per the GCW-6 fence — the depth-four witness is never published
unwired). -/
def s2TowerReadFourWired :
    (i : ℕ) → LevelExponentLattice i → (s2DepthFour h2 hq).fld 4 :=
  fun _ _ => 1

/-- pin: the wired read's value is the numeral `1`, at every index and lattice point. -/
theorem s2TowerReadFourWired_apply (i : ℕ) (g : LevelExponentLattice i) :
    s2TowerReadFourWired h2 hq i g = 1 := rfl

/-- the free-choice disclosure (NP-8's contrast fact at depth four): the read's codomain
has two distinct elements, so the wired value is a genuine CHOICE — licensed at exactly
this construction site — not a forced term like the arena/peel fields. -/
theorem s2FourKt_zero_ne_one : (0 : (s2DepthFour h2 hq).fld 4) ≠ 1 :=
  zero_ne_one

/-! ## Part 5 — ★★ R7: THE DEPTH-FOUR SPLIT NODE -/

section Node

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]

/-- ★★ **R7 — the first depth-four `SplitNodePointSource`**, at the R0 receiver
(`s2TerminalReceiverFour`) and the D3-19 chain (`s2DepthFourKeyChain`), conditional on
exactly the four open threshold datums.  Field provenance: points/evaluation NP-0
(verbatim), the SHIFTED valuation dispatch Part 1 (branches NP-0/R3), stage tables Part 3
(NP-1 + R1's banks against the landed μ₃/μ₄/μ₅ tables), thresholds/windows R4, letters/
ψ-root/canonical read R5 (`s2AmbientLetterFour`/`s2CanonicalReadFour` — the R5 handoff's
named `canonicalRead` pin holds by `rfl`), gauge fields Part 4 (R6, wired at
construction). -/
noncomputable def s2SplitNodeFour (w₁ : S2LevelOneThreshold)
    (w₂ : S2LevelTwoThresholdFour) (w₃ : S2LevelThreeThresholdFour)
    (w₄ : S2LevelFourThresholdFour) :
    SplitNodePointSource (L := L) (s2DepthFour h2 hq) (FractionRing (Polynomial O))
      (s2TerminalReceiverFour h2 hq) (s2DepthFourKeyChain h2 hq) where
  Point := S2NPPoint
  Pt := s2NPPtFour h2 hq
  point_exists := s2NPFour_point_exists h2 hq
  coeffHom := s2NPCoeffHom
  coord := s2NPCoord
  valueOn := s2NPValueOnR7 h2 hq
  value_zero := fun i _ => (s2NPValuationR7 h2 hq i).map_zero
  value_mul := fun i _ a b => (s2NPValuationR7 h2 hq i).map_mul a b
  value_add_ge := fun i _ a b => (s2NPValuationR7 h2 hq i).map_add a b
  value_add_eq := fun i _ a b hne => (s2NPValuationR7 h2 hq i).map_add_of_distinct_val hne
  hgt := s2R7Hgt h2 hq
  dig := s2R7Dig h2 hq
  pointHgt := s2NPPointHgtR7 h2 hq
  pointDig := fun i _ A => s2R7Dig h2 hq i A
  pointHgt_eval := fun _ _ _ => rfl
  slot_value := by
    intro i hi x _hx A _hA hdeg
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact (s2NPPointHgtR7_one h2 hq x A).trans
        (s2PHgt₁_eq_s2Hgt₁_of_natDegree_lt h2 hq
          (by rwa [s2DepthFour_Dcum_one h2 hq] at hdeg))
    · exact s2NPPointHgtR7_two h2 hq x A
    · exact s2NPPointHgtR7_three h2 hq x A
    · exact s2NPPointHgtR7_four h2 hq x A
  slot_digit := fun _ _ _ _ _ _ _ => rfl
  hgt_zero := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_zero h2 hq
    · exact s2Hgt₃_zero h2 hq
    · exact s2Hgt₄_zero h2 hq
    · exact s2Hgt₅_zero h2 hq
  dig_zero := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Dig₁_zero h2 hq
    · exact s2Dig₃_zero h2 hq
    · exact s2Dig₄_zero h2 hq
    · exact s2Dig₅_zero h2 hq
  hgt_ne_top := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact fun A hA _ => s2Hgt₁_ne_top h2 hq hA
    · exact fun A hA _ => s2Hgt₃_ne_top h2 hq hA
    · exact fun A hA _ => s2Hgt₄_ne_top h2 hq hA
    · exact fun A hA _ => s2Hgt₅_ne_top h2 hq hA
  dig_ne_zero := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact fun A hA hdeg => s2Dig₁_ne_zero h2 hq A hA
        (by rw [s2DepthTwo_Dcum_one h2 hq]
            rwa [s2DepthFour_Dcum_one h2 hq] at hdeg)
    · exact fun A hA hdeg => s2Dig₃_ne_zero h2 hq A hA
        (by rw [s2DepthFour_Dcum_three h2 hq]
            rw [s2DepthFour_Dcum_two h2 hq] at hdeg
            omega)
    · exact fun A hA hdeg => s2Dig₄_ne_zero h2 hq A hA
        (by rw [s2DepthFour_Dcum_four h2 hq]
            rw [s2DepthFour_Dcum_three h2 hq] at hdeg
            omega)
    · exact fun A hA hdeg => s2Dig₅_ne_zero h2 hq A hA hdeg
  hgt_add_ge := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_add_ge h2 hq
    · exact s2Hgt₃_add_ge h2 hq
    · exact s2Hgt₄_add_ge h2 hq
    · exact s2Hgt₅_add_ge h2 hq
  hgt_add_eq := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_add_eq h2 hq
    · exact s2Hgt₃_add_eq h2 hq
    · exact s2Hgt₄_add_eq h2 hq
    · exact s2Hgt₅_add_eq h2 hq
  dig_add := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Dig₁_add h2 hq
    · exact s2Dig₃_add h2 hq
    · exact s2Dig₄_add h2 hq
    · exact s2Dig₅_add h2 hq
  Full := s2R7Full h2 hq
  lift := s2R7_lift h2 hq
  thresholdZ := s2R7ThresholdZ w₁ w₂ w₃ w₄
  thresholdNat := s2R7ThresholdNat w₁ w₂ w₃ w₄
  threshold_nonneg := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact w₁.T_natCast
    · exact w₂.T_natCast
    · exact w₃.T_natCast
    · exact w₄.T_natCast
  window := by
    intro i hi x hx
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · refine ⟨?_, hx.2⟩
      exact s2LevelOneWindow_strict w₁
        ((hx.1 ⟨le_refl 1, by omega⟩).trans
          (show (((s2DepthFour h2 hq).u 2 : ℕ) : WithTop ℤ) = ((5 : ℤ) : WithTop ℤ) from by
            show (((5 : ℕ) : ℤ) : WithTop ℤ) = ((5 : ℤ) : WithTop ℤ); norm_num))
    · refine ⟨?_, hx.2⟩
      exact s2LevelTwoWindow_strict w₂
        ((hx.1 ⟨by omega, by omega⟩).trans
          (show (((s2DepthFour h2 hq).u 3 : ℕ) : WithTop ℤ) = ((21 : ℤ) : WithTop ℤ) from by
            show (((21 : ℕ) : ℤ) : WithTop ℤ) = ((21 : ℤ) : WithTop ℤ); norm_num))
    · refine ⟨?_, hx.2⟩
      exact s2LevelThreeWindow_strict w₃
        ((hx.1 ⟨by omega, by omega⟩).trans
          (show (((s2DepthFour h2 hq).u 4 : ℕ) : WithTop ℤ) = ((85 : ℤ) : WithTop ℤ) from by
            show (((85 : ℕ) : ℤ) : WithTop ℤ) = ((85 : ℤ) : WithTop ℤ); norm_num))
    · refine ⟨?_, hx.2⟩
      exact s2LevelFourWindow_strict w₄ (s2NPPointHgtR7_keyAt_four h2 hq x)
  ambientLetter := s2AmbientLetterFour L
  key_value := s2NPFour_key_value h2 hq
  psi_root := fun i hi => s2AmbientLetterFour_psi_root h2 hq L i hi
  canonicalRead := s2CanonicalReadFour h2 hq L
  arenaRead := s2ArenaReadFour h2 hq
  towerRead := s2TowerReadFourWired h2 hq
  peelUnit := s2PeelUnitFour h2 hq

variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)

/-! ### the stage-table and read pins (all `rfl` — the assembly reads the landed names) -/

/-- pin: the node's stage tables ARE the augmented Part-3 tables, definitionally. -/
theorem s2SplitNodeFour_tables :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).hgt = s2R7Hgt h2 hq ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).dig = s2R7Dig h2 hq ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).Full = s2R7Full h2 hq :=
  ⟨rfl, rfl, rfl⟩

/-- ★ pin (the R2 tie): the node's terminal-level stage tables are R2's μ₅ bank —
`hgt 4 = s2Hgt₅`, `dig 4 = s2Dig₅`, `Full 4 = S2Full₅`. -/
theorem s2SplitNodeFour_level_four_ties :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).hgt 4 = s2Hgt₅ h2 hq ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).dig 4 = s2Dig₅ h2 hq ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).Full 4 = S2Full₅ h2 hq :=
  ⟨rfl, rfl, rfl⟩

/-- ★★ pin (the R2 carrier tie): the node's level-4 stage carrier IS R2's
`s2SlotFourMu5`, the slot carrier built for the μ₅ refinement. -/
theorem s2SplitNodeFour_stageCarrier_four :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).stageCarrier 4 ⟨by omega, le_refl 4⟩
      = s2SlotFourMu5 h2 hq := rfl

/-- pin (the R5 handoff key): the node's canonical read IS R5's `s2CanonicalReadFour`,
definitionally — the exact hypothesis of the three R5 handoff theorems. -/
theorem s2SplitNodeFour_canonicalRead :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).canonicalRead = s2CanonicalReadFour h2 hq L :=
  rfl

/-- pin: the node's point read is the shifted dispatcher, definitionally. -/
theorem s2SplitNodeFour_pointHgt :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).pointHgt = s2NPPointHgtR7 h2 hq := rfl

/-- pin: the four thresholds are the four open datums, definitionally. -/
theorem s2SplitNodeFour_thresholds :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdZ 1 = w₁.T ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdZ 2 = w₂.T ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdZ 3 = w₃.T ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).thresholdZ 4 = w₄.T :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### the ONE-FIELD READ AUDIT (R6/R7's charge)

The three gauge fields: two are FORCED (any node at this witness carries the same
`arenaRead`/`peelUnit` values — Part 4's defense theorems), one is FREE and wired.  So the
witness is "wired at construction" in the exact IFC4 sense: `towerRead` is the unique
field where a choice existed, and the choice is the law-satisfying `1`. -/

/-- audit: the node's wired read IS the Part-4 wired read, definitionally. -/
theorem s2SplitNodeFour_towerRead :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).towerRead = s2TowerReadFourWired h2 hq := rfl

/-- audit: the node's arena read and peel unit are the FORCED values — so `towerRead` is
the one genuinely chosen gauge field (the one-field audit). -/
theorem s2SplitNodeFour_forced_fields :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).arenaRead = s2ArenaReadFour h2 hq ∧
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).peelUnit = s2PeelUnitFour h2 hq :=
  ⟨rfl, rfl⟩

/-- ★ live export pin: on the gauge-live range the exported tower-read family reads the
wired value `1` at every projected component. -/
theorem s2SplitNodeFour_towerReadFamily0_live {j : ℕ} (hj : GaugeLive 4 j)
    (g : GaugeLattice0 4) :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).towerReadFamily0 j g = 1 := by
  rw [SplitNodePointSource.towerReadFamily0_live _ hj]
  rfl

/-- junk export pin (no swallowing): off the gauge-live range the exported family is the
CC-11 junk `0`, NOT the wired value — nobody may quote this witness as "read ≡ 1 at every
level". -/
theorem s2SplitNodeFour_towerReadFamily0_junk {j : ℕ} (hj : ¬ GaugeLive 4 j)
    (g : GaugeLattice0 4) :
    (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).towerReadFamily0 j g = 0 :=
  SplitNodePointSource.towerReadFamily0_junk _ hj g

end Node

/-! ## Part 6 — ★★ R7: THE DEPTH-FOUR CHAIN REALIZATION -/

section Realization

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)

/-- ★★ **R7 — the depth-four `ChainRealization`**: receiver R0, keys D3-19, normalizer
R0, node Part 5 — conditional on exactly the four open threshold datums. -/
noncomputable def s2FourChainRealization :
    ChainRealization (s2DepthFour h2 hq) ((s2DepthFour h2 hq).fld 4)
      (FractionRing (Polynomial O)) L where
  receiver := s2TerminalReceiverFour h2 hq
  keys := s2DepthFourKeyChain h2 hq
  normalizer := s2LaurentNormalizerFour h2 hq
  node := s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄

/-- pins: the realization's four legs are the four landed names, definitionally. -/
theorem s2FourChainRealization_legs :
    (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).receiver = s2TerminalReceiverFour h2 hq ∧
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).keys = s2DepthFourKeyChain h2 hq ∧
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer
        = s2LaurentNormalizerFour h2 hq ∧
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node
        = s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄ :=
  ⟨rfl, rfl, rfl, rfl⟩

end Realization

/-! ## Part 7 — R34's second open CLOSED: the `.ofSplitNode` necessity mirrors

`C130sg.S2LevelOneThreshold.ofSplitNode` proved every depth-TWO node forces the level-1
datum.  With the depth-four node type now inhabited-shaped, the gauge-live mirrors land at
levels 2 and 3 (via `key_value`, exactly the level-1 argument one and two towers up).  At
the TERMINAL level 4 the converse is NOT forced by the field list: `window` bounds `T₄`
only by the node's OWN terminal key read, which no field pins to `171` — the honest form
is conditional on that read (and holds at the Part-5 witness, whose read is `171`). -/

section Necessity

variable {E' : Type} [Field E'] (L : Type uL) [Field L]
  [Algebra ((s2DepthFour h2 hq).fld 4) L]

/-- ★ necessity at level 2 (R34's deferred open, gauge-live half): EVERY depth-four split
node at the repository pair carries an `S2LevelTwoThresholdFour`. -/
noncomputable def s2LevelTwoThresholdFour_ofSplitNode
    (S : SplitNodePointSource (L := L) (s2DepthFour h2 hq) E'
      (s2TerminalReceiverFour h2 hq) (s2DepthFourKeyChain h2 hq)) :
    S2LevelTwoThresholdFour where
  T := S.thresholdZ 2
  Tnat := S.thresholdNat 2
  T_natCast := S.threshold_nonneg 2 (by constructor <;> omega)
  T_lt_key := by
    obtain ⟨x, hx⟩ := (S.point_exists 2 ⟨by omega, by omega⟩).some
    have hwin := (S.window 2 ⟨by omega, by omega⟩ x hx).1
    rw [S.key_value 2 ⟨by omega, by omega⟩ x hx,
      show (((s2DepthFour h2 hq).u (2 + 1) : ℕ) : WithTop ℤ) = ((21 : ℤ) : WithTop ℤ)
        from by
          show (((21 : ℕ) : ℤ) : WithTop ℤ) = ((21 : ℤ) : WithTop ℤ); norm_num] at hwin
    exact WithTop.coe_lt_coe.mp hwin

/-- ★ necessity at level 3 (R34's deferred open, gauge-live half): EVERY depth-four split
node at the repository pair carries an `S2LevelThreeThresholdFour`. -/
noncomputable def s2LevelThreeThresholdFour_ofSplitNode
    (S : SplitNodePointSource (L := L) (s2DepthFour h2 hq) E'
      (s2TerminalReceiverFour h2 hq) (s2DepthFourKeyChain h2 hq)) :
    S2LevelThreeThresholdFour where
  T := S.thresholdZ 3
  Tnat := S.thresholdNat 3
  T_natCast := S.threshold_nonneg 3 (by constructor <;> omega)
  T_lt_key := by
    obtain ⟨x, hx⟩ := (S.point_exists 3 ⟨by omega, by omega⟩).some
    have hwin := (S.window 3 ⟨by omega, by omega⟩ x hx).1
    rw [S.key_value 3 ⟨by omega, by omega⟩ x hx,
      show (((s2DepthFour h2 hq).u (3 + 1) : ℕ) : WithTop ℤ) = ((85 : ℤ) : WithTop ℤ)
        from by
          show (((85 : ℕ) : ℤ) : WithTop ℤ) = ((85 : ℤ) : WithTop ℤ); norm_num] at hwin
    exact WithTop.coe_lt_coe.mp hwin

/-- necessity at level 4, the honest CONDITIONAL form: the terminal level is not
gauge-live, so no field pins the node's terminal key read to `171`; given that read (which
the Part-5 witness computes — `s2NPPointHgtR7_keyAt_four`), the datum follows from
`window`. -/
noncomputable def s2LevelFourThresholdFour_ofSplitNode_of_read
    (S : SplitNodePointSource (L := L) (s2DepthFour h2 hq) E'
      (s2TerminalReceiverFour h2 hq) (s2DepthFourKeyChain h2 hq))
    (x : S.Point) (hx : S.Pt 4 x)
    (hread : S.pointHgt 4 x ((s2DepthFourKeyChain h2 hq).keyAt 4)
      = ((171 : ℤ) : WithTop ℤ)) :
    S2LevelFourThresholdFour where
  T := S.thresholdZ 4
  Tnat := S.thresholdNat 4
  T_natCast := S.threshold_nonneg 4 (by constructor <;> omega)
  T_lt_key := by
    have hwin := (S.window 4 ⟨by omega, le_refl 4⟩ x hx).1
    rw [hread] at hwin
    exact WithTop.coe_lt_coe.mp hwin

/-- roundtrip teeth: the Part-5 witness itself carries all three necessity datums back —
levels 2/3 unconditionally, level 4 through its own computed terminal read `171`
(`s2NPPointHgtR7_keyAt_four`).  Non-vacuity of the mirrors at the canonical witness. -/
example (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
    (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour) :
    S2LevelTwoThresholdFour × S2LevelThreeThresholdFour × S2LevelFourThresholdFour :=
  ⟨s2LevelTwoThresholdFour_ofSplitNode h2 hq L (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄),
   s2LevelThreeThresholdFour_ofSplitNode h2 hq L (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄),
   s2LevelFourThresholdFour_ofSplitNode_of_read h2 hq L
     (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄)
     ((s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).legalPoint 4 ⟨by omega, le_refl 4⟩)
     ((s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).legalPoint_mem 4 ⟨by omega, le_refl 4⟩)
     (s2NPPointHgtR7_keyAt_four h2 hq _)⟩

end Necessity

/-! ## Part 8 — the R5 handoff DISCHARGED, and the R8/R9 packaging

`CanonicalGeneratorDescent`/`DeepLevelExport` are typed at an `ArisingCore` +
`ChainRealization` (`Uniformity.Density.DeepExport`, gate G4).  The core's input payload
(`F₀`, `μ`, key-freeness) is R8/R8r's gated content; everything ELSE the records need, the
Part 5/6 witness supplies.  So the packaging below is parametric in exactly that payload:
`s2FourArisingCoreOf` builds the core at the depth-four data, `s2FourRealizedInputOf`
selects the legal point, and the descent record is inhabited at every gauge-live level of
the resulting realization — the G4 `DeepLevelExport` then wants only the G3 site package
(row C0), consumed through `ofLetterEq` below. -/

section Discharge

open Uniformity.Density.DeepExport

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **the depth-four `ArisingCore` packaging**, parametric in exactly the R8/R8r payload
(the input polynomial, its block data, and the key-freeness gate — D4-15's coprimality at
`F₀ = leaf²`, G9-gated, NOT invented here): stage `i = r = 4`, stage key `g16`, stage
degree `16`, at the R0 receiver. -/
noncomputable def s2FourArisingCoreOf {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic)
    (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
    (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
      ((g16 h2 hq).map (algebraMap O (FractionRing O)))) :
    ArisingCore (O := O) ((s2DepthFour h2 hq).fld 4) L n where
  π := 2
  hπ := h2
  complete := inferInstance
  finite := inferInstance
  F := s2Frame h2 hq
  H₀ := 1
  hpin := s2Frame_pin h2 hq
  r := 4
  i := 4
  hi := ⟨by omega, le_refl 4⟩
  T := s2DepthFour h2 hq
  receiver := s2TerminalReceiverFour h2 hq
  stageKey := g16 h2 hq
  stageDeg := 16
  stageKey_monic := g16_monic h2 hq
  stageKey_degree := g16_natDegree h2 hq
  F₀ := F₀
  F₀_monic := hF₀
  μ := μ
  hμ := hμ
  degree_input := hdeg
  degree_block := hblock
  keyfree := hcop

variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)

/-- ★ **the depth-four `RealizedInput` packaging** at the Part-6 realization: the three
repository dictionaries are `rfl`/landed pins, the selected point is the canonical legal
point at stage 4.  Parametric in exactly the R8/R8r payload; NO payload instance is
landed (G9's gate). -/
noncomputable def s2FourRealizedInputOf {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic)
    (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
    (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
      ((g16 h2 hq).map (algebraMap O (FractionRing O)))) :
    RealizedInput (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) where
  receiver_eq := rfl
  stageKey_eq := (s2DepthFourKeyAt_four h2 hq).symm
  stageDeg_eq := (s2DepthFour_Dcum_four h2 hq).symm
  point := (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).legalPoint 4 ⟨by omega, le_refl 4⟩
  point_mem := (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄).legalPoint_mem 4 ⟨by omega, le_refl 4⟩

/-- ★★ **the R5 handoff discharged — `CanonicalGeneratorDescent` INHABITED at the
depth-four realization**, at every gauge-live level: the node's `canonicalRead` is R5's
`s2CanonicalReadFour` by `rfl`, so the two named handoff theorems fire directly.  (G4's
TAU-dictionary component, at the first depth-four witness.) -/
theorem s2Four_canonicalGeneratorDescent {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic)
    (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
    (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
      ((g16 h2 hq).map (algebraMap O (FractionRing O))))
    {j : ℕ} (hj : GaugeLive 4 j) :
    CanonicalGeneratorDescent
      (core := s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄) j hj :=
  ⟨s2four_node_wrapValue_descent h2 hq L (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄) hj rfl,
    fun a => s2four_node_letterValue_descent h2 hq L
      (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄) hj a rfl⟩

/-- ★★ **the G4 record at the witness, conditional on exactly the G3 site package**: given
a `WleClearedLevelExport` at the deep-live level `j = 3` whose calculus letters tie to the
μ₄ letters (the site-calculus truncation transport, R5's recorded handoff item (ii)), the
shared `DeepLevelExport` record is inhabited through `ofLetterEq` — the wrap descent and
the receiver/letter equalities are the witness's own (R5's handoff theorems at
`hread := rfl`).  Row C0 supplies the site. -/
noncomputable def s2Four_deepLevelExport_of_site {n : ℕ} (F₀ : Polynomial O)
    (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ) (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
    (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
      ((g16 h2 hq).map (algebraMap O (FractionRing O))))
    (hj : DeepLive 4 3)
    (site : WleClearedLevelExport.{0, 0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj.2.le)
    (hletterZ : ∀ a : Fin (3 - 1),
      algebraMap ((s2DepthFour h2 hq).fld 4) L
          ((s2TerminalReceiverFour h2 hq).levelHom 3 (site.calculus.letterZ (a.1 + 2)))
        = algebraMap ((s2DepthFour h2 hq).fld 4) L
          ((s2TerminalReceiverFour h2 hq).levelHom 3
            ((s2Mu4Calculus h2 hq).letterZ (a.1 + 2)))) :
    DeepLevelExport.{0, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj :=
  DeepLevelExport.ofLetterEq site
    (s2four_node_wrapValue_descent h2 hq L (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄)
      hj.gaugeLive rfl)
    (fun a => (hletterZ a).trans
      (s2four_node_letter_receiver h2 hq L (s2SplitNodeFour h2 hq L w₁ w₂ w₃ w₄) rfl
        hj.gaugeLive.stageLive a))

end Discharge

end Uniformity.Density.Tower.C136r4

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none. -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136r4.s2FourKeyAt_three
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtFour_three_keyAt
#print axioms Uniformity.Density.Tower.C136r4.s2R34_direct_choice_fails_key_value
#print axioms Uniformity.Density.Tower.C136r4.s2NPValuationR7
#print axioms Uniformity.Density.Tower.C136r4.s2NPValueOnR7
#print axioms Uniformity.Density.Tower.C136r4.s2NPValueOnR7_one
#print axioms Uniformity.Density.Tower.C136r4.s2NPValueOnR7_two
#print axioms Uniformity.Density.Tower.C136r4.s2NPValueOnR7_three
#print axioms Uniformity.Density.Tower.C136r4.s2NPValueOnR7_four
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_one
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_two
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_three
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_four
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_keyAt_one
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_keyAt_two
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_keyAt_three
#print axioms Uniformity.Density.Tower.C136r4.s2NPPointHgtR7_keyAt_four
#print axioms Uniformity.Density.Tower.C136r4.s2NPPtFour
#print axioms Uniformity.Density.Tower.C136r4.s2NPFour_point_exists
#print axioms Uniformity.Density.Tower.C136r4.s2NPFour_key_value
#print axioms Uniformity.Density.Tower.C136r4.s2NPFour_window_ne_top
#print axioms Uniformity.Density.Tower.C136r4.s2R7Hgt
#print axioms Uniformity.Density.Tower.C136r4.s2R7Hgt_one
#print axioms Uniformity.Density.Tower.C136r4.s2R7Hgt_two
#print axioms Uniformity.Density.Tower.C136r4.s2R7Hgt_three
#print axioms Uniformity.Density.Tower.C136r4.s2R7Hgt_four
#print axioms Uniformity.Density.Tower.C136r4.s2R7Hgt_three_ne_direct
#print axioms Uniformity.Density.Tower.C136r4.s2R7Dig
#print axioms Uniformity.Density.Tower.C136r4.s2R7Full
#print axioms Uniformity.Density.Tower.C136r4.s2R7Full_four
#print axioms Uniformity.Density.Tower.C136r4.s2R7Fld_card
#print axioms Uniformity.Density.Tower.C136r4.s2R7_lift
#print axioms Uniformity.Density.Tower.C136r4.s2R7ThresholdZ
#print axioms Uniformity.Density.Tower.C136r4.s2R7ThresholdNat
#print axioms Uniformity.Density.Tower.C136r4.s2FourUnit_eq_one
#print axioms Uniformity.Density.Tower.C136r4.s2ArenaReadFour
#print axioms Uniformity.Density.Tower.C136r4.s2ArenaReadFour_apply
#print axioms Uniformity.Density.Tower.C136r4.s2ArenaReadFour_forced
#print axioms Uniformity.Density.Tower.C136r4.s2PeelUnitFour
#print axioms Uniformity.Density.Tower.C136r4.s2PeelUnitFour_apply
#print axioms Uniformity.Density.Tower.C136r4.s2PeelUnitFour_forced
#print axioms Uniformity.Density.Tower.C136r4.s2TowerReadFourWired
#print axioms Uniformity.Density.Tower.C136r4.s2TowerReadFourWired_apply
#print axioms Uniformity.Density.Tower.C136r4.s2FourKt_zero_ne_one
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_tables
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_level_four_ties
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_stageCarrier_four
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_canonicalRead
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_pointHgt
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_thresholds
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_towerRead
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_forced_fields
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_towerReadFamily0_live
#print axioms Uniformity.Density.Tower.C136r4.s2SplitNodeFour_towerReadFamily0_junk
#print axioms Uniformity.Density.Tower.C136r4.s2FourChainRealization
#print axioms Uniformity.Density.Tower.C136r4.s2FourChainRealization_legs
#print axioms Uniformity.Density.Tower.C136r4.s2LevelTwoThresholdFour_ofSplitNode
#print axioms Uniformity.Density.Tower.C136r4.s2LevelThreeThresholdFour_ofSplitNode
#print axioms Uniformity.Density.Tower.C136r4.s2LevelFourThresholdFour_ofSplitNode_of_read
#print axioms Uniformity.Density.Tower.C136r4.s2FourArisingCoreOf
#print axioms Uniformity.Density.Tower.C136r4.s2FourRealizedInputOf
#print axioms Uniformity.Density.Tower.C136r4.s2Four_canonicalGeneratorDescent
#print axioms Uniformity.Density.Tower.C136r4.s2Four_deepLevelExport_of_site

end AxCheck
