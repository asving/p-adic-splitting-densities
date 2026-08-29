/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136r1
import Uniformity.ChapC.C130nv5
import Uniformity.ChapC.C132nv6
import Uniformity.ChapC.C132rp10b
import Uniformity.ChapC.C132kp0

/-!
# Uniformity.ChapC.C136r2 — the deep-witness realization rows R3 + R4 [R34 2026-08-28]

**Rows R3 + R4** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4:

* **R3** ("points/evaluation", 60 min): *"Extend the NP point, coefficient hom,
  coordinate, and valuation laws through BOTH new live stages."* Models: `C130s17.s2EvalHom`
  (the point/coefficient/coordinate probe) and `C130sg.s2SplitNode` (the depth-two
  point-valuation dictionary this row extends one/two levels up). Campaign inputs: R1/R2
  (`C136r1`, landed) — the μ₃/μ₄/μ₅ height tables this row's point dictionary ties to.
* **R4** ("thresholds/windows", 60 min): *"Supply source-backed thresholds at levels 1–4
  and prove strict windows; no invented numeral branch."* Model: `C130sg.S2LevelOneThreshold`
  (the open-datum parametrization pattern) + `.ofSplitNode` (the necessity direction, cited
  as the shape, not re-derived here — see the named open below). Campaign floor set: the
  four numerals `5/21/85/171` with margins `4<5, 20<21, 84<85, 170<171`.

## R3 — the point/evaluation dictionary through μ₃, μ₄ (both new live stages) + μ₅ (superset)

`C130np0`'s NP-0 built the depth-two point dictionary (`S2NPPoint`, `s2NPCoeffHom`,
`s2NPCoord`, `s2NPValuation`/`s2NPValueOn`/`s2NPPointHgt`) for the TWO live stages of
`S2DepthTwo`. This row extends it through the depth-four tower's two NEW live stages
(3 = μ₃, 4 = μ₄) — the same `Point`/`coeffHom`/`coord` REUSED verbatim (they are
tower-independent: one canonical evaluation pair serves every level, per NP-0's own design),
with the substantive new content being the STAGE-VALUATION dispatch and its restriction
dictionary against the R1/R2 height tables.

* **Part A** — a generic combinator `s2ExtendVal` that packages + extends ANY landed
  `AddValuation (Polynomial O) (WithTop ℤ)` to `E = FractionRing (Polynomial O)`, replaying
  NV-5/NV-6's hand-written pipeline (`Val → hS → extendToLocalization → ofValuation →
  restriction pin`) ONCE, generically, rather than duplicating it three more times by hand.
  Also proves `s2Hgt₅_eq_top_iff` (genuinely new — the μ₅ finiteness-iff was not landed —
  built from the two already-landed halves `s2Hgt₅_zero`/`s2Hgt₅_ne_top`, C136e0).
* **Part B** — the combinator instantiated at the three landed `AddValuation`s the
  blocker note names: `s2AddVal₃` (μ₃, pre-campaign, `C132nv6`), `s2AddVal₄` (μ₄, D3-05,
  `C136d1`), `s2AddVal₅` (μ₅, D4-03, `C136e0`) — giving `s2AddEVal₃`/`s2AddEVal₄`/
  `s2AddEVal₅` on `E`, each with its restriction PIN back to `s2Hgt₃`/`s2Hgt₄`/`s2Hgt₅`.
* **Part C** — the depth-four point-valuation dispatcher `s2NPValuationFour`/
  `s2NPValueOnFour`/`s2NPPointHgtFour`, a direct four-branch extension of NP-0's
  `s2NPValuation`/`s2NPValueOn`/`s2NPPointHgt` (branches 1/2 UNCHANGED, reusing NP-0's own
  `s2AddEPVal₁`/`s2AddEVal₂`; branches 3/4 supplied by Part B). The four unfenced valuation
  laws (`value_zero/mul/add_ge/add_eq`) transfer with NO extra proof, exactly as at NP-0:
  `s2NPValuationFour h2 hq i` is a genuine `AddValuation` on every branch, so its own
  structure fields (`.map_zero`/`.map_mul`/`.map_add`/`.map_add_of_distinct_val`) supply
  them regardless of `i`. The restriction dictionaries `s2NPPointHgtFour_one/two/three/four`
  tie the point read to `s2PHgt₁`/`s2Hgt₂`/`s2Hgt₃`/`s2Hgt₄` respectively — level 3/4 are the
  genuinely new content; levels 1/2 are restated for the four-branch dispatcher.
* **Part D** (superset) — the μ₅-refinement point read `s2NPPointHgtMu5`, tied to `s2Hgt₅`
  and, via R2's own `s2SlotFourMu5_hgt_eq`, to the landed level-four slot carrier.

### Named open — level-2/3 `key_value` compatibility is UNVERIFIED (not invented)

NP-0's own docstring flags "the ONE genuine design discovery of this node": at the
depth-two tower's gauge-live index 1, NEITHER landed table (`s2Hgt₁` nor `s2Hgt₂`) alone
satisfies both `slot_value` (agreement with the level's own table on low degree) and
`key_value` (`pointHgt 1 x (keyAt 1) = u₂ = 5`) — a bespoke MacLane augmentation
(`s2PHgt₁`) had to be constructed to satisfy both simultaneously. In the depth-four
extension, levels 2 and 3 are NO LONGER terminal (they were the base case's terminal level
and a fresh level respectively) — they are now GAUGE-LIVE, each needing its own
`key_value` law `pointHgt i x (keyAt i) = u_{i+1}` in any future full split-node assembly
(R7). This row's `s2NPPointHgtFour_two`/`_three` tie the point read DIRECTLY to the level's
OWN table (`s2Hgt₂`/`s2Hgt₃`) — the correct choice for `slot_value` by construction, and
exactly the reading the campaign's blocker note asks for ("use the landed `s2AddVal₄`/
`s2AddVal₅`... tied to the point data"). Whether this SAME choice also satisfies the
eventual `key_value` law at levels 2/3 (i.e. whether `s2Hgt₂ (keyAt 2) = u₃ = 21` and
`s2Hgt₃ (keyAt 3) = u₄ = 85`) is NOT checked here — no landed theorem states it, and if it
fails, a bespoke fix analogous to `s2PHgt₁`'s discovery would be needed one level up. This
gap is recorded here, by name, as R7's problem to discover or discharge — not invented
around.

## R4 — source-backed thresholds at levels 1–4, strict windows, no invented numeral

`C130sg.S2LevelOneThreshold` parametrizes the ONE open datum at level 1 (`T₁ < u₂ = 5`,
`u₂` untouched here). This row builds the analogous OPEN-datum structures at levels 2, 3, 4
(`S2LevelTwoThresholdFour`/`S2LevelThreeThresholdFour`/`S2LevelFourThresholdFour`), each with
the SAME field shape (`T`, `Tnat`, `T_natCast`, `T_lt_key`) and the STRICT bound `u_{i+1}`
THREADED from the landed pins — never re-derived:

* level 2's bound `21` is `C132nv1.s2Hgt₃_Φ₂` (`s2Hgt₃ (keyAt 2) = 21`) — the height of
  level 2's own key under the landed μ₃ table, i.e. exactly what `u₃` means;
* level 3's bound `85` is `C136d0.s2Hgt₄_g8` (`s2Hgt₄ (keyAt 3) = 85`), the μ₄ analogue;
* level 4's bound `171` is `C136e0.s2Hgt₅_g16` (`s2Hgt₅ (keyAt 4) = 171`), the μ₅ analogue.

Each structure carries a DISCLOSURE tooth (anonymous, non-consumable, per
`S2LevelOneThreshold`'s own discipline) at the campaign's stated margins — `4 < 5`,
`20 < 21`, `84 < 85`, `170 < 171` — showing the near-maximal legal threshold is
Lean-inhabited at every level; openness is a FAITHFULNESS gap (which numeral the source's
inherited `T_i` is), not an emptiness.

The generic combinator `s2StrictWindow_of_key_value` proves the STRICT half of `window`
once, from a threshold's `T_lt_key` field plus a hypothetical `key_value` fact — exactly
the one-line step `s2SplitNode`'s own `window` proof takes (`WithTop.coe_lt_coe.mpr
w.T_lt_key`), extracted here so a future full split-node assembly (R7) does not re-derive
it per level. It is instantiated at all four levels (`s2LevelOneWindow_strict`/`Two`/
`Three`/`Four`).

### Named open — the necessity direction (`.ofSplitNode`) is deferred

`S2LevelOneThreshold.ofSplitNode` proves every ACTUAL depth-two split node forces the open
datum's bound — the converse of parametrization. No depth-four `SplitNodePointSource`
instance exists yet (that is R7's job), so the analogous necessity theorems for
`S2LevelTwoThresholdFour`/`ThreeFour`/`FourFour` cannot be stated, let alone proved, at this
row; they are left as R7's exit condition once the full node is assembled.

## Status

Zero `sorry`; no new axiom; axiom footprint Lean-core only (AxCheck footer). No landed
statement is touched — only new declarations in a new file. Verdict:
`runs/wave-c/verdict_R34.md`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C136r2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130np3
open Uniformity.Density.Tower.C130sg Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C130nv5
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv6 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136d3ad Uniformity.Density.Tower.C136e0
open Uniformity.Density.Tower.C136t Uniformity.Density.Tower.C136r0
open Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part A — the generic fraction-field valuation-extension combinator -/

/-- the μ₅ finiteness-iff, genuinely new (mirror of `s2Hgt₄_eq_top_iff`/`s2Hgt₃_eq_top_iff`
one level up), built purely from the two already-landed halves `s2Hgt₅_zero`/
`s2Hgt₅_ne_top` — no new mathematics. -/
theorem s2Hgt₅_eq_top_iff {A : Polynomial O} : s2Hgt₅ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro h
    by_contra hA
    exact s2Hgt₅_ne_top h2 hq hA h
  · rintro rfl
    exact s2Hgt₅_zero h2 hq

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- generic repackaging: an `AddValuation`'s `⊤`-characterization transported to its
`Valuation.toValuation`'s `0`-characterization (mirror of `s2Val₁_eq_zero_iff`, one proof
for every level). -/
private theorem s2ExtendVal_eq_zero_iff (v : AddValuation (Polynomial O) (WithTop ℤ))
    (heq : ∀ A : Polynomial O, v A = ⊤ ↔ A = 0) (A : Polynomial O) :
    v.toValuation A = 0 ↔ A = 0 := by
  rw [← Valuation.mem_supp_iff]
  show A ∈ AddValuation.supp v ↔ A = 0
  rw [AddValuation.mem_supp_iff]
  exact heq A

omit [Finite (ResidueField O)] in
/-- the submonoid hypothesis `extendToLocalization` needs, generic (mirror of
`s2Val₁_hS`/`s2Val₂_hS`). -/
private theorem s2ExtendVal_hS (v : AddValuation (Polynomial O) (WithTop ℤ))
    (heq : ∀ A : Polynomial O, v A = ⊤ ↔ A = 0) :
    nonZeroDivisors (Polynomial O) ≤ (v.toValuation).supp.primeCompl := by
  intro x hx
  rw [Ideal.mem_primeCompl_iff, Valuation.mem_supp_iff]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hx
  exact fun h => hx ((s2ExtendVal_eq_zero_iff v heq x).mp h)

/-- ★ **the generic combinator**: package + extend ANY landed `AddValuation (Polynomial O)
(WithTop ℤ)` to `E = FractionRing (Polynomial O)`, replaying NV-5/NV-6's pipeline (`Val`,
`hS`, `extendToLocalization`, `ofValuation`) ONE TIME rather than by hand at every level. -/
private noncomputable def s2ExtendVal (v : AddValuation (Polynomial O) (WithTop ℤ))
    (heq : ∀ A : Polynomial O, v A = ⊤ ↔ A = 0) :
    AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  AddValuation.ofValuation
    ((v.toValuation).extendToLocalization (s2ExtendVal_hS v heq) (FractionRing (Polynomial O)))

omit [Finite (ResidueField O)] in
private theorem s2ExtendVal_apply (v : AddValuation (Polynomial O) (WithTop ℤ))
    (heq : ∀ A : Polynomial O, v A = ⊤ ↔ A = 0) (x : FractionRing (Polynomial O)) :
    s2ExtendVal v heq x =
      (v.toValuation).extendToLocalization (s2ExtendVal_hS v heq)
        (FractionRing (Polynomial O)) x := rfl

omit [Finite (ResidueField O)] in
/-- ★ **the restriction PIN, generic** (mirror of `s2AddEVal₂_algebraMap`): the extension,
restricted along the canonical embedding, IS the original valuation — ONE proof serving
every level's instantiation. -/
theorem s2ExtendVal_algebraMap (v : AddValuation (Polynomial O) (WithTop ℤ))
    (heq : ∀ A : Polynomial O, v A = ⊤ ↔ A = 0) (A : Polynomial O) :
    s2ExtendVal v heq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A) = v A := by
  show (v.toValuation).extendToLocalization (s2ExtendVal_hS v heq)
      (FractionRing (Polynomial O)) (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = v A
  rw [Valuation.extendToLocalization_apply_map_apply]
  rfl

/-! ## Part B — the point valuation extended to μ₃, μ₄, μ₅ -/

/-- the μ₃ point valuation on `E`, from the pre-campaign landed `s2AddVal₃` (`C132nv6`). -/
noncomputable def s2AddEVal₃ : AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  s2ExtendVal (s2AddVal₃ h2 hq)
    (fun A => by rw [s2AddVal₃_apply]; exact s2Hgt₃_eq_top_iff h2 hq)

/-- ★ the restriction PIN at μ₃: the extension, restricted to `Polynomial O`, IS `s2Hgt₃`. -/
theorem s2AddEVal₃_algebraMap (A : Polynomial O) :
    s2AddEVal₃ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = s2Hgt₃ h2 hq A := by
  rw [s2AddEVal₃, s2ExtendVal_algebraMap, s2AddVal₃_apply]

/-- the μ₄ point valuation on `E`, from the campaign's own landed `s2AddVal₄` (D3-05,
`C136d1`) — exactly the datum the R3 blocker note names. -/
noncomputable def s2AddEVal₄ : AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  s2ExtendVal (s2AddVal₄ h2 hq)
    (fun A => by rw [s2AddVal₄_apply]; exact s2Hgt₄_eq_top_iff h2 hq)

/-- ★ the restriction PIN at μ₄: the extension, restricted to `Polynomial O`, IS `s2Hgt₄`. -/
theorem s2AddEVal₄_algebraMap (A : Polynomial O) :
    s2AddEVal₄ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = s2Hgt₄ h2 hq A := by
  rw [s2AddEVal₄, s2ExtendVal_algebraMap, s2AddVal₄_apply]

/-- the μ₅-refinement point valuation on `E`, from the campaign's own landed `s2AddVal₅`
(D4-03, `C136e0`) — the other datum the R3 blocker note names. -/
noncomputable def s2AddEVal₅ : AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  s2ExtendVal (s2AddVal₅ h2 hq)
    (fun A => by rw [s2AddVal₅_apply]; exact s2Hgt₅_eq_top_iff h2 hq)

/-- ★ the restriction PIN at μ₅: the extension, restricted to `Polynomial O`, IS `s2Hgt₅`. -/
theorem s2AddEVal₅_algebraMap (A : Polynomial O) :
    s2AddEVal₅ h2 hq (algebraMap (Polynomial O) (FractionRing (Polynomial O)) A)
      = s2Hgt₅ h2 hq A := by
  rw [s2AddEVal₅, s2ExtendVal_algebraMap, s2AddVal₅_apply]

/-- generic valuation laws at μ₅, unconditional (mirror of NP-0's `s2NPValueOn_zero/mul/
add_ge/add_eq`, direct from `s2AddEVal₅` being a genuine `AddValuation`). -/
theorem s2AddEVal₅_value_zero : s2AddEVal₅ h2 hq 0 = ⊤ := (s2AddEVal₅ h2 hq).map_zero

theorem s2AddEVal₅_value_mul (a b : FractionRing (Polynomial O)) :
    s2AddEVal₅ h2 hq (a * b) = s2AddEVal₅ h2 hq a + s2AddEVal₅ h2 hq b :=
  (s2AddEVal₅ h2 hq).map_mul a b

theorem s2AddEVal₅_value_add_ge (a b : FractionRing (Polynomial O)) :
    min (s2AddEVal₅ h2 hq a) (s2AddEVal₅ h2 hq b) ≤ s2AddEVal₅ h2 hq (a + b) :=
  (s2AddEVal₅ h2 hq).map_add a b

theorem s2AddEVal₅_value_add_eq (a b : FractionRing (Polynomial O))
    (hne : s2AddEVal₅ h2 hq a ≠ s2AddEVal₅ h2 hq b) :
    s2AddEVal₅ h2 hq (a + b) = min (s2AddEVal₅ h2 hq a) (s2AddEVal₅ h2 hq b) :=
  (s2AddEVal₅ h2 hq).map_add_of_distinct_val hne

/-! ## Part C — R3: the depth-four point-valuation dispatcher and its restriction
dictionary against `s2PHgt₁`/`s2Hgt₂`/`s2Hgt₃`/`s2Hgt₄`.  `Point`/`coeffHom`/`coord` are
REUSED verbatim from NP-0 (`S2NPPoint`, `s2NPCoeffHom`, `s2NPCoord`) — no new construction,
per the row's own reading (the probe pair is tower-independent). -/

/-- the depth-four point-valuation dispatch: branches 1/2 UNCHANGED from NP-0's own
`s2NPValuation` (`s2AddEPVal₁`/`s2AddEVal₂`); branches 3/4 supplied by Part B
(`s2AddEVal₃`/`s2AddEVal₄`) — the genuinely new content of this row. -/
noncomputable def s2NPValuationFour (i : ℕ) :
    AddValuation (FractionRing (Polynomial O)) (WithTop ℤ) :=
  if i ≤ 1 then s2AddEPVal₁ h2 hq
  else if i ≤ 2 then s2AddEVal₂ h2 hq
  else if i ≤ 3 then s2AddEVal₃ h2 hq
  else s2AddEVal₄ h2 hq

/-- **the `valueOn` field, depth-four shape.** -/
noncomputable def s2NPValueOnFour (i : ℕ) : FractionRing (Polynomial O) → WithTop ℤ :=
  ⇑(s2NPValuationFour h2 hq i)

theorem s2NPValueOnFour_one : s2NPValueOnFour h2 hq 1 = ⇑(s2AddEPVal₁ h2 hq) := rfl
theorem s2NPValueOnFour_two : s2NPValueOnFour h2 hq 2 = ⇑(s2AddEVal₂ h2 hq) := rfl
theorem s2NPValueOnFour_three : s2NPValueOnFour h2 hq 3 = ⇑(s2AddEVal₃ h2 hq) := rfl
theorem s2NPValueOnFour_four : s2NPValueOnFour h2 hq 4 = ⇑(s2AddEVal₄ h2 hq) := rfl

/-! ### the `valueOn` laws — unfenced (∀ i), exactly as at NP-0 (no case split: every
branch of the dispatch is a genuine `AddValuation`, so its own structure fields answer
regardless of `i`). -/

theorem s2NPValueOnFour_zero (i : ℕ) : s2NPValueOnFour h2 hq i 0 = ⊤ :=
  (s2NPValuationFour h2 hq i).map_zero

theorem s2NPValueOnFour_mul (i : ℕ) (a b : FractionRing (Polynomial O)) :
    s2NPValueOnFour h2 hq i (a * b) = s2NPValueOnFour h2 hq i a + s2NPValueOnFour h2 hq i b :=
  (s2NPValuationFour h2 hq i).map_mul a b

theorem s2NPValueOnFour_add_ge (i : ℕ) (a b : FractionRing (Polynomial O)) :
    min (s2NPValueOnFour h2 hq i a) (s2NPValueOnFour h2 hq i b)
      ≤ s2NPValueOnFour h2 hq i (a + b) :=
  (s2NPValuationFour h2 hq i).map_add a b

theorem s2NPValueOnFour_add_eq (i : ℕ) (a b : FractionRing (Polynomial O))
    (hne : s2NPValueOnFour h2 hq i a ≠ s2NPValueOnFour h2 hq i b) :
    s2NPValueOnFour h2 hq i (a + b) = min (s2NPValueOnFour h2 hq i a) (s2NPValueOnFour h2 hq i b) :=
  (s2NPValuationFour h2 hq i).map_add_of_distinct_val hne

/-- **the `value_zero` field, exact shape, depth four.** -/
theorem s2NP_value_zeroFour : ∀ i, StageLive 4 i → s2NPValueOnFour h2 hq i 0 = ⊤ :=
  fun i _ => s2NPValueOnFour_zero h2 hq i

/-- **the `value_mul` field, exact shape, depth four.** -/
theorem s2NP_value_mulFour : ∀ i, StageLive 4 i → ∀ a b,
    s2NPValueOnFour h2 hq i (a * b) = s2NPValueOnFour h2 hq i a + s2NPValueOnFour h2 hq i b :=
  fun i _ => s2NPValueOnFour_mul h2 hq i

/-- **the `value_add_ge` field, exact shape, depth four.** -/
theorem s2NP_value_add_geFour : ∀ i, StageLive 4 i → ∀ a b,
    min (s2NPValueOnFour h2 hq i a) (s2NPValueOnFour h2 hq i b)
      ≤ s2NPValueOnFour h2 hq i (a + b) :=
  fun i _ => s2NPValueOnFour_add_ge h2 hq i

/-- **the `value_add_eq` field, exact shape, depth four.** -/
theorem s2NP_value_add_eqFour : ∀ i, StageLive 4 i → ∀ a b,
    s2NPValueOnFour h2 hq i a ≠ s2NPValueOnFour h2 hq i b →
      s2NPValueOnFour h2 hq i (a + b) = min (s2NPValueOnFour h2 hq i a) (s2NPValueOnFour h2 hq i b) :=
  fun i _ => s2NPValueOnFour_add_eq h2 hq i

/-- **the `pointHgt` field, depth-four shape**: defined (not tabulated), so
`pointHgt_eval` is `rfl`, exactly as at NP-0. -/
noncomputable def s2NPPointHgtFour (i : ℕ) (x : S2NPPoint) (A : Polynomial O) : WithTop ℤ :=
  s2NPValueOnFour h2 hq i (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A)

/-- **the `pointHgt_eval` field, exact shape, depth four.** -/
theorem s2NP_pointHgt_evalFour : ∀ (i : ℕ) (x : S2NPPoint) (A : Polynomial O),
    s2NPPointHgtFour h2 hq i x A
      = s2NPValueOnFour h2 hq i (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) :=
  fun _ _ _ => rfl

/-! ### the restriction dictionaries: point reads ARE landed polynomial values -/

/-- **stage-1 dictionary, depth four**: unchanged from NP-0. -/
theorem s2NPPointHgtFour_one (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtFour h2 hq 1 x A = s2PHgt₁ h2 hq A := by
  show s2AddEPVal₁ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2PHgt₁ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEPVal₁_algebraMap]

/-- **stage-2 dictionary, depth four**: unchanged from NP-0 — level 2 is no longer
terminal, but its OWN table (`s2Hgt₂`) is still the correct `slot_value` read (see the
docstring's named open on `key_value`). -/
theorem s2NPPointHgtFour_two (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtFour h2 hq 2 x A = s2Hgt₂ h2 hq A := by
  show s2AddEVal₂ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₂ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₂_algebraMap]

/-- ★ **stage-3 dictionary, depth four — genuinely new (μ₃).** -/
theorem s2NPPointHgtFour_three (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtFour h2 hq 3 x A = s2Hgt₃ h2 hq A := by
  show s2AddEVal₃ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₃ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₃_algebraMap]

/-- ★ **stage-4 dictionary, depth four — genuinely new (μ₄), the row's own cited
target.** -/
theorem s2NPPointHgtFour_four (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtFour h2 hq 4 x A = s2Hgt₄ h2 hq A := by
  show s2AddEVal₄ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₄ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₄_algebraMap]

/-! ## Part D (superset) — the μ₅-refinement point read

Ties the point/evaluation apparatus to the μ₅ REFINEMENT (beyond the tower's four stages,
per R1/R2's own naming-ambiguity note) and, via R2's landed `s2SlotFourMu5_hgt_eq`, to the
landed level-four slot carrier — the superset resolution R1/R2 also took. -/

/-- the μ₅-refinement point read. -/
noncomputable def s2NPPointHgtMu5 (x : S2NPPoint) (A : Polynomial O) : WithTop ℤ :=
  s2AddEVal₅ h2 hq (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A)

/-- the `pointHgt_eval` shape at μ₅. -/
theorem s2NP_pointHgt_evalMu5 : ∀ (x : S2NPPoint) (A : Polynomial O),
    s2NPPointHgtMu5 h2 hq x A
      = s2AddEVal₅ h2 hq (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) :=
  fun _ _ => rfl

/-- ★ the restriction dictionary at μ₅: the point read IS `s2Hgt₅`. -/
theorem s2NPPointHgtMu5_eq (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtMu5 h2 hq x A = s2Hgt₅ h2 hq A := by
  show s2AddEVal₅ h2 hq
      (Polynomial.eval₂ (s2NPCoeffHom (O := O)) (s2NPCoord x) A) = s2Hgt₅ h2 hq A
  rw [s2NP_eval₂_eq_algebraMap, s2AddEVal₅_algebraMap]

/-- ★ ties the point read to R2's landed slot carrier `s2SlotFourMu5`: the point's height
IS the carrier's own `hgt` field, composing this row's dictionary with R2's `hgt`-field
pin (`s2SlotFourMu5_hgt_eq`). -/
theorem s2NPPointHgtMu5_eq_slot (x : S2NPPoint) (A : Polynomial O) :
    s2NPPointHgtMu5 h2 hq x A = (s2SlotFourMu5 h2 hq).hgt A := by
  rw [s2NPPointHgtMu5_eq, s2SlotFourMu5_hgt_eq]

/-! ## Part E — R4: source-backed thresholds at levels 2, 3, 4, no invented numeral

`C130sg.S2LevelOneThreshold` (untouched) already parametrizes level 1's open datum,
`T₁ < 5`.  The three structures below are its EXACT field-shape mirror at levels 2, 3, 4,
with the strict bound `u_{i+1}` threaded from the landed pins named in the module
docstring — never re-derived. -/

/-- **the open source datum at level 2** (mirror of `S2LevelOneThreshold`): the strict
bound `21` is `u₃` — the height of level 2's own key under the landed μ₃ table
(`C132nv1.s2Hgt₃_Φ₂`, `s2LevelTwoThresholdFour_bound_source` below). -/
structure S2LevelTwoThresholdFour where
  /-- the inherited level-2 threshold. -/
  T : ℤ
  /-- its natural avatar. -/
  Tnat : ℕ
  /-- the dictionary between the two. -/
  T_natCast : (Tnat : ℤ) = T
  /-- the necessary bound: below the level-2 key value `u₃ = 21`. -/
  T_lt_key : T < 21

/-- **the open source datum at level 3** (mirror of `S2LevelOneThreshold`): the strict
bound `85` is `u₄` — the height of level 3's own key under the landed μ₄ table
(`C136d0.s2Hgt₄_g8`, `s2LevelThreeThresholdFour_bound_source` below). -/
structure S2LevelThreeThresholdFour where
  /-- the inherited level-3 threshold. -/
  T : ℤ
  /-- its natural avatar. -/
  Tnat : ℕ
  /-- the dictionary between the two. -/
  T_natCast : (Tnat : ℤ) = T
  /-- the necessary bound: below the level-3 key value `u₄ = 85`. -/
  T_lt_key : T < 85

/-- **the open source datum at level 4** (mirror of `S2LevelOneThreshold`): the strict
bound `171` is the μ₅-refinement height — the height of level 4's own key under the
landed μ₅ table (`C136e0.s2Hgt₅_g16`, `s2LevelFourThresholdFour_bound_source` below). -/
structure S2LevelFourThresholdFour where
  /-- the inherited level-4 threshold. -/
  T : ℤ
  /-- its natural avatar. -/
  Tnat : ℕ
  /-- the dictionary between the two. -/
  T_natCast : (Tnat : ℤ) = T
  /-- the necessary bound: below the μ₅-refinement height `171`. -/
  T_lt_key : T < 171

/-! ### disclosure teeth (anonymous, non-consumable, per `S2LevelOneThreshold`'s own
discipline) at the campaign's stated margins `4 < 5`, `20 < 21`, `84 < 85`, `170 < 171`. -/

/-- DISCLOSURE tooth at level 1 (the campaign's stated margin `4 < 5`, on the LANDED
`S2LevelOneThreshold` — not a new type, just a second witness at the near-maximal legal
value). -/
example : S2LevelOneThreshold := ⟨4, 4, by norm_num, by norm_num⟩

/-- DISCLOSURE tooth at level 2 (`20 < 21`). -/
example : S2LevelTwoThresholdFour := ⟨20, 20, by norm_num, by norm_num⟩

/-- DISCLOSURE tooth at level 3 (`84 < 85`). -/
example : S2LevelThreeThresholdFour := ⟨84, 84, by norm_num, by norm_num⟩

/-- DISCLOSURE tooth at level 4 (`170 < 171`). -/
example : S2LevelFourThresholdFour := ⟨170, 170, by norm_num, by norm_num⟩

/-! ### the bound-source pins: the literal numerals are THREADED from the landed height
pins, never re-derived by hand. -/

/-- level-2 bound source: `s2Hgt₃ (keyAt 2) = 21`, i.e. exactly `u₃`. -/
theorem s2LevelTwoThresholdFour_bound_source :
    s2Hgt₃ h2 hq (s2DepthTwoKeyAt h2 hq 2) = ((21 : ℤ) : WithTop ℤ) :=
  s2Hgt₃_Φ₂ h2 hq

/-- level-3 bound source: `s2Hgt₄ (keyAt 3) = 85`, i.e. exactly `u₄`. -/
theorem s2LevelThreeThresholdFour_bound_source :
    s2Hgt₄ h2 hq (g8 h2 hq) = ((85 : ℤ) : WithTop ℤ) :=
  s2Hgt₄_g8 h2 hq

/-- level-4 bound source: `s2Hgt₅ (keyAt 4) = 171`, the μ₅-refinement height. -/
theorem s2LevelFourThresholdFour_bound_source :
    s2Hgt₅ h2 hq (g16 h2 hq) = ((171 : ℤ) : WithTop ℤ) :=
  s2Hgt₅_g16 h2 hq

/-! ## Part F — R4: the strict window, proved once, generically

Exactly `s2SplitNode`'s own `window` proof's strict half (`WithTop.coe_lt_coe.mpr
w.T_lt_key`), extracted as a reusable combinator so a future full split-node assembly (R7)
need not re-derive it at each of the four levels. -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- ★ **the generic strict-window step**: given the threshold's bound and a `pointHgt`
(or any value) that hits the bound EXACTLY at the key, the strict half of `window`
follows immediately. -/
theorem s2StrictWindow_of_key_value {bound T : ℤ} (hT : T < bound) {v : WithTop ℤ}
    (hv : v = ((bound : ℤ) : WithTop ℤ)) : ((T : ℤ) : WithTop ℤ) < v := by
  rw [hv]; exact WithTop.coe_lt_coe.mpr hT

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- the strict window at level 1, instantiated (mirror of `s2SplitNode`'s own `window`
proof). -/
theorem s2LevelOneWindow_strict (w : S2LevelOneThreshold) {v : WithTop ℤ}
    (hv : v = ((5 : ℤ) : WithTop ℤ)) : ((w.T : ℤ) : WithTop ℤ) < v :=
  s2StrictWindow_of_key_value w.T_lt_key hv

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- the strict window at level 2. -/
theorem s2LevelTwoWindow_strict (w : S2LevelTwoThresholdFour) {v : WithTop ℤ}
    (hv : v = ((21 : ℤ) : WithTop ℤ)) : ((w.T : ℤ) : WithTop ℤ) < v :=
  s2StrictWindow_of_key_value w.T_lt_key hv

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- the strict window at level 3. -/
theorem s2LevelThreeWindow_strict (w : S2LevelThreeThresholdFour) {v : WithTop ℤ}
    (hv : v = ((85 : ℤ) : WithTop ℤ)) : ((w.T : ℤ) : WithTop ℤ) < v :=
  s2StrictWindow_of_key_value w.T_lt_key hv

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- the strict window at level 4. -/
theorem s2LevelFourWindow_strict (w : S2LevelFourThresholdFour) {v : WithTop ℤ}
    (hv : v = ((171 : ℤ) : WithTop ℤ)) : ((w.T : ℤ) : WithTop ℤ) < v :=
  s2StrictWindow_of_key_value w.T_lt_key hv

end Uniformity.Density.Tower.C136r2

end

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136r2.s2Hgt₅_eq_top_iff
#print axioms Uniformity.Density.Tower.C136r2.s2ExtendVal_algebraMap
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₃
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₃_algebraMap
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₄
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₄_algebraMap
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₅
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₅_algebraMap
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₅_value_zero
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₅_value_mul
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₅_value_add_ge
#print axioms Uniformity.Density.Tower.C136r2.s2AddEVal₅_value_add_eq
#print axioms Uniformity.Density.Tower.C136r2.s2NPValuationFour
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_one
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_two
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_three
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_four
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_zero
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_mul
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_add_ge
#print axioms Uniformity.Density.Tower.C136r2.s2NPValueOnFour_add_eq
#print axioms Uniformity.Density.Tower.C136r2.s2NP_value_zeroFour
#print axioms Uniformity.Density.Tower.C136r2.s2NP_value_mulFour
#print axioms Uniformity.Density.Tower.C136r2.s2NP_value_add_geFour
#print axioms Uniformity.Density.Tower.C136r2.s2NP_value_add_eqFour
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtFour
#print axioms Uniformity.Density.Tower.C136r2.s2NP_pointHgt_evalFour
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtFour_one
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtFour_two
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtFour_three
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtFour_four
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtMu5
#print axioms Uniformity.Density.Tower.C136r2.s2NP_pointHgt_evalMu5
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtMu5_eq
#print axioms Uniformity.Density.Tower.C136r2.s2NPPointHgtMu5_eq_slot
#print axioms Uniformity.Density.Tower.C136r2.S2LevelTwoThresholdFour
#print axioms Uniformity.Density.Tower.C136r2.S2LevelThreeThresholdFour
#print axioms Uniformity.Density.Tower.C136r2.S2LevelFourThresholdFour
#print axioms Uniformity.Density.Tower.C136r2.s2LevelTwoThresholdFour_bound_source
#print axioms Uniformity.Density.Tower.C136r2.s2LevelThreeThresholdFour_bound_source
#print axioms Uniformity.Density.Tower.C136r2.s2LevelFourThresholdFour_bound_source
#print axioms Uniformity.Density.Tower.C136r2.s2StrictWindow_of_key_value
#print axioms Uniformity.Density.Tower.C136r2.s2LevelOneWindow_strict
#print axioms Uniformity.Density.Tower.C136r2.s2LevelTwoWindow_strict
#print axioms Uniformity.Density.Tower.C136r2.s2LevelThreeWindow_strict
#print axioms Uniformity.Density.Tower.C136r2.s2LevelFourWindow_strict

end AxCheck
