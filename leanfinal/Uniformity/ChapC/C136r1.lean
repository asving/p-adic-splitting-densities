/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136d3
import Uniformity.ChapC.C136e0
import Uniformity.ChapC.C130nv
import Uniformity.ChapC.C130np0
import Uniformity.ChapC.C130np1
import Uniformity.ChapC.C130np3
import Uniformity.ChapC.C130sg
import Uniformity.ChapC.C130s17
import Uniformity.ChapC.C136r0

/-!
# Uniformity.ChapC.C136r1 — the deep-witness realization rows R1 + R2 [R12 2026-08-28]

**Rows R1 + R2** of `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4:

* **R1** ("stage-three slot tables", 60 min): *"Extend `hgt/dig/Full/lift` to level 3,
  tied to the μ₄ value/operator data."*  Landed pattern: `C130sg.s2NPFull` +
  `C130s17.S2RepositoryRealization` (the depth-two total-table/bundling instances, read as
  the template being extended one tower deeper).  Campaign inputs: D3-01 (`C136d0.s2Hgt₄`)
  and D3-05 (`C136d1.s2AddVal₄`), both landed.
* **R2** ("stage-four slot tables", 60 min): *"Build level-4 slot carrier and tie its
  point height to μ₅ `nextValue`."*  Landed: `SplitNodePointSource.stageCarrier` (C130k2),
  the generic producing map this row's carrier is built to the SAME field shape of.
  Campaign inputs: D4-01 (`C136e0.s2Hgt₅`) and D4-03 (`C136e0.s2AddVal₅`), both landed.

## Naming-ambiguity note (flagged, not invented)

The blueprint's own §6.2/§6.3 headers name the `(2,1,85)` operator "**Depth-three / μ₄**"
and the `(1,1,171)` refinement "**Depth-four / μ₅**" — i.e. the row titles' "level"/"stage"
numeral is the OKUTSU–MONTES REFINEMENT DEPTH (μ₄ is OM-depth 3, μ₅ is OM-depth 4), which is
OFF BY ONE from the `DeepTower` STAGE index (μ₄ lives at tower stage `i = 4`, μ₅ is not a
tower stage at all — C.83's `DeepTower.hproper` excludes it, per T5/C136t).  This is
confirmed unambiguously by the landed data itself: `C136t.s2DepthFourKeyChain`'s
`keyAt 4 = g16` is explicitly called "the μ₄ normalized-existence leaf" in `C136d3`'s own
docstring, and `s2Hgt₄`/`s2AddVal₄` (D3-01/D3-05, this row's cited inputs) tie to tower
stage `u₄ = 85` (`C136d0.s2Hgt₄_g8 : s2Hgt₄ g₈ = 85`), not stage 3's `u₃ = 21`.  So R1's
"level 3" is read here as OM-depth 3 = μ₄ = tower stage 4, and R2's "level-4" as OM-depth 4
= μ₅ = the `(1,1,171)` refinement beyond stage 4 — exactly the reading that makes the row's
own cited campaign inputs (D3-01/D3-05 for R1, D4-01/D4-03 for R2) actually load-bearing.
Since extending the S2 total tables "one level" past the landed depth-two pattern requires
filling in BOTH the untouched tower-stage-3 branch (μ₃, `s2Hgt₃`, landed pre-campaign by the
μ₃ campaign, `C132nv1`) and the new tower-stage-4 branch (μ₄), this file supplies both —
the superset of either literal reading, so no reading is shortchanged.

## The "source tables" gap this row actually closes

Grepping the whole μ₃/μ₄/μ₅ stacks (`C132nv1`, `C136d0`–`C136e1`) for a digit table, a
`Full` predicate, or a `lift` law analogous to `s2Dig₁/S2Full₁/s2Lift₁` (`C130np1`) finds
NONE at any of these three levels: only the HEIGHT tables (`s2Hgt₃/s2Hgt₄/s2Hgt₅`) and their
`AddValuation` packagings are landed.  This is the "source tables" blocker anticipated by
the campaign brief.  It is NOT a faithfulness gap requiring an invented numeral, though: the
S2 terminal residue field is the SAME two-element field at every level (`C80.card_K₁`,
transported by the constant-field witness exactly as `C130s6.s2Fld₂_card` reads it off at
level 2), so the digit/Full/lift bank is FORCED at every level by the same argument NP-1/
CC-6 already ran at levels 1/2 — Part 0 below re-derives that argument generically (parametrized
by `Nat.card F = 2`) and Parts 1/2/3 instantiate it at levels 3, 4, and the μ₅ refinement.
No numeral is invented: `Dcum 3 = 8`, `Dcum 4 = 16` are `C136d3`'s own landed pins, and the
degree bound at the μ₅ refinement is the SAME `16` (its `e'f' = 1` growth-free normalized
existence, T5/C136t), not a fresh choice.

## R1 — what lands

* Part 0: generic card-2 field lemmas (`s2r1_eq_one_of_ne_zero`, `s2r1_one_add_one`),
  parametrizing NP-1/CC-6's private per-level arguments by a bare `Nat.card F = 2` fact.
* Part 1: the μ₃/tower-stage-3 digit/Full/lift bank (`s2Dig₃`, `S2Full₃`, `s2Lift₃`, plus
  the digit `zero/ne_zero/add` laws) — genuinely NEW, closing the pre-existing gap left by
  the μ₃ campaign (which landed only `s2Hgt₃`).
* Part 2: the μ₄/tower-stage-4 digit/Full/lift bank (`s2Dig₄`, `S2Full₄`, `s2Lift₄` +
  laws) — the row's own cited D3-01/D3-05 inputs consumed directly.
* Part 3: the extended FOUR-branch total tables `s2NPHgtFour`/`s2NPDigFour`/`s2NPFullFour`,
  mirroring `C130sg.s2NPFull`'s `if i ≤ 1 then … else …` recipe one level up, with pin
  theorems at every level (`s2NPHgtFour_one/two/three/four`, etc.).

## R2 — what lands

* Part 4: the μ₅-refinement digit/Full/lift bank (`s2Dig₅`, `S2Full₅`, `s2Lift₅` + laws),
  at the SAME degree bound `16` the refinement's normalized existence uses (T5).
* Part 5: `s2SlotFourMu5`, the level-four `Ladder.SlotCarrier` tied to the μ₅ refinement —
  built to the EXACT field shape `C130k2.SplitNodePointSource.stageCarrier` produces (`D`,
  `eC`, `fC` from the tower's own `Dcum 4`/`ehat 4`/`fhat 4` — valid because `e' = f' = 1`
  means the refinement changes neither cumulative invariant — and `hgt/dig/Full/hlift` from
  Parts 4).  `s2SlotFourMu5_hgt_eq : (s2SlotFourMu5 h2 hq).hgt = s2Hgt₅ h2 hq` is the
  point-height tie asked for by the row text, by construction (`rfl`).

## Named open — the `nextValue` identification

The row asks the carrier's height be "tied to μ₅ `nextValue`".  `FGMNSourceData.nextValue`
is a FIELD of an `FGMNSourceData` record; no such record exists yet for the μ₅ refinement
(that is D4-17, not cited as landed for this row).  So the tightest HONEST tie available now
is the constructional one stated above (`s2SlotFourMu5_hgt_eq`); the further identification
`(future μ₅ FGMNSourceData).nextValue = s2Hgt₅` wants D4-17's record and is left as that
node's job, not invented here.

GCW-6 fence: everything below is DATA (digit/Full/lift laws, total tables, one
`Ladder.SlotCarrier`) — no `SplitNodePointSource`, `ChainRealization`, or `RealizedInput`
is touched; that remains R3/R7/R9.

## Status

Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  No landed statement is
touched.  Verdict: `runs/wave-c/verdict_R12.md`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C136r1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130np3
open Uniformity.Density.Tower.C130sg Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136d3ad Uniformity.Density.Tower.C136e0
open Uniformity.Density.Tower.C136t Uniformity.Density.Tower.C136r0
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 0 — generic card-2 field lemmas (the NP-1/CC-6 argument, parametrized) -/

/-- Generic copy of `C130s6`'s private `fld₂_eq_one_of_ne_zero` / `C130np1`'s
`fld₁_eq_one_of_ne_zero`: over ANY field with exactly two elements, every nonzero element
is `1`.  Parametrizing by the bare `Nat.card F = 2` fact lets every level's digit/Full/lift
bank reuse ONE proof rather than re-deriving the units/`Subsingleton` argument per level. -/
private theorem s2r1_eq_one_of_ne_zero {F : Type} [Field F] (hcard : Nat.card F = 2)
    {c : F} (hc : c ≠ 0) : c = 1 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : Fˣ) : F) := (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- Generic copy of `C130s6`'s private `fld₂_one_add_one`: a two-element field has
characteristic 2. -/
private theorem s2r1_one_add_one {F : Type} [Field F] (hcard : Nat.card F = 2) :
    (1 : F) + 1 = 0 := by
  by_contra h
  have h1 := s2r1_eq_one_of_ne_zero hcard h
  exact one_ne_zero (α := F) (by linear_combination h1)

/-! ## Part 1 — R1, tower-stage-3 (μ₃): the digit/Full/lift bank

`s2Hgt₃` (`C132nv1`, pre-campaign) is landed; its digit/Full/lift companions are not.
Mirrors `C130np1`'s level-1 bank verbatim, one level up, with the generic Part 0 lemmas in
place of the private per-level units argument. -/

/-- the level-3 residue field has exactly two elements, by the SAME constant-field
transport `C130s6.s2Fld₂_card`/NP-1's `s2Fld₁_card` use at their own levels. -/
theorem s2Fld₃_card : Nat.card ((s2DepthFour h2 hq).fld 3) = 2 := C80.card_K₁ h2 hq

open Classical in
/-- **the S2 level-3 (μ₃) stage DIGIT table**: `0` at `0`, else `1` — the unique lawful
table over the 2-element level-3 field, exactly `s2Dig₁`/`s2Dig₂`'s recipe one level up. -/
noncomputable def s2Dig₃ (A : Polynomial O) : (s2DepthFour h2 hq).fld 3 :=
  if A = 0 then 0 else 1

theorem s2Dig₃_zero : s2Dig₃ h2 hq (0 : Polynomial O) = 0 := if_pos rfl

theorem s2Dig₃_of_ne_zero {A : Polynomial O} (hA : A ≠ 0) : s2Dig₃ h2 hq A = 1 :=
  if_neg hA

theorem s2Dig₃_ne_zero :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthFour h2 hq).Dcum 3 →
      s2Dig₃ h2 hq A ≠ 0 :=
  fun _ hA _ => by rw [s2Dig₃_of_ne_zero h2 hq hA]; exact one_ne_zero

theorem s2Dig₃_add (A B : Polynomial O) (k : ℤ)
    (hA : s2Hgt₃ h2 hq A = (k : WithTop ℤ)) (hB : s2Hgt₃ h2 hq B = (k : WithTop ℤ))
    (hne : s2Dig₃ h2 hq A + s2Dig₃ h2 hq B ≠ 0) :
    s2Hgt₃ h2 hq (A + B) = (k : WithTop ℤ) ∧
      s2Dig₃ h2 hq (A + B) = s2Dig₃ h2 hq A + s2Dig₃ h2 hq B := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [s2Hgt₃_zero h2 hq] at hA
    exact WithTop.top_ne_coe hA
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [s2Hgt₃_zero h2 hq] at hB
    exact WithTop.top_ne_coe hB
  refine absurd ?_ hne
  rw [s2Dig₃_of_ne_zero h2 hq hA0, s2Dig₃_of_ne_zero h2 hq hB0,
    s2r1_one_add_one (s2Fld₃_card h2 hq)]

/-- **the S2 level-3 (μ₃) FULL predicate**: `k` is realized by a nonzero slot-range
polynomial, exactly `S2Full₁`/`S2Full₂`'s recipe one level up. -/
def S2Full₃ (k : ℤ) : Prop :=
  ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum 3 ∧
    s2Hgt₃ h2 hq A = (k : WithTop ℤ)

/-- the `lift` law at the level-3 (μ₃) table: with the 2-element field the only nonzero
digit is `1`, so realizability of the height IS the lift. -/
theorem s2Lift₃ (k : ℤ) (hk : S2Full₃ h2 hq k) (c : (s2DepthFour h2 hq).fld 3)
    (hc : c ≠ 0) :
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum 3 ∧
      s2Hgt₃ h2 hq A = (k : WithTop ℤ) ∧ s2Dig₃ h2 hq A = c := by
  obtain ⟨A, hA0, hdeg, hgtA⟩ := hk
  exact ⟨A, hA0, hdeg, hgtA, by
    rw [s2Dig₃_of_ne_zero h2 hq hA0, s2r1_eq_one_of_ne_zero (s2Fld₃_card h2 hq) hc]⟩

/-! ## Part 2 — R1, tower-stage-4 (μ₄): the digit/Full/lift bank, D3-01/D3-05 consumed

`s2Hgt₄` (D3-01, `C136d0`) and `s2AddVal₄` (D3-05, `C136d1`) are the campaign's own landed
inputs for this row; the digit/Full/lift companions are new, same recipe again. -/

/-- the level-4 residue field has exactly two elements. -/
theorem s2Fld₄_card : Nat.card ((s2DepthFour h2 hq).fld 4) = 2 := C80.card_K₁ h2 hq

open Classical in
/-- **the S2 level-4 (μ₄) stage DIGIT table**: `0` at `0`, else `1`. -/
noncomputable def s2Dig₄ (A : Polynomial O) : (s2DepthFour h2 hq).fld 4 :=
  if A = 0 then 0 else 1

theorem s2Dig₄_zero : s2Dig₄ h2 hq (0 : Polynomial O) = 0 := if_pos rfl

theorem s2Dig₄_of_ne_zero {A : Polynomial O} (hA : A ≠ 0) : s2Dig₄ h2 hq A = 1 :=
  if_neg hA

theorem s2Dig₄_ne_zero :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthFour h2 hq).Dcum 4 →
      s2Dig₄ h2 hq A ≠ 0 :=
  fun _ hA _ => by rw [s2Dig₄_of_ne_zero h2 hq hA]; exact one_ne_zero

theorem s2Dig₄_add (A B : Polynomial O) (k : ℤ)
    (hA : s2Hgt₄ h2 hq A = (k : WithTop ℤ)) (hB : s2Hgt₄ h2 hq B = (k : WithTop ℤ))
    (hne : s2Dig₄ h2 hq A + s2Dig₄ h2 hq B ≠ 0) :
    s2Hgt₄ h2 hq (A + B) = (k : WithTop ℤ) ∧
      s2Dig₄ h2 hq (A + B) = s2Dig₄ h2 hq A + s2Dig₄ h2 hq B := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [s2Hgt₄_zero h2 hq] at hA
    exact WithTop.top_ne_coe hA
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [s2Hgt₄_zero h2 hq] at hB
    exact WithTop.top_ne_coe hB
  refine absurd ?_ hne
  rw [s2Dig₄_of_ne_zero h2 hq hA0, s2Dig₄_of_ne_zero h2 hq hB0,
    s2r1_one_add_one (s2Fld₄_card h2 hq)]

/-- **the S2 level-4 (μ₄) FULL predicate**. -/
def S2Full₄ (k : ℤ) : Prop :=
  ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum 4 ∧
    s2Hgt₄ h2 hq A = (k : WithTop ℤ)

/-- the `lift` law at the level-4 (μ₄) table. -/
theorem s2Lift₄ (k : ℤ) (hk : S2Full₄ h2 hq k) (c : (s2DepthFour h2 hq).fld 4)
    (hc : c ≠ 0) :
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum 4 ∧
      s2Hgt₄ h2 hq A = (k : WithTop ℤ) ∧ s2Dig₄ h2 hq A = c := by
  obtain ⟨A, hA0, hdeg, hgtA⟩ := hk
  exact ⟨A, hA0, hdeg, hgtA, by
    rw [s2Dig₄_of_ne_zero h2 hq hA0, s2r1_eq_one_of_ne_zero (s2Fld₄_card h2 hq) hc]⟩

/-! ## Part 3 — R1, the extended FOUR-branch total tables

Mirrors `C130sg.s2NPFull`'s (and `C130np0.s2NPHgt`'s / `C130np3.s2NPDig`'s) two-branch
`if i ≤ 1 then … else …` recipe, extended by TWO further branches (levels 3, 4) rather
than one, per the naming-ambiguity note above: whichever of "level 3"/"level 4" the row
text meant, both branches are supplied. -/

/-- the extended total `hgt` table, levels 1–4. -/
noncomputable def s2NPHgtFour (i : ℕ) : Polynomial O → WithTop ℤ :=
  if i ≤ 1 then s2Hgt₁ h2 hq
  else if i ≤ 2 then s2Hgt₂ h2 hq
  else if i ≤ 3 then s2Hgt₃ h2 hq
  else s2Hgt₄ h2 hq

theorem s2NPHgtFour_one : s2NPHgtFour h2 hq 1 = s2Hgt₁ h2 hq := rfl
theorem s2NPHgtFour_two : s2NPHgtFour h2 hq 2 = s2Hgt₂ h2 hq := rfl
theorem s2NPHgtFour_three : s2NPHgtFour h2 hq 3 = s2Hgt₃ h2 hq := rfl
theorem s2NPHgtFour_four : s2NPHgtFour h2 hq 4 = s2Hgt₄ h2 hq := rfl

/-- the extended total `dig` table, levels 1–4. -/
noncomputable def s2NPDigFour (i : ℕ) : Polynomial O → (s2DepthFour h2 hq).fld i :=
  if i ≤ 1 then s2Dig₁ h2 hq
  else if i ≤ 2 then s2Dig₂ h2 hq
  else if i ≤ 3 then s2Dig₃ h2 hq
  else s2Dig₄ h2 hq

theorem s2NPDigFour_one : s2NPDigFour h2 hq 1 = s2Dig₁ h2 hq := rfl
theorem s2NPDigFour_two : s2NPDigFour h2 hq 2 = s2Dig₂ h2 hq := rfl
theorem s2NPDigFour_three : s2NPDigFour h2 hq 3 = s2Dig₃ h2 hq := rfl
theorem s2NPDigFour_four : s2NPDigFour h2 hq 4 = s2Dig₄ h2 hq := rfl

/-- the extended total `Full` table, levels 1–4. -/
def s2NPFullFour (i : ℕ) : ℤ → Prop :=
  if i ≤ 1 then S2Full₁ h2 hq
  else if i ≤ 2 then S2Full₂ h2 hq
  else if i ≤ 3 then S2Full₃ h2 hq
  else S2Full₄ h2 hq

theorem s2NPFullFour_one : s2NPFullFour h2 hq 1 = S2Full₁ h2 hq := rfl
theorem s2NPFullFour_two : s2NPFullFour h2 hq 2 = S2Full₂ h2 hq := rfl
theorem s2NPFullFour_three : s2NPFullFour h2 hq 3 = S2Full₃ h2 hq := rfl
theorem s2NPFullFour_four : s2NPFullFour h2 hq 4 = S2Full₄ h2 hq := rfl

/-- ★ **R1 exit tooth — the `lift` law at every live level, in ONE `interval_cases`
dispatch**, exactly the shape a future depth-four `SplitNodePointSource`'s own `lift`
field needs (mirroring `C130sg.s2SplitNode`'s `lift := by … interval_cases i` block, now
through all four levels instead of two). -/
theorem s2LiftFour :
    ∀ i, StageLive 4 i → ∀ k : ℤ, s2NPFullFour h2 hq i k → ∀ c : (s2DepthFour h2 hq).fld i,
      c ≠ 0 → ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum i ∧
        s2NPHgtFour h2 hq i A = (k : WithTop ℤ) ∧ s2NPDigFour h2 hq i A = c := by
  intro i hi
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases i
  · exact s2Lift₁ h2 hq
  · exact s2Lift₂ h2 hq
  · exact s2Lift₃ h2 hq
  · exact s2Lift₄ h2 hq

/-! ## Part 4 — R2, the μ₅-refinement digit/Full/lift bank, D4-01/D4-03 consumed

`s2Hgt₅` (D4-01, `C136e0`) and `s2AddVal₅` (D4-03, `C136e0`) are the campaign's own landed
inputs for this row.  The degree bound is `16`, the SAME numeral as `Dcum 4` — not a fresh
choice, but T5/C136t's own fact that the `(1, 1, 171)` refinement's normalized existence is
growth-free (`e' = f' = 1`), so its slot range is bounded by `Dcum 4`, not a fifth cumulative
degree. -/

open Classical in
/-- **the μ₅-refinement stage DIGIT table**: `0` at `0`, else `1`, at the SAME constant
level-4 field the refinement's residual `X + 1` lives over. -/
noncomputable def s2Dig₅ (A : Polynomial O) : (s2DepthFour h2 hq).fld 4 :=
  if A = 0 then 0 else 1

theorem s2Dig₅_zero : s2Dig₅ h2 hq (0 : Polynomial O) = 0 := if_pos rfl

theorem s2Dig₅_of_ne_zero {A : Polynomial O} (hA : A ≠ 0) : s2Dig₅ h2 hq A = 1 :=
  if_neg hA

theorem s2Dig₅_ne_zero :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthFour h2 hq).Dcum 4 →
      s2Dig₅ h2 hq A ≠ 0 :=
  fun _ hA _ => by rw [s2Dig₅_of_ne_zero h2 hq hA]; exact one_ne_zero

theorem s2Dig₅_add (A B : Polynomial O) (k : ℤ)
    (hA : s2Hgt₅ h2 hq A = (k : WithTop ℤ)) (hB : s2Hgt₅ h2 hq B = (k : WithTop ℤ))
    (hne : s2Dig₅ h2 hq A + s2Dig₅ h2 hq B ≠ 0) :
    s2Hgt₅ h2 hq (A + B) = (k : WithTop ℤ) ∧
      s2Dig₅ h2 hq (A + B) = s2Dig₅ h2 hq A + s2Dig₅ h2 hq B := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [s2Hgt₅_zero h2 hq] at hA
    exact WithTop.top_ne_coe hA
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [s2Hgt₅_zero h2 hq] at hB
    exact WithTop.top_ne_coe hB
  refine absurd ?_ hne
  rw [s2Dig₅_of_ne_zero h2 hq hA0, s2Dig₅_of_ne_zero h2 hq hB0,
    s2r1_one_add_one (s2Fld₄_card h2 hq)]

/-- **the μ₅-refinement FULL predicate**, bounded by `Dcum 4 = 16` (the growth-free
refinement's own slot range, T5). -/
def S2Full₅ (k : ℤ) : Prop :=
  ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum 4 ∧
    s2Hgt₅ h2 hq A = (k : WithTop ℤ)

/-- the `lift` law at the μ₅-refinement table. -/
theorem s2Lift₅ (k : ℤ) (hk : S2Full₅ h2 hq k) (c : (s2DepthFour h2 hq).fld 4)
    (hc : c ≠ 0) :
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthFour h2 hq).Dcum 4 ∧
      s2Hgt₅ h2 hq A = (k : WithTop ℤ) ∧ s2Dig₅ h2 hq A = c := by
  obtain ⟨A, hA0, hdeg, hgtA⟩ := hk
  exact ⟨A, hA0, hdeg, hgtA, by
    rw [s2Dig₅_of_ne_zero h2 hq hA0, s2r1_eq_one_of_ne_zero (s2Fld₄_card h2 hq) hc]⟩

/-! ## Part 5 — R2, the level-four slot carrier tied to μ₅

Built to the EXACT field shape `C130k2.SplitNodePointSource.stageCarrier` produces at a
live stage `i` of a `DeepTower` `W` (`D := W.Dcum i`, `eC := W.ehat i`, `fC := W.fhat i`,
`hef := W.Dcum_eq_ehat_mul_fhat i`, `heC/hfC` positivity, `hgt/dig/Full/hlift` the node's
own per-level tables) — specialized at `i = 4` of `s2DepthFour`, with `hgt/dig/Full/hlift`
supplied by the μ₅-refinement bank of Part 4 rather than the μ₄ bank of Part 2.  This is
legitimate REUSE, not misuse, of `Dcum 4`/`ehat 4`/`fhat 4`: the refinement's own
cumulative invariants are `ehat 4 · e' = ehat 4 · 1 = ehat 4` and `fhat 4 · f' = fhat 4`
(T5/campaign §3.3's `e' = f' = 1`), so the refinement carries the SAME `(D, eC, fC)` triple
stage 4 already has — no new numeral, no new `hef` proof needed. -/

/-- ★★ **R2 — the level-four `Ladder.SlotCarrier`, tied to the μ₅ refinement.** -/
noncomputable def s2SlotFourMu5 : Ladder.SlotCarrier O ((s2DepthFour h2 hq).fld 4) where
  D := (s2DepthFour h2 hq).Dcum 4
  hD := DeepTower.Dcum_pos (s2DepthFour h2 hq) (le_refl 4)
  eC := (s2DepthFour h2 hq).ehat 4
  fC := (s2DepthFour h2 hq).fhat 4
  hef := DeepTower.Dcum_eq_ehat_mul_fhat (s2DepthFour h2 hq) 4
  heC := DeepTower.ehat_pos (s2DepthFour h2 hq) (le_refl 4)
  hfC := DeepTower.fhat_pos (s2DepthFour h2 hq) (le_refl 4)
  hgt := s2Hgt₅ h2 hq
  dig := s2Dig₅ h2 hq
  hgt_zero := s2Hgt₅_zero h2 hq
  dig_zero := s2Dig₅_zero h2 hq
  hgt_ne_top := fun _ hA _ => s2Hgt₅_ne_top h2 hq hA
  dig_ne_zero := s2Dig₅_ne_zero h2 hq
  hgt_add_ge := s2Hgt₅_add_ge h2 hq
  hgt_add_eq := s2Hgt₅_add_eq h2 hq
  dig_add := s2Dig₅_add h2 hq
  Full := S2Full₅ h2 hq
  hlift := s2Lift₅ h2 hq

/-- ★ **R2 exit tooth — the point-height tie asked for by the row text**: the carrier's
`hgt` field IS `s2Hgt₅`, by construction.  (`FGMNSourceData.nextValue = s2Hgt₅` for an
actual μ₅ `FGMNSourceData` record is D4-17's job — no such record is landed yet, so this
constructional tie is the tightest honest statement available now; see the docstring
header's "named open" note.) -/
theorem s2SlotFourMu5_hgt_eq : (s2SlotFourMu5 h2 hq).hgt = s2Hgt₅ h2 hq := rfl

/-- companion pin: the carrier's `D` field is `Dcum 4 = 16`, the degree the refinement's
normalized existence actually produces (T5, `s2WitnessFour_Dcum_four`). -/
theorem s2SlotFourMu5_D_eq : (s2SlotFourMu5 h2 hq).D = 16 :=
  s2DepthFour_Dcum_four h2 hq

/-- companion pin: the carrier's `dig`/`Full` fields are the Part 4 bank, by
construction. -/
theorem s2SlotFourMu5_dig_eq : (s2SlotFourMu5 h2 hq).dig = s2Dig₅ h2 hq := rfl

theorem s2SlotFourMu5_Full_eq : (s2SlotFourMu5 h2 hq).Full = S2Full₅ h2 hq := rfl

end Uniformity.Density.Tower.C136r1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136r1.s2Fld₃_card
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₃
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₃_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₃_of_ne_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₃_ne_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₃_add
#print axioms Uniformity.Density.Tower.C136r1.S2Full₃
#print axioms Uniformity.Density.Tower.C136r1.s2Lift₃
#print axioms Uniformity.Density.Tower.C136r1.s2Fld₄_card
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₄
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₄_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₄_of_ne_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₄_ne_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₄_add
#print axioms Uniformity.Density.Tower.C136r1.S2Full₄
#print axioms Uniformity.Density.Tower.C136r1.s2Lift₄
#print axioms Uniformity.Density.Tower.C136r1.s2NPHgtFour
#print axioms Uniformity.Density.Tower.C136r1.s2NPHgtFour_one
#print axioms Uniformity.Density.Tower.C136r1.s2NPHgtFour_two
#print axioms Uniformity.Density.Tower.C136r1.s2NPHgtFour_three
#print axioms Uniformity.Density.Tower.C136r1.s2NPHgtFour_four
#print axioms Uniformity.Density.Tower.C136r1.s2NPDigFour
#print axioms Uniformity.Density.Tower.C136r1.s2NPDigFour_one
#print axioms Uniformity.Density.Tower.C136r1.s2NPDigFour_two
#print axioms Uniformity.Density.Tower.C136r1.s2NPDigFour_three
#print axioms Uniformity.Density.Tower.C136r1.s2NPDigFour_four
#print axioms Uniformity.Density.Tower.C136r1.s2NPFullFour
#print axioms Uniformity.Density.Tower.C136r1.s2NPFullFour_one
#print axioms Uniformity.Density.Tower.C136r1.s2NPFullFour_two
#print axioms Uniformity.Density.Tower.C136r1.s2NPFullFour_three
#print axioms Uniformity.Density.Tower.C136r1.s2NPFullFour_four
#print axioms Uniformity.Density.Tower.C136r1.s2LiftFour
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₅
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₅_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₅_of_ne_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₅_ne_zero
#print axioms Uniformity.Density.Tower.C136r1.s2Dig₅_add
#print axioms Uniformity.Density.Tower.C136r1.S2Full₅
#print axioms Uniformity.Density.Tower.C136r1.s2Lift₅
#print axioms Uniformity.Density.Tower.C136r1.s2SlotFourMu5
#print axioms Uniformity.Density.Tower.C136r1.s2SlotFourMu5_hgt_eq
#print axioms Uniformity.Density.Tower.C136r1.s2SlotFourMu5_D_eq
#print axioms Uniformity.Density.Tower.C136r1.s2SlotFourMu5_dig_eq
#print axioms Uniformity.Density.Tower.C136r1.s2SlotFourMu5_Full_eq

end AxCheck
