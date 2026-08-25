/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130fd0
import Uniformity.ChapC.C130np3
import Uniformity.ChapC.C130np5
import Uniformity.ChapC.C130np7
import Uniformity.ChapC.C130np8
import Uniformity.ChapC.C130s18

/-!
# Uniformity.ChapC.C130sg — S2-source plan nodes SG-0 + SG-1 — the corrected frontier and
the funnel fire

**S2-source plan nodes SG-0 + SG-1** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 rows
SG-0 "Construct the corrected S2 frontier; exact level-two table ties and core-only/
cite-audited footprint" and SG-1 "Re-run `toChainRealization → calculusNonempty →
s2RealizedInput →` both socket applications"), the FINAL nodes of the plan.

## SG-0 — what lands

* ★★ `s2SplitNode` — the FIRST `SplitNodePointSource` instance at the S2 repository pair:
  every field is a NAMED landed piece (NP-0's points/evaluation/valuation, NP-0+NV/CC-6's
  stage value tables, NP-1/NP-3's digit tables and point digit reads, NP-1/CC-6's Full/lift,
  NP-4/NP-5's level-2 seam threshold and window, NP-6's letters/ψ-root, NP-7's canonical
  read, NP-8's arena/tower-read/peel data), assembled with `interval_cases` stage fencing —
  the "stage-law `i`-fencing" NP-0 deferred to this node.  Evaluation ambient
  `E := FractionRing (Polynomial O)` (the SF-4 probe, NP-0's carrier); residue ambient `L`
  arbitrary over the terminal field.
* ★★ `s2Frontier` — the corrected `S2SourceFrontier` instance (the structure's `fgmn` legs
  re-typed at the `r = 1` anchoring by this unit's sanctioned SG-0 edit of `C130s17`):
  node = `s2SplitNode`, level-two table ties `hgt_two`/`dig_two`/`full_two` all `rfl`
  (re-exposed as `s2Frontier_levelTwo_ties`), `fgmn := s2SourceDataOne`,
  `fgmnLaws := s2SourceLawsOne` (FD-0's records, all thirteen laws discharged), compat
  fields = FD-1's proofs.
* **The ONE open source datum, honestly parametrized**: `S2LevelOneThreshold` — the level-1
  inherited threshold `T₁`.  NP-4 found NO source occurrence naming it (level 1 is the base
  `KeyFrame`; no prior `LevelDatum`); NP-5 proved any candidate must satisfy `T₁ < 5` and
  refuted both landed avatars (`5 ≮ 5`, `10 ≮ 5`).  The frontier's field list DOES demand it
  (`window` quantifies over `StageLive 2 i ⊇ {1}`; `thresholdZ`/`threshold_nonneg` read
  index 1), so `s2Frontier` is CONDITIONAL on exactly this datum.  Necessity is proved
  (`S2LevelOneThreshold.ofSplitNode`: EVERY split node at the repository pair carries one),
  so the parametrization is exact — no wider, no narrower.  DISCLOSURE: the structure is
  Lean-nonempty (any `T₁ ≤ 4` works — the anonymous tooth below); its openness is a
  FAITHFULNESS gap (WHICH numeral EFF.T2.04's inherited threshold is at level 1), not an
  emptiness, and the campaign's no-invented-numeral rule is why no named instance is landed.

## SG-1 — the funnel, fired at the SG-0 frontier

`s2FrontierChainRealization → s2Frontier_calculusNonempty → s2FrontierRealizedInput →`
BOTH socket applications (`s2Frontier_ladder_socket`, `s2Frontier_deepTwist_socket`), each
conditional on exactly:

1. `w : S2LevelOneThreshold` — the open level-1 threshold source datum (above);
2. `ev : LegacyEvaluation` — the U13-refuted single-ambient evaluation half, PROVABLY EMPTY
   at the SG-0 frontier (★ `s2Frontier_legacyEvaluation_isEmpty` below — the U13
   contradiction now machine-transplants against the concrete node: `pointHgt 2 x (C 2) = 4`
   vs the forced `⊤`);
3. `lf : LegacyFGMN` — the FD-0-refuted depth-two FGMN half (this unit's `C130s17`
   quarantine), PROVABLY EMPTY at the landed operator readings
   (★ `s2LegacyFGMN_landed_empty`, transplanting FD-0's unsatisfiability); inhabitable, if
   at all, only by plan §5.2's genuinely-μ₃-level operators (nowhere landed).

So the funnel statements are TRUE and fire end-to-end, but remain PACKAGING SHAPES: their
`ev` leg is empty at S2 outright, hence no non-vacuous S2 socket conclusion is claimed —
exactly CC-17/CC-18's recorded conditionality, now with the vacuity CONCENTRATED in two
named, separately-refuted premises while the frontier itself (the S2 content) is inhabited
modulo the one named threshold datum.  Removing `ev`/`lf` is the plan's SF-3 consumer
ripple (re-type `NodePointSource`/`ChainRealization` themselves), not this node.

## Anti-drift pins

`s2FgmnAnchor`/`s2FgmnAnchorKeys` (the SG-0 duplicates in `C130s17`, forced by the import
direction) are `rfl`-pinned to C130fd0's `s2DepthOne`/`s2DepthOneKeyChain`
(`s2FgmnAnchor_eq_depthOne`, `s2FgmnAnchorKeys_eq_depthOne`); the frontier's record reads
are `rfl`-pinned to the NP/FD names (`s2Frontier_fgmn`, `s2Frontier_node_pointHgt`, the
threshold pins).

## Honesty scope

* `S2LevelOneThreshold` is the named STOP-turned-parameter: no source numeral is chosen.
* Nothing here discharges the sockets' ϑ-conjunct or the OM-8 L3 goal (CC-18's
  non-swallowing audit is untouched); no leanspec socket is re-signed.
* `s2LegacyFGMN_landed_empty` is CONDITIONAL on the landed operator readings
  (`normalizedResidual = s2NormRes`, `keyPolynomial = S2KeyPoly`), exactly as FD-0's
  unsatisfiability theorem is; a genuinely-μ₃-level depth-two record is NOT refuted.
* Cite ledger: **empty** — every declaration below rests on Lean/mathlib + the Lean-core
  NP/RP/KP/FD chain; `#print axioms` footer is the audit.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`S2LevelOneThreshold` (the parametrization of the open datum), `s2SplitNode`/`s2Frontier`
(the instance statements), `s2Frontier_legacyEvaluation_isEmpty`,
`s2LegacyFGMN_landed_empty`, and `S2LevelOneThreshold.ofSplitNode`.

**DEPENDS.** C130s17 (the SG-0-retyped frontier + funnel, `s2FgmnAnchor`) · C130s18 (the
socket applications) · C130fd0 (`s2SourceDataOne`/`s2SourceLawsOne`,
`s2SourceLaws_depthTwo_unsatisfiable`, `s2DepthOne`) · C130np0/np1/np3/np4/np5/np6/np7/np8
(the node pieces, as named above) · C130s2/C130s6/C130nv (the S2 cores) · C80/C09/C10/C44
(`s2Tower`, `LevelDatum.seam`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`; the only edits outside
this file are the sanctioned SG-0/SG-1 re-types in `C130s17.lean`/`C130s18.lean`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C130sg

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130nv
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C130fd0
open Uniformity.Density.Tower.C130np0 Uniformity.Density.Tower.C130np1
open Uniformity.Density.Tower.C130np3 Uniformity.Density.Tower.C130np4
open Uniformity.Density.Tower.C130np5 Uniformity.Density.Tower.C130np6
open Uniformity.Density.Tower.C130np7 Uniformity.Density.Tower.C130np8
open Uniformity.Density.Tower.C130kp0 Uniformity.Density.Tower.C130rp8

universe uE uG uL

/-! ## Part 0 — the one open source datum (the honest STOP, as a parameter)

The `SplitNodePointSource` field list demands a level-1 inherited threshold (`thresholdZ 1`
with its `ℕ`-avatar, and the strict half of `window` at `i = 1`).  NP-4 found no source
occurrence naming it; NP-5 proved the necessary bound `T₁ < 5` and refuted both landed
avatars.  Per the plan's no-invented-numeral rule the datum is PARAMETRIZED, not chosen. -/

/-- **The ONE open source datum of the S2 frontier** (NP-4/NP-5): the level-1 inherited
threshold, with its natural avatar (`threshold_nonneg`'s demand) and NP-5's necessary strict
bound `T < 5` (= `d(Φ₁(ρ)) = u₂`, NP-0's `key_value`).  DISCLOSURE: this structure is
Lean-nonempty (see the anonymous tooth below) — its openness is WHICH numeral the source's
inherited `T₁` (EFF.T2.04's `[hypothesis]`) is, a faithfulness question no Lean term
decides; the campaign therefore lands NO named instance. -/
structure S2LevelOneThreshold where
  /-- the inherited level-1 threshold (EFF.T2.04's `T ∈ 𝐙`, no source formula known). -/
  T : ℤ
  /-- the natural avatar demanded by `threshold_nonneg` (E.11's natural-valued `T`). -/
  Tnat : ℕ
  /-- the dictionary between the two. -/
  T_natCast : (Tnat : ℤ) = T
  /-- NP-5's necessary bound: below the level-1 key value `u₂ = 5`. -/
  T_lt_key : T < 5

/-- DISCLOSURE tooth (deliberately anonymous — NOT source-backed, NOT for consumption): the
open datum is Lean-inhabitable, so the `s2Frontier` conditionality below is a faithfulness
gap, not an emptiness.  Any consumer firing the funnel through a bare numeral here would
violate the campaign's no-invented-numeral rule; that is why this term has no name. -/
example : S2LevelOneThreshold := ⟨0, 0, rfl, by norm_num⟩

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — anti-drift pins for the SG-0 duplicates in C130s17 -/

/-- anti-drift pin: C130s17's SG-0 anchor tower IS C130fd0's `s2DepthOne`,
definitionally. -/
theorem s2FgmnAnchor_eq_depthOne : s2FgmnAnchor h2 hq = s2DepthOne h2 hq := rfl

/-- anti-drift pin: C130s17's SG-0 anchor chain IS C130fd0's `s2DepthOneKeyChain`,
definitionally. -/
theorem s2FgmnAnchorKeys_eq_depthOne :
    s2FgmnAnchorKeys h2 hq = s2DepthOneKeyChain h2 hq := rfl

/-! ## Part 2 — the total stage tables the node still needed (Full, thresholds)

NP-0/NP-3 landed the total `hgt`/`dig` tables (`s2NPHgt`/`s2NPDig`); the `Full` predicate
and the threshold pair get the same `i ≤ 1` branching here. -/

/-- the total `Full` table: NP-1's `S2Full₁` at `i ≤ 1`, CC-6's `S2Full₂` at `i ≥ 2` (so the
frontier tie `full_two` is `rfl`). -/
def s2NPFull (i : ℕ) : ℤ → Prop :=
  if i ≤ 1 then S2Full₁ h2 hq else S2Full₂ h2 hq

/-- pin: level one of the table is NP-1's `S2Full₁`. -/
theorem s2NPFull_one : s2NPFull h2 hq 1 = S2Full₁ h2 hq := rfl

/-- pin: level two of the table is CC-6's `S2Full₂`. -/
theorem s2NPFull_two : s2NPFull h2 hq 2 = S2Full₂ h2 hq := rfl

/-- the total integer threshold table: the OPEN level-1 datum at `i ≤ 1`, NP-4's
source-pinned seam `T₂ = d_r·u` (`EFF.HE6R1.18`, `LevelDatum.seam`) at `i ≥ 2` — the
level-2 value is the source FORMULA, not a numeral (its numeral `5` is NP-4's theorem). -/
def s2NPThresholdZ (w : S2LevelOneThreshold) (i : ℕ) : ℤ :=
  if i ≤ 1 then w.T else (((s2Tower h2 hq).levelDatum h2).seam : ℤ)

/-- the total natural-avatar threshold table. -/
def s2NPThresholdNat (w : S2LevelOneThreshold) (i : ℕ) : ℕ :=
  if i ≤ 1 then w.Tnat else ((s2Tower h2 hq).levelDatum h2).seam

/-- pin: the level-1 threshold is the open datum, definitionally. -/
theorem s2NPThresholdZ_one (w : S2LevelOneThreshold) :
    s2NPThresholdZ h2 hq w 1 = w.T := rfl

/-- pin: the level-2 threshold is the seam formula, definitionally. -/
theorem s2NPThresholdZ_two_eq_seam (w : S2LevelOneThreshold) :
    s2NPThresholdZ h2 hq w 2 = (((s2Tower h2 hq).levelDatum h2).seam : ℤ) := rfl

/-- numeral: the level-2 threshold is `5` (NP-4's `seam_s2Tower`). -/
theorem s2NPThresholdZ_two (w : S2LevelOneThreshold) :
    s2NPThresholdZ h2 hq w 2 = 5 :=
  seam_s2Tower_intCast h2 hq

/-! ## Part 3 — ★★ SG-0: the split node, assembled from NP-0..NP-8 -/

/-- ★★ **SG-0, the S2 `SplitNodePointSource` instance** — the first inhabitant of the split
node at the repository receiver/keys, conditional on exactly the one open source datum `w`
(the level-1 threshold).  Every field value and law is a NAMED landed NP/NV/CC piece; the
only new proofs are the `interval_cases` stage fencings of the per-level banks (the assembly
NP-0 deferred to SG-0) and the level-1 window strict half from `w.T_lt_key` + NP-0's
`key_value` computation. -/
def s2SplitNode (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] (w : S2LevelOneThreshold) :
    SplitNodePointSource (L := L) (S2DepthTwo h2 hq) (FractionRing (Polynomial O))
      (s2RepositoryRealization h2 hq).receiver (s2RepositoryRealization h2 hq).keys where
  Point := S2NPPoint
  Pt := s2NPPt h2 hq
  point_exists := s2NP_point_exists h2 hq
  coeffHom := s2NPCoeffHom
  coord := s2NPCoord
  valueOn := s2NPValueOn h2 hq
  value_zero := s2NP_value_zero h2 hq
  value_mul := s2NP_value_mul h2 hq
  value_add_ge := s2NP_value_add_ge h2 hq
  value_add_eq := s2NP_value_add_eq h2 hq
  hgt := s2NPHgt h2 hq
  dig := s2NPDig h2 hq
  pointHgt := s2NPPointHgt h2 hq
  pointDig := s2NPPointDig h2 hq
  pointHgt_eval := s2NP_pointHgt_eval h2 hq
  slot_value := s2NP_slot_value h2 hq
  slot_digit := s2NP_slot_digit h2 hq
  hgt_zero := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_zero h2 hq
    · exact s2Hgt₂_zero h2 hq
  dig_zero := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Dig₁_zero h2 hq
    · exact s2Dig₂_zero h2 hq
  hgt_ne_top := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_ne_top_slot h2 hq
    · exact s2Hgt₂_ne_top_slot h2 hq
  dig_ne_zero := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Dig₁_ne_zero h2 hq
    · exact s2Dig₂_ne_zero h2 hq
  hgt_add_ge := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_add_ge h2 hq
    · exact s2Hgt₂_add_ge h2 hq
  hgt_add_eq := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Hgt₁_add_eq h2 hq
    · exact s2Hgt₂_add_eq h2 hq
  dig_add := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Dig₁_add h2 hq
    · exact s2Dig₂_add h2 hq
  Full := s2NPFull h2 hq
  lift := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact s2Lift₁ h2 hq
    · exact s2Lift₂ h2 hq
  thresholdZ := s2NPThresholdZ h2 hq w
  thresholdNat := s2NPThresholdNat h2 hq w
  threshold_nonneg := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · exact w.T_natCast
    · rfl
  window := by
    intro i hi x hx
    obtain ⟨hlo, hhi⟩ := hi
    interval_cases i
    · refine ⟨?_, s2NP_window_ne_top h2 hq 1 (by decide) x hx⟩
      show ((w.T : ℤ) : WithTop ℤ) <
        s2NPPointHgt h2 hq 1 x ((s2RepositoryRealization h2 hq).keys.keyAt 1)
      rw [s2NPPointHgt_keyAt_one h2 hq x,
        show (s2DepthTwo h2 hq).u 2 = 5 from (s2DepthTwo_stage2 h2 hq).2.2,
        show ((5 : ℕ) : WithTop ℤ) = ((5 : ℤ) : WithTop ℤ) by norm_num]
      exact WithTop.coe_lt_coe.mpr w.T_lt_key
    · exact s2_window_at_two h2 hq x hx
  ambientLetter := s2AmbientLetter L
  key_value := s2NP_key_value h2 hq
  psi_root := s2_psi_root L (s2RepositoryRealization h2 hq).receiver
  canonicalRead := s2CanonicalRead h2 hq L
  arenaRead := s2ArenaRead h2 hq
  towerRead := s2TowerRead h2 hq
  peelUnit := s2PeelUnit h2 hq

/-! ## Part 4 — ★★ SG-0: the corrected frontier instance -/

/-- ★★ **SG-0, the corrected S2 source frontier** — the first `S2SourceFrontier`
inhabitant, at the SG-0-retyped (`r = 1`-anchored) FGMN legs, conditional on exactly the
one open source datum `w`: node = `s2SplitNode`, all three level-two table ties `rfl`,
`fgmn`/`fgmnLaws` = FD-0's `s2SourceDataOne`/`s2SourceLawsOne` (all thirteen laws
discharged by named landed theorems), compat fields = FD-1's proofs. -/
def s2Frontier (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] (w : S2LevelOneThreshold) :
    S2SourceFrontier h2 hq (FractionRing (Polynomial O)) L where
  node := s2SplitNode h2 hq L w
  hgt_two := rfl
  dig_two := rfl
  full_two := rfl
  fgmn := s2SourceDataOne h2 hq
  fgmnLaws := s2SourceLawsOne h2 hq
  grade_compat := fun x _ g => (s2NPPointHgt_two h2 hq x g).symm
  letter_compat := by
    intro i _
    show algebraMap ((S2DepthTwo h2 hq).fld 2) L
        ((s2RepositoryRealization h2 hq).receiver.topEquiv 1) = (s2AmbientLetter L i : L)
    rw [map_one, map_one, s2AmbientLetter_coe]

variable (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- The type-level pair the SF-4 tooth anticipated, now INHABITED: the probe evaluation
ambient with the residue side at the terminal field itself. -/
example (w : S2LevelOneThreshold) :
    S2SourceFrontier h2 hq (FractionRing (Polynomial O)) ((S2DepthTwo h2 hq).fld 2) :=
  s2Frontier h2 hq _ w

/-- read pin: the frontier's node point read is NP-0's `s2NPPointHgt`, definitionally. -/
theorem s2Frontier_node_pointHgt (w : S2LevelOneThreshold) :
    (s2Frontier h2 hq L w).node.pointHgt = s2NPPointHgt h2 hq := rfl

/-- read pin: the frontier's FGMN legs are FD-0's `r = 1` records, definitionally. -/
theorem s2Frontier_fgmn (w : S2LevelOneThreshold) :
    (s2Frontier h2 hq L w).fgmn = s2SourceDataOne h2 hq := rfl

/-- read pin: the level-1 threshold is the open datum, definitionally. -/
theorem s2Frontier_thresholdZ_one (w : S2LevelOneThreshold) :
    (s2Frontier h2 hq L w).node.thresholdZ 1 = w.T := rfl

/-- numeral pin: the level-2 threshold is NP-4's seam value `5`. -/
theorem s2Frontier_thresholdZ_two (w : S2LevelOneThreshold) :
    (s2Frontier h2 hq L w).node.thresholdZ 2 = 5 :=
  seam_s2Tower_intCast h2 hq

/-- ★ **the exact level-two table ties** (plan row SG-0's charge), re-exposed as one named
statement: the frontier's stage tables at the terminal level ARE CC-6's landed tables —
all three by `rfl` (the ties are definitional, not merely provable). -/
theorem s2Frontier_levelTwo_ties (w : S2LevelOneThreshold) :
    (s2Frontier h2 hq L w).node.hgt 2 = s2Hgt₂ h2 hq ∧
      (s2Frontier h2 hq L w).node.dig 2 = s2Dig₂ h2 hq ∧
      (s2Frontier h2 hq L w).node.Full 2 = S2Full₂ h2 hq :=
  ⟨(s2Frontier h2 hq L w).hgt_two, (s2Frontier h2 hq L w).dig_two,
    (s2Frontier h2 hq L w).full_two⟩

/-! ## Part 5 — the conditionality is EXACT: necessity of the open datum -/

/-- **Necessity of the open datum** (the converse of `s2Frontier`'s parametrization): EVERY
`SplitNodePointSource` at the S2 repository pair carries an `S2LevelOneThreshold` — its own
level-1 threshold satisfies the bound, by `key_value` (the level-1 key value is `u₂ = 5`)
and the strict window half.  So `s2Frontier`'s parameter is exactly the open content: the
frontier is inhabited IFF the level-1 threshold datum is supplied. -/
def S2LevelOneThreshold.ofSplitNode {E : Type uE} [Field E]
    (S : SplitNodePointSource (L := L) (S2DepthTwo h2 hq) E
      (s2RepositoryRealization h2 hq).receiver (s2RepositoryRealization h2 hq).keys) :
    S2LevelOneThreshold where
  T := S.thresholdZ 1
  Tnat := S.thresholdNat 1
  T_natCast := S.threshold_nonneg 1 (by decide)
  T_lt_key := by
    obtain ⟨x, hx⟩ := (S.point_exists 1 (by decide)).some
    have hwin := (S.window 1 (by decide) x hx).1
    rw [S.key_value 1 (by decide) x hx,
      show (s2DepthTwo h2 hq).u 2 = 5 from (s2DepthTwo_stage2 h2 hq).2.2,
      show ((5 : ℕ) : WithTop ℤ) = ((5 : ℤ) : WithTop ℤ) by norm_num] at hwin
    exact WithTop.coe_lt_coe.mp hwin

/-! ## Part 6 — the two quarantined premises are REFUTED where the campaign said they are

The funnel below carries `ev : LegacyEvaluation` and `lf : LegacyFGMN`.  Both emptiness
certificates land here, so the funnel's conditionality is machine-audited, not prose. -/

/-- ★ **the `ev` premise is EMPTY at the SG-0 frontier** — U13's char-2 contradiction,
machine-transplanted against the concrete node: any legacy single-ambient evaluation forces
`pointHgt 2 x (C 2) = ⊤` (the `[Algebra Kt L]` char-2 collapse kills the coefficient `2`),
but the landed node computes `pointHgt 2 x (C 2) = 4` (NP-0's tooth).  This upgrades
CC-17's prose caveat ("the contradiction transplants verbatim") to a theorem. -/
theorem s2Frontier_legacyEvaluation_isEmpty (w : S2LevelOneThreshold) :
    IsEmpty ((s2Frontier h2 hq L w).LegacyEvaluation) := by
  refine ⟨fun ev => ?_⟩
  -- the residue characteristic collapses `2` in `Kt`, hence in `L`
  have h2Kt : (2 : (S2DepthTwo h2 hq).fld 2) = 0 := by
    rcases s2Kt_eq_zero_or_one h2 hq (2 : (S2DepthTwo h2 hq).fld 2) with h | h
    · exact h
    · exfalso
      have h10 : (1 : (S2DepthTwo h2 hq).fld 2) + 1 = 1 + 0 := by
        rw [add_zero, one_add_one_eq_two, h]
      exact one_ne_zero (add_left_cancel h10)
  have h2L : (2 : L) = 0 := by
    have h := congrArg (algebraMap ((S2DepthTwo h2 hq).fld 2) L) h2Kt
    rwa [map_ofNat, map_zero] at h
  -- the legacy evaluation forces the U13 slot to `⊤` ...
  have hx := ev.pointHgt_eval 2 s2NPPointMk (Polynomial.C (2 : O))
  rw [Polynomial.eval₂_C] at hx
  have hc2 : ev.coeffHom (2 : O) = 0 := by
    rw [show ev.coeffHom (2 : O) = (2 : L) from map_ofNat ev.coeffHom 2, h2L]
  rw [hc2, ev.value_zero 2 (by decide)] at hx
  -- ... against the landed node's finite value `4` on the same slot
  have hfin : (s2Frontier h2 hq L w).node.pointHgt 2 s2NPPointMk (Polynomial.C (2 : O))
      = ((4 : ℤ) : WithTop ℤ) := s2NPPointHgt_two_C_two h2 hq s2NPPointMk
  exact WithTop.coe_ne_top (hfin.symm.trans hx)

/-- ★ **the `lf` premise is EMPTY at the landed operator readings** — FD-0's
unsatisfiability (`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`), transplanted to the
quarantine structure: no `LegacyFGMN` over ANY split frontier can read its
`normalizedResidual`/`keyPolynomial` as the landed S2 operators.  (A genuinely-μ₃-level
depth-two record — plan §5.2, nowhere landed — is NOT refuted; that is the premise's only
honest inhabitation route.) -/
theorem s2LegacyFGMN_landed_empty {E : Type uE} [Field E]
    (S : S2SourceFrontier h2 hq E L) (lf : S.LegacyFGMN)
    (hnorm : lf.fgmn.normalizedResidual = s2NormRes h2 hq)
    (hkp : lf.fgmn.keyPolynomial = S2KeyPoly h2 hq) : False :=
  (s2SourceLaws_depthTwo_unsatisfiable h2 hq _ lf.fgmn hnorm hkp).false lf.fgmnLaws

/-! ## Part 7 — ★ SG-1: the funnel, fired at the SG-0 frontier

Each stage is stated at `S := s2Frontier h2 hq L w`, so the full conditionality of every
statement is visible in its binders: `w` (open source datum) + `ev` (empty at S2, Part 6) +
`lf` (empty at the landed readings, Part 6).  Packaging shapes, per the recorded CC-17/
CC-18 conditionality; the S2 content is the `ev`/`lf`-free frontier of Parts 3–5. -/

/-- ★ SG-1 stage 1: `toChainRealization` fires at the SG-0 frontier. -/
def s2FrontierChainRealization (w : S2LevelOneThreshold)
    (ev : (s2Frontier h2 hq L w).LegacyEvaluation)
    (lf : (s2Frontier h2 hq L w).LegacyFGMN) :
    ChainRealization (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2) L 2 1 5 :=
  (s2Frontier h2 hq L w).toChainRealization ev lf

/-- ★ SG-1 stage 2: `calculusNonempty` fires at the SG-0 frontier. -/
theorem s2Frontier_calculusNonempty (w : S2LevelOneThreshold)
    (ev : (s2Frontier h2 hq L w).LegacyEvaluation)
    (lf : (s2Frontier h2 hq L w).LegacyFGMN) :
    Nonempty (FGMNCalculus (S2DepthTwo h2 hq) 2 1 5) :=
  (s2Frontier h2 hq L w).calculusNonempty ev lf

/-- ★ SG-1 stage 3: `s2RealizedInput` fires at the SG-0 frontier (the concrete
`keyAt 2 + 1` arising occurrence at degree 4). -/
def s2FrontierRealizedInput [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold)
    (ev : (s2Frontier h2 hq L w).LegacyEvaluation)
    (lf : (s2Frontier h2 hq L w).LegacyFGMN) :
    RealizedInput (s2ArisingCore h2 hq L)
      ((s2Frontier h2 hq L w).toChainRealization ev lf) :=
  (s2Frontier h2 hq L w).s2RealizedInput ev lf

/-- ★ SG-1 stage 4a: the S2 I.10a socket application fires at the SG-0 frontier. -/
theorem s2Frontier_ladder_socket [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold)
    (ev : (s2Frontier h2 hq L w).LegacyEvaluation)
    (lf : (s2Frontier h2 hq L w).LegacyFGMN) :
    CanonicalLadderConfigData
      (((s2Frontier h2 hq L w).s2RealizedInput ev lf).stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (((s2Frontier h2 hq L w).s2RealizedInput ev lf).inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      (((s2Frontier h2 hq L w).toChainRealization ev lf).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf))
      (canonicalResFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf))
      (useHeightFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf)) 4 :=
  s2_ladder_socket_application h2 hq (s2Frontier h2 hq L w) ev lf

/-- ★ SG-1 stage 4b: the S2 I.10b socket application fires at the SG-0 frontier, depth
pinned to the witness's own `r = 2`. -/
theorem s2Frontier_deepTwist_socket [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold)
    (ev : (s2Frontier h2 hq L w).LegacyEvaluation)
    (lf : (s2Frontier h2 hq L w).LegacyFGMN) :
    CanonicalDeepTwistConfigData
      (((s2Frontier h2 hq L w).s2RealizedInput ev lf).stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (((s2Frontier h2 hq L w).s2RealizedInput ev lf).inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      (((s2Frontier h2 hq L w).toChainRealization ev lf).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf))
      (canonicalResFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf))
      (useHeightFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf))
      (arenaFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf) Nat.one_lt_two)
      (towerReadFamily ((s2Frontier h2 hq L w).s2RealizedInput ev lf))
      ((s2Frontier h2 hq L w).toChainRealization ev lf).node.peelUnitFamily 2 4 :=
  s2_deepTwist_socket_application h2 hq (s2Frontier h2 hq L w) ev lf

end S2

end Uniformity.Density.Tower.C130sg

end

/-! ## Axiom footprint and cite ledger

CITES CONSUMED BY THIS FILE: **none**.  Every declaration rests on Lean/mathlib and the
Lean-core NP/RP/KP/FD chain; in particular `fgmn_dv_exact_mul` is not used. -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130sg.S2LevelOneThreshold
#print axioms Uniformity.Density.Tower.C130sg.s2FgmnAnchor_eq_depthOne
#print axioms Uniformity.Density.Tower.C130sg.s2FgmnAnchorKeys_eq_depthOne
#print axioms Uniformity.Density.Tower.C130sg.s2NPFull
#print axioms Uniformity.Density.Tower.C130sg.s2NPFull_one
#print axioms Uniformity.Density.Tower.C130sg.s2NPFull_two
#print axioms Uniformity.Density.Tower.C130sg.s2NPThresholdZ
#print axioms Uniformity.Density.Tower.C130sg.s2NPThresholdNat
#print axioms Uniformity.Density.Tower.C130sg.s2NPThresholdZ_one
#print axioms Uniformity.Density.Tower.C130sg.s2NPThresholdZ_two_eq_seam
#print axioms Uniformity.Density.Tower.C130sg.s2NPThresholdZ_two
#print axioms Uniformity.Density.Tower.C130sg.s2SplitNode
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_node_pointHgt
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_fgmn
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_thresholdZ_one
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_thresholdZ_two
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_levelTwo_ties
#print axioms Uniformity.Density.Tower.C130sg.S2LevelOneThreshold.ofSplitNode
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_legacyEvaluation_isEmpty
#print axioms Uniformity.Density.Tower.C130sg.s2LegacyFGMN_landed_empty
#print axioms Uniformity.Density.Tower.C130sg.s2FrontierChainRealization
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_calculusNonempty
#print axioms Uniformity.Density.Tower.C130sg.s2FrontierRealizedInput
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_ladder_socket
#print axioms Uniformity.Density.Tower.C130sg.s2Frontier_deepTwist_socket

end AxCheck
