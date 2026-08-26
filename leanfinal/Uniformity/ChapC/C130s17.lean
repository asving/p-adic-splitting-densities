/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130vw
import Uniformity.ChapC.C130pk
import Uniformity.ChapC.C130pt
import Uniformity.ChapC.C130s6
import Uniformity.ChapC.C130tr

/-!
# Uniformity.ChapC.C130s17 — the S2 acceptance gate (AMBIENT-SPLIT re-type, 2026-08-24)

**chain-carrier node CC-17 — the S2 acceptance gate**, re-typed by unit SF1 per
`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §2.

This file records the maximal honest S2 realization available from the landed carrier wave.
The repository side is a concrete inhabitant: the depth-two tower, canonical terminal
receiver, polynomial key chain, repaired Laurent normalizer, and complete level-two slot
carrier are assembled in `s2RepositoryRealization` (UNTOUCHED by the re-type).

## The U13 refutation and the ambient split (recorded 2026-08-24)

The original `S2SourceFrontier` typed its node source at ONE ambient `L` carrying both the
`O`-polynomial evaluation (`coeffHom`, `coord`, `valueOn`, `pointHgt_eval`) and the terminal
residue-field algebra (`[Algebra Kt L]`, `ambientLetter`, `psi_root`, `canonicalRead`).
U13 machine-REFUTED that typing (`leanfinal/scratch/U13_probe.lean`, `no_s2_node_source` /
`no_s2_source_frontier`, Lean-core): at S2 the terminal field has two elements, so
`(2 : L) = 0`, hence `coeffHom` kills the nonzero DVR constant `2` and `pointHgt_eval` +
`value_zero` force `pointHgt i x (C 2) = ⊤`, while `slot_value` + `hgt_ne_top` force it
finite on the live slot `i = 2`.  CC-17/CC-18's conditionals were therefore true-but-vacuous.

THIS FILE'S RE-TYPE (plan §2's REQUIRED CORRECTION): the bundle's node source is now
`SplitNodePointSource`, with the valued EVALUATION ambient `E` (a field with NO `Algebra Kt`
structure demanded) split from the RESIDUE/LETTER ambient `L` (which keeps `[Algebra Kt L]`).
No map `E → L` is carried, per the plan's fence.  The SF-4 non-vacuity tooth
(`s2Eval_C_two_ne_zero` below) machine-checks that the exact slot on which U13's refuter
fired is satisfiable in the split typing: at the concrete probe ambient
`FractionRing (Polynomial O)` with the injective coefficient read at the rational-function
coordinate, `eval₂ coeffHom coord (C 2) ≠ 0`.

## The SG-0 re-type of the FGMN legs (2026-08-25, unit SG01)

FD-0 (`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`, `runs/wave-b/verdict_FD01.md`)
machine-refuted this structure's ORIGINAL `fgmn`/`fgmnLaws` typing — `FGMNSourceData
(S2DepthTwo h2 hq) (s2RepositoryRealization h2 hq).keys 2 1 5` and its laws — at the landed
operator readings: `carried_key_is_key` + `carried_key_residual` + KP-9's degree dictionary
(`deg R₃(g) = deg g / 4` on keys) collide with the chain's own `deg (keyAt 2) = 4`.  Cause:
the abstract structure reuses the tower depth `r` as the FGMN key index, but the landed S2
operators realize the `μ₁ → μ₂` augmentation keyed at `keyAt 1` — the `r = 1` anchoring
RECORDED by RP-0's docstring, RP-11's course correction, and KP-3's anchoring note.  Per plan
§6 row SG-0 the two legs are therefore RE-TYPED here at that anchoring: the tower is the SAME
landed witness truncated to depth one (`s2FgmnAnchor` below — definitionally C130fd0's
`s2DepthOne`; the duplicate definition is forced by the import direction and rfl-pinned in
`C130sg`), the chain is `s2FgmnAnchorKeys` (`keyAt 1 = Φ′`), and FD-0's constructed records
`s2SourceDataOne`/`s2SourceLawsOne` (all thirteen laws discharged by named landed theorems)
fill the legs at the `C130sg` instance.  The REFUTED depth-two half moves to the quarantined
packaging premise `LegacyFGMN` (mirror of `LegacyEvaluation`, below).

## Corrected conditionality (REPLACES the pre-U13 caveat; updated at SG-0)

* `S2SourceFrontier` (split-ambient, r = 1 fgmn legs) is inhabited by `C130sg.s2Frontier`,
  CONDITIONAL on exactly one named source datum: the level-1 inherited threshold
  (`C130sg.S2LevelOneThreshold` — NP-4/NP-5's one open: no source occurrence names `T₁`;
  any candidate must satisfy `T₁ < 5`).  It is no longer refutable by U13's char-2 argument —
  the tooth section is the machine check.
* Packaging into the CURRENT single-ambient `ChainRealization` (C130fg, untouched here)
  additionally requires TWO QUARANTINED premises: `S2SourceFrontier.LegacyEvaluation` —
  exactly the U13-refuted single-ambient evaluation half, uninhabitable at S2 (the U13
  contradiction transplants verbatim; machine-certified at the SG-0 instance by
  `C130sg.s2Frontier_legacyEvaluation_isEmpty`) — and `S2SourceFrontier.LegacyFGMN` — the
  FD-0-refuted depth-two FGMN half, uninhabitable at the landed operator readings
  (`C130sg.s2LegacyFGMN_landed_empty`) and reserved for plan §5.2's genuinely-μ₃-level
  operators (nowhere landed).  Hence `toChainRealization`, `calculusNonempty`,
  `realizedInput`, and `s2RealizedInput` carry the EXPLICITLY-quarantined premises `ev`/`lf`
  and are retained as packaging shapes only, until the plan's SF-3 consumer ripple re-types
  `NodePointSource`/`ChainRealization` themselves.  Nothing downstream of `ev`/`lf` is a
  non-vacuous S2 statement; every non-vacuous statement of this file is either
  repository-side or `ev`/`lf`-free.

**[PK-2/U15, 2026-08-25] — the SF-3 consumer ripple ENACTED** (packaging route,
`PACKAGING_ROUTE_2026-08-25.md` §4.5): `SplitNodePointSource` + helpers moved to `C130k2`
(re-exported below); `ChainRealization` is now split-ambient with NO FGMN legs (C130fg,
PK-1), so the packaging is `toCarrier` — NO `LegacyEvaluation` and NO `LegacyFGMN` premise —
and `realizedInput`/`s2RealizedInput` are `ev`/`lf`-free.  The retired
`toChainRealization ev lf`/`calculusNonempty ev lf` are gone: the class packaging is the
factored `fgmnCalculusOf` (C130pk) and the honest anchored discharge is
`C130sg.s2_calculus_discharge` (unconditional, at `r = 1`, `(2,1,5)`).  `LegacyEvaluation`/
`LegacyFGMN`/`withLegacy` and the un-split `NodePointSource` are KEPT, marked QUARANTINE —
they are the U13/FD-0 refutation record, no longer on any packaging path; C130sg's two
emptiness theorems keep their statements verbatim.  The paragraph above this note is the
pre-ripple record.

Likewise, `S2InputData` exposes exactly the separate input-occurrence data needed by
`ArisingCore`; `S2InputData.toArisingCore` and `S2SourceFrontier.realizedInput` construct the
literal `RealizedInput`, selecting CC-9's `legalPoint` from the carried `point_exists`.

No declaration below assumes a cite.  The cite ledger for this unit is empty.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C130s17

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6

universe uE uKt uL

/-! ## The split-ambient node source — MOVED to the carrier skeleton ([PK-1/U15, 2026-08-25])

`SplitNodePointSource` and its helpers (`legalPoint`/`legalPoint_mem`/`stageCarrier`),
landed HERE by unit SF1 on 2026-08-24, moved VERBATIM to `C130k2.lean` (packaging-route
node PK-1, `PACKAGING_ROUTE_2026-08-25.md` §4.1) so the retyped CC-13 carrier
(`ChainRealization`, C130fg) can take the split node as its `node` leg — exactly the SF-3
consumer ripple SF1's landing note anticipated ("the plan's SF-3 consumer ripple may later
move it to the carrier skeleton").  The re-export below keeps the historical qualified name
`C130s17.SplitNodePointSource` resolving to the SAME constant (an alias, not a copy). -/

export Uniformity.Density.Tower (SplitNodePointSource)


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- Short name for the literal depth-two S2 tower fixed by design §6. -/
abbrev S2DepthTwo := s2DepthTwo h2 hq

/-! ## The fully concrete repository side (UNTOUCHED by the SF1 re-type) -/

/-- The canonical S2 terminal receiver.  C.97's witness uses one constant field at every
index, so CC-3's off-range `junk` maps are literally identity ring homomorphisms. -/
noncomputable def s2TerminalReceiver :
    TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2
      (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2) :=
  (S2DepthTwo h2 hq).terminalReceiver (fun _ _ _ => RingHom.id _)

/-- The maximal unconditional sub-record at the S2 gate: every repository-constructed
component of `ChainRealization`, plus CC-6's complete level-two stage carrier. -/
structure S2RepositoryRealization where
  receiver : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2
    (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2)
  keys : KeyChain (S2DepthTwo h2 hq)
  normalizer : LaurentNormalizer (S2DepthTwo h2 hq)
  stageTwo : Ladder.SlotCarrier O ((S2DepthTwo h2 hq).fld 2)

/-- The named, concrete maximal S2 repository realization. -/
noncomputable def s2RepositoryRealization : S2RepositoryRealization h2 hq where
  receiver := s2TerminalReceiver h2 hq
  keys := s2DepthTwoKeyChain h2 hq
  normalizer := (S2DepthTwo h2 hq).laurentNormalizer
  stageTwo := s2Slot₂ h2 hq

@[simp] theorem s2RepositoryRealization_receiver :
    (s2RepositoryRealization h2 hq).receiver = s2TerminalReceiver h2 hq := rfl

@[simp] theorem s2RepositoryRealization_keys :
    (s2RepositoryRealization h2 hq).keys = s2DepthTwoKeyChain h2 hq := rfl

@[simp] theorem s2RepositoryRealization_normalizer :
    (s2RepositoryRealization h2 hq).normalizer =
      (S2DepthTwo h2 hq).laurentNormalizer := rfl

@[simp] theorem s2RepositoryRealization_stageTwo :
    (s2RepositoryRealization h2 hq).stageTwo = s2Slot₂ h2 hq := rfl

/-! ## The r = 1 FGMN anchoring (SG-0 re-type, 2026-08-25)

FD-0 machine-refuted the depth-two typing of the frontier's FGMN legs at the landed operator
readings (`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`); the honest anchoring is the repo
depth `r = 1`, where the landed operators realize the `μ₁ → μ₂` augmentation keyed at
`keyAt 1 = Φ′`.  The two definitions below are byte-duplicates of C130fd0's
`s2DepthOne`/`s2DepthOneKeyChain` (rfl-pinned against them in `C130sg`): C130fd0 transitively
imports this file, so the anchoring objects must be re-declared here for the structure's
field types to mention them. -/

/-- [SG-0, 2026-08-25] **the depth-one FGMN anchor tower**: C.97's witness truncated to depth
ONE — the repo depth at which the landed S2 operators realize `FGMNSourceData` (RP-0's
docstring, RP-11's course correction, KP-3's anchoring note; the FD-0 finding).
Definitionally IDENTICAL to `C130fd0.s2DepthOne` (`C130sg.s2FgmnAnchor_eq_depthOne : rfl`). -/
noncomputable def s2FgmnAnchor : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 1 :=
  (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 1 (by omega)

/-- anti-drift pin: the anchor's terminal carrier IS the depth-two terminal carrier,
definitionally (C.97's witness uses one constant stage field at every index). -/
theorem s2FgmnAnchor_fld_eq : (s2FgmnAnchor h2 hq).fld 1 = (S2DepthTwo h2 hq).fld 2 := rfl

/-- `D₁ = ê₁·f̂₁ = 2` at the anchor. -/
theorem s2FgmnAnchor_Dcum_one : (s2FgmnAnchor h2 hq).Dcum 1 = 2 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide,
    Finset.prod_singleton, (s2FgmnAnchor h2 hq).he1, (s2FgmnAnchor h2 hq).hf1]
  rfl

/-- [SG-0] the anchor key assignment: the frame key `Φ′` at every index (only index `1` is
live; junk elsewhere, exactly as `s2DepthTwoKeyChain` treats its off-range indices). -/
noncomputable def s2FgmnAnchorKeyAt (_ : ℕ) : Polynomial O := (s2Frame h2 hq).key

/-- [SG-0] **the anchor key chain**: `keyAt 1 = Φ′`, monic, of the cumulative degree `2` —
definitionally `C130fd0.s2DepthOneKeyChain` (`C130sg.s2FgmnAnchorKeys_eq_depthOne : rfl`). -/
noncomputable def s2FgmnAnchorKeys : KeyChain (s2FgmnAnchor h2 hq) where
  keyAt := s2FgmnAnchorKeyAt h2 hq
  keyAt_one := rfl
  keyAt_monic := fun _ _ => (s2Frame h2 hq).hmonic
  keyAt_degree := by
    intro i hi
    obtain ⟨h1, h2i⟩ := hi
    interval_cases i
    show ((s2Frame h2 hq).key : Polynomial O).natDegree = (s2FgmnAnchor h2 hq).Dcum 1
    rw [(s2Frame h2 hq).hdeg, s2FgmnAnchor_Dcum_one h2 hq, C35b.e1_eq h2 hq,
      C35b.f1_eq h2 hq]

/-! ## Exact source frontier for a full S2 `ChainRealization` — SPLIT-AMBIENT re-type -/

/-- The exact source-side frontier left after the concrete repository assembly — RE-TYPED
2026-08-24 (unit SF1) at the split ambient of `S2_SOURCE_PLAN_2026-08-24.md` §2, after U13
machine-refuted the single-ambient typing (`scratch/U13_probe.lean`: `IsEmpty`, char-2
collision on the live slot `i = 2` at `C 2`).

The node source now evaluates into the valued ambient `E` and keeps letters/reads in the
residue ambient `L`; the three table equalities still prevent a future source instance from
bypassing CC-6 with freely chosen level-two tables.  This bundle is NOT claimed inhabited —
constructing an inhabitant is the S2-source campaign (plan §6) — but it is no longer
refutable by U13's char-2 argument (the SF-4 tooth below machine-checks the previously
contradictory slot).  Packaging into the CURRENT un-split `ChainRealization` additionally
requires the quarantined `LegacyEvaluation` premise; see its docstring. -/
structure S2SourceFrontier (E : Type uE) [Field E] (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] where
  node : SplitNodePointSource (L := L) (S2DepthTwo h2 hq) E
    (s2RepositoryRealization h2 hq).receiver (s2RepositoryRealization h2 hq).keys
  hgt_two : node.hgt 2 = s2Hgt₂ h2 hq
  dig_two : node.dig 2 = s2Dig₂ h2 hq
  full_two : node.Full 2 = S2Full₂ h2 hq
  /-- [SG-0, 2026-08-25] The FGMN source data, RE-TYPED at the recorded `r = 1` anchoring
  (`s2FgmnAnchor`) after FD-0 machine-refuted the original depth-two typing at the landed
  operator readings (`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`).  The depth-two half is
  now the quarantined `LegacyFGMN` premise. -/
  fgmn : FGMNSourceData (s2FgmnAnchor h2 hq) (s2FgmnAnchorKeys h2 hq) 2 1 5
  /-- [SG-0, 2026-08-25] The thirteen FGMN source laws at the same `r = 1` anchoring — the
  typing at which FD-0 discharged ALL thirteen by named landed theorems
  (`C130fd0.s2SourceLawsOne`). -/
  fgmnLaws : FGMNSourceLaws (s2FgmnAnchor h2 hq) (s2FgmnAnchorKeys h2 hq) 2 1 5 fgmn
  grade_compat : ∀ x : node.Point, node.Pt 2 x → ∀ g : Polynomial O,
    fgmn.nextValue g = node.pointHgt 2 x g
  letter_compat : ∀ i, StageLive 2 i →
    algebraMap ((S2DepthTwo h2 hq).fld 2) L
        ((s2RepositoryRealization h2 hq).receiver.topEquiv (fgmn.letter i)) =
      (node.ambientLetter i : L)

namespace S2SourceFrontier

variable {h2 hq}
variable {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- QUARANTINE (U13, 2026-08-24): the LEGACY single-ambient evaluation residual — exactly
the false-dictionary half that U13 refuted (`scratch/U13_probe.lean`, plan §2): an
`L`-valued coefficient read, coordinate, and lawful stage valuation tied to the split
bundle's `pointHgt` by `pointHgt_eval`.

At S2 this structure is UNINHABITABLE: `[Algebra Kt L]` forces `(2 : L) = 0`, so
`coeffHom 2 = 0` and `pointHgt_eval` + `value_zero` force `S.node.pointHgt 2 x (C 2) = ⊤`,
against the split bundle's own `slot_value` + `hgt_ne_top` — the U13 contradiction
transplants verbatim.  [PK-2/U15, 2026-08-25]: the SF-3 ripple is ENACTED —
the retyped carrier consumes the split node directly and NO packaging path consumes this
structure any more; it is KEPT purely as the U13 refutation record
(`C130sg.s2Frontier_legacyEvaluation_isEmpty` certifies its emptiness at the SG-0
instance).  Do NOT attempt to inhabit it; the campaign
fills `S2SourceFrontier`, never this. -/
structure LegacyEvaluation (S : S2SourceFrontier h2 hq E L) where
  coeffHom : O →+* L
  coord : S.node.Point → L
  valueOn : ℕ → L → WithTop ℤ
  value_zero : ∀ i, StageLive 2 i → valueOn i 0 = ⊤
  value_mul : ∀ i, StageLive 2 i → ∀ a b,
    valueOn i (a * b) = valueOn i a + valueOn i b
  value_add_ge : ∀ i, StageLive 2 i → ∀ a b,
    min (valueOn i a) (valueOn i b) ≤ valueOn i (a + b)
  value_add_eq : ∀ i, StageLive 2 i → ∀ a b,
    valueOn i a ≠ valueOn i b →
      valueOn i (a + b) = min (valueOn i a) (valueOn i b)
  pointHgt_eval : ∀ i x A,
    S.node.pointHgt i x A = valueOn i (Polynomial.eval₂ coeffHom (coord x) A)

/-- QUARANTINE (FD-0 → SG-0, 2026-08-25): the LEGACY depth-two FGMN residual — exactly the
false-anchoring half that FD-0 refuted (`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`,
`runs/wave-b/verdict_FD01.md`): the depth-two-typed FGMN records at the repository chain,
plus the two compat fields binding them to the split node (the shapes this structure's
`fgmn`/`fgmnLaws`/`grade_compat`/`letter_compat` carried before the SG-0 re-type).

At the landed operator readings (`normalizedResidual = s2NormRes`, `keyPolynomial =
S2KeyPoly`) this structure is UNINHABITABLE: `carried_key_is_key` forces
`keyAt 2 ∈ KP(μ₂)`, `carried_key_residual` forces `R₃(keyAt 2) = 1`, and KP-9's landed
degree dictionary collides with the chain's own `deg (keyAt 2) = 4` — machine-certified by
`C130sg.s2LegacyFGMN_landed_empty` (this file cannot import C130fd0, so the theorem lives
downstream).  A record built from genuinely `μ₃`-level depth-two operators (plan §5.2's
original intent, nowhere landed) is NOT refuted — which is why this is a named premise
rather than a dead field.  [PK-2/U15, 2026-08-25]: the SF-3 ripple is
ENACTED — the retyped carrier has NO FGMN legs and no packaging path consumes this
structure any more; it is KEPT purely as the FD-0 refutation record
(`C130sg.s2LegacyFGMN_landed_empty`).  Per the packaging route's §2 parameter adjudication,
a future genuinely-μ₃-level depth-two record must be typed `(2,1,21)`, not this structure's
`(2,1,5)`.  The campaign fills the `r = 1` legs of
`S2SourceFrontier`, never this. -/
structure LegacyFGMN (S : S2SourceFrontier h2 hq E L) where
  fgmn : FGMNSourceData (S2DepthTwo h2 hq) (s2RepositoryRealization h2 hq).keys 2 1 5
  fgmnLaws : FGMNSourceLaws (S2DepthTwo h2 hq)
    (s2RepositoryRealization h2 hq).keys 2 1 5 fgmn
  grade_compat : ∀ x : S.node.Point, S.node.Pt 2 x → ∀ g : Polynomial O,
    fgmn.nextValue g = S.node.pointHgt 2 x g
  letter_compat : ∀ i, StageLive 2 i →
    algebraMap ((S2DepthTwo h2 hq).fld 2) L
        ((s2RepositoryRealization h2 hq).receiver.topEquiv (fgmn.letter i)) =
      (S.node.ambientLetter i : L)

/-- Rebuild the legacy single-ambient `NodePointSource` from a split witness and the
quarantined evaluation premise.  Every non-evaluation field is the split bundle's own,
verbatim; only the eight `LegacyEvaluation` fields are new.  Empty premise at S2 (U13).
[PK-2/U15, 2026-08-25]: QUARANTINE — no packaging path consumes this any more (the retyped
carrier takes the split node directly); kept as the refutation record. -/
noncomputable def withLegacy (S : S2SourceFrontier h2 hq E L) (ev : S.LegacyEvaluation) :
    NodePointSource (L := L) (S2DepthTwo h2 hq)
      (s2RepositoryRealization h2 hq).receiver (s2RepositoryRealization h2 hq).keys where
  Point := S.node.Point
  Pt := S.node.Pt
  point_exists := S.node.point_exists
  coeffHom := ev.coeffHom
  coord := ev.coord
  valueOn := ev.valueOn
  value_zero := ev.value_zero
  value_mul := ev.value_mul
  value_add_ge := ev.value_add_ge
  value_add_eq := ev.value_add_eq
  hgt := S.node.hgt
  dig := S.node.dig
  pointHgt := S.node.pointHgt
  pointDig := S.node.pointDig
  pointHgt_eval := ev.pointHgt_eval
  slot_value := S.node.slot_value
  slot_digit := S.node.slot_digit
  hgt_zero := S.node.hgt_zero
  dig_zero := S.node.dig_zero
  hgt_ne_top := S.node.hgt_ne_top
  dig_ne_zero := S.node.dig_ne_zero
  hgt_add_ge := S.node.hgt_add_ge
  hgt_add_eq := S.node.hgt_add_eq
  dig_add := S.node.dig_add
  Full := S.node.Full
  lift := S.node.lift
  thresholdZ := S.node.thresholdZ
  thresholdNat := S.node.thresholdNat
  threshold_nonneg := S.node.threshold_nonneg
  window := S.node.window
  ambientLetter := S.node.ambientLetter
  key_value := S.node.key_value
  psi_root := S.node.psi_root
  canonicalRead := S.node.canonicalRead
  arenaRead := S.node.arenaRead
  towerRead := S.node.towerRead
  peelUnit := S.node.peelUnit

/-- ★ [PK-2/U15, 2026-08-25] **the carrier packaging, `ev`/`lf`-FREE** (replaces the
retired `toChainRealization ev lf`): a split-frontier witness packages into the PK-1-retyped
S2 `ChainRealization` with NO quarantined premise — the retyped carrier's node leg IS the
split node, so `S.node` slots in directly and neither the U13-refuted evaluation half
(`LegacyEvaluation`) nor the FD-0-refuted depth-two FGMN half (`LegacyFGMN`) is consumed.
The FGMN legs are gone from the carrier (factored into `fgmnCalculusOf`, C130pk); the
class discharge now lives at the honest `r = 1` anchoring (`C130sg.s2_calculus_discharge`),
so the retired `calculusNonempty ev lf` (the depth-two-typed, empty-premised packaging
shape) has NO replacement at this depth-two typing — per the §2 parameter adjudication of
`PACKAGING_ROUTE_2026-08-25.md`, every future S2 depth-two class statement must be typed
`(2,1,21)`, not `(2,1,5)`. -/
noncomputable def toCarrier (S : S2SourceFrontier h2 hq E L) :
    ChainRealization (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2) E L where
  receiver := (s2RepositoryRealization h2 hq).receiver
  keys := (s2RepositoryRealization h2 hq).keys
  normalizer := (s2RepositoryRealization h2 hq).normalizer
  node := S.node

/-- The canonical legal S2 level-two point, conditional only on the source P-locus carried
by `node.point_exists` — `ev`-free. -/
noncomputable def point (S : S2SourceFrontier h2 hq E L) : S.node.Point :=
  S.node.legalPoint 2 (show StageLive 2 2 from ⟨by decide, by decide⟩)

theorem point_mem (S : S2SourceFrontier h2 hq E L) : S.node.Pt 2 S.point :=
  S.node.legalPoint_mem 2 (show StageLive 2 2 from ⟨by decide, by decide⟩)

/-- The inherited integer threshold at the S2 occurrence; no numeral is substituted. -/
def thresholdZ (S : S2SourceFrontier h2 hq E L) : ℤ := S.node.thresholdZ 2

/-- The repository's natural-valued avatar of the inherited threshold. -/
def thresholdNat (S : S2SourceFrontier h2 hq E L) : ℕ := S.node.thresholdNat 2

/-- The canonical ambient read at the S2 occurrence, still deliberately distinct from
`arenaRead`. -/
def canonicalRead (S : S2SourceFrontier h2 hq E L) := S.node.canonicalRead 2

/-- The separate terminal-field arena read at the S2 occurrence. -/
def arenaRead (S : S2SourceFrontier h2 hq E L) := S.node.arenaRead 2

/-- The terminal-field lattice read at the S2 occurrence. -/
def towerRead (S : S2SourceFrontier h2 hq E L) := S.node.towerRead 2

/-- The S2 peel unit. -/
def peelUnit (S : S2SourceFrontier h2 hq E L) := S.node.peelUnit 2

/-- CC-6's concrete level-two carrier and the carrier derived from this future node source
have exactly the same repository degree data and the same three source tables — `ev`-free,
through the split `stageCarrier`. -/
theorem stageTwo_view (S : S2SourceFrontier h2 hq E L) :
    let C := S.node.stageCarrier 2 (show StageLive 2 2 from ⟨by decide, by decide⟩)
    C.D = (s2RepositoryRealization h2 hq).stageTwo.D ∧
      C.eC = (s2RepositoryRealization h2 hq).stageTwo.eC ∧
      C.fC = (s2RepositoryRealization h2 hq).stageTwo.fC ∧
      C.hgt = (s2RepositoryRealization h2 hq).stageTwo.hgt ∧
      C.dig = (s2RepositoryRealization h2 hq).stageTwo.dig ∧
      C.Full = (s2RepositoryRealization h2 hq).stageTwo.Full :=
  ⟨rfl, rfl, rfl, S.hgt_two, S.dig_two, S.full_two⟩

end S2SourceFrontier

/-! ## The SF-4 NON-VACUITY tooth — the split bundle is not char-2-refutable

U13's refuter fired on ONE slot: in the single-ambient typing, `[Algebra Kt L]` forced
`eval₂ coeffHom (coord x) (C 2) = coeffHom 2 = 0`, then `value_zero` + `slot_value` +
`hgt_ne_top` clashed on the live slot `i = 2`.  In the split typing the evaluation lands in
`E`, which carries NO `Algebra Kt E`.  At the plan §6 SF-4 probe ambient
`FractionRing (Polynomial O)`, with the injective coefficient read through `Polynomial.C`
and the rational-function coordinate `X`, that exact evaluation is provably NONZERO
(`s2Eval_C_two_ne_zero`): the refuting derivation no longer type-checks against the
re-typed bundle.  This is a satisfiability check for the re-typed `coeffHom`/`coord`/
`pointHgt_eval` slot ONLY — no inhabitation of `S2SourceFrontier` is claimed (that is the
campaign, plan §6 nodes NV-0..SG-1). -/

/-- SF-4 probe: the faithful coefficient read into the characteristic-preserving valued
ambient `FractionRing (Polynomial O)` — constants embed through `Polynomial.C` and the
fraction-ring coercion, killing nothing. -/
noncomputable def s2EvalHom : O →+* FractionRing (Polynomial O) :=
  (algebraMap (Polynomial O) (FractionRing (Polynomial O))).comp Polynomial.C

/-- SF-4 probe: the rational-function variable as the evaluation coordinate. -/
noncomputable def s2EvalCoord : FractionRing (Polynomial O) :=
  algebraMap (Polynomial O) (FractionRing (Polynomial O)) Polynomial.X

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- The probe coefficient read is injective — the faithfulness the single ambient could not
have at S2 (every `O →+* L` with `[Algebra Kt L]` kills `2` there). -/
theorem s2EvalHom_injective : Function.Injective (s2EvalHom (O := O)) :=
  (IsFractionRing.injective (Polynomial O) (FractionRing (Polynomial O))).comp
    Polynomial.C_injective

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- ★ **The SF-4 NON-VACUITY tooth**: the exact slot on which U13's refuter fired.  In the
un-split typing this evaluation was FORCED to `0` (char 2 of `L`), which made the bundle
`IsEmpty`; in the split typing, at the concrete probe pair, it is provably nonzero, so the
char-2 refutation cannot be replayed against the re-typed `S2SourceFrontier`.  The
hypothesis is `h2.ne_zero` at every S2 call site. -/
theorem s2Eval_C_two_ne_zero (htwo : (2 : O) ≠ 0) :
    Polynomial.eval₂ (s2EvalHom (O := O)) s2EvalCoord (Polynomial.C (2 : O)) ≠ 0 := by
  rw [Polynomial.eval₂_C]
  intro h
  exact htwo (s2EvalHom_injective (by rw [h, map_zero]))

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- The tooth at the S2 pin: `h2` supplies the nonzero hypothesis. -/
example (hirr : Irreducible (2 : O)) :
    Polynomial.eval₂ (s2EvalHom (O := O)) s2EvalCoord (Polynomial.C (2 : O)) ≠ 0 :=
  s2Eval_C_two_ne_zero hirr.ne_zero

/-- The ambient PAIR at the probe where the old refuter fired, elaborated: the re-typed
bundle instantiates at the valued probe `E = FractionRing (Polynomial O)` together with the
residue-side `L = Kt` itself (`Algebra.id`) — the typing in which U13's derivation is
severed.  (Type-level check only; no inhabitant is claimed.) -/
example : Type _ :=
  S2SourceFrontier h2 hq (FractionRing (Polynomial O)) ((S2DepthTwo h2 hq).fld 2)

/-! ## Exact input-occurrence frontier and conditional `RealizedInput` -/

/-- The remaining input-specific source occurrence needed to build an `ArisingCore` on the
concrete S2 tower.  These fields are not consequences of a `DeepTower`: completeness and a
monic input polynomial with the exact degree/key-free conditions must be supplied. -/
structure S2InputData (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] where
  n : ℕ
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  F₀ : Polynomial O
  F₀_monic : F₀.Monic
  μ : ℕ
  hμ : 1 ≤ μ
  degree_input : F₀.natDegree = n
  degree_block : n = μ * (S2DepthTwo h2 hq).Dcum 2
  keyfree : IsCoprime
    (F₀.map (algebraMap O (FractionRing O)))
    (((s2RepositoryRealization h2 hq).keys.keyAt 2).map
      (algebraMap O (FractionRing O)))

namespace S2InputData

variable {L : Type uL} [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- Package the explicit input occurrence into freeze-v2's literal `ArisingCore`. -/
noncomputable def toArisingCore (I : S2InputData h2 hq L) :
    ArisingCore (O := O) ((S2DepthTwo h2 hq).fld 2) L I.n where
  π := 2
  hπ := h2
  complete := I.complete
  finite := inferInstance
  F := s2Frame h2 hq
  H₀ := 1
  hpin := s2Frame_pin h2 hq
  r := 2
  i := 2
  hi := ⟨by decide, by decide⟩
  T := S2DepthTwo h2 hq
  receiver := (s2RepositoryRealization h2 hq).receiver
  stageKey := (s2RepositoryRealization h2 hq).keys.keyAt 2
  stageDeg := (S2DepthTwo h2 hq).Dcum 2
  stageKey_monic := (s2RepositoryRealization h2 hq).keys.keyAt_monic 2
    (show StageLive 2 2 from ⟨by decide, by decide⟩)
  stageKey_degree := (s2RepositoryRealization h2 hq).keys.keyAt_degree 2
    (show StageLive 2 2 from ⟨by decide, by decide⟩)
  F₀ := I.F₀
  F₀_monic := I.F₀_monic
  μ := I.μ
  hμ := I.hμ
  degree_input := I.degree_input
  degree_block := I.degree_block
  keyfree := I.keyfree

end S2InputData

/-! The input-polynomial side is in fact constructible once the campaign's standard
completeness instance is present: `keyAt 2 + 1` is monic of degree four and coprime to
`keyAt 2` after passage to the fraction field. -/

/-- A concrete S2 input polynomial, chosen only to witness the acceptance occurrence. -/
noncomputable def s2InputPolynomial : Polynomial O :=
  (s2RepositoryRealization h2 hq).keys.keyAt 2 + 1

theorem s2InputPolynomial_monic : (s2InputPolynomial h2 hq).Monic := by
  apply Polynomial.Monic.add_of_left
    ((s2RepositoryRealization h2 hq).keys.keyAt_monic 2
      (show StageLive 2 2 from ⟨by decide, by decide⟩))
  rw [degree_one]
  rw [degree_eq_natDegree
    ((s2RepositoryRealization h2 hq).keys.keyAt_monic 2
      (show StageLive 2 2 from ⟨by decide, by decide⟩)).ne_zero]
  rw [(s2RepositoryRealization h2 hq).keys.keyAt_degree 2
      (show StageLive 2 2 from ⟨by decide, by decide⟩),
    s2DepthTwo_Dcum_two h2 hq]
  decide

theorem s2InputPolynomial_natDegree : (s2InputPolynomial h2 hq).natDegree = 4 := by
  rw [s2InputPolynomial]
  change (((s2RepositoryRealization h2 hq).keys.keyAt 2) + C 1).natDegree = 4
  rw [natDegree_add_C,
    (s2RepositoryRealization h2 hq).keys.keyAt_degree 2
      (show StageLive 2 2 from ⟨by decide, by decide⟩),
    s2DepthTwo_Dcum_two h2 hq]

theorem s2InputPolynomial_keyfree : IsCoprime
    ((s2InputPolynomial h2 hq).map (algebraMap O (FractionRing O)))
    (((s2RepositoryRealization h2 hq).keys.keyAt 2).map
      (algebraMap O (FractionRing O))) := by
  rw [s2InputPolynomial, Polynomial.map_add, Polynomial.map_one]
  exact IsCoprime.add_one_left_of_dvd dvd_rfl

/-- The concrete input-occurrence data at `n = 4`, `μ = 1`.  Completeness is the standard
ambient campaign typeclass; every polynomial and dictionary field is proved here. -/
noncomputable def s2InputData (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : S2InputData h2 hq L where
  n := 4
  complete := inferInstance
  F₀ := s2InputPolynomial h2 hq
  F₀_monic := s2InputPolynomial_monic h2 hq
  μ := 1
  hμ := by decide
  degree_input := s2InputPolynomial_natDegree h2 hq
  degree_block := by rw [s2DepthTwo_Dcum_two]
  keyfree := s2InputPolynomial_keyfree h2 hq

/-- The resulting named S2 `ArisingCore`. -/
noncomputable def s2ArisingCore (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    ArisingCore (O := O) ((S2DepthTwo h2 hq).fld 2) L 4 :=
  (s2InputData h2 hq L).toArisingCore

namespace S2SourceFrontier

variable {h2 hq}
variable {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- Given the split source frontier and the explicit input frontier, construct the literal
S2 `RealizedInput` — [PK-2/U15, 2026-08-25]: the two quarantined legacy premises `ev`/`lf`
are DELETED (the PK-1 carrier consumes the split node directly).  The selected point is
CC-9's `legalPoint`, hence comes from the carried `point_exists`.  All three dictionary
fields remain `rfl` (scratch authority: `U15_check.s2RealizedInputV2`). -/
noncomputable def realizedInput (S : S2SourceFrontier h2 hq E L)
    (I : S2InputData h2 hq L) :
    RealizedInput I.toArisingCore S.toCarrier where
  receiver_eq := rfl
  stageKey_eq := rfl
  stageDeg_eq := rfl
  point := S.point
  point_mem := S.point_mem

/-- The maximal conditional acceptance-gate input, `ev`/`lf`-FREE ([PK-2/U15]): the arising
occurrence is the concrete `keyAt 2 + 1` occurrence; the only remaining premise is the
separately exposed split frontier itself (inhabited by `C130sg.s2Frontier`, conditional on
exactly the level-1 threshold source datum `w`). -/
noncomputable def s2RealizedInput
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq E L) :
    RealizedInput (s2ArisingCore h2 hq L) S.toCarrier :=
  realizedInput S (s2InputData h2 hq L)

end S2SourceFrontier

end Uniformity.Density.Tower.C130s17

/-! ## Axiom footprint and cite ledger

CITES CONSUMED BY THIS FILE: **none**.  All declarations below use Lean/mathlib theorems and
landed Lean-core CC constructors.  In particular `fgmn_dv_exact_mul` is not used.
-/

section AxCheck

-- [PK-1/U15] the split node source and its helpers moved to C130k2; their `#print axioms`
-- rows live there (the alias `C130s17.SplitNodePointSource` resolves to the same constant).
#print axioms Uniformity.Density.Tower.C130s17.s2TerminalReceiver
#print axioms Uniformity.Density.Tower.C130s17.S2DepthTwo
#print axioms Uniformity.Density.Tower.C130s17.S2RepositoryRealization
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_receiver
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_keys
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_normalizer
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_stageTwo
#print axioms Uniformity.Density.Tower.C130s17.s2FgmnAnchor
#print axioms Uniformity.Density.Tower.C130s17.s2FgmnAnchor_fld_eq
#print axioms Uniformity.Density.Tower.C130s17.s2FgmnAnchor_Dcum_one
#print axioms Uniformity.Density.Tower.C130s17.s2FgmnAnchorKeyAt
#print axioms Uniformity.Density.Tower.C130s17.s2FgmnAnchorKeys
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.LegacyEvaluation
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.LegacyFGMN
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.withLegacy
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.toCarrier
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.point
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.point_mem
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.thresholdZ
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.thresholdNat
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.canonicalRead
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.arenaRead
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.towerRead
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.peelUnit
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.stageTwo_view
#print axioms Uniformity.Density.Tower.C130s17.s2EvalHom
#print axioms Uniformity.Density.Tower.C130s17.s2EvalCoord
#print axioms Uniformity.Density.Tower.C130s17.s2EvalHom_injective
#print axioms Uniformity.Density.Tower.C130s17.s2Eval_C_two_ne_zero
#print axioms Uniformity.Density.Tower.C130s17.S2InputData
#print axioms Uniformity.Density.Tower.C130s17.S2InputData.toArisingCore
#print axioms Uniformity.Density.Tower.C130s17.s2InputPolynomial
#print axioms Uniformity.Density.Tower.C130s17.s2InputPolynomial_monic
#print axioms Uniformity.Density.Tower.C130s17.s2InputPolynomial_natDegree
#print axioms Uniformity.Density.Tower.C130s17.s2InputPolynomial_keyfree
#print axioms Uniformity.Density.Tower.C130s17.s2InputData
#print axioms Uniformity.Density.Tower.C130s17.s2ArisingCore
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.realizedInput
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.s2RealizedInput

end AxCheck
