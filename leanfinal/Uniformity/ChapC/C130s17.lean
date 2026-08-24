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

## Corrected conditionality (REPLACES the pre-U13 caveat)

* `S2SourceFrontier` (split-ambient) is NOT claimed inhabited: constructing an inhabitant is
  the S2-source campaign (plan §6, nodes NV/NP/RP/KP/FD/SG).  It is, however, no longer
  refutable by U13's char-2 argument — the tooth section is the machine check.
* Packaging into the CURRENT single-ambient `ChainRealization` (C130fg, untouched here)
  additionally requires the QUARANTINED premise `S2SourceFrontier.LegacyEvaluation` — exactly
  the U13-refuted single-ambient evaluation half, which is uninhabitable at S2 (the U13
  contradiction transplants verbatim against the split bundle's live tables).  Hence
  `toChainRealization`, `calculusNonempty`, `realizedInput`, and `s2RealizedInput` carry an
  EXPLICITLY-empty-at-S2 premise `ev` and are retained as packaging shapes only, until the
  plan's SF-3 consumer ripple re-types `NodePointSource`/`ChainRealization` themselves.
  Nothing downstream of `ev` is a non-vacuous S2 statement; every non-vacuous statement of
  this file is either repository-side or `ev`-free.

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

/-! ## The corrected split-ambient node source (S2_SOURCE_PLAN_2026-08-24.md §2)

The general (any-depth) split re-type of C130k's `NodePointSource`, landed here because this
file is the re-typed bundle's authority; the plan's SF-3 consumer ripple may later move it to
the carrier skeleton.  Field-for-field byte-parallel to C130k except the four evaluation
fields, whose codomain moves from `L` to the new valued ambient `E`. -/

section SplitAmbient

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- The AMBIENT-SPLIT node-point source (plan §2's REQUIRED CORRECTION, re-typed
2026-08-24 by unit SF1): C130k's `NodePointSource` with the single ambient `L` split into

* the VALUED EVALUATION ambient `E` — `coeffHom`, `coord`, `valueOn`, `pointHgt_eval` —
  a bare field, with NO `Algebra Kt E` demanded, so a faithful evaluation need not kill a
  nonzero DVR constant; and
* the RESIDUE/LETTER ambient `L` — `ambientLetter`, `psi_root`, `canonicalRead` — which
  keeps `[Algebra Kt L]` (at S2 this forces `(2 : L) = 0`, harmlessly: `L` no longer hosts
  the evaluation).

U13 (`leanfinal/scratch/U13_probe.lean`, `no_s2_node_source`) machine-refuted the un-split
typing at S2: the two roles cannot share one field in residue characteristic two.  Per the
plan's fence, NO map `E → L` and no identification of node points with FGMN roots is
carried.  All non-evaluation fields are byte-parallel to C130k's `NodePointSource`. -/
structure SplitNodePointSource
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    {Kt : Type uKt} [Field Kt] (E : Type uE) [Field E] {L : Type uL} [Field L]
    [Algebra Kt L]
    (receiver : TerminalReceiver F H₀ hpin r W Kt) (K : KeyChain W) where
  /-- DEF GENTOW5-1 and EFF.GENTOW5.16: the legal node points (the P-locus). -/
  Point : Type
  /-- EFF.GENTOW5.16: legality of a node point at each live stage. -/
  Pt : ℕ → Point → Prop
  /-- EFF.GENTOW5.16: every live stage has a legal point. -/
  point_exists : ∀ i, StageLive r i → Nonempty {x : Point // Pt i x}
  /-- EFF.GENTOW5.16/.19 (SPLIT: valued in `E`): the coefficient read of the evaluation. -/
  coeffHom : O →+* E
  /-- EFF.GENTOW5.16/.19 (SPLIT: valued in `E`): the coordinate of a node point. -/
  coord : Point → E
  /-- EFF.GENTOW5.16/.19 (SPLIT: valued in `E`): the stage valuation read. -/
  valueOn : ℕ → E → WithTop ℤ
  /-- EFF.GENTOW5.19: valuation law — zero has infinite value. -/
  value_zero : ∀ i, StageLive r i → valueOn i 0 = ⊤
  /-- EFF.GENTOW5.19: valuation law — multiplicativity. -/
  value_mul : ∀ i, StageLive r i → ∀ a b,
    valueOn i (a * b) = valueOn i a + valueOn i b
  /-- EFF.GENTOW5.19: valuation law — ultrametric inequality. -/
  value_add_ge : ∀ i, StageLive r i → ∀ a b,
    min (valueOn i a) (valueOn i b) ≤ valueOn i (a + b)
  /-- EFF.GENTOW5.19: valuation law — ultrametric equality off ties. -/
  value_add_eq : ∀ i, StageLive r i → ∀ a b,
    valueOn i a ≠ valueOn i b →
      valueOn i (a + b) = min (valueOn i a) (valueOn i b)

  /-- EFF.T2.04: the stage height table. -/
  hgt : ℕ → Polynomial O → WithTop ℤ
  /-- EFF.T2.05: the stage digit table. -/
  dig : (i : ℕ) → Polynomial O → W.fld i
  /-- EFF.T2.04 at a node point: the pointwise height read. -/
  pointHgt : ℕ → Point → Polynomial O → WithTop ℤ
  /-- EFF.T2.05 at a node point: the pointwise digit read. -/
  pointDig : (i : ℕ) → Point → Polynomial O → W.fld i
  /-- The point read is an actual polynomial evaluation, not a free table (SPLIT: the
  evaluation happens in `E`; retained unchanged in meaning, per plan §5.1). -/
  pointHgt_eval : ∀ i x A,
    pointHgt i x A = valueOn i (Polynomial.eval₂ coeffHom (coord x) A)
  /-- EFF.T2.04: the stage height table agrees with every legal-point read in slot range. -/
  slot_value : ∀ i (_hi : StageLive r i) (x : Point), Pt i x →
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < W.Dcum i → pointHgt i x A = hgt i A
  /-- EFF.T2.05: the stage digit table agrees with every legal-point read in slot range. -/
  slot_digit : ∀ i (_hi : StageLive r i) (x : Point), Pt i x →
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < W.Dcum i → pointDig i x A = dig i A

  /-- EFF.T2.04: stage law — zero has infinite height. -/
  hgt_zero : ∀ i, StageLive r i → hgt i 0 = ⊤
  /-- EFF.T2.05: stage law — zero has digit zero. -/
  dig_zero : ∀ i, StageLive r i → dig i 0 = 0
  /-- EFF.T2.04: stage law — slot-range nonzero polynomials have finite height. -/
  hgt_ne_top : ∀ i, StageLive r i → ∀ A : Polynomial O,
    A ≠ 0 → A.natDegree < W.Dcum i → hgt i A ≠ ⊤
  /-- EFF.T2.05: stage law — slot-range nonzero polynomials have nonzero digit. -/
  dig_ne_zero : ∀ i, StageLive r i → ∀ A : Polynomial O,
    A ≠ 0 → A.natDegree < W.Dcum i → dig i A ≠ 0
  /-- EFF.T2.04: stage law — ultrametric inequality for heights. -/
  hgt_add_ge : ∀ i, StageLive r i → ∀ A B,
    min (hgt i A) (hgt i B) ≤ hgt i (A + B)
  /-- EFF.T2.04: stage law — ultrametric equality off ties. -/
  hgt_add_eq : ∀ i, StageLive r i → ∀ A B,
    hgt i A ≠ hgt i B → hgt i (A + B) = min (hgt i A) (hgt i B)
  /-- EFF.T2.05: stage law — digit additivity at a common height, off digit cancellation. -/
  dig_add : ∀ i, StageLive r i → ∀ A B : Polynomial O, ∀ k : ℤ,
    hgt i A = (k : WithTop ℤ) → hgt i B = (k : WithTop ℤ) →
    dig i A + dig i B ≠ 0 →
      hgt i (A + B) = (k : WithTop ℤ) ∧ dig i (A + B) = dig i A + dig i B
  /-- EFF.T2.09: the fullness predicate for realizable heights. -/
  Full : ℕ → ℤ → Prop
  /-- EFF.T2.09: every full height realizes every nonzero digit by a slot-range polynomial. -/
  lift : ∀ i, StageLive r i → ∀ k : ℤ, Full i k → ∀ c : W.fld i, c ≠ 0 →
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < W.Dcum i ∧
      hgt i A = (k : WithTop ℤ) ∧ dig i A = c

  /-- EFF.T2.04/.11: inherited integer input, not a function inferred from `(W,i,F₀)`. -/
  thresholdZ : ℕ → ℤ
  /-- Repo dictionary to E.11's current natural-valued `BlockData.T`. -/
  thresholdNat : ℕ → ℕ
  /-- The dictionary obligation forced by the natural-valued `BlockData.T`: if a source
  instance has a genuinely negative inherited threshold, this field is uninhabitable and
  E.11 must be re-signed to `ℤ`; no truncation to zero is allowed. -/
  threshold_nonneg : ∀ i, StageLive r i → (thresholdNat i : ℤ) = thresholdZ i
  /-- EFF.T2.11: the WINDOW source law `T < d(Φ(ρ)) < ∞` at every legal point. -/
  window : ∀ i, StageLive r i → ∀ x : Point, Pt i x →
    (thresholdZ i : WithTop ℤ) < pointHgt i x (K.keyAt i) ∧
      pointHgt i x (K.keyAt i) ≠ ⊤

  /-- EFF.GENTOW5 S2.1/S2.3 (residue ambient `L`): the ambient node-point letters. -/
  ambientLetter : ℕ → Lˣ
  /-- EFF.GENTOW5.19: the exact key value `u_(i+1)` at a legal point (gauge-live only). -/
  key_value : ∀ i, GaugeLive r i → ∀ x : Point, Pt i x →
    pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ)
  /-- EFF.GENTOW5 S2.3 (residue ambient `L`): the transported `ψ`-root law for the ambient
  letter. -/
  psi_root : ∀ i, GaugeLive r i →
    Polynomial.eval₂ ((algebraMap Kt L).comp (receiver.levelHom i))
      (ambientLetter i : L) (W.ψ i) = 0
  /-- EFF.T1.01 and EFF.GENTOW5 S2.3 step (3) (residue ambient `L`): the L-valued node
  read. -/
  canonicalRead : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Lˣ
  /-- D.07/D.08, D.44 and EFF.T3.21: the separate terminal-field W-leg read. -/
  arenaRead : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Ktˣ
  /-- D.07/D.08, D.44 and EFF.T3.21: the terminal-field lattice read for the arena family. -/
  towerRead : (i : ℕ) → LevelExponentLattice i → Kt
  /-- EFF.T1.01--.03 and EFF.T3.21: the peel units of the separate arena data. -/
  peelUnit : ℕ → Ktˣ

namespace SplitNodePointSource

variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-- The canonical legal point at a live stage (choice on `point_exists`) — CC-9's
`legalPoint`, verbatim at the split typing (C130pt's definition on the un-split node). -/
noncomputable def legalPoint (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) : S.Point :=
  ((S.point_exists i hi).some : {x : S.Point // S.Pt i x}).1

/-- The canonical legal point is legal. -/
theorem legalPoint_mem (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) : S.Pt i (S.legalPoint i hi) :=
  ((S.point_exists i hi).some : {x : S.Point // S.Pt i x}).2

/-- CC-5's producing map at the split typing (C130st's `stageCarrier`, verbatim: every
field consumed is ambient-free, so the split changes nothing here): every live stage of a
`SplitNodePointSource` yields the landed E.10 `Ladder.SlotCarrier` over the stage residue
field `W.fld i`. -/
def stageCarrier (S : SplitNodePointSource (L := L) W E receiver K) (i : ℕ)
    (hi : StageLive r i) : Ladder.SlotCarrier O (W.fld i) where
  D := W.Dcum i
  hD := W.Dcum_pos hi.2
  eC := W.ehat i
  fC := W.fhat i
  hef := W.Dcum_eq_ehat_mul_fhat i
  heC := W.ehat_pos hi.2
  hfC := W.fhat_pos hi.2
  hgt := S.hgt i
  dig := S.dig i
  hgt_zero := S.hgt_zero i hi
  dig_zero := S.dig_zero i hi
  hgt_ne_top := S.hgt_ne_top i hi
  dig_ne_zero := S.dig_ne_zero i hi
  hgt_add_ge := S.hgt_add_ge i hi
  hgt_add_eq := S.hgt_add_eq i hi
  dig_add := S.dig_add i hi
  Full := S.Full i
  hlift := S.lift i hi

end SplitNodePointSource

end SplitAmbient

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
  fgmn : FGMNSourceData (S2DepthTwo h2 hq)
    (s2RepositoryRealization h2 hq).keys 2 1 5
  fgmnLaws : FGMNSourceLaws (S2DepthTwo h2 hq)
    (s2RepositoryRealization h2 hq).keys 2 1 5 fgmn
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
transplants verbatim.  It exists ONLY so the packaging into the CURRENT un-split
`ChainRealization` (C130fg, out of this unit's sanction) stays typeable until the plan's
SF-3 consumer ripple re-types that carrier.  Do NOT attempt to inhabit it; the campaign
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

/-- Rebuild the legacy single-ambient `NodePointSource` from a split witness and the
quarantined evaluation premise.  Every non-evaluation field is the split bundle's own,
verbatim; only the eight `LegacyEvaluation` fields are new.  Empty premise at S2 (U13). -/
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

/-- A split-frontier witness packages into the literal full S2 `ChainRealization` — but,
until C130fg's carrier is itself ambient-split (plan SF-3), ONLY through the quarantined
legacy premise `ev`, which is uninhabitable at S2 (U13).  This is a packaging shape, not a
non-vacuous S2 statement; its S2 content lives entirely in the `ev`-free fields of `S`. -/
noncomputable def toChainRealization (S : S2SourceFrontier h2 hq E L)
    (ev : S.LegacyEvaluation) :
    ChainRealization (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2) L 2 1 5 where
  receiver := (s2RepositoryRealization h2 hq).receiver
  keys := (s2RepositoryRealization h2 hq).keys
  normalizer := (s2RepositoryRealization h2 hq).normalizer
  node := S.withLegacy ev
  fgmn := S.fgmn
  fgmnLaws := S.fgmnLaws
  grade_compat := S.grade_compat
  letter_compat := S.letter_compat

/-- The first calculus is non-vacuous exactly when the split frontier AND (until the SF-3
carrier ripple) the quarantined legacy premise are inhabited; the latter is empty at S2
(U13).  No class instance is registered. -/
theorem calculusNonempty (S : S2SourceFrontier h2 hq E L) (ev : S.LegacyEvaluation) :
    Nonempty (FGMNCalculus (S2DepthTwo h2 hq) 2 1 5) :=
  chainRealization_calculus_nonempty (S.toChainRealization ev)

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

/-- Given the split source frontier, the quarantined legacy premise (empty at S2 — U13),
and the explicit input frontier, construct the literal S2 `RealizedInput`.  The selected
point is CC-9's `legalPoint`, hence comes from the carried `point_exists`. -/
noncomputable def realizedInput (S : S2SourceFrontier h2 hq E L)
    (ev : S.LegacyEvaluation) (I : S2InputData h2 hq L) :
    RealizedInput I.toArisingCore (S.toChainRealization ev) where
  receiver_eq := rfl
  stageKey_eq := rfl
  stageDeg_eq := rfl
  point := S.point
  point_mem := S.point_mem

/-- The maximal conditional acceptance-gate input: the arising occurrence is the concrete
`keyAt 2 + 1` occurrence; the remaining premises are the separately exposed split frontier
and the quarantined legacy evaluation (empty at S2 — U13). -/
noncomputable def s2RealizedInput
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq E L) (ev : S.LegacyEvaluation) :
    RealizedInput (s2ArisingCore h2 hq L) (S.toChainRealization ev) :=
  realizedInput S ev (s2InputData h2 hq L)

end S2SourceFrontier

end Uniformity.Density.Tower.C130s17

/-! ## Axiom footprint and cite ledger

CITES CONSUMED BY THIS FILE: **none**.  All declarations below use Lean/mathlib theorems and
landed Lean-core CC constructors.  In particular `fgmn_dv_exact_mul` is not used.
-/

section AxCheck

#print axioms Uniformity.Density.Tower.C130s17.SplitNodePointSource
#print axioms Uniformity.Density.Tower.C130s17.SplitNodePointSource.legalPoint
#print axioms Uniformity.Density.Tower.C130s17.SplitNodePointSource.legalPoint_mem
#print axioms Uniformity.Density.Tower.C130s17.SplitNodePointSource.stageCarrier
#print axioms Uniformity.Density.Tower.C130s17.s2TerminalReceiver
#print axioms Uniformity.Density.Tower.C130s17.S2DepthTwo
#print axioms Uniformity.Density.Tower.C130s17.S2RepositoryRealization
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_receiver
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_keys
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_normalizer
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_stageTwo
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.LegacyEvaluation
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.withLegacy
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.toChainRealization
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier.calculusNonempty
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
