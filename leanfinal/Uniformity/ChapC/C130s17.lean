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
# Uniformity.ChapC.C130s17 — the S2 acceptance gate

**chain-carrier node CC-17 — the S2 acceptance gate.**

This file records the maximal honest S2 realization available from the landed carrier wave.
The repository side is a concrete inhabitant: the depth-two tower, canonical terminal
receiver, polynomial key chain, repaired Laurent normalizer, and complete level-two slot
carrier are assembled in `s2RepositoryRealization`.

The full `ChainRealization` is not unconditionally inhabitable from the landed corpus.  The
precise missing source objects are exposed, without weakening, by `S2SourceFrontier`: a full
`NodePointSource` (including the legal P-locus/evaluation model, the still-missing level-one
stage family, inherited threshold/window, and the two source reads), an `FGMNSourceData`, its
thirteen `FGMNSourceLaws`, and OPEN-DICT-2/4.  `S2SourceFrontier.toChainRealization` proves
that these are exactly sufficient; `S2SourceFrontier.calculusNonempty` then reaches the
literal A-C.11 `FGMNCalculus` at `(e',f',u') = (2,1,5)`.

Likewise, `S2InputData` exposes exactly the separate input-occurrence data needed by
`ArisingCore`; `S2InputData.toArisingCore` and `S2SourceFrontier.realizedInput` construct the
literal `RealizedInput`, selecting CC-9's `legalPoint` from the carried `point_exists`.

No declaration below assumes a cite.  In particular, CC-14/15 are packaging theorems from an
`FGMNSourceLaws` argument and do not construct that source law package.  The cite ledger for
this unit is therefore empty.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C130s17

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6

universe uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- Short name for the literal depth-two S2 tower fixed by design §6. -/
abbrev S2DepthTwo := s2DepthTwo h2 hq

/-! ## The fully concrete repository side -/

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

/-! ## Exact source frontier for a full S2 `ChainRealization` -/

/-- The exact source-side frontier left after the concrete repository assembly.

The three table equalities prevent a future source instance from bypassing CC-6 with freely
chosen level-two tables.  All remaining fields are literal fields of `ChainRealization`.
Thus `toChainRealization` below is record packaging, while constructing an inhabitant of
this structure is precisely the missing source-mathematics task. -/
structure S2SourceFrontier (L : Type uL) [Field L]
    [Algebra ((S2DepthTwo h2 hq).fld 2) L] where
  node : NodePointSource (L := L) (S2DepthTwo h2 hq)
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

variable {L : Type uL} [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- A source-frontier witness packages into the literal full S2 `ChainRealization`.
This is conditional, not an unconditional inhabitant claim. -/
noncomputable def toChainRealization (S : S2SourceFrontier h2 hq L) :
    ChainRealization (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2) L 2 1 5 where
  receiver := (s2RepositoryRealization h2 hq).receiver
  keys := (s2RepositoryRealization h2 hq).keys
  normalizer := (s2RepositoryRealization h2 hq).normalizer
  node := S.node
  fgmn := S.fgmn
  fgmnLaws := S.fgmnLaws
  grade_compat := S.grade_compat
  letter_compat := S.letter_compat

/-- The first calculus would be non-vacuous exactly when the missing source frontier is
inhabited.  No class instance is registered. -/
theorem calculusNonempty (S : S2SourceFrontier h2 hq L) :
    Nonempty (FGMNCalculus (S2DepthTwo h2 hq) 2 1 5) :=
  chainRealization_calculus_nonempty S.toChainRealization

/-- The canonical legal S2 level-two point, conditional only on the source P-locus carried
by `node.point_exists`. -/
noncomputable def point (S : S2SourceFrontier h2 hq L) : S.node.Point :=
  S.node.legalPoint 2 (show StageLive 2 2 from ⟨by decide, by decide⟩)

theorem point_mem (S : S2SourceFrontier h2 hq L) : S.node.Pt 2 S.point :=
  S.node.legalPoint_mem 2 (show StageLive 2 2 from ⟨by decide, by decide⟩)

/-- The inherited integer threshold at the S2 occurrence; no numeral is substituted. -/
def thresholdZ (S : S2SourceFrontier h2 hq L) : ℤ := S.node.thresholdZ 2

/-- The repository's natural-valued avatar of the inherited threshold. -/
def thresholdNat (S : S2SourceFrontier h2 hq L) : ℕ := S.node.thresholdNat 2

/-- The canonical ambient read at the S2 occurrence, still deliberately distinct from
`arenaRead`. -/
def canonicalRead (S : S2SourceFrontier h2 hq L) := S.node.canonicalRead 2

/-- The separate terminal-field arena read at the S2 occurrence. -/
def arenaRead (S : S2SourceFrontier h2 hq L) := S.node.arenaRead 2

/-- The terminal-field lattice read at the S2 occurrence. -/
def towerRead (S : S2SourceFrontier h2 hq L) := S.node.towerRead 2

/-- The S2 peel unit. -/
def peelUnit (S : S2SourceFrontier h2 hq L) := S.node.peelUnit 2

/-- CC-6's concrete level-two carrier and the carrier derived from this future node source
have exactly the same repository degree data and the same three source tables. -/
theorem stageTwo_view (S : S2SourceFrontier h2 hq L) :
    let C := S.node.stageCarrier 2 (show StageLive 2 2 from ⟨by decide, by decide⟩)
    C.D = (s2RepositoryRealization h2 hq).stageTwo.D ∧
      C.eC = (s2RepositoryRealization h2 hq).stageTwo.eC ∧
      C.fC = (s2RepositoryRealization h2 hq).stageTwo.fC ∧
      C.hgt = (s2RepositoryRealization h2 hq).stageTwo.hgt ∧
      C.dig = (s2RepositoryRealization h2 hq).stageTwo.dig ∧
      C.Full = (s2RepositoryRealization h2 hq).stageTwo.Full :=
  ⟨rfl, rfl, rfl, S.hgt_two, S.dig_two, S.full_two⟩

end S2SourceFrontier

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

variable {L : Type uL} [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- Given the two explicit source frontiers, construct the literal S2 `RealizedInput`.
The selected point is CC-9's `legalPoint`, hence comes from the carried `point_exists`. -/
noncomputable def realizedInput (S : S2SourceFrontier h2 hq L)
    (I : S2InputData h2 hq L) :
    RealizedInput I.toArisingCore S.toChainRealization where
  receiver_eq := rfl
  stageKey_eq := rfl
  stageDeg_eq := rfl
  point := S.point
  point_mem := S.point_mem

/-- The maximal conditional acceptance-gate input: the arising occurrence is now the
concrete `keyAt 2 + 1` occurrence; only the separately exposed source frontier remains. -/
noncomputable def s2RealizedInput
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq L) :
    RealizedInput (s2ArisingCore h2 hq L) S.toChainRealization :=
  realizedInput h2 hq S (s2InputData h2 hq L)

end S2SourceFrontier

end Uniformity.Density.Tower.C130s17

/-! ## Axiom footprint and cite ledger

CITES CONSUMED BY THIS FILE: **none**.  All declarations below use Lean/mathlib theorems and
landed Lean-core CC constructors.  In particular `fgmn_dv_exact_mul` is not used.
-/

section AxCheck

#print axioms Uniformity.Density.Tower.C130s17.s2TerminalReceiver
#print axioms Uniformity.Density.Tower.C130s17.S2DepthTwo
#print axioms Uniformity.Density.Tower.C130s17.S2RepositoryRealization
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_receiver
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_keys
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_normalizer
#print axioms Uniformity.Density.Tower.C130s17.s2RepositoryRealization_stageTwo
#print axioms Uniformity.Density.Tower.C130s17.S2SourceFrontier
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
