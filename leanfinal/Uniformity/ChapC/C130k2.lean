/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130st

/-!
# Uniformity.ChapC.C130k2 — the split-ambient node source at the carrier skeleton (PK-1)

**[PK-1/U15, 2026-08-25]** — packaging-route node PK-1 of
`docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` (§4.1): `SplitNodePointSource` and its three
helpers (`legalPoint`, `legalPoint_mem`, `stageCarrier`) MOVE VERBATIM from `C130s17.lean`
(where unit SF1 landed them on 2026-08-24, after U13 machine-refuted the un-split typing) to
this new carrier-skeleton file, so that the retyped CC-13 carrier (`ChainRealization`,
`C130fg`) can take the split node as its `node` leg.  `C130s17` keeps a compatibility
re-export.  This file lives in a NEW module (rather than `C130k`) to avoid touching the
landed CC-1 content; the un-split `NodePointSource` (C130k) survives untouched as the
QUARANTINE record of the U13 refutation.

Every declaration below is byte-for-byte the SF1 text from `C130s17.lean` (docstrings
included); nothing is added, weakened, or restated.  The elaboration authority for the
consuming retype is `leanfinal/scratch/U15_check.lean`.

DEPENDS: C130st (CC-5: `DeepTower.fhat`/`Dcum_eq_ehat_mul_fhat`/`Dcum_pos`, E.10's
`Ladder.SlotCarrier` transitively), C130k via C130st (CC-1 skeleton: `KeyChain`,
`TerminalReceiver`, live ranges), C83 (`DeepTower`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no `True`-bodied field;
no instance of any carrier is declared.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uE uKt uL

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
carried.  All non-evaluation fields are byte-parallel to C130k's `NodePointSource`.

[PK-1/U15, 2026-08-25]: moved verbatim from `C130s17` to the carrier skeleton — the SF-3
consumer ripple anticipated by SF1's landing note is enacted by the packaging route. -/
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

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.SplitNodePointSource
#print axioms Uniformity.Density.Tower.SplitNodePointSource.legalPoint
#print axioms Uniformity.Density.Tower.SplitNodePointSource.legalPoint_mem
#print axioms Uniformity.Density.Tower.SplitNodePointSource.stageCarrier

end AxCheck
