/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C87
import Uniformity.ChapC.C130k
import Uniformity.ChapE.E10

/-!
# Uniformity.ChapC.C130st — indexed stage source → `SlotCarrier` (chain-carrier node CC-5)

**Chain-carrier node CC-5** (`CHAIN_CARRIER_DESIGN_2026-08-24.md` §4.2, §8 row C.130c, §10):
the indexed stage value/digit/full/lift SOURCE interface, exported at freeze-v2's layer-C.130c
names from the landed `NodePointSource` (C130k, node CC-1), and **the theorem producing the
landed E.10 `Ladder.SlotCarrier` from an instance** at every live stage — `stageCarrier`.

## What this cures (the C.130c blocker, verdict C130A)

C130A found that E.10's carrier at a live stage is NOT derivable from C.83's `(e,f,u,ψ)`
telescope: the stage valuation/read, digits, and the EFF.T2.04/.05/.09 `Full`/lift laws are
extra mathematical structure.  The design's answer (§9) is that they are SOURCE OBLIGATIONS,
carried as fields of `NodePointSource` and tied to legal node points by `pointHgt_eval` +
`slot_value`/`slot_digit` so the tables are not freely chosen.  This file goes in the one
honest direction: it CONSUMES those source fields and DERIVES the consumer's `SlotCarrier`
("C.130c derives `Ladder.SlotCarrier` from these fields" — design §4.2).  No field of any
carrier is introduced here; every new declaration is a definition from, or a theorem about,
already-landed structures.

## The indexed stage interface (per-name EFF rows)

* `stageHgt`  — `EFF.T2.05`'s `h(A)` at stage `i` (with `h(0) = +∞`), whose valuation laws
  (`EFF.T2.04`, r12's disclosure: ultrametric inequality, equality off ties) are the
  `hgt_add_ge`/`hgt_add_eq` source fields;
* `stageDig`  — `EFF.T2.05`'s `dig(A) ∈ K^×` at stage `i` (with `dig(0) = 0`), nonvanishing on
  nonzero slot-range polynomials; shared-height additivity is `EFF.HE7.96`(c)'s mechanism;
* `StageFull` — `EFF.T2.09`'s full-height predicate at stage `i` (`(OCC)`'s finite-domain
  obligation stays with instances);
* `stageLift` — `EFF.T2.09`'s `(LIFT)`: at a full height every nonzero digit is realised by a
  slot-range integral polynomial.  Lifts exist AT FULL HEIGHTS ONLY; no all-height lift is
  stated or stateable here (the structural sub-threshold refusal, as at E.10).

## The producing theorem, and the `(DEG-EF)` bookkeeping

`stageCarrier S i hi : Ladder.SlotCarrier O (W.fld i)` packages the stage-`i` source family as
E.10's carrier.  Its `(DEG-EF)` constants are CHOSEN as the cumulative tower data
`eC := ê_i = e_1⋯e_i` (C.83's `ehat`) and `fC := f̂_i = f_1⋯f_i` (`fhat`, new here), so
`hef : D_i = ê_i·f̂_i` is the PROVED tower identity `Dcum_eq_ehat_mul_fhat` — pure
`Finset.prod_mul_distrib` bookkeeping over C.83's per-stage data.  This manufactures no source
hypothesis: each `(e_j, f_j)` remains a C.83 HYPOTHESIS field of `W`, exactly as `EFF.T2.04`
prescribes (`(DEG-EF)` "explicitly not inferred from monicity" — and it is not: it is inferred
from the tower's assumed stage constants).  Positivity (`hD`/`heC`/`hfC`) is `W.he`/`W.hf` on
the live range (`ehat_pos` from C.87; `fhat_pos`/`Dcum_pos` new here).

## Non-vacuity (the "free tables" trap, closed)

* The anti-drift pins `stageCarrier_D/eC/fC/hgt/dig/Full` are all `rfl`: the produced carrier's
  tables ARE the source fields — in particular `Full` is live and source-bound, NOT `True`
  (design §8 row C.130c's explicit demand).
* `stageCarrier_hgt_eq_point_read` / `stageCarrier_dig_eq_point_read`: on slot range the
  produced carrier's reads agree with the ACTUAL polynomial evaluation at EVERY legal node
  point (`pointHgt_eval` + `slot_value`/`slot_digit`) — the tie C130A found missing from any
  bare-`DeepTower` derivation.

## Deliberately NOT here (later CC nodes)

The threshold dictionary and `CanonicalThresholdAt` (CC-7); the S2 level-2 instantiation of
the stage-source fields (CC-6); `RealizedInput`/`inputBlock` (CC-8); the FGMN source carrier
(CC-13); every socket application (CC-18).  Nothing here inhabits `NodePointSource` — the
producing theorem is a derivation FROM an instance, never a claim that an instance exists.

DEPENDS: C130k (CC-1 skeleton: `NodePointSource`, `KeyChain`, live ranges), C87 (`ehat_pos`),
C83 (`DeepTower`, `ehat`, `Dcum`), E10 (`Ladder.SlotCarrier`).

## Status

Sorry-free, axiom-free (Lean core only); no new structure, no new axiom, no `unsafe`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

/-! ## The `(DEG-EF)` cumulative bookkeeping on C.83's tower

`fhat` is `ehat`'s residual companion; the three lemmas are the arithmetic the stage carrier's
`(DEG-EF)` fields ride on.  All four live in the `DeepTower` namespace (C.87's pattern). -/

namespace DeepTower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- `f̂_i = f_1⋯f_i` — the cumulative residual degree, `ehat`'s companion (C.83 defines
`ehat` and `Dcum`; the `(DEG-EF)` split of `Dcum` needs the third product). -/
def fhat (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 i, T.f j

/-- `f̂_i > 0` on the live range: every factor is positive by `W.hf` (mirror of C.87's
`ehat_pos`). -/
theorem fhat_pos (W : DeepTower F H₀ hpin r) {i : ℕ} (hir : i ≤ r) : 0 < W.fhat i := by
  rw [DeepTower.fhat]
  refine Finset.prod_pos fun t ht => ?_
  rw [Finset.mem_Icc] at ht
  exact W.hf t ht.1 (ht.2.trans hir)

/-- `(DEG-EF)` at cumulative stage data (`EFF.T2.04`, instantiated by the tower's per-stage
constants): `D_i = ê_i · f̂_i`.  Pure product bookkeeping — the `(e_j, f_j)` themselves stay
C.83 hypothesis fields. -/
theorem Dcum_eq_ehat_mul_fhat (W : DeepTower F H₀ hpin r) (i : ℕ) :
    W.Dcum i = W.ehat i * W.fhat i := by
  rw [DeepTower.Dcum, DeepTower.ehat, DeepTower.fhat, Finset.prod_mul_distrib]

/-- `D_i > 0` on the live range. -/
theorem Dcum_pos (W : DeepTower F H₀ hpin r) {i : ℕ} (hir : i ≤ r) : 0 < W.Dcum i := by
  rw [W.Dcum_eq_ehat_mul_fhat i]
  exact Nat.mul_pos (W.ehat_pos hir) (W.fhat_pos hir)

end DeepTower

/-! ## The indexed stage source interface, at freeze-v2's layer-C.130c names -/

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

namespace NodePointSource

/-- Freeze-v2 layer C.130c, the stage VALUE read: `EFF.T2.05`'s `h(A)` at stage `i`
(`h(0) = +∞`; `EFF.T2.04`'s valuation laws are the `hgt_add_ge`/`hgt_add_eq` source fields
of `NodePointSource`). -/
def stageHgt (S : NodePointSource (L := L) W receiver K) (i : ℕ) :
    Polynomial O → WithTop ℤ := S.hgt i

/-- Freeze-v2 layer C.130c, the stage DIGIT read: `EFF.T2.05`'s `dig(A) ∈ K^×` at stage `i`
(`dig(0) = 0`; nonvanishing on nonzero slot-range polynomials is the `dig_ne_zero` source
field). -/
def stageDig (S : NodePointSource (L := L) W receiver K) (i : ℕ) :
    Polynomial O → W.fld i := S.dig i

/-- Freeze-v2 layer C.130c, the stage FULL predicate: `EFF.T2.09`'s full heights at stage `i`
(`(OCC)`'s finite-domain obligation stays with instances, exactly as at E.10). -/
def StageFull (S : NodePointSource (L := L) W receiver K) (i : ℕ) : ℤ → Prop := S.Full i

/-- Freeze-v2 layer C.130c, the stage LIFT law (`EFF.T2.09` `(LIFT)`): at a full height of a
live stage, every nonzero digit is realised by a nonzero slot-range integral polynomial.
Restated on the layer's names; the content is `NodePointSource`'s `lift` source field —
lifts exist AT FULL HEIGHTS ONLY. -/
theorem stageLift (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) (k : ℤ) (hk : S.StageFull i k) (c : W.fld i) (hc : c ≠ 0) :
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < W.Dcum i ∧
      S.stageHgt i A = (k : WithTop ℤ) ∧ S.stageDig i A = c :=
  S.lift i hi k hk c hc

/-! ## The producing theorem (CC-5's exit condition) -/

/-- ★ **CC-5, the producing theorem — freeze-v2 layer C.130c's `stageCarrier`**: every live
stage of a `NodePointSource` yields the landed E.10 `Ladder.SlotCarrier` over the stage
residue field `W.fld i`.

Field provenance: `D` is C.83's cumulative `Dcum i` (= C130b's `stageDeg`); the `(DEG-EF)`
constants are the cumulative `ê_i`/`f̂_i` with `hef` the PROVED tower identity
`Dcum_eq_ehat_mul_fhat` (`EFF.T2.04`); positivity is `W.he`/`W.hf` through
`ehat_pos`/`fhat_pos`/`Dcum_pos`; `hgt`/`dig`/`Full` and every law field are the
`EFF.T2.04/.05/.09` SOURCE fields of `S` at stage `i`, consumed verbatim — see the anti-drift
pins below.  In particular `Full` is `S.Full i`: live and source-bound, not `True`. -/
def stageCarrier (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : Ladder.SlotCarrier O (W.fld i) where
  D := W.Dcum i
  hD := W.Dcum_pos hi.2
  eC := W.ehat i
  fC := W.fhat i
  hef := W.Dcum_eq_ehat_mul_fhat i
  heC := W.ehat_pos hi.2
  hfC := W.fhat_pos hi.2
  hgt := S.stageHgt i
  dig := S.stageDig i
  hgt_zero := S.hgt_zero i hi
  dig_zero := S.dig_zero i hi
  hgt_ne_top := S.hgt_ne_top i hi
  dig_ne_zero := S.dig_ne_zero i hi
  hgt_add_ge := S.hgt_add_ge i hi
  hgt_add_eq := S.hgt_add_eq i hi
  dig_add := S.dig_add i hi
  Full := S.StageFull i
  hlift := S.lift i hi

/-! ## Anti-drift pins (all `rfl`): the produced carrier consumes the SOURCE, verbatim -/

/-- Pin: the produced carrier's degree is C.83's cumulative stage degree. -/
theorem stageCarrier_D (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : (S.stageCarrier i hi).D = W.Dcum i := rfl

/-- Pin: the produced carrier's `(DEG-EF)` ramification constant is the cumulative `ê_i`. -/
theorem stageCarrier_eC (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : (S.stageCarrier i hi).eC = W.ehat i := rfl

/-- Pin: the produced carrier's `(DEG-EF)` residual constant is the cumulative `f̂_i`. -/
theorem stageCarrier_fC (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : (S.stageCarrier i hi).fC = W.fhat i := rfl

/-- Pin: the produced carrier's height table IS the stage-`i` source table (no fresh table). -/
theorem stageCarrier_hgt (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : (S.stageCarrier i hi).hgt = S.hgt i := rfl

/-- Pin: the produced carrier's digit table IS the stage-`i` source table (no fresh table). -/
theorem stageCarrier_dig (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : (S.stageCarrier i hi).dig = S.dig i := rfl

/-- Pin: the produced carrier's `Full` IS the stage-`i` source predicate — live and
source-bound, NOT `True` (design §8, row C.130c). -/
theorem stageCarrier_Full (S : NodePointSource (L := L) W receiver K) (i : ℕ)
    (hi : StageLive r i) : (S.stageCarrier i hi).Full = S.Full i := rfl

/-! ## The legal-point tie: the produced tables are point evaluations on slot range -/

/-- Non-vacuity tie for the VALUE read (`EFF.T2.05` `(SLOT-V)` through the carrier): on slot
range, the produced carrier's height IS the stage valuation of the actual polynomial
evaluation at EVERY legal node point.  `slot_value` + `pointHgt_eval`, chained. -/
theorem stageCarrier_hgt_eq_point_read (S : NodePointSource (L := L) W receiver K)
    (i : ℕ) (hi : StageLive r i) (x : S.Point) (hx : S.Pt i x)
    (A : Polynomial O) (hA : A ≠ 0) (hdeg : A.natDegree < W.Dcum i) :
    (S.stageCarrier i hi).hgt A
      = S.valueOn i (Polynomial.eval₂ S.coeffHom (S.coord x) A) :=
  (S.slot_value i hi x hx A hA hdeg).symm.trans (S.pointHgt_eval i x A)

/-- Non-vacuity tie for the DIGIT read (`EFF.T2.05` `(SLOT-R)` through the carrier): on slot
range, the produced carrier's digit IS the pointwise digit read at EVERY legal node point. -/
theorem stageCarrier_dig_eq_point_read (S : NodePointSource (L := L) W receiver K)
    (i : ℕ) (hi : StageLive r i) (x : S.Point) (hx : S.Pt i x)
    (A : Polynomial O) (hA : A ≠ 0) (hdeg : A.natDegree < W.Dcum i) :
    (S.stageCarrier i hi).dig A = S.pointDig i x A :=
  (S.slot_digit i hi x hx A hA hdeg).symm

end NodePointSource

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DeepTower.fhat
#print axioms Uniformity.Density.Tower.DeepTower.fhat_pos
#print axioms Uniformity.Density.Tower.DeepTower.Dcum_eq_ehat_mul_fhat
#print axioms Uniformity.Density.Tower.DeepTower.Dcum_pos
#print axioms Uniformity.Density.Tower.NodePointSource.stageHgt
#print axioms Uniformity.Density.Tower.NodePointSource.stageDig
#print axioms Uniformity.Density.Tower.NodePointSource.StageFull
#print axioms Uniformity.Density.Tower.NodePointSource.stageLift
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_D
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_eC
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_fC
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_hgt
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_dig
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_Full
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_hgt_eq_point_read
#print axioms Uniformity.Density.Tower.NodePointSource.stageCarrier_dig_eq_point_read

end AxCheck
