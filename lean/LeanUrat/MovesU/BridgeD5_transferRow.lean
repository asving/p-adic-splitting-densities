/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.ReadLocality
import LeanUrat.MovesT.TV_B8
import LeanUrat.MovesU.BridgeD1_treeModelWire
import LeanUrat.MovesU.BridgeD2_chartSemantics

/-!
# IB-D5 — `TransferRow n p` (bridge campaign BP1, cluster c7; ADJ / statement fence)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†6) /
§4 group D (IB-D5) / §3.7.  Deps: IB-D1 (`bridgeTm`), IB-D2 (`bridgeChart`).
STATEMENT-ONLY unit: the structure IS the deliverable — a NEW NAMED KERNEL ROW
(statement-fence event, flagged for orchestrator ratification per the
blueprint's ADJ marking; it enters `BridgeKernels` as the `transfer` row).

THE ROW (†6) — the ONE stability kernel of the D-group, consumed four times:
`vt_real` (IB-D15), `vt_surj` (IB-D16), `canonical_stable` (IB-D8), and the
`treeOf` coherence.  Two faces:
* `realizes_transfer` — TREE-N's decision/realization stability across levels:
  a tree realized at one level ≥ its threshold is realized at EVERY level ≥
  its threshold.  This is the note's Thm 2.1 face (TREE-N); the Lean-side open
  row `MovesT.treeN_stable` (`MovesT/E11_treeN.lean:90`, a FENCED sorry, named
  open row, owner HC-2/D4R0K) is its fenced SIBLING — cited here, NOT consumed
  (the fence: no sorried declaration flows into bridge statements).
* `fiber_transfer` — the FIBER-side face `canonical_stable` needs: a box class
  whose level-N reduction fibers at V (through the digit dictionary) fibers at
  V at level N' ≥ N.
OWNER: HC-2/D4R0K + TREE-N (per the blueprint's row table).

TRANSCRIPTION RESOLUTIONS (recorded):
* The blueprint heads the row "`TransferRow n p`", but `fiber_transfer`'s
  display mentions the box dictionary `boxeq` — whose concrete instance
  `boxEquivD` is IB-A11's deliverable (another cluster; not yet on disk).  The
  structure is therefore PARAMETRIC in the boxeq family (the BridgeD2
  precedent for exactly this dependency); IB-F2 instantiates it at IB-A11's
  `boxEquivD` when wiring `BridgeKernels.transfer`.  A boxeq FIELD was
  rejected: the row must not pick its own dictionary (it would un-pin (†3)).
* `fiber_transfer` carries the same `0 < N` / `0 < N'` guards as
  `realizes_transfer` (the guarded-chart discipline) plus the transfer
  direction `N ≤ N'` (the `boxProj` direction of (†6)'s display) and the
  threshold guard `V.thr n ≤ N` (whence thr ≤ N' — the consumers always hold
  it; a guard-free row would be strictly stronger than the note's Thm 2.1
  face).  (†3c)'s boxProj-compat (IB-A12) is thereby part of the ROW's
  eventual discharge, not of its consumers' statements.

SYN-C2 RECORD (2026-07-30, C2/N2 ratification,
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "SYNTHESIS PASS 1
ADJUDICATIONS": "ONE ReadLocality kernel row … TransferRow … and StableInputs
… become derived lemmas"): `TransferRow` is DEMOTED from kernel row to
DERIVED surface.  THE kernel is `MovesT.ReadLocality`
(MovesT/ReadLocality.lean, owner HC-2/D4R0K), instantiated at the bridge as
`BridgeReadLocality` below; `transferRow_of_readLocality` DERIVES this file's
structure from it (derivation body = prover-phase: the TV-B3..B6-genre
mem/child/redPoly composition run at the dressed tower + IB-A12's boxProj
digit-truncation compat through `hdig`).  The structure itself is
byte-identical (IB-D8's binder and `BridgeKernelsCtor.transfer` consume it
unchanged); what changed is its STATUS in the honesty ledger — the wiring
supplies the `transfer` field through the derivation, and the ledger names
ReadLocality once.

SYN-C2 TRANSCRIPTION RESOLUTION — THE LAYOUT DRESSING (recorded; the C2
spec's silent seam, resolved here): `ReadLocality` is stated at MovesT's
STANDARD level-blocked box labeling ("coordinate c at level ⌊c/n⌋ + 1"; the
level-<N block = the FIRST n·N coordinates — `TreeNStable`'s pinned
convention), while the bridge's (†3) labeling is coefficient-blocked (slot
i·N + k = digit k of coefficient i, `digitIdx`).  The RAW bridge pair
provably VIOLATES the row's `chart_pin` (`bridgeChart n N' hN' b = b·N' ≥ n`
for 1 ≤ b, n ≤ N'), so instantiating the row at (bridgeTm, bridgeChart)
verbatim would carry a REFUTABLE hypothesis (the M1 soundness lesson).  The
row therefore instantiates at the BLOCK-INTERLEAVE DRESSING:
`bridgeTmStd` = `bridgeTm` reading its boxes through
`MovesT.blockInterleave` (bridge slot i·N + k ↦ standard slot k·n + i), and
`bridgeChartStd` = the dressed chart (= slot b, the level-0 block —
`chart_pin` HOLDS by `b.isLt`).  Compiled coherence gates:
`blockInterleave_bridgeChart` (the dressed chart IS the dressing-image of the
pinned digit-0 chart — PROVED) and `bridgeChartStd_pin` (chart_pin's
non-vacuity at the instance — PROVED).  The N3 probe / HC-2 discharge target
is `BridgeReadLocality` (one object, one discharge).

CROSS-RECORDS (concurrent-fleet reconciliation, 2026-07-30):
* `BridgeN3b_readLocality.lean` (the executed N3 probe) COMPILED both halves
  of this seam independently — LEG 3's
  `bridgeChart_levelMajor_chart_pin_false` is exactly the "raw pair violates
  chart_pin" fact above, and its verdict "SYN-C2 must re-key the chart face"
  is EXECUTED here by re-keying the INSTANTIATION (the dressing), not the
  row's statement: the abstract row keeps TV-B2's level-major `< n` form
  because `TreeNStable`/`StableInputs` (ratified/byte-frozen MovesT
  statements) are level-major — a layout-free or digitIdx-keyed row could not
  derive them.  LEG 2's interface countermodel
  (`child_locality_not_interface_derivable`) negates only the
  interface-GENERIC universal; `transferRow_of_readLocality` below is
  CONDITIONAL on `BridgeReadLocality`, so no compiled negation coexists with
  it (the M1 coexistence rule, checked).
* IB-D28/Q10 (the designer-round layout-adjudication memo, BP1 addendum
  D-TM): `MovesT.blockInterleave` + the gates here ARE that memo's
  deliverable option (ii) — "the reconciliation permutation of Fin (n·N) as a
  typed statement".  The designer wire (IB-D27, `bridgeTm :=
  canTreeModelN …`) passes through `bridgeTmStd` unchanged (the dressing is
  parametric in `bridgeTm`), and the N3 discharge path (prove
  `BridgeReadLocality` FROM the (†13)/(†14) construction) fires at this one
  object.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†6) THE TRANSFER ROW — the one stability kernel (TREE-N / Thm 2.1 face;
    fenced Lean sibling `MovesT.treeN_stable`, cited NOT consumed — header).
    NEW NAMED ROW (statement fence: flagged for ratification); enters
    `BridgeKernels` as the `transfer` row, parametric in the (†3) box
    dictionary (header resolution).
    * `realizes_transfer`: realization of V transfers between any two levels
      ≥ V's threshold (both guarded positive).
    * `fiber_transfer`: fibering of the level-N REDUCTION of a level-N' box
      class (read through the dictionary) transfers UP to level N', for
      N ≤ N' within V's threshold range. -/
structure TransferRow (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N)) : Prop where
  realizes_transfer : ∀ (V : MovesT.VTree p (ZMod p)) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N'), V.thr n ≤ N → V.thr n ≤ N' →
    MovesT.Realizes (bridgeTm p n N) (bridgeChart n N hN) V →
    MovesT.Realizes (bridgeTm p n N') (bridgeChart n N' hN') V
  fiber_transfer : ∀ (V : MovesT.VTree p (ZMod p)) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (hNN' : N ≤ N') (f : Box p n N'),
    V.thr n ≤ N →
    V.fiberAt (bridgeTm p n N) (bridgeChart n N hN)
      (boxeq N (boxProj p n hNN' f)) →
    V.fiberAt (bridgeTm p n N') (bridgeChart n N' hN') (boxeq N' f)

/-! ## SYN-C2 — the dressed bridge tower + THE derivation
(header, SYN-C2 records; kernel: `MovesT.ReadLocality`) -/

/-- SYN-C2: the STANDARD-DRESSED bridge model — `bridgeTm` reading its boxes
    through the (†3)→standard block-interleave relabeling
    (`MovesT.blockInterleave`; header dressing record).  The abstract tower
    `ReadLocality`/`TreeNStable` speak about THIS model; the raw `bridgeTm`
    reads are recovered definitionally (`MovesT.reindexModel_child`/`_mem`). -/
noncomputable def bridgeTmStd (p : ℕ) [Fact p.Prime] (n N : ℕ) :
    MovesD.TreeModel p (ZMod p) n N (n * N) (bridgePol p) :=
  MovesT.reindexModel (bridgeTm p n N) (MovesT.blockInterleave n N)

/-- SYN-C2: the STANDARD-DRESSED chart — coefficient b's level-0 digit sits at
    standard slot b (the level-0 block IS the first n coordinates). -/
def bridgeChartStd (n N : ℕ) (hN : 0 < N) : Fin n → Fin (n * N) :=
  fun b => Fin.castLE (le_mul_of_one_le_right (Nat.zero_le n) hN) b

/-- SYN-C2 compiled gate: `chart_pin`'s non-vacuity at the dressed instance —
    the dressed chart lands in the level-1 block (contrast: the RAW
    `bridgeChart` provably violates this, header dressing record). -/
theorem bridgeChartStd_pin (n N : ℕ) (hN : 0 < N) (b : Fin n) :
    ((bridgeChartStd n N hN b : ℕ)) < n := b.isLt

/-- SYN-C2 compiled gate (dressing faithfulness): the dressed chart IS the
    block-interleave image of the pinned digit-0 chart `bridgeChart` — slot
    b·N + 0 (digit 0 of coefficient b, (†3)) relabels to standard slot b. -/
theorem blockInterleave_bridgeChart (n N : ℕ) (hN : 0 < N) (b : Fin n) :
    MovesT.blockInterleave n N (bridgeChart n N hN b)
      = bridgeChartStd n N hN b := by
  apply Fin.ext
  rw [MovesT.blockInterleave_val]
  have hval : ((bridgeChart n N hN b : ℕ)) = (b : ℕ) * N := rfl
  rw [hval, Nat.mul_mod_left, Nat.mul_div_cancel _ hN]
  simp [bridgeChartStd]

/-- SYN-C2: THE ONE KERNEL ROW AT THE BRIDGE — `MovesT.ReadLocality`
    instantiated at the dressed tower (N₀ = 1, `bridgeTmStd`,
    `bridgeChartStd`), ∀-closed over the tree.  This is the single named
    hypothesis surface the honesty ledger carries for the (†6)/TREE-N/Thm-2.1
    content; owner HC-2/D4R0K; discharge/N3-probe target (one object). -/
def BridgeReadLocality (n p : ℕ) [Fact p.Prime] : Prop :=
  ∀ V : MovesT.VTree p (ZMod p),
    MovesT.ReadLocality (N₀ := 1)
      (fun N' (_ : 1 ≤ N') => bridgeTmStd p n N')
      (fun N' (h : 1 ≤ N') => bridgeChartStd n N' h) V

/-! ## SYN-C2 prover-phase helpers (private) — the TV-B3..B6 chain, CROSS-LEVEL

The TV-B3/B5/B6 units (MovesT/TV_B3.lean etc.) prove the transfer chain at ONE
model (two boxes, one level).  The (†6) row transfers across LEVELS, so the
same mem/child/redPoly composition is re-run here at TWO models over the same
tree degree n — private helpers only; the fenced public units are untouched. -/

section CrossLevelHelpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : MovesD.CanonPolicy p F}

/-- the E5/TV-B3 `mem_oneNode_iff` twin (private there; re-derived here). -/
private lemma memOneNodeIff {N m : ℕ} (T : MovesD.TreeModel p F n N m pol)
    (ν : MovesC.Node p F) (h : MovesT.ChildRoot none ν) (x : MovesD.Box p m) :
    T.mem (some (MovesT.oneNode ν h)) x ↔ T.child none ν x := by
  have h1 : (([ν] : List (MovesC.Node p F)) ≠ [] ∧
      ∀ (j : ℕ) (hj : j < ([ν] : List (MovesC.Node p F)).length),
        ((([ν] : List (MovesC.Node p F))[j]'hj).species
          = MovesC.ReadSpecies.root ↔ j = 0)) := by
    refine ⟨by simp, ?_⟩
    intro j hj
    have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hj)
    subst hj0
    simpa using (show ν.species = MovesC.ReadSpecies.root from h)
  exact T.mem_single ν h1 x

/-- TV-B3's core run cross-level: mem is child-GENERATED (`mem_single`/
`mem_snoc`), so a pointwise child transfer between two models/boxes transfers
mem at every history (TV-B8 snoc induction). -/
private lemma memCross {N₁ m₁ N₂ m₂ : ℕ}
    (T₁ : MovesD.TreeModel p F n N₁ m₁ pol) (T₂ : MovesD.TreeModel p F n N₂ m₂ pol)
    (x₁ : MovesD.Box p m₁) (x₂ : MovesD.Box p m₂)
    (hchild : ∀ (o : Option (MovesC.History p F)) (ν : MovesC.Node p F),
      T₁.child o ν x₁ ↔ T₂.child o ν x₂) :
    ∀ H : MovesC.History p F, T₁.mem (some H) x₁ ↔ T₂.mem (some H) x₂ := by
  intro H
  induction H using MovesC.History.snoc_induction with
  | hone ν h =>
    exact (memOneNodeIff T₁ ν h x₁).trans
      ((hchild none ν).trans (memOneNodeIff T₂ ν h x₂).symm)
  | hsnoc H₀ ν hν ih =>
    rw [T₁.mem_snoc H₀ ν hν x₁, T₂.mem_snoc H₀ ν hν x₂]
    exact and_congr ih (hchild (some H₀) ν)

/-- TV-B5's NsHalts transfer, cross-level (NsHalts is mem/child-composed). -/
private lemma nsHaltsCross {N₁ m₁ N₂ m₂ : ℕ}
    (T₁ : MovesD.TreeModel p F n N₁ m₁ pol) (T₂ : MovesD.TreeModel p F n N₂ m₂ pol)
    (x₁ : MovesD.Box p m₁) (x₂ : MovesD.Box p m₂)
    (hchild : ∀ (o : Option (MovesC.History p F)) (ν : MovesC.Node p F),
      T₁.child o ν x₁ ↔ T₂.child o ν x₂)
    (hmem : ∀ H : MovesC.History p F, T₁.mem (some H) x₁ ↔ T₂.mem (some H) x₂)
    (o : Option (MovesC.History p F)) :
    MovesT.NsHalts T₁ o x₁ ↔ MovesT.NsHalts T₂ o x₂ := by
  unfold MovesT.NsHalts
  cases o with
  | none =>
    exact and_congr (iff_of_true (T₁.root_mem x₁) (T₂.root_mem x₂))
      (forall_congr' fun ν => not_congr (hchild none ν))
  | some H =>
    exact and_congr (hmem H)
      (forall_congr' fun ν => not_congr (hchild (some H) ν))

/-- TV-B5's PrunedMem transfer, cross-level (IrrHalts x-free). -/
private lemma prunedMemCross {N₁ m₁ N₂ m₂ : ℕ}
    (T₁ : MovesD.TreeModel p F n N₁ m₁ pol) (T₂ : MovesD.TreeModel p F n N₂ m₂ pol)
    (x₁ : MovesD.Box p m₁) (x₂ : MovesD.Box p m₂)
    (hchild : ∀ (o : Option (MovesC.History p F)) (ν : MovesC.Node p F),
      T₁.child o ν x₁ ↔ T₂.child o ν x₂)
    (hmem : ∀ H : MovesC.History p F, T₁.mem (some H) x₁ ↔ T₂.mem (some H) x₂)
    (H : MovesC.History p F) :
    MovesT.PrunedMem T₁ H x₁ ↔ MovesT.PrunedMem T₂ H x₂ := by
  unfold MovesT.PrunedMem
  refine and_congr (hmem H) (forall_congr' fun H' => imp_congr Iff.rfl
    (imp_congr Iff.rfl (imp_congr Iff.rfl (and_congr Iff.rfl
      (not_congr (nsHaltsCross T₁ T₂ x₁ x₂ hchild hmem (some H')))))))

/-- TV-B6's six-clause assembly, cross-level: a pointwise child transfer plus
equal level-0 reductions transfer the whole `fiberAt` between levels. -/
private lemma fiberAtCross {N₁ m₁ N₂ m₂ : ℕ} (V : MovesT.VTree p F)
    (T₁ : MovesD.TreeModel p F n N₁ m₁ pol) (T₂ : MovesD.TreeModel p F n N₂ m₂ pol)
    (χ₁ : Fin n → Fin m₁) (χ₂ : Fin n → Fin m₂)
    (x₁ : MovesD.Box p m₁) (x₂ : MovesD.Box p m₂)
    (hchild : ∀ (o : Option (MovesC.History p F)) (ν : MovesC.Node p F),
      T₁.child o ν x₁ ↔ T₂.child o ν x₂)
    (hred : MovesT.redPoly χ₁ x₁ = MovesT.redPoly χ₂ x₂) :
    V.fiberAt T₁ χ₁ x₁ ↔ V.fiberAt T₂ χ₂ x₂ := by
  have hmem := memCross T₁ T₂ x₁ x₂ hchild
  have hhen : MovesT.henPayload χ₁ x₁ = MovesT.henPayload χ₂ x₂ := by
    unfold MovesT.henPayload MovesT.henDegrees
    rw [hred]
  unfold MovesT.VTree.fiberAt
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr Iff.rfl ?_))))
  · exact forall_congr' fun H => iff_congr Iff.rfl
      (and_congr Iff.rfl (prunedMemCross T₁ T₂ x₁ x₂ hchild hmem H))
  · exact forall_congr' fun H => imp_congr Iff.rfl (imp_congr Iff.rfl
      (or_congr Iff.rfl (and_congr
        (nsHaltsCross T₁ T₂ x₁ x₂ hchild hmem (some H)) Iff.rfl)))
  · rw [hhen]
  · exact forall_congr' fun H => imp_congr Iff.rfl (imp_congr Iff.rfl
      (and_congr Iff.rfl
        (not_congr (nsHaltsCross T₁ T₂ x₁ x₂ hchild hmem (some H)))))
  · rw [hred]

/-- The dressing transport: `fiberAt` at a reindexed model IS `fiberAt` at the
original model with the relabeled box and the pulled-back chart. -/
private lemma fiberAtReindex {N m : ℕ} (V : MovesT.VTree p F)
    (T : MovesD.TreeModel p F n N m pol) (e : Fin m ≃ Fin m)
    (χ : Fin n → Fin m) (y : MovesD.Box p m) :
    V.fiberAt (MovesT.reindexModel T e) χ y
      ↔ V.fiberAt T (fun b => e.symm (χ b)) (fun s => y (e s)) := by
  have hred : MovesT.redPoly (fun b => e.symm (χ b)) (fun s => y (e s))
      = MovesT.redPoly χ y := by
    unfold MovesT.redPoly
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.apply_symm_apply]
  have hhen : MovesT.henPayload (fun b => e.symm (χ b)) (fun s => y (e s))
      = MovesT.henPayload χ y := by
    unfold MovesT.henPayload MovesT.henDegrees
    rw [hred]
  unfold MovesT.VTree.fiberAt
  rw [hred, hhen]
  exact Iff.rfl

end CrossLevelHelpers

section DigitHelpers

/-- base-p digit sums with digits < P stay below P^N. -/
private lemma sumDigitsLt (P : ℕ) (hP : 1 < P) :
    ∀ (N : ℕ) (d : ℕ → ℕ), (∀ k, k < N → d k < P) →
      (∑ j ∈ Finset.range N, d j * P ^ j) < P ^ N := by
  intro N
  induction N with
  | zero => intro d _; simp
  | succ N ih =>
    intro d hd
    rw [Finset.sum_range_succ]
    have h1 : (∑ j ∈ Finset.range N, d j * P ^ j) < P ^ N :=
      ih d fun k hk => hd k (by omega)
    have h2 : d N * P ^ N ≤ (P - 1) * P ^ N :=
      Nat.mul_le_mul_right _ (by have := hd N (by omega); omega)
    have h3 : P ^ N + (P - 1) * P ^ N = P ^ (N + 1) := by
      have hP1 : P - 1 + 1 = P := by omega
      calc P ^ N + (P - 1) * P ^ N = (P - 1 + 1) * P ^ N := by ring
        _ = P * P ^ N := by rw [hP1]
        _ = P ^ (N + 1) := by rw [pow_succ]; ring
    omega

/-- base-P digit UNIQUENESS: two digit strings below P with equal weighted sums
agree (read level by level: mod P kills the tail, then divide). -/
private lemma digitsEqOfSumEq (P : ℕ) (hP : 1 < P) :
    ∀ (N : ℕ) (d d' : ℕ → ℕ), (∀ k, k < N → d k < P) → (∀ k, k < N → d' k < P) →
      (∑ j ∈ Finset.range N, d j * P ^ j) = (∑ j ∈ Finset.range N, d' j * P ^ j) →
      ∀ k, k < N → d k = d' k := by
  intro N
  induction N with
  | zero => intro d d' _ _ _ k hk; omega
  | succ N ih =>
    intro d d' hd hd' hsum k hk
    have hpeel : ∀ e : ℕ → ℕ,
        (∑ j ∈ Finset.range (N + 1), e j * P ^ j)
          = e 0 + P * (∑ j ∈ Finset.range N, e (j + 1) * P ^ j) := by
      intro e
      rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ]
      ring
    rw [hpeel d, hpeel d'] at hsum
    have hd0 : d 0 = d' 0 := by
      have h1 : (d 0 + P * (∑ j ∈ Finset.range N, d (j + 1) * P ^ j)) % P
          = (d' 0 + P * (∑ j ∈ Finset.range N, d' (j + 1) * P ^ j)) % P := by
        rw [hsum]
      rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hd 0 (by omega)), Nat.mod_eq_of_lt (hd' 0 (by omega))] at h1
    have hrest : (∑ j ∈ Finset.range N, d (j + 1) * P ^ j)
        = (∑ j ∈ Finset.range N, d' (j + 1) * P ^ j) := by
      rw [hd0] at hsum
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel hsum)
    cases k with
    | zero => exact hd0
    | succ j =>
      exact ih (fun j => d (j + 1)) (fun j => d' (j + 1))
        (fun j hj => hd (j + 1) (by omega)) (fun j hj => hd' (j + 1) (by omega))
        hrest j (by omega)

/-- (†3b) digit-truncation compat, derived PARAMETRICALLY from the digit law
`hdig` (the IB-A12 `boxEquivD_boxProj` genre, at ANY lawful dictionary): for
k < N ≤ N', digit k of the level-N projection IS digit k of the level-N' box —
both digit strings read the same ℕ below p^N, and base-p digits are unique. -/
private lemma digitCompat {p : ℕ} [Fact p.Prime] {n : ℕ}
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (hdig : ∀ (N : ℕ) (f : Box p n N) (i : Fin n),
      f i = ∑ k : Fin N, ((boxeq N f (digitIdx n N i k)).val : ZMod (p ^ N))
        * (p : ZMod (p ^ N)) ^ (k : ℕ))
    {N N' : ℕ} (hNN' : N ≤ N') (f : Box p n N') (i : Fin n) (k : Fin N) :
    boxeq N (boxProj p n hNN' f) (digitIdx n N i k)
      = boxeq N' f (digitIdx n N' i (Fin.castLE hNN' k)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (by omega)⟩
  set g := boxProj p n hNN' f with hg
  set d' : ℕ → ℕ := fun j =>
    if hj : j < N then (boxeq N g (digitIdx n N i ⟨j, hj⟩)).val else 0 with hd'
  set d : ℕ → ℕ := fun j =>
    if hj : j < N' then (boxeq N' f (digitIdx n N' i ⟨j, hj⟩)).val else 0 with hd
  have hd'eq : ∀ (j : ℕ) (hj : j < N),
      d' j = (boxeq N g (digitIdx n N i ⟨j, hj⟩)).val := by
    intro j hj
    simp only [hd']
    rw [dif_pos hj]
  have hdeq : ∀ (j : ℕ) (hj : j < N'),
      d j = (boxeq N' f (digitIdx n N' i ⟨j, hj⟩)).val := by
    intro j hj
    simp only [hd]
    rw [dif_pos hj]
  have hd'lt : ∀ j, j < N → d' j < p := by
    intro j hj
    rw [hd'eq j hj]
    exact ZMod.val_lt _
  have hdlt : ∀ (j : ℕ), j < N' → d j < p := by
    intro j hj
    rw [hdeq j hj]
    exact ZMod.val_lt _
  -- the level-N reading of g, as the cast of one ℕ
  have hgi : g i = ((∑ j ∈ Finset.range N, d' j * p ^ j : ℕ) : ZMod (p ^ N)) := by
    rw [hdig N g i]
    push_cast
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd'eq (j : ℕ) j.isLt]
  -- the level-N' reading of f, as the cast of one ℕ
  have hfi : f i = ((∑ j ∈ Finset.range N', d j * p ^ j : ℕ) : ZMod (p ^ N')) := by
    rw [hdig N' f i]
    push_cast
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdeq (j : ℕ) j.isLt]
  -- project the level-N' reading down: the ≥ N tail dies mod p^N
  have hsplit : (∑ j ∈ Finset.range N', d j * p ^ j)
      = (∑ j ∈ Finset.range N, d j * p ^ j) + ∑ j ∈ Finset.Ico N N', d j * p ^ j := by
    have h := (Finset.sum_Ico_consecutive (fun j => d j * p ^ j)
      (Nat.zero_le N) hNN').symm
    simpa only [← Finset.range_eq_Ico] using h
  have hdvd : (p ^ N : ℕ) ∣ ∑ j ∈ Finset.Ico N N', d j * p ^ j :=
    Finset.dvd_sum fun j hj =>
      (pow_dvd_pow p (Finset.mem_Ico.mp hj).1).mul_left (d j)
  have hzero : ((∑ j ∈ Finset.Ico N N', d j * p ^ j : ℕ) : ZMod (p ^ N)) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod (p ^ N)) (p ^ N) _).mpr hdvd
  -- both ℕ readings agree in ZMod (p^N)
  have hSS : ((∑ j ∈ Finset.range N, d' j * p ^ j : ℕ) : ZMod (p ^ N))
      = ((∑ j ∈ Finset.range N, d j * p ^ j : ℕ) : ZMod (p ^ N)) := by
    calc ((∑ j ∈ Finset.range N, d' j * p ^ j : ℕ) : ZMod (p ^ N))
        = g i := hgi.symm
      _ = ZMod.castHom (pow_dvd_pow p hNN') (ZMod (p ^ N)) (f i) := rfl
      _ = ZMod.castHom (pow_dvd_pow p hNN') (ZMod (p ^ N))
            ((∑ j ∈ Finset.range N', d j * p ^ j : ℕ) : ZMod (p ^ N')) := by
          rw [← hfi]
      _ = ((∑ j ∈ Finset.range N', d j * p ^ j : ℕ) : ZMod (p ^ N)) :=
          map_natCast _ _
      _ = ((∑ j ∈ Finset.range N, d j * p ^ j : ℕ) : ZMod (p ^ N))
            + ((∑ j ∈ Finset.Ico N N', d j * p ^ j : ℕ) : ZMod (p ^ N)) := by
          rw [hsplit]
          push_cast
          ring
      _ = ((∑ j ∈ Finset.range N, d j * p ^ j : ℕ) : ZMod (p ^ N)) := by
          rw [hzero, add_zero]
  -- lift to ℕ (both sums < p^N), then digits are unique
  have hnat : (∑ j ∈ Finset.range N, d' j * p ^ j)
      = (∑ j ∈ Finset.range N, d j * p ^ j) := by
    have hlt' : (∑ j ∈ Finset.range N, d' j * p ^ j) < p ^ N :=
      sumDigitsLt p hp N d' hd'lt
    have hlt : (∑ j ∈ Finset.range N, d j * p ^ j) < p ^ N :=
      sumDigitsLt p hp N d fun j hj => hdlt j (lt_of_lt_of_le hj hNN')
    have h := congrArg ZMod.val hSS
    rwa [ZMod.val_cast_of_lt hlt', ZMod.val_cast_of_lt hlt] at h
  have hdd : d' (k : ℕ) = d (k : ℕ) :=
    digitsEqOfSumEq p hp N d' d hd'lt
      (fun j hj => hdlt j (lt_of_lt_of_le hj hNN')) hnat (k : ℕ) k.isLt
  have hL : d' (k : ℕ) = (boxeq N g (digitIdx n N i k)).val :=
    hd'eq (k : ℕ) k.isLt
  have hR : d (k : ℕ)
      = (boxeq N' f (digitIdx n N' i (Fin.castLE hNN' k))).val :=
    hdeq (k : ℕ) (lt_of_lt_of_le k.isLt hNN')
  apply ZMod.val_injective
  rw [← hL, ← hR]
  exact hdd

end DigitHelpers

/-- SYN-C2 THE DERIVATION (TransferRow leg) — the (†6) row follows from the
    ONE kernel row at the dressed bridge tower.  E-PHASE SKELETON (statement
    pinned, body `sorry`): the derivation is Lean-side composition work, NOT
    open mathematics — `Realizes`/`fiberAt` are mem/child/redPoly-composed,
    so `child_local` + `chart_pin` transfer them across levels exactly as the
    TV-B3..B6 chain does at fixed level (run at `bridgeTmStd`, then unfolded
    to `bridgeTm` via `MovesT.reindexModel_child`/`_mem`), with the box-side
    agreement supplied by IB-A12's digit-truncation compat
    (`boxEquivD_boxProj`-genre) through the parametric digit law `hdig`
    (= `TreePin.boxeq_digits`'s shape, the BridgeD2 precedent) and the chart
    gate `blockInterleave_bridgeChart`.  Consumed by the IB-F2/F4 wiring to
    supply `BridgeKernelsCtor.transfer`; the ledger names ReadLocality once. -/
theorem transferRow_of_readLocality (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (hdig : ∀ (N : ℕ) (f : Box p n N) (i : Fin n),
      f i = ∑ k : Fin N, ((boxeq N f (digitIdx n N i k)).val : ZMod (p ^ N))
        * (p : ZMod (p ^ N)) ^ (k : ℕ))
    (RL : BridgeReadLocality n p) :
    TransferRow n p boxeq := by
  -- the chart pullback identities (the compiled gate `blockInterleave_bridgeChart`)
  have hχ : ∀ (M : ℕ) (hM : 0 < M),
      (fun b => (MovesT.blockInterleave n M).symm (bridgeChartStd n M hM b))
        = bridgeChart n M hM := by
    intro M hM
    funext b
    rw [← blockInterleave_bridgeChart n M hM b, Equiv.symm_apply_apply]
  -- the forward dressing: a raw fiberAt witness reads at the dressed tower
  have hdress : ∀ (V : MovesT.VTree p (ZMod p)) (M : ℕ) (hM : 0 < M)
      (x : MovesD.Box p (n * M)),
      V.fiberAt (bridgeTm p n M) (bridgeChart n M hM) x →
      V.fiberAt (bridgeTmStd p n M) (bridgeChartStd n M hM)
        (fun c => x ((MovesT.blockInterleave n M).symm c)) := by
    intro V M hM x hx
    refine (fiberAtReindex V (bridgeTm p n M) (MovesT.blockInterleave n M)
      (bridgeChartStd n M hM) (fun c => x ((MovesT.blockInterleave n M).symm c))).mpr ?_
    have hbox : (fun s => x ((MovesT.blockInterleave n M).symm
        ((MovesT.blockInterleave n M) s))) = x := by
      funext s
      rw [Equiv.symm_apply_apply]
    show V.fiberAt (bridgeTm p n M)
      (fun b => (MovesT.blockInterleave n M).symm (bridgeChartStd n M hM b))
      (fun s => x ((MovesT.blockInterleave n M).symm ((MovesT.blockInterleave n M) s)))
    rw [hχ M hM, hbox]
    exact hx
  -- the backward dressing: a dressed fiberAt witness reads raw
  have hundress : ∀ (V : MovesT.VTree p (ZMod p)) (M : ℕ) (hM : 0 < M)
      (y : MovesD.Box p (n * M)),
      V.fiberAt (bridgeTmStd p n M) (bridgeChartStd n M hM) y →
      V.fiberAt (bridgeTm p n M) (bridgeChart n M hM)
        (fun s => y ((MovesT.blockInterleave n M) s)) := by
    intro V M hM y hy
    have h := (fiberAtReindex V (bridgeTm p n M) (MovesT.blockInterleave n M)
      (bridgeChartStd n M hM) y).mp hy
    rwa [hχ M hM] at h
  constructor
  · -- `realizes_transfer`: transport the witness through the dressing, extend
    -- it by zeros above the cutoff min N N', transfer via the kernel row
    rintro V N N' hN hN' hthrN hthrN' ⟨x, hx⟩
    set y : MovesD.Box p (n * N) :=
      fun c => x ((MovesT.blockInterleave n N).symm c) with hydef
    have hy : V.fiberAt (bridgeTmStd p n N) (bridgeChartStd n N hN) y :=
      hdress V N hN x hx
    -- the zero-extension of y's sub-cutoff block to level N'
    have hcN : min N N' ≤ N := min_le_left N N'
    have hcN' : min N N' ≤ N' := min_le_right N N'
    set y' : MovesD.Box p (n * N') := fun c =>
      if hc : (c : ℕ) < n * min N N' then
        y ⟨(c : ℕ), lt_of_lt_of_le hc (Nat.mul_le_mul_left n hcN)⟩ else 0 with hy'def
    have hagree : ∀ c : Fin (n * min N N'),
        y (Fin.castLE (Nat.mul_le_mul_left n hcN) c)
          = y' (Fin.castLE (Nat.mul_le_mul_left n hcN') c) := by
      intro c
      have hc : ((Fin.castLE (Nat.mul_le_mul_left n hcN') c : Fin (n * N')) : ℕ)
          < n * min N N' := c.isLt
      simp only [hy'def]
      rw [dif_pos hc]
      rfl
    have hchild : ∀ (o : Option (MovesC.History p (ZMod p)))
        (ν : MovesC.Node p (ZMod p)),
        (bridgeTmStd p n N).child o ν y ↔ (bridgeTmStd p n N').child o ν y' :=
      fun o ν => (RL V).child_local (min N N') (le_min hthrN hthrN')
        N hN N' hN' hcN hcN' o ν y y' hagree
    have hred : MovesT.redPoly (bridgeChartStd n N hN) y
        = MovesT.redPoly (bridgeChartStd n N' hN') y' := by
      unfold MovesT.redPoly
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb : (b : ℕ) < n * min N N' :=
        lt_of_lt_of_le b.isLt
          (le_mul_of_one_le_right (Nat.zero_le n) (lt_min hN hN'))
      have hyb : y (bridgeChartStd n N hN b) = y' (bridgeChartStd n N' hN' b) :=
        hagree ⟨(b : ℕ), hb⟩
      rw [hyb]
    have hy' : V.fiberAt (bridgeTmStd p n N') (bridgeChartStd n N' hN') y' :=
      (fiberAtCross V (bridgeTmStd p n N) (bridgeTmStd p n N')
        (bridgeChartStd n N hN) (bridgeChartStd n N' hN') y y' hchild hred).mp hy
    exact ⟨fun s => y' ((MovesT.blockInterleave n N') s), hundress V N' hN' y' hy'⟩
  · -- `fiber_transfer`: the boxes agree below n·N through the (†3b) digit law
    intro V N N' hN hN' hNN' f hthr hfib
    set y : MovesD.Box p (n * N) := fun c =>
      boxeq N (boxProj p n hNN' f) ((MovesT.blockInterleave n N).symm c) with hydef
    set y' : MovesD.Box p (n * N') := fun c =>
      boxeq N' f ((MovesT.blockInterleave n N').symm c) with hy'def
    have hy : V.fiberAt (bridgeTmStd p n N) (bridgeChartStd n N hN) y :=
      hdress V N hN (boxeq N (boxProj p n hNN' f)) hfib
    have hagree : ∀ c : Fin (n * N),
        y (Fin.castLE (Nat.mul_le_mul_left n (le_refl N)) c)
          = y' (Fin.castLE (Nat.mul_le_mul_left n hNN') c) := by
      intro c
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · exact absurd c.isLt (by simp [hn0])
      · have hi : (c : ℕ) % n < n := Nat.mod_lt _ hn
        have hk : (c : ℕ) / n < N := by
          rw [Nat.div_lt_iff_lt_mul hn]
          exact lt_of_lt_of_le c.isLt (Nat.mul_comm n N).le
        have hcompat := digitCompat boxeq hdig hNN' f
          ⟨(c : ℕ) % n, hi⟩ ⟨(c : ℕ) / n, hk⟩
        simp only [hydef, hy'def]
        exact hcompat
    have hchild : ∀ (o : Option (MovesC.History p (ZMod p)))
        (ν : MovesC.Node p (ZMod p)),
        (bridgeTmStd p n N).child o ν y ↔ (bridgeTmStd p n N').child o ν y' :=
      fun o ν => (RL V).child_local N hthr N hN N' hN' (le_refl N) hNN' o ν y y' hagree
    have hred : MovesT.redPoly (bridgeChartStd n N hN) y
        = MovesT.redPoly (bridgeChartStd n N' hN') y' := by
      unfold MovesT.redPoly
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb : (b : ℕ) < n * N :=
        lt_of_lt_of_le b.isLt (le_mul_of_one_le_right (Nat.zero_le n) hN)
      have hyb : y (bridgeChartStd n N hN b) = y' (bridgeChartStd n N' hN' b) :=
        hagree ⟨(b : ℕ), hb⟩
      rw [hyb]
    have hy' : V.fiberAt (bridgeTmStd p n N') (bridgeChartStd n N' hN') y' :=
      (fiberAtCross V (bridgeTmStd p n N) (bridgeTmStd p n N')
        (bridgeChartStd n N hN) (bridgeChartStd n N' hN') y y' hchild hred).mp hy
    have hout := hundress V N' hN' y' hy'
    have hbox : (fun s => y' ((MovesT.blockInterleave n N') s)) = boxeq N' f := by
      funext s
      simp only [hy'def]
      rw [Equiv.symm_apply_apply]
    rwa [hbox] at hout

end LeanUrat.MovesU
