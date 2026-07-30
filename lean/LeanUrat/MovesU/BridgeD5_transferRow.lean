/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.ReadLocality
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
  sorry

end LeanUrat.MovesU
