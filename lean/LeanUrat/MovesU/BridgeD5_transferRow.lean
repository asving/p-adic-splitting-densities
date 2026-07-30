/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
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

end LeanUrat.MovesU
