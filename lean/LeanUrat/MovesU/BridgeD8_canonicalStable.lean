/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD5_transferRow
import LeanUrat.MovesU.BridgeD7_canonical

/-!
# IB-D8 — `canonical_stable` from `TransferRow` (bridge campaign BP1, cluster c7)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†7
tail) / §4 group D (IB-D8).  Deps: IB-D7 (`bridgeCanonical` + pin), IB-D5
(`TransferRow`), IB-A12 (see the resolution below).  Charge: TREE-N's
decision stability for the constructed classifier — the
`ClassifierSpec.canonical_stable` field (Defs.lean:66–68) at
`canonical := bridgeCanonical`, conditional on the `transfer` kernel row.

PROOF SKETCH (H ~30): the hypothesis `bridgeCanonical … N (boxProj h f) =
some σ` forces 0 < N (at N = 0 the classifier is `none` —
`bridgeCanonical_level0`; the N = 0 source case is VACUOUS), so
`bridgeCanonical_pin` unpacks a witness T with `bridgeThr σ T ≤ N` and
`(vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N (boxProj h f))`.
`TransferRow.fiber_transfer` (at V := vt σ T, thr guard from `bridgeVt_thr`,
0 < N' from 0 < N ≤ N') transports the fiber membership up to
`(vt σ T).fiberAt (Tm N') (chart N' hN') (boxeq N' f)`; with
`bridgeThr σ T ≤ N ≤ N'`, `bridgeCanonical_pin` backward at N' closes.

TRANSCRIPTION RESOLUTIONS (recorded):
* The blueprint lists IB-A12 ((†3c) boxProj-compat) among D8's deps; as
  landed in IB-D5, `fiber_transfer` is stated THROUGH `boxProj` directly, so
  (†3c) is folded into the ROW's discharge obligation and this unit consumes
  the row alone — no statement-level A12 dependency remains.
* The dictionary is the same `boxeq` binder as IB-D7 (A11 pending, recorded
  there); `{N N'}` implicit + `(h : N ≤ N')` explicit mirror the
  `ClassifierSpec.canonical_stable` field shape exactly, so IB-D11's
  assembly wires this theorem in verbatim (modulo the TR row argument, which
  D11 takes from `BridgeKernels.transfer`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†7 tail) DECISION STABILITY: a level-N verdict on the reduction of a
    level-N' class persists at level N' — `ClassifierSpec.canonical_stable`'s
    supply at the constructed classifier, from the `TransferRow` kernel row
    (proof sketch in the file header; N = 0 source vacuous via
    `bridgeCanonical_level0`). -/
theorem bridgeCanonical_stable (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (TR : TransferRow n p boxeq)
    {N N' : ℕ} (h : N ≤ N') (f : Box p n N') (σ : SplittingType n) :
    bridgeCanonical n p boxeq N (boxProj p n h f) = some σ →
    bridgeCanonical n p boxeq N' f = some σ := sorry

end LeanUrat.MovesU
