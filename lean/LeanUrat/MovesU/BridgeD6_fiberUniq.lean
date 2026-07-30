/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD4_vtLaws

/-!
# IB-D6 — FIBERING σ-UNIQUENESS (†7u) (bridge campaign BP1, cluster c7)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†7u)
/ §4 group D (IB-D6).  Deps: IB-D3 (`bridgeTree`), IB-D4 (`bridgeVt`).
Charge: two typed trees fibering at the same (N, box point) have EQUAL vt,
hence EQUAL σ — the well-definedness of the σ emitted by `bridgeCanonical`
(IB-D7's forward direction) and the single-valuedness of `treeOf` (†9,
IB-D17).

PROOF SKETCH (blueprint): `MovesT.vtree_eq_of_fiberAt`
(MovesT/F3_dictSum.lean:45, PROVED Lean-core — two complete finite trees
fibering the SAME box point are EQUAL) gives `vt σ T = vt σ' T'`; then
σ.1 = (vt σ T).typemult = (vt σ' T').typemult = σ'.1 by `bridgeVt_typemult`,
hence σ = σ' by `Subtype.ext`.  The same-σ corollary `T = T'` is
`bridgeVt_inj`.

TRANSCRIPTION RESOLUTION (recorded): stated at a GENERAL box point
`x : MovesD.Box p (n * N)` rather than at a dictionary image `boxeq N f` —
the blueprint's "fibering at (N, f)" always enters through `boxeq N f`
(IB-A11's deliverable, another cluster, not yet on disk), and the general-x
form subsumes it with no strength change (x is arbitrary either way).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†7u), vt face: two typed trees fibering at the same level-N box point
    have equal underlying VTrees.  Direct cite of
    `MovesT.vtree_eq_of_fiberAt` at the pinned model/chart. -/
theorem bridgeVt_eq_of_fiberAt {n p : ℕ} [Fact p.Prime]
    {σ σ' : SplittingType n} (T : bridgeTree n p σ) (T' : bridgeTree n p σ')
    {N : ℕ} (hN : 0 < N) {x : MovesD.Box p (n * N)}
    (h : (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN) x)
    (h' : (bridgeVt n p σ' T').fiberAt (bridgeTm p n N) (bridgeChart n N hN) x) :
    bridgeVt n p σ T = bridgeVt n p σ' T' :=
  MovesT.vtree_eq_of_fiberAt h h'

/-- (†7u), σ face: the emitted splitting type is well-defined — two typed
    trees fibering at the same level-N box point have equal σ (typemult
    through `bridgeVt_eq_of_fiberAt`, then `Subtype.ext`). -/
theorem bridgeSigma_eq_of_fiberAt {n p : ℕ} [Fact p.Prime]
    {σ σ' : SplittingType n} (T : bridgeTree n p σ) (T' : bridgeTree n p σ')
    {N : ℕ} (hN : 0 < N) {x : MovesD.Box p (n * N)}
    (h : (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN) x)
    (h' : (bridgeVt n p σ' T').fiberAt (bridgeTm p n N) (bridgeChart n N hN) x) :
    σ = σ' := by
  have hvt : bridgeVt n p σ T = bridgeVt n p σ' T' :=
    bridgeVt_eq_of_fiberAt T T' hN h h'
  refine Subtype.ext ?_
  rw [← bridgeVt_typemult n p σ T, ← bridgeVt_typemult n p σ' T', hvt]

/-- (†7u), same-σ corollary (IB-D17's single-valuedness of `treeOf`): within
    one σ the fibering tree is unique (`bridgeVt_inj` on
    `bridgeVt_eq_of_fiberAt`). -/
theorem bridgeTree_eq_of_fiberAt {n p : ℕ} [Fact p.Prime]
    {σ : SplittingType n} (T T' : bridgeTree n p σ)
    {N : ℕ} (hN : 0 < N) {x : MovesD.Box p (n * N)}
    (h : (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN) x)
    (h' : (bridgeVt n p σ T').fiberAt (bridgeTm p n N) (bridgeChart n N hN) x) :
    T = T' :=
  bridgeVt_inj n p σ (bridgeVt_eq_of_fiberAt T T' hN h h')

end LeanUrat.MovesU
