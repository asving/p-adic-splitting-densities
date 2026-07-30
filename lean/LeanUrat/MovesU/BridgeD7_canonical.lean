/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD6_fiberUniq

/-!
# IB-D7 — `bridgeCanonical` + `canonical_pin` (bridge campaign BP1, cluster c7)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†7)
/ §4 group D (IB-D7).  Deps: IB-D3 (`bridgeTree`), IB-D6 (†7u uniqueness),
IB-A11 (`boxEquivD` — see the resolution below).  Charge: the classifier of
Architecture B (adjudicated Q1: "the classifier IS the tree-fibering
verdict"), defined so `TreePin.canonical_pin` holds BY CONSTRUCTION —
`canonical N f = some σ` iff the digit class fibers at a carried σ-tree
within threshold.

THE DEFINITION (†7, open Classical):
    canonical N f := if hN : 0 < N then
      (if h : ∃ (σ : SplittingType n) (T : Tree σ), thr σ T ≤ N ∧
           (vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N f)
       then some h.choose else none) else none

PROOF SKETCH for the pin (both directions, H ~40): dif unfolding; FORWARD —
`h.choose` is SOME fibering type; the hypothesis σ equals it by (†7u)
well-definedness (`bridgeSigma_eq_of_fiberAt`: `MovesT.vtree_eq_of_fiberAt` +
typemult + `Subtype.ext`), so `some h.choose = some σ` pins the witness pair
onto σ (rewrite the choose-spec witness along the σ-equality); BACKWARD —
∃-intro into the dite's positive branch, then the emitted choose equals σ by
the same uniqueness.  N = 0 is outside the pin's guard (`hN : 0 < N` is a
binder, matching `TreePin.canonical_pin`'s guarded shape,
DefsLedger.lean:363–366).

TRANSCRIPTION RESOLUTION (recorded): the box dictionary is a BINDER
`boxeq : ∀ N, Box p n N ≃ MovesD.Box p (n * N)` — the concrete `boxEquivD`
is IB-A11's deliverable (another cluster; not yet on disk; the BridgeD2/D5
precedent).  IB-D11/IB-D18 instantiate `boxeq := boxEquivD` when assembling
`ClassifierSpec`/`TreePin`, which specializes this pin to the exact
`TreePin.canonical_pin` field.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open Classical in
/-- (†7) THE CLASSIFIER (Architecture B): the tree-fibering verdict — `some`
    of the (unique, by †7u) splitting type whose carried tree fibers at the
    digit image of f within threshold; `none` if no carried tree fibers, and
    `none` at the unguarded level N = 0. -/
noncomputable def bridgeCanonical (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N)) :
    ∀ N : ℕ, Box p n N → Option (SplittingType n) :=
  fun N f =>
    if hN : 0 < N then
      if h : ∃ (σ : SplittingType n) (T : bridgeTree n p σ),
          bridgeThr n p σ T ≤ N ∧
            (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN)
              (boxeq N f)
      then some h.choose
      else none
    else none

/-- The level-0 edge, definitional: the classifier is silent at N = 0 (the
    single-class box — `RealInstanceV2.stratumCount_level0`'s mechanism; used
    by IB-D8's vacuous source case). -/
theorem bridgeCanonical_level0 (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N)) (f : Box p n 0) :
    bridgeCanonical n p boxeq 0 f = none :=
  dif_neg (lt_irrefl 0)

/-- (†7) `canonical_pin`, BOTH directions — `TreePin.canonical_pin`'s supply
    at `boxeq := boxEquivD` (header resolution): the classifier emits σ IFF
    the digit class fibers at a carried σ-tree within threshold.  Forward =
    choose + (†7u) uniqueness; backward = ∃-intro (proof sketch in the file
    header). -/
theorem bridgeCanonical_pin (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (N : ℕ) (hN : 0 < N) (f : Box p n N) (σ : SplittingType n) :
    bridgeCanonical n p boxeq N f = some σ ↔
      ∃ T : bridgeTree n p σ, bridgeThr n p σ T ≤ N ∧
        (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN)
          (boxeq N f) := sorry

end LeanUrat.MovesU
