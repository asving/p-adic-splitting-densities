/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-D9a — `bridgeTrueType` DEF (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†8) /
§4 group D (IB-D9a, split of D9 post-Codex finding 1).

INFORMAL STATEMENT: the classifier's true-type map, defined THROUGH `ZpReads` so
that `ZpBridge.lift_true` becomes a case analysis on the dite (†8):
`trueType N f := if h : ∃ σ, ZpReads n p zf N f σ then some h.choose else none`
(open Classical).

DEPS: IB-E11 (`zfType` def — Group E, another cluster).  TRANSCRIPTION
RESOLUTION (recorded): IB-E11 has not landed, so the ℤ_p reading `zf` is a
BINDER with `ZpBridge.zfType`'s exact type `Polynomial ℤ_[p] → Multiset (ℕ × ℕ)`
(DefsLedger.lean:722); at consumption (IB-E9/IB-D11) the binder is instantiated
at IB-E11's `zfType`.  This matches the executable order the blueprint fixed
(E1 → E11 → D9a → D10 → (E8, E10) → D9b → E9 — Group E display) since a
zf-parametric D9a needs nothing from E11.

PROOF SKETCH: none — DEF-only unit (R, ~8).  The dite needs Classical
decidability of the ∃ (supplied by `Classical.propDecidable`); `some h.choose`
is well-defined by (†8u)'s single-lift uniqueness, PROVED at IB-D10
(`zpReads_unique_of_lift`, BridgeD10_trueTypeLevel0.lean) and consumed by
IB-D9b's `lift_true`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†8) THE TRUE TYPE, defined THROUGH `ZpReads` so that `lift_true` is a dite
    case analysis: emit the (unique — IB-D10's `zpReads_unique_of_lift`) σ every
    monic degree-n ℤ_p lift of `f` reads, if one exists; else `none`.
    `zf` = IB-E11's `zfType` at consumption (see file header). -/
noncomputable def bridgeTrueType (n p : ℕ) [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ) (f : Box p n N) :
    Option (SplittingType n) :=
  letI := Classical.propDecidable (∃ σ : SplittingType n, ZpReads n p zf N f σ)
  if h : ∃ σ : SplittingType n, ZpReads n p zf N f σ then some h.choose else none

end LeanUrat.MovesU
