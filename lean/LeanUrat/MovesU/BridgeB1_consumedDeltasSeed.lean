/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers

/-!
# IB-B1 — (†4a) the depth seed: `1 ∈ consumedDeltas C.T C.Fam`

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (†4a) /
§4 group B (IB-B1).

INFORMAL STATEMENT: the shallow depth δ = 1 is always a consumed base-change
depth — `(1 : ℕ+) ∈ MovesS.consumedDeltas C.T C.Fam`.  This discharges the
`RegData.one_mem_depthSet` field ("δ = 1 (the shallow pool) always arises",
MovesU/Defs.lean) of the tautological roster `bridgeRegData` (IB-B8), whose
`depthSet` is `(consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))` — B8
lifts this seed through `Finset.mem_image`.  If this were false the whole
`RegData` type would be uninstantiable at the roster — it is not.

DEPS: — (leaf unit; consumed by IB-B8).

PROOF SKETCH (blueprint: "iterate-monotone seed membership — routine"):
`MovesS.consumedDeltas T F = (step)^[n] {1}` with
`step s = s ∪ Finset.image₂ (·*·) (deltaFactors T F) s` (MovesS/Defs.lean:613).
Since `s ⊆ step s` (`Finset.subset_union_left`), the seed {1} survives every
iterate: induction on the iterate count via `Function.iterate_succ_apply'`
(`f^[k+1] x = f (f^[k] x)`), seed case `Finset.mem_singleton_self`.

TRANSCRIPTION RESOLUTION (recorded): the blueprint display "1 ∈ consumedDeltas
C.T C.Fam" is transcribed verbatim over a carrier pack `C : UCarriers n` (the
form IB-B8 consumes); `consumedDeltas` is `Finset ℕ+`-valued, so the membership
is stated at `(1 : ℕ+)` — the ℕ-level `1 ∈ depthSet` form is B8's one-step
image lift, not restated here.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-B1 — (†4a): the shallow depth δ = 1 is always consumed — the seed {1} of
    `consumedDeltas`' multiplicative-closure iterate survives every step.
    Feeds `bridgeRegData.one_mem_depthSet` (IB-B8). -/
theorem one_mem_consumedDeltas {n : ℕ} (C : UCarriers n) :
    (1 : ℕ+) ∈ MovesS.consumedDeltas C.T C.Fam :=
  sorry

end LeanUrat.MovesU
