/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesD.Defs

/-!
# IB-D1 — VERIFY-AND-WIRE pol/Tm (bridge campaign BP1; front-runner ADJ unit)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 / §4
group D (IB-D1) / §5 R7.  Charge: verify that MovesSp SP8's "real-TreeModel
instantiation" supplies an (n, N)-generic `MovesD.CanonPolicy`/`MovesD.TreeModel`
pair, and export `bridgePol p` / `bridgeTm p n N`; if it is n = 2-specific,
report the exact generalization needed and the area re-plans.

VERIFICATION EXECUTED (2026-07-30, by reading the as-built sources — the ADJ
half of this unit; the finding stands unless a prover refutes it):
* `MovesSp/SP8_instantiation.lean`: `canTreeModel_ofTreeModel` CONSUMES
  `T : MovesD.TreeModel p F n N m pol` as a BINDER and returns the abstract
  SP-COMP interface `CanTreeModel n p f`; it CONSTRUCTS no `TreeModel`.  The M2
  non-vacuity witness `toyCanModel : CanTreeModel 2 2 f₂` has `Branch := PUnit`
  — also not a `TreeModel`.
* The ONLY concrete `MovesD.TreeModel` instances in the corpus are toys:
  `MovesT.sibModel : TreeModel 2 (ZMod 2) 2 1 2 polTriv` (S2_sibFalse.lean:179),
  `MovesT.eligToyModel : TreeModel 2 (ZMod 2) 2 3 9 polTriv` (D2_eligGate.lean:114),
  `MovesT.toyModel`/`toyModelB : TreeModel 2 (ZMod 2) 2 3 9 polTriv`
  (G1_toyGate.lean:528/736) — all n = 2, FIXED (N, m), over the TRIVIAL policy
  `polTriv` (liftOf ≡ X, MovesT/Defs.lean:1850), with toy-semantic mem/child.
VERDICT: RISK R7 CONFIRMED — no (n, N)-generic real (pol, Tm) exists in-corpus.
EXACT GENERALIZATION NEEDED: a MovesD designer round constructing, per prime p,
the canonical policy (the (S6b) offset-P formula POL-PIN fixes) and the level-N
canonical-tree membership/child semantics of T_can(f) at the working level
m = n·N — `TreeModel`'s five fields (`mem`/`child`/`root_mem`/`mem_single`/
`mem_snoc`/`mem_realizable`) over `MovesD.CanonPolicy p (ZMod p)` at general
(n, N).  MovesD owns `TreeModel`; the constructor may need the MovesD policy
machinery at general n (blueprint R7's re-plan trigger — ORCHESTRATOR:
schedule the designer round; D-group statements are Tm-parametric, so only
this unit blocks on it).

The exports below are the wire half: the sorried defs carry the designer
obligation as data sorries so downstream D-group units can NAME the pinned
(pol, Tm) now.  They are NOT provable by any in-corpus wiring (finding above);
filling them = the designer round's deliverable.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- THE PINNED CANONICAL POLICY, per prime (blueprint §3.4: "fixed once per
    (n, p)"; the policy itself is n-free — `MovesD.CanonPolicy` carries only the
    per-node lift rule).  DESIGNER OBLIGATION (R7 confirmed, see file header):
    no in-corpus real instance exists; the toy `MovesT.polTriv` is p = 2-pinned
    and trivial (liftOf ≡ X), not the (S6b) POL-PIN policy. -/
noncomputable def bridgePol (p : ℕ) [Fact p.Prime] : MovesD.CanonPolicy p (ZMod p) :=
  sorry

/-- THE PINNED PER-LEVEL TREE MODEL at the working level m = n·N (TREE-N's own
    level), consumed by `TreePin.Tm` (DefsLedger.lean:347).  DESIGNER OBLIGATION
    (R7 confirmed): the corpus's only TreeModels are n = 2 toys over `polTriv`;
    the general constructor is a MovesD designer round (file header for the
    exact field list). -/
noncomputable def bridgeTm (p : ℕ) [Fact p.Prime] (n N : ℕ) :
    MovesD.TreeModel p (ZMod p) n N (n * N) (bridgePol p) :=
  sorry

end LeanUrat.MovesU
