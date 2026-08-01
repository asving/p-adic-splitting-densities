/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesD.R7_runRealizer

/-!
# Scaffold/DictIII/O14apMap — Step 9, MAPPED (unit III-R1)

Transcription of `lean/blueprints/BP_III.md` §1.10 (unit III-R1). ROOT Step 9's
consumed instance RRE(p, ZMod p) IS the corpus theorem
`LeanUrat.MovesD.runRealizerExists_zmod` (`MovesD/R7_runRealizer.lean`, O-14a′
Corollary 4); this module only re-exports it under the ROOT-facing name. Zero new
proof debt; footprint Lean-core (verified at the O14ap arc). The residual-law Prop
`MovesD.RunRealizerExists` itself lives in `MovesD/R7_polFillReduction.lean`
(imported transitively).
-/

namespace LeanUrat.Scaffold.DictIII

/-- ROOT Step 9's consumed instance RRE(p, ZMod p) IS the corpus theorem — re-export
    with the ROOT-facing name; footprint Lean-core (verified at the O14ap arc). -/
theorem runRealizerSupply (p : ℕ) [Fact p.Prime] :
    MovesD.RunRealizerExists p (ZMod p) :=
  MovesD.runRealizerExists_zmod p

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-R1 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.runRealizerSupply

/-!
# MANIFEST (unit III-R2): THE REDUCTION map note — no new declaration

BP_III §1.10 / §2 row III-R2 (src O14ap r3 §0): the `#check`-anchored map of ROOT
Step 9.  All anchors live in `LeanUrat.MovesD` (`MovesD/R7_polFillReduction.lean`,
`MovesD/R7_runRealizer.lean`); every one is Lean-core, verified at the O14ap arc.

**THE REDUCTION** (`canPolicyC_pin : RunRealizerExists p F → OffsetPPin (canPolicyC p F)`):
the ONE residual Prop `RunRealizerExists` fills ALL FIVE pin laws at the choice
policy, so the (†15) pair `canPolicy`/`canPolicy_pin` discharges from it alone.

**The recentering half — filled by `CanRealizes`**: `RunRealizerExists` demands, at
every recentering node of every `HistoryCoherent` history, a `CanRealizes` witness
(the pin's five realizer laws bundled at ONE node); `canLiftOf`/`canLiftOf_spec`
route that witness into the pin's `total` clause.

**The interior half — `interior_node_e_eq_one` etc.**: coherence itself supplies the
CR content at interior nodes: `interior_node_e_eq_one` (every interior stride is 1),
`interior_recentering_unramified` (σ.e = 1 at interior recenterings),
`interior_center_realizer_exists` (the node's own recorded lift is the center
realizer), and over `ZMod p` `frame_deg_one` (every frame key linear, so the (S6b′)
support clause is free — O-14a′ Thm 1(ii)/(iii)).

**The last-node flank** (twice-stable; O14ap r3 §0 item 1): `exists_run_start`
locates the run anchor; `terminal_center_realizer` derives the (S6b) threshold there
and transports it along the recentering run.

**The consumed instance** (twice-stable; O14ap r3 §0 item 2):
`runRealizerExists_zmod : RunRealizerExists p (ZMod p)` — interior nodes via the
recorded lift, terminal node via the flank theorem; re-exported above as
`runRealizerSupply` (unit III-R1), the ROOT-facing name.

**Fence** (O14ap r3 §0 items 3/5): at GENERAL F the compiled support clause (CR2) is
REFUTED-AS-STATED at deg Φ > 1 (the F₉ inert-quadratic countermodel); the general-F
stretch-threaded law is DEMOTED to Conjecture 5.4.C (open lemmas OL-1/OL-2), consumed
by nothing on the mandatory path.  Only the `ZMod p` instance is consumed.
-/

-- The recentering half (R7_polFillReduction.lean):
#check @LeanUrat.MovesD.CanRealizes
#check @LeanUrat.MovesD.canLiftOf
#check @LeanUrat.MovesD.canLiftOf_spec
#check @LeanUrat.MovesD.canPolicyC
#check @LeanUrat.MovesD.RunRealizerExists
#check @LeanUrat.MovesD.canPolicyC_pin          -- THE REDUCTION
#check @LeanUrat.MovesD.interior_recentering_unramified
#check @LeanUrat.MovesD.interior_center_realizer_exists

-- The interior half + terminal flank + consumed instance (R7_runRealizer.lean):
#check @LeanUrat.MovesD.interior_node_e_eq_one
#check @LeanUrat.MovesD.frame_deg_one
#check @LeanUrat.MovesD.exists_run_start
#check @LeanUrat.MovesD.terminal_center_realizer
#check @LeanUrat.MovesD.runRealizerExists_zmod  -- RRE(p, ZMod p): Step 9's supply
