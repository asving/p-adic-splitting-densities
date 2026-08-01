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
