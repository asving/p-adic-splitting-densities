/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL15c_packEfloorId — LST leg (ii) at `packE`, unfolded (BP5 CL-15c)

**Unit CL-15c** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4
CL-15, split per REVISION 2 finding 10).

**Informal statement.** Leg (ii) of `LSTStmt'` at `packE T rl` — the inlined
staircase equation (F3-3): `floorB b = (lines (kIdx)).at (blockEdge b)`.

**Proof sketch (blueprint §3.2 (ii)).** DEFINITIONAL: `rl.floorB b` is DEFINED as
`(rl.line T.K).at (T.blockEdge b)` (DefsCar `TowerRealizable.floorB`, the
blueprint's "DefsCar.lean:266" pointer), and `packE` wires `kIdx _ := T.K`,
`lines _ := rl.line`, `blockEdge _ := T.blockEdge`, `floorB _ := rl.floorB` —
so the leg is `rfl`-adjacent.

**Deps.** CL-09 (fold-back only). No proof-side deps.

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE` has NOT landed at HEAD (sibling
cluster); this unit states the leg's DEFINITIONAL UNFOLDING in tower/realizability
vocabulary per the display-(8) field values named above. Fold-back to the literal
pack leg = CL-19 glue (rfl-adjacent).

difficulty: routine-opus. Size: ~5 of CL-15's ~90 total.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- **CL-15c** — leg (ii) at `packE`, unfolded (see the module docstring): the
staircase-floor identification `floorB b = (line K).at (blockEdge b)`, definitional
through `TowerRealizable.floorB`. -/
theorem CL15c_packE_floor {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (b : ℕ) :
    rl.floorB b = (rl.line T.K).at (T.blockEdge b) := rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL15c_packE_floor
