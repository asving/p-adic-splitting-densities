/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL15d_packEavoid — LST leg (iii) at `packE`, unfolded (BP5 CL-15d)

**Unit CL-15d** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4
CL-15, split per REVISION 2 finding 10).

**Informal statement.** Leg (iii) of `LSTStmt'` at `packE T rl`: level sets
strictly above the floor avoid the floor set — for `floorB b < γ'` and
`c ∈ levelSet b γ'`, NOT (`blk c = b ∧ ht c ≤ floorB b`).

**Proof sketch (blueprint §3.2 (iii)).** Pure logic, C1's leg-(iii) argument
verbatim: `c ∈ T.levelSet b γ'` gives `T.ht c = γ' > rl.floorB b`, contradicting
`T.ht c ≤ rl.floorB b`. Two lines.

**Deps.** CL-09 (fold-back only). No proof-side deps (`C1_LST`'s leg (iii) is the
template, not an import).

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE` has NOT landed at HEAD (sibling
cluster); this unit states the leg's DEFINITIONAL UNFOLDING in tower/realizability
vocabulary: `packE.floorB _ ↦ rl.floorB`, `packE.lvl _ ↦ T.levelSet`,
`packE.blk _ ↦ T.blk`, `packE.ht _ ↦ T.ht`. Fold-back to the literal pack leg =
CL-19 glue (rfl-adjacent).

difficulty: routine-opus. Size: ~5 of CL-15's ~90 total.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- **CL-15d** — leg (iii) at `packE`, unfolded (see the module docstring): a
level set at height strictly above the block floor cannot meet the floor set
(`ht c = γ' > floorB b` contradicts `ht c ≤ floorB b`). -/
theorem CL15d_packE_avoid {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (b : ℕ) (γ' : ℚ)
    (hfl : rl.floorB b < γ') :
    ∀ c ∈ T.levelSet b γ', ¬ (T.blk c = b ∧ T.ht c ≤ rl.floorB b) := by
  rintro c hc ⟨-, hle⟩
  have hht : T.ht c = γ' := hc.2
  rw [hht] at hle
  exact absurd hle (not_le.mpr hfl)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL15d_packE_avoid
