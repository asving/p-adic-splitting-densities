/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL15b_packErestrictExt — LST leg (i-c) at `packE`, unfolded (BP5 CL-15b)

**Unit CL-15b** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4
CL-15, split per REVISION 2 finding 10).

**Informal statement.** Leg (i-c) of `LSTStmt'` at `packE T rl` — level-set
functionality: if two digit assignments agree on `levelSet b γ` (and both kill the
below-γ block-b digits, the leg's `hlow` row), their slot-coefficient expansions
have equal γ-components.

**Proof sketch (blueprint §3.2 (i-c)).** DEFINITIONAL at `packE`: each γ-component
of `packE.slotCoeff` reads its argument ONLY through the restriction to
`levelSet b γ`, and `hagree` makes the two restrictions EQUAL as functions
(funext + if-congr), so `congrArg` closes. The `hlow` row is kept for leg parity
with the R1 def text (it is unused at `packE`).

**Deps.** CL-09 (fold-back only). No proof-side deps — the leg is congruence.

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE` has NOT landed at HEAD (sibling
cluster); this unit states the leg's DEFINITIONAL UNFOLDING in tower vocabulary:
`packE.G.inγ γ (packE.slotCoeff _ b z)` ↦
`T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then z c else 0))`
(evalE ∘ display-(8) slotCoeff); `packE.lvl _ ↦ T.levelSet`; `packE.blk _ ↦ T.blk`;
`packE.ht _ ↦ T.ht`; the leg's `window` hypothesis is `True` at `packE` and hence
dropped. Fold-back to the literal pack leg = CL-19 glue (rfl-adjacent); `rl` does
not occur in the unfolded leg and is omitted.

difficulty: routine-opus. Size: ~15 of CL-15's ~90 total.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

/-- **CL-15b** — leg (i-c) at `packE`, unfolded (see the module docstring):
assignments agreeing on the level set have equal slot-coefficient γ-components;
the restriction reads only level-set values, so this is congruence. -/
theorem CL15b_packE_ic {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (x y : T.Coord → ↥(T.stg 0).FQ)
    (hagree : ∀ c ∈ T.levelSet b γ, x c = y c)
    (hlow : ∀ c : T.Coord, T.blk c = b → T.ht c < γ → x c = 0 ∧ y c = 0) :
    T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then x c else 0))
      = T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then y c else 0)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL15b_packE_ic
