/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.C4_DOM

/-!
# HC1.CL18_packEdom — `DOMStmt'` at `packE`, unfolded (BP5 CL-18)

**Unit CL-18** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4).

**Informal statement.** `DOMStmt'` (R3) at `packE T rl`: interior line domination
— for all `m < i` and base indices `b` inside the per-i interior, the current line
dominates: `(line m).at b ≤ (line i).at b`. R3's `i` ranges over ALL ℕ, so the
instance must guard `i > K`: `packE.interiorEnd _ i := if i ≤ T.K then
rl.interiorEnd i else 0` (display (8)) makes the `i > K` case vacuous.

**Proof sketch (blueprint §3.2 DOM).** Cases on `i ≤ T.K`: main branch —
`(C4_DOM T rl ⟨i, _⟩ m hm b hb').1` after the if-rewrite (C4_DOM: PROVED Lean-core
at HEAD, from `rl.steeper`/`rl.vertex_entry` via `MovesC.C2_DOM`); guard branch —
`hb` gives `b < 0`, absurd (`Nat.not_lt_zero`).

**Deps.** CL-09 (fold-back only); `C4_DOM` (PROVED Lean-core at HEAD).

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE` has NOT landed at HEAD (sibling
cluster); this unit states the statement def's DEFINITIONAL UNFOLDING in
tower/realizability vocabulary per the display-(8) field values:
`packE.lines _ ↦ rl.line`, `packE.interiorEnd _ i ↦ if i ≤ T.K then
rl.interiorEnd i else 0` (the `i > K` guard baked into the hypothesis `hb`
verbatim). `packE.Hist = Unit`, so the def's `∀ H` binder is dropped. Fold-back to
the literal `DOMStmt' p (packE T rl)` = CL-19 glue (rfl-adjacent).

difficulty: routine-opus. Size: ~25.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- **CL-18** — `DOMStmt'` at `packE`, unfolded (see the module docstring):
interior line domination with the `i > K` guard baked into `interiorEnd`
(`if i ≤ T.K then rl.interiorEnd i else 0`); the `i ≤ K` branch is C4_DOM's first
conjunct, the `i > K` branch is vacuous (`b < 0`). -/
theorem CL18_packE_dom {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (i m b : ℕ)
    (hm : m < i) (hb : b < if i ≤ T.K then rl.interiorEnd i else 0) :
    (rl.line m).at b ≤ (rl.line i).at b := by
  by_cases hle : i ≤ T.K
  · rw [if_pos hle] at hb
    exact (C4_DOM T rl ⟨i, by omega⟩ m hm b hb).1
  · rw [if_neg hle] at hb
    exact absurd hb (Nat.not_lt_zero b)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL18_packE_dom
