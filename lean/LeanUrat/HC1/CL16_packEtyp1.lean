/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL16_packEtyp1 — TYP conjunct 1 at `packE`, unfolded (BP5 CL-16)

**Unit CL-16** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4,
SCOPED at REVISION 2 finding 7 — the binding Q-6 ruling: bank NOTHING beyond the
three R6 conjuncts. This file emits `packE_typ1` ONLY; no `packE_secB1`, no extra
public name. The observation that `SecB1Stmt'` (R4) is the SAME lemma up to binder
order survives as exactly this comment, pointing at the blueprint — nothing more.)

**Informal statement.** `TYPStmt'` conjunct 1 (R2) at `packE T rl`: unconditional
additivity of `inγ γ' ∘ slotCoeff b` in the digit tuple —
`inγ γ' (slotCoeff b (x + y)) = inγ γ' (slotCoeff b x) + inγ γ' (slotCoeff b y)`.
(DEFECT-2 scoping, per the A17 record: the repair was choosing the right INSTANCE
— the graded-expansion pack, whose evaluation is UNCONDITIONALLY additive — never
weakening the `TYPStmt'` text; the polynomial-Coeff pack stays refuted
cross-strata.)

**Proof sketch (blueprint §3.2 TYP conjunct 1).** Componentwise at γ': the
level-set restriction commutes with `+` (pointwise: the if-branches add and
`0 + 0 = 0`); rewrite each side through `T.typComposite` via the
extension-of-restriction equality (for `z` supported inside `levelSet b γ'`,
`T.inGr γ' (T.slotCoeff b z) = T.typComposite b γ'` of the subtype tuple —
definitional through `typComposite`'s dite); close with `(C2_TYPa T b γ').2`
(`typComposite` additivity in the level-set digit tuple — PROVED Lean-core at
HEAD, including the former conjunct-(b) carry wall).

**Deps.** CL-09 (fold-back only); `C2_TYPa` (PROVED Lean-core at HEAD).

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE` has NOT landed at HEAD (sibling
cluster); this unit states the conjunct's DEFINITIONAL UNFOLDING in tower
vocabulary: `packE.G.inγ γ' (packE.slotCoeff _ b z)` ↦
`T.inGr γ' (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ' then z c else 0))`
(evalE ∘ display-(8) slotCoeff), `packE.Digit ↦ ↥(T.stg 0).FQ`. Fold-back to the
literal `TYPStmt'` conjunct at `packE` = CL-19 glue (rfl-adjacent); `rl` does not
occur in the unfolded conjunct and is omitted.

difficulty: routine-opus. Size: ~70.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

/-- **CL-16 (`packE_typ1` — the ONLY public banked for TYP conjunct 1, per the
binding Q-6 ruling)** — `TYPStmt'` conjunct 1 at `packE`, unfolded (see the module
docstring): the γ'-component of the slot-coefficient expansion is additive in the
digit tuple, unconditionally. -/
theorem packE_typ1 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) (x y : T.Coord → ↥(T.stg 0).FQ) :
    T.inGr γ' (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ' then (x + y) c else 0))
      = T.inGr γ' (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ' then x c else 0))
        + T.inGr γ' (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ' then y c else 0)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.packE_typ1
