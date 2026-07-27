/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.C2_TYPa — TYP(a): the composite computes in_γ' and is ADDITIVE in the digits

moves_ref: MOVES 3795–3807 "in_{γ'}(B) = Σ_{c ∈ L_{γ'}(B)} y′_c·in(m_c) … an
ADDITIVE function … of exactly the level-set digits". deps: T4, T5, T6. The F3-1
repair: additivity in (y_c)_c, NEVER in box points (jet additivity is
p^N-torsion-impossible). The unit-lift additive carry (base-residue carries killed
in the piece) is the one genuinely delicate step. difficulty: HARD. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- Unit C2: TYP(a) — on assignments with block-b digits of height < γ' all zero,
`inγ γ' (slotCoeff b y) = typComposite b γ' (y ↾ levelSet)`, and the composite is
additive in the digit tuple. -/
theorem C2_TYPa {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) :
    (∀ y : T.Coord → ↥(T.stg 0).FQ, (Function.support y).Finite →
      (∀ c, y c ≠ 0 → T.blk c = b) →
      (∀ c, T.blk c = b → T.ht c < γ' → y c = 0) →
      T.inGr γ' (T.slotCoeff b y)
        = T.typComposite b γ' (fun c => y c.1)) ∧
    (∀ x y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ,
      T.typComposite b γ' (x + y)
        = T.typComposite b γ' x + T.typComposite b γ' y) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C2_TYPa
