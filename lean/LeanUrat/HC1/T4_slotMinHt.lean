/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L0_FactB_unique

/-!
# HC1.T4_slotMinHt — LST(i-b): the iterated slot minimum

moves_ref: MOVES 3738–3739 "w(B) = min{ht(b, l) : (b, l) ∈ blk(B), y_{(b,l)} ≠ 0}
(the iterated slot-minimum)". deps: T3; Moves `hK1`/`L0_FactB_unique`. Stated in the
Moves `SlotMinAttained` attained form (E-phase convention; sInf on WithTop ℚ dodged).
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T4: for a block-b supported, finitely supported assignment with nonzero
slot coefficient, the carrier weight is the attained minimum of the heights of the
nonzero digit coordinates. -/
theorem T4_slotMinHt {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hfin : (Function.support y).Finite) (hsupp : ∀ c, y c ≠ 0 → T.blk c = b)
    (hne : T.slotCoeff b y ≠ 0) :
    ∃ c₀ : T.Coord, y c₀ ≠ 0 ∧ T.wQ (T.slotCoeff b y) = (T.ht c₀ : WithTop ℚ) ∧
      ∀ c : T.Coord, y c ≠ 0 → T.ht c₀ ≤ T.ht c := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T4_slotMinHt
