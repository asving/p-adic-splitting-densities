/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.T12_coordFin — bookkeeping: level-N boxes are finite; fibers are level sets

moves_ref: MOVES 2088–2094 (height scales declared once). deps: DefsTower. sketch:
bounded slot vectors, product finiteness. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T12: coordinates restricted to any level-N box (p-adic level and top slot
bounded) form a finite set, and the `(blk, ht)`-fibers are exactly the level sets. -/
theorem T12_coordFin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (lmax bmax : ℕ) :
    Set.Finite {c : T.Coord | c.l < lmax ∧ c.slot (Fin.last T.K) < bmax} ∧
    (∀ (b : ℕ) (γ : ℚ), {c : T.Coord | T.blk c = b ∧ T.ht c = γ} = T.levelSet b γ) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T12_coordFin
