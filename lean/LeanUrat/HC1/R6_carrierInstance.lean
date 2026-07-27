/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R5_EQ2Pass

/-!
# HC1.R6_carrierInstance — the instantiation deliverable at δ = 1

moves_ref: MOVESR blueprint D4(a) "instantiation from the OM engine is HC-1's
declared deliverable" + campaign §1 HC-2. deps: T6, C1–C4, R1–R4. The LST/TYP/DOM
LEGS of `CStatements` hold for the tower's real carrier; the jets/counting legs
(thmCa/thmCb/C05/C1/C15) are NOT claimed: they need the JetSetup bridge —
**HC-2's seam**, recorded. difficulty: medium (assembly).
hyp: `TowerRealizable` (§5).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open LeanUrat.Moves

/-- Unit R6 (`hc1_carrier_legs`): for every realizable tower there is a carrier
pack whose graded pieces are the tower's REAL pieces (`grQ` — the non-vacuity
pin) satisfying the LST, TYP, and DOM statement defs. -/
theorem R6_carrierInstance {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) :
    ∃ K : CarrierPackR p,
      (∀ γ : ℚ, K.G.Gr γ = T.grQ γ) ∧
      LSTStmt' p K ∧ TYPStmt' p K ∧ DOMStmt' p K := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.R6_carrierInstance
