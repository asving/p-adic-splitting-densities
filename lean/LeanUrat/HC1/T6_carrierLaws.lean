/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesGr.L0_pmul_mk
import LeanUrat.MovesGr.L0_initialForm_zero
import LeanUrat.MovesGr.L0_initialForm_ne_zero
import LeanUrat.MovesGr.L0_deg_add

/-!
# HC1.T6_carrierLaws — the real carrier satisfies the four GradedCarrier laws

moves_ref: MOVES 3799–3801 ("the class map is additive and kills weight > δ′ —
D.1") + D.1(b). deps: DefsCar; MovesGr `L0_pmul_mk`, `L0_initialForm_*`,
`L0_deg_add` (proved). First leg: `HasSide` (the side-valuation bundle exists —
the constant-weight nonnegativity rides the spine induction). Second leg: the four
laws through the ⌊strTop·γ⌋ reindexing (C-1 re-thread); off-lattice clauses vacuous
by D3's convention. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T6: the tower's side bundle exists and the concrete carrier data satisfy
the four GradedCarrier laws (`Tower.carrier` packages them). -/
theorem T6_carrierLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) : T.HasSide ∧ T.CarrierLaws := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T6_carrierLaws
