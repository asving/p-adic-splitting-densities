/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.Moves.L3_K1
import LeanUrat.Moves.L2_keyResidualPow

/-!
# HC1.T3_htChainWeight — LST(i-a): ht IS the K1-chain weight of the basis monomial

moves_ref: MOVES 3736–3738 "ht(b, l) is the K1-chain weight of the coordinate's
basis monomial p^l·∏_r Φ̂_r^{innerslot_r(b)}". Stage scale = strTop·abs
(strTop = STR_K·e_K, §2.2 — audit C-1; SANITY at K = 0, (e₀,h₀): w(p^l·φ^b) =
e₀·l + b·h₀ = e₀·(l + b·κ₀) = strTop·ht ✓). deps: DefsTower; Moves `L3_K1`,
`L2_keyResidualPow` (clean); the per-move κ-update discipline (LST proof, MOVES
3750–3777). difficulty: HARD. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T3: the absolute height is the top stage's weight of the basis monomial,
divided by the frame stretch strTop. -/
theorem T3_htChainWeight {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (c : T.Coord) (hc : c.MonoNZ) :
    (((T.stg (Fin.last T.K)).w (T.mono c) : ℤ) : ℚ) = (T.strTop : ℚ) * T.ht c := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T3_htChainWeight
