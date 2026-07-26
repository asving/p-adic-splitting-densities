/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore

/-!
# Moves/L4_TRANSvii_R4 — D.7(vii) child-coefficient digit = parent ψ-digit × frame unit (S5')

MOVES ~2258-2267.  AUDIT-3 REPAIR: this is the CROSS-STAGE verification of S5' against the
`TransitionCore` construction records.  The child residual `σ'.R B` for a coefficient
`B ∈ Ĉ` is a monomial at the forced position `−σ'.t·(σ.w B)` whose scalar is the parent
D.6 digit `σ.digPrime z̄ B` times a frame unit `z̄^m`; and `σ'.wPrev B = σ.w B` (history
invariant).  All three conjuncts are READ OFF the transition records:
`TransitionCore.child_dig` (the digit/position pair) and `TransitionData.child_wPrev`
(the parent-valuation history invariant); `inC σ'.Φ B` becomes `inC Φhat B` via
`TransitionData.child_key : σ'.Φ = Φhat`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial

theorem L4_TRANSvii {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (hcore : StageCore σ) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) (htrans : TransitionCore σ σ' Φhat e' h' zbar) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC σ'.Φ B) : ∃ (c' : (↥σ'.K)ˣ) (m : ℤ), σ'.R B = LaurentPolynomial.C (c' : ↥σ'.K) * LaurentPolynomial.T (- σ'.t * σ.w B) ∧ ((c' : ↥σ'.K) : F) = σ.digPrime zbar B * ((zbar ^ m : Fˣ) : F) ∧ σ'.wPrev B = σ.w B := by
  -- Move `inC σ'.Φ B` to `inC Φhat B` via the child-key record.
  have hBc' : inC Φhat B := htrans.base.child_key ▸ hBc
  -- The digit/position pair is exactly the `child_dig` construction record.
  obtain ⟨c', m, hRB, hcF⟩ := htrans.child_dig B hB hBc'
  -- The third conjunct is the history invariant `child_wPrev`.
  exact ⟨c', m, hRB, hcF, htrans.base.child_wPrev B⟩

end LeanUrat.Moves
