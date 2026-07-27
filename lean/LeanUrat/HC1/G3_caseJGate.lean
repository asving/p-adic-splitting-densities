/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# HC1.G3_caseJGate — the Case-J anchor-monomial gate (a > 0), algebraic instance

moves_ref: MOVES 2644–2651 (the anchored display; "Case J pinned a > 0"); D.12
(Case J sealed, 12 strata). Over ZMod 2 (c̃ = 1), P := z·(z+1)²·(z²+z+1) (a = 1,
μ = 2, ψ′ = z+1, h = z²+z+1 with ψ′ ∤ z^a·h): the substitution display and
`a' = ord_z P(z+1) = μ = 2`, `R'_anch = (z'+1)·h(z'+1)`. deps: none (pure
Polynomial ZMod-2 arithmetic). difficulty: easy-medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

/-- the Case-J gate polynomial `P = z·(z+1)²·(z²+z+1)` over F₂. -/
noncomputable def caseJP : Polynomial (ZMod 2) :=
  Polynomial.X * (Polynomial.X + 1) ^ 2 * (Polynomial.X ^ 2 + Polynomial.X + 1)

/-- Unit G3: the anchored substitution display at the Case-J instance — the
composition identity, and `a' = ord_z P(z+1) = μ = 2` (X² divides, X³ does not),
with the anchored factor `(z'+1)·h(z'+1)` explicit. -/
theorem G3_caseJGate :
    (caseJP.comp (Polynomial.X + 1)
      = Polynomial.X ^ 2 * ((Polynomial.X + 1) *
        ((Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)).comp
          (Polynomial.X + 1)))) ∧
    ((Polynomial.X : Polynomial (ZMod 2)) ^ 2 ∣ caseJP.comp (Polynomial.X + 1)) ∧
    (¬ (Polynomial.X : Polynomial (ZMod 2)) ^ 3 ∣ caseJP.comp (Polynomial.X + 1)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G3_caseJGate
