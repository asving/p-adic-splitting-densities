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
  -- Substituting `z ↦ z + 1` and reducing over F₂ collapses `P` to the anchor
  -- normal form `z⁵ + z²`; all three legs read off it.
  have hnf : caseJP.comp (X + 1) = (X : Polynomial (ZMod 2)) ^ 5 + X ^ 2 := by
    unfold caseJP
    simp only [mul_comp, pow_comp, add_comp, X_comp, one_comp]
    ring_nf
    reduce_mod_char
  refine ⟨?_, ?_, ?_⟩
  · -- the anchored substitution display, in the sealed factored form
    unfold caseJP
    simp only [mul_comp, pow_comp, add_comp, X_comp, one_comp]
    ring_nf
    reduce_mod_char
  · -- `a' = ord_z P(z+1) ≥ μ = 2`: `X²` divides `X⁵ + X²`
    rw [hnf]
    exact ⟨X ^ 3 + 1, by ring⟩
  · -- `a' = 2` exactly: `X³` does not divide (`coeff 2 = 1 ≠ 0`)
    rw [hnf]
    intro hdvd
    rw [Polynomial.X_pow_dvd_iff] at hdvd
    have h2 := hdvd 2 (by norm_num)
    simp [Polynomial.coeff_X_pow] at h2

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G3_caseJGate
