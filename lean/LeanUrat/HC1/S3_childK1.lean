/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine

/-!
# HC1.S3_childK1 — K1(Φ̂/w′) is definitional

moves_ref: MOVES 2338–2340 "(ii) K1(Φ̂/w′) is definitional (the accepted pass-4
observation)". deps: S2. sketch: unfold; the development of f at Φ̂ IS the defining
data; w′(Φ̂) = h′. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S3: the child key's own weight is h′ and Lemma K1 holds at the child's own
key for the child valuation. -/
theorem S3_childK1 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (hdeg : 1 ≤ Φhat.natDegree) (e' h' : ℕ) (he' : 1 ≤ e') (hh' : 1 ≤ h')
    (hw1 : σ.w 1 = 0) :
    childW σ Φhat e' h' Φhat = (h' : ℤ) ∧
    K1At (childW σ Φhat e' h') Φhat ((h' : ℤ)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S3_childK1
