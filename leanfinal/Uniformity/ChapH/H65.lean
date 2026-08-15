/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Real.Basic

/-!
# Uniformity.ChapH.H65 — `RateSpecies`, the `(A2-RATE)` species as a predicate

**Chapter H, NODE H.65** (`blueprint/CHAP-H_general_induction.md` §9, source `EFF.GENIND.151`,
`ANNEX R R1.1`). For `Q : ℕ` with `2 ≤ Q`, a normalized conservative complement `f : ℕ → ℝ`
*has the rate species with constants `(K, B, c)`* when
`∀ M, 1 ≤ M → f M ≤ K * M ^ B * (Q ^ (M − c))⁻¹` (natural subtraction in the exponent).

Definitional, no proof obligation. DEPENDS: none.

**Deliberate scope.** `(A2-RATE)` as displayed in the source has two halves — an *exactness*
half (the complement is a finite signed sum of `q`-powers with polynomially many terms) and the
*rate* half above. Every chapter-H consumer (H.67, H.68, H.71, H.72) is a bound consumer, so
this predicate carries the rate half alone; a node needing exactness must re-plan for a separate
`ExactSpecies` predicate.

**Vacuity disclosure (carried unchanged from the source).** At general degree data `(μ, d)` the
species is a hypothesis pin, not a theorem: nothing in this chapter supplies it beyond `μ = 2`
(H.28).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

/-- **(A2-RATE)** — the species pinned onto `P(k)`'s fourth member (`ANNEX R R1.1`): a normalized
conservative complement decays with a POLYNOMIAL coefficient and an EXPONENTIAL deficit, with
constants depending on the degree data only. -/
def RateSpecies (Q : ℕ) (K : ℝ) (B c : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ M, 1 ≤ M → f M ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.RateSpecies

end AxCheck
