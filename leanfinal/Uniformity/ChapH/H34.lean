/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity

/-!
# Uniformity.ChapH.H34 — `exp_compose`, `mul_le_of_exp_compose`

**Chapter H, NODE H.34** (`blueprint/CHAP-H_general_induction.md` §6, ENV-H1). The exponent
composition of the GROWING regime: a depth-`D` entry rate `ρ ≤ Q^(−(D−1))` times a residual
mass `δ ≤ Q^(−(M−c))` is at most `Q^(−(N−1−c))`, *exactly*, because `D + M = N`.

* `exp_compose`: the `ℕ`-exponent identity `(D − 1) + (M − c) = N − 1 − c` (subtraction-free
  content: it needs `1 ≤ D`, `c ≤ M`, `D + M = N`, without which the `ℕ` truncations bite).
* `mul_le_of_exp_compose`: the inequality it licenses, over `ℝ`.

DEPENDS: none.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iii), the GROWING regime: "with (i),
`contribution_l ≤ K·N^B·Q^{−(D_l−1)−(M_l−c)} = K·N^B·Q^{−(N−c−1)}` — the exponents COMPOSE EXACTLY
because `D_l + M_l = N`"). The corpus's own scoping is preserved: the identity is definitional
(`M_l := N − D_l`), and what `EFF.GENIND.152`'s machine leg D checks is the *extraction*, which is
geometric and has no node here.

**PROOF.** (1) `omega`. (2) `mul_le_mul` on the two bounds, then the product of inverses is the
inverse of the product (`mul_inv`), the product of powers is the power of the sum (`pow_add`), and
`exp_compose` identifies that sum with `N − 1 − c`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The signature of `mul_le_of_exp_compose` is frozen by the blueprint/stub gate; `hQ` and `hρ0`
-- are carried but not consumed by this (sharper) proof, so the unused-variable linter is off.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- The exponents compose exactly: `(D − 1) + (M − c) = N − 1 − c` when `D + M = N`, `1 ≤ D` and
`c ≤ M` (the two side conditions that stop `ℕ` truncation). NODE H.34(i). -/
theorem exp_compose {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M) (h : D + M = N) :
    (D - 1) + (M - c) = N - 1 - c := by
  omega

/-- The GROWING-regime product bound: an entry rate `ρ ≤ Q^(−(D−1))` against a residual mass
`δ ≤ Q^(−(M−c))` multiplies to at most `Q^(−(N−1−c))`, the exponents composing exactly via
`D + M = N`. NODE H.34(ii). -/
theorem mul_le_of_exp_compose {Q : ℕ} (hQ : 2 ≤ Q) {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M)
    (h : D + M = N) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) (hδ : δ ≤ ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - 1 - c))⁻¹ := by
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hstep : ρ * δ ≤ ((Q : ℝ) ^ (D - 1))⁻¹ * ((Q : ℝ) ^ (M - c))⁻¹ :=
    mul_le_mul hρ hδ hδ0 (by positivity)
  have hprod : ((Q : ℝ) ^ (D - 1))⁻¹ * ((Q : ℝ) ^ (M - c))⁻¹ = ((Q : ℝ) ^ (N - 1 - c))⁻¹ := by
    rw [← mul_inv, ← pow_add, exp_compose hD hc h]
  exact hprod ▸ hstep

section AxCheck
#print axioms Uniformity.Density.Induction.exp_compose
#print axioms Uniformity.Density.Induction.mul_le_of_exp_compose
end AxCheck

end Uniformity.Density.Induction
