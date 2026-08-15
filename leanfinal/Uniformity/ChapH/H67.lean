/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H34

/-!
# Uniformity.ChapH.H67 — the GROWING regime: the exponents compose exactly

**Chapter H, NODE H.67** (`blueprint/CHAP-H_general_induction.md` §10, ENV-H1). Fix `2 ≤ Q`,
`1 ≤ D`, `c ≤ M`, `D + M = N`. Given

* a child complement fraction `δ ≤ K · M^B · Q^(−(M − c))` — the child's `(A2-RATE)` at its
  strictly lower degree (H.65's `RateSpecies`, evaluated at the child window `M`), and
* a route prefactor `ρ ≤ Q^(−(D − 1))` — H.36's codimension,

the product obeys `ρ · δ ≤ K · N^B · Q^(−(N − 1 − c))`: **the exponents compose exactly**, because
`(D − 1) + (M − c) = N − 1 − c` (H.34's `exp_compose`, whose two side conditions `1 ≤ D` and
`c ≤ M` are exactly what stops `ℕ` truncation from biting).

DEPENDS: H.34, H.36, H.65, H.66 (`exp_compose` is the only one consumed as a term; the other three
are the DAG's semantic suppliers of the two hypotheses and of the species bookkeeping that H.71
uses downstream) · mathlib `mul_le_mul`, `mul_inv`, `pow_add`, `pow_le_pow_left₀`.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iii)'s GROWING branch, verbatim: *"GROWING (`M_l > c₀`):
the child's (A2-RATE) at its strictly lower degree `μ_l·d < m·d` ((IH), degree descent
GENIND-1(iii)) gives `u_l/T_l ≤ K·M_l^B·Q^{−(M_l−c)}`; with (i),
`contribution_l ≤ K·N^B·Q^{−(D_l−1)−(M_l−c)} = K·N^B·Q^{−(N−c−1)}` — the exponents COMPOSE EXACTLY
because `D_l + M_l = N`"*).

## The proof, in three moves

1. `ρ · δ ≤ Q^(−(D−1)) · (K · M^B · Q^(−(M−c)))` by `mul_le_mul` (all four factors nonnegative).
2. Regroup and compose: the two inverse powers merge to `(Q^((D−1) + (M−c)))⁻¹`, and
   `exp_compose hD hc hDM` rewrites that exponent as `N − 1 − c`. **This is the exact step**; no
   slack is introduced here.
3. Inflate the polynomial factor from the child window to the parent: `M ≤ N` follows from
   `D + M = N`, so `(M:ℝ)^B ≤ (N:ℝ)^B`, and `0 ≤ K` carries it through.

**⚠ THE DEGREE DESCENT IS A HYPOTHESIS, NOT A PROOF.** *"the child's (A2-RATE) at its strictly lower
degree … ((IH), degree descent GENIND-1(iii))"* — the descent `μ_l·d < m·d` is geometric (fracture
permanence, honesty item H-3) and the `(IH)` is the strong induction's. This node takes the child's
rate bound `hδ` as a **hypothesis**, which is exactly the interface; H.71 supplies it from the
induction. Nothing here proves that any child actually satisfies `hδ`.

**⚠ NEITHER H.67 NOR H.68 ALONE DISCHARGES `CODEX F3`.** This node is the GROWING half of the
two-regime split forced by `EFF.GENIND.149`'s `R1.0`; the BOUNDED half is H.68 (`rate_bounded`), and
`EFF.GENIND.149` records that half (ii) — the bounded one — *"is the mathematically substantive
one"*. Landing only this node reproduces the defect.

**Signature note.** `hQ : 2 ≤ Q` and `hρ0 : 0 ≤ ρ` are carried by the frozen signature but not
consumed by this (sharper) proof: the nonnegativity that step 1 needs is `0 ≤ δ` together with
`0 ≤ Q^(−(D−1))`, which holds for every `Q : ℕ` by the cast. The unused-variable linter is disabled
for that reason, exactly as at H.34.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The signature is frozen by the blueprint/stub gate; `hQ` and `hρ0` are carried but not consumed
-- by this proof (cf. H.34), so the unused-variable linter is off.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- **The GROWING regime** (`GENIND-C1`(iii), first branch). A route prefactor `ρ ≤ Q^(−(D−1))`
against a child complement fraction `δ ≤ K · M^B · Q^(−(M−c))` multiplies to at most
`K · N^B · Q^(−(N−1−c))`: the exponents compose exactly via `D + M = N` (H.34), and the only
inflation is `M^B ↦ N^B`. NODE H.67. -/
theorem rate_growing {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c D M N : ℕ} (hK : 0 ≤ K)
    (hD : 1 ≤ D) (hc : c ≤ M) (hDM : D + M = N) {ρ δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹)
    (hδ : δ ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹ := by
  -- (1) Multiply the two bounds.
  have hstep : ρ * δ ≤ ((Q : ℝ) ^ (D - 1))⁻¹ * (K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) :=
    mul_le_mul hρ hδ hδ0 (by positivity)
  -- (2) The exponents compose EXACTLY: `(D − 1) + (M − c) = N − 1 − c` (H.34).
  have hprod : ((Q : ℝ) ^ (D - 1))⁻¹ * (K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹)
      = K * (M : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹ := by
    have hre : ((Q : ℝ) ^ (D - 1))⁻¹ * (K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹)
        = K * (M : ℝ) ^ B * (((Q : ℝ) ^ (D - 1)) * ((Q : ℝ) ^ (M - c)))⁻¹ := by
      rw [mul_inv]; ring
    rw [hre, ← pow_add, exp_compose hD hc hDM]
  -- (3) Inflate the polynomial factor from the child window `M` to the parent window `N`.
  have hMN : (M : ℝ) ≤ (N : ℝ) := by
    have h : M ≤ N := by omega
    exact_mod_cast h
  have hMB : (M : ℝ) ^ B ≤ (N : ℝ) ^ B := pow_le_pow_left₀ (Nat.cast_nonneg M) hMN B
  have hinv0 : (0 : ℝ) ≤ ((Q : ℝ) ^ (N - 1 - c))⁻¹ := by positivity
  calc ρ * δ ≤ ((Q : ℝ) ^ (D - 1))⁻¹ * (K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) := hstep
    _ = K * (M : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹ := hprod
    _ ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB hK) hinv0

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.rate_growing

end AxCheck
