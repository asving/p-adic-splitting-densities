/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Uniformity.ChapH.H68 — the BOUNDED regime: the route prefactor carries the whole rate

**Chapter H, NODE H.68** (`blueprint/CHAP-H_general_induction.md` §10, ENV-H1). Fix `2 ≤ Q`,
`1 ≤ D`, `D + M = N`, and a threshold `c₀` with `M ≤ c₀`. Given only the **trivial** child bound
`0 ≤ δ ≤ 1` and the route prefactor bound `ρ ≤ Q^(−(D − 1))` (H.36's codimension),

`ρ · δ ≤ Q^(−(N − c₀ − 1))`.

The child's own vanishing is **never invoked**: the route prefactor carries the whole rate. This is
the point of the branch — a capped child window cannot supply a decaying rate, and does not have to.

DEPENDS: H.36, H.65 / H.66 (semantic suppliers of the two hypotheses; no term of either is consumed)
· mathlib `mul_le_mul_of_nonneg_left`, `pow_le_pow_right₀`, `inv_anti₀`, `pow_pos`.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iii)'s BOUNDED branch, verbatim: *"BOUNDED (`M_l ≤ c₀`):
the child limit is never invoked; the trivial `u_l/T_l ≤ 1` and (i) alone give
`contribution_l ≤ Q^{−(D_l−1)} = Q^{−(N−M_l−1)} ≤ Q^{−(N−c₀−1)}` — the route prefactor carries the
whole rate, **which is Codex's bounded-`M_l` half, now displayed**"*); `EFF.GENIND.149` (`R1.0`'s
half (ii), the defect this repairs, verbatim: *"a capped child window `M_l = N − D_l` can stay
BOUNDED while the genre depth `D_l` grows with `N`, and there the child's own `M_l → ∞` vanishing
cannot be applied — those β-terms vanish only through the route prefactor, and no bounded-vs-growing
split was displayed"*).

## The proof, in three moves

1. `ρ · δ ≤ ρ · 1 = ρ ≤ Q^(−(D − 1))` — the only use `δ` gets is `δ ≤ 1`.
2. `N − c₀ − 1 ≤ D − 1` in `ℕ` (with truncation): from `D + M = N` and `M ≤ c₀`, by `omega`. The
   truncated case `c₀ ≥ N` is harmless — the left side is then `0`.
3. Monotonicity of `x ↦ Q^x` (needs `1 ≤ Q`, from `hQ`) and then antitonicity of inversion on the
   positives turn that exponent inequality into `Q^(−(D − 1)) ≤ Q^(−(N − c₀ − 1))`.

**⚠ THIS IS THE MATHEMATICALLY SUBSTANTIVE HALF OF `CODEX F3`.** `EFF.GENIND.149`'s CONDITIONALITY:
*"**Half (ii) is the mathematically substantive one** and is what forces GENIND-C1(iii)'s two-regime
split; half (i) is a hypothesis-display gap."* The pair (H.67, H.68) is the split; **neither node
alone discharges the defect**, and a fleet agent landing only H.67 has reproduced the defect. H.67
(`rate_growing`) is the GROWING half; this file is the BOUNDED half, and the two together are what
`H.69`/`H.71` combine by domination (H.66).

**TEETH (why no battery row could have found this).** `EFF.GENIND.149`: *"Eight in-house hostile
passes did not find it, and no battery row could have: the runner computes exact counts, and an
exact count is silent about the RATE its own asymptotics need"* — the disposition is therefore a
Lean theorem and nothing else.

**Signature note.** `hδ0 : 0 ≤ δ` is carried by the frozen signature but not consumed: `δ ≤ 1` and
`0 ≤ ρ` suffice for step 1. The unused-variable linter is disabled for that reason.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The signature is frozen by the blueprint/stub gate; `hδ0` is carried but not consumed by this
-- proof, so the unused-variable linter is off.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- **The BOUNDED regime** (`GENIND-C1`(iii), second branch — Codex's half, now displayed). When
the child window `M` is capped by the threshold `c₀`, the child's own decay is never invoked: the
trivial bound `δ ≤ 1` together with the route prefactor `ρ ≤ Q^(−(D−1))` already gives
`ρ · δ ≤ Q^(−(N − c₀ − 1))`. NODE H.68. -/
theorem rate_bounded {Q : ℕ} (hQ : 2 ≤ Q) {D M N c₀ : ℕ} (hD : 1 ≤ D) (hDM : D + M = N)
    (hM : M ≤ c₀) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - c₀ - 1))⁻¹ := by
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by
    have h1 : (1 : ℕ) ≤ Q := by omega
    exact_mod_cast h1
  have hQ0 : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_one hQ1
  -- The exponent comparison, with `ℕ` truncation: `N − c₀ − 1 ≤ D − 1` from `D + M = N`, `M ≤ c₀`.
  have hexp : N - c₀ - 1 ≤ D - 1 := by omega
  have hpow : (Q : ℝ) ^ (N - c₀ - 1) ≤ (Q : ℝ) ^ (D - 1) := pow_le_pow_right₀ hQ1 hexp
  have hinv : ((Q : ℝ) ^ (D - 1))⁻¹ ≤ ((Q : ℝ) ^ (N - c₀ - 1))⁻¹ :=
    inv_anti₀ (pow_pos hQ0 (N - c₀ - 1)) hpow
  -- The child limit is never invoked: `δ ≤ 1` is all that is used of `δ`.
  calc ρ * δ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hδ1 hρ0
    _ = ρ := mul_one ρ
    _ ≤ ((Q : ℝ) ^ (D - 1))⁻¹ := hρ
    _ ≤ ((Q : ℝ) ^ (N - c₀ - 1))⁻¹ := hinv

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.rate_bounded

end AxCheck
