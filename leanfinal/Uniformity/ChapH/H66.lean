/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H65
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Positivity

/-!
# Uniformity.ChapH.H66 — `RateSpecies` is closed under domination and constant inflation

**Chapter H, NODE H.66** (`blueprint/CHAP-H_general_induction.md` §10, sources `EFF.GENIND.153`
(the `c`-choice `c := c′ + 1` and its absorption of the head leg: *"`c ≥ c₀ + 1 ≥ 2 ≥ 1` absorbs the
head leg (`Q^{−(N−1)} ≤ Q^{−(N−c)}` iff `c ≥ 1`)"* — clause (ii) at `B = B'`) and
`EFF.GENIND.152`(iii) (the two-regime split, whose legs are combined by domination — clause (i))).

Two closure clauses for H.65's `RateSpecies Q K B c f := ∀ M, 1 ≤ M → f M ≤ K * M ^ B * (Q ^ (M − c))⁻¹`:

* `RateSpecies.of_le` — **domination**: a pointwise-smaller function inherits the species with the
  SAME constants;
* `RateSpecies.mono` — **constant inflation**: the species survives enlarging any of `K`, `B`, `c`
  (`K ≤ K'`, `B ≤ B'`, `c ≤ c'`), given `2 ≤ Q` and `0 ≤ K`.

DEPENDS: H.65 · mathlib `pow_le_pow_right₀`, `inv_anti₀`, `mul_le_mul`, `pow_pos`.

## Why the hypotheses are what they are

Inflating `c` is the only direction that is not visually obvious: the exponent `M − c` is NATURAL
subtraction, so `c ≤ c'` gives `M − c' ≤ M − c`, hence `Q ^ (M − c') ≤ Q ^ (M − c)` and — after
inverting, which reverses the inequality — `(Q ^ (M − c))⁻¹ ≤ (Q ^ (M − c'))⁻¹`. That is the
`c`-absorption step `EFF.GENIND.153` performs by hand, and it needs `1 < Q` (whence `2 ≤ Q`, the
only use of `hQ`) for the base to be non-shrinking, plus `0 ≤ K` to multiply the two monotonicities
together. `1 ≤ M` is what makes `M ^ B ≤ M ^ B'` for `B ≤ B'`; at `M = 0` the `B`-clause is false,
which is why `RateSpecies` quantifies over `M ≥ 1` in the first place.

## Teeth

None in the corpus — the closure is PROOF-ONLY. This node is the bookkeeping that makes H.71's
three-leg sum a one-line `RateSpecies` conclusion rather than three `calc` blocks.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **Clause (i), domination.** A function dominated by a species member on `M ≥ 1` is itself a
species member with the same constants — the combinator that merges `EFF.GENIND.152`(iii)'s two
regimes. -/
theorem RateSpecies.of_le {Q : ℕ} {K : ℝ} {B c : ℕ} {f g : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hg : ∀ M, 1 ≤ M → g M ≤ f M) : RateSpecies Q K B c g :=
  fun M hM => (hg M hM).trans (h M hM)

/-- **Clause (ii), constant inflation.** The species is monotone in each of its three constants:
enlarging the coefficient `K`, the polynomial degree `B`, or the exponent offset `c` weakens the
bound. The `c`-clause is `EFF.GENIND.153`'s head-leg absorption. -/
theorem RateSpecies.mono {Q : ℕ} (hQ : 2 ≤ Q) {K K' : ℝ} {B B' c c' : ℕ} {f : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hK : K ≤ K') (hK0 : 0 ≤ K) (hB : B ≤ B') (hc : c ≤ c') :
    RateSpecies Q K' B' c' f := by
  intro M hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by
    have h1 : (1 : ℕ) ≤ Q := by omega
    exact_mod_cast h1
  have hQ0 : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_one hQ1
  have hK'0 : (0 : ℝ) ≤ K' := hK0.trans hK
  -- The polynomial factor: `K * M ^ B ≤ K' * M ^ B'`.
  have hMB0 : (0 : ℝ) ≤ (M : ℝ) ^ B := by positivity
  have hpow : (M : ℝ) ^ B ≤ (M : ℝ) ^ B' := pow_le_pow_right₀ hM1 hB
  have hnum : K * (M : ℝ) ^ B ≤ K' * (M : ℝ) ^ B' := mul_le_mul hK hpow hMB0 hK'0
  have hnum0 : (0 : ℝ) ≤ K' * (M : ℝ) ^ B' := mul_nonneg hK'0 (by positivity)
  -- The exponential factor: natural subtraction reverses, then inversion reverses again.
  have hsub : M - c' ≤ M - c := by omega
  have hQpow : (Q : ℝ) ^ (M - c') ≤ (Q : ℝ) ^ (M - c) := pow_le_pow_right₀ hQ1 hsub
  have hinv : ((Q : ℝ) ^ (M - c))⁻¹ ≤ ((Q : ℝ) ^ (M - c'))⁻¹ :=
    inv_anti₀ (pow_pos hQ0 (M - c')) hQpow
  have hinv0 : (0 : ℝ) ≤ ((Q : ℝ) ^ (M - c))⁻¹ := inv_nonneg.mpr (pow_pos hQ0 (M - c)).le
  calc f M ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹ := h M hM
    _ ≤ K' * (M : ℝ) ^ B' * ((Q : ℝ) ^ (M - c'))⁻¹ := mul_le_mul hnum hinv hinv0 hnum0

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.RateSpecies.of_le
#print axioms Uniformity.Density.Induction.RateSpecies.mono

end AxCheck
