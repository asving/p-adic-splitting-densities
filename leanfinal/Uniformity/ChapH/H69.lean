/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H69 — summing the two rate regimes over a child family and over genres

**Chapter H, NODE H.69** (`blueprint/CHAP-H_general_induction.md` §10, ENV-H1). Each of the `r`
children of a node contributes at most the UNIFORMIZED bound
`K · N^B · Q^(−(N − 1 − max c c₀))` — the GROWING regime's bound (H.67) and the BOUNDED regime's
bound (H.68) after both have been pushed to the common shape by `RateSpecies.mono` (H.66(ii)),
which is why the hypothesis is stated at the threshold `max c c₀`. Multiplying the child sum by an
arrangement count `p · N^m` (H.37's slope-tuple bound times the opaque arrangement factor `p̃(m)`)
gives

`(p · N^m) · Σ_i g i ≤ (r · p) · N^m · (K · N^B) · Q^(−(N − 1 − max c c₀))`,

i.e. exactly the consumed sentence's `O(poly(N) · Q^{−(N−c′)})` with `c′ = max(c, c₀)`.

DEPENDS: H.37, H.66, H.67, H.68 (all four are SEMANTIC suppliers — this node consumes no term of
any of them; the uniformization is the caller's job, see the ⚠ below) · mathlib `Finset.sum_le_sum`,
`Finset.sum_const`, `mul_le_mul_of_nonneg_left`.

SOURCE: `EFF.GENIND.152` (`GENIND-C1`(iv), verbatim: *"Summing (ii)–(iii) over children and (iv)
over genres: the recursion's β-part contributes `≤ m·p̃(m)·K·N^{m+B}·Q^{−(N−c′−1)}` relative mass,
`c′ = max(c, c₀)` — exactly the consumed sentence's `O(poly(N)·Q^{−(N−c)})`, now DERIVED from the
displayed (A2-RATE) + GENIND-3's fibration + the depth identity. ∎"*).

**⚠ `p̃(m)` IS OPAQUE HERE (H.37's fence).** The corpus's `p̃(m)` counts arrangement types — frame
grammar, chapter C, and NOT a chapter-H object. This node therefore takes the arrangement count
`p : ℕ` and the child count `r : ℕ` as bare parameters and proves only the bookkeeping inequality.
The conclusion's shape `poly(N) · Q^{−(N−c)}` is what `RateSpecies` (H.65) recognizes, and H.66's
`mono` is what converts the displayed constant into the species `(K'', m + B, c′)`.

**⚠ UNIFORMIZING THE TWO REGIMES IS THE CALLER'S JOB.** H.67's bound sits at threshold `c` and
H.68's at `c₀`; this node's hypothesis `hg` is already stated at `max c c₀`, which is what the
caller obtains by applying `RateSpecies.mono` (H.66(ii)) to the BOUNDED bound with `K' := max K 1`,
`B' := B`, `c' := max c c₀`. Nothing here re-derives that step, and nothing here assumes a relation
between `c` and `c₀`.

## The proof, in two moves

1. `Σ_i g i ≤ r · (K · N^B · Q^(−(N−1−max c c₀)))` — `Finset.sum_le_sum` termwise, then
   `Finset.sum_const` over `Finset.univ : Finset (Fin r)`, whose card is `r`.
2. multiply by the nonnegative `p · N^m` (`mul_le_mul_of_nonneg_left`) and regroup (`ring`).

**Signature note.** `hQ`, `hK`, `hN` and `hg0` are carried by the frozen signature but not consumed:
the inequality is pure ordered-field bookkeeping, needing only `hg` and the nonnegativity of the
cast factor `p · N^m` (automatic for ℕ-casts). The unused-variable linter is disabled for that
reason. In particular the conclusion holds even when the family is empty (`r = 0`: both sides are
`0 ≤ 0`) — no positivity hypothesis is smuggled in through the child count.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The signature is frozen by the blueprint/stub gate; `hQ`, `hK`, `hN`, `hg0` are carried but not
-- consumed by this proof, so the unused-variable linter is off.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- **NODE H.69, the family/genre sum.** Given `r` children each bounded by the uniformized rate
`K · N^B · Q^(−(N−1−max c c₀))` and an arrangement count `p · N^m`, the total relative mass is at
most `(r · p) · N^m · (K · N^B) · Q^(−(N−1−max c c₀))` — `GENIND-C1`(iv). -/
theorem rate_sum_over_family {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c c₀ N m p r : ℕ} (hK : 0 ≤ K)
    (hN : 1 ≤ N) (g : Fin r → ℝ) (hg0 : ∀ i, 0 ≤ g i)
    (hg : ∀ i, g i ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹) :
    (p * N ^ m : ℝ) * ∑ i, g i
      ≤ (r * p : ℝ) * (N : ℝ) ^ m * (K * (N : ℝ) ^ B) * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹ := by
  -- Move 1: the child sum against `r` copies of the common bound.
  have hsum : ∑ i, g i ≤ (r : ℝ) * (K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹) := by
    calc ∑ i, g i
        ≤ ∑ _i : Fin r, K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹ :=
          Finset.sum_le_sum fun i _ => hg i
      _ = (r : ℝ) * (K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  -- Move 2: multiply by the nonnegative arrangement count and regroup.
  have hp : (0 : ℝ) ≤ (p * N ^ m : ℝ) := by positivity
  calc (p * N ^ m : ℝ) * ∑ i, g i
      ≤ (p * N ^ m : ℝ) * ((r : ℝ) * (K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum hp
    _ = (r * p : ℝ) * (N : ℝ) ^ m * (K * (N : ℝ) ^ B) * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹ := by
        ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.rate_sum_over_family

end AxCheck
