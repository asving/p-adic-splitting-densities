/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H83 — the genre-F budgets, the free-digit total, and the node

**Chapter H, NODE H.83** (`blueprint/CHAP-H_general_induction.md` §12, the `n = 4` template). For
`k ≥ 1` and `N ≥ 4k + 1` the genre-F budget space has floors `v(α₁) ≥ k+1`, `v(α₀) ≥ 2k+1`,
`v(β₁) ≥ 3k+1`, `v(β₀) ≥ 4k+1`, so the four free-digit counts

`(N − k − 1) + (N − 2k − 1) + (N − 3k − 1) + (N − 4k − 1) = 4N − 10k − 4`,

**exactly** the entry exponent (no over- or undercount) — here stated in the subtraction-free form
`… + (10k + 4) = 4N`. The stage-initial node is `min(v(α₁) + k, v(α₀)) ≥ 2k+1`,
`min(v(β₁) + k, v(β₀)) ≥ 4k+1`, i.e. the W-11 node `C(2S+1, S+1)` at `S = 2k` — the same node shape
genre E reaches at `S = 2h`.

**Why `4k + 1 ≤ N` is a hypothesis and cannot be dropped.** Genre F requires `N ≥ 4k+1` (`v(B₀) =
4k` exact); below the floor the `ℕ`-subtractions truncate and the displayed count is simply false —
at `(N, k) = (4, 1)` the true slot count is `3` while `4N − 10k − 4 = 2`. The floor is at its true
minimum: the corpus row `(Zp, 7, 5, k1)` sits at equality `N = 5 = 4·1 + 1`, where the last
coordinate contributes zero free digits (`3 + 2 + 1 + 0 = 6 = 4·5 − 10 − 4`).

DEPENDS: none (both statements are `omega`).

SOURCE: `EFF.GENH4.15` (`LEMMA GENH4-1F`, the budget space and the W-11 node identification);
`EFF.GENH4.06`'s `[r2]` rider for the admissibility floor `N ≥ 4k+1`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The genre-F free-digit total: under the admissibility floor `4k + 1 ≤ N`, the four free-digit
counts sum to `4N − 10k − 4`, stated subtraction-free on the right. -/
theorem quartic_total_F {N k : ℕ} (hN : 4 * k + 1 ≤ N) :
    (N - k - 1) + (N - 2 * k - 1) + (N - 3 * k - 1) + (N - 4 * k - 1) + (10 * k + 4) = 4 * N := by
  omega

/-- The genre-F stage-initial node: `min(v(α₁) + k, v(α₀)) = 2k+1` and
`min(v(β₁) + k, v(β₀)) = 4k+1` at the budget floors — the W-11 node `C(2S+1, S+1)` at `S = 2k`,
with both minima attained twice. -/
theorem quartic_node_F (k : ℕ) :
    min ((k + 1) + k) (2 * k + 1) = 2 * k + 1 ∧ min ((3 * k + 1) + k) (4 * k + 1) = 4 * k + 1 := by
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.quartic_total_F
#print axioms Uniformity.Density.Induction.quartic_node_F

end AxCheck
