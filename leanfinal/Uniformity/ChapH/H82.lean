/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H82 — the genre-E budget floors and the stage-initial node

**Chapter H, NODE H.82** (`blueprint/CHAP-H_general_induction.md` §12, the `n = 4` template). At
odd `h = 2t + 1` (and `N ≥ 4t + 3`) the genre-E budget space has the four floors

`v(α₁) ≥ (h+1)/2 = t+1`, `v(α₀) ≥ h+1 = 2t+2`, `v(β₁) ≥ (3h+1)/2 = 3t+2`, `v(β₀) ≥ 2h+1 = 4t+3`,

which is `quartic_floors_E`: the corpus's four displayed floor *formulas* in `h`, evaluated at
`h = 2t+1`, agree with the four closed forms in `t` (the two `(·)/2` entries are `ℕ`-divisions,
exact because the numerators are even at odd `h`). The four free-digit counts then sum to
`4N − 5h − 3` (H.39).

`quartic_node_E` is the stage-initial node at those floors:

`min(2·(t+1) + (2t+1), 2·(2t+2)) = 4t+3 = 2h+1` and
`min(2·(3t+2) + (2t+1), 2·(4t+3)) = 8t+5 = 4h+1`,

i.e. the corpus's `dv(A₁) ≥ min(2h+1, 2h+2) = 2h+1 = S+1` and
`dv(A₀) ≥ min(4h+1, 4h+2) = 4h+1 = 2S+1`.

**The `β₁` min is attained twice, and that is why this is an equality node.** `EFF.GENIND.68`'s
audit records *"`β₁ = b₁ + sα₁`: `v ≥ min((3h+1)/2, h + (h+1)/2) = min((3h+1)/2, (3h+1)/2) =
(3h+1)/2` ✓ (the two are equal, so the min is attained twice — the display's `min` is exact)"*.
Landing the node as a `min` **identity** rather than as an inequality preserves that exactness; an
inequality-only statement would lose it.

**Arithmetic audit (recomputed at `h = 1` and `h = 3`).** `h = 1` (`t = 0`): floors `1, 2, 2, 3`;
node `min(2+1, 4) = 3 = 2h+1` ✓, `min(4+1, 6) = 5 = 4h+1` ✓. `h = 3` (`t = 1`): floors `2, 4, 5,
7`; node `min(4+3, 8) = 7 = 2h+1` ✓, `min(10+3, 14) = 13 = 4h+1` ✓. `h = 3` is the cell where
`GENH4.B`'s CORRECTION lives (H.47), so both floor sets are checked exactly where the corpus's slip
was.

DEPENDS: H.39 (the free-digit total) — both statements below are `omega` (`omega` handles `min` and
`ℕ`-division by the literal `2` natively).

SOURCE: `EFF.GENIND.68` (the budgets *"`v(α₁) ≥ (h+1)/2`, `v(α₀) ≥ h+1`, `v(β₁) ≥ (3h+1)/2`,
`v(β₀) ≥ 2h+1`"* and the node computation *"`dv(A₁) ≥ min(2·(h+1)/2 + h, 2(h+1)) = min(2h+1, 2h+2)
= 2h+1 = S+1`; `dv(A₀) ≥ min(2·(3h+1)/2 + h, 2(2h+1)) = min(4h+1, 4h+2) = 4h+1 = 2S+1`"*), with the
`[r1, PE1-M4]` repair of the sealed line's editing scar (both minima displayed, values unchanged).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The genre-E budget floors at odd `h = 2t + 1`: the corpus's floor formulas
`(h+1)/2, h+1, (3h+1)/2, 2h+1` evaluate to `t+1, 2t+2, 3t+2, 4t+3`. Both `ℕ`-divisions are exact,
the numerators being even at odd `h`. -/
theorem quartic_floors_E (t : ℕ) :
    (2 * t + 1 + 1) / 2 = t + 1 ∧ (2 * t + 1) + 1 = 2 * t + 2 ∧
    (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 ∧ 2 * (2 * t + 1) + 1 = 4 * t + 3 := by
  omega

/-- The genre-E stage-initial node at the budget floors: `dv(A₁) = min(2h+1, 2h+2) = 2h+1` and
`dv(A₀) = min(4h+1, 4h+2) = 4h+1` at `h = 2t + 1`. Stated as `min` *identities*, which records
that each minimum is attained (the `β₁` one twice). -/
theorem quartic_node_E (t : ℕ) :
    min (2 * (t + 1) + (2 * t + 1)) (2 * (2 * t + 2)) = 2 * (2 * t + 1) + 1 ∧
    min (2 * (3 * t + 2) + (2 * t + 1)) (2 * (4 * t + 3)) = 4 * (2 * t + 1) + 1 := by
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.quartic_floors_E
#print axioms Uniformity.Density.Induction.quartic_node_E

end AxCheck
