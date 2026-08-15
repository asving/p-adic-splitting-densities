/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H43 — the quintic vertex-at-4 genre's vertex condition and first visibility

**Chapter H, NODE H.43** (`blueprint/CHAP-H_general_induction.md` §7). For `v₄ ≥ 1` and `h` odd
(written `h = 2t + 1`), lower-hull convexity at the vertex `(4, v₄)` requires the left slope `h/2`
to exceed the right slope `v₄`, i.e. `h > 2v₄`, i.e. `h ≥ 2v₄ + 1`. Under that vertex condition
the entry height `v₀ = v₄ + 2h` satisfies `v₀ ≥ 7` (minimised at `(v₄, h) = (1, 3)`), so the
visibility requirement `v₀ ≤ N − 1` makes the genre first visible at `N ≥ 8`.

DEPENDS: none (pure `ℕ` arithmetic; ENV-H1).

**SOURCE.** `EFF.GENIND.51` (the law and its `VERTEX CONDITION h ≥ 2v₄+1`, and the visibility
`v₀ = v₄ + 2h ≤ N−1`, first visible at `N = 8`), with §S14 claim group `C8`'s independent recount.
The pre-seal smoke's RED (a predicted `V4E2(1,1)` at `(Zp,2,4,n5)`) is exactly the `h < 2v₄+1`
violation this node's first clause rules out.

**NOTE — no `def` for this genre's law.** `EFF.GENIND.51`'s disposition is a *signed vacuity
disclosure*: the `(q−1)²q^{5N−5v₄−5h−4}` display is checked only in the negative direction
(PREDICTED-ABSENT), so chapter H lands the *conditions* (proved geometry, arithmetically
checkable) and deliberately does **not** define `lawV4E2`.

**PROOF.** All three by `omega`. For `v4e2_first_visible`, `hvc` gives `t ≥ v₄ ≥ 1`, hence
`v₄ + 2(2t+1) ≥ 1 + 2·3 = 7`; for `v4e2_needs_eight`, `7 ≤ N − 1` in `ℕ` forces `8 ≤ N`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- Hull convexity at the vertex `(4, v₄)`: for odd `h = 2t + 1`, the strict slope inequality
`2v₄ < h` is the integral condition `h ≥ 2v₄ + 1`. -/
theorem v4e2_vertex_condition {v₄ t : ℕ} (hv : 1 ≤ v₄) (h : 2 * v₄ < 2 * t + 1) :
    2 * v₄ + 1 ≤ 2 * t + 1 := by
  omega

/-- Under the vertex condition, the entry height `v₀ = v₄ + 2h` is at least `7`
(minimised at `(v₄, h) = (1, 3)`). -/
theorem v4e2_first_visible {v₄ t : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1) :
    7 ≤ v₄ + 2 * (2 * t + 1) := by
  omega

/-- Visibility `v₀ ≤ N − 1` together with the vertex condition forces `N ≥ 8`: the genre is first
visible at `N = 8`. -/
theorem v4e2_needs_eight {v₄ t N : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1)
    (hvis : v₄ + 2 * (2 * t + 1) ≤ N - 1) : 8 ≤ N := by
  omega

section AxCheck
#print axioms Uniformity.Density.Induction.v4e2_vertex_condition
#print axioms Uniformity.Density.Induction.v4e2_first_visible
#print axioms Uniformity.Density.Induction.v4e2_needs_eight
end AxCheck

end Uniformity.Density.Induction
