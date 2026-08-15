/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity

/-!
# Uniformity.ChapH.H33 — `two_mul_a_le_sideLen`, `two_mul_a_le_S`

**Chapter H, NODE H.33** (`blueprint/CHAP-H_general_induction.md` §6, ENV-H1). The domination
`b_S − a ≥ 1/2`, stated subtraction-free.

* `two_mul_a_le_sideLen`: `2 * (e * f) ≤ e * m * f` for `2 ≤ m` — i.e. `2a ≤ L`.
* `two_mul_a_le_S`: with `L ≤ S` in addition, `2 * (e * f) ≤ S` — i.e. `2a ≤ S`, which is the
  `(C2E.3)` domination `(S + 1)/2 − a ≥ 1/2`.

DEPENDS: none.

**⚠ WHY THE `2 *` FORM.** `b_S = (S + 1)/2` is a half-integer whenever `S` is even, and `ℕ`
division would floor it — the exact failure mode that would silently weaken `hprice` (H.09). Every
chapter-H statement about `b_S` is multiplied through by `2`; this node is what licenses that,
because `2a ≤ S` says exactly that `2 * (b_S − a) = S + 1 − 2a ≥ 1` is a genuine positive `ℕ`.

**SOURCE.** `EFF.GENIND.204` (`(C2E.3)`: "Since `L = eμγ ≥ 2eγ = 2a`,
`(S+1)/2 − a ≥ (L+1)/2 − a ≥ 1/2`"); `EFF.GENIND.189` (`(C2.0)`: `L ≥ 2a`).

**PROOF.** (i) `2 * (e*f) = e * 2 * f ≤ e * m * f` by monotonicity of multiplication in the middle
factor. (ii) transitivity of (i) with `hS`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `2a ≤ L`: the side length `L = e * m * f` dominates twice the area coordinate `a = e * f`
whenever the multiplicity `m` is at least `2`. NODE H.33(i). -/
theorem two_mul_a_le_sideLen {e f m : ℕ} (hm : 2 ≤ m) : 2 * (e * f) ≤ e * m * f := by
  have hrw : 2 * (e * f) = e * 2 * f := by ring
  rw [hrw]
  gcongr

/-- `2a ≤ S`: the `(C2E.3)` domination. With `L = e * m * f ≤ S` and `2 ≤ m`, twice the area
coordinate `a = e * f` is at most `S`, i.e. `(S + 1)/2 − a ≥ 1/2`. NODE H.33(ii). -/
theorem two_mul_a_le_S {e f m S : ℕ} (hm : 2 ≤ m) (hS : e * m * f ≤ S) :
    2 * (e * f) ≤ S :=
  le_trans (two_mul_a_le_sideLen hm) hS

section AxCheck
#print axioms Uniformity.Density.Induction.two_mul_a_le_sideLen
#print axioms Uniformity.Density.Induction.two_mul_a_le_S
end AxCheck

end Uniformity.Density.Induction
