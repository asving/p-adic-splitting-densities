/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H40 — the quartic f-first law `CS4-F(k)`, its floor, and the missing-floor witness

**Chapter H, NODE H.40** (`blueprint/CHAP-H_general_induction.md` §7). Defines
`lawF q N k = (q(q−1)/2)·q^{4N − 10k − 4}`, the quartic f-first genre's per-centre opening locus,
and lands two clauses about its visibility floor `4k + 1 ≤ N` (equivalently `4k ≤ N − 1`, read off
the entry heights `(4k, 3k, 2k, k)`, so `v(a₀) = 4k`):

* `lawF_exp_honest` — the floor implies `10k + 4 ≤ 4N`, i.e. the `ℕ`-subtraction in the exponent
  never truncates on the genre's own domain;
* `lawF_exp_neg_below_floor` — at `(N, k) = (2, 1)` the exponent is **negative over `ℤ`**
  (`4·2 − 10·1 − 4 = −6`), the sharpest signature of a missing floor: no `ℕ`-valued count can have
  a negative exponent, so the unfloored display returns `2^{−6}` against a true locus of `0`.

DEPENDS: none (pure arithmetic; ENV-H1).

**SOURCE.** `EFF.GENIND.49` (the law, and **ANNEX R R4**'s correction); `EFF.GENIND.163` (`R4.1`,
the floor re-derived from the heights `(4k, 3k, 2k, k)`); `EFF.GENIND.162` (`R4.0`, the finding);
`EFF.GENH4.06` (the same inequality as an *admissibility* condition `N ≥ 4k+1`, with the distinct
failure witness `(N,k) = (4,1)`). The two failure modes — visibility (the genre is empty below the
floor) and admissibility (the displayed slot-count form is wrong even where the genre is nonempty)
— are recorded separately in the blueprint but are the same inequality.

**PROOF.** (1) `lawF_exp_honest` by `omega` (`4N ≥ 16k + 4 ≥ 10k + 4`). (2)
`lawF_exp_neg_below_floor` by `norm_num`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- `CS4-F(k)` — the quartic f-first genre's per-centre opening locus,
`(q(q−1)/2)·q^{4N−10k−4}` (`GENIND` §S5.3; `#ψ = q(q−1)/2` monic irreducible quadratics). -/
def lawF (q N k : ℕ) : ℕ := (q * (q - 1) / 2) * q ^ (4 * N - 10 * k - 4)

/-- On the visibility floor `4k + 1 ≤ N`, `lawF`'s exponent is honest: `10k + 4 ≤ 4N`, so the
`ℕ`-subtraction `4N − 10k − 4` does not truncate. -/
theorem lawF_exp_honest {N k : ℕ} (hfl : 4 * k + 1 ≤ N) : 10 * k + 4 ≤ 4 * N := by
  omega

/-- Below the floor, at `(N, k) = (2, 1)`, the exponent is negative over `ℤ` — the missing-floor
witness: `4·2 − 10·1 − 4 = −6`. -/
theorem lawF_exp_neg_below_floor : (4 : ℤ) * 2 - 10 * 1 - 4 = -6 := by
  norm_num

section AxCheck
#print axioms Uniformity.Density.Induction.lawF
#print axioms Uniformity.Density.Induction.lawF_exp_honest
#print axioms Uniformity.Density.Induction.lawF_exp_neg_below_floor
end AxCheck

end Uniformity.Density.Induction
