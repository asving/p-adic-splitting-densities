/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H39 — the four-summand exponent identity behind `lawE`

**Chapter H, NODE H.39** (`blueprint/CHAP-H_general_induction.md` §7). For `h = 2t + 1` (h odd)
and `N ≥ 4t + 3`, the four free-digit counts of the `(2,2)`-E stage sum to `lawE`'s exponent:

`(N − (t+1)) + (N − 1 − (2t+1)) + (N − (3t+2)) + (N − 1 − (4t+2)) = 4N − 10t − 8 = 4N − 5h − 3`,

stated subtraction-free by moving `10t + 8` to the left-hand side. The second clause is the
rewriting of the same exponent in the `h = 2t+1` substituted form.

DEPENDS: none (pure `ℕ` arithmetic; ENV-H1).

**SOURCE.** `EFF.GENIND.68` (`LEMMA GENIND-4`'s free-digit total — the no-over/undercount check),
with the same four-summand pattern at `EFF.GENIND.50` (`CS5-V1E2`).

**PROOF.** Both by `omega`: the hypothesis `4t + 3 ≤ N` clears every `ℕ`-subtraction
(`t+1 ≤ N`, `2t+2 ≤ N`, `3t+2 ≤ N`, `4t+3 ≤ N`).

Note the signature carries `h = 2t + 1` rather than `Odd h`: the corpus's summands `(h+1)/2` and
`(3h+1)/2` are only integers for odd `h`, and the substituted form keeps every summand a literal
`ℕ` expression that `omega` can see through.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- The four free-digit counts of the `(2,2)`-E stage, at `h = 2t + 1`, sum to `lawE`'s
exponent `4N − 10t − 8`; stated subtraction-free as a sum equal to `4 * N`. -/
theorem lawE_exp_four_summands {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    (N - (t + 1)) + (N - 1 - (2 * t + 1)) + (N - (3 * t + 2)) + (N - 1 - (4 * t + 2))
      + (10 * t + 8) = 4 * N := by
  omega

/-- `lawE`'s exponent at odd `h = 2t + 1`: `4N − 5h − 3 = 4N − (10t + 8)`. -/
theorem lawE_exp_odd {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    4 * N - 5 * (2 * t + 1) - 3 = 4 * N - (10 * t + 8) := by
  omega

section AxCheck
#print axioms Uniformity.Density.Induction.lawE_exp_four_summands
#print axioms Uniformity.Density.Induction.lawE_exp_odd
end AxCheck

end Uniformity.Density.Induction
