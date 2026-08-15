/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H32 — the supporting-line sum

**Chapter H, NODE H.32** (`blueprint/CHAP-H_general_induction.md` §6). *The supporting-line sum.*
For `S H : ℕ`:

`2 · Σ_{r<S} (r+1)·H = S·(S+1)·H`.

This is the corpus's `Σ_{r=1}^{S} rH/S = (S+1)H/2 = b_S·H`, cleared of denominators: multiplying
through by `2S` and cancelling the `1/S` leaves exactly the `ℕ` identity above, which is the form
the pricing consumes.

DEPENDS: none (pure `ℕ` arithmetic; ENV-H1).

**SOURCE.** `EFF.GENIND.204` (`C2-G3`: *"Relative to the side's right endpoint, its `S`
coefficient columns have supporting-line heights `H/S, 2H/S, …, SH/S`"*), with the spec's audit
*"`Σ_{r=1}^{S} rH/S = (H/S)·S(S+1)/2 = (S+1)H/2` ✓ exact"*; `EFF.GENIND.189` (the same sum at
`S = L`, `(C2.2)`).

**THE CEILING TERM IS DELIBERATELY ABSENT.** `C2-G3`'s inequality carries an `O_m(1)` absorbing
ceiling errors, already-pinned level-zero digits and the residual-letter census. Chapter H carries
that slack as the `StageInterface.slack` field (H.09), so this node is the *identity* and the
*bound* is H.33's. Folding the `O_m(1)` in here would make the node unprovable — it is a
genre-dependent constant, not a formula.

**PROOF.** Induction on `S`: the successor step is `Finset.sum_range_succ` followed by `ring`.
(Equivalently `Finset.sum_mul` backwards plus Gauss's `Finset.sum_range_id_mul_two`; the direct
induction is shorter and avoids the index shift.)

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- *The supporting-line sum,* denominator-free: `2 · Σ_{r<S} (r+1)·H = S·(S+1)·H`. The corpus's
`Σ_{r=1}^{S} rH/S = (S+1)H/2` after clearing `2S`. -/
theorem two_mul_supportLine_sum (S H : ℕ) :
    2 * (∑ r ∈ Finset.range S, (r + 1) * H) = S * (S + 1) * H := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

section AxCheck
#print axioms Uniformity.Density.Induction.two_mul_supportLine_sum
end AxCheck

end Uniformity.Density.Induction
