/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Uniformity.ChapH.H23

/-!
# Uniformity.ChapH.H24 — the `uTwo` base values `u(1) = 1` and `u(2) = Q`

**Chapter H, NODE H.24** (`blueprint/CHAP-H_general_induction.md` §5). The two seed values of the
`m = 2` conservative complement `uTwo` (H.23):

* `uTwo_one : uTwo Q 1 = 1` — the window-1 boundary;
* `uTwo_two : uTwo Q 2 = Q` — the first step of the recursion, where the α-sum is empty (`k ≥ 1`
  forces `2k ≥ 2 > 1 = N − 1`, so no α-event is admissible) and only the head term `Q^{N−1} = Q`
  survives.

DEPENDS: H.23 (`uTwo`).

SOURCE: `EFF.GENIND.150` (*"iterating from `u(1) = 1`, `u(2) = Q`"*); `EFF.GENIND.160` (`R3.1`'s
window-1 clause `u_{m,d}(1) = total = 1`, and the two-way coherence check: the closed form
`u(2ℓ+1) = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}` returns `1` at `ℓ = 0`).

**⚠ DEPENDS COMPLETENESS (the G.31 lesson)** (blueprint). `uTwo_one` is the **window-1 boundary**
whose absence was `CODEX F2`, a CONFIRMED GAP (`EFF.GENIND.159`). It is a DEPENDS of H.26's closed
form (whose odd branch is anchored there) and of H.25's recursion at `N = 3` (which calls
`uTwo Q 1`). Both DEPENDS fields name it. H.22(ii) supplies the *reason* the value is `1` — at
`N = 1` the whole state space is the single DRAIN state, `q^{d m (N−1)} = q^0 = 1`; this node
supplies the value.

Both clauses hold at EVERY `Q : ℕ`, with no `2 ≤ Q` hypothesis: `uTwo Q 1 = 1` is the defining
equation, and the `u(2)` computation only needs the α-sum to be empty, which is an index fact
independent of `Q`. (At the degenerate `Q = 0, 1` the values `0` resp. `1` are still what the
recursion returns; nothing downstream reads them there.)

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.24(i), the window-1 boundary.** `uTwo Q 1 = 1`: at window `N = 1` the only state is
`a = 0`, which reads DRAIN (conservative UNDECIDED), so the conservative complement is the whole
one-point space. This is the value whose absence was `EFF.GENIND.159`'s confirmed scope gap. -/
theorem uTwo_one (Q : ℕ) : uTwo Q 1 = 1 := by
  rw [uTwo]

/-- **NODE H.24(ii), the first step.** `uTwo Q 2 = Q`: the head term contributes `Q^{N−1} = Q^1`,
and the α-sum is empty because every `k ≥ 1` violates the admissibility bound `2k ≤ N − 1 = 1`. -/
theorem uTwo_two (Q : ℕ) : uTwo Q 2 = Q := by
  rw [uTwo]
  -- `Σ_{k < 2} (if 1 ≤ k ∧ 2k ≤ 1 then … else 0) = 0`: `k = 0` fails `1 ≤ k`, `k = 1` fails
  -- `2 ≤ 1`.
  simp [Finset.sum_range_succ]

end Uniformity.Density.Induction

/-! ## Numeric gate — the two seed values across primes and prime powers.
`#guard` fails elaboration when the proposition evaluates to `false`, so this is a build-time check
on the recursion (`uTwo` is compiled by well-founded recursion, so `decide` cannot see through it;
the evaluator can). The stub's `q ∈ {2,3,5,7}` column for `uTwo_two`, plus the `Q = 4, 9` prime
powers (`Q = q^d` with `d > 1` is the intended reading of the argument). -/

section NumericGate

open Uniformity.Density.Induction

#guard [2, 3, 5, 7, 4, 9].all fun Q => uTwo Q 1 == 1

#guard [2, 3, 5, 7, 4, 9].all fun Q => uTwo Q 2 == Q

/-! Coherence with H.29's certified column: `uTwo 2 1 = 1`, `uTwo 2 2 = 2`, `uTwo 3 1 = 1`,
`uTwo 3 2 = 3` are the first two entries of each of the two audited rows. -/
#guard [uTwo 2 1, uTwo 2 2] == [1, 2]

#guard [uTwo 3 1, uTwo 3 2] == [1, 3]

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo_one
#print axioms Uniformity.Density.Induction.uTwo_two

end AxCheck
