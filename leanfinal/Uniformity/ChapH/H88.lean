/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H88 — `CapBranch`, `capBranch`, and `GENH4-CAP`'s trichotomy

**Chapter H, NODE H.88** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.18`,
`LEMMA GENH4-CAP` as re-derived at `[r3, PE3 MINOR 1]` from `GENH4-3(i)`'s own "else (ii)").

The reader's exits at `dv0 = N` form a trichotomy with **pairwise-disjoint** antecedents
(`w := dv(A₁)`):

* **(a)** `N > 2w`, either parity → `twoSided`;
* **(b)** `N ≤ 2w` and `N` odd → `ram`;
* **(c)** `N ≤ 2w` and `N` even → `und`.

Landing the read as a **total function** `capBranch` with a proved trichotomy makes overlapping
antecedents impossible to express — the structural fix for the repair history ledgered in the
source (an `r2` restatement dropped the RAM clause's one-side condition `N ≤ 2w`, producing
overlapping antecedents).  `capBranch_seven_three` is the Lean form of the committed refutation of
that ordering: at `(N, w) = (7, 3)` the refuted ordering says `ram`, the correct trichotomy says
`twoSided` (matching the committed counter-key artifact `2SIDED(3,4) = 384` versus the refuted
prediction `512 / 0`).

DEPENDS: none.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The three exits of the `dv0 = N` boundary read, with PAIRWISE-DISJOINT antecedents
(`GENH4-CAP`, as re-derived at `[r3, PE3 MINOR 1]` from `GENH4-3(i)`'s own "else (ii)"). -/
inductive CapBranch where | twoSided | ram | und
  deriving DecidableEq

/-- **NODE H.88.** The boundary read as a total function of `(N, w)`: the two-sided exit when
`2w < N`, otherwise the ramified exit on odd `N` and the undecided exit on even `N`. -/
def capBranch (N w : ℕ) : CapBranch :=
  if 2 * w < N then .twoSided else if N % 2 = 1 then .ram else .und

/-- **NODE H.88.** The trichotomy: each of the three exits is characterized by its own
pairwise-disjoint antecedent. -/
theorem capBranch_trichotomy (N w : ℕ) :
    (capBranch N w = .twoSided ↔ 2 * w < N) ∧
    (capBranch N w = .ram ↔ (N ≤ 2 * w ∧ N % 2 = 1)) ∧
    (capBranch N w = .und ↔ (N ≤ 2 * w ∧ N % 2 = 0)) := by
  unfold capBranch
  split_ifs with h1 h2 <;> simp only [true_iff, false_iff] <;> omega

/-- **NODE H.88.** The refuted `r2` ordering (which put "`N` odd ⟹ RAM" first, dropping the
one-side condition) sends `(N, w) = (7, 3)` to the ramified exit; the correct trichotomy sends it
to the two-sided exit. -/
theorem capBranch_seven_three : capBranch 7 3 = .twoSided := by decide

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.capBranch
#print axioms Uniformity.Density.Induction.capBranch_trichotomy
#print axioms Uniformity.Density.Induction.capBranch_seven_three

end AxCheck
