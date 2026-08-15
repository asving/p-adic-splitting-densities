/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H23

/-!
# Uniformity.ChapH.H29 — the `uTwo` audit, at BOTH `q = 2` and `q = 3`

**Chapter H, NODE H.29** (`blueprint/CHAP-H_general_induction.md` §5, ENV-H1). Closed numeric
facts about the `m = 2` conservative complement `uTwo` (H.23), at two values of `Q`:

* `uTwo 2 · = 1, 2, 6, 12, 32, 64` for `N = 1, …, 6`;
* `uTwo 3 · = 1, 3, 15, 45, 189, 567` for `N = 1, …, 6`.

DEPENDS: H.23.

**SOURCE.** The values are the blueprint's own recomputation from `EFF.GENIND.150`'s recursion and
closed form (audited at H.25 and H.26); the corpus displays no `uTwo` table, only the symbolic legs.

**⚠ WHY THE `q = 3` COLUMN IS MANDATORY (the G.23 lesson).** Chapter G's `G.23` count formula was
refuted because the two candidate laws `q^{2N−2k−1}` and `q^{2N−2k−2}` agree exactly at `q = 2`, and
every numeric cross-check in that chapter ran at `q = 2`. The same trap is live here in three
places: `(Q − 1) = 1` at `Q = 2` kills every letter factor, so a missing or spurious `(Q − 1)` is
invisible; `Q^k` versus `Q^(k · c(m))` agree at `m = 2`; and the α-term's composition weights
coincide at `Q = 2` (H.20's audit). Hence both columns, as theorems.

**PROOF.** `uTwo` is compiled by well-founded recursion, so its defining equations are not
kernel-definitional and `decide` cannot close these (H.23's note). Unfolding is by the equation
lemmas (`simp [uTwo]`) together with `Finset.sum_range_succ` to expand the α-sum; `simp`'s
arithmetic normalisation then discharges each numeral.

**Relation to H.23's `#guard` block.** H.23 already gates the same twelve values through the
evaluator. This node upgrades them to kernel-checked theorems, which is what makes them a
regression: a future change to `uTwo`'s *definition* cannot pass silently.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **The `q = 2` column of the `uTwo` audit.** `uTwo 2 N` for `N = 1, …, 6`. NODE H.29(i). -/
theorem uTwo_audit_two :
    uTwo 2 1 = 1 ∧ uTwo 2 2 = 2 ∧ uTwo 2 3 = 6 ∧ uTwo 2 4 = 12 ∧ uTwo 2 5 = 32 ∧ uTwo 2 6 = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [uTwo, Finset.sum_range_succ]

/-- **The `q = 3` column of the `uTwo` audit** — the column that makes the audit informative:
at `Q = 2` the letter factor `(Q − 1)` is `1` and cannot be seen. NODE H.29(ii). -/
theorem uTwo_audit_three :
    uTwo 3 1 = 1 ∧ uTwo 3 2 = 3 ∧ uTwo 3 3 = 15 ∧ uTwo 3 4 = 45 ∧ uTwo 3 5 = 189 ∧ uTwo 3 6 = 567 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [uTwo, Finset.sum_range_succ]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.uTwo_audit_two
#print axioms Uniformity.Density.Induction.uTwo_audit_three

end AxCheck
