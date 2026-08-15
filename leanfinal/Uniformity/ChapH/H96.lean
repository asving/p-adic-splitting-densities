/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H95
import Uniformity.ChapG.G37

/-!
# Uniformity.ChapH.H96 — `package_two`: `P(2)` holds, UNCONDITIONALLY

**Chapter H, NODE H.96** (`blueprint/CHAP-H_general_induction.md` §13; source `EFF.GENIND.15`,
`THEOREM GENIND.B`'s base pins *"the proved bases `P(2)` (W-11/W12-L0) and `P(3)`
(HEX3+HMENU3)"*). *`P(2)` HOLDS, UNCONDITIONALLY — the base case, from chapter G.*

`InductionPackage 2` holds with `(K, B, c) = (1, 0, 0)`:

* the **menu** member is chapter G's `coveringMenu_two`, the three-type degree-2 menu
  `{splitType, inertType, ramType}`;
* the **rate** member is chapter G's exact law `undecidedSeq O 2 N = (1/q)^N` (`G.37`, resting on
  the headline count `undecidedCount O 2 N = q^N` at `G.36`), which gives
  `undecidedSeq O 2 M ≤ 1 * M^0 * (q^(M − 0))⁻¹` outright — with *equality*, not slack.

**⚠ THIS IS THE CHAPTER'S ONE UNCONDITIONAL PACKAGE, AND IT IS A CHAPTER-G PAYOFF.** Chapter G's
honesty item H-10 records that the exact `n = 2` law is genuinely new — `leanfinal` and `leancheck`
both previously carried only the lossy `≤ q^(3M)` at level `2M`. That exactness is what makes
`package_two` provable with `(K, B, c) = (1, 0, 0)`, the sharpest constants the species allows
(`EFF.GENIND.153` remarks that *"the `m = 2` closed forms realize `(K, B, c) = (1, 1, 1)` — the
ansatz is sharp at the ground instance"*; chapter H's constants here are sharper still because
chapter G's law is an equality rather than a bound). **If this node were missing, the chapter's
base case would be missing and H.98 would be vacuous** — so it is a gate as much as a theorem.

**ARITHMETIC AUDIT (recomputed fresh).** `undecidedSeq O 2 N = q^(−N)`: at `q = 2`, `N = 1..4`,
`1/2, 1/4, 1/8, 1/16`; the target `1 · N^0 · q^(−N)` is the same ✓ (equality). At `q = 3`:
`1/3, 1/9, 1/27, 1/81` ✓.

**⚠ DO NOT IDENTIFY WITH H.28's `m = 2` CLUSTER RATE.** H.28 bounds a *cluster* system,
`u(N)/Q^(2(N−1)) ≤ N · Q^(−(N−1))`; the rate here is a *full-space* statement (the level-`N`
undecided fraction of `Coeff O 2 N`). They are **different objects** and are not to be wired
together (§16 item 6).

**TEETH.** chapter G's `W11-T-DRAIN` (30 firings) and `W11-EXHAUST`/P-4 dispositions, both
**Lean theorem** at `G.36`/`G.37` → inherited here as a landed dependency.

DEPENDS: H.65 (`Induction.RateSpecies`), H.95 (`InductionPackage`) · landed **chapter G**
`Uniformity.Density.undecidedSeq_two_eq` (`ChapG/G37.lean`), `undecidedCount_two_eq`
(`ChapG/G36.lean`) · landed `Uniformity.Density.coveringMenu_two`, `undecidedSeq`, `residueCard`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

/-- **NODE H.96.** `P(2)` holds unconditionally, with constants `(K, B, c) = (1, 0, 0)`: the menu
is chapter G's `coveringMenu_two` and the rate is chapter G's exact drainage law
`undecidedSeq O 2 N = (1/q)^N`. -/
theorem package_two : InductionPackage 2 := by
  refine ⟨1, 0, 0, zero_le_one, ?_⟩
  intro O _ _ _ _ _
  refine ⟨⟨{splitType, inertType, ramType}, coveringMenu_two⟩, ?_⟩
  intro M _
  rw [undecidedSeq_two_eq, Nat.sub_zero]
  simp [one_div, inv_pow]

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.package_two

end AxCheck
