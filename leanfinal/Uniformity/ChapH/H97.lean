/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H95
import Uniformity.ChapG.G54

/-!
# Uniformity.ChapH.H97 — `package_three_of_rate`: `P(3)` given the `n = 3` rate

**Chapter H, NODE H.97** (`blueprint/CHAP-H_general_induction.md` §13; sources `EFF.GENIND.15`
(the base `P(3)` (HEX3+HMENU3)), `EFF.GENIND.151` (the species instance *"the `n = 3` systems:
HEX3.B as displayed"*, i.e. `undecided/q^(3N) ≤ (1+N) q^(−N)` — polynomial coefficient,
exponential deficit), `EFF.GENIND.149` (the `o(1)`-is-not-a-rate finding), and `blueprint/CHAP-G`
honesty items H-1 and H-4). *The second base case: `InductionPackage 3` from the `n = 3` rate.*

The menu member is chapter G's five-type cubic menu `coveringMenu_three`
(`{c3split, c3linInert, c3inert, c3linRam, c3ram}`, `ChapG/G54.lean`); the rate member is the
hypothesis, with constants `(K, B, c) = (1, 1, 0)`, i.e. `undecidedSeq O 3 N ≤ N · q^(−N)`.

**⚠ BLUEPRINT DEFECT DECLARED AND CURED IN PLACE — `package_three_of_drainage` IS NOT LANDED.**
The node's committed SIGNATURE read

```
theorem package_three_of_drainage (hd : DrainageAt 3) : InductionPackage 3
```

and the blueprint itself proves that form **unprovable** from what exists:

1. chapter G's arithmetic layer gives `hex3U_le` (`hex3U q N ≤ N · q^(2N−2)`-shaped data,
   `ChapG/G69.lean`) and `hex3U_div_tendsto_zero` (`ChapG/G70.lean`), but the bridge turning that
   arithmetic layer into a statement about `undecidedCount O 3 N` is **chapter G's own named
   frontier** (its honesty item H-1) — so the rate cannot be sourced from chapter G alone;
2. the hypothesis `DrainageAt 3` supplies only `UndecidedVanishes O 3 σ`, a **limit**; a bare
   `o(1)` does not yield `RateSpecies` (`EFF.GENIND.149`'s own counterexample: `1/log(M+1)` is
   `o(1)` with no exponential rate).

Of the two sanctioned resolutions the blueprint **rejects** weakening `InductionPackage` to demand
only `UndecidedVanishes` (that is exactly `EFF.GENIND.149`'s failure, and would reproduce
`CODEX F3`), and **adopts** stating the node with the `n = 3` rate as an explicit hypothesis —
the form landed below. The hypothesis `hrate` **is** chapter G's named frontier, so the node turns
an unprovable claim into a *typed obligation*. `DrainageAt 3` is then a **consequence** and not a
hypothesis: `RateSpecies` with `B = 1`, `c = 0` forces `undecidedSeq O 3 N → 0`, hence
`gapSeq → 0` through the landed `gapSeq_le_undecidedSeq`. Per §15 rule 3,
`package_three_of_drainage` is **not signed and must not be landed**.

**⚠ THE `HYP.137` CARVE-OUT IS RESPECTED.** Chapter G's H-2/H-4: the tail-σ lemma is a NON-NODE
and the `n = 3` bound any downstream consumer uses is the **conservative** one
(`U₃^σ ≤ U₃^conv`). `hrate` is stated about `undecidedSeq`, the conservative object ✓ — so no
node here needs `HYP.137`.

**TEETH.** chapter G's `HEX3-LAW` (92 checks, 46 rows, with the note's own fit disclosure: the law
was FITTED on 14 of 29 pairs, so the independent force is the twelve never-measured pairs) →
executable regression, retained. The `hrate` hypothesis itself has **no teeth** and is the
frontier.

DEPENDS: H.65 (`Induction.RateSpecies`), H.95 (`InductionPackage`) · landed **chapter G**
`Uniformity.Density.coveringMenu_three` (`ChapG/G54.lean`) · landed `undecidedSeq`, `residueCard`,
`CoveringMenu`.

## Status

Sorry-free, axiom-free (Lean core only); CONDITIONAL on `hrate` (chapter G's declared frontier).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

/-- **NODE H.97, in the blueprint's ADOPTED form.** `P(3)` holds once the `n = 3` rate is
supplied: with `(K, B, c) = (1, 1, 0)` the menu member is chapter G's five-type cubic menu and the
rate member is the hypothesis `hrate` — chapter G's named frontier, made a typed obligation.

The superseded `package_three_of_drainage` is **not** landed: drainage is a limit, and
`InductionPackage` demands a rate (`EFF.GENIND.149`). -/
theorem package_three_of_rate
    (hrate : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      Induction.RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)) :
    InductionPackage 3 := by
  refine ⟨1, 1, 0, zero_le_one, ?_⟩
  intro O _ _ _ _ _
  exact ⟨⟨{c3split, c3linInert, c3inert, c3linRam, c3ram}, coveringMenu_three⟩, hrate O⟩

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.package_three_of_rate

end AxCheck
