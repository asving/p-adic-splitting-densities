/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I02
import Uniformity.ChapI.I03

/-!
# Uniformity.ChapI.I02_I03w — public `n = 2` witnesses for `DecidedSliceAt` and `MenuLawAt`
# (CHFD first-wave nodes CHFD-N2A0 / CHFD-N2A1)

**An I.02/I.03-adjacent appendix file, not a blueprint node** (the H09w/H89w/H73w/F04w
precedent). `docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md` records that `I02.lean:116-125`
and `I03.lean:177-210` already carry Lean-core, non-vacuous proofs of `DecidedSliceAt 2` and
`MenuLawAt 2` — but only as anonymous `example`s inside their own carrier files. Those files are
frozen to "carrier + gate" per their own dispositions and are not touched here. This file gives
the two `n = 2` witnesses public names so later consumers (the `CapstoneHypotheses 2` assembly,
`leanfinal/scratch/CHFD_probe.lean`) can cite them instead of re-deriving anonymous gates.

**No statement invention.** Both bodies below are byte-identical replays of the named-in-map
proof scripts (`I02.lean:116-125`'s `example : DecidedSliceAt 2`, and `I03.lean:177-210`'s
`example : MenuLawAt 2`, themselves mirrored verbatim in `scratch/CHFD_probe.lean`'s
`decidedSliceAt_two`/`menuLawAt_two`). `a1LabelCell` is redeclared `private` here only because
I.03's own `a1LabelCell` is `private` to that file (I.03 disposition item 3) and therefore not
importable; the redeclaration is the identical ten-field record, forced at `r = 0` exactly as
I.03 documents (three free fields `expConst`/`visConst`/`coeff`, set to the same `0`, `0`, `1`).

## Disposition

* **Nothing new is asserted about the capstone.** Both `DecidedSliceAt` and `MenuLawAt` are I.02/
  I.03's own `Prop` carriers, imported unchanged; no axiom is declared, no cite is imported.
* **NOT owner-gated.** Pure transcription/naming of already-machine-checked content (map rows
  CHFD-N2A0, CHFD-N2A1); no new mathematical content crosses a trust boundary here.
* Does not touch `I02.lean`, `I03.lean`, any roll-up, `leanspec/`, or any `ChapC` file.
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- Local restatement of I.03's `private` `a1LabelCell` (I.03 disposition item 3): the ten-field
`A1Cell 0` record whose only non-forced fields are `expConst = 0`, `visConst = 0`, `coeff = 1`,
carrying nothing beyond the `σ`-label. Needed here only as plumbing for `menuLawAt_two` below,
since I.03's own declaration of the same name is `private` to that file. -/
private def a1LabelCell (σ : FactorizationType) : Induction.A1Cell 0 where
  offset := fun i => i.elim0
  stride := fun i => i.elim0
  stride_pos := fun i => i.elim0
  expCoeff := fun i => i.elim0
  expCoeff_pos := fun i => i.elim0
  expConst := 0
  visCoeff := fun i => i.elim0
  visConst := 0
  coeff := 1
  σ := σ

/-- **Public name for the CHFD-N2A0 witness** (map row `a0`, `I02.lean:116-125`): `DecidedSliceAt`
at `n = 2`, from Chapter G's landed `uniformityStatement_two` through the landed `n = 2` drainage
tie `genuineDensity_eq_decidedDensity_two`. Byte-identical proof script to I.02's own anonymous
gate and to `scratch/CHFD_probe.lean`'s `decidedSliceAt_two`. -/
theorem decidedSliceAt_two : DecidedSliceAt 2 := by
  intro σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := uniformityStatement_two σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, by rw [← genuineDensity_eq_decidedDensity_two]; exact h2⟩

/-- **Public name for the CHFD-N2A1 witness** (map row `a1`, `I03.lean:177-210`): `MenuLawAt` at
`n = 2`, at the real three-cell family `[a1LabelCell splitType, a1LabelCell inertType,
a1LabelCell ramType]` over the menu `{splitType, inertType, ramType}`, closed by landed
`coveringMenu_two`. Byte-identical proof script to I.03's own anonymous gate and to
`scratch/CHFD_probe.lean`'s `menuLawAt_two`. -/
theorem menuLawAt_two : MenuLawAt 2 := by
  refine ⟨0, [a1LabelCell splitType, a1LabelCell inertType, a1LabelCell ramType],
    {splitType, inertType, ramType}, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with h | h | h <;> subst h <;> simp [a1LabelCell]
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    · exact ⟨a1LabelCell splitType, by simp, rfl⟩
    · exact ⟨a1LabelCell inertType, by simp, rfl⟩
    · exact ⟨a1LabelCell ramType, by simp, rfl⟩
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    exacts [splitType_degree, inertType_degree, ramType_degree]
  · intro O _ _ _ _ _
    exact coveringMenu_two

end Uniformity.Density

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.decidedSliceAt_two
#print axioms Uniformity.Density.menuLawAt_two
