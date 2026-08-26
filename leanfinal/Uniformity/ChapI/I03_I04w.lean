/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I03
import Uniformity.ChapG.G54

/-!
# Uniformity.ChapI.I03_I04w — the `DrainageAt 2` / `MenuLawAt 3` public wrappers (2026-08-26)

**Unit CW1b** (Sonnet transcription tier), brief `runs/wave-b/brief_CW_wrappers.md`, source of
truth `docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md` (fleet rows `CHFD-N2A2`/`CHFD-N3A1`)
and `leanfinal/scratch/CHFD_probe.lean` (the machine-checked boundary this file promotes to
production).  An I.03/I.04-adjacent **appendix file, not a blueprint node** — the H09w/H89w/
H73w/F04w precedent, matching CW1a's `I02_I03w.lean` for the sibling unit.

Both wrappers below are byte-identical replays of already machine-checked proofs:

* `drainageAt_two : DrainageAt 2` replays `CHFD_probe.lean`'s `drainageAt_two`
  (itself the anonymous content of I.04's own note-node accounting for `a2` at `n=2`), via the
  landed `Uniformity.Density.drainage_two` (`Density/Drainage.lean:838`).  `DrainageAt` itself is
  landed at `Density/Statement.lean:118`; no new `Prop` is declared here (I.04's "no parallel
  drainage `Prop`" ruling, `I04_I12_I19_I22_NOTES_2026-08-20.md`, is respected — this only names a
  witness at the existing carrier).
* `menuLawAt_three : MenuLawAt 3` replays `CHFD_probe.lean`'s `menuLawAt_three`, packaging the
  landed five-type cubic menu `coveringMenu_three` (`ChapG/G54.lean:35`) with the mechanical
  `A1Family` label cells over `{c3split, c3linInert, c3inert, c3linRam, c3ram}`
  (`ChapG/G52.lean`), exactly as I.03's own `n=2` gate does one degree down
  (`ChapI/I03.lean:177-210`).

**No statement invention.**  `DrainageAt`/`MenuLawAt` are unchanged (`Density/Statement.lean`,
`ChapI/I03.lean`); the only plumbing addition is a local `private def a1LabelCell`, forced at
`r = 0` (ten fields, six `Fin 0`-indexed via `Fin.elim0`, `expConst = 0`, `visConst = 0`,
`coeff = 1`), since I.03's own `a1LabelCell` is `private` to that file and not importable from
here — identical in every field to both I.03's and CW1a's copies.
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- **`CHFD-N2A2`**: `a2` at `n = 2`, named.  Replays `CHFD_probe.lean`'s `drainageAt_two`
directly from the landed `drainage_two` (`Density/Drainage.lean:838`); `DrainageAt` is
`Density/Statement.lean:118`'s carrier, unaltered. -/
theorem drainageAt_two : DrainageAt 2 := by
  intro O _ _ _ _ _ σ
  exact drainage_two σ

/-- Mechanical `A1Family` label cell at `r = 0`: carries only the σ-label, all locus/stride/
exponent/visibility fields forced by `Fin.elim0`, the two free scalar fields set to the inert
placeholders `0`/`1`.  Local copy of I.03's own `private a1LabelCell`, unimportable across files. -/
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

/-- **`CHFD-N3A1`**: `a1` at `n = 3`, named.  The cubic menu half is already landed
(`coveringMenu_three`, `ChapG/G54.lean:35`); this supplies the mechanical A1 label family that
`MenuLawAt` additionally requests, over the five degree-3 types `c3split`, `c3linInert`,
`c3inert`, `c3linRam`, `c3ram` (`ChapG/G52.lean`), exactly as I.03's own `n = 2` gate does one
degree down (`ChapI/I03.lean:193-210`). -/
theorem menuLawAt_three : MenuLawAt 3 := by
  refine ⟨0,
    [a1LabelCell c3split, a1LabelCell c3linInert, a1LabelCell c3inert,
      a1LabelCell c3linRam, a1LabelCell c3ram],
    {c3split, c3linInert, c3inert, c3linRam, c3ram}, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with h | h | h | h | h <;> subst h <;> simp [a1LabelCell]
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h | h | h <;> subst h
    · exact ⟨a1LabelCell c3split, by simp, rfl⟩
    · exact ⟨a1LabelCell c3linInert, by simp, rfl⟩
    · exact ⟨a1LabelCell c3inert, by simp, rfl⟩
    · exact ⟨a1LabelCell c3linRam, by simp, rfl⟩
    · exact ⟨a1LabelCell c3ram, by simp, rfl⟩
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h | h | h <;> subst h
    exacts [c3_degrees.1, c3_degrees.2.1, c3_degrees.2.2.1,
      c3_degrees.2.2.2.1, c3_degrees.2.2.2.2]
  · intro O _ _ _ _ _
    exact coveringMenu_three

end Uniformity.Density

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.drainageAt_two
#print axioms Uniformity.Density.menuLawAt_three
