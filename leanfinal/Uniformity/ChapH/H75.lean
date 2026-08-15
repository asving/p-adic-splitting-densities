/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H06
import Uniformity.ChapH.H11
import Uniformity.ChapH.H12
import Uniformity.ChapH.H74

/-!
# Uniformity.ChapH.H75 — the `μ = 2` dictionary's instance table, as closed facts

**Chapter H, NODE H.75** (`blueprint/CHAP-H_general_induction.md` §11, the σ dictionary and the
`(e, f)`-forcing chain). H.73 defines the leaf dictionary `stageSigma` and H.74 proves it
degree-exhausting in general; this file pins the **instance rows** of `EFF.GENHN.15`'s table at the
chapter's own witness data, so the table is a closed fact rather than a specialization a reader has
to perform:

* `genreE2 t = (2; 2, 1, 2; 2t+1)`, the `(2,1,2)` row:
  `ram ↦ ⟨{(4,1)}⟩`, `twoSided ↦ ⟨{(2,1),(2,1)}⟩`, `inert ↦ ⟨{(2,2)}⟩`, each of degree `4 = 2·2`;
* `genreA2witness = (2; 3, 1, 2; 2)`, the `(3,1,2)` row: `ram ↦ ⟨{(6,1)}⟩`, degree `6 = 2·3`;
* `genreD2bwitness = (2; 1, 2, 2; 1)`, the `(1,2,2)` row: `ram ↦ ⟨{(2,2)}⟩`, degree `4 = 2·2`.

**Why these witness data.** `genreA2witness` is the `e₁ = 3` datum whose `RAM` block is `{(6,1)}` —
the wild `p = 3`, `e₁ = 3` cell that `GN-SIGMA` calls *"never-oracled territory"*, and where the
planted mutant `GN-T-SIG` (`E31 RAM σ {(6,1)} → {(3,2)}`) fired. Landing the dictionary value at
exactly that datum ties the σ layer to the one place the oracle's coverage is newest.
`genreD2bwitness` is genre F's datum `(1,2,2)`, so the third degree conjunct is `GENH4.C`'s F-row,
identical to the `(1,2,2)` row of `GENHN.C` — the re-basing claim of `EFF.GENHN.15`, checked here.

**⚠ σ VALUES ARE NOT EXECUTABLE — the project-wide finding F1** (blueprint AMENDMENT A-H.1/F1).
`DecidableEq FactorizationType` is `Classical.decEq` (`Density/LocalData.lean`), hence
noncomputable, so no `decide`/`#eval` can check a σ **value**: `stageSigma_genreE` below is proved
by `simp` unfolding the definitions and reducing the numerals, not by evaluation. Only the
**degree projections** (`ℕ`-valued, as in `stageSigma_degree_instances`) are numerically checkable,
and that is exactly the split the leanspec gate's executable section uses.

**Degree consistency is necessary, not sufficient.** Nothing here asserts that any particular
polynomial has any particular σ; the σ *decision* stays with the executable regressions `GN-SIGMA`
(37,792 jobs / 0 bad against PARI `factorpadic`, including the wild `p = 3` batch) and `GH-SIGMA`
(6,185/0, including 4,130 `q = 7` F-RAM members).

DEPENDS: H.06 (`genreE2`), H.11 (`genreA2witness`), H.12 (`genreD2bwitness`), H.73 (`StageLeaf`,
`stageSigma`), H.74 (`stageSigma_degree`) · landed `FactorizationType.degree`.

SOURCE: `EFF.GENHN.15`'s instance list (the four specializations at lines 1012–1016);
`EFF.GENH4.11` (the two-genre quartic dictionary, whose genre-E and genre-F rows coincide with the
`(2,1,2)` and `(1,2,2)` rows here).

TEETH: `GN-SIGMA`'s wild-`p = 3` batch · `GH-SIGMA`'s `q = 7` F-RAM members → **Lean theorem** for
the values.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **The genre-E row of the `μ = 2` dictionary**, at every `genreE2 t = (2; 2, 1, 2; 2t+1)`:
`ram ↦ ⟨{(4,1)}⟩`, `twoSided ↦ ⟨{(2,1),(2,1)}⟩`, `inert ↦ ⟨{(2,2)}⟩`. Proved by unfolding, not by
`decide`: σ values are not executable (finding F1). -/
theorem stageSigma_genreE (t : ℕ) :
    stageSigma (genreE2 t) .ram = ⟨{(4, 1)}⟩ ∧
    stageSigma (genreE2 t) .twoSided = ⟨{(2, 1), (2, 1)}⟩ ∧
    stageSigma (genreE2 t) .inert = ⟨{(2, 2)}⟩ :=
  ⟨by simp [stageSigma, genreE2], by simp [stageSigma, genreE2], by simp [stageSigma, genreE2]⟩

/-- **The degree projections of the three instance rows** — the numerically checkable half of the
instance table (`4`, `6`, `4`), each the block degree `2 · keyDeg` of its datum. -/
theorem stageSigma_degree_instances (t : ℕ) :
    (stageSigma (genreE2 t) .ram).degree = 4 ∧
    (stageSigma genreA2witness .ram).degree = 6 ∧
    (stageSigma genreD2bwitness .ram).degree = 4 :=
  ⟨by simp [stageSigma, genreE2, FactorizationType.degree],
   by simp [stageSigma, genreA2witness, FactorizationType.degree],
   by simp [stageSigma, genreD2bwitness, FactorizationType.degree]⟩

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.stageSigma_genreE
#print axioms Uniformity.Density.Induction.stageSigma_degree_instances

end AxCheck
