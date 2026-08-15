/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02
import Uniformity.ChapH.H73

/-!
# Uniformity.ChapH.H74 — the `μ = 2` leaf dictionary is degree-exhausting

**Chapter H, NODE H.74** (`blueprint/CHAP-H_general_induction.md` §11, the σ dictionary and the
`(e, f)`-forcing chain). Every one of the three σ-blocks of H.73's dictionary `stageSigma` has
total degree `2 · D′` with `D′ = keyDeg G = e₁ f₁` — the block degree of a `μ = 2` stage:

* `ram`: `(2e₁) · f₁ = 2e₁f₁` ✓
* `twoSided`: `e₁ f₁ + e₁ f₁ = 2e₁f₁` ✓
* `inert`: `e₁ · (2f₁) = 2e₁f₁` ✓

so the dictionary *exhausts* the block in every case: no leaf leaves degree unaccounted for, and
no leaf over-counts.

**Arithmetic audit (the four instance specializations of `EFF.GENHN.15`, recomputed fresh).**
`(e₁,f₁,μ) = (2,1,2)` → `{(4,1)}` / `{(2,1)²}` / `{(2,2)}`, each of degree `4 = 2·2` ✓.
`(1,2,2)` → `{(2,2)}` / `{(1,2)²}` / `{(1,4)}`, each `4` ✓.
`(3,1,2)` → `{(6,1)}` / `{(3,1)²}` / `{(3,2)}`, each `6 = 2·3` ✓.
`(1,3,2)` → `{(2,3)}` / `{(1,3)²}` / `{(1,6)}`, each `6` ✓.
All four have `Σ e·f = 2e₁f₁` over the multiset. Cross-check against `GENH4.C`'s two-genre
quartic dictionary (`EFF.GENH4.11`): genre E `(2,1,2)` gives `RAM ↦ {(4,1)}`,
`2SIDED ↦ {(2,1),(2,1)}`, `INERT ↦ {(2,2)}` — identical to the `(2,1,2)` row; genre F `(1,2,2)`
gives `{(2,2)}` / `{(1,2),(1,2)}` / `{(1,4)}` — identical to the `(1,2,2)` row. So `GENHN.C`
really is `GENH4.C` re-based.

**The structural parity facts are observations, not nodes.** `EFF.GENH4.11`'s audit notes that
*genre E always has even `e`* (every root has `v(θ) = h/2` with `h` odd, so `2 ∣ e`) and that
*genre F always has even `f`* (`F_{q²} ⊆ k_L`), and that every dictionary entry respects them.
Those are consequences of the *carrier* (H.76's hypotheses), so they enter here as remarks
verifiable by inspection of the audit above rather than as separate statements.

**Degree consistency is necessary, not sufficient.** This node proves the necessary half; the σ
*decision* (which leaf a given polynomial actually takes) stays with the executable regressions
`GN-SIGMA` (37,792 jobs / 0 bad against PARI `factorpadic`, including the wild `p = 3`, `e₁ = 3`
stage) and `GH-SIGMA` (6,185/0). Nothing here asserts that any particular polynomial has any
particular σ.

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.keyDeg`), H.73 (`StageLeaf`, `stageSigma`) ·
landed `FactorizationType.degree`.

SOURCE: `EFF.GENHN.15`'s own *arithmetic audit (rule 22)*, verbatim: *"The three rows are
degree-consistent with the block degree `2e₁f₁`: RAM gives `2e₁ · f₁ = 2e₁f₁` ✓; 2SIDED gives
`2 × (e₁ · f₁) = 2e₁f₁` ✓; INERT gives `e₁ · 2f₁ = 2e₁f₁` ✓."*

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **The `μ = 2` dictionary is degree-exhausting.** Each of the three σ-blocks of `stageSigma`
has total degree `2 · keyDeg G = 2 e₁ f₁`, the block degree of a `μ = 2` stage. -/
theorem stageSigma_degree (G : GenreDatum) (l : StageLeaf) :
    (stageSigma G l).degree = 2 * G.keyDeg := by
  cases l <;>
    simp [stageSigma, FactorizationType.degree, GenreDatum.keyDeg,
      Multiset.map_cons, Multiset.sum_cons] <;>
    ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.stageSigma_degree

end AxCheck
