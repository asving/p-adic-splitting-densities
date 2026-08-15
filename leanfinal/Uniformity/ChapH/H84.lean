/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H84 — both quartic stage-initial nodes have the W-11 shape `(2S+1, S+1)`

**Chapter H, NODE H.84** (`blueprint/CHAP-H_general_induction.md` §12, the `n = 4` template). The
genre-E stage-initial node computed at H.82 is `(dv(A₀), dv(A₁)) = (4h+1, 2h+1)`, and the genre-F
node computed at H.83 is `(4k+1, 2k+1)`. Both are the pair `(2S+1, S+1)` — the E one at `S = 2h`
(stage units), the F one at `S = 2k` (`v₁`-units). One identity, two instantiations:

`(4h+1, 2h+1) = (2·(2h)+1, (2h)+1)` and `(4k+1, 2k+1) = (2·(2k)+1, (2k)+1)`.

**⚠ WHY THIS NODE EXISTS AT ALL, AND WHAT IT IS NOT.** The claim *"the composite stage's
stage-initial node is literally the `n = 2` refine node"* is the structural reason the corpus can
run W-11's laws inside the stage (`CANDIDATE GENIND-5`, `EFF.GENIND.70`). It is **not** a deep
fact — it is an arithmetic coincidence of the two `S`-substitutions — and landing it as a
triviality is the honest transcription: `EFF.GENIND.70` is a **CANDIDATE, NOT PROVED**, and this
file must not let the node coincidence look like evidence for the count-isomorphism. Nothing
below states or implies *"the stage read IS the W-11 read"* (honesty item H-5(5)); the content is
the arithmetic of the two substitutions and no more.

`w11_node_shape` is the naming lemma for the shape itself (a tautology, retained per the stub's
signed list for the roll-up's readability); `w11_node_E` and `w11_node_F` are the two
instantiations that carry the arithmetic.

DEPENDS: H.82 (the genre-E node `(4h+1, 2h+1)`), H.83 (the genre-F node `(4k+1, 2k+1)`) — both
are `ℕ`-arithmetic, so nothing is imported from them; the statements here are self-contained.

SOURCE: `EFF.GENIND.68` (*"the W-11 refine node `C(2S+1, S+1)` ON THE NOSE, in stage units"*, with
`S := 2h`); `EFF.GENH4.15` (*"= the W-11 node `C(2S+1, S+1)` at `S = 2k` in `v₁`-units"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The W-11 node shape `C(2S+1, S+1)`, named. A tautology: it exists only to fix the two
coordinates of the shape for the roll-up's readability. -/
theorem w11_node_shape (S : ℕ) : 2 * S + 1 = 2 * S + 1 ∧ S + 1 = S + 1 :=
  ⟨rfl, rfl⟩

/-- The genre-E stage-initial node `(4h+1, 2h+1)` is the W-11 node `(2S+1, S+1)` at `S = 2h`. -/
theorem w11_node_E (h : ℕ) : (4 * h + 1, 2 * h + 1) = (2 * (2 * h) + 1, (2 * h) + 1) := by
  simp only [Prod.mk.injEq, and_true]
  omega

/-- The genre-F stage-initial node `(4k+1, 2k+1)` is the W-11 node `(2S+1, S+1)` at `S = 2k`. -/
theorem w11_node_F (k : ℕ) : (4 * k + 1, 2 * k + 1) = (2 * (2 * k) + 1, (2 * k) + 1) := by
  simp only [Prod.mk.injEq, and_true]
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.w11_node_shape
#print axioms Uniformity.Density.Induction.w11_node_E
#print axioms Uniformity.Density.Induction.w11_node_F

end AxCheck
