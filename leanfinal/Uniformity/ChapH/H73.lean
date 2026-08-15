/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H01
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H73 — `StageLeaf` and `stageSigma`, the `μ = 2` leaf dictionary

**Chapter H, NODE H.73** (`blueprint/CHAP-H_general_induction.md` §11, the σ dictionary and the
`(e, f)`-forcing chain). A `μ = 2` stage read decides one of three **σ-blocks**, and this file
names them (`StageLeaf`) and records the block each one contributes, relative to the ambient
genre datum `G = (Q; e₁, f₁, μ; h)`:

* `ram      ↦ ⟨{(2e₁, f₁)}⟩`
* `twoSided ↦ ⟨{(e₁, f₁), (e₁, f₁)}⟩`
* `inert    ↦ ⟨{(e₁, 2f₁)}⟩`

**Three labels, not five — and why.** The Y-trichotomy of `EFF.GENHN.38` has *five* geometric
cases (`RAM`, `2SIDED`, `SPLTAIL`, `SPLITEQ`, `INERT`) but only *three* σ-blocks: `SPLTAIL` and
`SPLITEQ` both reduce to a 2SIDED configuration for every lift (`SPLTAIL` by the undercut floor,
`SPLITEQ` by one refine step), so the dictionary's own grouping puts them in `twoSided`'s block.
`StageLeaf` is the **σ-valued** dictionary; the five-case read is geometric (it is the polygon's
hull position) and has no node here. Adding `spltail` / `splitEq` constructors would change the
contract.

The blocks are stated *relative to the ambient*; at towers one composes with the ambient's own
`(e, f)` — that composition is H.78's `composedSigma`.

Definitional, no proof obligation. The degree-conservation obligation that goes with a dictionary
of this shape is NODE H.74 (`(stageSigma G ℓ).degree = 2 * G.keyDeg`), and the σ *decision* itself
is carried by the executable regression `GN-SIGMA` against PARI `factorpadic`, not by this file.

DEPENDS: H.01 (`GenreDatum`) · landed `Uniformity.FactorizationType`.

SOURCE: `EFF.GENHN.15` (`THEOREM GENHN.C`, the dictionary verbatim: *"`stage-RAM ↦ {(2e₁·e_A,
f₁·f_A)} = {(2e₁, f₁)}`-block; `stage-2SIDED / SPLITEQ / SPLTAIL ↦ {(e₁, f₁), (e₁, f₁)}`;
`stage-INERT ↦ {(e₁, 2f₁)}`"*, with *"(blocks relative to the ambient; compose with the ambient's
own `(e, f)` at towers)"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The three decided leaf labels of a `μ = 2` stage read (`GENHN.C`; `SPLITEQ` and `SPLTAIL` share
`twoSided`'s σ-block, per the dictionary's own grouping). -/
inductive StageLeaf where
  | ram
  | twoSided
  | inert
  deriving DecidableEq, Fintype

/-- `GENHN.C`'s leaf dictionary, relative to the ambient. -/
def stageSigma (G : GenreDatum) : StageLeaf → FactorizationType
  | .ram      => ⟨{(2 * G.e₁, G.f₁)}⟩
  | .twoSided => ⟨{(G.e₁, G.f₁), (G.e₁, G.f₁)}⟩
  | .inert    => ⟨{(G.e₁, 2 * G.f₁)}⟩

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.StageLeaf
#print axioms Uniformity.Density.Induction.instDecidableEqStageLeaf
#print axioms Uniformity.Density.Induction.instFintypeStageLeaf
#print axioms Uniformity.Density.Induction.stageSigma

end AxCheck
