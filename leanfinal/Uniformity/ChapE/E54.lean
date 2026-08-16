/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E45
import Uniformity.Density.TypeOfInvariance

/-!
# Uniformity.ChapE.E54 — `ladderSigma_frame_invariant`: the `(FRAME)`/`(ORIGIN)` shell

**Chapter E, NODE E.54** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and the
transport laws), ENV-E1.

`EFF.T2.13`'s `(FRAME)` discipline, at the dictionary's use shape: *"Frame changes preserve factor
degrees, multiplicities, separability, and transported root classes. Literal coefficient strings
are not asserted to be invariant."* Together with `EFF.T2.14`'s `(ORIGIN)` (*"The factor `Y^ν` is
recorded and removed before the normalized residual is factored"*; *"A nonzero origin shift is not
silently discarded"*), this says: a frame change of the residual read — scalar `c ≠ 0`, variable
scale `b ≠ 0`, origin monomial `Y^ν` peeled off BEFORE factoring — leaves the emitted factor
DEGREES and MULTIPLICITIES alone, hence leaves `ladderSigma`'s inputs alone, hence leaves σ alone.

The node also anchors the twist-invariance clause of `EFF.HE7.08` (*"Every statement used below is
twist-invariant … vanishing/non-vanishing at a residue, degree, and the multiset of irreducible
factors up to `K₂^×`-scaling"*).

## ⚠ NODE-KIND NOTE — this lemma is thin BY DESIGN, and the blueprint says so

The signed statement is `congrArg`: given that the frame change induces the leaf-multiset equality
`h : leaves = leaves'`, σ is unchanged because `ladderSigma` is a function of that multiset alone.
That triviality is deliberate and is recorded in the blueprint's own SIGNATURE NOTE. Read honestly:

* **What this node proves.** That the σ dictionary depends on nothing beyond the `(deg, mult)`
  numerical shadow — so no frame-dependent datum can leak into a σ-value through `ladderSigma`.
  E.34's unit-multiplication action on roots is the relabelling bijection behind the shadow.
* **What this node does NOT prove.** That any particular frame change induces `h`. That is the
  INSTANCES' obligation: `EFF.T2.13`/`.14` are IMPORTED frame conversions and `EFF.T2.36`'s
  `R_{λ₂}(Z) = τ(H₀)·R̂(Z/δ)` instance belongs to chapter C. Nothing here discharges them.
* **Where the real teeth are.** At the `typeOf` level, in the LANDED kernel, and they are cited by
  name — see the citation gate below, which is `#check`ed so the citation cannot rot:
  `Uniformity.Density.typeOf_shift` (HYP.05, recentering `x ↦ x + c`, no side condition),
  `Uniformity.Density.typeOf_scaleRoots` (HYP.06, the `π`-power extraction) and
  `Uniformity.Density.typeOf_scale` (HYP.06 in the recursion's phrasing). Every instance that
  needs the polynomial-level move consumes one of those three, not this shell.

DEPENDS: E.45 (`ladderSigma`, `LadderLeaf`) · landed `typeOf_shift`, `typeOf_scaleRoots`,
`typeOf_scale` (cited, not consumed by the proof).

SOURCE: `EFF.T2.13` (`(FRAME)`, verbatim); `EFF.T2.14` (`(ORIGIN)`); `EFF.HE7.08`
(twist-invariance as the load-bearing scope fence, with tooth HE7-T-BADTWIST showing that dropping
the twist mispredicts σ).

TEETH: HE7-T-BADTWIST + the S7 HETOW frame gate / nonzero-origin tooth → dispositions at §13; the
chapter-E shell is a **Lean theorem**, thin by design.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.54.** *Frame/origin invariance of σ at the dictionary.* `ladderSigma` sees only the
leaf multiset — the `(deg, mult)` numerical shadow — so a frame change that fixes that shadow
(hypothesis `h`, which is what `EFF.T2.13`'s `(FRAME)` and `EFF.T2.14`'s `(ORIGIN)` supply on the
instance side) fixes σ. Thin by design: the mathematical content is the instances' obligation to
produce `h`, and the polynomial-level teeth are the landed `typeOf_shift` /
`typeOf_scaleRoots` / `typeOf_scale`. -/
theorem ladderSigma_frame_invariant (e₀ f₀ : ℕ) (leaves leaves' : Multiset LadderLeaf)
    (h : leaves = leaves') :  -- the shadow equality the frame change induces
    ladderSigma e₀ f₀ leaves = ladderSigma e₀ f₀ leaves' :=
  congrArg (ladderSigma e₀ f₀) h

end Uniformity.Density.Ladder

/-! ## Citation gate — the landed `typeOf`-level teeth exist at the shape claimed

The node's DEPENDS list cites three landed invariances by name. `#check` makes those citations
machine-verified rather than docstring folklore: if any is renamed or re-signed, this file stops
elaborating. Nothing below is used by the proof above. -/

section CitationGate

#check @Uniformity.Density.typeOf_shift
#check @Uniformity.Density.typeOf_scaleRoots
#check @Uniformity.Density.typeOf_scale

end CitationGate

/-! ## Numeric gate — σ is a function of the leaf multiset, and only of it

Two directions, both on `.data` per defect A-E.1/E-D10 (`FactorizationType`'s `DecidableEq` is
`Classical.decEq`, so no gate may `decide` an equation between σ-values):

* the invariance has content only through `h` — a frame change that permutes the emission (a
  `Multiset`, so order is not data) leaves σ fixed;
* the hypothesis is not idle — dropping it, σ genuinely moves, so this is not a vacuous shell
  masking a false general claim. -/

section NumericGate

open Uniformity Uniformity.Density.Ladder

/-- Depth-0 leaf with terminal read `(4, 1)`. -/
private def leafA : LadderLeaf := ⟨[], (4, 1)⟩

/-- Depth-1 leaf, one traversed level `(2, 1)`, terminal read `(2, 1)`: composes to `(4, 1)` at
base `(1, 1)` — the SAME shadow entry as `leafA`, reached through a different read history. -/
private def leafB : LadderLeaf := ⟨[(2, 1)], (2, 1)⟩

/-- Depth-0 leaf with terminal read `(4, 2)` — a different letter. -/
private def leafC : LadderLeaf := ⟨[], (4, 2)⟩

-- Order in the emission is not data (it is a `Multiset`), so a re-listed frame gives the same σ.
#guard (ladderSigma 1 1 {leafA, leafC}).data == (ladderSigma 1 1 {leafC, leafA}).data

-- Distinct read histories with the same composed `(e, f)` give the same σ entry.
#guard leafA.ef 1 1 == leafB.ef 1 1
#guard (ladderSigma 1 1 {leafA}).data == (ladderSigma 1 1 {leafB}).data

-- The hypothesis `h` is doing work: a different leaf multiset gives a different σ.
#guard !((ladderSigma 1 1 {leafA}).data == (ladderSigma 1 1 {leafC}).data)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.ladderSigma_frame_invariant

end AxCheck
