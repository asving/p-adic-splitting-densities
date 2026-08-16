/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapE.E45 — `LadderLeaf`, `LadderLeaf.ef`, `ladderSigma`: the σ dictionary

**Chapter E, NODE E.45** [def] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws, the chapter's TERMINAL SUPPLY), ENV-E1 (the arithmetic arena: exponent and
height bookkeeping, no local base `O`) plus the landed kernel.

A **ladder leaf** is the numerical record of one terminal emission of the σ-ladder read:

* `path : List (ℕ × ℕ)` — the per-level jump data, one entry `(ℓᵢ, gᵢ)` per level traversed
  (value-index jump and residue-degree jump);
* `term : ℕ × ℕ` — the terminal read `(ℓ′, deg r′)` of the deciding separable-side factor.

Its `(e, f)` at base `(e₀, f₀)` is the composed product of the successive increments,

`leafEF (e₀, f₀) leaf = (e₀ · Π ℓᵢ · ℓ′, f₀ · Π gᵢ · deg r′)`,

which is `EFF.T2.31` clause 6's *"multiplying the successive displayed e- and f-increments"* and
THEOREM HE7.D's `e = e₁ℓ₁⋯ℓ_{i+1}`, `f = f₁g₁⋯g_{i+1}`, spelled at a base pair so that the rung
transport law (E.47/E.48) can descend one level by moving a factor from the path into the base.
The **dictionary** `ladderSigma` sends a multiset of leaves to its image under `leafEF`, read as
a factorization type.

## GC-4 conformance (declared)

* **Output carrier.** The landed `Uniformity.FactorizationType`
  (`Uniformity/Density/LocalData.lean:43`), by anonymous constructor against its landed
  definition — the CHAP-B `typeOf g = ⟨{(ℓ, m·d)}⟩` pattern. The landed constructor IS the raw
  multiset (`structure FactorizationType where data : Multiset (ℕ × ℕ)`), so no `.ext`
  adaptation is needed; no parallel type is introduced anywhere.
* **Spelling (defect E-D8, stage-0e gate).** The blueprint SIGNATURE and §0.3's name list write
  the carrier `Uniformity.Density.FactorizationType`; **that name does not resolve.**
  `FactorizationType`, `.degree`, `.ext`, `.degree_mk_add` live directly in `Uniformity`
  (only `typeOf`, `typeOf_degree`, `monicFactors`, `typeOf_mul` are in `Uniformity.Density`).
  Landed here at the resolving name, per E-D8's stub-side repair.
* **Named dictionary function.** `ladderSigma`, not an inline multiset expression.
* **Dictionary DOMAIN.** `LadderLeaf` is an allowed domain — a decidable, inductive-free record
  (`deriving DecidableEq`), never itself a σ-value.
* **Mandatory degree-conservation lemma.** `ladderSigma_degree` / `ladderSigma_degree_eq_deg`
  are **NODE E.46**, a separate node and file; they are deliberately NOT declared here (landing
  them twice would collide at the chapter roll-up). GC-4's invariant is nevertheless given
  teeth in this file NOW: the numeric gate below re-executes clause 1 of E.46
  (`(ladderSigma e₀ f₀ leaves).degree = Σ_leaves (ef).1 * (ef).2`) on concrete leaves, so the
  dictionary does not sit unchecked while E.46 is in flight.
* **Ordering / multiset normalization** is `HYP.12` [CORE-SET]; nothing here re-decides it. The
  σ-value is a `Multiset`, so leaf order in a `path` matters (it is a `List`, the traversal
  record) while leaf order in the emission does not.
* **Executable-gate constraint (defect E-D10).** `FactorizationType`'s `DecidableEq` is
  `Classical.decEq` (noncomputable), so no gate may `decide` an equation between σ-VALUES. The
  gates below therefore run on `.data` (`Multiset (ℕ × ℕ)` has a real instance) and on
  `.degree` (ℕ-equality) only.

DEPENDS: none chapter-E-internal · landed `Uniformity.FactorizationType`
(`Uniformity/Density/LocalData.lean:43`).

SOURCE: `EFF.T2.31` clause 6 (*"their ramification and residue degrees are obtained by
multiplying the successive displayed e- and f-increments"*); `EFF.HE7.48` (the composed
invariants display); `EFF.T2.33`–`.37` (the five instance dictionaries: `(e,f) = (e₁e_s,
f₁f_s)`, `(e₁ℓ, f₁ deg r)`, `(e₁ℓℓ₂, f₁ d_r deg r₂)`, `(e₁e₂ℓ₂, f₁f₂ deg r₂)`).

TEETH: Q1 (1,335 PARI σ agreements at `n = 8` — every one is a value of this dictionary) →
instance evidence; the dictionary itself is definitional, and E.46 is its mandatory invariant.
The gate below reproduces the μ₂ = 2 alphabet `{(8,1)}`, `{(4,2)}`, `{(4,1),(4,1)}`, each of
degree 8, as `ladderSigma` values.

## Status

Sorry-free, axiom-free (Lean core only). Definitional node: nothing is proved here.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.45.** *One terminal emission of the σ-ladder read* (the numerical shadow, D-E2).
`path` records one `(ℓᵢ, gᵢ)` jump pair per level traversed, in traversal order; `term` is the
terminal read `(ℓ′, deg r′)` of the deciding separable-side factor. This is a dictionary DOMAIN
only (GC-4): a σ-value is never a `LadderLeaf`. -/
structure LadderLeaf where
  /-- The per-level jump data `(ℓᵢ, gᵢ)`: value-index and residue-degree jumps, in traversal
  order. -/
  path : List (ℕ × ℕ)
  /-- The terminal read `(ℓ′, deg r′)` of the deciding separable-side factor. -/
  term : ℕ × ℕ
  deriving DecidableEq

/-- **NODE E.45.** *The composed `(e, f)` of a leaf at base `(e₀, f₀)*` — `EFF.HE7.48`'s
display, `e = e₀ · Πᵢ ℓᵢ · ℓ′` and `f = f₀ · Πᵢ gᵢ · deg r′`. Carrying the base as an explicit
argument (rather than folding it into `path`) is what lets the rung transport law descend a
level by moving one jump pair out of the path and into the base. -/
def LadderLeaf.ef (l : LadderLeaf) (e₀ f₀ : ℕ) : ℕ × ℕ :=
  (e₀ * (l.path.map Prod.fst).prod * l.term.1,
   f₀ * (l.path.map Prod.snd).prod * l.term.2)

/-- **NODE E.45.** *The σ dictionary* (GC-4): a multiset of ladder leaves, read at base
`(e₀, f₀)`, becomes the landed factorization type carrying their composed `(e, f)` pairs. This
is the chapter's terminal supply — what chapter H's §11 dictionary, the drainage recursions and
chapter F's σ-law faces consume from E. -/
def ladderSigma (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) :
    Uniformity.FactorizationType :=
  ⟨leaves.map fun l => l.ef e₀ f₀⟩

end Uniformity.Density.Ladder

/-! ## Numeric gate — the dictionary, evaluated

`#guard` fails elaboration when the checked `Bool` is `false`, so these run at build time. Per
defect E-D10 nothing here compares two σ-values directly: the checks are on `.data`
(`Multiset (ℕ × ℕ)`, a real `DecidableEq`) and on `.degree` (ℕ-equality). -/

section NumericGate

open Uniformity Uniformity.Density.Ladder

/-- Depth-0 leaf: no levels traversed, terminal read `(8, 1)`. -/
private def leafInert : LadderLeaf := ⟨[], (8, 1)⟩

/-- Depth-0 leaf: terminal read `(4, 2)` — the `e > 1 ∧ f > 1` letter of the μ₂ = 2 alphabet. -/
private def leafMixed : LadderLeaf := ⟨[], (4, 2)⟩

/-- Depth-0 leaf: terminal read `(4, 1)`; two of these make the split letter of degree 8. -/
private def leafHalf : LadderLeaf := ⟨[], (4, 1)⟩

/-- Depth-1 leaf: one traversed level `(ℓ₁, g₁) = (2, 1)`, terminal read `(ℓ′, deg r′) = (1, 2)`.
At base `(e₀, f₀) = (2, 1)` this composes to `e = 2·2·1 = 4`, `f = 1·1·2 = 2` — `EFF.HE7.48`'s
two-level display landing on the same `(4, 2)` letter. -/
private def leafTwoLevel : LadderLeaf := ⟨[(2, 1)], (1, 2)⟩

/-- Depth-2 leaf: levels `(2, 1)` then `(1, 2)`, terminal read `(2, 1)`. At base `(1, 1)` this
composes to `e = 1·(2·1)·2 = 4`, `f = 1·(1·2)·1 = 2`. -/
private def leafThreeLevel : LadderLeaf := ⟨[(2, 1), (1, 2)], (2, 1)⟩

-- `LadderLeaf.ef`: the composed invariants, on each leaf above.
#guard leafInert.ef 1 1 == (8, 1)
#guard leafMixed.ef 1 1 == (4, 2)
#guard leafTwoLevel.ef 2 1 == (4, 2)
#guard leafThreeLevel.ef 1 1 == (4, 2)
-- The base really is a base: scaling `(e₀, f₀)` scales the composed pair.
#guard leafThreeLevel.ef 3 5 == (12, 10)

-- The μ₂ = 2 alphabet as `ladderSigma` values, checked on `.data` (E-D10).
#guard (ladderSigma 1 1 {leafInert}).data == ({(8, 1)} : Multiset (ℕ × ℕ))
#guard (ladderSigma 1 1 {leafMixed}).data == ({(4, 2)} : Multiset (ℕ × ℕ))
#guard (ladderSigma 1 1 {leafHalf, leafHalf}).data == ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))

-- Each alphabet letter has degree 8 (`EFF.T2.30`'s `(FUND)` `|Ω| = ef`, summed).
#guard (ladderSigma 1 1 {leafInert}).degree == 8
#guard (ladderSigma 1 1 {leafMixed}).degree == 8
#guard (ladderSigma 1 1 {leafHalf, leafHalf}).degree == 8

-- GC-4's mandatory invariant (NODE E.46, clause 1) re-executed numerically on every frame
-- above, so the dictionary is not unchecked while E.46 is in flight:
--   `(ladderSigma e₀ f₀ leaves).degree = Σ_{l ∈ leaves} (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2`.
private def degreeConserved (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) : Bool :=
  (ladderSigma e₀ f₀ leaves).degree ==
    (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum

#guard degreeConserved 1 1 {leafInert}
#guard degreeConserved 1 1 {leafMixed}
#guard degreeConserved 1 1 {leafHalf, leafHalf}
#guard degreeConserved 2 1 {leafTwoLevel}
#guard degreeConserved 1 1 {leafThreeLevel}
#guard degreeConserved 3 5 {leafInert, leafMixed, leafHalf, leafTwoLevel, leafThreeLevel}
#guard degreeConserved 1 1 (0 : Multiset LadderLeaf)

-- Degenerate frames: the empty emission is the degree-0 type, and a zero base collapses `e`.
#guard (ladderSigma 1 1 (0 : Multiset LadderLeaf)).data == (0 : Multiset (ℕ × ℕ))
#guard (ladderSigma 1 1 (0 : Multiset LadderLeaf)).degree == 0
#guard (ladderSigma 0 1 {leafInert}).degree == 0

end NumericGate

/-! ## Axiom footprint

Definitional node: `#print axioms` on a `def` reports the footprint of its BODY, which is the
check that matters here (no classical choice sneaks into the dictionary through the landed
carrier). -/

section AxCheck

#print axioms Uniformity.Density.Ladder.LadderLeaf
#print axioms Uniformity.Density.Ladder.LadderLeaf.ef
#print axioms Uniformity.Density.Ladder.ladderSigma

end AxCheck
