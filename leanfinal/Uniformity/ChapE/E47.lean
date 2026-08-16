/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E46

/-!
# Uniformity.ChapE.E47 — rung composition of leaves (associativity of the ladder product)

**Chapter E, NODE E.47** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws, the chapter's TERMINAL SUPPLY), ENV-E1 (the arithmetic arena: no local base
`O`).

Prepending one rung `(ℓ, g)` to a leaf's traversal path multiplies its composed invariants
componentwise — *the dictionary commutes with descending one level*:

* **leaf level** (`LadderLeaf.ef_prepend`):
  `(LadderLeaf.mk ((ℓ,g) :: p) t).ef e₀ f₀ = (LadderLeaf.mk p t).ef (e₀ * ℓ) (f₀ * g)`.
  This is why NODE E.45 carries the base pair `(e₀, f₀)` as an explicit argument instead of
  folding it into `path`: the extra rung can be moved OUT of the path and INTO the base, which
  is exactly `EFF.T2.21`'s child-carrier bookkeeping `e_child = e_𝒞 e′`, `f_child = f_𝒞 deg r′`.
* **dictionary level** (`ladderSigma_prepend`, the form chapter C's tower grammar consumes):
  `ladderSigma e₀ f₀ (leaves.map (prepend (ℓ,g))) = ladderSigma (e₀*ℓ) (f₀*g) leaves`.

Read right-to-left, the law says a σ-value computed by a CHILD read at the child's base pair is
the σ-value the PARENT read would emit after recording the jump — `EFF.HE7.16`(ii)'s level-`i`
composition, and (via CHAP-H's H-10 ruling) the composed-key σ composition that E consumes from
the GENHN side and nothing else.

## GC-4 (declared, and why nothing new is owed)

`LadderLeaf.prepend` is a map of dictionary DOMAIN objects (`LadderLeaf → LadderLeaf`), not a new
σ output: the only σ-values in this file are `ladderSigma` values, whose mandatory
degree-conservation lemma is **NODE E.46** (`ladderSigma_degree`), already landed and imported
here. `ladderSigma_prepend_degree` below is the corollary a consumer of the transport law wants —
it is E.46's invariant read through this law, not a second invariant.

## Executable-gate constraint (E-D10, in force)

`Uniformity.FactorizationType`'s `DecidableEq` is `Classical.decEq` (noncomputable), so no gate
may `decide` an equation between σ-VALUES — `decide` gets stuck on `Classical.choice`. The gates
below therefore state this node's own law on `.data` (`Multiset (ℕ × ℕ)`, a real instance) and on
`.degree` (`ℕ`), which is precisely the spelling NODE E.67's associativity spot check uses.

DEPENDS: E.45 (`LadderLeaf`, `LadderLeaf.ef`, `ladderSigma`), E.46 (`ladderSigma_degree`, for the
degree corollary) · mathlib `List.prod_cons`, `Multiset.map_map`, `Multiset.map_congr`.

SOURCE: `EFF.T2.21` (the child carrier's inherited invariants `e_child = e_𝒞 e′`,
`f_child = f_𝒞 deg r′` — prepending IS the child jump's bookkeeping); `EFF.HE7.16`(ii) (the
level-`i` composition); `EFF.GENHN.17`-side surviving composition formulas via CHAP-H H-10's
ruling (the composed-key σ composition is exactly this law).

TEETH: `he7rannex_supp.py` (level-3 σ = PARI, 79/79 — three-level compositions) → instance
evidence; the law itself is a **Lean theorem** (this file). The numeric gate below re-executes
the law at E.67's frame and at a three-level composition, on `.data`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.47.** *Prepending a rung to a leaf's path.* The traversal record grows at the FRONT
(`path` is in traversal order, outermost level first), and the terminal read is untouched: the
deciding separable-side factor of the emission does not change when a level is recorded above
it. A map of dictionary DOMAIN objects — a `LadderLeaf` is never a σ-value (GC-4). -/
def LadderLeaf.prepend (r : ℕ × ℕ) (l : LadderLeaf) : LadderLeaf :=
  ⟨r :: l.path, l.term⟩

/-- **NODE E.47, leaf level.** *One rung moves from the path into the base.* Prepending the rung
`r = (ℓ, g)` multiplies the composed invariants componentwise: `e` gains the factor `ℓ`, `f`
gains `g`. Equivalently, in the blueprint's `mk` spelling,
`(LadderLeaf.mk ((ℓ,g) :: p) t).ef e₀ f₀ = (LadderLeaf.mk p t).ef (e₀ * ℓ) (f₀ * g)`. This is
`EFF.T2.21`'s child bookkeeping and the reason E.45's base pair is an explicit argument. -/
theorem LadderLeaf.ef_prepend (r : ℕ × ℕ) (l : LadderLeaf) (e₀ f₀ : ℕ) :
    (LadderLeaf.prepend r l).ef e₀ f₀ = l.ef (e₀ * r.1) (f₀ * r.2) := by
  simp [LadderLeaf.prepend, LadderLeaf.ef, List.prod_cons, mul_assoc]

/-- **NODE E.47, dictionary level** (the consumed form). *The σ dictionary commutes with
descending one level*: reading a whole emission with the rung `r` recorded on every leaf is the
same σ-value as reading it at the base pair already multiplied by `r`. Chapter C's tower grammar,
the drainage recursions and H §11's `composedSigma` consume the law in this shape. -/
theorem ladderSigma_prepend (e₀ f₀ : ℕ) (r : ℕ × ℕ) (leaves : Multiset LadderLeaf) :
    ladderSigma e₀ f₀ (leaves.map (LadderLeaf.prepend r))
      = ladderSigma (e₀ * r.1) (f₀ * r.2) leaves := by
  refine Uniformity.FactorizationType.ext ?_
  change (leaves.map (LadderLeaf.prepend r)).map (fun l => l.ef e₀ f₀)
      = leaves.map (fun l => l.ef (e₀ * r.1) (f₀ * r.2))
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun l _ => LadderLeaf.ef_prepend r l e₀ f₀

/-- **NODE E.47, the degree corollary** (NODE E.46's invariant read through the transport law).
Degree conservation survives the descent: the degree of the prepended emission is the `e·f` sum
computed at the DESCENDED base. Nothing new is asserted — this is `ladderSigma_degree` (E.46)
rewritten along `ladderSigma_prepend`, supplied so consumers of the transport law need not
re-derive it. -/
theorem ladderSigma_prepend_degree (e₀ f₀ : ℕ) (r : ℕ × ℕ) (leaves : Multiset LadderLeaf) :
    (ladderSigma e₀ f₀ (leaves.map (LadderLeaf.prepend r))).degree
      = (leaves.map fun l =>
          (l.ef (e₀ * r.1) (f₀ * r.2)).1 * (l.ef (e₀ * r.1) (f₀ * r.2)).2).sum := by
  rw [ladderSigma_prepend, ladderSigma_degree]

end Uniformity.Density.Ladder

/-! ## Numeric gate — the composition law, evaluated

`#guard` fails elaboration when the checked `Bool` is `false`, so these run at build time. Per
E-D10 the σ-level identity is checked on `.data`, never between σ-VALUES; the leaf-level identity
is on `ℕ × ℕ` and the corollary on `ℕ`, both directly decidable. -/

section NumericGate

open Uniformity Uniformity.Density.Ladder

/-- The depth-0 leaf `⟨[], (1,2)⟩` of E.67's frame: prepending `(2,1)` to it is the depth-1 leaf
`⟨[(2,1)], (1,2)⟩`, which at base `(1,1)` composes to `(2, 2)` and at base `(2,1)` to `(4, 2)`. -/
private def leafTerm : LadderLeaf := ⟨[], (1, 2)⟩

/-- A depth-1 leaf, for the two-rung (three-level) composition below. -/
private def leafOne : LadderLeaf := ⟨[(1, 2)], (2, 1)⟩

-- Leaf level: the rung really moves from the path into the base (E.67's spot check).
#guard (LadderLeaf.prepend (2, 1) leafTerm).ef 1 1 == leafTerm.ef (1 * 2) (1 * 1)
#guard (LadderLeaf.prepend (2, 1) leafTerm).ef 1 1 == (2, 2)
#guard (LadderLeaf.prepend (2, 1) leafTerm).ef 2 1 == (4, 2)

-- The `mk` spelling of the blueprint STATEMENT, at the same data.
#guard (LadderLeaf.mk [(2, 1)] (1, 2)).ef 1 1 == (LadderLeaf.mk [] (1, 2)).ef (1 * 2) (1 * 1)

-- Two rungs, composed in both orders of application: prepend `(1,2)` then `(2,1)` versus
-- descending the base twice — the three-level composition `he7rannex_supp.py` checks.
#guard (LadderLeaf.prepend (2, 1) leafOne).ef 1 1 == leafOne.ef (1 * 2) (1 * 1)
#guard (LadderLeaf.prepend (2, 1) (LadderLeaf.prepend (1, 2) leafTerm)).ef 1 1
    == leafTerm.ef (1 * 2 * 1) (1 * 1 * 2)

-- Dictionary level, on `.data` (E-D10): E.67's associativity spot check.
#guard (ladderSigma 2 1 (({leafTerm} : Multiset LadderLeaf).map (LadderLeaf.prepend (2, 1)))).data
    == (ladderSigma (2 * 2) (1 * 1) {leafTerm}).data
-- A multi-leaf emission, and the empty one.
#guard (ladderSigma 1 1 (({leafTerm, leafOne, leafTerm} : Multiset LadderLeaf).map
      (LadderLeaf.prepend (3, 2)))).data
    == (ladderSigma (1 * 3) (1 * 2) {leafTerm, leafOne, leafTerm}).data
#guard (ladderSigma 1 1 ((0 : Multiset LadderLeaf).map (LadderLeaf.prepend (3, 2)))).data
    == (ladderSigma (1 * 3) (1 * 2) (0 : Multiset LadderLeaf)).data

-- The degree corollary, at the same frames (`.degree` is ℕ, directly decidable).
#guard (ladderSigma 2 1 (({leafTerm} : Multiset LadderLeaf).map (LadderLeaf.prepend (2, 1)))).degree
    == 8
#guard (ladderSigma 1 1 (({leafTerm, leafOne} : Multiset LadderLeaf).map
      (LadderLeaf.prepend (3, 2)))).degree
    == (ladderSigma (1 * 3) (1 * 2) {leafTerm, leafOne}).degree

-- NEGATIVE control: the rung is NOT free to land in the wrong component. Prepending `(2,1)`
-- and descending the base by the SWAPPED rung `(1,2)` disagree, so the law's pairing of
-- `r.1` with `e₀` and `r.2` with `f₀` is load-bearing.
#guard !((ladderSigma 1 1 (({leafTerm} : Multiset LadderLeaf).map (LadderLeaf.prepend (2, 1)))).data
    == (ladderSigma (1 * 1) (1 * 2) {leafTerm}).data)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.LadderLeaf.prepend
#print axioms Uniformity.Density.Ladder.LadderLeaf.ef_prepend
#print axioms Uniformity.Density.Ladder.ladderSigma_prepend
#print axioms Uniformity.Density.Ladder.ladderSigma_prepend_degree

end AxCheck
