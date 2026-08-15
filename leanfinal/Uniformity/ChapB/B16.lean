/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B14

/-!
# Uniformity.ChapB.B16 — the side of a slope

**Chapter B, NODE B.16** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

For `u ℓ : ℕ` the abscissa `j` is **on the `(u,ℓ)`-side** of `f`'s `φ`-adic polygon when the
`j`-th support point attains B.14's cleared support value:
`ℓ • npHgt φ f j + u * j = suppVal φ f u ℓ`.  `sideSet φ f u ℓ` collects those abscissae as a
`Finset`, over the same uniform range `Finset.range (f.natDegree + 1)` that `suppVal` takes its
`inf` over.

Two declarations, both definitional:

* `OnSide` — the on-side predicate (a `Prop`, not a `Bool`: decidability is supplied
  classically at the one place it is needed);
* `sideSet` — the on-side abscissae as a `Finset`, by `Finset.filter` with `Classical`
  decidability.  The landed precedent for `open Classical in` inside a definition body is
  `Uniformity.Density.monicFactors` (`Density/TypeOf.lean:154`).

DEPENDS: B.11 (`npHgt`) · B.14 (`suppVal`) · mathlib `Finset.filter`, `Classical`.

**PROOF.** Definitional.

## Faithfulness

The corpus's on-side condition is `EFF.W12.23`'s three-way membership law, verbatim: "`j` a
**VERTEX** of `P`: `v(a_j) = P(j)` exactly and `digit_{P(j)}(a_j) ≠ 0`; `j` an **on-side lattice
point** (side `S`): `v(a_j) ≥ P(j)`, with `digit_{P(j)}(a_j)` = the residual coefficient `r_j`;
every other `j < m`: … `v(a_j) ≥ ⌈P(j)⌉`".  `OnSide` is the *first* clause's equality
`v(a_j) = P(j)` in cleared form; the *digit* half of the vertex clause is B.28's residual
coefficient and its nonvanishing is B.30.

The third clause (the "automatic ceiling") is not a condition at all in this representation:
`suppVal` is an `inf`, so `suppVal φ f u ℓ ≤ ℓ • npHgt φ f j + u * j` holds for every `j` in
range by definition, which is exactly "every point lies weakly above the polygon".  **That the
ceiling clause becomes vacuous is a real simplification and is claimed as such** (blueprint §14
item 3).

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

SOURCE: `EFF.W12.23`; `EFF.HE3.14` (the side's "lattice abscissas `j₀ + ℓk`").

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.16 (a) — the on-side predicate.** `OnSide φ f u ℓ j` : the abscissa `j` lies on the
side of slope `−u/ℓ`, i.e. the `j`-th support point attains the cleared support value. -/
def OnSide (φ f : Polynomial O) (u ℓ j : ℕ) : Prop :=
  ℓ • npHgt φ f j + (u * j : ℕ) = suppVal φ f u ℓ

/-- **B.16 (b) — the on-side abscissae, as a `Finset`.** Filtered out of the same uniform range
`Finset.range (f.natDegree + 1)` over which `suppVal` takes its `inf`, with `Classical`
decidability for the `Prop`-valued `OnSide`. -/
noncomputable def sideSet (φ f : Polynomial O) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (OnSide φ f u ℓ)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.OnSide
#print axioms Uniformity.Density.Leaf.sideSet
end AxCheck
