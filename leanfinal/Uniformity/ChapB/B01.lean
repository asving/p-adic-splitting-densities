/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapB.B01 — `IsKey`, the order-1 key data

**Chapter B, NODE B.01** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

An **order-1 key** over `O` is a monic `φ ∈ O[X]` of positive degree whose reduction
`φ.map (IsLocalRing.residue O)` is irreducible over the residue field. Write `m` for
`φ.natDegree`; since the reduction of a monic polynomial is monic of the same degree, `φ̄`
is monic irreducible of degree `m`.

This node records the *lift*, not the *type*: the type-of-order-zero is `φ̄`, recovered as
`φ.map (IsLocalRing.residue O)`. Two conventions are deliberately NOT imposed — (i) `φ̄ ≠ X`
(GN15 imposes it for key polynomials; this chapter does not, because `φ̄ = X` is the ordinary
Newton polygon, the one case where the landed `exists_monic_scaleRoots` read applies verbatim),
and (ii) irreducibility of `φ` itself over `O`, which follows from `irred` by
`Polynomial.Monic.irreducible_of_irreducible_map` and is derived where needed rather than assumed.

DEPENDS: none (mathlib `Polynomial.Monic`, `Irreducible`, `IsLocalRing.residue`).

**PROOF.** Definitional.

**Flagged for human review as a new definition** (parent CLAUDE.md trust boundary).

SOURCE: `EFF.W12.23`; `EFF.HE6.08` (at `e₁ = 1`); `docs/GMN_citations.md` Def 1.21.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `IsKey φ` : `φ` is monic of positive degree with irreducible reduction — an order-1 key. -/
structure IsKey (φ : Polynomial O) : Prop where
  /-- The key is monic. -/
  monic : φ.Monic
  /-- The key has positive degree. -/
  pos : 0 < φ.natDegree
  /-- The reduction of the key is irreducible over the residue field. -/
  irred : Irreducible (φ.map (IsLocalRing.residue O))

section AxCheck
#print axioms Uniformity.Density.Leaf.IsKey
end AxCheck

end Uniformity.Density.Leaf
