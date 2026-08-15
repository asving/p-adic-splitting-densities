/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B21

/-!
# Uniformity.ChapB.B23 — the digit polynomial

**Chapter B, NODE B.23** (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual layer).
Source: `EFF.W12.23` (*"Each `a_j` is a free module of `N` digit-slots over the residue
`F_q`-space `F_q^d ≅ F_{q^d}` … write `digit_h(a_j) ∈ F_{q^d}` for the slot at height `h`"* — the
GMN order-1 residual-coefficient convention); `EFF.HE3.14`.

For `π : O`, `k : ℕ` and `a ∈ O[X]`, `digPoly π k a` is the coefficientwise digit of `a` at
height `k`, assembled back into a polynomial over the residue field:
`digPoly π k a = Σ_{i ≤ a.natDegree} C (digAt π k (a.coeff i)) * X ^ i`.

B.21 is the scalar digit `digAt`; this node is the *polynomial* half of the corpus's `digit_h`,
and B.28 pushes it into the residual field `F_{q^d}`.  When `π ^ k` divides every coefficient of
`a` — equivalently `(k : ℕ∞) ≤ gaussVal a`, B.08's reading — this is the reduction of `a / π ^ k`
mod `π`; that is B.24's `digPoly_eq_map`, and B.24 is also where the coefficient formula,
the degree bound and the vanishing criterion are proved.  Nothing here reads the junk branch of
`digAt`: the truncation at `a.natDegree` is harmless because `a.coeff i = 0` above it, which B.24
turns into `digAt π k (a.coeff i) = 0`.

DEPENDS: B.21 (`digAt`) · mathlib `Polynomial.C`, `Polynomial.X`, `Finset.range`.

**PROOF.** Definitional.  Environment ENV-A (blueprint §0.1).  The body is the gate-verified
`leanspec/Leanspec/ChapB.lean` stub body verbatim.

## Status

Sorry-free, axiom-free (Lean core only).  **Flagged for human review** (definition faithfulness).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.23 — the digit polynomial.** `digPoly π k a` : the coefficientwise digit of `a` at height
`k`, as a polynomial over the residue field.  When `π ^ k` divides every coefficient of `a`, this
is `(a / π ^ k) mod π`. -/
noncomputable def digPoly (π : O) (k : ℕ) (a : Polynomial O) :
    Polynomial (IsLocalRing.ResidueField O) :=
  ∑ i ∈ Finset.range (a.natDegree + 1), Polynomial.C (digAt π k (a.coeff i)) * Polynomial.X ^ i

section AxCheck
#print axioms Uniformity.Density.Leaf.digPoly
end AxCheck

end Uniformity.Density.Leaf
