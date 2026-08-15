/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B11
import Uniformity.ChapB.B13a

/-!
# Uniformity.ChapB.B13b — the polygon's terminal point has height zero

**Chapter B, NODE B.13** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A — **part b of the mandated 2-way split** (`dev_top` in `B13a.lean`,
`npHgt_top` here).

*The top of the polygon.* Let `φ` be monic with `m := φ.natDegree > 0` and let `f` be monic
with `f.natDegree = μ * m`. Then `npHgt φ f μ = 0`: the abscissa `μ` carries a point of the
`φ`-adic Newton polygon and that point sits at height `0`. This is the corpus's terminal
point `(μ, 0)`, here a theorem rather than a convention.

DEPENDS: B.11 (`npHgt`) · B.13a (`dev_top`) · mathlib `IsDiscreteValuationRing.addVal_one`,
`Finset.range_one`, `Polynomial.coeff_one_zero`.

**PROOF.** `npHgt φ f μ = gaussVal (dev φ f μ)` by definition, and `dev φ f μ = 1` by B.13a.
So the claim is `gaussVal (1 : O[X]) = 0`: `(1 : O[X]).natDegree = 0`, so the `inf` of B.07
runs over `Finset.range 1 = {0}` and evaluates to `addVal O ((1 : O[X]).coeff 0) =
addVal O 1 = 0`.

SOURCE: `EFF.HE3.13` verbatim (*"`A_μ = 1`, `dv = 0`"*); `EFF.HE6.10` (*"`dv(A_μ) = 0`"*);
`EFF.W12.23` (the polygon includes the terminal point `(m, 0)`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The polygon's terminal point.** For `φ` monic of positive degree and `f` monic of degree
`μ * φ.natDegree`, the height of the `φ`-adic Newton polygon at the abscissa `μ` is `0`. -/
theorem npHgt_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) : npHgt φ f μ = 0 := by
  rw [npHgt, dev_top hφ hd hf hdeg, gaussVal]
  simp [Finset.range_one]

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt_top
end AxCheck

end Uniformity.Density.Leaf
