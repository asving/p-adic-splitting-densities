/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapB.B07 — `gaussVal`, the Gauss valuation of a polynomial

**Chapter B, NODE B.07** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

For `a ∈ O[X]`, `gaussVal a : ℕ∞` is the minimum of the `π`-valuations of the coefficients of
`a`, taken over `Finset.range (a.natDegree + 1)`. It is `⊤` exactly when `a = 0`, since every
coefficient of `0` has valuation `⊤`.

DEPENDS: mathlib `IsDiscreteValuationRing.addVal`
(`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`), `Finset.inf`.

**PROOF.** Definitional. `Finset.inf` (not `Finset.inf'`) is used deliberately: `ℕ∞` has
`OrderTop`, so `Finset.inf` is total and the empty-`Finset` corner is `⊤` rather than a side
condition. The range is `a.natDegree + 1` and not all of `ℕ`: coefficients above `natDegree`
vanish and would contribute `⊤`, which cannot lower an `inf`, so the truncation is harmless —
and B.08 proves it (`gaussVal_range`).

**Flagged for human review as a new definition** (parent CLAUDE.md trust boundary).

SOURCE: `EFF.HE6.10` verbatim ("`dv(A_j) := min_i(e₁ v(a_{j,i}) + i h)`", which at `e₁ = 1`,
`h = 0` is `min_i v(a_{j,i})`); `EFF.W12.23` verbatim ("`v(a_j) := min coefficient valuation =
the height of the lowest nonzero slot").

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open IsDiscreteValuationRing in
/-- `gaussVal a` : the minimum `π`-valuation of the coefficients of `a` (`⊤` iff `a = 0`). -/
noncomputable def gaussVal (a : Polynomial O) : ℕ∞ :=
  (Finset.range (a.natDegree + 1)).inf (fun i => addVal O (a.coeff i))

section AxCheck
#print axioms Uniformity.Density.Leaf.gaussVal
end AxCheck

end Uniformity.Density.Leaf
