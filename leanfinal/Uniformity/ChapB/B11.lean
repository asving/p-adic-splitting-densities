/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02
import Uniformity.ChapB.B07

/-!
# Uniformity.ChapB.B11 — `npHgt`, the height function of the `φ`-adic Newton polygon

**Chapter B, NODE B.11** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

For an order-1 key `φ` and any `f`, `npHgt φ f j : ℕ∞` is the Gauss valuation (B.07) of the
`j`-th `φ`-adic development coefficient (B.02): the height of the polygon's `j`-th support
point.

DEPENDS: B.02 (`dev`) · B.07 (`gaussVal`).

**PROOF.** Definitional.

**FAITHFULNESS.** This is the primary object of DECISION D-1. The corpus's polygon is "the
lower hull of `{(j, dv(A_j))}_{j ≤ μ}`" (`EFF.HE3.13`, `EFF.HE6.10`, `EFF.W12.23` all
verbatim); this node declares the *point set as a function* `j ↦ dv(A_j)`, and D-1 declares
that the hull is never formed. The `⊤` value replaces the corpus's convention of *omitting* an
abscissa from the support: a zero development coefficient has `dv = ∞`, which in the corpus's
own words is guarded away by the peel convention `EFF.HE6.09` ("a root `ρ` with `Φ′(ρ) = 0` has
`dv(Φ′(ρ)) = ∞` and carries NO finite side label"). Here nothing is guarded away: `⊤` is a
value of `ℕ∞`, an `inf` absorbs it, and the peel convention is a *consequence* (B.13's
`npHgt φ f μ = 0` plus B.20's finiteness), not an assumption.

**Flagged for human review as the chapter's central new definition** (parent CLAUDE.md trust
boundary).

SOURCE: `EFF.HE3.13`; `EFF.HE6.10`; `EFF.W12.23`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `npHgt φ f j` : the height of the `φ`-adic Newton polygon's `j`-th support point (`⊤` when
the `j`-th development coefficient vanishes, i.e. when the abscissa `j` carries no point). -/
noncomputable def npHgt (φ f : Polynomial O) (j : ℕ) : ℕ∞ := gaussVal (dev φ f j)

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt
end AxCheck

end Uniformity.Density.Leaf
