/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B16

/-!
# Uniformity.ChapB.B34 — purity: the polygon is one side, end to end

**Chapter B, NODE B.34** [def] (`blueprint/CHAP-B_leaf_layer.md` §5, the one-sided /
initial-form layer), ENV-A. One signed declaration, definitional.

*The initial form of a one-sided polynomial.* `f` is **`(u,ℓ)`-pure** when B.16's on-side
predicate holds at **both** ends of the abscissa range: at `0` and at
`f.natDegree / φ.natDegree`. Equivalently `sideSet φ f u ℓ` contains both endpoints, so the
`φ`-adic polygon of `f` is the single side of slope `−u/ℓ` spanning the whole range — there is
no second slope to split off. On such an `f` the initial form `resPoly π φ f u ℓ h H₀` (B.29)
is the whole residual datum, of degree `sideDeg φ f u ℓ h` with nonzero constant term (B.30).

Two conventions, both load-bearing:

* **The right endpoint is `f.natDegree / φ.natDegree`, not `f.natDegree`.** The development
  index runs to `μ = deg f / deg φ` (B.13's `dev φ f μ = 1`), so the abscissa range of the
  polygon is `0 … μ`; `f.natDegree` is the range `suppVal`'s `inf` is *taken over* (B.14), a
  deliberately over-wide uniform window, not the polygon's own right end. Writing
  `f.natDegree` here would assert on-sideness at an abscissa where the height is `⊤` (B.13's
  tail clause) whenever `φ.natDegree > 1`, which is never what a consumer wants.
* **Purity is stated at the two endpoints only**, not as "`sideSet` is all of `0 … μ`": the
  intermediate abscissae need not be on the side (they sit weakly above it), and B.17's
  `ℓ`-spacing says only the abscissae in one residue class mod `ℓ` can be on it at all. Two
  endpoints on one line of slope `−u/ℓ` is exactly "the polygon is that one side".

For a `(u,ℓ)`-pure monic `f` of degree `μ*m` the two clauses have a numerical consequence used
throughout §§6–7: B.13 gives `npHgt φ f μ = 0`, so `OnSide φ f u ℓ μ` reads
`ℓ • 0 + u*μ = suppVal φ f u ℓ`, i.e. `suppVal φ f u ℓ = u*μ` — the polygon's right endpoint
sits at height `0`, as `EFF.HE3.13`'s `A_μ = 1` requires. That consequence is *derived* where
it is needed (B.35, B.41, B.44), not built into this predicate.

DEPENDS: B.16 (`OnSide`, and through it B.11's `npHgt` and B.14's `suppVal`). The node's
DEPENDS line also names B.20 (`sideDeg`), B.29 (`resPoly`) and B.30 — those are the *initial
form* the statement glosses, consumed by B.35 and downstream; the predicate itself needs only
B.16, so only B.16 is imported.

**PROOF.** Definitional. Environment ENV-A (blueprint §0.1). The body is the gate-verified
`leanspec/Leanspec/ChapB.lean:564` stub body verbatim.

## Faithfulness

`EFF.HE6.32` step 1 and `EFF.HE3.32` both work "at a slope `λ`" with the block factor already
separated, i.e. on a pure polynomial; `docs/GMN_citations.md` Thm 1.15 phrases the conclusion
as "`N_φ(F_i)` one-sided of slope `λ_i`". `IsPure` is that conclusion as a predicate: the
polygon of `f` consists of the single side of slope `−u/ℓ`.
**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

SOURCE: `docs/GMN_citations.md` Thm 1.15; `EFF.HE3.32`; `EFF.HE6.32`.

**TEETH.** Signed non-applicable (a definition).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.34 — purity.** `IsPure φ f u ℓ` : the `φ`-adic polygon of `f` is a single side of slope
`−u/ℓ` spanning the whole abscissa range `0 … f.natDegree / φ.natDegree`, i.e. B.16's on-side
predicate holds at both endpoints of that range. -/
def IsPure (φ f : Polynomial O) (u ℓ : ℕ) : Prop :=
  OnSide φ f u ℓ 0 ∧ OnSide φ f u ℓ (f.natDegree / φ.natDegree)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.IsPure
end AxCheck
