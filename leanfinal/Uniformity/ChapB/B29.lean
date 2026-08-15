/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B20
import Uniformity.ChapB.B28

/-!
# Uniformity.ChapB.B29 — the residual polynomial

**Chapter B, NODE B.29** [def] (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual
layer), ENV-A. One signed declaration, definitional.

*The residual polynomial.* With the data of B.28 — an order-1 key `φ`, a polynomial `f`,
`u ℓ : ℕ`, a nonemptiness witness `h` for `sideSet φ f u ℓ`, and the left-endpoint height
`H₀` — the residual polynomial of the `(u,ℓ)`-side is

```
resPoly := Σ_{k ≤ d} C (resCoeff k) * Y^k  ∈  (resField φ)[Y],   d := sideDeg φ f u ℓ h.
```

It is `EFF.HE3.14`'s `R_λ(Z) = Σ_{k=0}^{d_λ} res(A_{j₀+ℓk} / π^{κ₀−uk}) · Z^k`, assembled from
B.28's coefficients: the sum runs over `Finset.range (d + 1)`, i.e. `k = 0, …, d` inclusive, one
term per on-side lattice abscissa `j₀ + ℓk`.

Three conventions inherited from B.28 and load-bearing here:

* the coefficient at index `k` is read at the **line** height `H₀ − u·k`, not at the point
  height `npHgt φ f (j₀ + ℓk)` — that is B.28's whole content, and it is why the terms above
  the side's line contribute `0`;
* `H₀` is pinned at the side's **left endpoint** `sideMin` (the GC-1 pin; A-F.1 confirms
  B.28/B.29/B.30 were already stated and proved under it and are untouched by the PA-1 repair
  of B.63/B.65/B.73/B.74). `H₀` stays an explicit argument, passed straight through from
  B.28, because extracting it from `npHgt φ f (sideMin φ f u ℓ h)` needs the finiteness proof
  and a `def` must not carry a proof obligation; B.30 pins it by hypothesis;
* the coefficient `resCoeff … k` is junk for `k > d`, but the sum never reads those indices.

**This node does NOT normalize to monic.** The corpus's "monic after normalization"
(`docs/GMN_citations.md` Def 2.21) is a choice of representative in the `K^×`-scaling orbit;
the two facts every consumer needs — `natDegree = d` and `coeff 0 ≠ 0` — are scaling-invariant
and are B.30. Monicity would force a division and buys nothing; the *factorization* statements
(B.48, B.63) are stated up to units, exactly as `EFF.HE3.32`'s `R_λ = Π_r r^{m_r}` is.

DEPENDS: B.20 (`sideDeg`) · B.28 (`resCoeff`, and through it `resField`, `resMk`, `dev`,
`sideMin`) · mathlib `Finset.range`, `Polynomial.C`, `Polynomial.X`.

**PROOF.** Definitional. Environment ENV-A (blueprint §0.1). The body is the gate-verified
`leanspec/Leanspec/ChapB.lean` stub body verbatim.

## §12 rule 6 FRAGILE

Like B.20 and B.28, the declaration carries the **dependent `Nonempty` argument**
`h : (sideSet φ f u ℓ).Nonempty` inside its type — twice over, once through `sideDeg` in the
summation range and once through `resCoeff`'s `sideMin`. Consumers must pass one and the same
proof term `h`, or rewrite along a congruence; the stub gate flagged this at B.20/B.28/B.29 and
it recurs inside hypotheses downstream (B.43's `hgg'`/`hhh'` quantify over `hne`, and B.71,
B.79–B.83 consume it).

## Faithfulness

`EFF.HE3.13`: *"a residual polynomial `R_λ ∈ K[Z]` of degree `d_λ` with `R_λ(0) ≠ 0`"*.
`docs/GMN_citations.md` Def 2.21 (at order 1): *"`R_{λ}(f)(y) := c_s + c_{s+e} y + … + c_{s+de}
y^d ∈ F_r[y]`, a monic (after normalization) degree-`d` polynomial … `c_s` and `c_{s+de}` are
always nonzero, so `R_λ(f)` has degree `d` and is never divisible by `y`"* — degree `d` and
nonvanishing constant term are **not** asserted here: they are B.30, and they need `IsKey φ`,
`Irreducible π`, `suppVal φ f u ℓ ≠ ⊤` and the `H₀` pin, none of which a `def` may carry.
The non-normalization is the deliberate choice recorded above.
**Flagged for human review** (definition faithfulness).

SOURCE: `EFF.HE3.13`; `EFF.HE3.14`; `docs/GMN_citations.md` Def 2.21; `EFF.HE6.11`.

**TEETH.** `W12-SHAPE`, `HE-SIG` → **executable regression** retained, not discharged here (the
batteries read `R_λ`'s factorization type per row; the reading is chapter B's §10 gate layer).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.29 — the residual polynomial.** `resPoly π φ f u ℓ h H₀` is `R_{u/ℓ}(f) ∈
(resField φ)[Y]`: the degree-`≤ sideDeg φ f u ℓ h` polynomial whose `k`-th coefficient is
B.28's residual coefficient `resCoeff π φ f u ℓ h H₀ k`, the `(sideMin + ℓk)`-th development
coefficient read at the side's line height `H₀ − u·k`. Not normalized to monic: `natDegree = d`
and `coeff 0 ≠ 0` are B.30. -/
noncomputable def resPoly (π : O) (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ) : Polynomial (resField φ) :=
  ∑ k ∈ Finset.range (sideDeg φ f u ℓ h + 1),
    Polynomial.C (resCoeff π φ f u ℓ h H₀ k) * Polynomial.X ^ k

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.resPoly
end AxCheck
