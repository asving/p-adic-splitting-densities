/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B20
import Uniformity.ChapB.B25

/-!
# Uniformity.ChapB.B28 — the residual coefficients of a side

**Chapter B, NODE B.28** (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual layer),
ENV-A. One signed declaration, definitional.

*The residual coefficients of a side.* Fix an order-1 key `φ`, a polynomial `f`, `u ℓ : ℕ` with
`0 < ℓ` and `Nat.Coprime u ℓ`, and a nonemptiness witness `h` for `sideSet φ f u ℓ`. Write
`j₀ := sideMin φ f u ℓ h` (B.20's left endpoint) and `d := sideDeg φ f u ℓ h`, and let `H₀ : ℕ`
be the natural number with `npHgt φ f j₀ = (H₀ : ℕ∞)`. The **`k`-th residual coefficient**
(`k ≤ d`) is

```
resCoeff k := resMk π φ (H₀ - u * k) (dev φ f (j₀ + ℓ * k))  ∈  resField φ,
```

i.e. the digit of the `(j₀ + ℓk)`-th development coefficient read at the **line** height
`H₀ − u·k`, pushed into the residual field. It is `0` exactly when the point at abscissa
`j₀ + ℓk` lies strictly above the `(u,ℓ)`-line — that correctness clause is B.30a
(`resCoeff_eq_zero_iff`), not this node.

**The height is `H₀ − u·k`, not `npHgt φ f (j₀ + ℓk)`.** This is the whole content of the
definition and it is the difference between the *line* and the *point*: the residual
coefficient reads every development coefficient at the height the side's line prescribes, so
that the coefficients above the line reduce to `0` and the ones on it do not.

`H₀` is passed as an **explicit argument** rather than extracted from `npHgt φ f j₀` inside the
definition, because extracting it needs the finiteness proof (`npHgt φ f j₀ ≠ ⊤`) and a `def`
must not carry a proof obligation. B.29's `resPoly` passes it through; B.30 pins it by the
hypothesis `hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)`.

Two further conventions, both upstream of this file and both load-bearing for consumers:

* the subtraction `H₀ - u * k` is **`Nat` truncated subtraction**; on the intended range
  `k ≤ d` the line height `H₀ − u·k` is a genuine natural number (B.30 supplies that), and
  outside it the truncation is harmless because the node is only ever consumed for `k ≤ d`;
* `H₀` is pinned at the side's **left endpoint** `sideMin`, so the side is traversed with the
  height *decreasing* by `u` per lattice step (slope `−u/ℓ`). B.28/B.29/B.30 share this pin.

DEPENDS: B.02 (`dev`) · B.11 (`npHgt`, for the `H₀` pin's meaning) · B.16 (`sideSet`) ·
B.20 (`sideMin`, `sideDeg`) · B.23 (`digPoly`, via `resMk`) · B.25 (`resMk`, `resField`).

**PROOF.** Definitional. Environment ENV-A (blueprint §0.1).

## §12 rule 6 FRAGILE

The declaration carries a **dependent `Nonempty` argument** (`h : (sideSet φ f u ℓ).Nonempty`
feeding `sideMin`) inside a `def` type, together with the `H₀` pin. Consumers must pass the
*same* `h` term or rewrite along `Subsingleton.elim`-style congruence; the stub gate flagged
this at B.20/B.28/B.29 and it recurs inside hypotheses downstream (B.71, B.79–B.83).

## Faithfulness

`EFF.HE3.14` verbatim (the coherent-construction pin): *"For the side of `P(F)` with slope
`λ = u/ℓ` in lowest terms, left endpoint `(j₀, κ₀)`, lattice abscissas `j₀ + ℓk`
(`k = 0, …, d_λ`; the line heights `κ₀ − ku ∈ ℤ`):
`R_λ(Z) := Σ_{k=0}^{d_λ} res(A_{j₀+ℓk}(θ) · n(u)(θ)^k / n(κ₀)(θ)) · Z^k`."*

At `e₁ = 1` the normalizer system `n(·)` is the pure power `n(k) = π^k` (`EFF.HE6.13`'s
`n(k) := x^{i₀(k)} π^{(k − i₀(k)h)/e₁}` with `i₀ = 0`, `h = 0`), so the argument of `res` is
`A_{j₀+ℓk} · π^{uk} / π^{κ₀} = A_{j₀+ℓk} / π^{κ₀−uk}` — verbatim this node with `κ₀ = H₀`.
**The `ϖ`-vs-`n(k)` discrepancy and its coset factor `η_θ^{−q(k)}` (`EFF.HE6.13` RIDER,
`EFF.HE6.15` as corrected by `EFF.HE6.58`) are invisible at `e₁ = 1`, where `q(k) = 0` and
`ϖ = π = n(1)`.** That is H-1's scope claim made concrete, and it is §14 item 4.
**Flagged for human review** (definition faithfulness).

SOURCE: `EFF.HE3.14` (the coherent construction); `EFF.HE6.11`; `EFF.W12.23`.

**TEETH.** THE WITNESS (`EFF.HE3.24`, a PARI-adjudicated flip between the *naive* and the
*coherent* `R_λ` at `(e₁,f₁) = (2,2)`, i.e. the naive normalization is **wrong** at `e₁ ≥ 2`)
→ **signed non-applicability at `e₁ = 1`**: the witness distinguishes naive from coherent
normalization only when `e₁ ≥ 2`, and `e₁ = 1` is out of its scope by construction. **This is
the chapter's most delicate teeth disposition and it is §14 item 4.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.28 — the residual coefficient.** `resCoeff π φ f u ℓ h H₀ k` is the `k`-th residual
coefficient of the `(u,ℓ)`-side of `f`'s `φ`-adic Newton polygon: the `(j₀ + ℓk)`-th
development coefficient (`j₀ = sideMin φ f u ℓ h`) read at the **line** height `H₀ − u·k` and
pushed into the residual field `resField φ`. -/
noncomputable def resCoeff (π : O) (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) (H₀ k : ℕ) : resField φ :=
  resMk π φ (H₀ - u * k) (dev φ f (sideMin φ f u ℓ h + ℓ * k))

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.resCoeff
end AxCheck
