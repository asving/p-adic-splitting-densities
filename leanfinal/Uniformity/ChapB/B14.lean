/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B11

/-!
# Uniformity.ChapB.B14 — `suppVal`, the cleared support value of the `φ`-adic polygon

**Chapter B, NODE B.14** [def] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

For an order-1 key `φ`, a polynomial `f`, and `u ℓ : ℕ`,
`suppVal φ f u ℓ : ℕ∞ = (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • npHgt φ f j + u * j)`.
For `0 < ℓ` this is `ℓ` times the corpus's support function at the slope `u/ℓ`:
`suppVal φ f u ℓ = ℓ · h_F(u/ℓ)` where `h_F(κ) = min_j (dv(A_j) + jκ)` is `EFF.HE3.31`'s `(★)`.
Clearing the denominator is what keeps the whole layer inside `ℕ∞`.

DEPENDS: B.11 (`npHgt`) · mathlib `Finset.inf`, the `ℕ∞` `AddCommMonoidWithOne` / `SMul ℕ`
structure.

**PROOF.** Definitional. Two choices are load-bearing and deliberate:

* `ℓ • x` rather than `(ℓ : ℕ∞) * x`, because scalar multiplication by a natural number on
  `ℕ∞` carries the `nsmul` simp set and avoids the `⊤ * 0` corner cases (`ℓ • ⊤ = ⊤` for
  `ℓ > 0`, and `0 • ⊤ = 0`, which is exactly why `0 < ℓ` is a hypothesis of every consumer);
* the range is `f.natDegree + 1`, uniform in `u` and `ℓ`, which by B.12's tail clause
  (`npHgt φ f j = ⊤` for `f.natDegree < j`) and B.08's `gaussVal_range` loses nothing.

**FAITHFULNESS.** The corpus's own two displays, both transcribed here at `e₁ = 1`:
`EFF.HE3.31` (byte-frozen, consumer-pinned by HE6 and HE7)
`h_F(κ) = min_j (dv(A_j) + jκ) = Σ_{slopes λ} L_λ · min(λ, κ)` and `EFF.HE6.17`(d)
`h_F(κ) := min_j (dv(A_j) + jκ)`. The *second* equality of `(★)` — the sum over slopes — is
**not** part of this definition; it is a theorem about it, and it is not a chapter-B node (it
belongs to the counting layer, chapters C/H).

**Flagged for human review; this is DECISION D-1's second object** (parent CLAUDE.md trust
boundary).

SOURCE: `EFF.HE3.31` (`(★)`, byte-frozen); `EFF.HE6.17`(d); `EFF.HE6.30` (`(†)`);
`EFF.HE3.22` (`LEMMA HE3-1′`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `suppVal φ f u ℓ` : the cleared support value of `f`'s `φ`-adic polygon at the slope
`−u/ℓ`, i.e. `ℓ` times the corpus's `h_F(u/ℓ) = min_j (dv(A_j) + j·u/ℓ)`. -/
noncomputable def suppVal (φ f : Polynomial O) (u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • npHgt φ f j + (u * j : ℕ))

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal
end AxCheck

end Uniformity.Density.Leaf
