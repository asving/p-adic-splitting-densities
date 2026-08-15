/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B16
import Uniformity.ChapB.B20
import Uniformity.ChapB.B29

/-!
# Uniformity.ChapB.B73 — the descent-trigger predicate

**Chapter B, NODE B.73** [def] (`blueprint/CHAP-B_leaf_layer.md` §8, the order-1 type), ENV-C.
One signed declaration, definitional.

*The descent-trigger predicate.*  `NeedsDescent π φ f` holds when some side of `f`'s `φ`-adic
Newton polygon — a genuine side, i.e. one carrying at least two on-side abscissae — has a
**non-separable** residual polynomial.  That is exactly the situation in which the order-1 read
does not terminate: the residual factorization no longer separates the factors of `f` attached
to that side, and the algorithm must descend to a higher-order key.  By B.65, `¬ NeedsDescent`
is exactly the hypothesis of B.63.

The existential binds the slope `(u, ℓ)`, the side's nonemptiness witness `h` (needed to name
`sideMin`), and the left-endpoint height `H₀`; the four conjuncts before the negation are the
side's admissibility conditions — `0 < ℓ`, `Nat.Coprime u ℓ` (the slope in lowest terms),
`1 < (sideSet φ f u ℓ).card` (a *side*, not a single vertex), and the `H₀` pin.

DEPENDS: B.16 (`sideSet`) · B.20 (`sideMin`) · B.29 (`resPoly`, and through it `resCoeff`,
`resField`, `sideDeg`) · B.11 (`npHgt`, transitively) · mathlib `Polynomial.Separable`,
`Finset.card`.

**PROOF.** Definitional.  Environment ENV-C (blueprint §0.1) — note that ENV-C's extra
instances `[IsAdicComplete (maximalIdeal O) O]` and `[Finite (ResidueField O)]` are *not*
consumed by this definition and therefore, by Lean's auto-inclusion rule, do not appear in its
signature; the elaborated binder list is `{O} [CommRing O] [IsDomain O]
[IsDiscreteValuationRing O]`, byte-identical to the gate-verified
`leanspec/Leanspec/ChapB.lean` stub (checked against `#check @LeanspecB.NeedsDescent`).

## The `H₀` pin *[repaired: A-F.1 / PA-1]*

The body pins `H₀` at the side's **left endpoint**: `npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)`.
This is the PA-1 repair (blueprint AMENDMENT A-F.1, site 3 of four — B.63, B.65, B.73, B.74),
which replaced the pre-repair pin `npHgt φ f 0 = (H₀ : ℕ∞)` at exactly those four sites.  The
two pins agree on a pure one-sided polygon (whose only side contains abscissa `0`) and differ on
an interior side of a multi-slope polygon; under the old pin the predicate read a `resPoly` that
is `0` on such a side — never separable — so the repair is what makes `NeedsDescent` a faithful
trigger on multi-slope polygons rather than a vacuously-scoped one.  B.28/B.29/B.30 were already
stated under the `sideMin` pin and are untouched; B.75/B.76's abscissa-`0` reads are the
visibility API and are deliberately *not* repaired (GC-1's closing rider keeps the two APIs apart
by name).  B.77's `resPoly_congr` is convention-free by design (`H₀ < N` only), so it transports
this definition's residual polynomials unchanged.

## Faithfulness

`docs/GMN_citations.md` Lemma 3.11(3) at order 1: the order-1 read terminates on a side exactly
when that side's residual polynomial is separable.  `EFF.HE6R1.09`'s jump condition is the
**level-2** analogue and must not be conflated with this one (H-3).  The quarry has a declaration
of the same name (`lean/LeanUrat/OM/ResidualPolynomial.lean`'s `needsDescent`), but it is
`PadicValuation`-wired and is therefore **not** a quarry copy (H-6); the name coincidence is
deliberate and harmless, since the two live in different projects that are never in the same
environment.  **Flagged for human review** (definition faithfulness).

SOURCE: `docs/GMN_citations.md` Lemma 3.11(3); `EFF.HE3.15`; `EFF.W12.86` step 5.

**TEETH.** Signed non-applicable (a definition).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

-- ENV-A (blueprint §0.1): the polynomial arena.  ENV-C's `[IsAdicComplete (maximalIdeal O) O]`
-- and `[Finite (ResidueField O)]` are not consumed by this definition; see the module note.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.73 — the descent-trigger predicate.**  `NeedsDescent π φ f` : some side of `f`'s
`φ`-adic Newton polygon (at least two on-side abscissae, slope `−u/ℓ` in lowest terms) has a
residual polynomial that is not separable — the order-1 read does not terminate.  The height
`H₀` is pinned at the side's left endpoint `sideMin` *[repaired: A-F.1 / PA-1]*. -/
def NeedsDescent (π : O) (φ f : Polynomial O) : Prop :=
  ∃ (u ℓ : ℕ) (h : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ), 0 < ℓ ∧ Nat.Coprime u ℓ ∧
    1 < (sideSet φ f u ℓ).card ∧ npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) ∧
    ¬ (resPoly π φ f u ℓ h H₀).Separable

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.NeedsDescent
end AxCheck
