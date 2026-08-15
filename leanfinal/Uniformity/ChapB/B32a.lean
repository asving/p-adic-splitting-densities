/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02
import Uniformity.ChapB.B07

/-!
# Uniformity.ChapB.B32a — the ultrametric and additivity helpers of the representation bound

**Chapter B, NODE B.32, part (a) of the mandated 3-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5, "the representation bound (the carry lemma)"), ENV-A′.

This file carries the two structural facts the representation bound rests on, both of them
about *sums*:

* `le_gaussVal_of_forall_coeff` / `gaussVal_le_addVal_coeff` — the two readings of `gaussVal`
  as an infimum over **all** coefficient valuations (not only those below the degree: past the
  degree the coefficient is `0` and contributes `⊤`);
* `min_gaussVal_le_gaussVal_add` — the Gauss valuation is ultrametric,
  `min (gaussVal a) (gaussVal b) ≤ gaussVal (a + b)`. This is the blueprint's "private helper of
  two lines from B.08"; it is public here because parts (b) and (c) live in other files;
* `dev_add_of_monic` — the `φ`-adic development is **additive**:
  `dev φ (a + b) j = dev φ a j + dev φ b j`, since both halves of monic division are.

**THE LANDED ROUTE DEPARTS FROM THE BLUEPRINT'S PROOF SKETCH, AND THIS IS THE PLACE THAT
RECORDS IT.** The blueprint proves B.32 by a *carry induction*: replace `c` by
`c' t = (c t %ₘ φ) + (c (t-1) /ₘ φ)`, show the weighted `inf` does not drop, and induct on
`Σ_t (c t).natDegree`. The landed proof instead factors the same content through two
monotonicity laws for `suppVal` (part (b)):

* `suppVal` is ultrametric on sums — from `dev_add_of_monic` plus `min_gaussVal_le_gaussVal_add`
  here, applied abscissa by abscissa;
* `ℓ • gaussVal c + u * t ≤ suppVal φ (c * φ ^ t) u ℓ` — from B.31's
  `gaussVal_le_npHgt` and the index shift `dev φ (h * φ) (j+1) = dev φ h j`.

Composing them over `f = Σ_t c t * φ ^ t` gives the bound directly. The two routes prove the
same frozen statement; the landed one avoids the well-founded recursion on `Σ_t (c t).natDegree`
and needs no degree bookkeeping, which is why it is shorter. Nothing in the SIGNATURE, the
hypotheses, or the split count changes.

DEPENDS: B.02 (`dev`) · B.07 (`gaussVal`) · mathlib `IsDiscreteValuationRing.addVal_add`,
`IsDiscreteValuationRing.addVal_zero`, `Polynomial.add_modByMonic`,
`Polynomial.modByMonic_add_div`, `Finset.le_inf`, `Finset.inf_le`.

## Faithfulness

`EFF.W12.23` ("monic division gives the UNIQUE `Φ`-adic development") in its additive reading:
the development of a sum is the sum of the developments, so a `φ`-adic polygon can only be
*raised* by cancellation, never lowered.

SOURCE: `EFF.W12.23`; `EFF.W12.24` (the right-to-left sweep, read as an inequality).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsDiscreteValuationRing

-- ENV-A (blueprint §0.1): the polynomial arena. `hπ : Irreducible π` is not needed in this
-- file — every statement here is about the `inf`-shape of `gaussVal`, not about divisibility.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Lower bounds for `gaussVal`, from all coefficients at once.** A value below every
coefficient valuation is below the Gauss valuation. -/
theorem le_gaussVal_of_forall_coeff {v : ℕ∞} {a : Polynomial O}
    (h : ∀ i, v ≤ addVal O (a.coeff i)) : v ≤ gaussVal a := by
  simp only [gaussVal, Finset.le_inf_iff]
  exact fun i _ => h i

/-- **The Gauss valuation is below *every* coefficient valuation**, including those past the
degree (where the coefficient is `0` and the valuation is `⊤`). -/
theorem gaussVal_le_addVal_coeff (a : Polynomial O) (i : ℕ) :
    gaussVal a ≤ addVal O (a.coeff i) := by
  by_cases hi : i < a.natDegree + 1
  · simp only [gaussVal]
    exact Finset.inf_le (Finset.mem_range.2 hi)
  · rw [a.coeff_eq_zero_of_natDegree_lt (by omega), addVal_zero]
    exact le_top

/-- **The Gauss valuation is ultrametric.** `min (gaussVal a) (gaussVal b) ≤ gaussVal (a + b)`
— the blueprint's step-2 "sum bound". -/
theorem min_gaussVal_le_gaussVal_add (a b : Polynomial O) :
    min (gaussVal a) (gaussVal b) ≤ gaussVal (a + b) := by
  refine le_gaussVal_of_forall_coeff fun i => ?_
  rw [Polynomial.coeff_add]
  exact le_trans (min_le_min (gaussVal_le_addVal_coeff a i) (gaussVal_le_addVal_coeff b i))
    addVal_add

/-- Monic division distributes over sums on the quotient side too (mathlib has
`Polynomial.add_modByMonic` for the remainder side but no `add_divByMonic`). Private helper of
`dev_add_of_monic`. -/
private theorem add_divByMonic {φ : Polynomial O} (hφ : φ.Monic) (a b : Polynomial O) :
    (a + b) /ₘ φ = a /ₘ φ + b /ₘ φ := by
  refine mul_left_cancel₀ hφ.ne_zero ?_
  have h := modByMonic_add_div (a + b) φ
  have ha := modByMonic_add_div a φ
  have hb := modByMonic_add_div b φ
  rw [add_modByMonic] at h
  rw [mul_add]
  linear_combination h - ha - hb

/-- **The `φ`-adic development is additive.** Both halves of monic division are additive, and
`dev` is an iterate of them. -/
theorem dev_add_of_monic {φ : Polynomial O} (hφ : φ.Monic) (a b : Polynomial O) (j : ℕ) :
    dev φ (a + b) j = dev φ a j + dev φ b j := by
  induction j generalizing a b with
  | zero => exact add_modByMonic a b
  | succ j ih =>
    show dev φ ((a + b) /ₘ φ) j = _
    rw [add_divByMonic hφ]
    exact ih _ _

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.le_gaussVal_of_forall_coeff
#print axioms Uniformity.Density.Leaf.gaussVal_le_addVal_coeff
#print axioms Uniformity.Density.Leaf.min_gaussVal_le_gaussVal_add
#print axioms Uniformity.Density.Leaf.dev_add_of_monic
end AxCheck
