/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B07
import Uniformity.StrongHensel

/-!
# Uniformity.ChapB.B08 — the divisibility characterisation of `gaussVal`

**Chapter B, NODE B.08** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A′ (= ENV-A with `hπ : Irreducible π`, carried in the signature).

The Gauss valuation of B.07 is read off by divisibility: for `π` irreducible,
`(k : ℕ∞) ≤ gaussVal a ↔ ∀ i, π ^ k ∣ a.coeff i`. Two consequences land with it —
`gaussVal a = ⊤ ↔ a = 0` (the support reading) and the range-independence
`gaussVal a = (Finset.range M).inf (fun i => addVal O (a.coeff i))` for any `M > a.natDegree`
(so that B.14 may take one uniform range for all `j`).

Three public declarations: the same fact in the three shapes every consumer needs
(`le_gaussVal_iff` for divisibility transport, `gaussVal_eq_top_iff` for the support,
`gaussVal_range` for the uniform range).

DEPENDS: B.07 (`gaussVal`) · landed `Uniformity.Hensel.pow_dvd_iff_le_addVal`
(`Uniformity/StrongHensel.lean`) · mathlib `Finset.le_inf_iff`, `Finset.inf_eq_top_iff`,
`Polynomial.coeff_eq_zero_of_natDegree_lt`, `IsDiscreteValuationRing.addVal_zero`,
`IsDiscreteValuationRing.addVal_eq_top_iff`.

**PROOF.**
1. `le_gaussVal_iff` (→): `Finset.le_inf_iff` gives `(k : ℕ∞) ≤ addVal O (a.coeff i)` for `i`
   in the range and `pow_dvd_iff_le_addVal hπ` converts it; for `i` outside the range
   `coeff_eq_zero_of_natDegree_lt` gives `a.coeff i = 0`, which every power divides.
2. (←): `Finset.le_inf` with `pow_dvd_iff_le_addVal hπ` in the other direction.
3. `gaussVal_eq_top_iff` (→): `Finset.inf_eq_top_iff` gives `addVal O (a.coeff i) = ⊤` for `i`
   in the range, hence `a.coeff i = 0` by `addVal_eq_top_iff`; with the out-of-range case that
   is `a = 0` by `Polynomial.ext`. (←) every coefficient of `0` has `addVal = ⊤`.
4. `gaussVal_range`: antisymmetry. Each `inf` is bounded by the other pointwise — the indices
   of `range M` beyond `a.natDegree` contribute `addVal O 0 = ⊤`, the neutral element of the
   `inf`, and `range (a.natDegree + 1) ⊆ range M` gives the reverse bound.

SOURCE: `EFF.HE6.10`; `EFF.W12.23`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The Gauss valuation is `≥ k` exactly when `π ^ k` divides every coefficient. -/
theorem le_gaussVal_iff (hπ : Irreducible π) {k : ℕ} {a : Polynomial O} :
    (k : ℕ∞) ≤ gaussVal a ↔ ∀ i, π ^ k ∣ a.coeff i := by
  simp only [gaussVal, Finset.le_inf_iff, Finset.mem_range]
  constructor
  · intro h i
    by_cases hi : i < a.natDegree + 1
    · exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 (h i hi)
    · rw [a.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact dvd_zero _
  · intro h i _
    exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 (h i)

/-- The Gauss valuation is `⊤` exactly on the zero polynomial. -/
theorem gaussVal_eq_top_iff {a : Polynomial O} : gaussVal a = ⊤ ↔ a = 0 := by
  simp only [gaussVal, Finset.inf_eq_top_iff, Finset.mem_range, addVal_eq_top_iff]
  constructor
  · intro h
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_zero]
    by_cases hi : i < a.natDegree + 1
    · exact h i hi
    · exact a.coeff_eq_zero_of_natDegree_lt (by omega)
  · rintro rfl i _
    simp

/-- The Gauss valuation may be computed over any range strictly containing the degree: the
extra indices contribute `addVal O 0 = ⊤`, which no `inf` can see. -/
theorem gaussVal_range (a : Polynomial O) {M : ℕ} (hM : a.natDegree < M) :
    gaussVal a = (Finset.range M).inf (fun i => IsDiscreteValuationRing.addVal O (a.coeff i)) := by
  simp only [gaussVal]
  refine le_antisymm (Finset.le_inf fun i _ => ?_) (Finset.le_inf fun i hi => ?_)
  · by_cases h : i < a.natDegree + 1
    · exact Finset.inf_le (Finset.mem_range.2 h)
    · rw [a.coeff_eq_zero_of_natDegree_lt (by omega), addVal_zero]
      exact le_top
  · have hiM : i < M := lt_of_lt_of_le (Finset.mem_range.1 hi) (by omega)
    exact Finset.inf_le (Finset.mem_range.2 hiM)

section AxCheck
#print axioms Uniformity.Density.Leaf.le_gaussVal_iff
#print axioms Uniformity.Density.Leaf.gaussVal_eq_top_iff
#print axioms Uniformity.Density.Leaf.gaussVal_range
end AxCheck

end Uniformity.Density.Leaf
