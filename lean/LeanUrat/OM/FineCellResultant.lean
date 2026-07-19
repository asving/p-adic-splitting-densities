/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.SparseResultant
import LeanUrat.OM.ProductTheorem

/-!
# Phase 1 — FineCellResultant: valuation of the fine-cell resultant

Leaf module for PHASE 1 of `notes/BLUEPRINT_WILD_FORMALIZATION_2026-07-13.md`
("fine-cell resultant-valuation constancy").  Imports Mathlib plus the two already-proved
leaves `SparseResultant` (closed-form lattice exponents) and `PadicLift` (the level-`N`
`zmodValuation`).  Adds nothing to the measure wall.

Two deliverables:

* **NEW-1** `vResultant_eq_prod_cross_pairs`: for monic split polynomials `Gi, Gj` over a
  field `K` and any `Valuation K Γ₀`,
  `v (resultant Gi Gj) = ∏_{θi ∈ roots Gi} ∏_{θj ∈ roots Gj} v (θi − θj)`.
  Since a `Valuation` takes values in a *multiplicative* `LinearOrderedCommMonoidWithZero`
  `Γ₀`, the blueprint's additive `Σ v(θi − θj)` is here the product `∏ v(θi − θj)` (the
  additive spelling is `Multiplicative` of this).  Proof: mathlib's
  `Polynomial.resultant_eq_prod_roots_sub` turns `resultant Gi Gj` into a product over the
  root pairs `Gi.roots ×ˢ Gj.roots` of the differences `θi − θj`; then `map_multiset_prod`
  (`Valuation` is a `MonoidWithZeroHomClass`) distributes `v` over the product, and the
  double-product form is the `Finset.prod`/`Multiset` reshaping.

* **NEW-2** `finecell_vResultant_const`: fine-cell constancy for the realized deep-wild
  sparse-twist family.  For sparse twists `F_i = sparseTwist p ψ_i e h`,
  `F_j = sparseTwist p ψ_j e h` over `ZMod (p^N)` with residual resultant a unit and the
  lattice exponent `d_i d_j e h` below the cutoff `N`, the level-`N` native valuation of the
  resultant is the *fixed lattice integer* `d_i d_j e h` — independent of `p` and of the
  residual data, determined by the Newton data `(d_i, d_j, e, h)` alone.  This is `NEW-2` of
  the blueprint: the exponent IS `SparseResultant.resultant_sparseTwist{,_isUnit}`, and
  reading it off as a valuation is `PadicLift`/`ProductTheorem`'s
  `zmodValuation_pow_mul_unit`.  A cross-side companion `finecell_vResultant_const_cross`
  wires `resultant_sparseTwist_cross` the same way (exponent `d_i d_j e_j h_i`).

No `sorry`, no `axiom`, no `native_decide`; all public results elaborate with core-only
axiom footprints (`propext`, `Classical.choice`, `Quot.sound`) — see `#print axioms` at end.
-/

set_option linter.style.longLine false

namespace LeanUrat.OM.FineCellResultant

open Polynomial

/-! ## NEW-1 — valuation of the resultant as a product over cross-pairs of roots -/

section AbstractValuation

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **NEW-1 (multiset form).**  For monic split `Gi, Gj` and a valuation `v : Valuation K Γ₀`,
`v (resultant Gi Gj)` is the product, over the multiset of root pairs `Gi.roots ×ˢ Gj.roots`,
of `v (θi − θj)`.  Pure valuation-of-a-product computation on top of mathlib's
`resultant_eq_prod_roots_sub`. -/
theorem vResultant_eq_prod_roots_sub (v : Valuation K Γ₀) {Gi Gj : K[X]}
    (hGi : Gi.Monic) (hGj : Gj.Monic) (hGi' : Gi.Splits) (hGj' : Gj.Splits) :
    v (resultant Gi Gj)
      = ((Gi.roots ×ˢ Gj.roots).map fun ij => v (ij.1 - ij.2)).prod := by
  rw [resultant_eq_prod_roots_sub Gi Gj hGi hGj hGi' hGj', map_multiset_prod,
    Multiset.map_map]
  rfl

/-- **NEW-1 (double-product form).**  Same hypotheses; the cross-pair product written as an
iterated product `∏_{θi ∈ roots Gi} ∏_{θj ∈ roots Gj} v (θi − θj)` (the blueprint's
`Σ_{θi} Σ_{θj} v(θi − θj)`, additive `Σ` = multiplicative `∏` in the value monoid `Γ₀`).

Route: `vResultant_eq_prod_roots_sub` then the standard `Multiset.prod` over a product
multiset `= ∏ over the first, of ∏ over the second` (`Multiset.prod_map_prod_map` shape,
here via `Multiset.product` unfolding). -/
theorem vResultant_eq_prod_cross_pairs (v : Valuation K Γ₀) {Gi Gj : K[X]}
    (hGi : Gi.Monic) (hGj : Gj.Monic) (hGi' : Gi.Splits) (hGj' : Gj.Splits) :
    v (resultant Gi Gj)
      = (Gi.roots.map fun θi => (Gj.roots.map fun θj => v (θi - θj)).prod).prod := by
  rw [vResultant_eq_prod_roots_sub v hGi hGj hGi' hGj']
  -- unfold the multiset product `s ×ˢ t` into the iterated product
  induction Gi.roots using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.prod_add, Multiset.map_cons,
      Multiset.prod_cons, Multiset.map_map, ← ih]
    rfl

end AbstractValuation

/-! ## NEW-2 — fine-cell constancy of the level-`N` resultant valuation

The realized deep-wild fine cells are the sparse-twist families of `SparseResultant`.  Over
`ZMod (p^N)` the resultant of two same-side sparse twists is `p^(d_i d_j e h) · unit`
(`SparseResultant.resultant_sparseTwist_isUnit`), so — provided that fixed lattice exponent
is below the valuation cutoff `N` — the level-`N` native valuation reads off *exactly* the
lattice integer `d_i d_j e h`.  Constancy is manifest: the value depends only on the Newton
data `(d_i, d_j, e, h)`, not on `p` or the residuals. -/

open PadicLift SparseResultant ProductTheorem

/-- **NEW-2 (same side).**  Fine-cell constancy of the resultant valuation for a realized
same-side sparse-twist cell over `ZMod (p^N)`.

Given residuals `ψ_i, ψ_j` of degrees `d_i, d_j`, common slope datum `(e, h)`, coprime
residuals (`resultant ψ_i ψ_j` a unit) and the lattice exponent below the cutoff
(`d_i d_j e h < N`, honest hypothesis — the level-`N` valuation caps at `N`), the level-`N`
native valuation of the fine-cell resultant is the fixed lattice integer `d_i · d_j · e · h`,
determined by the Newton data alone.

The exponent IS `resultant_sparseTwist_isUnit` (already proved); reading it off as a
valuation is `zmodValuation_pow_mul_unit`.  A concrete realized cell is obtained by picking
any `(d_i, d_j, e, h)`, e.g. the n=6 `[2,4]` size-3 case `(d_i, d_j) = (1, 1)` on the deep
side; the constant does not depend on the residuals. -/
theorem finecell_vResultant_const {p N : ℕ} [Fact (Nat.Prime p)]
    {ψi ψj : (ZMod (p ^ N))[X]} {di dj : ℕ}
    (hdi : ψi.natDegree = di) (hdj : ψj.natDegree = dj) (e h : ℕ)
    (hres : IsUnit (resultant ψi ψj di dj))
    (hcut : di * dj * e * h < N) :
    zmodValuation p N
        (resultant (sparseTwist (p : ZMod (p ^ N)) ψi e h)
          (sparseTwist (p : ZMod (p ^ N)) ψj e h) (di * e) (dj * e))
      = di * dj * e * h := by
  obtain ⟨u, hu⟩ := resultant_sparseTwist_isUnit hdi hdj e h hres
  exact zmodValuation_pow_mul_unit p hcut hu

/-- **NEW-2 (cross side).**  The cross-side companion: for sparse twists of strictly ordered
slopes `h_i/e_i < h_j/e_j` with `ψ_j` monic and `ψ_i(0)` a unit, the fine-cell resultant
valuation is the fixed lattice integer `d_i · d_j · e_j · h_i` (the exponent of
`resultant_sparseTwist_cross`), again below-cutoff and independent of `p`/residual data. -/
theorem finecell_vResultant_const_cross {p N : ℕ} [Fact (Nat.Prime p)]
    {ψi ψj : (ZMod (p ^ N))[X]} {di dj : ℕ}
    (hdi : ψi.natDegree = di) (hdj : ψj.natDegree = dj) {ei hi ej hj : ℕ}
    (hei : 0 < ei) (hej : 0 < ej) (hslope : hi * ej < hj * ei)
    (hψj : ψj.Monic) (hψi0 : IsUnit (ψi.coeff 0))
    (hcut : di * dj * ej * hi < N) :
    zmodValuation p N
        (resultant (sparseTwist (p : ZMod (p ^ N)) ψi ei hi)
          (sparseTwist (p : ZMod (p ^ N)) ψj ej hj) (di * ei) (dj * ej))
      = di * dj * ej * hi := by
  obtain ⟨u, hu⟩ :=
    resultant_sparseTwist_cross hdi hdj hei hej hslope hψj hψi0
  exact zmodValuation_pow_mul_unit p hcut hu

#print axioms vResultant_eq_prod_roots_sub
#print axioms vResultant_eq_prod_cross_pairs
#print axioms finecell_vResultant_const
#print axioms finecell_vResultant_const_cross

end LeanUrat.OM.FineCellResultant
