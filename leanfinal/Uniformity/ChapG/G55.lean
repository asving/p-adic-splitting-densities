/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.Density.TypeOfAlgebra

/-!
# Uniformity.ChapG.G55 — `typeOf_split3_of_residue`

**Chapter G, NODE G.55** (`blueprint/CHAP-G_base_cases_menus.md` §8). *SEP3 leaf.* A monic
cubic whose reduction has three distinct roots in the residue field splits into three monic
linear factors, so its type is `c3split`.

DEPENDS: G.52 · landed `exists_monic_factorization_finset` (CN-17, `MultiHensel.lean:111`),
`typeOf_prod_X_sub_C` (CN-14, `TypeOfAlgebra.lean:90`), `typeOf_mul` (CN-03),
`typeOf_of_natDegree_one`.

**Proof route (an equivalent two-factor peel, chaining the already-landed CN-18
`typeOf_of_residual_coprime` twice rather than the `Finset`-indexed CN-17 directly): peel
`X - C ρ̄₁` off the product first, then peel `X - C ρ̄₂` off the remaining quadratic factor.
Both peels are the same coprime-residual-factorization step G.56 already uses once; this node
uses it twice.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

theorem typeOf_split3_of_residue {a : Fin 3 → O}
    (ρ₁ ρ₂ ρ₃ : O) (h12 : IsUnit (ρ₁ - ρ₂)) (h13 : IsUnit (ρ₁ - ρ₃)) (h23 : IsUnit (ρ₂ - ρ₃))
    (hres : (monicPoly a).map (residue O)
      = (X - C (residue O ρ₁)) * (X - C (residue O ρ₂)) * (X - C (residue O ρ₃))) :
    typeOf (monicPoly a) = c3split := by
  have hu12 : IsUnit (residue O ρ₁ - residue O ρ₂) := by
    have := h12.map (residue O); rwa [map_sub] at this
  have hu13 : IsUnit (residue O ρ₁ - residue O ρ₃) := by
    have := h13.map (residue O); rwa [map_sub] at this
  have hu23 : IsUnit (residue O ρ₂ - residue O ρ₃) := by
    have := h23.map (residue O); rwa [map_sub] at this
  have hc12 := isCoprime_X_sub_C_of_isUnit_sub hu12
  have hc13 := isCoprime_X_sub_C_of_isUnit_sub hu13
  have hc23 := isCoprime_X_sub_C_of_isUnit_sub hu23
  -- Step 1: peel `X - C ρ̄₁` off the product, leaving the quadratic remainder.
  have hres' : (monicPoly a).map (residue O)
      = (X - C (residue O ρ₁)) * ((X - C (residue O ρ₂)) * (X - C (residue O ρ₃))) := by
    rw [hres, mul_assoc]
  obtain ⟨g, h, hgmon, hhmon, hfeq, hgmap, hhmap, hgdeg, hhdeg, hsplit1⟩ :=
    typeOf_of_residual_coprime (monicPoly_monic a) (monic_X_sub_C (residue O ρ₁))
      ((monic_X_sub_C (residue O ρ₂)).mul (monic_X_sub_C (residue O ρ₃)))
      (hc12.mul_right hc13) hres'
  have hgd1 : g.natDegree = 1 := by rw [hgdeg, natDegree_X_sub_C]
  have htyg : typeOf g = ⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ := typeOf_of_natDegree_one hgmon hgd1
  -- Step 2: peel `X - C ρ̄₂` off the remaining quadratic `h`.
  obtain ⟨g', h', hg'mon, hh'mon, hh'eq, hg'map, hh'map, hg'deg, hh'deg, hsplit2⟩ :=
    typeOf_of_residual_coprime hhmon (monic_X_sub_C (residue O ρ₂)) (monic_X_sub_C (residue O ρ₃))
      hc23 hhmap
  have hg'd1 : g'.natDegree = 1 := by rw [hg'deg, natDegree_X_sub_C]
  have hh'd1 : h'.natDegree = 1 := by rw [hh'deg, natDegree_X_sub_C]
  have htyg' : typeOf g' = ⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ := typeOf_of_natDegree_one hg'mon hg'd1
  have htyh' : typeOf h' = ⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ := typeOf_of_natDegree_one hh'mon hh'd1
  refine FactorizationType.ext ?_
  rw [hsplit1, hsplit2, htyg, htyg', htyh']
  rfl

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_split3_of_residue

end AxCheck
