/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.Density.TypeOfAlgebra
import Uniformity.Density.InertLeaf

/-!
# Uniformity.ChapG.G56 — `typeOf_linInert_of_residue`

**Chapter G, NODE G.56** (`blueprint/CHAP-G_base_cases_menus.md` §8). *SEPLQ leaf.* A monic
cubic whose reduction factors as a linear times an irreducible quadratic has type `c3linInert`.

DEPENDS: G.52 · landed `typeOf_of_residual_coprime` (CN-18, `TypeOfAlgebra.lean:131`),
`typeOf_inert_of_irreducible_map` (CN-21, `InertLeaf.lean:179`), `typeOf_of_natDegree_one`,
`typeOf_mul`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

theorem typeOf_linInert_of_residue {a : Fin 3 → O}
    {ρ : O} {g₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hdeg : g₀.natDegree = 2)
    (hirr : Irreducible g₀)
    (hres : (monicPoly a).map (residue O) = (X - C (residue O ρ)) * g₀) :
    typeOf (monicPoly a) = c3linInert := by
  -- `X - C ρ̄` is coprime to `g₀`: it is irreducible, of a different degree than `g₀`, so it
  -- cannot divide the irreducible `g₀`.
  have hcop : IsCoprime (X - C (residue O ρ)) g₀ := by
    rw [Irreducible.coprime_iff_not_dvd (irreducible_X_sub_C (residue O ρ)), dvd_iff_isRoot]
    intro hroot
    obtain ⟨c, hc⟩ := dvd_iff_isRoot.2 hroot
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hg₀.ne_zero hc
    have hdegc : c.natDegree = 1 := by
      have heq : g₀.natDegree = (X - C (residue O ρ)).natDegree + c.natDegree := by
        rw [hc]; exact natDegree_mul (X_sub_C_ne_zero _) hc0
      rw [natDegree_X_sub_C, hdeg] at heq
      omega
    rcases hirr.2 hc with hu | hu
    · exact (not_isUnit_X_sub_C _) hu
    · exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
  obtain ⟨g, h, hgmon, hhmon, hfeq, hgmap, hhmap, hgdeg, hhdeg, hsplit⟩ :=
    typeOf_of_residual_coprime (monicPoly_monic a) (monic_X_sub_C (residue O ρ)) hg₀ hcop hres
  have hgd1 : g.natDegree = 1 := by rw [hgdeg, natDegree_X_sub_C]
  have hhd2 : h.natDegree = 2 := by rw [hhdeg, hdeg]
  have htyg : typeOf g = ⟨{(1, 1)}⟩ := typeOf_of_natDegree_one hgmon hgd1
  have htyh : typeOf h = ⟨({(1, 2)} : Multiset (ℕ × ℕ))⟩ := by
    have hty := typeOf_inert_of_irreducible_map hhmon (by rw [hhd2]; norm_num)
      (by rw [hhmap]; exact hirr)
    rwa [hhd2] at hty
  refine FactorizationType.ext ?_
  rw [hsplit, htyg, htyh]
  rfl

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_linInert_of_residue

end AxCheck
