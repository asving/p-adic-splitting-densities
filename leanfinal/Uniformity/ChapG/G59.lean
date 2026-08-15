/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.Density.TypeOfAlgebra
import Uniformity.Density.QuadCert
import Uniformity.Density.Transport

/-!
# Uniformity.ChapG.G59 — `typeOf_linRam_of_residue`

**Chapter G, NODE G.59** (`blueprint/CHAP-G_base_cases_menus.md` §8). A monic cubic with `a₂` a
unit and `a₁, a₀ ∈ 𝔪`, `a₀ ∉ 𝔪²`, has type `c3linRam`: Hensel peels a unit-root linear factor
and the remaining quadratic is Eisenstein.

DEPENDS: G.52 · landed `typeOf_of_residual_coprime`, `typeOf_ram_of_eisenstein`,
`typeOf_of_natDegree_one`, `typeOf_mul`, `exists_monicPoly_eq`, `monicPoly_coeff_lt`.

**TEETH.** `HM3-ORACLE`, `HM3-XREAD` → executable regression.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

section Expand

set_option linter.unusedSectionVars false

variable {O : Type*} [CommRing O] [IsDomain O]

/-- The expansion of a monic cubic's coefficient vector into named terms; a purely
computational unfolding of `monicPoly`, private to this node. -/
private theorem g59_expand (a : Fin 3 → O) :
    monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
  have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [monicPoly, Fin.sum_univ_three, e0, e1, e2, pow_zero, pow_one, mul_one]
  ring

end Expand

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

theorem typeOf_linRam_of_residue {a : Fin 3 → O}
    (h2 : IsUnit (a 2)) (h1 : a 1 ∈ maximalIdeal O) (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) : typeOf (monicPoly a) = c3linRam := by
  set c : ResidueField O := residue O (a 2) with hc
  have hu2 : IsUnit c := h2.map (residue O)
  have ha0z : residue O (a 0) = 0 := (residue_eq_zero_iff (a 0)).2 h0
  have ha1z : residue O (a 1) = 0 := (residue_eq_zero_iff (a 1)).2 h1
  -- Step 1: reduce `monicPoly a` mod `𝔪` to `X² * (X + C c)` (well, `(X + C c) * X²`).
  have hexpand : monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := g59_expand a
  have hfgh : (monicPoly a).map (residue O) = (X + C c) * X ^ 2 := by
    rw [hexpand]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, ha0z, ha1z, map_zero]
    ring
  -- Step 2: the two residual factors `X + C c` and `X²` are coprime (`c` is a unit).
  have hcop0 : IsCoprime (X - C (-c)) (X - C (0 : ResidueField O)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by simpa using hu2.neg)
  have hcop1 : IsCoprime ((X : Polynomial (ResidueField O)) + C c) X := by
    have e1 : (X - C (-c) : Polynomial (ResidueField O)) = X + C c := by
      rw [map_neg, sub_neg_eq_add]
    have e2 : (X - C (0 : ResidueField O) : Polynomial (ResidueField O)) = X := by
      rw [map_zero, sub_zero]
    rwa [e1, e2] at hcop0
  have hcop : IsCoprime ((X : Polynomial (ResidueField O)) + C c) (X ^ 2) := hcop1.pow_right
  -- Step 3: peel the two factors via the order-0 residual coprimality lift.
  obtain ⟨g, h, hgmon, hhmon, hfeq, hgmap, hhmap, hgdeg, hhdeg, hsplit⟩ :=
    typeOf_of_residual_coprime (monicPoly_monic a) (monic_X_add_C c) (monic_X_pow 2) hcop hfgh
  have hgd1 : g.natDegree = 1 := by rw [hgdeg, natDegree_X_add_C]
  have hhd2 : h.natDegree = 2 := by rw [hhdeg, natDegree_X_pow]
  have htyg : typeOf g = ⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ := typeOf_of_natDegree_one hgmon hgd1
  -- Step 4: `h` is Eisenstein — its constant coefficient carries `a 0`'s valuation exactly,
  -- since `(monicPoly a).coeff 0 = g.coeff 0 * h.coeff 0` and ideals absorb any factor.
  have ha0eq : a 0 = g.coeff 0 * h.coeff 0 := by
    have h1' : (monicPoly a).coeff 0 = a 0 := monicPoly_coeff_lt a (by norm_num)
    rw [← h1', hfeq, Polynomial.mul_coeff_zero]
  have hh0notin : h.coeff 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    exact h0' (ha0eq ▸ Ideal.mul_mem_left _ _ hmem)
  have hh0mem : h.coeff 0 ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    have := congrArg (fun p : Polynomial (ResidueField O) => p.coeff 0) hhmap
    simpa [Polynomial.coeff_map, Polynomial.coeff_X_pow] using this
  have hh1mem : h.coeff 1 ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    have := congrArg (fun p : Polynomial (ResidueField O) => p.coeff 1) hhmap
    simpa [Polynomial.coeff_map, Polynomial.coeff_X_pow] using this
  obtain ⟨b, hbeq⟩ := exists_monicPoly_eq hhmon hhd2
  have hb0 : h.coeff 0 = b 0 := by
    rw [← hbeq]; exact monicPoly_coeff_lt b (by norm_num)
  have hb1 : h.coeff 1 = b 1 := by
    rw [← hbeq]; exact monicPoly_coeff_lt b (by norm_num)
  have hb0mem : b 0 ∈ maximalIdeal O := hb0 ▸ hh0mem
  have hb0notin : b 0 ∉ (maximalIdeal O) ^ 2 := hb0 ▸ hh0notin
  have hb1mem : b 1 ∈ maximalIdeal O := hb1 ▸ hh1mem
  have htyb : typeOf (monicPoly b) = ramType := typeOf_ram_of_eisenstein hb0mem hb0notin hb1mem
  have htyh : typeOf h = ⟨({(2, 1)} : Multiset (ℕ × ℕ))⟩ := by rw [hbeq] at htyb; exact htyb
  -- Step 5: assemble.
  refine FactorizationType.ext ?_
  rw [hsplit, htyg, htyh]
  rfl

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_linRam_of_residue

end AxCheck
