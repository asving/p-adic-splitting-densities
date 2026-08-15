/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.ChapG.G73
import Uniformity.Density.TypeOfAlgebra
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G74 — `exists_split3_lift`

**Chapter G, NODE G.74** (`blueprint/CHAP-G_base_cases_menus.md` §10). Every class of
`species3 N` (the `q^N`-element species with `c 0 = c 1 = 0`) has a `c3split` lift: `x²(x+a₂)`.

DEPENDS: G.52, G.73 · landed `typeOf_prod_X_sub_C`, `typeOf_mul`, `monicPoly`, `proj_eq_iff_dvd`,
`proj_surjective`.

**TEETH.** `HEX3-SPECIES` → executable regression.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- `[Finite (ResidueField O)]` is carried for the frozen `Coeff O 3 N` signature (per the leanspec
-- design stub); the proof itself does not need finiteness.
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

theorem exists_split3_lift {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧ typeOf (monicPoly a) = c3split := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) (c 2)
  set b : Fin 3 → O := ![0, 0, x] with hb
  refine ⟨b, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [proj, b, hc.1, hc.2, hx]
  · set r : Fin 3 → O := ![0, 0, -x] with hr
    have hfact : monicPoly b = ∏ i : Fin 3, (X - C (r i)) := by
      have h2 : ((2 : Fin 3) : ℕ) = 2 := rfl
      rw [Fin.prod_univ_three]
      simp only [monicPoly, Fin.sum_univ_three, hb, hr]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, map_zero, map_neg, h2]
      ring
    have htype := typeOf_prod_X_sub_C r
    rw [← hfact] at htype
    rw [htype]
    apply FactorizationType.ext
    decide

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.exists_split3_lift

end AxCheck
