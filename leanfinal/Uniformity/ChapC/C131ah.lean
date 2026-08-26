/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131v

/-!
# Uniformity.ChapC.C131ah — shadow-development linearity

**Chapter C, NODE C.131ah′ — RB3 shadow-linearity API**
(`docs/in-progress/BLOCKERS_PLAN_2026-08-26.md`, node F3.5).

This file lands the three probe-complete algebraic facts needed to decompose shadow
discrepancies additively:

* `biRead_add`: the two-stage read is coefficientwise additive;
* `biRead_composedKey_monic`: the shadow divisor is monic, via the mapped canonical `xNF`;
* `shadowDev_add`: shadow development is additive in its polynomial argument.

The genuinely new persistence mechanism remains the separate coefficient-budget-to-height
bridge; it is not asserted here.

## Status

Sorry-free and axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing Uniformity.Density Uniformity.Density.Leaf
open Uniformity.Density.Tower.C131k
open Uniformity.Density.Tower.C131v

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The coefficientwise two-stage read is additive in its polynomial argument. -/
theorem biRead_add {F : KeyFrame O π} (a b : Polynomial O) :
    biRead F (a + b) = biRead F a + biRead F b := by
  ext j
  rw [Polynomial.coeff_add, biRead_coeff, biRead_coeff, biRead_coeff,
    dev_add_of_monic F.hmonic, map_add]

/-- The two-stage read of the composed key is monic. -/
theorem biRead_composedKey_monic {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (biRead F (composedKey T)).Monic := by
  have heq : biRead F (composedKey T)
      = (xNF F (composedKey T)).map (AdjoinRoot.mk F.key) := by
    ext j
    rw [biRead_coeff, Polynomial.coeff_map, xNF_coeff, xDigit_eq_dev]
  rw [heq]
  exact (xNF_monic F (composedKey_monic T) (composedKey_natDegree_mul T hπ)).map _

/-- Shadow development is additive in its polynomial argument. -/
theorem shadowDev_add {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (a b : Polynomial O) (j : ℕ) :
    shadowDev T (a + b) j = shadowDev T a j + shadowDev T b j := by
  letI := F.nontrivial_adjoinRoot
  rw [shadowDev_eq_reass, shadowDev_eq_reass, shadowDev_eq_reass, biRead_add,
    devQ_add (biRead_composedKey_monic T hπ), reass_add]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Tower.biRead_add
#print axioms Uniformity.Density.Tower.biRead_composedKey_monic
#print axioms Uniformity.Density.Tower.shadowDev_add
end AxCheck
