/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.Density.InertLeaf

/-!
# Uniformity.ChapG.G57 — `typeOf_inert3_of_irreducible_map`

**Chapter G, NODE G.57** (`blueprint/CHAP-G_base_cases_menus.md` §8). *SEPC leaf.* A monic cubic
with irreducible reduction has type `c3inert`.

DEPENDS: G.52 · landed `typeOf_inert_of_irreducible_map` (CN-21), `monicPoly_monic`,
`monicPoly_natDegree`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem typeOf_inert3_of_irreducible_map [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h : Irreducible ((monicPoly a).map (residue O))) : typeOf (monicPoly a) = c3inert := by
  have hd : 0 < (monicPoly a).natDegree := by rw [monicPoly_natDegree]; norm_num
  have hty := typeOf_inert_of_irreducible_map (monicPoly_monic a) hd h
  rw [monicPoly_natDegree] at hty
  exact hty

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_inert3_of_irreducible_map

end AxCheck
