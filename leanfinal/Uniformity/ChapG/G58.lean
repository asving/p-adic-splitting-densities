/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.Density.NormLeaves
import Uniformity.Density.Transport

/-!
# Uniformity.ChapG.G58 — `typeOf_ram3_of_eisenstein`

**Chapter G, NODE G.58** (`blueprint/CHAP-G_base_cases_menus.md` §8). An Eisenstein monic cubic
has type `c3ram` — the cheapest certificate in the chapter at general `n`, since
`typeOf_eisenstein` (`NormLeaves.lean`, CN-20) already does the hard work at general degree.

DEPENDS: G.52 · landed `typeOf_eisenstein`, `monicPoly_coeff_lt`, `monicPoly_monic`,
`monicPoly_natDegree`.

**TEETH.** `HM3-ORACLE` → executable regression.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem typeOf_ram3_of_eisenstein {a : Fin 3 → O}
    (hlow : ∀ i : Fin 3, a i ∈ maximalIdeal O) (h0 : a 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf (monicPoly a) = c3ram := by
  have hd : 0 < (monicPoly a).natDegree := by rw [monicPoly_natDegree]; norm_num
  have hlow' : ∀ i < (monicPoly a).natDegree, (monicPoly a).coeff i ∈ maximalIdeal O := by
    intro i hi
    rw [monicPoly_natDegree] at hi
    rw [monicPoly_coeff_lt a hi]
    exact hlow ⟨i, hi⟩
  have h0' : (monicPoly a).coeff 0 ∉ (maximalIdeal O) ^ 2 := by
    rw [monicPoly_coeff_lt a (show (0 : ℕ) < 3 by norm_num)]
    exact h0
  have hty := typeOf_eisenstein (monicPoly_monic a) hd hlow' h0'
  rw [monicPoly_natDegree] at hty
  exact hty

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_ram3_of_eisenstein

end AxCheck
