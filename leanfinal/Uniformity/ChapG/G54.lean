/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.ChapG.G53
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G54 — `coveringMenu_three` / `genuineDensity_three_eq_zero`

**Chapter G, NODE G.54** (`blueprint/CHAP-G_base_cases_menus.md` §8). The five types form a
covering menu at degree 3; every other type has genuine density `0` at `n = 3`.

DEPENDS: G.52, G.53 · landed `CoveringMenu` (`GenuineDensity.lean:458`),
`genuineDensity_eq_zero_of_forall_ne` (`DensityAPI.lean:69`).

**SCOPE NOTE.** `CoveringMenu` is a statement about **types**, not about HMENU3's **families**.
This node does not prove HM3.C's menu (a statement about decided strata with exact counts). Do
not cite this node as `(hMenu-3)`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem coveringMenu_three :
    CoveringMenu O 3 ({c3split, c3linInert, c3inert, c3linRam, c3ram} : Finset FactorizationType) := by
  intro a
  rcases typeOf_three_cases a with h | h | h | h | h <;> simp [h]

theorem genuineDensity_three_eq_zero {σ : FactorizationType} (hs : σ ≠ c3split)
    (hi : σ ≠ c3linInert) (hc : σ ≠ c3inert) (hr : σ ≠ c3linRam) (ht : σ ≠ c3ram) :
    genuineDensity O 3 σ = 0 := by
  apply genuineDensity_eq_zero_of_forall_ne
  intro a
  rcases typeOf_three_cases a with h | h | h | h | h <;> rw [h] <;> exact Ne.symm (by assumption)

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.coveringMenu_three
#print axioms Uniformity.Density.genuineDensity_three_eq_zero

end AxCheck
