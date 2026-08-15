/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G12 — `tang_of_proj_eq`, depth is a property of the class

**Chapter G, NODE G.12** (`blueprint/CHAP-G_base_cases_menus.md` §4). *Depth is a property of
the class.* For `t ≤ N`, if one lift of `c` has a centre of depth `≥ t` then every lift does.

DEPENDS: landed `Uniformity.Density.congAt_of_proj_eq` (`Drainage.lean:639`),
`qval_congr` (`Drainage.lean:437`), `qder_congr` (`Drainage.lean:443`),
`dvd_transfer` (`Drainage.lean:449`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem tang_of_proj_eq (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {a b : Fin 2 → O}
    (hab : proj O 2 N a = proj O 2 N b) {γ : O} (h : Tang π a t γ) : Tang π b t γ := by
  have hcong : CongAt π N a b := congAt_of_proj_eq hπ hab
  exact ⟨dvd_transfer ht (qval_congr hcong γ) h.1,
    dvd_transfer (by omega) (qder_congr hcong γ) h.2⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.tang_of_proj_eq

end AxCheck
