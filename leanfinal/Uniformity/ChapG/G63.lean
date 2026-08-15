/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G62

/-!
# Uniformity.ChapG.G63 — `card_cubicFamilyIndex` / `schema_surjective`

**Chapter G, NODE G.63** (`blueprint/CHAP-G_base_cases_menus.md` §9). `#CubicFamilyIndex = 53`
and the schema map is surjective onto `Fin 33`.

DEPENDS: G.62.

This node is fireable only because G.62's `CubicFamilyIndex.schema` now has a landed body
(blueprint defect D2, cured at AMENDMENT 2026-08-15 §A-5): both statements were finite checks
that could not be decided against a bodyless `def`. G.62's own Status note records that
`decide` already confirms both facts against the landed body — this file is that confirmation,
landed as the chapter's own declarations.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

theorem card_cubicFamilyIndex : Nat.card CubicFamilyIndex = 53 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 8000 in
theorem schema_surjective : Function.Surjective CubicFamilyIndex.schema := by
  decide

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.card_cubicFamilyIndex
#print axioms Uniformity.Density.Menu.schema_surjective

end AxCheck
