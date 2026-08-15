/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G09
import Uniformity.ChapG.G12

/-!
# Uniformity.ChapG.G29 — `decidedAt_of_depth_lt`

**Chapter G, NODE G.29** (`blueprint/CHAP-G_base_cases_menus.md` §5). Every class of depth `< N`
is decided (for the type of any of its lifts).

DEPENDS: G.09, G.12 · landed `decidedAt_of_not_tang` (`Drainage.lean:652`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem decidedAt_of_depth_lt (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N : ℕ} {c : Coeff O 2 N}
    (hc : c ∉ tangSet π N N) {a : Fin 2 → O} (ha : proj O 2 N a = c) :
    DecidedAt O 2 (typeOf (monicPoly a)) N c := by
  have hnex : ¬ ∃ γ, Tang π a N γ := fun ⟨γ, hγ⟩ => hc ⟨a, ha, γ, hγ⟩
  exact ha ▸ decidedAt_of_not_tang hπ hnex

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.decidedAt_of_depth_lt

end AxCheck
