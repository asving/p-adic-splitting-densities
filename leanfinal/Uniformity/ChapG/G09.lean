/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G09 — `tangSet`, the tangency-filtration set

**Chapter G, NODE G.09** (`blueprint/CHAP-G_base_cases_menus.md` §4). `tangSet π N t` is the
set of level-`N` classes having a lift with a centre of tangency depth at least `t`.

DEPENDS: landed `Uniformity.Density.Tang` (`Drainage.lean:511`), `proj`.

Definitional, no proof obligation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Level-`N` classes admitting a lift with a centre of tangency depth `≥ t`. -/
def tangSet (π : O) (N t : ℕ) : Set (Coeff O 2 N) :=
  {c | ∃ a : Fin 2 → O, proj O 2 N a = c ∧ ∃ γ : O, Tang π a t γ}

end Uniformity.Density.Menu
