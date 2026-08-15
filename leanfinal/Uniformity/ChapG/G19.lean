/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G09

/-!
# Uniformity.ChapG.G19 — `depthSet`, classes of exact depth `t`

**Chapter G, NODE G.19** (`blueprint/CHAP-G_base_cases_menus.md` §4). `depthSet π N t` = classes
of depth **exactly** `t`.

DEPENDS: G.09.

Definitional, no proof obligation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- Level-`N` classes whose maximal centre depth is exactly `t`. -/
def depthSet (π : O) (N t : ℕ) : Set (Coeff O 2 N) := tangSet π N t \ tangSet π N (t + 1)

end Uniformity.Density.Menu
