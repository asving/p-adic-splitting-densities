/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G14

/-!
# Uniformity.ChapG.G15 — `tangAdm`, the depth-`t` admissible set

**Chapter G, NODE G.15** (`blueprint/CHAP-G_base_cases_menus.md` §4). The depth-`t` family:
centre modulus `⌈t/2⌉`, read `readAt`, admissible set
`{(F, F') | π^t ∣ F ∧ π^⌈t/2⌉ ∣ F'}` expressed by vanishing of the truncations.

DEPENDS: G.14 · landed `Res`.

Definitional, no proof obligation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- The admissible set of the depth-`t` family in `(value, derivative)` coordinates. -/
def tangAdm (π : O) (t N : ℕ) : Set (Res O N × Res O N) :=
  (dvdSet π t N) ×ˢ (dvdSet π ((t + 1) / 2) N)

end Uniformity.Density.Menu
