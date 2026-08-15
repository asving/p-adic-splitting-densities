/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G24

/-!
# Uniformity.ChapG.G25 — `decidedAt_ram_of_depth_odd`

**Chapter G, NODE G.25** (`blueprint/CHAP-G_base_cases_menus.md` §5). A class of odd depth `< N`
is `ramType`-decided at level `N`.

DEPENDS: G.24 · landed `typeOf_of_certRam` (`Drainage.lean:286`), `CertRam_congr`
(`Drainage.lean:463`), `congAt_of_proj_eq` (`Drainage.lean:639`), `proj_surjective`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem decidedAt_ram_of_depth_odd (hπ : Irreducible π) {N j : ℕ} {c : Coeff O 2 N}
    (hmem : c ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    DecidedAt O 2 ramType N c := by
  intro a ha
  have hcert : CertRam π a (2 * j + 2) := certRam_of_depth_odd hπ (ha ▸ hmem) hN
  exact typeOf_of_certRam hπ hcert

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.decidedAt_ram_of_depth_odd

end AxCheck
