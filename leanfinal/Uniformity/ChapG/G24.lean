/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G09
import Uniformity.ChapG.G12
import Uniformity.ChapG.G19

/-!
# Uniformity.ChapG.G24 — `certRam_of_depth_odd`

**Chapter G, NODE G.24** (`blueprint/CHAP-G_base_cases_menus.md` §5). A class of odd depth
exactly `t = 2j+1` carries the RAM certificate at window `t+1`: at a witnessing centre the value
has exact valuation `2j+1` and the derivative valuation `≥ j+1`.

DEPENDS: G.09, G.12, G.19 · landed `Uniformity.Density.CertRam` (`Drainage.lean:251`),
`Tang` (`Drainage.lean:511`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem certRam_of_depth_odd (hπ : Irreducible π) {N j : ℕ} {a : Fin 2 → O}
    (hmem : proj O 2 N a ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    CertRam π a (2 * j + 2) := by
  obtain ⟨⟨b, hb, γ, hγ⟩, hnotmem⟩ := hmem
  have htang : Tang π a (2 * j + 1) γ := tang_of_proj_eq hπ (by omega) hb hγ
  have hval : π ^ (2 * j + 1) ∣ qval a γ := htang.1
  have hder : π ^ (j + 1) ∣ qder a γ := by
    have h := htang.2
    rwa [show (2 * j + 1 + 1) / 2 = j + 1 by omega] at h
  refine ⟨γ, j, le_refl _, hval, ?_, hder⟩
  intro hcon
  refine hnotmem ⟨a, rfl, γ, hcon, ?_⟩
  rwa [show (2 * j + 2 + 1) / 2 = j + 1 by omega]

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.certRam_of_depth_odd

end AxCheck
