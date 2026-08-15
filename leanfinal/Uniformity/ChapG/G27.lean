/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G27 — `decidedAt_inert_of_ani`, anisotropic residual ⟹ INERT-decided

**Chapter G, NODE G.27** (`blueprint/CHAP-G_base_cases_menus.md` §5). Anisotropic residual at an
even-depth centre ⟹ the INERT certificate at window `2k+1`; hence the class is `inertType`-decided
at every level `N ≥ 2k+1`.

DEPENDS: landed `Uniformity.Density.CertInert` (`Drainage.lean:258`), `typeOf_of_certInert`
(`Drainage.lean:329`), `CertInert_congr` (`Drainage.lean:484`), `congAt_of_proj_eq`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem decidedAt_inert_of_ani (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hani : Anisotropic ![b₀, b₁]) :
    DecidedAt O 2 inertType N (proj O 2 N a) := by
  have hcert : CertInert π a N := ⟨γ, k, b₀, b₁, hN, h0, h1, hani⟩
  intro b hb
  have hcong : CongAt π N a b := congAt_of_proj_eq hπ hb.symm
  exact typeOf_of_certInert hπ (CertInert_congr hπ hcong hcert)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.decidedAt_inert_of_ani

end AxCheck
