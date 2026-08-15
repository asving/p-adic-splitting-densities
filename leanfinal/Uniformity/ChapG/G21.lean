/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G21 — `residualPair`, the residual pair at an even-depth centre

**Chapter G, NODE G.21** (`blueprint/CHAP-G_base_cases_menus.md` §4). *The residual pair at an
even-depth centre.* For a centre `γ` with `π^(2k) ∣ qval a γ` and `π^k ∣ qder a γ`, the residual
pair is `(qval a γ / π^(2k), qder a γ / π^k)` reduced mod `𝔪`, an element of `ResidueField O ×
ResidueField O`.

DEPENDS: landed `qval`, `qder`, `IsLocalRing.residue`.

⚠ **SIGNATURE landed in the two-hypothesis form**, per the blueprint's own declared PROOF note:
the verbatim `⟨_, rfl⟩`-based SIGNATURE cannot express the required `Classical.choose` witnesses
without hypotheses supplied at the use site, so the fleet lands the two-hypothesis form (also the
form the amended leanspec stub signs, `leanspec/Leanspec/ChapG.lean:226-229`). Definitional, no
proof obligation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The residual pair `(b₀, b₁)` read at a centre of even depth `2k`, in the residue field. -/
noncomputable def residualPair {k : ℕ} {a : Fin 2 → O} {γ : O}
    (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ) :
    IsLocalRing.ResidueField O × IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O h0.choose, IsLocalRing.residue O h1.choose)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.residualPair

end AxCheck
