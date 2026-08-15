/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G06
import Uniformity.ChapG.G07
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G08 — `CertFamily.decidedDensity_ge`, the family density lower bound

**Chapter G, NODE G.08** (`blueprint/CHAP-G_base_cases_menus.md` §3). A certified family gives a
density lower bound: `q^m·#S / q^(n·N) ≤ decidedDensity O n σ`.

DEPENDS: G.06, G.07 · landed `Uniformity.Density.decidedDensity_ge_of_subset`
(`DensityAPI.lean:160`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem CertFamily.decidedDensity_ge {n N : ℕ} (F : CertFamily O n N) :
    ((residueCard O : ℝ) ^ F.m * (Nat.card F.S : ℝ)) / (residueCard O : ℝ) ^ (n * N)
      ≤ decidedDensity O n F.σ := by
  have hsub : F.set ⊆ decidedSet O n F.σ N := fun _ hc => F.decidedAt hc
  have hge := decidedDensity_ge_of_subset hsub
  rw [F.card] at hge
  push_cast at hge
  exact hge

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.CertFamily.decidedDensity_ge

end AxCheck
