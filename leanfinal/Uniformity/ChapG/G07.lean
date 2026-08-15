/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G05
import Uniformity.Density.CensusGen

/-!
# Uniformity.ChapG.G07 — `CertFamily.card`, the family count law

**Chapter G, NODE G.07** (`blueprint/CHAP-G_base_cases_menus.md` §3). *The family count law.*
A certified family's set has exactly `q^m · #S` members.

DEPENDS: G.05 · landed `UniformityCheck.card_certSet_gen` (`CensusGen.lean:64`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem CertFamily.card {n N : ℕ} (F : CertFamily O n N) :
    Nat.card F.set = residueCard O ^ F.m * Nat.card F.S := by
  show Nat.card {c : Coeff O n N | ∃ γ, F.cert γ c} = residueCard O ^ F.m * Nat.card F.S
  exact UniformityCheck.card_certSet_gen F.hm F.read F.S F.cert F.hcert F.hshift F.huniq

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.CertFamily.card

end AxCheck
