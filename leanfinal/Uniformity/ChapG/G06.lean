/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G05

/-!
# Uniformity.ChapG.G06 — `CertFamily.decidedAt`

**Chapter G, NODE G.06** (`blueprint/CHAP-G_base_cases_menus.md` §3). Every class of a certified
family's set is `σ`-decided at level `N`.

DEPENDS: G.05 · landed `Uniformity.Density.DecidedAt` (`GenuineDensity.lean:66`),
`Uniformity.Density.proj_surjective` (`LocalData.lean:138`).

**NOTE (transcription fidelity).** The Lean schema field `hforce` is not the corpus's
`disc ≠ 0`-restricted Ore clause: it is a hypothesis each instance must discharge for *all*
lifts, which the `n = 2` instances of §5 do (valuation-theoretic, not Ore-theoretic; `typeOf` is
total). No instance in this chapter may be justified by citing HMENU3's (A0).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem CertFamily.decidedAt {n N : ℕ} (F : CertFamily O n N) {c : Coeff O n N}
    (hc : c ∈ F.set) : DecidedAt O n F.σ N c := by
  obtain ⟨γ, hγ⟩ := hc
  intro a ha
  exact F.hforce γ a (ha ▸ hγ)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.CertFamily.decidedAt

end AxCheck
