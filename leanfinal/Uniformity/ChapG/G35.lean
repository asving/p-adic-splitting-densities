/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G09
import Uniformity.ChapG.G29
import Uniformity.ChapG.G33
import Uniformity.ChapG.G34

/-!
# Uniformity.ChapG.G35 — `undecidedSet_eq_tangSet`

**Chapter G, NODE G.35** (`blueprint/CHAP-G_base_cases_menus.md` §6). The undecided level-`N`
classes are *exactly* the classes admitting a centre of tangency depth `N` — the level-`N`
tangency-filtration set `tangSet π N N` (G.09). `undecidedSet O 2 N = tangSet π N N`.

DEPENDS: G.09, G.12, G.29, G.33, G.34 · landed `undecidedSet`, `UndecidedAt`,
`splitType_ne_inertType`, `proj_surjective`.

**PROOF.**
* (⊇) Let `c ∈ tangSet π N N`, witnessed by a lift `a` and a centre `γ` of tangency depth `N`.
  If some `σ` were `DecidedAt` on `c`, then G.33's split lift and G.34's inert lift of `a` (both
  projecting to `c`) would force `splitType = σ = inertType`, contradicting
  `splitType_ne_inertType`. So no `σ` is decided: `c ∈ undecidedSet O 2 N`.
* (⊆) Contrapositive: if `c ∉ tangSet π N N`, take any lift `a` of `c` (`proj_surjective`); G.29
  gives `DecidedAt O 2 (typeOf (monicPoly a)) N c`, so some type IS decided on `c`, i.e.
  `c ∉ undecidedSet O 2 N` (`UndecidedAt` demands NO type is decided).

**TEETH.** `W11-EXHAUST` / P-4 → Lean theorem (this node discharges exactly that check).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **G.35.** The undecided level-`N` classes are exactly the level-`N` tangency-filtration
set: `undecidedSet O 2 N = tangSet π N N`. -/
theorem undecidedSet_eq_tangSet (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    undecidedSet O 2 N = tangSet π N N := by
  ext c
  constructor
  · intro hu
    by_contra hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    exact hu _ (decidedAt_of_depth_lt hπ hc ha)
  · rintro ⟨a, ha, γ, hT⟩
    intro σ hσ
    obtain ⟨b₁, hb₁proj, hb₁type⟩ := exists_split_lift hπ hT
    obtain ⟨b₂, hb₂proj, hb₂type⟩ := exists_inert_lift hπ hT
    have h1 : typeOf (monicPoly b₁) = σ := hσ b₁ (hb₁proj.trans ha)
    have h2 : typeOf (monicPoly b₂) = σ := hσ b₂ (hb₂proj.trans ha)
    have hs : splitType = σ := hb₁type.symm.trans h1
    have hi : inertType = σ := hb₂type.symm.trans h2
    exact splitType_ne_inertType (hs.trans hi.symm)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.undecidedSet_eq_tangSet

end AxCheck
