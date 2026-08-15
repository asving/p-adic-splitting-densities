/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G26 — `depth_even_dichotomy`, the even-depth residual dichotomy

**Chapter G, NODE G.26** (`blueprint/CHAP-G_base_cases_menus.md` §5). *The even-depth
dichotomy.* At a witnessing centre of even depth exactly `2k`, write `qval a γ = π^(2k)·b₀`,
`qder a γ = π^k·b₁`. Then **either** `![b₀, b₁]` is anisotropic, **or** the residual quadratic
`y² + b₁y + b₀` has a root `z̄` mod `𝔪` at which it is *simple* (i.e. `π ∤ (b₁ + 2z)`). The
remaining case — a residual double root — is impossible, because it would produce a centre of
depth `2k+1`.

DEPENDS: landed `Anisotropic` (`QuadCert.lean:340`), `exists_residual_root`
(`Drainage.lean:523`), `qval_shift`, `qder_shift`, `Tang`.

This node is a re-cut of the landed `cert_of_not_tang`'s even branch (`Drainage.lean:589–619`),
which performs exactly this case split inline; the chapter needs it standalone because the
census keys strata by the residual class.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem depth_even_dichotomy (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a (2 * k) γ) (hmax : ¬ ∃ γ', Tang π a (2 * k + 1) γ')
    {b₀ b₁ : O} (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁) :
    Anisotropic ![b₀, b₁] ∨ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z) := by
  by_cases haniso : Anisotropic ![b₀, b₁]
  · exact Or.inl haniso
  · obtain ⟨z, hz⟩ := exists_residual_root hπ haniso
    have hval' : π ^ (2 * k + 1) ∣ qval a (γ + π ^ k * z) := by
      rw [qval_shift, h0, h1]
      obtain ⟨c, hc⟩ := hz
      exact ⟨c, by linear_combination (π ^ (2 * k)) * hc⟩
    have hder' : qder a (γ + π ^ k * z) = π ^ k * (b₁ + 2 * z) := by
      rw [qder_shift, h1]; ring
    by_cases hdd : π ∣ (b₁ + 2 * z)
    · exfalso
      refine hmax ⟨γ + π ^ k * z, hval', ?_⟩
      rw [show ((2 * k + 1) + 1) / 2 = k + 1 by omega, hder']
      obtain ⟨c, hc⟩ := hdd
      exact ⟨c, by rw [hc]; ring⟩
    · exact Or.inr ⟨z, hz, hdd⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.depth_even_dichotomy

end AxCheck
