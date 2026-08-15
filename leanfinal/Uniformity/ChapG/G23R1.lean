/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapG.G23R1 — `prodResFactor`, the two-coordinate truncation and its fibre count

**Chapter G, NODE G.23R1** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The route counts the residual-class admissible set as
the preimage of a TOP-level set under the two-coordinate truncation
`Res O N × Res O N → Res O m₀ × Res O m₁`; this node supplies that map as an additive group
homomorphism together with the fibre count `#(f ⁻¹' S) · q^(m₀+m₁) = q^N · q^N · #S`.

The count is stated **subtraction-free** (chapter discipline, G.14's shape): the kernel size
`q^(N−m₀) · q^(N−m₁)` never appears; it is eliminated by applying
`card_preimage_of_surjective` twice — once at `S`, once at `Set.univ` — exactly as
`card_dvdSet` (G.14) does.

DEPENDS: landed `Uniformity.Density.resFactor`, `resFactor_surjective`, `card_res`,
`card_preimage_of_surjective` (`LocalData.lean:192,215,221,228`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- The two-coordinate truncation `Res O N × Res O N → Res O m₀ × Res O m₁`, as an additive
group homomorphism (the form `card_preimage_of_surjective` consumes). -/
def prodResFactor {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N) :
    (Res O N × Res O N) →+ (Res O m₀ × Res O m₁) where
  toFun x := (resFactor h₀ x.1, resFactor h₁ x.2)
  map_zero' := by simp
  map_add' x y := by simp

omit [Finite (IsLocalRing.ResidueField O)] in
@[simp] theorem prodResFactor_apply {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N)
    (x : Res O N × Res O N) :
    prodResFactor (O := O) h₀ h₁ x = (resFactor h₀ x.1, resFactor h₁ x.2) := rfl

theorem prodResFactor_surjective {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N) :
    Function.Surjective (prodResFactor (O := O) h₀ h₁) := by
  rintro ⟨u, v⟩
  obtain ⟨x, rfl⟩ := resFactor_surjective (O := O) h₀ u
  obtain ⟨y, rfl⟩ := resFactor_surjective (O := O) h₁ v
  exact ⟨(x, y), rfl⟩

/-- **The two-coordinate fibre count, subtraction-free.** -/
theorem card_preimage_prodResFactor {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N)
    (S : Set (Res O m₀ × Res O m₁)) :
    Nat.card (prodResFactor (O := O) h₀ h₁ ⁻¹' S) * (residueCard O ^ m₀ * residueCard O ^ m₁)
      = residueCard O ^ N * residueCard O ^ N * Nat.card S := by
  classical
  have hsurj := prodResFactor_surjective (O := O) h₀ h₁
  have hS := card_preimage_of_surjective (prodResFactor (O := O) h₀ h₁) hsurj S
  have hU := card_preimage_of_surjective (prodResFactor (O := O) h₀ h₁) hsurj Set.univ
  rw [Set.preimage_univ] at hU
  have hu1 : Nat.card (Set.univ : Set (Res O N × Res O N))
      = residueCard O ^ N * residueCard O ^ N := by
    rw [Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_prod, card_res]
  have hu2 : Nat.card (Set.univ : Set (Res O m₀ × Res O m₁))
      = residueCard O ^ m₀ * residueCard O ^ m₁ := by
    rw [Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_prod, card_res, card_res]
  rw [hu1, hu2] at hU
  rw [hS, hU]
  ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.prodResFactor
#print axioms Uniformity.Density.Menu.card_preimage_prodResFactor

end AxCheck
