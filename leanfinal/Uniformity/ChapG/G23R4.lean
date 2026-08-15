/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G23R1
import Uniformity.ChapG.G23R2

/-!
# Uniformity.ChapG.G23R4 — `resTop` / `resAdm` / `resClassSet`, and the preimage identity

**Chapter G, NODE G.23R4** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). Three objects and one identity:

* `resAdm π P k N ⊆ Res O N × Res O N` — the admissible set of the residual-class family: the
  `(value, derivative)` pairs of the shape `(π^(2k)·y₀, π^k·y₁)` whose digit pair `(ȳ₀, ȳ₁)`
  lies in `P`. It refines `tangAdm π (2k) N` (G.15) by the digit condition, so the route's
  certificate is A-1's `cert_𝒫`.
* `resTop π P k ⊆ Res O (2k+1) × Res O (k+1)` — the same read at the TOP levels, where the two
  digits are exactly determined and the set is a copy of `P` (G.23R5).
* `resClassSet π P k N ⊆ Coeff O 2 N` — the level-`N` classes certified by the family.
* `resAdm_eq_preimage` — `resAdm` is the preimage of `resTop` under `prodResFactor` (G.23R1),
  which is what turns the count into a fibre count.

DEPENDS: G.23R1, G.23R2 · landed `Res`, `resFactor`, `resFactor_mk`, `qval`, `qder`, `proj`,
`mem_maximalIdeal_pow_iff_dvd`, `mem_maximalIdeal_iff_dvd`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- The residual-class admissible set read at the TOP levels `(2k+1, k+1)`. -/
def resTop (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k : ℕ) :
    Set (Res O (2 * k + 1) × Res O (k + 1)) :=
  {x | ∃ y₀ y₁ : O,
      x = (Ideal.Quotient.mk _ (π ^ (2 * k) * y₀), Ideal.Quotient.mk _ (π ^ k * y₁))
        ∧ (IsLocalRing.residue O y₀, IsLocalRing.residue O y₁) ∈ P}

/-- The residual-class admissible set at level `N`: the `(value, derivative)` reads of the shape
`(π^(2k)·y₀, π^k·y₁)` whose digit pair lies in `P`. -/
def resAdm (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
    (k N : ℕ) : Set (Res O N × Res O N) :=
  {x | ∃ y₀ y₁ : O,
      x = (Ideal.Quotient.mk _ (π ^ (2 * k) * y₀), Ideal.Quotient.mk _ (π ^ k * y₁))
        ∧ (IsLocalRing.residue O y₀, IsLocalRing.residue O y₁) ∈ P}

/-- The level-`N` classes carrying a residual pair in `P` at some centre of depth `≥ 2k`. -/
def resClassSet (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O))
    (k N : ℕ) : Set (Coeff O 2 N) :=
  {c | ∃ (a : Fin 2 → O) (γ b₀ b₁ : O), proj O 2 N a = c ∧
      qval a γ = π ^ (2 * k) * b₀ ∧ qder a γ = π ^ k * b₁ ∧
      (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ P}

/-- A level-`N` class whose level-`(j+1)` truncation reads `π ^ j · y` is itself of the shape
`π ^ j · y'` with the same digit. -/
private theorem exists_digit_of_resFactor (hπ : Irreducible π) {j N : ℕ} (h : j + 1 ≤ N)
    {x : Res O N} {y : O}
    (hx : resFactor (O := O) h x = Ideal.Quotient.mk _ (π ^ j * y)) :
    ∃ y' : O, x = Ideal.Quotient.mk _ (π ^ j * y') ∧
      IsLocalRing.residue O y' = IsLocalRing.residue O y := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) x
  rw [resFactor_mk] at hx
  obtain ⟨s, hs⟩ := (mem_maximalIdeal_pow_iff_dvd hπ (j + 1) _).1 (Ideal.Quotient.eq.1 hx)
  refine ⟨y + π * s, ?_, ?_⟩
  · have hw : w = π ^ j * (y + π * s) := by linear_combination hs
    rw [hw]
  · exact Ideal.Quotient.eq.2 ((mem_maximalIdeal_iff_dvd hπ _).2 ⟨s, by ring⟩)

/-- **The route's counting identity in set form**: the level-`N` admissible set is the preimage
of the TOP-level one. -/
theorem resAdm_eq_preimage (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)} {k N : ℕ}
    (h₀ : 2 * k + 1 ≤ N) (h₁ : k + 1 ≤ N) :
    resAdm π P k N = prodResFactor (O := O) h₀ h₁ ⁻¹' resTop π P k := by
  ext x
  constructor
  · rintro ⟨y₀, y₁, rfl, hP⟩
    exact ⟨y₀, y₁, by simp [resFactor_mk], hP⟩
  · rintro ⟨y₀, y₁, heq, hP⟩
    rw [prodResFactor_apply, Prod.ext_iff] at heq
    obtain ⟨z₀, hz₀, hr₀⟩ := exists_digit_of_resFactor hπ h₀ heq.1
    obtain ⟨z₁, hz₁, hr₁⟩ := exists_digit_of_resFactor hπ h₁ heq.2
    exact ⟨z₀, z₁, Prod.ext_iff.2 ⟨hz₀, hz₁⟩, by rw [hr₀, hr₁]; exact hP⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.resTop
#print axioms Uniformity.Density.Menu.resAdm
#print axioms Uniformity.Density.Menu.resClassSet
#print axioms Uniformity.Density.Menu.resAdm_eq_preimage

end AxCheck
