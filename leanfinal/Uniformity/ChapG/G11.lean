/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G02

/-!
# Uniformity.ChapG.G11 — `tang_centre_unique`, centre uniqueness

**Chapter G, NODE G.11** (`blueprint/CHAP-G_base_cases_menus.md` §4). *Centre uniqueness.* Two
centres of depth `≥ t` for the same `a` are congruent mod `π^⌈t/2⌉`.

DEPENDS: G.02 · landed `qval_shift`, `qder_shift`, `Uniformity.Density.pow_dvd_iff_le`,
`exists_addVal_eq`, `pow_dvd_right_of_mul` (`Drainage.lean:116`).

**On the private helper.** The blueprint's step 5 ("valuation of a sum with unequal valuations")
is exactly mathlib's `AddValuation.map_add_eq_of_lt_left`, so no bespoke helper is needed; the
node lands as a single declaration.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem tang_centre_unique (hπ : Irreducible π) {a : Fin 2 → O} {t : ℕ} {γ γ' : O}
    (h : Tang π a t γ) (h' : Tang π a t γ') : π ^ ((t + 1) / 2) ∣ (γ' - γ) := by
  by_contra hcon
  set δ : O := γ' - γ with hδdef
  have hδne : δ ≠ 0 := ne_zero_of_not_dvd hcon
  obtain ⟨x, hx⟩ := exists_addVal_eq hδne
  have hxlt : x < (t + 1) / 2 := by
    by_contra hge
    exact hcon ((pow_dvd_iff_le hπ hx _).2 (not_lt.1 hge))
  have hγ'eq : γ' = γ + δ := by rw [hδdef]; ring
  have hval_eq : qval a γ' = qval a γ + δ * (qder a γ + δ) := by
    rw [hγ'eq, qval_shift]; ring
  have hdvd_prod : π ^ t ∣ δ * (qder a γ + δ) := by
    have h2 : π ^ t ∣ qval a γ + δ * (qder a γ + δ) := hval_eq ▸ h'.1
    simpa using dvd_sub h2 h.1
  have hderge : ((t + 1) / 2 : ℕ) ≤ IsDiscreteValuationRing.addVal O (qder a γ) :=
    (pow_dvd_iff_le_addVal hπ _ _).1 h.2
  have hxval :
      IsDiscreteValuationRing.addVal O δ < IsDiscreteValuationRing.addVal O (qder a γ) := by
    rw [hx]
    calc (x : ℕ∞) < ((t + 1) / 2 : ℕ) := by exact_mod_cast hxlt
    _ ≤ IsDiscreteValuationRing.addVal O (qder a γ) := hderge
  have hsum' : IsDiscreteValuationRing.addVal O (qder a γ + δ) = (x : ℕ∞) := by
    rw [add_comm, AddValuation.map_add_eq_of_lt_left (IsDiscreteValuationRing.addVal O) hxval, hx]
  have hprodval :
      IsDiscreteValuationRing.addVal O (δ * (qder a γ + δ)) = ((2 * x : ℕ) : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_mul, hx, hsum', two_mul, Nat.cast_add]
  have ht_le : t ≤ 2 * x := (pow_dvd_iff_le hπ hprodval t).1 hdvd_prod
  omega

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.tang_centre_unique

end AxCheck
