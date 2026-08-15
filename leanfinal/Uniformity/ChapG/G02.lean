/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G01

/-!
# Uniformity.ChapG.G02 — `exactVal_iff_addVal` / `exactVal_unique`

**Chapter G, NODE G.02** (`blueprint/CHAP-G_base_cases_menus.md` §3). `ExactVal π k x` holds iff
`x ≠ 0` and `addVal O x = k`; and `ExactVal π k x` with `ExactVal π k' x` forces `k = k'`.

DEPENDS: G.01 · landed `Uniformity.Density.addVal_eq_of_dvd_not_dvd` (`Drainage.lean:101`),
`Uniformity.Density.pow_dvd_iff_le` (`Drainage.lean:95`), `Uniformity.Density.exists_addVal_eq`
(`Drainage.lean:90`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem exactVal_iff_addVal (hπ : Irreducible π) {k : ℕ} {x : O} :
    ExactVal π k x ↔ IsDiscreteValuationRing.addVal O x = (k : ℕ∞) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact addVal_eq_of_dvd_not_dvd hπ h1 h2
  · intro hx
    refine ⟨(pow_dvd_iff_le hπ hx k).2 le_rfl, fun hcon => ?_⟩
    have := (pow_dvd_iff_le hπ hx (k + 1)).1 hcon
    omega

theorem exactVal_unique (hπ : Irreducible π) {k k' : ℕ} {x : O}
    (h : ExactVal π k x) (h' : ExactVal π k' x) : k = k' := by
  have e1 := (exactVal_iff_addVal hπ).1 h
  have e2 := (exactVal_iff_addVal hπ).1 h'
  rw [e1] at e2
  exact_mod_cast e2

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.exactVal_iff_addVal
#print axioms Uniformity.Density.Menu.exactVal_unique

end AxCheck
