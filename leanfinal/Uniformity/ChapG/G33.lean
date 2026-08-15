/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G33 — `exists_split_lift`

**Chapter G, NODE G.33** (`blueprint/CHAP-G_base_cases_menus.md` §6). A class with a depth-`N`
centre has a `splitType` lift: kill the value at the centre.

DEPENDS: landed `Uniformity.Density.typeOf_split_of_root` (`Drainage.lean:263`),
`Uniformity.Density.proj_eq_iff_dvd` (`DensityAPI.lean:124`), `Uniformity.Density.qval`.

**PROOF (blueprint).**
1. put `b := ![a 0 - qval a γ, a 1]`.
2. `qval b γ = qval a γ - qval a γ = 0` by `simp [qval]; ring`.
3. `typeOf_split_of_root` gives `typeOf (monicPoly b) = splitType`.
4. `proj O 2 N b = proj O 2 N a`: by `proj_eq_iff_dvd hπ`, coordinatewise; the `1`-coordinate is
   equal, the `0`-coordinate differs by `qval a γ`, which `hT.1` says is `π^N`-divisible.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem exists_split_lift (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = splitType := by
  refine ⟨![a 0 - qval a γ, a 1], ?_, ?_⟩
  · rw [proj_eq_iff_dvd hπ]
    intro i
    fin_cases i <;> simp [hT.1]
  · apply typeOf_split_of_root (R := γ)
    show qval ![a 0 - qval a γ, a 1] γ = 0
    simp only [qval, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

section AxCheck
#print axioms Uniformity.Density.Menu.exists_split_lift
end AxCheck

end Uniformity.Density.Menu
