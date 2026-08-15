/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G50 — the degree-2 type trichotomy

**Chapter G, NODE G.50** (`blueprint/CHAP-G_base_cases_menus.md` §7). Every degree-2 splitting
type is one of the three, so the density function at `n = 2` is completely determined by G.48.

DEPENDS: landed `Uniformity.Density.genuineDensity_two_eq_zero` (`Drainage.lean:1037`).

**Design note (blueprint, verbatim).** The fourth disjunct is deliberately *not* a claim that no
other degree-2 type exists as a `FactorizationType` (e.g. `⟨{(1,1)}⟩ + ⟨{(1,1)}⟩` in a different
`Multiset` presentation is `splitType`, but `⟨{(2,2)}⟩` has degree 4 and
`⟨{(1,1),(1,1),(1,1)}⟩` degree 3); it is the density statement, which is what the capstone
needs.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

theorem degree_two_type_cases {σ : FactorizationType} (hσ : σ.degree = 2) :
    σ = splitType ∨ σ = inertType ∨ σ = ramType ∨
      (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        genuineDensity O 2 σ = 0) := by
  by_cases hs : σ = splitType
  · exact Or.inl hs
  by_cases hi : σ = inertType
  · exact Or.inr (Or.inl hi)
  by_cases hr : σ = ramType
  · exact Or.inr (Or.inr (Or.inl hr))
  · exact Or.inr (Or.inr (Or.inr (fun O _ _ _ _ _ => genuineDensity_two_eq_zero hs hi hr)))

section AxCheck
#print axioms Uniformity.Density.degree_two_type_cases
end AxCheck

end Uniformity.Density
