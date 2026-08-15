/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G52
import Uniformity.ChapG.G53
import Uniformity.ChapG.G54
import Uniformity.Density.GenuineDensity

/-!
# Uniformity.ChapG.G72 — `totalMass_three_of_drainage` / `one_le_sum_three`

**Chapter G, NODE G.72** (`blueprint/CHAP-G_base_cases_menus.md` §9). `Σ_σ R_σ = 1` at `n = 3`
over the five-type menu, GIVEN drainage; and unconditionally `Σ_σ R_σ ≥ 1`.

DEPENDS: G.52, G.53, G.54 · landed `sum_genuineDensity_eq_one_of_drainage`,
`one_le_sum_genuineDensity`.

**TEETH.** `HM3-RTAU` → executable regression (the individual five values stay unproved here;
this node only gives the sum).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The explicit five-element `Finset` sum unfolds to the flat sum, using the four distinctness
side conditions at each `insert` step — exactly the ten conjuncts of `c3_pairwise_ne`. -/
private theorem g72_sum_expand (f : FactorizationType → ℝ) :
    ∑ σ ∈ ({c3split, c3linInert, c3inert, c3linRam, c3ram} : Finset FactorizationType), f σ
      = f c3split + f c3linInert + f c3inert + f c3linRam + f c3ram := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := c3_pairwise_ne
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h1, h2, h3, h4⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h5, h6, h7⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h8, h9⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact h10),
      Finset.sum_singleton]
  ring

theorem totalMass_three_of_drainage [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hd : ∀ σ : FactorizationType, UndecidedVanishes O 3 σ) :
    genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram = 1 := by
  have h := sum_genuineDensity_eq_one_of_drainage coveringMenu_three (fun σ _ => hd σ)
  rwa [g72_sum_expand (genuineDensity O 3)] at h

theorem one_le_sum_three :
    1 ≤ genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram := by
  have h := one_le_sum_genuineDensity (O := O) coveringMenu_three
  rwa [g72_sum_expand (genuineDensity O 3)] at h

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.totalMass_three_of_drainage
#print axioms Uniformity.Density.one_le_sum_three

end AxCheck
