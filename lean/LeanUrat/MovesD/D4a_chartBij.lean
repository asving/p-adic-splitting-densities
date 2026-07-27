/-
Unit D4a.chart_bij  (MovesD campaign, E-phase)  [AUX]
informal: a JetSetup's ≺-sorted chart is a bijection onto the N×n grid.
deps: MovesC.Defs.
sketch: injectivity from `coordOf_sorted` + `CoordPrec` irreflexivity; surjectivity from
injective-into-a-grid-of-card-m (`J.hm`, pigeonhole).  difficulty: medium.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}

/-- The ≺-sorted chart is a bijection onto the N×n grid. -/
theorem chart_bij {H : History p F} (J : JetSetup H n N m) :
    Function.Injective J.coordOf ∧
      ∀ c ∈ Finset.range N ×ˢ Finset.range n, ∃ j : Fin m, J.coordOf j = c := by
  -- `CoordPrec` is irreflexive: no coordinate precedes itself.
  have hirr : ∀ c : Coord, ¬ CoordPrec c c := by
    intro c hc
    rcases hc with h | ⟨-, h⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h
  -- Injectivity: distinct indices are ≺-ordered, so equal charts are impossible.
  have hinj : Function.Injective J.coordOf := by
    intro j j' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp := (J.coordOf_sorted j j').1 hlt
      rw [h] at hp
      exact hirr _ hp
    · have hp := (J.coordOf_sorted j' j).1 hgt
      rw [h] at hp
      exact hirr _ hp
  refine ⟨hinj, ?_⟩
  -- Surjectivity: an injection of `Fin m` into the grid of card `m` fills it.
  intro c hc
  have hsub : Finset.univ.image J.coordOf ⊆ Finset.range N ×ˢ Finset.range n := by
    intro c' hc'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc'
    obtain ⟨j, rfl⟩ := hc'
    simp only [Finset.mem_product, Finset.mem_range]
    exact J.coordOf_lt j
  have hcard_img : (Finset.univ.image J.coordOf).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcard_grid : (Finset.range N ×ˢ Finset.range n).card = m := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range, J.hm]
    ring
  have heq : Finset.univ.image J.coordOf = Finset.range N ×ˢ Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard_grid, hcard_img]))
  have hmem : c ∈ Finset.univ.image J.coordOf := by rw [heq]; exact hc
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, hj⟩

end LeanUrat.MovesD
