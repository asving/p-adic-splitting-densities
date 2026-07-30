/-
Unit D4b.chart_count  (MovesD campaign, E-phase)  [AUX]
informal: pulled-back predicate counts over `Fin m` = grid filter counts.
deps: D4a.
sketch: `Nat.card_congr` along D4a's bijection; `Finset.card_filter` bridging.
difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D4a_chartBij

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}

/-- Chart-pulled predicate counts equal grid filter counts. -/
theorem chart_count {H : History p F} (J : JetSetup H n N m) (φ : Coord → Prop)
    [DecidablePred φ] :
    Nat.card {c : Fin m // φ (J.coordOf c)}
      = ((Finset.range N ×ˢ Finset.range n).filter (fun c => φ c)).card := by
  obtain ⟨hinj, hsurj⟩ := chart_bij J
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun (a : Fin m) _ => J.coordOf a) ?_ ?_ ?_
  · -- image lands in the φ-filtered grid
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨J.coordOf_lt a, ha⟩
  · -- injectivity of the chart
    intro a₁ _ a₂ _ h
    exact hinj h
  · -- surjectivity onto the φ-filtered grid, via D4a's grid-surjectivity
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb
    obtain ⟨⟨hb1, hb2⟩, hφ⟩ := hb
    obtain ⟨a, ha⟩ := hsurj b (by
      simp only [Finset.mem_product, Finset.mem_range]; exact ⟨hb1, hb2⟩)
    refine ⟨a, ?_, ha⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha]
    exact hφ

end LeanUrat.MovesD
