/-
Unit D6e.prevRim_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — the rim thresholds μ_{i−1}·D_i are shape data).
deps: Defs.
sketch: case split on i; getElem?-elim; Matches μ/e/g/Dwidth.  difficulty: easy.
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

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {P : Shape n}

/-- The rim thresholds are shape data. -/
theorem prevRim_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i, H.prevRim n i = (P : ShapePrefix).prevRimS n i := by
  obtain ⟨hlen, hmatch⟩ := hP
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [History.prevRim, ShapePrefix.prevRimS]
    by_cases hi : i < H.nodes.length
    · rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)]
      obtain ⟨_, he, _, hg, hμ, _, _, _, hDw, _, _, _, _⟩ := hmatch i hi
      simp only [Option.elim, Node.childWidth, ShapeRead.childWidthS]
      rw [hμ, he, hg, hDw]
    · rw [not_lt] at hi
      rw [List.getElem?_eq_none hi, List.getElem?_eq_none (hlen ▸ hi)]
      rfl

end LeanUrat.MovesD
