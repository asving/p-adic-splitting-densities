/-
Unit D6a.strFrame_shape  (MovesD campaign, E-phase)
moves_ref: (L9's "SHAPE data" — STR_i = ∏_{m<i} e_m).
deps: Defs.
sketch: List.take/map congruence from Matches' e-clause.  difficulty: easy.
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

/-- The history stretch is shape data. -/
theorem strFrame_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ i, H.strFrame i = (P : ShapePrefix).strS i := by
  obtain ⟨hlen, hmatch⟩ := hP
  have hmap : H.nodes.map Node.e = (P : ShapePrefix).reads.map ShapeRead.e := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_map, hlen]
    · intro k h₁ _
      rw [List.length_map] at h₁
      simp only [List.getElem_map]
      exact (hmatch k h₁).2.1
  intro i
  unfold History.strFrame ShapePrefix.strS
  rw [List.map_take, List.map_take, hmap]

end LeanUrat.MovesD
