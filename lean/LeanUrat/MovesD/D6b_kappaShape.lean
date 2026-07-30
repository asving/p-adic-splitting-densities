/-
Unit D6b.kappaH_shape  (MovesD campaign, E-phase)
moves_ref: (L9 — κ_r = h_r/(e_r·STR_r) is shape data).
deps (blueprint): D6a.  [as-built, 2026-07-30 verify-2 fold-in: imports only Defs;
D6a's content is inlined — the retained-e lists' nodewise agreement is re-derived here.]
sketch: getElem?-elim; Matches e/h + D6a.  difficulty: easy.  hypothesis_fields: none.
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

/-- The level weights κ_r are shape data. -/
theorem kappaH_shape {H : History p F} (hP : (P : ShapePrefix).MatchesHist H) :
    ∀ r, H.kappaH r = (P : ShapePrefix).kappaS r := by
  obtain ⟨hlen, hmatch⟩ := hP
  -- The retained ramification indices agree nodewise, hence as mapped lists.
  have hmapE : H.nodes.map Node.e = (P : ShapePrefix).reads.map ShapeRead.e := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 _
      have hi : i < H.nodes.length := by simpa using h1
      simpa using (hmatch i hi).2.1
  -- The accumulated stretch STR_r is shape data (D6a, proved inline).
  have hstr : ∀ r, H.strFrame r = (P : ShapePrefix).strS r := by
    intro r
    simp only [History.strFrame, ShapePrefix.strS]
    congr 1
    rw [List.map_take, List.map_take, hmapE]
  intro r
  simp only [History.kappaH, ShapePrefix.kappaS]
  rcases Nat.lt_or_ge r H.nodes.length with hr | hr
  · rw [List.getElem?_eq_getElem hr, List.getElem?_eq_getElem (hlen ▸ hr)]
    have hm := hmatch r hr
    simp only [Option.elim_some]
    rw [hm.2.1, hm.2.2.1, hstr r]
  · rw [List.getElem?_eq_none hr, List.getElem?_eq_none (hlen ▸ hr)]
    simp

end LeanUrat.MovesD
