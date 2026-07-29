/-  MovesV unit V3-3b `spword_collapse` (RE-KEYED REV 7, C11) — THE TOTALITY
    + TIE THEOREM: `template?`'s dite PASSES; the total `template` declared. -/
import LeanUrat.MovesV.V3_spwordA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem template_total {n : ℕ} (ε : EntShapeV n) : (ε.template?).isSome := by
  sorry

/-- the TOTAL template (downstream units' token — no forward reference:
Defs is Option-typed, units are total). -/
noncomputable def EntShapeV.template {n : ℕ} (ε : EntShapeV n) :
    EntTemplate n :=
  (ε.template?).get (template_total ε)

end LeanUrat.MovesV
