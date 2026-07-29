/-  MovesV unit V3-3a `spword_exists` (RE-KEYED REV 9, N-3) — the dite PASSES
    on WF prefixes. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem spWord_exists (n : ℕ) (P : MovesD.ShapePrefix)
    (hWF : MovesD.ShapeWF n P) : ∃ ws, SpWordFits n P ws := by
  sorry

theorem spWord_fits (n : ℕ) (P : MovesD.ShapePrefix)
    (hWF : MovesD.ShapeWF n P) : SpWordFits n P (spWord n P) := by
  rw [spWord, dif_pos (spWord_exists n P hWF)]
  exact (spWord_exists n P hWF).choose_spec

end LeanUrat.MovesV
