/-
Unit Sp.n1RootConfirming [REV 3, G2 — split from the rev-2 Sp.n1Clause to break
the n1singleton cycle: this half has NO n = 3/enum deps] — moves_ref: "At n = 1
the catalogue word is the single ROOT letter (W = n = 1, selection ⊥ — (G6)'s
degenerate degree)".
sketch: RootStage gives W = n = 1; (G6) gives sel = none. difficulty: easy.
hypothesis_fields: (τ-hen) SEMANTICS is VP's — only letter arithmetic stated.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem n1_root_confirming {s : Species} (h : RootAdmissible 1 s) :
    s.W = 1 ∧ s.sel = none := by
  obtain ⟨hRoot, hCoh, _⟩ := h
  have hW : s.W = 1 := hRoot.2.2.2
  exact ⟨hW, hCoh.2.2.2.2.2.mpr hW⟩

end LeanUrat.MovesSp
