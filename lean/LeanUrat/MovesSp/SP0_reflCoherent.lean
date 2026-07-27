/-
Unit Sp.reflCoherent — moves_ref: "(G1)–(G6) … A species tuple is GEOMETRICALLY
COHERENT iff" (the display).
sketch: unfold both; `decide`-friendly Bool/Prop transcription,
`simp [coherentB, Coherent, List.all_eq_true, …]`. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem coherentB_iff (s : Species) : coherentB s = true ↔ Coherent s := by
  simp only [coherentB, Coherent, WellTyped, IsComposition, wellTypedB,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  cases hsel : s.sel <;>
    simp_all <;> tauto

end LeanUrat.MovesSp
