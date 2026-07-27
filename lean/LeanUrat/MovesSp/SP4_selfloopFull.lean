/-
Unit Sp.selfloopFull [REV 2, F13 — hypothesis types in full] — moves_ref: "n = 3
check: the two loop classes Q2.3▸(1,2) and Q3▸(1,3) are exactly the full POST-REC
letters at stages (1,1,2) and (1,1,3), per (i)."
deps: Sp.selfloopChar. sketch: unfold IsFull; direct from the characterization.
difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem selfloop_isFull {n : ℕ} {s : Species} (hc : Coherent s)
    (hb : Budget n s) (h : SuccStep n s s) : IsFull s ∧ s.tag = .postRec := sorry

end LeanUrat.MovesSp
