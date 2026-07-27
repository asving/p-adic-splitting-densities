/-
Unit Sp.reflSucc [REV 2, F8 — both statements in full] — moves_ref: "SUCC(s) :=
{ s′ ∈ 𝒮_n^raw : D(s′) = e·g·D, w(s′) = g·w, W(s′) = μ, …}" and "(G5) STAGE
REACHABILITY: tag = ROOT forces (D, w, W) = (1, 1, n)" (the root-admissibility face).
deps: Sp.reflCoherent, Sp.reflBudget. sketch: match on sel (the StageLaws half);
And-transport with the two reflection iffs. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem succStepB_iff (n : ℕ) (s s' : Species) :
    succStepB n s s' = true ↔ SuccStep n s s' := sorry

theorem rootAdmissibleB_iff (n : ℕ) (s : Species) :
    rootAdmissibleB n s = true ↔ RootAdmissible n s := sorry

end LeanUrat.MovesSp
