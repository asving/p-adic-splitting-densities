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

/-- Soundness of the `coherentB` Bool transcription (self-contained restatement of the
`Sp.reflCoherent` face; kept private so it never collides with `coherentB_iff`). -/
private theorem coh_iff (s : Species) : coherentB s = true ↔ Coherent s := by
  unfold coherentB Coherent WellTyped wellTypedB IsComposition
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  rcases hsel : s.sel with _ | gm <;> simp_all [beq_iff_eq] <;> tauto

/-- Soundness of the `budgetB` Bool transcription (self-contained restatement of the
`Sp.reflBudget` face; kept private so it never collides with `budgetB_iff`). -/
private theorem bud_iff (n : ℕ) (s : Species) : budgetB n s = true ↔ Budget n s := by
  unfold budgetB Budget
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rcases hsel : s.sel with _ | gm <;> simp_all <;> tauto

/-- Reflection of the (D.10) POST-INC / POST-REC tag clauses of `StageLaws`:
a decidable-equality `==` set equal to a Bool `c` unfolds to a Prop-level `↔`.
Applied once (via `Bool.eq_iff_iff` + `beq_iff_eq`) so it cannot loop the way the
general `Bool.eq_iff_iff` does as a simp lemma. -/
private theorem beq_eq_iff {α : Type*} [DecidableEq α] (a b : α) (c : Bool) :
    ((a == b) = c) ↔ (a = b ↔ c = true) := by
  rw [Bool.eq_iff_iff, beq_iff_eq]

theorem succStepB_iff (n : ℕ) (s s' : Species) :
    succStepB n s s' = true ↔ SuccStep n s s' := by
  unfold succStepB SuccStep StageLaws
  simp only [Bool.and_eq_true, coh_iff, bud_iff]
  rcases hsel : s.sel with _ | gm <;> simp_all [beq_eq_iff, decide_eq_true_eq]
  tauto

theorem rootAdmissibleB_iff (n : ℕ) (s : Species) :
    rootAdmissibleB n s = true ↔ RootAdmissible n s := by
  unfold rootAdmissibleB RootAdmissible RootStage
  simp only [Bool.and_eq_true, coh_iff, bud_iff, beq_iff_eq]
  tauto

end LeanUrat.MovesSp
