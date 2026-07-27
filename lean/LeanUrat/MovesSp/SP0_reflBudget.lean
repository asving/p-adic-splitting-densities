/-
Unit Sp.reflBudget — moves_ref: "(B1)–(B5) are inequalities between INTEGERS
attached to shape fields".
sketch: as reflCoherent. difficulty: easy.
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem budgetB_iff (n : ℕ) (s : Species) : budgetB n s = true ↔ Budget n s := by
  cases hsel : s.sel with
  | none =>
      simp only [budgetB, Budget, hsel, Bool.and_eq_true, decide_eq_true_eq,
        reduceCtorEq, IsEmpty.forall_iff, forall_const, and_true, true_and]
      tauto
  | some gm =>
      simp only [budgetB, Budget, hsel, Bool.and_eq_true, decide_eq_true_eq,
        Option.some.injEq, forall_eq']
      tauto

end LeanUrat.MovesSp
