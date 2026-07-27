/-
Unit Sp.compEncode — moves_ref: "the two flank compositions as indicator vectors
of their cut sets (≤ 2n entries, spans ≤ n by (B5))."
sketch: partial sums of a positive composition are strictly monotone; recover
parts as gaps of the sorted cut set; induction on lists. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- partial-sum cut set of a composition (blueprint: body = P-phase work). -/
def compCuts (c : List ℕ) : Finset ℕ := sorry

theorem compCuts_inj {span} {c c' : List ℕ} (h : IsComposition c span)
    (h' : IsComposition c' span) (he : compCuts c = compCuts c') : c = c' := sorry

end LeanUrat.MovesSp
