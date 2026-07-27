/-
Unit XG.2c interTrichotomy — X.3(d)'s first half, DERIVED (finding 11)
[E-phase: stated, body sorry]
moves_ref: "(d) … an f whose complete tree is undetected at EVERY level has an ns leaf
(TB-CAP's clause trichotomy — detection fails at all N only on the (τ-ns) class)".
sketch: f ∉ InfTree ⟹ Finite (Branch f); if every leaf ns-free, XG.2b exits f from some
Undec N — contradiction; so some leaf carries an ns node; `C.nsCover` places f in a
fiber. deps: XG.2b. difficulty: MEDIUM. hyp_fields: nsCover ((NS-c) input).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XG2b

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem interTrichotomy {n p : ℕ} [Fact p.Prime] (C : XCtx n p) :
    (⋂ N, C.Undec N) ⊆ InfTree C ∪ (⋃ i, C.nsFiber i) := by
  sorry

end LeanUrat.MovesX
