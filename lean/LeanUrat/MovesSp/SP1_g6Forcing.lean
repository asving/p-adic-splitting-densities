/-
Unit Sp.g6Forcing — moves_ref: "(G6) TERMINAL RULE: selection = ⊥ iff W = 1.
[A W = 1 window forces the whole side datum — e = ℓ = 1, s₀′ = a = 0, λ = {(1,1)},
no flanks —]".
sketch: s0 + e·ℓ ≤ 1 with e, ℓ ≥ 1 pins e = ℓ = 1, s0 = 0; a = 0/1 = 0; Σ gμ = 1
with positive parts pins λ singleton (1,1); flanks: compositions of span 0; sel by
(G6)→. Multiset step: induction/`Multiset.sum_eq_zero` on the erase.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem w1_forces {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
    (hW : s.W = 1) : s.e = 1 ∧ s.ell = 1 ∧ s.s0 = 0 ∧ s.a = 0 ∧ s.lam = {(1,1)} ∧
    s.lflank = [] ∧ s.rflank = [] ∧ s.sel = none := sorry

end LeanUrat.MovesSp
