/-
Unit Sp.fullForcing — moves_ref: "(i) At each fixed (tag, D, w, W) there is AT
MOST ONE full letter: μ = W with (B4)'s g·μ ≤ ℓ and (B3)'s a + ℓ ≤ W forces
g = 1, ℓ = W, a = 0, λ = {(1, W)} …; then (B3)'s s₀′ + w′ ≤ W with w′ = e·ℓ = e·W
forces e = 1 and s₀′ = 0 …, by (G1) both flanks empty, by (G3) slots {0, …, W}".
sketch: sel = (1, W): (B4) W ≤ ℓ; (B3) a + ℓ ≤ W ⇒ ℓ = W, a = 0; λ: member (1, W)
with Σ = W ⇒ erase has sum 0 & positive parts ⇒ singleton (`Multiset.cons_erase`
+ sum_eq_zero); (B3) s0 + e·W ≤ W, e ≥ 1, W ≥ 1 ⇒ e = 1, s0 = 0; (G1) flanks span
0; (G3). difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem full_forces {n} {s : Species} (hc : Coherent s)
    (hb : Budget n s) (hf : IsFull s) : s.e = 1 ∧ s.ell = s.W ∧ s.a = 0 ∧ s.s0 = 0 ∧
    s.lam = {(1, s.W)} ∧ s.lflank = [] ∧ s.rflank = [] ∧
    s.slots = Finset.Icc 0 s.W := sorry

end LeanUrat.MovesSp
