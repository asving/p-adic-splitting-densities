/-
Unit U-1 `dispatch_spec` (easy) — the (m, c) route iff-triple.
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION … (c ≥ 1 with m = 1 forces
c = 1)".  sketch: unfold, split_ifs, omega.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem dispatch_spec {V : Type*} {St : ℕ → Type*} (o : Outcome V St)
    (h1 : 1 ≤ o.m) (hc : o.c ≤ o.m) :
    (routeOf o = .termFin ↔ o.c = 0) ∧
    (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧
    (routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m) :=
  sorry

end LeanUrat.MovesS
