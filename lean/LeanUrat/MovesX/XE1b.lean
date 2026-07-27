/-
Unit XE.1b — kernel Prop WEIGHT-CHARGE (T4 burden)  [E-phase: def-witness unit]
display: "#T4(H) ≤ s(n)·v_p(disc f)" (`WeightChargeT4P`, Defs §D).
owner/status: math-side OPEN kernel (X.1b); consumed by name (XC.4, X3aRouteP).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (K : XConsts n) : Prop := WeightChargeT4P n X K

end LeanUrat.MovesX
