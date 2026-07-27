/-
Unit XE.1c — kernel Prop WEIGHT-CHARGE (FULL burden)  [E-phase: def-witness unit]
display: "#T1-recenterings + #T4 ≤ s(n)·v_p(disc f)" (`WeightChargeFullP`, Defs §D).
owner/status: math-side OPEN kernel (X.1b); consumed by name (XC.3, X3aRouteP, XE.2/3).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (K : XConsts n) : Prop := WeightChargeFullP n X K

end LeanUrat.MovesX
