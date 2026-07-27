/-
Unit XE.1g — kernel Prop (X2-TAILS)  [E-phase: def-witness unit]
display: "frac(TallEvent h*) ≤ C_T·p^{−c_T·h*}" — THE defined event (finding 4)
(`X2TailsP`, Defs §D).
owner/status: [2b]-owed, discharged at [2b]'s acceptance; consumed by name (XE.2, XE.3).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (K : XConsts n) : Prop := X2TailsP n X K

end LeanUrat.MovesX
