/-
Unit XE.1h — kernel Prop (X2-PROGRESS)  [E-phase: def-witness unit]
display: undetected-at-N fourth-piece branches are deep or tall at linear rates
(`X2ProgressP`, Defs §D).
owner/status: owned by PROGRESS; consumed by name (XE.2).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (K : XConsts n) : Prop := X2ProgressP n X K

end LeanUrat.MovesX
