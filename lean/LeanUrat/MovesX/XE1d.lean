/-
Unit XE.1d — kernel Prop (X2-AFF)  [E-phase: def-witness unit]
display: "thr(b) ≤ 1 + c₀·Σ h_r on the fourth-piece family" (`X2AffP`, Defs §D).
owner/status: owned by PROGRESS; consumed by name (XD.4, XE.2, XE.3).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (K : XConsts n) : Prop := X2AffP n X K

end LeanUrat.MovesX
