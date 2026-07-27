/-
Unit XE.1e — kernel Prop (X2-CAP)  [E-phase: def-witness unit]
display: "cap(b) ≤ c_cap·(1 + Σ h_r)", quantified INSIDE the ns-free fourth-piece
family (finding 2) (`X2CapP`, Defs §D).
owner/status: owned by PROGRESS; consumed by name (XD.4, XE.2, XE.3).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (K : XConsts n) : Prop := X2CapP n X K

end LeanUrat.MovesX
