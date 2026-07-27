/-
Unit XE.1f — kernel Prop (X2-BRIDGE)  [E-phase: def-witness unit]
display: both clauses — Undec(N) covered by disc-zero ∪ ns-fibers ∪ InfTree ∪ the
witness-branch piece, and the complement-in-Undec is null; rev-4 witness = IsLeafB ∧
NsFreeB in BOTH clauses (`X2BridgeP`, Defs §D).
owner/status: owned by PROGRESS; consumed by name (XE.2, XE.3).
Non-vacuity by construction (Ruling 1); single ledger-tracked inhabitation obligation.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) : Prop := X2BridgeP n X

end LeanUrat.MovesX
