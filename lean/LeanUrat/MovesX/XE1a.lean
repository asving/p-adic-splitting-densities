/-
Unit XE.1a — kernel Prop (X1a-ALIGN)  [E-phase: def-witness unit; no proof obligation]
display: "d_cert(H) ≤ ind(f) on every stratum, off disc = 0" (`X1aAlignP`, Defs §D).
owner/status: math-side OPEN kernel; consumed by name (XC.1, XC.3, XC.4, XE.2, XE.3).
NON-VACUITY BY CONSTRUCTION (Ruling 1): a Prop about the shared `X : XFamily n`; the ONE
inhabitation obligation (the real `XFamily` instance, owner MovesD/MovesT) is
ledger-tracked. The `example` below is the unit's content: the def elaborates against Defs.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false

example {n : ℕ} (X : XFamily n) (st : AlignState) : Prop := X1aAlignP n X st

end LeanUrat.MovesX
