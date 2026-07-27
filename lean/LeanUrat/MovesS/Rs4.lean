/-
Unit U-28 `rs4_rational_step` (medium) — RS.4 with the full inherited set (R2-19).
moves_ref: "(RS.4) Σ_σ R_σ = 1 identically in q … RS.4 inherits EVERY condition
of the block solve".  THE DISPLAYED INHERITED SET, all explicit in RS4Chain:
C.L (nine CL-5 inputs) · C.B (RS.1's set: xrb/CL-9, recursion_meas/CL-10+CL-8
provenance) · C.hns ((ns-null)) · C.pools_e0 + C.legs_reg (ESCAPE(E0)/CL-1, full
per-pool quantifier) · C.WshP/wsh_ok (denominator regularity; CL-17(ii)'s
PRODUCTION burden is the seam pin W17ii/S-8 — INHERITED AND OPEN via the typed
premise `h17 : C.wsh17_pin` (R57): the acceptance record MAY NOT be marked
unconditional while W17ii is open) · RB in (iv)-POLY form (CL-6) + XHD-s geoms +
INIT-RAT ιP + (J-RAT) jP · C.x3_total (X.3/CL-4, pinned W-4) · C.rs1_equates
(pinned W-1e) · C.rsh_interp (pinned W-1's shadow).
sketch: eval(Σ Rsh − 1) at p ∈ PrimePools = Σ Rval − decidedTotal = 0
(rsh_interp, rs1_equates, x3_total); prime infinitude + U-27.
-/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem rs4_rational_step {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) (h17 : C.wsh17_pin) (hdet : DetHyp T RB hK) :
    (∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) = 1 :=
  sorry

end LeanUrat.MovesS
