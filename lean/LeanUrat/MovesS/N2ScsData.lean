/-
Unit `n2_scs_data` (easy; S5 construction batch) — DegCons/SCSData DATA (the
corrected R35 windows: at o_K, ℓ = g = μ = 1, W = 2, D = 1); the LAWS display is
U-29b3 (`N2DegScs.lean`).  Also carries `n2hdc`/`n2hK` — the DegCons term and the
U-6-produced Kmat hypothesis every gate consumer takes.
-/
import LeanUrat.MovesS.N2Shape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

noncomputable def n2SCS : SCSData n2T := sorry

theorem n2hdc : DegCons n2T := sorry

/-- U-6's hK at the instance (kcol members have full block size). -/
theorem n2hK : ∀ e, e ∈ Finset.Icc 1 2 → KmatHyp n2T e := sorry

end LeanUrat.MovesS
