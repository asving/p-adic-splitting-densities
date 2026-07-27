/-
Unit `n2_rsh` (medium; S5 chain batch) — rsh_interp at the explicit values:
eval β_{(1,2)} = (q₀+1)/(q₀²+q₀+1) etc., with the DEVICE WshP from
n2_wshp_device (the R44 scope contradiction is GONE: R46).  Also carries the
gate's discharge of `wsh17_pin` (:= the device W17ii height-sum instance —
NONTRIVIALLY discharged by n2_sh_laws' shweight_card at the singleton height;
at wave 4 the field is re-keyed to W17ii's real statement, R57).
-/
import LeanUrat.MovesS.N2WshpDevice
import LeanUrat.MovesS.N2ShEvents
import LeanUrat.MovesS.N2ShLaws

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_rsh (hdet : DetHyp n2T n2RB n2hK) :
    n2Chain.wsh17_pin ∧
    (∀ σ ∈ n2Chain.Sigmas, ∀ p ∈ n2Chain.PrimePools,
      ∃ hok : Rsh n2T n2M n2RB n2hdc n2hK hdet n2F n2Chain.WshP σ ∈ OKat p,
        ((evalAt p ⟨Rsh n2T n2M n2RB n2hdc n2hK hdet n2F n2Chain.WshP σ, hok⟩ : ℚ) : ℝ)
          = n2Chain.Rval σ p) ∧
    (∀ p ∈ n2Chain.PrimePools,
      n2Chain.Rval {n2v12} p = (((p + 1) / (p ^ 2 + p + 1) : ℚ) : ℝ)) :=
  sorry

end LeanUrat.MovesS
