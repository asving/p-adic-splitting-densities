/-  MovesV unit V4-3 `act_agreement_stmt` (PARAMETRIC REV 6, Codex5-30) —
    (ii-c) ACTIVE-VALUE, the RECORDED Prop (never proved here): the all-active
    face.  [E-PHASE FORM: the per-pool package existence shape at the
    parameters; the AVAgree clause binds at V7-2a's AVRec_Stmt against the
    ledger's OWN solve objects — MANIFEST deviations.] -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

def ActiveValueAgree {n : ℕ} (T : MovesS.TableShape n)
    (M : MovesS.MeasuredSide T) (RB : MovesS.RatBurdens T M)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e) : Prop :=
  ∀ q₀ ∈ MovesS.allActivePools M, ∀ e (he : e ∈ Finset.Icc 1 n),
    Nonempty (MovesS.PoolHyp T M RB e (hK e he) q₀)

end LeanUrat.MovesV
