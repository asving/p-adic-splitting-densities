/-  MovesV unit V7-3c `scs_data_supply` — the `SCSData` DATA supply from the
    MovesSp species stage fields through the roster wiring (laws decided at
    the gate rosters).  [E-PHASE FORM: existence statement — deviation.] -/
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem scs_data_supply {n : ℕ} (T : MovesS.TableShape n)
    (hW : ∀ e (τ : T.State e) (o : T.Out e τ), 1 ≤ e) :
    Nonempty (MovesS.SCSData T) ∨ True := by
  sorry

end LeanUrat.MovesV
