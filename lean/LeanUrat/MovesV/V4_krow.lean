/-  MovesV unit V4-4 `kernel_row_hfree` — K_e's entrance-height-freeness BY
    TYPE + the no-division fence: the entry def is the displayed dite sum
    (definitional; consumes no hent, divides by no source mass). -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem kernel_row_hfree {n : ℕ} {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (RB : MovesS.RatBurdens T M) (e : ℕ)
    (hK : MovesS.KmatHyp T e) (τ β : T.State e) :
    MovesS.Kmat T RB e hK τ β
      = ∑ o : T.Out e τ,
          if hk : MovesS.routeOf (T.odata e τ o) = .kcol then
            (if MovesS.kTarget T e τ o hk (hK τ o hk) = β
             then RB.TG e τ o else 0)
          else 0 :=
  rfl

end LeanUrat.MovesV
