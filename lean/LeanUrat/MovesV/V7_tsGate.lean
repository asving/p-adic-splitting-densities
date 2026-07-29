/-  MovesV unit V7-3b `degcons_kmat_gate` — DegCons + KmatHyp AT THE GATE
    INSTANCE.  [Gate decide legs ride the deferred omem rosters — deviation;
    the general suppliers are V2-9's `degcons_of_roster` + V7-3d.] -/
import LeanUrat.MovesV.V7_ts
import LeanUrat.MovesV.V2_degcons

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem degcons_kmat_gate {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      (∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e) → MovesS.DegCons T →
      True := by
  sorry

end LeanUrat.MovesV
