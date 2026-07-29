/-  MovesV unit V4-2 `act_triangular` — (ii-b): the evaluated kernel matrix at
    q₀ is block-triangular; stated on MovesS.Kmat at evaluation (matrix zeros
    only — no stochastic reading). -/
import LeanUrat.MovesV.V4_act
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

theorem act_triangular {n : ℕ} {T : MovesS.TableShape n}
    {M : MovesS.MeasuredSide T} (RB : MovesS.RatBurdens T M) {e : ℕ}
    (hK : MovesS.KmatHyp T e) (q₀ : ℚ) (hq : q₀ ∈ M.Pools)
    (τ β : T.State e) (hact : M.activeState q₀ e τ)
    (hin : ¬ M.activeState q₀ e β)
    (hrow : ∀ (o : T.Out e τ) (hk : MovesS.routeOf (T.odata e τ o) = .kcol),
      MovesS.kTarget T e τ o hk (hK τ o hk) = β →
      ∀ hok : RB.TG e τ o ∈ OKat q₀,
        (evalAt q₀ ⟨RB.TG e τ o, hok⟩ : ℚ) = 0)
    (hok : MovesS.Kmat T RB e hK τ β ∈ OKat q₀) :
    (evalAt q₀ ⟨MovesS.Kmat T RB e hK τ β, hok⟩ : ℚ) = 0 := by
  sorry

end LeanUrat.MovesV
