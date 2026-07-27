/-
Unit U-4 `scs_flank` (medium) — hypotheses now SUFFICIENT (R2-1, R2-2).
moves_ref: "m = 1 forces NO flank side (the read side spans the window: e·ℓ = W)
and a SINGLETON residual shape λ = {(g, μ)}".  sketch: m = 1 ⟹ member positions =
Fin 1 ⟹ selIdx is the only position; memberOf avoids it (memberOf_ne_sel) yet is
injective into it ⟹ its domain is EMPTY ⟹ flankCount = 0 AND no non-selected
residual factor (sel_mem makes resFactors the singleton); flank_zero gives
flankWidth = 0; window_comp gives W = e·ℓ; res_sum on the singleton gives g·μ = ℓ.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem scs_flank {T : TableShape n} (S : SCSData T) {e : ℕ}
    {τ : T.State e} {o : T.Out e τ} (hm : (T.odata e τ o).m = 1) :
    S.flankCount e τ o = 0 ∧
    S.resFactors e τ o = {(S.g e τ o, S.μsel e τ o)} ∧
    S.W e τ o = e * S.ℓ e τ o ∧
    S.g e τ o * S.μsel e τ o = S.ℓ e τ o :=
  sorry

end LeanUrat.MovesS
