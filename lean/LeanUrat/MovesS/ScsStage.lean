/-
Unit U-5 `scs_stage` (easy) — W′D′ = WD via stage_D/stage_W + U-4.
moves_ref: "W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D".
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.ScsFlank

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem scs_stage {T : TableShape n} (S : SCSData T) {e : ℕ}
    {τ : T.State e} {o : T.Out e τ} (hm : (T.odata e τ o).m = 1) :
    S.W' e τ o * S.D' e τ o = S.W e τ o * S.D e τ o :=
  sorry

end LeanUrat.MovesS
