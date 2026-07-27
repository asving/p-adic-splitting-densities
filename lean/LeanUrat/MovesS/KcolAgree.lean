/-
Unit U-3 `kcol_agree` (easy) — a continuing member of full block size forces m = 1.
sketch: contrapose with U-2.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.Ktri

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem kcol_agree {T : TableShape n} (hdc : DegCons T) {e : ℕ}
    (he : e ∈ Finset.Icc 1 n) {τ : T.State e} {o : T.Out e τ}
    (hmem : ∃ μ ∈ (T.odata e τ o).mem, μ.continuing ∧ μ.size = e) :
    (T.odata e τ o).m = 1 :=
  sorry

end LeanUrat.MovesS
