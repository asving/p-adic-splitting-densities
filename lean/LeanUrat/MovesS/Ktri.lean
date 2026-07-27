/-
Unit U-2 `ktri` (easy) — (K-TRI): at m ≥ 2 every member size < e.
moves_ref: "at m ≥ 2 EVERY e_j < e".  sketch: μ.size + (m−1) ≤ Σ sizes ≤ e via
size_pos on the other members; omega.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem ktri {T : TableShape n} (hdc : DegCons T) {e : ℕ}
    (he : e ∈ Finset.Icc 1 n) {τ : T.State e} {o : T.Out e τ}
    (hm : 2 ≤ (T.odata e τ o).m) :
    ∀ μ ∈ (T.odata e τ o).mem, μ.size < e :=
  sorry

end LeanUrat.MovesS
