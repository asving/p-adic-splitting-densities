/-
Unit U-6 `scs` (medium) — kcol ⟹ all member sizes = e; PRODUCES the `hK` argument
of every Kmat consumer.  moves_ref: "(SCS) a (c = 1, m = 1) outcome's single child
inherits the block size: e₁ = e".  sketch: hk + U-1 ⟹ m = 1; the only member is
selIdx, continuing (sel_continuing); cluster_child + U-5 + cluster_parent:
size = W′D′ = WD = e.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.Dispatch
import LeanUrat.MovesS.ScsStage

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem scs {T : TableShape n} (S : SCSData T) (hdc : DegCons T) {e : ℕ}
    (he : e ∈ Finset.Icc 1 n) {τ : T.State e} {o : T.Out e τ}
    (hk : routeOf (T.odata e τ o) = .kcol) :
    ∀ μ ∈ (T.odata e τ o).mem, μ.size = e :=
  sorry

end LeanUrat.MovesS
