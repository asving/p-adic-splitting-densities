/-
Unit U-16a3 `consumedDeltas_def` (medium) — the closure spec lemma for the
multiplicative δ-closure (R17, DELTA-ABS; the def `consumedDeltas` lives in
Defs.lean, filled at E-phase).  moves_ref: "δ ranging over 1 AND every base-change
index a β_{e_j,τ_j}(q^{δ_j}) leg of b_e^split or RS.1-SH consumes ([2r] BASE-INDEX
CONVENTION + (e2), δ ABSOLUTE)".  For any nesting chain of split/shape legs
(length ≤ n by U-2), the chain's PRODUCT — the semantic index rel. the base prime —
lies in `consumedDeltas`; hence `RegP`/`legs_reg` carry E0 over every EFFECTIVE
pool p^(δ₁·…·δ_k), and `pools_closed` keeps each in `Pools`.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowSubstMul

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem nested_delta_mem (T : TableShape n) (F : ShapeFam T) (l : List ℕ+)
    (hlen : l.length ≤ n) (hfac : ∀ δ ∈ l, δ ∈ deltaFactors T F) :
    l.prod ∈ consumedDeltas T F :=
  sorry

end LeanUrat.MovesS
