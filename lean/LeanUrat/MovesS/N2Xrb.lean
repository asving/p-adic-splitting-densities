/-
Unit U-29d-iii `n2_xrb` (easy) — h_ent-independence at pools, by construction.
-/
import LeanUrat.MovesS.N2Beta

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_xrb : ∀ e (he : e ∈ Finset.Icc 1 2) (h h' : ℕ) (τ : n2T.State e)
    (σ' : Multiset n2T.VType) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2B.βmeas e he h τ σ' q₀ = n2B.βmeas e he h' τ σ' q₀ :=
  n2B.xrb

end LeanUrat.MovesS
