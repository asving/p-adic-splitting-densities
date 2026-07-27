/-
Unit U-29d-iv `n2_rexact` (easy) — βfull = βmeas at pools, by construction; the
(ns-null) tag holds at the instance (the chain's `hns`).
-/
import LeanUrat.MovesS.N2Beta

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_rexact :
    n2B.nsNull ∧
    (∀ e (he : e ∈ Finset.Icc 1 2) (h_ent : ℕ) (τ : n2T.State e)
      (σ' : Multiset n2T.VType) (q₀ : ℚ), q₀ ∈ n2M.Pools →
      n2B.βfull e he h_ent τ σ' q₀ = n2B.βmeas e he h_ent τ σ' q₀) :=
  sorry

end LeanUrat.MovesS
