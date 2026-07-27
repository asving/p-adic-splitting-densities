/-
Unit `n2_d4r0` (easy; S5 ledger batch, LedgerIV item (2)) — event disjointness.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_d4r0 : ∀ e (τ : n2T.State e) (x : n2M.Rep e τ) (q₀ : ℚ) (N : ℕ)
    (c c' : n2M.Cell e τ) (h h' : n2M.Hgt), (c, h) ≠ (c', h') →
    Disjoint (n2M.cellEvt e τ x c h q₀ N) (n2M.cellEvt e τ x c' h' q₀ N) :=
  sorry

end LeanUrat.MovesS
