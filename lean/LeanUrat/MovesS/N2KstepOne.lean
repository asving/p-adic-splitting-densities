/-
Unit `n2_kstep_one` (easy; S5 ledger batch, LedgerIV item (6)) — the 1×1 base
tie: kstep 1 = the kcol row mass (q₀⁻³), in the pinned hK-free existential-cast
form (G1).
-/
-- Discharges via the `kstep_one` field of the instance `LedgerIV` (the D-5 pin
-- idiom, exactly as `n2_part1` reads `n2Chain.L.part1` and `n2_hmc` reads
-- `n2Chain.L.hmc`): the only `LedgerIV n2T n2M` is `n2Chain.L`.  N2Sigmas
-- supplies `n2Chain`; it transitively re-exports N2Carriers.
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_kstep_one : ∀ e (τ β : n2T.State e) (q₀ : ℚ), q₀ ∈ n2M.Pools →
    n2M.activeState q₀ e τ →
    n2M.kstep 1 e τ β q₀ =
    ∑ o ∈ {o : n2T.Out e τ | routeOf (n2T.odata e τ o) = .kcol ∧
        ∃ μ ∈ (n2T.odata e τ o).mem, ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
      }.toFinset, n2M.rowVal e τ o q₀ :=
  n2Chain.L.kstep_one

end LeanUrat.MovesS
