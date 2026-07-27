/-
Unit `n2_sh_laws` (medium; S5 shallow-device batch, DEVICE-ONLY) — wshval_bdd,
shDom_ne, sh_realized, shweight_card, AND `wshval_card` (Fable#9-G-1: previously
unowned; the device's singleton height class discharges it via shweight_card +
shevt_grouping).
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_sh_laws :
    (∀ Ŝ ∈ n2F.Sh, ∀ q₀ ∈ n2M.Pools, n2Chain.WshVal Ŝ q₀ ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ Ŝ ∈ n2F.Sh, (n2Chain.shDom Ŝ).Nonempty) ∧
    (∀ Ŝ ∈ n2F.Sh, ∀ q₀ ∈ allActivePools n2M,
      ∃ N₀, ∀ N ≥ N₀, (n2Chain.shEvt Ŝ q₀ N).Nonempty) ∧
    (∀ Ŝ ∈ n2F.Sh, ∀ h : n2M.Hgt, h ∈ n2Chain.shDom Ŝ → ∀ q₀ ∈ n2M.Pools,
      ∃ N₀, ∀ N ≥ N₀, n2Chain.shWeightH Ŝ h q₀ * (Fintype.card (n2M.Box q₀ N) : ℝ)
        = ((n2Chain.shEvtH Ŝ h q₀ N).card : ℝ)) ∧
    (∀ Ŝ ∈ n2F.Sh, ∀ q₀ ∈ n2M.Pools, ∃ N₀, ∀ N ≥ N₀,
      n2Chain.WshVal Ŝ q₀ * (Fintype.card (n2M.Box q₀ N) : ℝ)
        = ((n2Chain.shEvt Ŝ q₀ N).card : ℝ)) :=
  sorry

end LeanUrat.MovesS
