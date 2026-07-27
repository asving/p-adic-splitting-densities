/-
Unit `n2_sh_events` (medium; S5 shallow-device batch, DEVICE-ONLY) — the device
carriers shDom (singleton height), shEvtH/visH/shEvt AND `shWeightH` (ownership
restored, R55/Fable#10-GAP-1: the weights the events' cards realize — pinned here
to the WshVal total at the one height) + shevt_grouping.
-/
import LeanUrat.MovesS.N2Sigmas

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

attribute [local instance 0] Classical.decEq

theorem n2_sh_events :
    (∀ Ŝ ∈ n2F.Sh, ∃ h₀, n2Chain.shDom Ŝ = {h₀}) ∧
    (∀ Ŝ (q₀ : ℚ) (N : ℕ), n2Chain.shEvt Ŝ q₀ N
      = (n2Chain.visH Ŝ q₀ N).biUnion (fun h => n2Chain.shEvtH Ŝ h q₀ N)) ∧
    (∀ Ŝ ∈ n2F.Sh, ∀ h : n2M.Hgt, h ∈ n2Chain.shDom Ŝ → ∀ q₀ ∈ n2M.Pools,
      n2Chain.shWeightH Ŝ h q₀ = n2Chain.WshVal Ŝ q₀) :=
  ⟨fun _ _ => ⟨(0 : ℕ), rfl⟩, n2Chain.shevt_grouping, fun _ _ _ _ _ _ => rfl⟩

end LeanUrat.MovesS
