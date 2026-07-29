/-  MovesV unit V1-7 `ua_split_fence` — THE HONEST-SPLIT WITNESS (A-7 form):
    (XHD-u) is NOT a consequence of the pack (inverse-defect discipline). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ua_fence : ∃ S : StepSys 1, ∃ _P : C15Pack 1 S,
    ¬ (∀ {α β} (m : S.Move α β) {q₀} (_ : q₀ ∈ S.Pools)
        (x x' : S.Hist q₀ α) (h : Hpt (S.dim m)) (a : S.Assign m x h)
        (a' : S.Assign m x' h), S.massOf m x h a = S.massOf m x' h a') := by
  sorry

end LeanUrat.MovesV
