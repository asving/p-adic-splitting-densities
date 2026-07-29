/-  MovesV unit V0-3 `semilin_sum_exact` — the finitely many component sums ADD
    EXACTLY to the H(γ)-sum (no overlap terms — the SemilinPart disj TYPE field). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem semilin_sum_exact {D : ℕ} (S : SemilinPart D) (f : Hpt D → ℝ)
    (hf : ∀ h, 0 ≤ f h) (v : Fin S.comps.length → ℝ)
    (hv : ∀ j, HasSum (fun h : {h // (S.comps.get j).Mem h} => f h.1) (v j)) :
    HasSum (fun h : {h // S.Mem h} => f h.1) (∑ j, v j) := by
  sorry

end LeanUrat.MovesV
