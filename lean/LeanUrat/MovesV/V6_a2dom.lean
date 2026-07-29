/-  MovesV unit V6-2a `a2_domain_chart` (RE-KEYED C3) — the A2 height-domain
    normal form THROUGH THE CHART. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem A2chart_image :
    A2chart '' {h | A2dom.Mem h}
      = {h : Hpt 2 | 1 ≤ h 1 ∧ 3 * h 1 < h 0 ∧ Odd (h 0 - h 1)} := by
  sorry

theorem A2chart_inj : Set.InjOn A2chart {h | A2dom.Mem h} := by
  sorry

/-- one component ⟹ the disjointness convention holds VACUOUSLY. -/
theorem a2_one_component :
    ([A2dom] : List (LinSet 2)).Pairwise
      (fun L L' => ∀ h, ¬(L.Mem h ∧ L'.Mem h)) :=
  List.pairwise_singleton _ _

end LeanUrat.MovesV
