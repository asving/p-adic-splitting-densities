/-  MovesV unit V2-8 `anchor_twist_fence` (RESTATED C10) — ANCHOR ALIGNMENT,
    STRUCTURAL: the partition map factors through the twist BY `part_eq`. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem anchor_twisted {Carrier : ℚ → Type} (G : GenSpec Carrier) (a_eff : ℤ)
    (ha : G.kind = .anchor a_eff) :
    ∀ q₀ x, G.part q₀ x = G.base q₀ (G.twistOf q₀ a_eff x) := by
  intro q₀ x
  have h := G.part_eq q₀ x
  rw [ha] at h
  simpa [GenKind.twistExp] using h

theorem anchor_zero {Carrier : ℚ → Type} (G : GenSpec Carrier)
    (h0 : G.kind = .anchor 0) :
    ∀ q₀, G.part q₀ = G.base q₀ := by
  intro q₀
  funext x
  have h := G.part_eq q₀ x
  rw [h0] at h
  simpa [GenKind.twistExp, G.twist0] using h

end LeanUrat.MovesV
