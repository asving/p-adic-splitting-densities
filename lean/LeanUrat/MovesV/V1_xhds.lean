/-  MovesV unit V1-4 `xhds_eval_nonneg` — each `Gc γ j` evaluates ≥ 0 at pools. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

theorem gProd_nonneg {n} {S : StepSys n} (W : XHDw n S) :
    ∀ {α} (γ : Template n S α) (h : Hpt γ.D) (q₀ : ℚ), 0 ≤ (q₀ : ℝ) →
    0 ≤ gProd W γ h q₀
  | _, .last m, h, q₀, hq => zpow_nonneg hq _
  | _, .lastT m, h, q₀, hq => zpow_nonneg hq _
  | _, .cons m γ, h, q₀, hq =>
      mul_nonneg (zpow_nonneg hq _) (gProd_nonneg W γ (Hpt.drop h) q₀ hq)

theorem xhds_eval_nonneg {n} {S : StepSys n} {TE : TmplEvents n S}
    {D : XHDd n S TE} (X : XHDw n S) (Xs : XHDs n S X D)
    {α} (γ : Template n S α) (j : Fin (D.dom γ).comps.length)
    (q₀ : ℚ) (hq : q₀ ∈ S.Pools) :
    (0 : ℝ) ≤ ((evalAt q₀ ⟨Xs.Gc γ j, Xs.Gc_ok γ j q₀ hq⟩ : ℚ) : ℝ) := by
  have h1 : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast S.pools_gt_one q₀ hq
  refine HasSum.nonneg ?_ (Xs.Gc_hasSum γ j q₀ hq)
  exact fun h => gProd_nonneg X γ h.1 q₀ (by linarith)

end LeanUrat.MovesV
