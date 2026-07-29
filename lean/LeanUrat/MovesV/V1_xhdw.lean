/-  MovesV unit V1-1 `xhdw_range` — the weight monomial's numeric range at pools. -/
import LeanUrat.MovesV.V0_affine

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem xhdw_pos {n} {S : StepSys n} (X : XHDw n S) {α β} (m : S.Move α β)
    (h : Hpt (S.dim m)) {q₀ : ℚ} (hq : q₀ ∈ S.Pools) : 0 < X.g m h q₀ := by
  have h1 : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast S.pools_gt_one q₀ hq
  exact zpow_pos (by linarith) _

theorem xhdw_le_const {n} {S : StepSys n} (X : XHDw n S) {α β} (m : S.Move α β)
    (h : Hpt (S.dim m)) {q₀ : ℚ} (hq : q₀ ∈ S.Pools) :
    X.g m h q₀ ≤ (q₀ : ℝ) ^ (-(((X.E m).const : ℕ) : ℤ)) := by
  have h1 : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast S.pools_gt_one q₀ hq
  have h2 : (-(((X.E m).eval h : ℕ) : ℤ)) ≤ -(((X.E m).const : ℕ) : ℤ) := by
    have := affine_ge_const (X.E m) h
    omega
  exact zpow_le_zpow_right₀ h1.le h2

end LeanUrat.MovesV
