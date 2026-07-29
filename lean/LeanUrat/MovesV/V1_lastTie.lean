/-  MovesV unit V1-3c `counting_tie_last` (REV 9, M-2 split) — tgam_last(+T) +
    marks_chains (the DERIVED bound; the rev-7 FIELD's name survives here). -/
import LeanUrat.MovesV.V1_chains

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem tgam_last {n} {S : StepSys n} (TE : TmplEvents n S) {α β}
    (m : S.Move α β) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dim m))
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE (.last m) x h = S.cntraw m x h := by
  sorry

theorem tgam_lastT {n} {S : StepSys n} (TE : TmplEvents n S) {α v}
    (m : S.MoveT α v) {q₀} (x : S.Hist q₀ α) (h : Hpt (S.dimT m))
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE (.lastT m) x h = S.cntrawT m x h := by
  sorry

theorem marks_chains {n} {S : StepSys n} (TE : TmplEvents n S) {α}
    (γ : Template n S α) {q₀} (x : S.Hist q₀ α) (h : Hpt γ.D)
    (hq : q₀ ∈ S.Pools) (hzc : S.zc x) :
    Tgam TE γ x h ≤ chainCount S γ x h := by
  sorry

end LeanUrat.MovesV
