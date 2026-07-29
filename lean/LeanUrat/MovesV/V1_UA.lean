/-  MovesV unit V1-6 `UA_fixed_history` (RE-SIGNATURED REV 5, M-3) — (U-A) AS
    THE NOTE PROVES IT: GIVEN only the typed §C-supply pack. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem UA {n} {S : StepSys n} (P : C15Pack n S) {α β} (m : S.Move α β) {q₀}
    (hq : q₀ ∈ S.Pools) (x : S.Hist q₀ α) (hzc : S.zc x) (h : Hpt (S.dim m))
    (a a' : S.Assign m x h) : S.massOf m x h a = S.massOf m x h a' := by
  rw [P.mass_factors m x h a hq hzc, P.mass_factors m x h a' hq hzc]

theorem UAT {n} {S : StepSys n} (P : C15Pack n S) {α v} (m : S.MoveT α v) {q₀}
    (hq : q₀ ∈ S.Pools) (x : S.Hist q₀ α) (hzc : S.zc x) (h : Hpt (S.dimT m))
    (a a' : S.AssignT m x h) : S.massOfT m x h a = S.massOfT m x h a' := by
  rw [P.mass_factorsT m x h a hq hzc, P.mass_factorsT m x h a' hq hzc]

end LeanUrat.MovesV
