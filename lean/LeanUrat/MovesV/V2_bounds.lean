/-  MovesV unit V2-10 `wloc_wstate_split` (RESTATED C11) — the SPLIT-bound
    fence: gate degree records + the Wstate > Wloc consistency witness. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- (a) the gate data's degree records (root Wloc = 3; s_blk2 Wloc = 2). -/
theorem gate_bounds : TH3.natDegree = 3 ∧ Tsplit.natDegree = 2 ∧
    Tdbl.natDegree = 1 := by
  sorry

/-- (b) an explicit SYNTHETIC family witnessing `Wstate s > Wloc s m`. -/
theorem wstate_gt_wloc_consistent :
    ∃ (C : CtsFamily 1) (s : Skeleton 1) (m : (C.bd s).Letter),
      C.Wloc s m < (C.bd s).Wstate := by
  sorry

end LeanUrat.MovesV
