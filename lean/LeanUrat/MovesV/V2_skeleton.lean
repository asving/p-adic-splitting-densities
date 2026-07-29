/-  MovesV unit V2-1 `skeleton_menu` — ROSTER (2): (a) letter-menu projection;
    (b) Skeleton-3 finiteness via the PROVED SP2/SP6 catalogue. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem letter_menu_out {n : ℕ} {s : Skeleton n} (B : BlockData n s)
    (m : B.Letter) : B.letterSp m ∈ MovesSp.Out n s.sp :=
  B.letter_menu m

theorem skeleton3_finite : Finite (Skeleton 3) := by
  sorry

end LeanUrat.MovesV
