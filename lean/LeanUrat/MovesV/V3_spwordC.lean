/-  MovesV unit V3-3c `entshape_bridge` — the MovesSp.EntranceShape behind
    (ε̊, h) (the §1 consumption tie A-3). -/
import LeanUrat.MovesV.V3_spwordB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem entshape_bridge {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) :
    Nonempty (MovesSp.EntranceShape n εT.gsel εT.musel) :=
  ⟨{ word    := εT.word
     hne     := εT.hne
     hMem    := εT.hMem
     hChain  := εT.hWalk.imp (fun _ _ hab => hab.1)
     hEntry  := εT.hEntry
     heights := fun i => (εT.pairSlots h).getD i.val (0, 0)
     depths  := fun j => (εT.depthSlots h).getD j.val 0 }⟩

end LeanUrat.MovesV
