/-  MovesV unit V2-1 `skeleton_menu` — ROSTER (2): (a) letter-menu projection;
    (b) Skeleton-3 finiteness via the PROVED SP2/SP6 catalogue. -/
import LeanUrat.MovesV.Defs
import LeanUrat.MovesSp.SP2_finThm

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem letter_menu_out {n : ℕ} {s : Skeleton n} (B : BlockData n s)
    (m : B.Letter) : B.letterSp m ∈ MovesSp.Out n s.sp :=
  B.letter_menu m

theorem skeleton3_finite : Finite (Skeleton 3) := by
  have h : (MovesSp.SnRaw 3).Finite := (MovesSp.SP_FIN 3 (by norm_num)).1
  haveI : Finite ↥(MovesSp.SnRaw 3) := h.to_subtype
  refine Finite.of_injective
    (fun s : Skeleton 3 => (⟨s.sp, s.mem⟩ : ↥(MovesSp.SnRaw 3))) ?_
  rintro ⟨sp1, m1⟩ ⟨sp2, m2⟩ h
  simp only [Subtype.mk.injEq] at h
  subst h
  rfl

end LeanUrat.MovesV
