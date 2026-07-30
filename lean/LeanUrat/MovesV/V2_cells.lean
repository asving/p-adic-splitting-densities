/-  MovesV unit V2-2 `cellidx_delete` (DEDUPLICATED REV 5) — ROSTER (2):
    (a) the CellIdx Fintype instance; (b) deleted cells have empty fibers. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

noncomputable instance BlockData.cellIdxFintype {n : ℕ} {s : Skeleton n}
    (B : BlockData n s) : Fintype B.CellIdx := by
  classical
  haveI := B.finG
  haveI := fun g => (B.gen g).finI
  exact Subtype.fintype _

open Classical in
theorem deleted_empty {n : ℕ} {s : Skeleton n} (B : BlockData n s)
    (a : ∀ g : B.Gen, (B.gen g).idx) (hdel : B.sizeP a = 0)
    (q₀ : ℚ) (hpp : IsPP q₀) :
    (letI := B.finCar q₀
     (Finset.univ.filter
       (fun x : B.Carrier q₀ => ∀ g, (B.gen g).part q₀ x = a g)).card) = 0 := by
  have hc := B.size_count a q₀ hpp
  rw [hdel] at hc
  simpa using hc.symm

end LeanUrat.MovesV
