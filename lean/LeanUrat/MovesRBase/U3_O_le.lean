/-
Unit U3  (MovesR base layer)
moves_ref: "nested base changes then compose LITERALLY as subrings … no per-pair
embedding choices".
deps: Defs (U1), U2, MapComp. difficulty: medium.
sketch: `Subfield.subtype (Fsub p d) = (Subfield.subtype (Fsub p m)).comp
(Subfield.inclusion (Fsub_le p h))`, then `map_comp` rewrites each element of
`(WittVector.map (Fsub p d).subtype).range` as a `WittVector.map (Fsub p m).subtype`
image.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.MovesRBase.U2_Fsub_le
import LeanUrat.MovesRBase.MapComp

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U3: `O_d ≤ O_m` for `d ∣ m` — the substantive content of the composition
convention ("compose LITERALLY as subrings"). -/
theorem O_le {d m : ℕ+} (h : d ∣ m) : O p d ≤ O p m := by
  rintro x hx
  rw [O, RingHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [O, RingHom.mem_range]
  refine ⟨WittVector.map (Subfield.inclusion (Fsub_le p h)) y, ?_⟩
  rw [map_comp]
  have hfe : (Subfield.subtype (Fsub p m)).comp (Subfield.inclusion (Fsub_le p h))
      = Subfield.subtype (Fsub p d) := rfl
  rw [hfe]

end MovesRBase
