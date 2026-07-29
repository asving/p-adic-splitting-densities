/-  MovesV unit V3-2 `hent_proj` — h_ent is a PROJECTION of ε (determined by
    P̂ alone); heights are RETAINED, not quotiented. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem hent_proj {n : ℕ} (ε ε' : EntShapeV n) (h : ε.Phat = ε'.Phat) :
    ε.hent = ε'.hent := by
  unfold EntShapeV.hent
  rw [h]

/-- non-degeneracy: distinct retained height data ⟹ distinct hent (rfl-level:
heights are retained, not quotiented). -/
theorem hent_ne {n : ℕ} (ε ε' : EntShapeV n)
    (hne : (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))
        ≠ (ε'.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, R.ustar))) :
    ε.hent ≠ ε'.hent :=
  hne

end LeanUrat.MovesV
