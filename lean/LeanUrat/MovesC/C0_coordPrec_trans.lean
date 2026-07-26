/-
Unit C0.coordPrec_trans — moves_ref: §C.0 the global order ≺
Transitivity of the global order (level ascending, index descending within a level).
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

theorem C0_coordPrec_trans (a b c : Coord) (h1 : CoordPrec a b) (h2 : CoordPrec b c) : CoordPrec a c := by
  simp only [CoordPrec] at *
  omega

end LeanUrat.MovesC
