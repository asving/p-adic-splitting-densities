/-
Unit C2.floorH_root  (moves_ref: §C.1 E_fresh(ν₀) := E(ν₀) (empty floor at the root read))
take 0 = [], foldr max ⊥ [] = ⊥. Definitional.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C2_floorH_root (H : History p F) (b : ℕ) : H.floorH 0 b = ⊥ := rfl

end LeanUrat.MovesC
