/-
Unit C2.EInh_implied  (moves_ref: §C.1(i) forced zeros from the exact-downset (ZC) —
re-keyed to the DEFINED H.htH; the C.1(i) inherited-content implication is J.inh_implied.)
Sketch: (J.zc i).downset_exact ← direction pins j from height ≤ floor at an interior index;
interior_zero forces solve j = 0; IsSolution then reads x j = solve j (...) = 0.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C2_EInh_implied {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) (hi : i < H.nodes.length) (j : Fin m) (hint : (J.coordOf j).2 < (H.nodes[i]'hi).μ * (H.nodes[i]'hi).childWidth) (hbelow : ((H.htH (i+1) (J.coordOf j) : ℚ) : WithBot ℚ) ≤ H.floorH (i+1) (J.coordOf j).2) : ∀ x : Fin m → ZMod p, (J.Sigma (i+1)).IsSolution x → x j = 0 := by
  intro x hx
  -- The (ZC-a) exact-downset (← direction): height ≤ floor at an interior base index pins j.
  have hpinned : (J.Sigma (i+1)).pinned j = true :=
    ((J.zc i hi).downset_exact j hint).mpr hbelow
  -- (ZC-a) literal zeros: an interior pin solves to the constant 0.
  rw [hx j hpinned]
  exact (J.zc i hi).interior_zero j hint hpinned _

end LeanUrat.MovesC
