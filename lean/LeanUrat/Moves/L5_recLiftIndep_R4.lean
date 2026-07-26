import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

/-- **D.10 lift independence at its honest scope.** Two admissible recentering
lifts `t1`, `t2` of the SAME center `cc` produce the SAME primed residual on
every polynomial: `σ1.ratRes f = σ2.ratRes f` in `RatFunc F`. Both sides equal
`σ.ratResShift cc f` by the two `RecenterSubstCore` substitution laws — the
graded (read-height) content depends on `t` only through `(v(t), dig(t))`, so
the lift drops out. -/
theorem L5_recLiftIndep {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ1 σ2 : Stage p F) (cc : ↥σ.K) (t1 t2 : Polynomial ℤ_[p]) (hrec1 : IsRecenteringCore σ σ1 cc t1) (hsub1 : RecenterSubstCore σ σ1 cc) (hrec2 : IsRecenteringCore σ σ2 cc t2) (hsub2 : RecenterSubstCore σ σ2 cc) : ∀ f : Polynomial ℤ_[p], σ1.ratRes f = σ2.ratRes f := by
  intro f
  rw [hsub1 f, hsub2 f]

end LeanUrat.Moves
