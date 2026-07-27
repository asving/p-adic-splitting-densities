/-
Unit D0b.thmC_top  (MovesD campaign, E-phase)
moves_ref: "Each NONEMPTY summand is Theorem C(b) with Z = ⊤ on the lift-carrying history
  η: μ(S(η,⊤)) = ∏ᵢ vol(E_fresh(νᵢ))" (§D4-R D4R.1 proof).
deps: C6_thmC_b, D0a.
sketch: `C6_thmC_b J top (topLocus_admissible _)`; `boxMass = p^(n*N)` by `J.hm`;
  `numPinned = 0`.  difficulty: easy.
hypothesis_fields: none (J a binder; existence = `Presented.jet`, HC-2).
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}

/-- At Z = ⊤ the total pin count is exactly the fresh-inventory sum Σ m*(νᵢ). -/
theorem totalPins_top {H : History p F} (J : JetSetup H n N m) :
    totalPins J (topLocus p m)
      = (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) := by
  sorry

/-- Theorem C(b) at Z = ⊤ on the presented history (division-free box identity). -/
theorem thmC_top {H : History p F} (J : JetSetup H n N m) :
    Nat.card (J.SHZ (topLocus p m)) * p ^ totalPins J (topLocus p m) = p ^ (n * N) := by
  sorry

end LeanUrat.MovesD
