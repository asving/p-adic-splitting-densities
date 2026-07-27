/-
Unit U17c.presentNorm_total  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD `PresentNorm` clause (i) — TOTALITY.
deps: U17a + U17b + membership bookkeeping (H' ∈ PrefSet → its class is a PrefIdx
member); the assembled `presentNorm_polOM` additionally consumes U18.
difficulty: medium.  hypothesis_fields: inherits U17a's stage supplier (`StageTransHyp`).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The TOTALITY clause of `PresentNorm n (polOM p F) P`: every policy-free realizable
prefix has a normalized class-mate up to Galois. -/
theorem presentNorm_total {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F) :
    ∀ H : History p F, H ∈ PrefSetAny n P →
      ∃ i : PrefIdx n (polOM p F) P,
        EtaGalEq (etaData (P : ShapePrefix) H) i.1 := by
  sorry

/-- ASSEMBLED (U17c + U18): the full typed dictionary pin `PresentNorm` at `polOM` —
U15/U16's `hnorm` discharger. -/
theorem presentNorm_polOM {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F) :
    PresentNorm n (polOM p F) P := by
  sorry

end LeanUrat.MovesJ
