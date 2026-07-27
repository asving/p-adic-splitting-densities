/-
Unit U26.class_fiber_welldef  (HC-2 campaign, E-phase — blueprint §5 Layer D)
moves_ref: MovesD §3.4 `ClassFiberWelldef` (one η-class, one classifier locus, over ALL
representatives and ALL jets).
deps: U18, C6.thmC_a (locus-equality via Theorem C(a): both loci = the same transported
T(H,⊤) system).  difficulty: hard.  PROOF-FIRST; DEFERRABLE (D15 carries it as `hwd`;
deferral is a recorded non-discharge, not a failure).
fallback: `OmUniqHyp` (§3; P-3 STRUCK — rev 2).  hypothesis_fields: possibly `OmUniqHyp`
(stated clean here; if the proof fails, consumers re-key to carry it).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- One η-class, one classifier locus (MovesD §3.4's Prop, at the canonical policy). -/
theorem class_fiber_welldef {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n N m : ℕ} {P : Shape n} :
    ClassFiberWelldef p F n N m (polOM p F) P := by
  sorry

end LeanUrat.MovesJ
