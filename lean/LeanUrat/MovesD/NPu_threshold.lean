/-
Unit NPu.threshold  (MovesD campaign, E-phase)  [REV 6, Codex#4 f.4]
moves_ref: L12: "N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅, N(P̂) := 1 if
Pref(P̂) = ∅ … N(P̂) is finite" — NP is the DEFINED formula (§3.3; the max collapses by
shape-constancy; the empty convention falls out of the sup). `hstab` is DERIVED, not
assumed (the rev-5 field deleted).  [REV 7: NP_stab is stated on the INHABITED branch
(NP = NPband); the empty branch never consumes stability.]
deps: Defs, L9s.
sketch: NP_stab — every band coordinate has level ≤ NP − 1 (the filter's sup), so the
level-range extension beyond NP adds nothing; combine with L9s at Nshape via
NP_le_Nshape.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- 1 ≤ N(P̂) (both branches of the piecewise NP). -/
theorem NP_pos : 1 ≤ P.NP pol := by
  sorry

/-- N(P̂) ≤ Nshape(P̂) (sup < Nshape; 1 ≤ Nshape). -/
theorem NP_le_Nshape : P.NP pol ≤ (P : ShapePrefix).Nshape := by
  sorry

/-- A-stability from NP on (INHABITED branch — NP = NPband). -/
theorem NP_stab [Nonempty (PrefIdx n pol P)] :
    ∀ N : ℕ, P.NP pol ≤ N → (P : ShapePrefix).A n N = (P : ShapePrefix).A' n := by
  sorry

end LeanUrat.MovesD
