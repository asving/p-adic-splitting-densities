/-
Unit W3.D4R2'_full  (MovesD campaign, E-phase)  [REV 6, Codex#4 f.3: BOTH displayed
bounds, over the subtype, no case analysis needed; REV 8: on `Shape.CD` — the ∅ case is
1 ≤ 1 ∧ 1 ≤ 1, the note's own C_∅ arithmetic through the F3/CD bridge]
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, M(P̂) ≤ n^{|P̂|} p-FREE (L11)" — the display PAIR,
verbatim, unconditional on the note's universe (`Shape n` + hnorm).
deps: D3a, W2.
sketch: ⟨D4R2' hnorm, Mfac_le P⟩.  difficulty: easy.
hypothesis_fields: `hnorm` (Codex#4 f.2).
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D3a_poolBound
import LeanUrat.MovesD.W2_MfacLe

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- D4R.2′, the display pair: C ≤ M·p^W and M ≤ n^{|P̂|}. -/
theorem D4R2'_full (hnorm : PresentNorm n pol P) :
    P.CD pol ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W ∧
      (P : ShapePrefix).Mfac ≤ n ^ (P : ShapePrefix).reads.length :=
  ⟨D4R2' hnorm, Mfac_le P⟩

end LeanUrat.MovesD
