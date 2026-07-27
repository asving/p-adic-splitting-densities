/-
Unit U22.readsOf_SAE  (HC-2 campaign, E-phase — blueprint §5 Layer D; escalation risk)
moves_ref: §C rev 12 (SAE) display (MovesC `TransitionAdmissible` conjuncts 3–4).
F-EMPTY CITE (mandatory per blueprint): (SAE) is the clause whose ABSENCE the certified
F-EMPTY refutation exposed (nominal fresh volume 2⁻⁶, actual census count 0 — MovesC
round-4 header); a run predicate without it would admit classifier-impossible histories.
deps: D4, the parent's (ZC)-zeroed strips (the stratum's interior zeros raise actual
valuations strictly above the old line), K1 slot reading.  difficulty: HARD.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (SAE) for runs: the span-entry inequalities — `new(j) > old(j)` STRICT at every span
slot below the window vertex, equality at the adjacent vertex (conjuncts 3–4 of
`TransitionAdmissible`, extracted). -/
theorem readsOf_SAE {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length) :
    (∀ j : ℕ, (H.nodes[i+1]'hi1).s0 ≤ j →
      j ≤ (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide →
      j < (H.nodes[i]'(by omega)).μ →
      (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
        < (H.nodes[i+1]'hi1).line.at (j * (H.nodes[i]'(by omega)).childWidth)) ∧
    ((H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide = (H.nodes[i]'(by omega)).μ →
      (H.nodes[i+1]'hi1).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)
        = (H.nodes[i]'(by omega)).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) := by
  sorry

end LeanUrat.MovesJ
