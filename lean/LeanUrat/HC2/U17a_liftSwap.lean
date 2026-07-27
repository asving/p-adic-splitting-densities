/-
Unit U17a.lift_swap  (HC-2 campaign, E-phase — blueprint §5 Layer C; escalation risk: the
one unit consuming stage RECONSTRUCTION)
moves_ref: MovesD §3.2 PresentNorm clause (i) totality ("L1's kernel-(a) totality + the
L6-corollary + conjugation equivariance"); §B2-DEF D.10 "lift independence".
deps: U25 (polOM total on eligible nodes), U1b (read-pair lift discharge),
Moves L5_recLiftIndep_R4 (PROVED — D.10's lift-independence core), `StageTransHyp`
(swapping a lift changes the child key Φ′ = Φ − t′, so DOWNSTREAM stages must be rebuilt —
stage existence enters HERE, ONLY through the named hypothesis; no unit names P-1).
difficulty: HARD.  hypothesis_fields: `StageTransHyp` (§3 — discharge: HC-1's D.7
induction, or the recorded P-1-reduced contingency; consumer-invisible either way).
E-PHASE NOTE: "all recentering lifts = polOM.liftOf" is rendered as the all-nodes
`IsCanon` (lifts are junk data off recenterings; the policy is blind + deterministic) —
matches SideReads(v) and feeds U17c's PrefSet membership.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- LIFT SWAP: every policy-free realizable prefix member has a same-η, polOM-canonical
class-mate (same shape, side digits, ψ-coefficients per read; coherence, realizability
and the box preserved). -/
theorem lift_swap {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F)
    (H : History p F) (hH : H ∈ PrefSetAny n P) :
    ∃ H' : History p F,
      (P : ShapePrefix).MatchesHist H' ∧
      etaData (P : ShapePrefix) H' = etaData (P : ShapePrefix) H ∧
      (polOM p F).IsCanon H' ∧
      HistoryCoherent H' ∧ Realizable H' ∧ InBox n H' := by
  sorry

end LeanUrat.MovesJ
