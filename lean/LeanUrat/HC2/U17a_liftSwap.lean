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
  -- BLOCKED (2026-07-31, hc2-p-phase-hard prover round; statement byte-unchanged).
  -- The named `StageTransHyp` as typed CANNOT drive the required rebuild:
  -- (a) RECENTERING legs have NO supplier — swapping a recentering lift to
  --     `polOM.liftOf` changes the child key `Φ' = Φ − t'`, so the child stage must be
  --     REBUILT via `IsRecenteringCore σ σ'`, but `StageTransHyp` concludes only the
  --     increment-shaped `TransitionCoreL`; the recentered-stage constructor is HC-1
  --     D.7/D.10 property, not present in this hypothesis;
  -- (b) INCREMENT legs are the HK-03 steep perimeter: `stageTransHyp_steep_empty`
  --     (HC2/HK03, E-phase skeleton) records that under `StageTransHyp` NO lawful
  --     steep read instance (`2 ≤ e'·g`, every increment by `hspecInc`) exists on a
  --     `StageCoreL` stage — so the rebuild either needs the closure-by-contradiction
  --     route (requiring `StageCoreL`/`IAug`/`ψ ≠ X` at the REBUILT stage — exactly
  --     the unproved HK-49/HK-50 rebuild invariant) or a re-keyed hypothesis;
  -- (c) the BP2 decomposition of this unit (HK-49/HK-50/HK-53/HK-54/HK-41,
  --     BRIDGE_BP2_HC2K1_2026-07-30.md §4) is NOT yet elaborated, and its risk row R-8
  --     pre-declares the fallback: U17a converts to carrying the leg-shaped named
  --     hypothesis — a statement-fence event (designer sign-off), never a prover fill.
  -- Also gated behind the in-flight HK-06 `StageTransHyp` re-key (task #44; the
  -- ARCHIVAL-DISCIPLINE note in HK03 renames the subject to `StageTransHypOld`).
  sorry

end LeanUrat.MovesJ
