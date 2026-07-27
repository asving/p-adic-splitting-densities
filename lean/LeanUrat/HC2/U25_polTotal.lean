/-
Unit U25.polOM_total  (HC-2 campaign, E-phase — blueprint §5 Layer D; escalation risk #1
for arithmetic: the D.10 scale bookkeeping)
moves_ref: §D4-R L1 (canonical-choice totality, kernel (a) — DUAL-VERIFIED at the math
level: PROJECT_STATE "kernel parts (a)+(b) DISCHARGED"); §B2-DEF (S6b′) consumers item
(ii) "the recentering lift (D.10): W = λ″ > w(Φ̂) — (I-aug) is literally the hypothesis".
deps: Stage.hS6b + coherence's (I-aug) chain.  difficulty: HARD.
NAMED RISK (blueprint; resolve FIRST at E-phase, before any prover runs): the scale
bookkeeping — `RecenterLiftSpec` wants `σ.w tL = σ.w σ.Φ` while `hStretch` puts C-weights
in `e·ℤ`; the note's D.10 resolves this with the eligibility side conditions (e_read = 1
reads). If the Lean node vocabulary admits ineligible recentering nodes that the note
excludes, this unit's hypothesis must name the eligibility predicate (statement-fence:
hypothesis NARROWING, needs sign-off + a note-line citation — MOVES 2583–2671). The U30
gate is the day-one tripwire for exactly this risk.
hypothesis_fields: none (target), or the named eligibility predicate (fallback).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- POL-TOTALITY (L1 kernel-(a)): at every recentering node of a coherent realizable
history, a `RecenterLiftSpec` realizer exists. -/
theorem polOM_total {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    ∃ tL : Polynomial ℤ_[p], RecenterLiftSpec (H.nodes[i]'hi) tL := by
  sorry

/-- Hence `polOM.liftOf` itself satisfies the spec at such nodes (choice reading). -/
theorem polOM_liftOf_spec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    RecenterLiftSpec (H.nodes[i]'hi) ((polOM p F).liftOf (H.nodes[i]'hi)) := by
  sorry

end LeanUrat.MovesJ
