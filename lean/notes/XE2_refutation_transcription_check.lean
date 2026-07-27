/-
Companion to notes/XE2_refutation_witness.lean (escalation prover, 2026-07-27).

TRANSCRIPTION CHECK: the ∀-closure refuted by
`LeanUrat.MovesX.XE2Refutation.envelopeExp_statement_false` accepts `envelopeExp`
itself as an inhabitant, i.e. it agrees with the declaration's actual type (up to
definitional equality).  Hence a sorry-free, axiom-free proof of `envelopeExp` as
stated would yield False: the XE.2 statement is unprovable (indeed false).

This file imports the sorry-bodied XE2 unit, so it (unlike the witness file)
depends on sorryAx — it certifies only the TYPE agreement.  Check with:
  cd lean && lake env lean notes/XE2_refutation_transcription_check.lean
-/
import LeanUrat.MovesX.XE2

namespace LeanUrat.MovesX.XE2TranscriptionCheck

open LeanUrat.MovesX

set_option linter.unusedVariables false

example : (∀ (n : ℕ) (hn : 2 ≤ n) (X : XFamily n) (K : XConsts n),
        X2ProgressP n X K → X2BridgeP n X → X2AffP n X K → X2CapP n X K →
        X1aAlignP n X ⟨true, false⟩ → WeightChargeFullP n X K →
        X2TailsP n X K → NsNullP n X → X3aRouteP n X K →
        ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧ ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
          ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N))) :=
  envelopeExp

end LeanUrat.MovesX.XE2TranscriptionCheck
