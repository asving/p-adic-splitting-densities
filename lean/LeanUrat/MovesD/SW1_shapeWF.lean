/-
Unit SW1.ShapeWF_of_matches  (MovesD campaign, E-phase)  [REV 6 — the universe-loss
guard; REV 8, Codex#6 c.2 — MonicTie now DERIVED except its one genuinely encoding-level
clause; REV 9, Fable#7 G-1/G-2 — hw0 named + the wchain mechanism written in]
moves_ref: (the L3 dictionary: every note-η's shape is dictionary-image — so the subtype
loses NOTHING of the note's universe). THE MONICTIE DERIVATION [REV 8]: monicTop → r = 0
is DERIVED (`hmonicRoot` + `root_iff` via Matches); the RESIDUE — the root read's
monicTop ↔ (s0 + wSide = n) — is the named encoding gap ENC-MONIC, kept as the WEAKEST
SUFFICIENT hypothesis `hmt0` ("slot 3 = the monic lead, digit 1", §D4-R.6).
deps: E4, E5, E10.
sketch: transport each certificate clause from the matched history: species_iff from
`History.root_iff`; window/dchain from `HistoryCoherent`; gmu from E5 (hOrd) + E4; edvd
from `Node.hEdvd`; root_box from `InBox`; gamTie from coherence's γ-tie clause + Matches
+ D6a (strS); anchorTie from `Node.hAnchor` + `hbezCanon`-uniqueness against `bezT`;
w0 from `hw0` + Matches' pool-card clause (exponent-injectivity at p ≥ 2); wchain via
`TransitionData.child_field` + E10's field-tower card lemma (hψirr/hψmonic/hψdeg/
hzbarRoot), recenterings via `IsRecenteringCore` K-equality + `hspecRec`.
difficulty: medium-hard.
hypothesis_fields: `hmt0` (ENC-MONIC), `hw0` (ROOT-POOL) — both ledgered, §2.
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

/-- Every matched coherent in-box history's shape carries the certificate — the note's
universe is not lost to the subtype (ENC-MONIC = hmt0, ROOT-POOL = hw0; §2 ledger). -/
theorem ShapeWF_of_matches {Q : ShapePrefix} {H : History p F} (hM : Q.MatchesHist H)
    (hcoh : HistoryCoherent H) (hbox : InBox n H)
    (hmt0 : ∀ h0 : 0 < Q.reads.length,
      ((Q.reads[0]'h0).monicTop = true ↔ (Q.reads[0]'h0).s0 + (Q.reads[0]'h0).wSide = n))
    (hw0 : ∀ hj : 0 < H.nodes.length, Nat.card ↥((H.nodes[0]'hj).σ.K) = p) :
    ShapeWF n Q := by
  sorry

end LeanUrat.MovesD
