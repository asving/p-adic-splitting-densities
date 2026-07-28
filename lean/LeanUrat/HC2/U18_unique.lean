/-
Unit U18.presentNorm_unique  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD §3.2 clause (ii) "UNIQUENESS (embedding rigidity)".
deps: MovesD canonRoot/fieldEnum; mathlib.  difficulty: hard.
PROOF-FIRST — rev 2 REMOVES the illusory axiom fallback (P-3 STRUCK, audit GAP-3: it
could not discharge this statement as typed). STANDING PROBE (permanent, blueprint §3
P-3): the `hbr`-drop mutation — same-f, same-shape, DISTINCT-BRANCH histories with
DISTINCT η-data refute any uniqueness statement lacking a branch-identity hypothesis;
this statement's PrefSet normalization is what excludes it.
K3 RESTATEMENT (2026-07-28, sign-off round — the consolidated-frontier K3 kernel): the
statement GAINS THE ADJACENCY HYPOTHESES `AdjacentReads H` / `AdjacentReads H'` (Defs K3
addendum), DICTATED by the conditional refutation `lean/scratch_U18_unique_false.lean`:
at a last-node NON-ADJACENT recentering (`s0 + wSide < μ_parent`, the witness's
`hnonadj`), realizability's (HV) clause is vacuous and `canonRoot` is TRIVIAL
(ψ = X − C center has a singleton root set), so conjugating only the last node's residue
data by Frobenius produces a second PrefSet member with EtaGalEq-related but DISTINCT
η-data — machine-checked modulo the concrete 2-node instance (HC-1 S9 territory).
Adjacency restores (HV)'s reach to every read, which is exactly what the least-root
normalization needs to bite at recenterings. CONSEQUENCE for consumers: this no longer
discharges `PresentNorm`'s clause (ii) as typed; `presentNorm_polOM` (U17c) carries
`OmUniqHyp` per the P-3 disposition — with the recorded caveat that `OmUniqHyp` as typed
is itself conditionally refuted (`omUniqHyp_refuted_by_witness`, same scratch); the
wave-4 dictionary negotiation decides the final uniqueness form.
hypothesis_fields: hadj/hadj' (K3).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- UNIQUENESS, ADJACENCY-GUARDED (K3 restatement): Galois-related normalized classes of
ADJACENT histories coincide (both normalized ⇒ each read's residue root is the
fieldEnum-LEAST root of its ψ-image; least-root pinning forces the Galois witness to fix
the generated subfield tower — and adjacency gives (HV)'s cross-read tie at every step,
closing the non-adjacent-recentering escape the refutation witness exploited). -/
theorem presentNorm_unique {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} :
    ∀ H H' : History p F,
      H ∈ PrefSet n (polOM p F) P → H' ∈ PrefSet n (polOM p F) P →
      AdjacentReads H → AdjacentReads H' →
      EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') →
      etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H' := by
  sorry

end LeanUrat.MovesJ
