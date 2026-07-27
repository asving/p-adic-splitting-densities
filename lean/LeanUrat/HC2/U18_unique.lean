/-
Unit U18.presentNorm_unique  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD §3.2 clause (ii) "UNIQUENESS (embedding rigidity)".
deps: MovesD canonRoot/fieldEnum; mathlib.  difficulty: hard.
PROOF-FIRST — rev 2 REMOVES the illusory axiom fallback (P-3 STRUCK, audit GAP-3: it
could not discharge this statement as typed). If the proof fails, the consumers carry
`OmUniqHyp` (Defs §3), typed VERBATIM as this statement — a recorded non-discharge,
never a declaration. STANDING PROBE (permanent, blueprint §3 P-3): the `hbr`-drop
mutation — same-f, same-shape, DISTINCT-BRANCH histories with DISTINCT η-data refute any
uniqueness statement lacking a branch-identity hypothesis; this statement's PrefSet
normalization is what excludes it.
hypothesis_fields: none (or `OmUniqHyp` if it fails).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- UNIQUENESS: Galois-related normalized classes coincide (both normalized ⇒ each read's
residue root is the fieldEnum-LEAST root of its ψ-image; least-root pinning forces the
Galois witness to fix the generated subfield tower). -/
theorem presentNorm_unique {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} :
    ∀ H H' : History p F,
      H ∈ PrefSet n (polOM p F) P → H' ∈ PrefSet n (polOM p F) P →
      EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') →
      etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H' := by
  sorry

end LeanUrat.MovesJ
