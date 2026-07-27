/-
Unit U1b.nodeLift_exists  (HC-2 campaign, E-phase — rev 2, audit GAP-1: THE OWNED
STAGE↔NODE BRIDGE; the F10 trap gets a named unit instead of an inline check)
moves_ref: §B2-DEF D.5 (the lift at the READ's own pair, per the F10 adjudication);
MovesC `IsNodeLift` docstring.
deps: D8, Moves L3_liftExists (the stage-pair sibling — proof SHAPE only, never its
statement), Stage.hS6b.  difficulty: medium.
hypothesis_fields: none (target) — the named D.5 side conditions `hdvd`/`hthr` below are
the E-phase concretization of the blueprint's "(the read's D.5 side conditions)" ellipsis
(the pre-authorized fallback; statement-fence: hypothesis narrowing, sign-off pending —
recorded in MANIFEST deviations).
NAMED RISK (blueprint): the stride/stretch arithmetic — `hStretch` puts C-weights in
`e·ℤ` while the read pair wants `σ.w (t_k) = h'·(g−k)`.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Read-pair lift existence from stage data (L3's proof shape at the node's pair): the
(S6b) realizers taken at the read's `h'` on the frame's CURRENT valuation. -/
theorem nodeLift_exists {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (ψ : Polynomial ↥σ.K) (g e' h' : ℕ) (hψm : ψ.Monic) (hψd : ψ.natDegree = g)
    (hg : 1 ≤ g) (hh' : 1 ≤ h')
    (hdvd : ∀ k : ℕ, k < g → (σ.e : ℤ) ∣ (h' : ℤ) * ((g : ℤ) - (k : ℤ)))
    (hthr : ∀ k : ℕ, k < g → (σ.e : ℤ) * σ.wPrev σ.Φ < (h' : ℤ) * ((g : ℤ) - (k : ℤ))) :
    ∃ Φhat, IsReadLift σ ψ g e' h' Φhat := by
  sorry

end LeanUrat.MovesJ
