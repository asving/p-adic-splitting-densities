/-
Unit D0a.topLocus_laws  (MovesD campaign, E-phase)
moves_ref: "Z = ⊤: no constraint, vol(⊤) = 1" (§D4-R L6).
deps: MovesC.Defs (via Defs).
sketch: `pinned ≡ false`; unfold + simp.  difficulty: easy.
hypothesis_fields: none.
[E-PHASE NOTE: the blueprint's binder `Σf` is renamed `Sf` — `Σ` is a binder token in
Lean; recorded in MANIFEST deviations.]
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

/-- ⊤ solves at every box point (nothing is pinned). -/
theorem topLocus_sol (x : Box p m) : (topLocus p m).IsSolution x := by
  intro i h
  simp [topLocus] at h

/-- ⊤ pins nothing: `numPinned = 0` (so `vol(⊤) = 1` in the division-free reading). -/
theorem topLocus_numPinned : (topLocus p m).numPinned = 0 := by
  simp [DigitSystem.numPinned, topLocus]

/-- ⊤ is admissible against EVERY state cylinder (§C.2's `AdmissibleZ`, vacuously). -/
theorem topLocus_admissible (Sf : Locus p m) : AdmissibleZ Sf (topLocus p m) := by
  intro c h
  simp [topLocus] at h

end LeanUrat.MovesD
