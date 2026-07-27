/-
Unit F3.emptyBridge  (MovesD campaign, E-phase)
[REV 5, reconciliation (3) — Codex#3 finding 5 ∧ Fable#3 C-6: the ∅-representation
deviation is a THEOREM on the Option-level object, not a prose declaration.]
moves_ref: "Pref(∅) = {∅}" (L12/D4R.1's dispatch) — now LITERAL: the Option-level Pref of
the empty shape IS the singleton of the empty chain, and the corpus C (`CD`) equals the
class count of `PrefOpt` UNIFORMLY (both branches machine-checked). The consumed
arithmetic (D14a's law, D10's constant via CD_eq) is thereby EQUIVALENT to the note's
ontology by theorem.
deps: Defs, D2a, F1.
sketch: set ext + match unfolding; `Option.some` injective for the card transport.
difficulty: easy.  hypothesis_fields: none.
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
  {pol : CanonPolicy p F} {P : Shape n}

/-- The note's "Pref(∅) = {∅}", literally, on the Option-level object. -/
theorem PrefOpt_empty (hP : (P : ShapePrefix).reads = []) :
    PrefOpt n pol P = ({Option.none} : Set (Option (History p F))) := by
  sorry

/-- On nonempty shapes the Option-level Pref is the some-image of the literal PrefSet. -/
theorem PrefOpt_nonempty (hne : (P : ShapePrefix).reads ≠ []) :
    PrefOpt n pol P = Option.some '' PrefSet n pol P := by
  sorry

/-- The corpus C equals the Option-level class count UNIFORMLY (both branches). -/
theorem CD_correspondence :
    P.CD pol = Nat.card ↥(etaDataO (P : ShapePrefix) '' PrefOpt n pol P) := by
  sorry

end LeanUrat.MovesD
