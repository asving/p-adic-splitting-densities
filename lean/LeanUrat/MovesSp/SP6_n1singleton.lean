/-
Unit Sp.n1singleton [REV 3, G2 — was Sp.n1Clause; the cycle is split: only the
root-confirming half is consumed here, and Sp.n1Word consumes THIS unit]
[REV 4, Codex-12 + Fable NOTE B — the sketch's route declared; confirmingRoot1 a
DefsN3 literal] — moves_ref: "(G6) … (or W = n = 1 at the root — the degenerate
degree)" + the n = 1 clause: "At n = 1 the catalogue word is the single ROOT
letter".
deps: Sp.speciesEnumComplete, Sp.n1RootConfirming, Sp.succTerminal, Sp.g6Forcing.
sketch: root-admissible at n = 1 pins every field (g6Forcing at W = 1);
terminal ⇒ no step case. difficulty: easy-medium.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SnRaw1_eq : ∀ s, InCatalogue 1 s ↔ s = confirmingRoot1 := sorry

end LeanUrat.MovesSp
