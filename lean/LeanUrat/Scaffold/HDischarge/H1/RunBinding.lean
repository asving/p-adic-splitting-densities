/-
HDISCHARGE_H1 §5.3 — H1-U12 (`CountedRunBinding`): member (c)'s row, STATEMENT ONLY.

The OL-2a-6 face over the corpus's counted set via `ReadsOf` (HC2 Wall A): every
(polynomial, history) pair in the counted corpus is a classifier run — H is a coherent
recorded tower realized by f's developments at every read. Transcribed VERBATIM from
`lean/blueprints/HDISCHARGE_H1.md` §5.3, H1-U12 bullet.

E-PHASE-FLAGGED: the CONCRETE `corpus` binder is wired at E-phase to the classifier's
counted boxes (candidates: TreeSeam/`MovesT.treeN` fibers; the M04 §5.5 K1 route) —
NOT probed at the concrete corpus here. The wired conformance theorem (the (c)
discharge) is the SEPARATE unit H1-U13 (`countedRunBinding_wired`, gated on falsifier
N-2 green). This def is an interface carrier only; never cite it as evidence for (c).
-/
import LeanUrat.Scaffold.HDischarge.H1.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H1

open LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC LeanUrat.MovesJ

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- H1-U12 — member (c)'s row: the OL-2a-6 face over the corpus's counted set. Every
counted (f, H) pair is a `ReadsOf` run (the HC2 Wall-A record). The concrete `corpus`
binder is wired at E-phase (TreeSeam/`MovesT.treeN` fiber candidates; M04 §5.5 K1
route); the wired discharge is H1-U13. -/
def CountedRunBinding (n : ℕ) (corpus : Set (Polynomial ℤ_[p] × History p F)) : Prop :=
  ∀ fH ∈ corpus, ReadsOf p F n fH.1 fH.2

end LeanUrat.Scaffold.HDischarge.H1
