/-
Unit D2a.L8_finite_C  (MovesD campaign, E-phase)
moves_ref: "L8: Pref(P̂) is FINITE … Hence #Pref(P̂) ≤ M(P̂)·∏_r Q_r^{d_r} < ∞".
deps: Defs.
sketch: EtaData is a Pi of finite types; `if_neg`.  difficulty: easy.
hypothesis_fields: `hnorm : PresentNorm n pol P` (on `CD_eq` — the open dictionary pin,
HC-2; §2 ledger) [REV 7, Codex#5 g.4]; the `Finite` instance itself is hypothesis-free
(the η-class construction).
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

/-- `EtaData` is a Pi (over `Fin _.length`) of products of function types `Fin _ → F`;
since `F` is finite it is finite. -/
instance instEtaDataFinite (P' : ShapePrefix) : Finite (EtaData F P') := by
  unfold EtaData
  infer_instance

/-- L8, structural: the class index is finite (a subtype of the finite `EtaData`). -/
instance instPrefIdxFinite : Finite (PrefIdx n pol P) := by
  infer_instance

/-- On nonempty shapes the corpus C is the class count (the note's C over normalized
presentations, never a policy-void artifact — hnorm). -/
theorem CD_eq (hnorm : PresentNorm n pol P) (hne : (P : ShapePrefix).reads ≠ []) :
    P.CD pol = Nat.card (PrefIdx n pol P) := by
  unfold Shape.CD
  rw [if_neg hne]

end LeanUrat.MovesD
