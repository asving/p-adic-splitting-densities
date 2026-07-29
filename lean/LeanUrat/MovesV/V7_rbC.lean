/-  MovesV unit V7-5c `ratBurdens_inst` leg (d) + assembly — cellP REVERTED
    to the sizeP wiring (F-5); the nonemptiness step `cell_ne_inst`
    displayed; the assembled Nonempty (RatBurdens T M) under the stated
    premises. -/
import LeanUrat.MovesV.V7_rbB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the roster lemma (REV 4, G-1's displayed nonemptiness step): pick a zc
history (zc_ne), apply productivity (out_ne), classify (cellOfA/cellOfAT). -/
theorem cell_ne_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (αc : S.Cell) {q₀ : ℚ} (hq : q₀ ∈ S.Pools) :
    Nonempty (V.CellOf αc) := by
  obtain ⟨x, hzc⟩ := S.zc_ne q₀ hq αc
  rcases S.out_ne q₀ hq αc x hzc with ⟨β, m, h, ha⟩ | ⟨v, m, h, ha⟩
  · exact ⟨(V.toCtsCells.stepKey (Sum.inl ⟨β, m, h, ha.some⟩)).1⟩
  · exact ⟨(V.toCtsCells.stepKey (Sum.inr ⟨v, m, h, ha.some⟩)).1⟩

/-- NAMED OPEN INSTANTIATION DUTY (M4 soundness repair, ratification
verdict 2026-07-29): the E-phase `∨ True` escape (`Or.inr trivial` — a
propositionally vacuous seam) is DELETED; the honest statement is the
∃-bundled duty — a table shape + measured side + rational-burden data built
from the bound CTS objects (the V7-3a/V7-4 seam instances; a degenerate
witness does NOT discharge the duty — MANIFEST record).  Quantifier repair
as in `ledgerIV_inst`: `Nonempty (RatBurdens T M)` at the old ARBITRARY
(T, M) arguments would be an unsafe sorry. -/
theorem ratBurdens_exists {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      Nonempty (MovesS.RatBurdens T M) := by
  sorry

end LeanUrat.MovesV
