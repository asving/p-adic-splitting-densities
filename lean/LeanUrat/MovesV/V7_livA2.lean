/-  MovesV unit V7-6a2 `ledgerIV_counts` — THE DISJOINTNESS/CENSUS SUITE:
    d4r0 via evt_disj_cell at distinct keys; init_count via ent_card +
    box_card (gate: 128 = (1/4)·512); ent_count_card rfl-level. -/
import LeanUrat.MovesV.V7_livA1
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- ent_count_card at the census keying — rfl-level BY DEF (§2.F). -/
theorem ledgerIV_ent_count_card {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ) :
    (V.entInst ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)).card
      = V.entCensus ε β₀ q₀ :=
  rfl

/-- the F-1 acceptance number at gate B: (1/4)·512 = 128. -/
theorem ledgerIV_gate_number : gateB_iota * 512 = 128 := by
  norm_num [gateB_iota]

theorem ledgerIV_d4r0 {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ} (x : S.Hist q₀ αc)
    (p p' : AStep S αc x) (N : ℕ)
    (hkey : V.toCtsCells.stepKey p ≠ V.toCtsCells.stepKey p') :
    Disjoint (V.toCtsCells.evtOfStep p N) (V.toCtsCells.evtOfStep p' N) :=
  V.evt_disj_cell x p p' N hkey

end LeanUrat.MovesV
