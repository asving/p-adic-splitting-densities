/-  MovesV unit V4-10 `meas_marked` (READING LAW at REV 7, C8) — (iv)-MEAS in
    the marked-space form: MarkDisj DERIVED (never hypothesized); f-fence via
    the two-continuation equal-projection instance. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- (a) THE READING LAW: the reading is a FUNCTION of the marked point
(definitional congruence — no extra data enters). -/
theorem markReading {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ} {x : S.Hist q₀ αc}
    (mp mp' : MStep V αc x) (h : mp = mp') :
    V.mReading mp = V.mReading mp' := by rw [h]

/-- (b) THE DERIVED marked-space disjointness (the rev-4/5 HYPOTHESIS name,
now THIS lemma). -/
theorem MarkDisj {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ} {x : S.Hist q₀ αc}
    (mp mp' : MStep V αc x) (h : V.mReading mp ≠ V.mReading mp') (N : ℕ) :
    Disjoint (V.mEvt mp N) (V.mEvt mp' N) := by
  sorry

/-- (b′) the POINT-level form (adds evt_disj_assign within equal readings). -/
theorem MarkDisj_pt {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ} {x : S.Hist q₀ αc}
    (mp mp' : MStep V αc x) (h : mp ≠ mp') (N : ℕ) :
    Disjoint (V.mEvt mp N) (V.mEvt mp' N) := by
  sorry

/-- (c) the terminal-branch corollary (terminals are `.inr` MStep points
with markCard 1). -/
theorem MarkDisjT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ} {x : S.Hist q₀ αc}
    (mp mp' : MStep V αc x) (hT : mp.1.isRight) (hT' : mp'.1.isRight)
    (h : mp ≠ mp') (N : ℕ) :
    Disjoint (V.mEvt mp N) (V.mEvt mp' N) :=
  MarkDisj_pt V mp mp' h N

/-- (d) the f-FENCE: a two-continuation instance where the f-projections
COINCIDE — no ordinary-source disjointness is claimed anywhere. -/
def EqualProjInstance : Prop :=
  ∃ (C : CtsFamily 1) (S : StepSys 1) (V : CtsMeasured 1 C S)
    (αc : S.Cell) (q₀ : ℚ) (x : S.Hist q₀ αc) (mp mp' : MStep V αc x),
    mp ≠ mp' ∧ V.toCtsCells.evtOfStep mp.1 0 = V.toCtsCells.evtOfStep mp'.1 0

theorem equalProj_instance : EqualProjInstance := by
  sorry

end LeanUrat.MovesV
