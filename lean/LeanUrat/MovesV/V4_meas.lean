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
  rw [Finset.disjoint_left]
  rintro ⟨b, t⟩ hmem hmem'
  simp only [CtsMeasured.mEvt, Finset.mem_image, Prod.mk.injEq] at hmem hmem'
  obtain ⟨b1, hb1, hbb1, htt1⟩ := hmem
  obtain ⟨b2, hb2, hbb2, htt2⟩ := hmem'
  subst hbb1; subst hbb2
  have hkey : V.toCtsCells.stepKey mp.1 ≠ V.toCtsCells.stepKey mp'.1 := by
    intro hk
    exact h (by simp only [CtsMeasured.mReading, hk, htt1, htt2])
  exact (Finset.disjoint_left.1 (V.evt_disj_cell x mp.1 mp'.1 N hkey)) hb1 hb2

/-- (b′) the POINT-level form (adds evt_disj_assign within equal readings). -/
theorem MarkDisj_pt {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} {q₀ : ℚ} {x : S.Hist q₀ αc}
    (mp mp' : MStep V αc x) (h : mp ≠ mp') (N : ℕ) :
    Disjoint (V.mEvt mp N) (V.mEvt mp' N) := by
  obtain ⟨p, i⟩ := mp
  obtain ⟨p', i'⟩ := mp'
  by_cases hr : V.mReading ⟨p, i⟩ = V.mReading ⟨p', i'⟩
  · -- equal readings, distinct points: same key + same tag, distinct assignments
    have hkey : V.toCtsCells.stepKey p = V.toCtsCells.stepKey p' := by
      have := congrArg Prod.fst hr; simpa [CtsMeasured.mReading] using this
    have htag : (i : ℕ) = (i' : ℕ) := by
      have := congrArg Prod.snd hr; simpa [CtsMeasured.mReading] using this
    have hpp : p ≠ p' := by
      rintro rfl
      exact h (congrArg (fun j => (⟨p, j⟩ : MStep V αc x)) (Fin.ext htag))
    have hstep : Disjoint (V.toCtsCells.evtOfStep p N)
        (V.toCtsCells.evtOfStep p' N) := by
      rcases p with ⟨β, mv, hpt, a⟩ | ⟨v, mv, hpt, a⟩ <;>
        rcases p' with ⟨β', mv', hpt', a'⟩ | ⟨v', mv', hpt', a'⟩
      · -- inl / inl
        haveI : Nonempty {d : MoveData n C // V.toCtsCells.toStepCells.symm d.src = αc} :=
          ⟨((V.toCtsCells.moveOf_bij αc).2 ⟨β, mv⟩).choose⟩
        have hbij := V.toCtsCells.moveOf_bij αc
        have h1 := congrArg Prod.fst hkey
        simp only [CtsCells.stepKey] at h1
        have hdd := (Sigma.mk.inj_iff.1 (Sum.inl.inj h1)).1
        have hbm : (⟨β, mv⟩ : Σ βc, S.Move αc βc) = ⟨β', mv'⟩ := by
          rw [← Function.invFun_eq (hbij.2 (⟨β, mv⟩ : Σ βc, S.Move αc βc)),
              ← Function.invFun_eq (hbij.2 (⟨β', mv'⟩ : Σ βc, S.Move αc βc)), hdd]
        injection hbm with hβ hmv
        subst hβ
        obtain rfl := eq_of_heq hmv
        have hsnd := congrArg Prod.snd hkey
        simp only [CtsCells.stepKey] at hsnd
        injection hsnd with _ hh
        subst hh
        have haa : a ≠ a' := by rintro rfl; exact hpp rfl
        exact V.evt_disj_assign mv x hpt a a' haa N
      · exact absurd (congrArg Prod.fst hkey) (by simp [CtsCells.stepKey])
      · exact absurd (congrArg Prod.fst hkey) (by simp [CtsCells.stepKey])
      · -- inr / inr
        have h1 := congrArg Prod.fst hkey
        simp only [CtsCells.stepKey] at h1
        have hvv : v = v' := (Sigma.mk.inj_iff.1 (Sum.inr.inj h1)).1
        subst hvv
        haveI : Nonempty {d : TermData n C v // V.toCtsCells.toStepCells.symm ⟨d.s, d.α⟩ = αc} :=
          ⟨((V.toCtsCells.moveOfT_bij αc v).2 mv).choose⟩
        have hbij := V.toCtsCells.moveOfT_bij αc v
        have h1' := congrArg Prod.fst hkey
        simp only [CtsCells.stepKey] at h1'
        have hdd := (Sigma.mk.inj_iff.1
          (eq_of_heq (Sigma.mk.inj_iff.1 (Sum.inr.inj h1')).2)).1
        have hbm : mv = mv' := by
          rw [← Function.invFun_eq (hbij.2 mv), ← Function.invFun_eq (hbij.2 mv'), hdd]
        subst hbm
        have hsnd := congrArg Prod.snd hkey
        simp only [CtsCells.stepKey] at hsnd
        injection hsnd with _ hh
        subst hh
        have haa : a ≠ a' := by rintro rfl; exact hpp rfl
        exact V.evt_disj_assignT mv x hpt a a' haa N
    rw [Finset.disjoint_left]
    rintro ⟨b, t⟩ hmem hmem'
    simp only [CtsMeasured.mEvt, Finset.mem_image, Prod.mk.injEq] at hmem hmem'
    obtain ⟨b1, hb1, hbb1, _⟩ := hmem
    obtain ⟨b2, hb2, hbb2, _⟩ := hmem'
    subst hbb1; subst hbb2
    exact (Finset.disjoint_left.1 hstep) hb1 hb2
  · exact MarkDisj V ⟨p, i⟩ ⟨p', i'⟩ hr N

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
