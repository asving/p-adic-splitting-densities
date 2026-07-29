/-  MovesV unit V4-10 `meas_marked` (READING LAW at REV 7, C8) — (iv)-MEAS in
    the marked-space form: MarkDisj DERIVED (never hypothesized); f-fence via
    the two-continuation equal-projection instance. -/
import LeanUrat.MovesV.Defs
import LeanUrat.MovesV.V1_witnessC

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

/-! ### The equal-projection witness (V4-10 f-fence): a terminal toy with TWO
distinct assignments (`AssignT := Fin 2`) whose f-events are `∅` — two DISTINCT
marked steps whose f-projections coincide, keyed to `V1_witnessC`'s `Ctoy`. -/

/-- `mcS` with a two-element terminal assignment set (mass 0, so `evt_cardT`
holds against the `∅` event below). -/
noncomputable def epS : StepSys 1 := { mcS with
  AssignT := fun _ _ _ _ => Fin 2
  finAT := by intro α v m q₀ x h; exact inferInstance
  massOfT := by intro α v m q₀ x h a; exact (0 : ℝ)
  out_ne := by intro q₀ hq α x hzc; exact Or.inr ⟨vlab1, (), (fun _ => 0), ⟨0⟩⟩ }

/-- the classifier half over `epS`: identical to `mcCells` except the terminal
f-event is `∅` (forced: distinct assignments must have disjoint events). -/
noncomputable def epCells : CtsCells 1 Ctoy epS where
  toStepCells := cellEquiv
  Pools := pow2
  pools_sub := fun _ hq => hq
  pools_pp := by
    rintro q₀ ⟨k, hk, rfl⟩
    exact ⟨2, Nat.prime_two, ⟨k, hk⟩, by norm_num⟩
  pools_closed := pow2_closed
  pools_infinite := pow2_infinite
  Box q₀ N := Fin (max 1 (q₀.num.toNat ^ N))
  finB _ _ := inferInstance
  boxpos _ _ := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩
  box_card := by
    intro q₀ hq N
    rw [Fintype.card_fin]
    exact boxC_card q₀ hq N
  moveOf d := d.hc.elim
  moveOf_bij := by
    intro αc
    constructor
    · intro d d' _
      exact d.1.hc.elim
    · rintro ⟨βc, mv⟩
      exact mv.elim
  moveOfT _ := ()
  moveOfT_bij := by
    intro αc v
    constructor
    · intro d d' _
      exact Subtype.ext (termData_eq d.1 d'.1)
    · intro mv
      exact ⟨⟨⟨sk1, (), (), fun h => h, Subsingleton.elim vlab1 v, cId sk1⟩,
        rfl⟩, rfl⟩
  DCellO _ _ _ _ := Unit
  finDO _ _ _ _ := inferInstance
  cellOfA d := d.hc.elim
  cellOfAT := by intro v d q₀ x h a; exact ()
  emult := by intro s m o α c; exact 1
  evtOf := by intro αc βc mv; exact mv.elim
  evtOfT := by intro αc v mv q₀ x h a N; exact ∅

/-- the step key forgets the terminal assignment (`cellOfAT` is constant), so ALL
`epS` steps share one key — `evt_disj_cell` is vacuous. -/
lemma epCells_stepKey_eq {αc : epS.Cell} {q₀} (x : epS.Hist q₀ αc)
    (p p' : AStep epS αc x) : epCells.stepKey p = epCells.stepKey p' := by
  rcases p with ⟨_, mv, _, _⟩ | ⟨v, mv, h, a⟩
  · exact mv.elim
  · rcases p' with ⟨_, mv', _, _⟩ | ⟨v', mv', h', a'⟩
    · exact mv'.elim
    · obtain rfl : v = v' := Subsingleton.elim v v'
      obtain rfl : mv = mv' := rfl
      obtain rfl : h = h' := funext fun i => i.elim0
      rfl

/-- the measured carrier over `epS` (the ∅-census entrance device, as in `mcV`). -/
noncomputable def epV : CtsMeasured 1 Ctoy epS where
  toCtsCells := epCells
  evt_disj_cell := by
    intro αc q₀ x p p' N hne
    exact absurd (epCells_stepKey_eq x p p') hne
  stabLvl _ := 0
  stabLvlT _ := 0
  evt_card := by intro αc βc mv; exact mv.elim
  evt_cardT := by
    intro αc v mv q₀ x h a hq hzc N hN
    rw [show epCells.evtOfT mv x h a N = ∅ from rfl,
        show epS.massOfT mv x h a = (0 : ℝ) from rfl]
    simp
  evt_disj_assign := by intro αc βc mv; exact mv.elim
  evt_disj_assignT := by
    intro αc v mv q₀ x h a a' hne N
    rw [show epCells.evtOfT mv x h a N = ∅ from rfl]
    exact Finset.disjoint_empty_left _
  cdom d := d.hc.elim
  cdomT _ _ := zeroPart _
  mdom d := d.hc.elim
  mdomT _ := zeroPart _
  activeState _ _ := True
  act_size := by
    intro q₀ hq c
    change True ↔ (1 : Polynomial ℚ).eval q₀ ≠ 0
    simp
  stLvl _ := 0
  stInst := fun c q₀ N => @Finset.univ _ (epCells.finB q₀ N)
  stInst_card := by
    intro c q₀ hq
    letI : Fintype (epCells.Box q₀ 0) := epCells.finB q₀ 0
    rw [Finset.card_univ]
    change ((Fintype.card (Fin (max 1 (q₀.num.toNat ^ 0))) : ℚ))
      = (1 : Polynomial ℚ).eval q₀
    simp
  entDom _ := ⟨[], List.Pairwise.nil⟩
  entLands _ _ := False
  decLands _ _ := Decidable.isFalse fun h => h
  entEvt _ _ _ _ := ∅
  entLvl _ := 0
  entInst _ _ _ _ := ∅
  ent_card := by intro ε β₀ q₀ hq N hN; simp
  ent_sel := by
    intro ε ε' β₀ q₀ hq _ _ _ _
    exact Finset.disjoint_empty_left _
  ent_cut := by
    intro ε β₀ q₀ hq hne
    exact absurd hne Finset.not_nonempty_empty

/-- the two distinct terminal steps (differing only in the `Fin 2` assignment). -/
def epP (a : Fin 2) : @AStep 1 epS () (2 : ℚ) () :=
  Sum.inr ⟨vlab1, (), (fun i => i.elim0), a⟩

/-- read off the assignment (used only to separate `epP 0` from `epP 1`). -/
def epGetA : @AStep 1 epS () (2 : ℚ) () → Fin 2
  | Sum.inl ⟨_, mv, _, _⟩ => mv.elim
  | Sum.inr ⟨_, _, _, a⟩ => a

/-- the two marked steps (mark `0` on each; terminal `markCard = 1`). -/
def epMp (a : Fin 2) : @MStep 1 Ctoy epS epV () (2 : ℚ) () :=
  ⟨epP a, ⟨0, Nat.zero_lt_one⟩⟩

theorem equalProj_instance : EqualProjInstance :=
  ⟨Ctoy, epS, epV, (), 2, (), epMp 0, epMp 1,
    fun heq =>
      absurd (congrArg epGetA (congrArg Sigma.fst heq)) (by decide),
    rfl⟩

end LeanUrat.MovesV
