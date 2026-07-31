/-  TV-E3 (BRIDGE BP3, cluster c4; E-phase skeleton) — LedgerIV GROUPS
    (1)-(2) at the measuredOf witness: xhd_sum / xhd_no_stray /
    xhd_no_orphan / d4r0.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E3).
    deps: TV-E1, TV-E2.  Consumer: TV-E7 (assembly).
    Statements = the `MovesS.LedgerIV` fields (MovesS/Defs:212-223)
    transcribed VERBATIM at M := measuredOf V X cp hfin.
    Sketch: xhd_sum from the X.w face HasSum at μcell (the XHDsC
    Gcell_hasSum face through the μcellH reading); xhd_no_stray /
    xhd_no_orphan from the X.d faces — the XHDdC no_strayC/no_orphanC
    route, as in rep_row's D21 record; d4r0 from V.evt_disj_cell +
    V.evt_disj_assign(T) through the double-dite cellEvt.
    HYPOTHESIS-ROW RESOLUTION (recorded): the row is ledgerIV_inst's own
    row VERBATIM (V7_livC:54-60) + hfin — every member is pre-warranted
    (the duty's premises; TV-E7 has exactly this row available); trimming
    unused members at prover time strengthens the lemma and needs no fence. -/
import LeanUrat.MovesV.TV_E2
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV
open scoped Classical

/-- [E3 helper] the outcome key of an all-outcomes point (non-dependent
Σ-packaging; used by the d4r0 key extraction). -/
private def cellAllOutE3 {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {αc : S.Cell} :
    DCellAll V αc → Σ s : Skeleton n, Σ m : (C.bd s).Letter, (C.bd s).Outc m
  | .inl ⟨d, _⟩ => ⟨d.1.s, d.1.m, d.1.o⟩
  | .inr ⟨_, d, _⟩ => ⟨d.1.s, d.1.m, d.1.o⟩

/-! ### Terminal twins of the V7_livA1 producers (mechanical mirrors:
cntcT/no_strayCT/no_orphanCT/evt_cardT/wT_eq/cellEvtT for cntc/…). -/

/-- terminal twin of `ledgerIV_cells` (V7-6a1): a listed height's terminal
cell event is eventually nonempty. -/
theorem ledgerIV_cellsT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    {v : VLabel n} (d : TermData n C v) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dimT (V.moveOfT d))) (hmem : (V.cdomT d c).Mem h) :
    ∃ N₀, ∀ N ≥ N₀, (V.cellEvtT d x c h N).Nonempty := by
  classical
  refine ⟨V.stabLvlT (V.moveOfT d), fun N hN => ?_⟩
  have hcnt : 0 < V.cntcT d x c h := X.dC.no_strayCT d c h hmem hq x hzc
  unfold CtsMeasured.cntcT at hcnt
  rw [Finset.card_pos] at hcnt
  obtain ⟨a₀, ha₀⟩ := hcnt
  have hq0 : (0 : ℝ) < (q₀ : ℝ) := by
    have h1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
    exact_mod_cast lt_trans one_pos h1
  have hmass : 0 < S.massOfT (V.moveOfT d) x h a₀ := by
    rw [X.w.wT_eq (V.moveOfT d) x h a₀ (V.pools_sub hq) hzc]
    exact zpow_pos hq0 _
  have hboxN : 0 < @Fintype.card _ (V.finB q₀ N) :=
    (@Fintype.card_pos_iff _ (V.finB q₀ N)).mpr (V.boxpos q₀ N)
  have hboxR : (0 : ℝ) < ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ) := by
    exact_mod_cast hboxN
  have hev : ((V.evtOfT (V.moveOfT d) x h a₀ N).card : ℝ)
      = S.massOfT (V.moveOfT d) x h a₀
        * ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ) :=
    V.evt_cardT (V.moveOfT d) x h a₀ hq hzc N hN
  have hcardR : (0 : ℝ) < ((V.evtOfT (V.moveOfT d) x h a₀ N).card : ℝ) := by
    rw [hev]; exact mul_pos hmass hboxR
  have hcardN : 0 < (V.evtOfT (V.moveOfT d) x h a₀ N).card := by
    exact_mod_cast hcardR
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcardN
  unfold CtsMeasured.cellEvtT
  exact ⟨y, Finset.mem_biUnion.mpr ⟨a₀, ha₀, hy⟩⟩

/-- terminal twin of `ledgerIV_orphan` (V7-6a1): an unlisted height's
terminal cell event is empty. -/
theorem ledgerIV_orphanT {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    {v : VLabel n} (d : TermData n C v) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm ⟨d.s, d.α⟩)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dimT (V.moveOfT d))) (hout : ¬ (V.cdomT d c).Mem h) (N : ℕ) :
    V.cellEvtT d x c h N = ∅ := by
  classical
  have hnp : ¬ (0 < V.cntcT d x c h) := fun hp =>
    hout (X.dC.no_orphanCT d x c h hq hzc hp)
  have hz : V.cntcT d x c h = 0 := Nat.eq_zero_of_not_pos hnp
  unfold CtsMeasured.cntcT at hz
  have hfilt := Finset.card_eq_zero.mp hz
  unfold CtsMeasured.cellEvtT
  rw [hfilt, Finset.biUnion_empty]

/-! ### The double-dite event laws on the all-outcomes key. -/

/-- on the listed domain, `evtAll` is eventually nonempty (the no_stray face
through the double dite). -/
theorem evtAll_eventually_nonempty {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    {αc : S.Cell} {q₀ : ℚ} (hq : q₀ ∈ V.Pools)
    (x : S.Hist q₀ αc) (hzc : S.zc x)
    (ca : DCellAll V αc) (H : Σ D : ℕ, Hpt D) (hmem : cdomAllMem V ca H) :
    ∃ N₀, ∀ N ≥ N₀, (evtAll V x N ca H).Nonempty := by
  classical
  obtain ⟨D, h⟩ := H
  cases ca with
  | inl dc =>
      obtain ⟨⟨d, hd⟩, c⟩ := dc
      subst hd
      obtain ⟨e, hmm⟩ := hmem
      simp only [evtAll, dif_pos e]
      rw [eq_of_heq (cast_heq _ x)]
      exact ledgerIV_cells V X cp d x hzc hq c (castHpt e h) hmm
  | inr vdc =>
      obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
      subst hd
      obtain ⟨e, hmm⟩ := hmem
      simp only [evtAll, dif_pos e]
      rw [eq_of_heq (cast_heq _ x)]
      exact ledgerIV_cellsT V X cp d x hzc hq c (castHpt e h) hmm

/-- off the listed domain, `evtAll` is empty (the no_orphan face through the
double dite; the D-mismatch legs are ∅ by definition). -/
theorem evtAll_empty_off_dom {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    {αc : S.Cell} {q₀ : ℚ} (hq : q₀ ∈ V.Pools)
    (x : S.Hist q₀ αc) (hzc : S.zc x)
    (ca : DCellAll V αc) (H : Σ D : ℕ, Hpt D) (hmem : ¬ cdomAllMem V ca H)
    (N : ℕ) : evtAll V x N ca H = ∅ := by
  classical
  obtain ⟨D, h⟩ := H
  cases ca with
  | inl dc =>
      obtain ⟨⟨d, hd⟩, c⟩ := dc
      subst hd
      simp only [evtAll]
      split
      · next e =>
          rw [eq_of_heq (cast_heq _ x)]
          exact ledgerIV_orphan V X cp d x hzc hq c (castHpt e h)
            (fun m => hmem ⟨e, m⟩) N
      · rfl
  | inr vdc =>
      obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
      subst hd
      simp only [evtAll]
      split
      · next e =>
          rw [eq_of_heq (cast_heq _ x)]
          exact ledgerIV_orphanT V X cp d x hzc hq c (castHpt e h)
            (fun m => hmem ⟨e, m⟩) N
      · rfl

/-- TV-E3(a) [LedgerIV group (1), xhd_sum]: guarded two-sided XHD exactness,
representative-quantified — the cell mass is THE height sum of the fixed-
height weights (verbatim `MovesS.LedgerIV.xhd_sum` at measuredOf). -/
theorem measuredOf_xhd_sum {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (x : (measuredOf V X cp hfin).Rep e τ)
      (c : (measuredOf V X cp hfin).Cell e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      HasSum (fun h : (measuredOf V X cp hfin).HDom e τ c =>
          (measuredOf V X cp hfin).gwt e τ c h q₀)
        ((measuredOf V X cp hfin).μcell e τ x c q₀) := by
  intro e τ x c q₀ hq hact
  have hsum1 : Summable (fun h : {h : Σ D : ℕ, Hpt D // h ∈ hdomOf V hfin τ c} =>
      gwtAll V X.w cp (toCellAll V hfin τ c) h.1 q₀) := by
    have hsum0 : Summable (fun ch : Σ c' : DCellAll V (V.toStepCells.symm τ.1),
        Σ D : ℕ, Hpt D => μcellH V X.w (x q₀ hq).1 ch.1 ch.2) :=
      hb.ctbl_add (x q₀ hq).1 (x q₀ hq).2 hq hact
    have hinj : Function.Injective
        (fun h : {h : Σ D : ℕ, Hpt D // h ∈ hdomOf V hfin τ c} =>
          (⟨toCellAll V hfin τ c, h.1⟩ :
            Σ c' : DCellAll V (V.toStepCells.symm τ.1), Σ D : ℕ, Hpt D)) := by
      intro a b hab
      exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp hab).2)
    exact Summable.congr (hsum0.comp_injective hinj)
      (fun h => (gwtAll_eq_μcellH V X.w cp hq (x q₀ hq).1 (x q₀ hq).2
        (toCellAll V hfin τ c) h.1 h.2).symm)
  have hval : (measuredOf V X cp hfin).μcell e τ x c q₀
      = ∑' h : {h : Σ D : ℕ, Hpt D // h ∈ hdomOf V hfin τ c},
          gwtAll V X.w cp (toCellAll V hfin τ c) h.1 q₀ := by
    show μcellOf V X.w cp hfin τ c q₀ = _
    unfold μcellOf
    exact dif_pos hq
  rw [hval]
  exact hsum1.hasSum

/-- TV-E3(b) [LedgerIV group (1), xhd_no_stray]: listed heights are
eventually realized (verbatim `MovesS.LedgerIV.xhd_no_stray` at measuredOf;
the XHDdC no_strayC route). -/
theorem measuredOf_xhd_no_stray {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (x : (measuredOf V X cp hfin).Rep e τ)
      (c : (measuredOf V X cp hfin).Cell e τ)
      (h : (measuredOf V X cp hfin).Hgt),
      h ∈ (measuredOf V X cp hfin).HDom e τ c →
      ∀ q₀ ∈ (measuredOf V X cp hfin).Pools,
      (measuredOf V X cp hfin).activeState q₀ e τ →
      ∃ N₀, ∀ N ≥ N₀,
        ((measuredOf V X cp hfin).cellEvt e τ x c h q₀ N).Nonempty := by
  intro e τ x c h hmem q₀ hq hact
  obtain ⟨N₀, hN⟩ := evtAll_eventually_nonempty V X cp hq (x q₀ hq).1
    (x q₀ hq).2 (toCellAll V hfin τ c) h hmem
  refine ⟨N₀, fun N hNN => ?_⟩
  show (if hq' : q₀ ∈ V.Pools then
      evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c) h else ∅).Nonempty
  rw [dif_pos (show q₀ ∈ V.Pools from hq)]
  exact hN N hNN

/-- TV-E3(c) [LedgerIV group (1), xhd_no_orphan]: unlisted heights carry
empty events (verbatim `MovesS.LedgerIV.xhd_no_orphan` at measuredOf; the
XHDdC no_orphanC route). -/
theorem measuredOf_xhd_no_orphan {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (x : (measuredOf V X cp hfin).Rep e τ)
      (c : (measuredOf V X cp hfin).Cell e τ)
      (h : (measuredOf V X cp hfin).Hgt),
      h ∉ (measuredOf V X cp hfin).HDom e τ c →
      ∀ (q₀ : ℚ) (N : ℕ),
        (measuredOf V X cp hfin).cellEvt e τ x c h q₀ N = ∅ := by
  intro e τ x c h hmem q₀ N
  show (if hq' : q₀ ∈ V.Pools then
      evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c) h else ∅) = ∅
  split
  · next hq =>
      exact evtAll_empty_off_dom V X cp hq (x q₀ hq).1 (x q₀ hq).2
        (toCellAll V hfin τ c) h hmem N
  · rfl

/-- TV-E3(d) [LedgerIV group (2), d4r0]: (cell, height)-keyed event
disjointness (verbatim `MovesS.LedgerIV.d4r0` at measuredOf; from
V.evt_disj_cell + V.evt_disj_assign(T) through the double-dite cellEvt). -/
theorem measuredOf_d4r0 {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (x : (measuredOf V X cp hfin).Rep e τ) (q₀ : ℚ) (N : ℕ)
      (c c' : (measuredOf V X cp hfin).Cell e τ)
      (h h' : (measuredOf V X cp hfin).Hgt), (c, h) ≠ (c', h') →
      Disjoint ((measuredOf V X cp hfin).cellEvt e τ x c h q₀ N)
        ((measuredOf V X cp hfin).cellEvt e τ x c' h' q₀ N) := by
  intro e τ x q₀ N c c' h h' hne
  by_cases hq : q₀ ∈ V.Pools
  case neg =>
    show Disjoint
      (if hq' : q₀ ∈ V.Pools then
        evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c) h else ∅)
      (if hq' : q₀ ∈ V.Pools then
        evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c') h' else ∅)
    rw [dif_neg hq, dif_neg hq]
    exact Finset.disjoint_empty_left _
  case pos =>
    show Disjoint
      (if hq' : q₀ ∈ V.Pools then
        evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c) h else ∅)
      (if hq' : q₀ ∈ V.Pools then
        evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c') h' else ∅)
    rw [dif_pos hq, dif_pos hq]
    rw [Finset.disjoint_left]
    intro b hb hb'
    apply hne
    obtain ⟨o, cc⟩ := c
    obtain ⟨o', cc'⟩ := c'
    obtain ⟨D, hh⟩ := h
    obtain ⟨D', hh'⟩ := h'
    have hzc : S.zc (x q₀ hq).1 := (x q₀ hq).2
    by_cases h1 : (C.bd τ.1.1).cont o.1 o.2 <;>
      by_cases h2 : (C.bd τ.1.1).cont o'.1 o'.2
    -- ── continuing/continuing ──
    · rw [show toCellAll V hfin τ ⟨o, cc⟩
          = Sum.inl ⟨⟨⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, rfl⟩, cc⟩ from by
        unfold toCellAll; rw [dif_pos h1]] at hb
      rw [show toCellAll V hfin τ ⟨o', cc'⟩
          = Sum.inl ⟨⟨⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩, rfl⟩, cc'⟩ from by
        unfold toCellAll; rw [dif_pos h2]] at hb'
      simp only [evtAll] at hb hb'
      split at hb
      case isFalse => simp at hb
      case isTrue e1 =>
      split at hb'
      case isFalse => simp at hb'
      case isTrue e2 =>
      subst e1
      subst e2
      have hb2 : b ∈ V.cellEvt (⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩ : MoveData n C)
          (x q₀ hq).1 cc hh N := hb
      have hb2' : b ∈ V.cellEvt (⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩ : MoveData n C)
          (x q₀ hq).1 cc' hh' N := hb'
      unfold CtsMeasured.cellEvt at hb2 hb2'
      rw [Finset.mem_biUnion] at hb2 hb2'
      obtain ⟨a, haf, hbe⟩ := hb2
      obtain ⟨a', haf', hbe'⟩ := hb2'
      rw [Finset.mem_filter] at haf haf'
      -- the two AStep points at the shared source
      set p : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inl ⟨V.toStepCells.symm
            (MoveData.tgt ⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩),
          V.moveOf ⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, hh, a⟩ with hp
      set p' : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inl ⟨V.toStepCells.symm
            (MoveData.tgt ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩),
          V.moveOf ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩, hh', a'⟩ with hp'
      have hbp : b ∈ V.toCtsCells.evtOfStep p N := hbe
      have hbp' : b ∈ V.toCtsCells.evtOfStep p' N := hbe'
      by_cases hk : V.toCtsCells.stepKey p = V.toCtsCells.stepKey p'
      case neg =>
        exact absurd hbp'
          (Finset.disjoint_left.mp
            (V.evt_disj_cell (x q₀ hq).1 p p' N hk) hbp)
      case pos =>
      haveI : Nonempty {dd : MoveData n C //
          V.toStepCells.symm dd.src = V.toStepCells.symm τ.1} :=
        ⟨⟨⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, rfl⟩⟩
      have hbij := V.moveOf_bij (V.toStepCells.symm τ.1)
      have hk1 := congrArg Prod.fst hk
      simp only [hp, hp', CtsCells.stepKey] at hk1
      have hdd := (Sigma.mk.inj_iff.1 (Sum.inl.inj hk1)).1
      have hd1 : Function.invFun
          (fun dd : {dd : MoveData n C //
              V.toStepCells.symm dd.src = V.toStepCells.symm τ.1} =>
            (⟨V.toStepCells.symm dd.1.tgt,
              castMove dd.2 rfl (V.moveOf dd.1)⟩ :
              Σ βc, S.Move (V.toStepCells.symm τ.1) βc))
          ⟨V.toStepCells.symm
            (MoveData.tgt ⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩),
            V.moveOf ⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩⟩
          = ⟨⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, rfl⟩ :=
        Function.leftInverse_invFun hbij.1 ⟨⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, rfl⟩
      have hd2 : Function.invFun
          (fun dd : {dd : MoveData n C //
              V.toStepCells.symm dd.src = V.toStepCells.symm τ.1} =>
            (⟨V.toStepCells.symm dd.1.tgt,
              castMove dd.2 rfl (V.moveOf dd.1)⟩ :
              Σ βc, S.Move (V.toStepCells.symm τ.1) βc))
          ⟨V.toStepCells.symm
            (MoveData.tgt ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩),
            V.moveOf ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩⟩
          = ⟨⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩, rfl⟩ :=
        Function.leftInverse_invFun hbij.1
          ⟨⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩, rfl⟩
      rw [hd1, hd2] at hdd
      have hd5 : (⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩ : MoveData n C)
          = ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩ := Subtype.ext_iff.mp hdd
      have hd6 := congrArg (fun d : MoveData n C =>
        (⟨d.s, d.m, d.o⟩ : Σ s : Skeleton n,
          Σ m : (C.bd s).Letter, (C.bd s).Outc m)) hd5
      have ho : o = o' := eq_of_heq (Sigma.mk.inj_iff.mp hd6).2
      subst ho
      -- heights
      have hk2 := congrArg Prod.snd hk
      simp only [hp, hp', CtsCells.stepKey] at hk2
      have hhh : hh = hh' := eq_of_heq (Sigma.mk.inj_iff.mp hk2).2
      subst hhh
      -- assignments: equal (else per-assignment disjointness contradicts b)
      by_cases haa : a = a'
      · have hcc : cc = cc' := by rw [← haf.2, ← haf'.2, haa]
        subst hcc
        rfl
      · exact absurd hbp' (Finset.disjoint_left.mp
          (V.evt_disj_assign _ (x q₀ hq).1 hh a a' haa N) hbp)
    -- ── continuing/terminal: the step keys differ at the Sum constructor ──
    · rw [show toCellAll V hfin τ ⟨o, cc⟩
          = Sum.inl ⟨⟨⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, rfl⟩, cc⟩ from by
        unfold toCellAll; rw [dif_pos h1]] at hb
      rw [show toCellAll V hfin τ ⟨o', cc'⟩
          = Sum.inr ⟨C.vlabOf τ.1.1 o'.1 o'.2 h2,
            ⟨⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, rfl⟩, cc'⟩ from by
        unfold toCellAll; rw [dif_neg h2]] at hb'
      simp only [evtAll] at hb hb'
      split at hb
      case isFalse => simp at hb
      case isTrue e1 =>
      split at hb'
      case isFalse => simp at hb'
      case isTrue e2 =>
      subst e1
      subst e2
      have hb2 : b ∈ V.cellEvt (⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩ : MoveData n C)
          (x q₀ hq).1 cc hh N := hb
      have hb2' : b ∈ V.cellEvtT (⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩ :
          TermData n C (C.vlabOf τ.1.1 o'.1 o'.2 h2))
          (x q₀ hq).1 cc' hh' N := hb'
      unfold CtsMeasured.cellEvt at hb2
      unfold CtsMeasured.cellEvtT at hb2'
      rw [Finset.mem_biUnion] at hb2 hb2'
      obtain ⟨a, haf, hbe⟩ := hb2
      obtain ⟨a', haf', hbe'⟩ := hb2'
      set p : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inl ⟨V.toStepCells.symm
            (MoveData.tgt ⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩),
          V.moveOf ⟨τ.1.1, o.1, o.2, h1, τ.1.2⟩, hh, a⟩ with hp
      set p' : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inr ⟨C.vlabOf τ.1.1 o'.1 o'.2 h2,
          V.moveOfT ⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, hh', a'⟩ with hp'
      have hbp : b ∈ V.toCtsCells.evtOfStep p N := hbe
      have hbp' : b ∈ V.toCtsCells.evtOfStep p' N := hbe'
      have hkne : V.toCtsCells.stepKey p ≠ V.toCtsCells.stepKey p' := by
        intro hk
        have hfst := congrArg Prod.fst hk
        simp only [hp, hp', CtsCells.stepKey] at hfst
        cases hfst
      exact absurd hbp' (Finset.disjoint_left.mp
        (V.evt_disj_cell (x q₀ hq).1 p p' N hkne) hbp)
    -- ── terminal/continuing: mirror ──
    · rw [show toCellAll V hfin τ ⟨o, cc⟩
          = Sum.inr ⟨C.vlabOf τ.1.1 o.1 o.2 h1,
            ⟨⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, rfl⟩, cc⟩ from by
        unfold toCellAll; rw [dif_neg h1]] at hb
      rw [show toCellAll V hfin τ ⟨o', cc'⟩
          = Sum.inl ⟨⟨⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩, rfl⟩, cc'⟩ from by
        unfold toCellAll; rw [dif_pos h2]] at hb'
      simp only [evtAll] at hb hb'
      split at hb
      case isFalse => simp at hb
      case isTrue e1 =>
      split at hb'
      case isFalse => simp at hb'
      case isTrue e2 =>
      subst e1
      subst e2
      have hb2 : b ∈ V.cellEvtT (⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩ :
          TermData n C (C.vlabOf τ.1.1 o.1 o.2 h1))
          (x q₀ hq).1 cc hh N := hb
      have hb2' : b ∈ V.cellEvt (⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩ : MoveData n C)
          (x q₀ hq).1 cc' hh' N := hb'
      unfold CtsMeasured.cellEvtT at hb2
      unfold CtsMeasured.cellEvt at hb2'
      rw [Finset.mem_biUnion] at hb2 hb2'
      obtain ⟨a, haf, hbe⟩ := hb2
      obtain ⟨a', haf', hbe'⟩ := hb2'
      set p : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inr ⟨C.vlabOf τ.1.1 o.1 o.2 h1,
          V.moveOfT ⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, hh, a⟩ with hp
      set p' : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inl ⟨V.toStepCells.symm
            (MoveData.tgt ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩),
          V.moveOf ⟨τ.1.1, o'.1, o'.2, h2, τ.1.2⟩, hh', a'⟩ with hp'
      have hbp : b ∈ V.toCtsCells.evtOfStep p N := hbe
      have hbp' : b ∈ V.toCtsCells.evtOfStep p' N := hbe'
      have hkne : V.toCtsCells.stepKey p ≠ V.toCtsCells.stepKey p' := by
        intro hk
        have hfst := congrArg Prod.fst hk
        simp only [hp, hp', CtsCells.stepKey] at hfst
        cases hfst
      exact absurd hbp' (Finset.disjoint_left.mp
        (V.evt_disj_cell (x q₀ hq).1 p p' N hkne) hbp)
    -- ── terminal/terminal ──
    · rw [show toCellAll V hfin τ ⟨o, cc⟩
          = Sum.inr ⟨C.vlabOf τ.1.1 o.1 o.2 h1,
            ⟨⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, rfl⟩, cc⟩ from by
        unfold toCellAll; rw [dif_neg h1]] at hb
      rw [show toCellAll V hfin τ ⟨o', cc'⟩
          = Sum.inr ⟨C.vlabOf τ.1.1 o'.1 o'.2 h2,
            ⟨⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, rfl⟩, cc'⟩ from by
        unfold toCellAll; rw [dif_neg h2]] at hb'
      simp only [evtAll] at hb hb'
      split at hb
      case isFalse => simp at hb
      case isTrue e1 =>
      split at hb'
      case isFalse => simp at hb'
      case isTrue e2 =>
      subst e1
      subst e2
      have hb2 : b ∈ V.cellEvtT (⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩ :
          TermData n C (C.vlabOf τ.1.1 o.1 o.2 h1))
          (x q₀ hq).1 cc hh N := hb
      have hb2' : b ∈ V.cellEvtT (⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩ :
          TermData n C (C.vlabOf τ.1.1 o'.1 o'.2 h2))
          (x q₀ hq).1 cc' hh' N := hb'
      unfold CtsMeasured.cellEvtT at hb2 hb2'
      rw [Finset.mem_biUnion] at hb2 hb2'
      obtain ⟨a, haf, hbe⟩ := hb2
      obtain ⟨a', haf', hbe'⟩ := hb2'
      rw [Finset.mem_filter] at haf haf'
      set p : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inr ⟨C.vlabOf τ.1.1 o.1 o.2 h1,
          V.moveOfT ⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, hh, a⟩ with hp
      set p' : AStep S (V.toStepCells.symm τ.1) (x q₀ hq).1 :=
        Sum.inr ⟨C.vlabOf τ.1.1 o'.1 o'.2 h2,
          V.moveOfT ⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, hh', a'⟩ with hp'
      have hbp : b ∈ V.toCtsCells.evtOfStep p N := hbe
      have hbp' : b ∈ V.toCtsCells.evtOfStep p' N := hbe'
      by_cases hk : V.toCtsCells.stepKey p = V.toCtsCells.stepKey p'
      case neg =>
        exact absurd hbp'
          (Finset.disjoint_left.mp
            (V.evt_disj_cell (x q₀ hq).1 p p' N hk) hbp)
      case pos =>
      haveI hne1 : Nonempty {dd : TermData n C (C.vlabOf τ.1.1 o.1 o.2 h1) //
          V.toStepCells.symm ⟨dd.s, dd.α⟩ = V.toStepCells.symm τ.1} :=
        ⟨⟨⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, rfl⟩⟩
      haveI hne2 : Nonempty {dd : TermData n C (C.vlabOf τ.1.1 o'.1 o'.2 h2) //
          V.toStepCells.symm ⟨dd.s, dd.α⟩ = V.toStepCells.symm τ.1} :=
        ⟨⟨⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, rfl⟩⟩
      have hk1 := congrArg Prod.fst hk
      simp only [hp, hp', CtsCells.stepKey] at hk1
      have hout := congrArg (cellAllOutE3 V) hk1
      simp only [cellAllOutE3] at hout
      have hd1 : Function.invFun
          (fun dd : {dd : TermData n C (C.vlabOf τ.1.1 o.1 o.2 h1) //
              V.toStepCells.symm ⟨dd.s, dd.α⟩ = V.toStepCells.symm τ.1} =>
            castMoveT dd.2 (V.moveOfT dd.1))
          (V.moveOfT ⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩)
          = ⟨⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, rfl⟩ :=
        Function.leftInverse_invFun
          (V.moveOfT_bij (V.toStepCells.symm τ.1) _).1
          ⟨⟨τ.1.1, o.1, o.2, h1, rfl, τ.1.2⟩, rfl⟩
      have hd2 : Function.invFun
          (fun dd : {dd : TermData n C (C.vlabOf τ.1.1 o'.1 o'.2 h2) //
              V.toStepCells.symm ⟨dd.s, dd.α⟩ = V.toStepCells.symm τ.1} =>
            castMoveT dd.2 (V.moveOfT dd.1))
          (V.moveOfT ⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩)
          = ⟨⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, rfl⟩ :=
        Function.leftInverse_invFun
          (V.moveOfT_bij (V.toStepCells.symm τ.1) _).1
          ⟨⟨τ.1.1, o'.1, o'.2, h2, rfl, τ.1.2⟩, rfl⟩
      rw [hd1, hd2] at hout
      have ho : o = o' := eq_of_heq (Sigma.mk.inj_iff.mp hout).2
      subst ho
      -- heights
      have hk2 := congrArg Prod.snd hk
      simp only [hp, hp', CtsCells.stepKey] at hk2
      have hhh : hh = hh' := eq_of_heq (Sigma.mk.inj_iff.mp hk2).2
      subst hhh
      -- assignments
      by_cases haa : a = a'
      · have hcc : cc = cc' := by rw [← haf.2, ← haf'.2, haa]
        subst hcc
        rfl
      · exact absurd hbp' (Finset.disjoint_left.mp
          (V.evt_disj_assignT _ (x q₀ hq).1 hh a a' haa N) hbp)

end LeanUrat.MovesV
