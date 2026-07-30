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
  sorry

end LeanUrat.MovesV
