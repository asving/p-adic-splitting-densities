/-  TV-E4 (BRIDGE BP3, cluster c4; E-phase skeleton) — LedgerIV GROUPS
    (3)-(5) at the measuredOf witness: part1 / rep_indep / meas_card.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E4).
    deps: TV-E1, TV-E2.  Consumer: TV-E7 (assembly).
    Statements = the `MovesS.LedgerIV` fields (MovesS/Defs:225-236)
    transcribed VERBATIM at M := measuredOf V X cp hfin.
    Sketch: part1 via the PROVED part1 producer (V4_part1C — its hb/hc/hd
    premises are ledgerIV_inst's own premises verbatim, re-indexed from the
    DCellAll Σ-carrier to the per-(e,τ) cell Fintype); rep_indep via
    rep_row (V4-9; cp premise present, XHDdC from X.dC) — near-rfl if
    rowVal is DEFINED as the representative cell sum (the TV-E2 record);
    meas_card via V.evt_card at N ≥ stabLvl (+ V.box_card for the ℝ-cast),
    aggregated over the cell's assignment fiber through the double-dite.
    HYPOTHESIS-ROW RESOLUTION: ledgerIV_inst's own row verbatim + hfin
    (see the TV-E3 header record; trimming = strengthening, no fence). -/
import LeanUrat.MovesV.TV_E2
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV
open scoped Classical

/-- [E4 helper] the per-(cell, height) counting law on the all-outcomes key:
on the listed domain, the x-free cp weight COUNTS its double-dite event,
eventually (evt_card/evt_cardT at N ≥ stabLvl through the per-assignment
disjointness — the (iv)-MEAS aggregation). -/
theorem evtAll_card {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    {αc : S.Cell} {q₀ : ℚ} (hq : q₀ ∈ V.Pools)
    (x : S.Hist q₀ αc) (hzc : S.zc x)
    (ca : DCellAll V αc) (H : Σ D : ℕ, Hpt D) (hmem : cdomAllMem V ca H) :
    ∃ N₀, ∀ N ≥ N₀,
      gwtAll V X.w cp ca H q₀ * ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ)
        = ((evtAll V x N ca H).card : ℝ) := by
  classical
  obtain ⟨D, h⟩ := H
  cases ca with
  | inl dc =>
      obtain ⟨⟨d, hd⟩, c⟩ := dc
      subst hd
      obtain ⟨e, hmm⟩ := hmem
      refine ⟨V.stabLvl (V.moveOf d), fun N hN => ?_⟩
      simp only [gwtAll, evtAll, dif_pos e]
      rw [eq_of_heq (cast_heq _ x)]
      -- the biUnion card is the assignment-fiber sum (per-assignment disjointness)
      letI := S.finA (V.moveOf d) x (castHpt e h)
      have hcard : (V.cellEvt d x c (castHpt e h) N).card
          = ∑ a ∈ Finset.univ.filter
              (fun a : S.Assign (V.moveOf d) x (castHpt e h) =>
                V.cellOfA d x (castHpt e h) a = c),
              (V.evtOf (V.moveOf d) x (castHpt e h) a N).card := by
        unfold CtsMeasured.cellEvt
        exact Finset.card_biUnion
          (fun a _ b _ hab => V.evt_disj_assign _ x _ a b hab N)
      rw [hcard]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ =>
        V.evt_card (V.moveOf d) x (castHpt e h) a hq hzc N hN)]
      rw [Finset.sum_congr rfl (fun a _ => by
        rw [X.w.w_eq (V.moveOf d) x (castHpt e h) a (V.pools_sub hq) hzc])]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcnt : ((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ)
          = (V.cntc d x c (castHpt e h) : ℚ) :=
        cp.count d c x hzc hq (castHpt e h) hmm
      have hcnt' : (((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ)
          = ((Finset.univ.filter
              (fun a : S.Assign (V.moveOf d) x (castHpt e h) =>
                V.cellOfA d x (castHpt e h) a = c)).card : ℝ) := by
        rw [hcnt]; norm_cast
      rw [hcnt']
      ring
  | inr vdc =>
      obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
      subst hd
      obtain ⟨e, hmm⟩ := hmem
      refine ⟨V.stabLvlT (V.moveOfT d), fun N hN => ?_⟩
      simp only [gwtAll, evtAll, dif_pos e]
      rw [eq_of_heq (cast_heq _ x)]
      letI := S.finAT (V.moveOfT d) x (castHpt e h)
      have hcard : (V.cellEvtT d x c (castHpt e h) N).card
          = ∑ a ∈ Finset.univ.filter
              (fun a : S.AssignT (V.moveOfT d) x (castHpt e h) =>
                V.cellOfAT d x (castHpt e h) a = c),
              (V.evtOfT (V.moveOfT d) x (castHpt e h) a N).card := by
        unfold CtsMeasured.cellEvtT
        exact Finset.card_biUnion
          (fun a _ b _ hab => V.evt_disj_assignT _ x _ a b hab N)
      rw [hcard]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ =>
        V.evt_cardT (V.moveOfT d) x (castHpt e h) a hq hzc N hN)]
      rw [Finset.sum_congr rfl (fun a _ => by
        rw [X.w.wT_eq (V.moveOfT d) x (castHpt e h) a (V.pools_sub hq) hzc])]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcnt : ((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ)
          = (V.cntcT d x c (castHpt e h) : ℚ) :=
        cp.countT d c x hzc hq (castHpt e h) hmm
      have hcnt' : (((cp.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ)
          = ((Finset.univ.filter
              (fun a : S.AssignT (V.moveOfT d) x (castHpt e h) =>
                V.cellOfAT d x (castHpt e h) a = c)).card : ℝ) := by
        rw [hcnt]; norm_cast
      rw [hcnt']
      ring

/-- TV-E4(a) [LedgerIV group (3), part1]: the guarded unit-mass cell
partition (verbatim `MovesS.LedgerIV.part1` at measuredOf). -/
theorem measuredOf_part1 {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ e ∈ Finset.Icc 1 n, ∀ (τ : (ctsTable C hfin).State e)
      (x : (measuredOf V X cp hfin).Rep e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      ∑ c : (measuredOf V X cp hfin).Cell e τ,
        (measuredOf V X cp hfin).μcell e τ x c q₀ = 1 := by
  sorry

/-- TV-E4(b) [LedgerIV group (4), rep_indep]: the row value is the cell-fiber
mass sum at EVERY representative (verbatim `MovesS.LedgerIV.rep_indep` at
measuredOf; near-rfl at the TV-E2 rowVal definition + rep_row). -/
theorem measuredOf_rep_indep {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (o : (ctsTable C hfin).Out e τ)
      (x : (measuredOf V X cp hfin).Rep e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      (measuredOf V X cp hfin).rowVal e τ o q₀
        = ∑ c ∈ (measuredOf V X cp hfin).cells e τ o,
            (measuredOf V X cp hfin).μcell e τ x c q₀ := by
  intro e τ o x q₀ hq hact
  -- rowVal IS the cell-fiber μcell sum by definition (μcell x-free); the two
  -- Set.toFinset instances agree up to Finset.sum_congr.
  show rowValOf V X.w cp hfin τ o q₀ = _
  unfold rowValOf MovesS.MeasuredSide.cells
  exact Finset.sum_congr (Set.toFinset_congr rfl) (fun _ _ => rfl)

/-- TV-E4(c) [LedgerIV group (5), meas_card]: counting-native measurement —
the fixed-height weight times |Box| is eventually the event cardinality
(verbatim `MovesS.LedgerIV.meas_card` at measuredOf; V.evt_card at
N ≥ stabLvl + box_card). -/
theorem measuredOf_meas_card {n : ℕ} {C : CtsFamily n} {S : StepSys n}
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
      (measuredOf V X cp hfin).activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
      (measuredOf V X cp hfin).gwt e τ c h q₀
          * (Fintype.card ((measuredOf V X cp hfin).Box q₀ N) : ℝ)
        = (((measuredOf V X cp hfin).cellEvt e τ x c h q₀ N).card : ℝ) := by
  intro e τ x c h hmem q₀ hq hact
  obtain ⟨N₀, hN⟩ := evtAll_card V X cp hq (x q₀ hq).1 (x q₀ hq).2
    (toCellAll V hfin τ c) h hmem
  refine ⟨N₀, fun N hNN => ?_⟩
  have hev : (measuredOf V X cp hfin).cellEvt e τ x c h q₀ N
      = evtAll V ((x q₀ hq).1) N (toCellAll V hfin τ c) h := by
    show (if hq' : q₀ ∈ V.Pools then
        evtAll V ((x q₀ hq').1) N (toCellAll V hfin τ c) h else ∅) = _
    rw [dif_pos (show q₀ ∈ V.Pools from hq)]
  rw [hev]
  exact hN N hNN

end LeanUrat.MovesV
