/-  MovesV unit V7-6a1 `ledgerIV_cells` (RE-SPLIT REV 4, G-2; MarkDisj
    premises REMOVED REV 7, C8) — THE CELL SUITE: meas_card / xhd_no_stray /
    xhd_no_orphan (three legs) at the instance, GIVEN V + X(dC) + cp. -/
import LeanUrat.MovesV.V7_msC

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ledgerIV_cells {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (d : MoveData n C) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (hmem : (V.cdom d c).Mem h) :
    ∃ N₀, ∀ N ≥ N₀, (V.cellEvt d x c h N).Nonempty := by
  refine ⟨V.stabLvl (V.moveOf d), fun N hN => ?_⟩
  -- h ∈ HDom ⇒ the cell-refined count is positive, so the assignment filter is nonempty.
  have hcnt : 0 < V.cntc d x c h := X.dC.no_strayC d c h hmem hq x hzc
  unfold CtsMeasured.cntc at hcnt
  rw [Finset.card_pos] at hcnt
  obtain ⟨a₀, ha₀⟩ := hcnt
  -- q₀ > 0 (pools are prime powers > 1).
  have hq0 : (0 : ℝ) < (q₀ : ℝ) := by
    have h1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
    have : (0 : ℚ) < q₀ := lt_trans one_pos h1
    exact_mod_cast this
  -- the per-assignment mass is a positive power of q₀.
  have hmass : 0 < S.massOf (V.moveOf d) x h a₀ := by
    rw [X.w.w_eq (V.moveOf d) x h a₀ (V.pools_sub hq) hzc]
    exact zpow_pos hq0 _
  -- the box count is positive.
  have hboxN : 0 < @Fintype.card _ (V.finB q₀ N) :=
    (@Fintype.card_pos_iff _ (V.finB q₀ N)).mpr (V.boxpos q₀ N)
  have hboxR : (0 : ℝ) < ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ) := by exact_mod_cast hboxN
  -- hence the assignment's level-N event is nonempty for N ≥ stabLvl.
  have hev : ((V.evtOf (V.moveOf d) x h a₀ N).card : ℝ)
      = S.massOf (V.moveOf d) x h a₀ * ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ) :=
    V.evt_card (V.moveOf d) x h a₀ hq hzc N hN
  have hcardR : (0 : ℝ) < ((V.evtOf (V.moveOf d) x h a₀ N).card : ℝ) := by
    rw [hev]; exact mul_pos hmass hboxR
  have hcardN : 0 < (V.evtOf (V.moveOf d) x h a₀ N).card := by exact_mod_cast hcardR
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcardN
  unfold CtsMeasured.cellEvt
  exact ⟨y, Finset.mem_biUnion.mpr ⟨a₀, ha₀, hy⟩⟩

theorem ledgerIV_orphan {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (d : MoveData n C) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) (c : V.DCellO d.s d.m d.o d.α)
    (h : Hpt (S.dim (V.moveOf d))) (hout : ¬ (V.cdom d c).Mem h) (N : ℕ) :
    V.cellEvt d x c h N = ∅ := by
  -- h ∉ HDom ⇒ (contrapositive of no_orphanC) the cell-refined count is zero,
  -- so the assignment filter is empty and the biUnion collapses.
  have hnp : ¬ (0 < V.cntc d x c h) := fun hp =>
    hout (X.dC.no_orphanC d x c h hq hzc hp)
  have hz : V.cntc d x c h = 0 := Nat.le_zero.mp (not_lt.mp hnp)
  unfold CtsMeasured.cntc at hz
  have hfilt := Finset.card_eq_zero.mp hz
  unfold CtsMeasured.cellEvt
  rw [hfilt, Finset.biUnion_empty]

end LeanUrat.MovesV
