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

namespace LeanUrat.MovesV

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
  sorry

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
  sorry

end LeanUrat.MovesV
