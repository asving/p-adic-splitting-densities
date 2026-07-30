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

namespace LeanUrat.MovesV

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
  sorry

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
  sorry

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
  sorry

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
