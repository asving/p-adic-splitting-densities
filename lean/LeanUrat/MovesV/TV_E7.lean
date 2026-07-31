/-  TV-E7 (BRIDGE BP3, cluster c4; E-phase skeleton) — THE ASSEMBLY:
    `ledgerIV_inst` proved at (T, M) := (ctsTable, measuredOf).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E7).
    deps: TV-E3, TV-E4, TV-E5b, TV-E6.  Consumers: TV-F6 (the combined seam
    producer `measured_seam`), TV-E8 (non-vacuity gate).
    Sketch: T := ctsTable C hfin (TablePins conjunct = ctsTable_pins, the
    proved tableShape_inst bundle restated); the guarded |Box| tie = rfl-
    genre at the Box := V.Box pin (measuredOf_box); bundle the TV-E3/E4/
    E5b/E6 law groups into `Nonempty (LedgerIV T M)`.
    STATEMENT RECORD (boundary honesty, flagged for ratification):
    (i) the conclusion below is BYTE-IDENTICAL to `ledgerIV_inst`
        (V7_livC:61-65); the hypothesis row is ledgerIV_inst's row PLUS the
        ONE named warranted addition `hfin : Finite (Skeleton n)` —
        `tableShape_inst`'s own hypothesis (V7_ts:70), without which no
        TablePins witness is constructible in-corpus (Skeleton-finiteness
        is proved only at n = 1 (V1_witnessC) and n = 3 (V2_skeleton)).
        Whether `ledgerIV_inst` itself gains `hfin`, or per-n finiteness
        instances discharge it, is an execution-time ratification item
        (statement fence — surfaced here, not improvised).
    (ii) the eventual sorry-fill of `ledgerIV_inst` IN V7_livC.lean (module
        sorry-free + the docstring pin-inventory update from the compiled
        witness, per the V7_livC closing instruction) is an EDIT TO AN
        EXISTING FILE — orchestrator/prover-phase duty, NOT performed at
        E-phase (new-files-only rule); this theorem is the proof's home. -/
import LeanUrat.MovesV.TV_E3
import LeanUrat.MovesV.TV_E4
import LeanUrat.MovesV.TV_E5b
import LeanUrat.MovesV.TV_E6

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-E7: `ledgerIV_inst`'s ∃-bundled duty PROVED at the real (Q5-shared)
witness — ∃ (T, M), TablePins C T ∧ (the guarded |Box| card tie) ∧
Nonempty (LedgerIV T M), with T := ctsTable C hfin and M := measuredOf
V X cp hfin.  Conclusion byte-identical to V7_livC's `ledgerIV_inst`; row
= its row + hfin (see the file-header statement record).
[QUEUE ITEM 11 EXECUTED, 2026-07-31 (Asvin sign-off; ledger
lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 11): the ratified
`hdom : EntDomOrder0 V` row addition landed (here, TV_E6's comp_once, and
V7_livC's `ledgerIV_inst`); the 2026-07-30 blocked record (one law short —
comp_once's hdom) is RESOLVED and the recorded mechanical assembly is
executed below at the SHARED witness, exactly as sketched.  V7_livC's own
sorry still stands behind the hfin ratification item of this file's
header (its row has no `hfin`), see the record there.] -/
theorem ledgerIV_inst_assembly {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hdom : EntDomOrder0 V)
    (hfin : Finite (Skeleton n)) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.LedgerIV T M) :=
  ⟨ctsTable C hfin, measuredOf V X cp hfin, ctsTable_pins C hfin,
    fun _ _ _ _ => rfl,
    ⟨{ xhd_sum := measuredOf_xhd_sum V X cp hVA hHMC hb hc hd hEC hEU hfin
       xhd_no_stray := measuredOf_xhd_no_stray V X cp hVA hHMC hb hc hd hEC hEU hfin
       xhd_no_orphan := measuredOf_xhd_no_orphan V X cp hVA hHMC hb hc hd hEC hEU hfin
       d4r0 := measuredOf_d4r0 V X cp hVA hHMC hb hc hd hEC hEU hfin
       part1 := measuredOf_part1 V X cp hVA hHMC hb hc hd hEC hEU hfin
       rep_indep := measuredOf_rep_indep V X cp hVA hHMC hb hc hd hEC hEU hfin
       meas_card := measuredOf_meas_card V X cp hVA hHMC hb hc hd hEC hEU hfin
       kstep_one := measuredOf_kstep_one V X cp hVA hHMC hb hc hd hEC hEU hfin
       hmc := measuredOf_hmc V X cp hVA hHMC hb hc hd hEC hEU hfin
       act_target := measuredOf_act_target V X cp hVA hHMC hb hc hd hEC hEU hfin
       init_agg := measuredOf_init_agg V X cp hVA hHMC hb hc hd hEC hEU hfin
       init_count := measuredOf_init_count V X cp hVA hHMC hb hc hd hEC hEU hfin
       ent_count_card := measuredOf_ent_count_card V X cp hVA hHMC hb hc hd hEC hEU hfin
       comp_once := measuredOf_comp_once V X cp hVA hHMC hb hc hd hEC hEU hdom hfin }⟩⟩

end LeanUrat.MovesV
