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
= its row + hfin (see the file-header statement record). -/
theorem ledgerIV_inst_assembly {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.LedgerIV T M) := by
  -- [PROVER RECORD, 2026-07-30 — BLOCKED on exactly ONE law: LedgerIV group
  -- (9) `comp_once` needs the named hypothesis `hdom : EntDomOrder0 V`
  -- (see the TV-E6(d) record — the file-header-anticipated fence event; the
  -- certificates for hEU's census-constancy clause are not mintable from
  -- this row).  ALL OTHER LedgerIV fields are PROVED at (ctsTable,
  -- measuredOf): groups (1)-(2) TV-E3 (xhd_sum/no_stray/no_orphan/d4r0),
  -- (3)-(5) TV-E4 (part1/rep_indep/meas_card), (6)-(7) TV-E5b
  -- (kstep_one/hmc/act_target via the PROVED TV-E5a bridge), (8) TV-E6
  -- (init_agg/init_count/ent_count_card).  The TablePins conjunct
  -- (ctsTable_pins) and the |Box| tie (rfl at Box := V.Box) are proved.
  -- Once the orchestrator ratifies the hdom row addition, this assembly is
  -- mechanical: ⟨ctsTable C hfin, measuredOf V X cp hfin, ctsTable_pins C
  -- hfin, fun _ _ _ _ => rfl-genre card tie, ⟨{ xhd_sum := measuredOf_xhd_sum
  -- V X cp hVA hHMC hb hc hd hEC hEU hfin, … , comp_once := (the hdom-fed
  -- leg) }⟩⟩.  Honest sorry per the campaign discipline; do NOT swap in a
  -- degenerate-entrance hybrid M (it would break the Q5 SHARED witness the
  -- F-cluster's laws are proved over and gut the ledger's entrance content —
  -- the M4 vacuous-seam lesson).
  sorry

end LeanUrat.MovesV
