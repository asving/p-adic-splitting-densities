/-  TV-F5 (BRIDGE BP3, cluster c5; E-phase skeleton) — jcell_sum + ASSEMBLY:
    `ratBurdens_exists` discharged at the shared measuredOf witness.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-F5).
    deps: TV-F1 (packs), TV-F2 (coherence incl. the jcell_sum gate
    deliverable — pre-checked candidate), TV-F3 (degree ties), TV-F4 (cellP
    laws).  Consumers: TV-F6 (the combined seam producer).

    NOTE (no-existing-file rule, the TV_G3 precedent): the sorried duty
    `ratBurdens_exists` (V7_rbC.lean:52) is byte-identical in statement to
    `ratBurdens_exists_pack` below; the prover fills the V7_rbC sorry from
    this pack (or inlines the same proof there) — that fill is the ONLY edit
    to the existing file, made at prover phase.  This file adds the producer,
    it does not touch the existing declaration.

    PROVER DUTIES (the blueprint's own wording, recorded):
    (i) jcell_sum: jP is DEFINED as the cell sum at split routes (co-design
      with F1; `SeamCoherent.jcell_sum` is the pre-checked candidate — the
      F2 gate ran before this prover).
    (ii) "verify no E-only premise leaked": the pack's row below is
      BYTE-IDENTICAL to `ratBurdens_exists`'s (no `hdom : EntDomOrder0 V`).
      The seam ∃s (TV-F2/F3/F4) carry hdom on the ι-leg (TV-F1's iotaPGof
      requires it); if hdom cannot be discharged from this row at the
      witness, the exit is ESCALATION (named-hypothesis addition on the
      pack, flagged for ratification) — never a forced proof and never a
      silent row change on the existing V7_rbC statement. -/
import LeanUrat.MovesV.TV_F4

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.MovesV

/-- TV-F5 CONDITIONAL ASSEMBLY: the three seam bundles re-package into
`MovesS.RatBurdens` at the packs (tgP := seamTgP, jP := seamJP,
ιP := seamIotaP, jPCell := seamJPCell, cellP := seamCellP).  Pure
re-packaging: value/ok laws from `SeamCoherent`, degree ties from
`SeamDegreeLaws`, the cellP roster from `SeamCellLaws`, ι_countS_one from
the PROVED `seamIotaP_countS_one` (TV-F3), jcell_sum from
`SeamCoherent.jcell_sum`. -/
theorem ratBurdens_of_seam {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} (X : XHD n S TE V)
    (cp : CellPolyPack n C S V) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (hdom : EntDomOrder0 V)
    {T : MovesS.TableShape n} {M : MovesS.MeasuredSide T}
    (K : SeamKeys V T M)
    (hco : SeamCoherent V X cp J hEU hEC hA hdom K)
    (hdeg : SeamDegreeLaws V X cp J hEU hEC hA hdom K)
    (hcell : SeamCellLaws cp K) :
    Nonempty (MovesS.RatBurdens T M) := by
  sorry

/-- TV-F5 ASSEMBLY: the `ratBurdens_exists` producer — statement
byte-identical to the named open duty at MovesV/V7_rbC.lean:42-51 (premise
row verbatim; conclusion ∃ T M, TablePins ∧ guarded |Box| card tie ∧
Nonempty (RatBurdens T M)).  Proof sketch: eliminate TV-F4's cumulative
`seam_cell_exists` (discharging its extra hdom premise from this row or
escalating — duty (ii) in the header) and apply `ratBurdens_of_seam`; the
witness is the SHARED measuredOf (T, M) — TV-F6 certifies the sharing with
the LedgerIV side. -/
theorem ratBurdens_exists_pack {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hTie : MDomTie V TE X.d) (J : JCells n C S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.RatBurdens T M) := by
  sorry

end LeanUrat.MovesV
