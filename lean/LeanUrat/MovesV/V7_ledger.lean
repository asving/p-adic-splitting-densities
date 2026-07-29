/-  MovesV unit V7-1 `ctsm_ledger` — THE PER-CLAUSE HYPOTHESIS LEDGER as ONE
    record: data (C, S, V, TE, X, cp, cc, RB, hK per REV 7 C9) + the named
    burden Props, each typed to its §3 unit statement.  (v) rides as the
    OPEN kernel: NO HMC-typed conclusion field exists — every displayed
    consumer takes HMC as an explicit ANTECEDENT.  [E-PHASE FORM: the
    stage_laws field is V7-3d's abstract-T form; T/M/RB/hK ride as DATA
    pinned to the V7-3a/4 instances at assembly — MANIFEST deviations.] -/
import LeanUrat.MovesV.V7_stageLaw
import LeanUrat.MovesV.V5_comphA
import LeanUrat.MovesV.V3_entu
import LeanUrat.MovesV.V2_valA
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V4_agree

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

structure CtsmLedger (n : ℕ) where
  C : CtsFamily n
  S : StepSys n
  V : CtsMeasured n C S
  TE : TmplEvents n S
  X : XHD n S TE V
  cp : CellPolyPack n C S V
  cc : CompCarrier V TE
  J : JCells n C S V
  hTie : MDomTie V TE X.d
  hMark : MarkFiberTie TE
  -- M2 (round-4 ratification verdict, 2026-07-29): the REALIZATION-
  -- COMPLETENESS row — tmark surjectivity onto `Chains` (owner XHD/[2b]).
  -- A LEDGER FIELD (mirroring hMark): the row has content (the coupling toy
  -- exhibits `0 < chainCount` with `Tgam = 0`, so no unconditional proof
  -- exists) and the capstone's `ValB_Stmt` is now Tgam-keyed through it.
  hRC : RealizationComplete TE
  pack : C15Pack n S
  hVA : ValA n C S V
  hEC : EntCount V
  hEU : EntU V
  hAff : AffEnt n
  -- the seam-side data (pinned to the V7-3a/V7-4 instances at assembly):
  T : MovesS.TableShape n
  M : MovesS.MeasuredSide T
  RB : MovesS.RatBurdens T M
  hK : ∀ e, e ∈ Finset.Icc 1 n → MovesS.KmatHyp T e
  scs : MovesS.SCSData T
  stage_laws : StageLawBurden n T scs

/-- notational projections. -/
def CtsmLedger.D {n : ℕ} (L : CtsmLedger n) : XHDd n L.S L.TE := L.X.d

end LeanUrat.MovesV
