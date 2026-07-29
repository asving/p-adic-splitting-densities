/-  MovesV unit V7-6c `ledgerIV_inst` — THE ASSEMBLY: MovesS.LedgerIV,
    theorem-under-hypotheses (XHD + cp + hVA + HMC-tagged legs + PART-1 legs
    + ENT-COUNT + (ENT-U) — the ledger's own tags, verbatim).
    M4 SOUNDNESS REPAIR (ratification verdict, 2026-07-29): the E-phase
    `Nonempty (…) ∨ True` escape (discharged by `Or.inr trivial` — a
    propositionally vacuous seam) is DELETED.  The honest statement is the
    ∃-bundled instantiation duty below, left as a NAMED OPEN SORRY: the
    Phase-B witness must be the V7-3a table + the V7-4 measured side built
    from THESE CTS objects (real cells, real events, real masses — the
    degenerate all-inactive witness does NOT discharge the duty; MANIFEST
    record).  NOTE the deliberate quantifier repair: concluding
    `Nonempty (LedgerIV T M)` for the ARBITRARY (T, M) arguments of the old
    statement would be FALSE (adversarial M breaks part1), i.e. the exact
    M1 failure mode — the ∃-form is the strongest sorry-safe statement. -/
import LeanUrat.MovesV.V7_livB
import LeanUrat.MovesV.V4_part1C

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- NAMED OPEN INSTANTIATION DUTY (M4): a table shape and measured side
carrying the full `MovesS.LedgerIV` law suite, to be built from the bound
CTS system (V7-3a/V7-4 seam instances). -/
theorem ledgerIV_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      Nonempty (MovesS.LedgerIV T M) := by
  sorry

end LeanUrat.MovesV
