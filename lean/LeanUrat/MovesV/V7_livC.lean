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
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- NAMED OPEN INSTANTIATION DUTY (M4; WITNESS-PINNED at the final-
ratification M-seam repair, 2026-07-29 — the verdict: "the existential
conclusions do not state that their witnesses are the table and measured
system constructed from the supplied `C`, `V`, or `X` … the existential
sorry duties can be witnessed by systems unrelated to the CTS objects
unless explicit equivalences and field ties are added"): the ∃ now pins
the TABLE side to the CTS carriers (`VType ≃ VLabel n`, per-block
`State e ≃ StateOf n e` — satisfied by `tableShape_inst`) and pins the
measured side's box CARDINALITIES to V's boxes at V's pools (the |Box|
tie, card-level and GUARDED on V-box nonemptiness — unguarded it would
collide with `MeasuredSide.boxpos` at an adversarial empty-box V).
INSTANTIATION ATTEMPT (recorded): the MeasuredSide over V (Box := V.Box,
cells := the DCellO fibers, cellEvt := V.cellEvt, μcell := μcellH) needs
the full V7-4 field map (~30 fields) + the LedgerIV suite discharged from
X/cp/hVA + part1/part2 (the xhd_sum leg IS V0-3 + cp.count; part1 IS the
supplied `hb`/`hc`/`hd` route) — a dedicated instance unit, not
completable inline; stays the named sorried duty.  Hard M-side STRUCTURE
ties (M.Pools = V.Pools, M.Box ≃ V.Box) were NOT baked in (fence-rule
record: MeasuredSide's own pool/box laws could make them false for
adversarial V — the M1 failure mode). -/
theorem ledgerIV_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      Nonempty (T.VType ≃ VLabel n) ∧
      (∀ e, Nonempty (T.State e ≃ StateOf n e)) ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.LedgerIV T M) := by
  sorry

end LeanUrat.MovesV
