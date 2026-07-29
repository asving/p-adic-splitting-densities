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

/-- NAMED OPEN INSTANTIATION DUTY (M4; pins RESTATED at the ROUND-4 M1
repair, 2026-07-29 — the verdict: the old record claimed the pins "exclude
every degenerate unrelated witness", which its clauses did not deliver).
EXACT PIN INVENTORY (boundary-record rule — what this statement ties, and
what it does NOT):
TIED, table side (option (a), STRENGTHENED — `TablePins C T`, V7-3a):
`VType ≃ VLabel n`; per-block `State e ≃ StateOf n C e` (the carrier now
CARRIES the CTS `CellIdx`); `Wstate`/`Wloc` transport the REAL CTS degree
bounds; per-(e,τ) `Out ≃ Σ letter, outcome`; the odata member lists tied
to the `omem` rosters in (size, δ, status-with-target-skeleton).
`tableShape_inst` PROVES `TablePins` at its compiled witness.
TIED, measured side: ONLY the |Box| CARDINALITY at V's pools, guarded on
V-box nonemptiness (unguarded it would collide with `MeasuredSide.boxpos`
at an adversarial empty-box V).
NOT TIED (option (b), SCOPED — this record makes no stronger claim):
`M.Pools`, `M.Cell`/cells, `M.cellEvt`/events, `M.μcell`/masses, `M.rowVal`
rows, `M.EntShape`/entrances, marked values, and the witness's identity
with `tableShape_inst`'s result; on the table side, the target CELL INDEX
inside a continuing member's status payload.  A witness satisfying the
pins can still carry degenerate measured-side data (e.g. `Cell := PEmpty`,
`μcell := 0`) — the pins CONSTRAIN the witness, they do not determine it.
FENCE-RULE RECORD (why the M-side stays card-level): hard structure ties
(M.Pools = V.Pools, M.Box ≃ V.Box, mass ties) could make the ∃ FALSE for
adversarial V against `MeasuredSide`'s own pool/box laws — the M1 failure
mode; Phase B discharges the duty with the real V7-4 field map (~30
fields; Box := V.Box, cells := the DCellO fibers, cellEvt := V.cellEvt,
μcell := μcellH) + the LedgerIV suite from X/cp/hVA + part1/part2 (the
xhd_sum leg IS V0-3 + cp.count; part1 IS the supplied `hb`/`hc`/`hd`
route), after which the pins can be strengthened FROM the compiled
witness. -/
theorem ledgerIV_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) :
    ∃ (T : MovesS.TableShape n) (M : MovesS.MeasuredSide T),
      TablePins C T ∧
      (∀ q₀ ∈ V.Pools, ∀ N : ℕ, Nonempty (V.Box q₀ N) →
        Fintype.card (M.Box q₀ N) = @Fintype.card _ (V.finB q₀ N)) ∧
      Nonempty (MovesS.LedgerIV T M) := by
  sorry

end LeanUrat.MovesV
