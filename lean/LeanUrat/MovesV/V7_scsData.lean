/-  MovesV unit V7-3c `scs_data_supply` — the `SCSData` DATA supply from the
    MovesSp species stage fields through the roster wiring (laws decided at
    the gate rosters).
    M4 SOUNDNESS REPAIR (ratification verdict, 2026-07-29): the E-phase
    `Nonempty (…) ∨ True` escape (discharged by `Or.inr trivial` — a
    propositionally vacuous seam) is DELETED.  The honest statement is the
    ∃-bundled duty below, a NAMED OPEN SORRY: the Phase-B witness is the
    V7-3a table (`tableShape_inst`) equipped with the species stage-field
    data (W/D/ℓ/g/μsel/W′/D′ + the cluster laws) — concluding
    `Nonempty (SCSData T)` for an ARBITRARY T would be FALSE (e.g. a
    member-size law can fail), i.e. the M1 failure mode; the ∃-form is the
    strongest sorry-safe statement. -/
import LeanUrat.MovesV.V7_ts

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- NAMED OPEN INSTANTIATION DUTY (M4; pins RESTATED at the ROUND-4 M1
repair, 2026-07-29 — the old record claimed the pins "exclude every
degenerate unrelated witness"; they did not).
EXACT PIN INVENTORY (boundary-record rule):
TIED (option (a), STRENGTHENED): `TablePins C T` — `VType ≃ VLabel n`,
per-block `State e ≃ StateOf n C e` (the carrier now CARRIES the CTS
`CellIdx`), real `Wloc`/`Wstate` bound transport, per-(e,τ) Out equivs and
the odata member lists tied to the `omem` rosters in (size, δ,
status-with-target-skeleton); `tableShape_inst` PROVES `TablePins` at its
compiled witness.
NOT TIED (SCOPED): the SCSData stage fields themselves (W/D/ℓ/g/μsel/W′/D′,
flanks, resFactors, selIdx, memberOf) — the ∃ asserts only that SOME
supply exists over a pinned table; a pin-satisfying witness could carry a
wrong-but-lawful stage supply.  INSTANTIATION ATTEMPT (recorded): a
trivial stage supply (ℓ = g = μsel = 1, flanks 0, W = e, D = 1) discharges
the algebraic laws but FAILS `sel_continuing`/`cluster_child` against the
CTS `odata` (the selected member's continuing flag and size `W′·D′` are
the REAL species stage fields, not free data) — the honest witness is the
MovesSp stage-field wiring over `tableShape_inst`'s roster, the V7-3c
Phase-B unit.  FENCE-RULE RECORD: harder stage-field ties baked into the ∃
could make it FALSE for adversarial `C` (the M1 failure mode). -/
theorem scs_data_supply {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      TablePins C T ∧
      Nonempty (MovesS.SCSData T) := by
  sorry

end LeanUrat.MovesV
