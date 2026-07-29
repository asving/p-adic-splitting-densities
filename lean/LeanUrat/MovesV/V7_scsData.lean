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

/-- NAMED OPEN INSTANTIATION DUTY (M4; WITNESS-PINNED at the final-
ratification M-seam repair, 2026-07-29 — the verdict: "the existential
conclusions do not state that their witnesses are the table … constructed
from the supplied `C`"): a table shape carrying the full (SCS) stage-data
supply WHOSE CARRIERS ARE THE CTS ONES — the pin clauses (verdict-typed:
`VType ≃ VLabel n`, per-block `State e ≃ StateOf n e`) exclude every
degenerate unrelated witness; the V7-3a construction satisfies them
(`tableShape_inst`: State := StateOf, vEquiv over VLabel).
INSTANTIATION ATTEMPT (recorded): a trivial stage supply (ℓ = g = μsel = 1,
flanks 0, W = e, D = 1) discharges the algebraic laws but FAILS
`sel_continuing`/`cluster_child` against the CTS `odata` (the selected
member's continuing flag and size `W′·D′` are the REAL species stage
fields, not free data) — the honest witness is the MovesSp stage-field
wiring over `tableShape_inst`'s roster, the V7-3c Phase-B unit.  Hard
M-side ties were NOT baked in (fence-rule record: for adversarial `C` they
could make the ∃ false — the M1 failure mode). -/
theorem scs_data_supply {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      Nonempty (T.VType ≃ VLabel n) ∧
      (∀ e, Nonempty (T.State e ≃ StateOf n e)) ∧
      Nonempty (MovesS.SCSData T) := by
  sorry

end LeanUrat.MovesV
