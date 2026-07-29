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

/-- NAMED OPEN INSTANTIATION DUTY (M4): a table shape from the CTS family
carrying the full (SCS) stage-data supply. -/
theorem scs_data_supply {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n, Nonempty (MovesS.SCSData T) := by
  sorry

end LeanUrat.MovesV
