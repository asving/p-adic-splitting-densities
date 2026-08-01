/-  Scaffold/HDischarge/H7/AxChk.lean — unit **H7-E1** (HDISCHARGE_H7.md §3.6, W2, MECH).

    Axiom census for the landed H7 wave, per the `AxChk_baseline` discipline:
    one `#print axioms` line for EVERY declaration landed by W0/W1a–d —
    §3.1 (`Rows.lean` — H7-A1/A2/A3), §3.2 (`Receipt.lean` — H7-B1/B2/B3),
    §3.3 (`Aggregate.lean` — H7-C1a/C1b), §3.4 (`ResTrans.lean` — H7-C2),
    §3.5 (`Order0Gate.lean` — H7-D1a/b/c + carrier defs).  Explicit finite
    list, no wildcard.  Standalone; NOT imported by anything.

    Gate: `lake env lean LeanUrat/Scaffold/HDischarge/H7/AxChk.lean`.
    Acceptance bar: Lean core only (`propext`, `Classical.choice`,
    `Quot.sound`) — or "does not depend on any axioms" — for every row;
    zero `sorryAx` at wave close; any other axiom in the footprint is a
    stop-the-line regression.  -/
import LeanUrat.Scaffold.HDischarge.H7.Rows
import LeanUrat.Scaffold.HDischarge.H7.Receipt
import LeanUrat.Scaffold.HDischarge.H7.Aggregate
import LeanUrat.Scaffold.HDischarge.H7.ResTrans
import LeanUrat.Scaffold.HDischarge.H7.Order0Gate

-- §3.1 `Rows.lean` — unit H7-A1 (`SiteDatum` + `InGuard`)
#print axioms LeanUrat.Scaffold.HDischarge.H7.SiteDatum
#print axioms LeanUrat.Scaffold.HDischarge.H7.InGuard

-- §3.1 `Rows.lean` — unit H7-A2 (`ITauShadow`)
#print axioms LeanUrat.Scaffold.HDischarge.H7.ITauShadow

-- §3.1 `Rows.lean` — unit H7-A3 (`KLocCounts`)
#print axioms LeanUrat.Scaffold.HDischarge.H7.KLocCounts

-- §3.2 `Receipt.lean` — units H7-B1/B2/B3
#print axioms LeanUrat.Scaffold.HDischarge.H7.engineSIBRow_of_rows
#print axioms LeanUrat.Scaffold.HDischarge.H7.stratum_product_law
#print axioms LeanUrat.Scaffold.HDischarge.H7.guard_read_headroom

-- §3.3 `Aggregate.lean` — units H7-C1a/C1b
#print axioms LeanUrat.Scaffold.HDischarge.H7.uniform_on_union
#print axioms LeanUrat.Scaffold.HDischarge.H7.sib_of_uniform_words

-- §3.4 `ResTrans.lean` — unit H7-C2
#print axioms LeanUrat.Scaffold.HDischarge.H7.pow_dvd_mul_iff_of_coprime_cofactor

-- §3.5 `Order0Gate.lean` — unit H7-D1a (`f1Datum` + the `Fact (Nat.Prime 5)` instance)
#print axioms LeanUrat.Scaffold.HDischarge.H7.instFactPrimeOfNatNat_leanUrat
#print axioms LeanUrat.Scaffold.HDischarge.H7.f1Datum

-- §3.5 `Order0Gate.lean` — unit H7-D1b (synthetic carriers + the interface-fit gate)
#print axioms LeanUrat.Scaffold.HDischarge.H7.f1FiberData
#print axioms LeanUrat.Scaffold.HDischarge.H7.f1Cell
#print axioms LeanUrat.Scaffold.HDischarge.H7.gate_f1_iTauShadow

-- §3.5 `Order0Gate.lean` — unit H7-D1c (guard gate)
#print axioms LeanUrat.Scaffold.HDischarge.H7.gate_f1_guard
