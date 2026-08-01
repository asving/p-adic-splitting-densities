/-  Scaffold/HDischarge/H4/AxChk.lean — unit **H4-L9** (HDISCHARGE_H4.md §L.4, MECH).

    Axiom census for the H4 Lean statement layer, per the `AxChk_baseline`
    discipline: one `#print axioms` line for EVERY L-unit declaration of
    §L.1 (`Defs.lean` — units H4-L1/L2/L7), §L.2 (`Kernel.lean` — units
    H4-L3/L4/L5/L8), and §L.3 (`TypedFaces.lean` — unit H4-L6). Explicit
    finite list, no wildcard. Standalone; NOT imported by anything.

    Gate: `lake env lean LeanUrat/Scaffold/HDischarge/H4/AxChk.lean`.
    Acceptance bar: Lean core only (`propext`, `Classical.choice`,
    `Quot.sound`) — or "does not depend on any axioms" — for every row;
    any other axiom in the footprint is a stop-the-line regression.  -/
import LeanUrat.Scaffold.HDischarge.H4.Defs
import LeanUrat.Scaffold.HDischarge.H4.Kernel
import LeanUrat.Scaffold.HDischarge.H4.TypedFaces

-- §L.1 `Defs.lean` — unit H4-L1 (shared shape/skeleton defs)
#print axioms LeanUrat.Scaffold.HDischarge.H4.StageTuple
#print axioms LeanUrat.Scaffold.HDischarge.H4.StageTuple.Bez
#print axioms LeanUrat.Scaffold.HDischarge.H4.wSet
#print axioms LeanUrat.Scaffold.HDischarge.H4.anchorSlot
#print axioms LeanUrat.Scaffold.HDischarge.H4.slotHeight
#print axioms LeanUrat.Scaffold.HDischarge.H4.attainIdx
#print axioms LeanUrat.Scaffold.HDischarge.H4.SlotTree
#print axioms LeanUrat.Scaffold.HDischarge.H4.SlotTree.dimOf

-- §L.1 `Defs.lean` — unit H4-L2 (`LedgerSkel`)
#print axioms LeanUrat.Scaffold.HDischarge.H4.LedgerSkel

-- §L.1 `Defs.lean` — unit H4-L7 (`RealizedLedger`)
#print axioms LeanUrat.Scaffold.HDischarge.H4.RealizedLedger

-- §L.2 `Kernel.lean` — unit H4-L3
#print axioms LeanUrat.Scaffold.HDischarge.H4.SlotTree.dimOf_scale

-- §L.2 `Kernel.lean` — unit H4-L4
#print axioms LeanUrat.Scaffold.HDischarge.H4.eq2_dim_of_skel

-- §L.2 `Kernel.lean` — unit H4-L5
#print axioms LeanUrat.Scaffold.HDischarge.H4.eq2law_of_skel

-- §L.2 `Kernel.lean` — unit H4-L8 (+ its two typed faces)
#print axioms LeanUrat.Scaffold.HDischarge.H4.UBXbStmt
#print axioms LeanUrat.Scaffold.HDischarge.H4.K3deltaStmt
#print axioms LeanUrat.Scaffold.HDischarge.H4.k3delta_of_ubxb

-- §L.3 `TypedFaces.lean` — unit H4-L6
#print axioms LeanUrat.Scaffold.HDischarge.H4.H4aConsumptionFace
