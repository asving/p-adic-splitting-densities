/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG9_m4bConst
import LeanUrat.MovesU.SlotsG10_jcInvHist

/-!
# IB-G12 — CLOSURE MANIFEST for the thirteen-slot family (bridge campaign BP1,
cluster c12; doc unit — PARTIAL, see the pending record below)

Blueprint: `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 closing
paragraph + §4 group G (IB-G12): "closure manifest (identifier → decl table,
grep-verified)" — the standing CLOSURE MANIFEST rule from wave-4 round 7:
every identifier in each displayed slot Prop resolves to a BUILT declaration
(no phantom vocabulary).  This file makes the manifest COMPILED: each row is a
`#check` against the fully-qualified name, so the closure claim is re-verified
by every build (strictly stronger than a grep).

## The table (slot Prop → identifiers → built decl path)

`Slot_m4bConst` (SlotsG9_m4bConst.lean):
| identifier | built decl (file) |
|---|---|
| `MovesV.CtsFamily` | LeanUrat/MovesV/Defs.lean:292 |
| `MovesV.StepSys` (+ `.Cell`) | LeanUrat/MovesV/Defs.lean:81 |
| `MovesV.CtsMeasured` (fields `entDom`/`entLands`; `Pools` via `CtsCells`) | MovesV/Defs.lean:792 |
| `MovesV.EntTemplate` (+ `.entDim`) | LeanUrat/MovesV/Defs.lean:498/536 |
| `MovesV.LinSet` (+ `.Mem`) | LeanUrat/MovesV/Defs.lean:57/61 |
| `MovesV.SemilinPart.comps` | LeanUrat/MovesV/Defs.lean:66 |
| `MovesV.Hpt` | LeanUrat/MovesV/Defs.lean:30 |
| `MovesV.Order0Perimeter` | LeanUrat/MovesV/V3_spwordD.lean:118 |
| `MovesV.CtsMeasured.instCensus` | LeanUrat/MovesV/Defs.lean:953 |
| `MovesV.CtsMeasured.instRealizable` | LeanUrat/MovesV/Defs.lean:956 |

`Slot_jcInvHist` + `NodeRetainedKeyEq` (SlotsG10_jcInvHist.lean):
| identifier | built decl (file) |
|---|---|
| `MovesC.Node` (+ fields species/e/g/μ/a/s0/wSide/Dwidth/σ) | LeanUrat/MovesC/Defs.lean:361 |
| `Moves.Stage` (`.K`, via `ν.σ.K`) | LeanUrat/Moves/Defs.lean:106 |
| `MovesC.History` (`.lastNode` def'd in MovesT) | MovesC/Defs.lean · MovesT/Defs.lean:402 |
| `MovesD.CanonPolicy` | LeanUrat/MovesD/Defs.lean:356 |
| `MovesD.TreeModel` | LeanUrat/MovesD/Defs.lean:630 |
| `MovesT.CellData` (+ `.Cell`) | LeanUrat/MovesT/Defs.lean:335 |
| `MovesT.EntSt` (`.st`) | LeanUrat/MovesT/Defs.lean:305 |
| `MovesT.entEvent` | LeanUrat/MovesT/Defs.lean:311 |
| `MovesT.cellEventE` | LeanUrat/MovesT/Defs.lean:396 |
| `Nat.card`, `Set.Nonempty` | Mathlib |

PENDING ROWS (recorded; not writable at 2026-07-30, cluster c12): the eleven
sibling-cluster slots (Slot_rel1, Slot_rel2a/b/d/e, Slot_rel3 — IB-G2/G3;
Slot_rs0Lump — IB-G4; Slot_trackRule — IB-G5; Slot_dnLattice — IB-G6;
Slot_m1m5Echo — IB-G7; Slot_x1aDict — IB-G8) are not on disk; their manifest
rows go in a NEW follow-up file once they land (new-files-only discipline).
ORCHESTRATOR NOTE (duty, not done here): MANIFEST.json's BRIDGE section
(blueprint §7 file-level acceptance) is an existing-file edit — orchestrator
wires it.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

section ClosureManifest

-- Slot_m4bConst's vocabulary resolves (compiled closure rows):
#check @LeanUrat.MovesV.CtsFamily
#check @LeanUrat.MovesV.StepSys
#check @LeanUrat.MovesV.StepSys.Cell
#check @LeanUrat.MovesV.CtsMeasured
#check @LeanUrat.MovesV.CtsMeasured.entDom
#check @LeanUrat.MovesV.CtsMeasured.entLands
#check @LeanUrat.MovesV.EntTemplate
#check @LeanUrat.MovesV.EntTemplate.entDim
#check @LeanUrat.MovesV.LinSet
#check @LeanUrat.MovesV.LinSet.Mem
#check @LeanUrat.MovesV.SemilinPart.comps
#check @LeanUrat.MovesV.Hpt
#check @LeanUrat.MovesV.Order0Perimeter
#check @LeanUrat.MovesV.CtsMeasured.instCensus
#check @LeanUrat.MovesV.CtsMeasured.instRealizable
#check @LeanUrat.MovesU.Slot_m4bConst

-- Slot_jcInvHist's vocabulary resolves (compiled closure rows):
#check @LeanUrat.MovesC.Node
#check @LeanUrat.MovesC.Node.species
#check @LeanUrat.MovesC.Node.e
#check @LeanUrat.MovesC.Node.g
#check @LeanUrat.MovesC.Node.μ
#check @LeanUrat.MovesC.Node.a
#check @LeanUrat.MovesC.Node.s0
#check @LeanUrat.MovesC.Node.wSide
#check @LeanUrat.MovesC.Node.Dwidth
#check @LeanUrat.MovesC.Node.σ
#check @LeanUrat.MovesC.History.lastNode
#check @LeanUrat.MovesD.CanonPolicy
#check @LeanUrat.MovesD.TreeModel
#check @LeanUrat.MovesT.CellData
#check @LeanUrat.MovesT.CellData.Cell
#check @LeanUrat.MovesT.EntSt.st
#check @LeanUrat.MovesT.entEvent
#check @LeanUrat.MovesT.cellEventE
#check @LeanUrat.MovesU.NodeRetainedKeyEq
#check @LeanUrat.MovesU.Slot_jcInvHist

end ClosureManifest

end LeanUrat.MovesU
