/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG2_relFamily
import LeanUrat.MovesU.SlotsG3_rel3
import LeanUrat.MovesU.SlotsG4_rs0Lump
import LeanUrat.MovesU.SlotsG5_trackRule
import LeanUrat.MovesU.SlotsG6_dnLattice
import LeanUrat.MovesU.SlotsG7_m1m5Echo
import LeanUrat.MovesU.SlotsG8_x1aDict

/-!
# IB-G12 follow-up — CLOSURE MANIFEST B (bridge campaign BP1, cluster
BP1-P10-slots, 2026-07-30; the NEW-FILE follow-up the G12 unit's PENDING
paragraph reserved)

Compiled closure rows (each a `#check` re-verified by every build) for the
slot Props filled by cluster BP1-P10-slots: `Slot_rel1` (SlotsG2),
`Slot_rs0Lump` (G4), `Slot_trackRule` (G5), `Slot_dnLattice` (G6),
`Slot_m1m5Echo` (G7), `Slot_x1aDict` (G8).  STILL-PENDING rows:
`Slot_rel2a/b/d/e` and `Slot_rel3` remain honest sorries (BLOCKED records in
SlotsG2/SlotsG3 — no displayed bodies, no manifest rows owed yet).
Mathlib-owned identifiers (`Nat.card`, `AddSubgroup.closure`, `Pi.single`,
`Set.ncard`, `Finset.*`, `Multiset.*`, `WithTop`, `Nat.factorial`,
`Fin.castSucc`/`succ`/`last`) are not tabled, per the G12 convention
("`Nat.card`, `Set.Nonempty` | Mathlib").
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

section ClosureManifestB

-- Slot_rel1 (SlotsG2_relFamily.lean) — the G1 carrier + the re-typed clauses:
#check @LeanUrat.MovesU.CInterface
#check @LeanUrat.MovesU.CInterface.count
#check @LeanUrat.MovesU.GradedCarrier
#check @LeanUrat.MovesU.TowerData.BaseLaws
#check @LeanUrat.MovesU.TowerData.StageCarrierLaws
#check @LeanUrat.MovesU.TowerData.ClimbLaws
#check @MovesRBase.qq
#check @MovesRBase.Fsub
#check @MovesRBase.O
#check @LeanUrat.Moves.DigitSystem.IsSolution
#check @LeanUrat.MovesC.IsUnitriangular
#check @LeanUrat.MovesC.Line.at
#check @LeanUrat.MovesC.DomData
#check @LeanUrat.MovesU.Slot_rel1

-- Slot_rs0Lump (SlotsG4_rs0Lump.lean):
#check @LeanUrat.MovesU.UCarriers
#check @LeanUrat.MovesS.verdictImage
#check @LeanUrat.MovesS.MeasuredSide.kstep
#check @LeanUrat.MovesS.MeasuredSide.activeState
#check @LeanUrat.MovesS.MeasuredSide.Pools
#check @LeanUrat.MovesS.TableShape.VType
#check @LeanUrat.MovesU.Slot_rs0Lump

-- Slot_trackRule (SlotsG5_trackRule.lean):
#check @LeanUrat.MovesU.KernelCarriers
#check @LeanUrat.MovesU.Cl7Kernel
#check @LeanUrat.MovesU.Cl7Kernel.L
#check @LeanUrat.MovesX.MonicBox
#check @LeanUrat.MovesX.discZero
#check @LeanUrat.MovesX.XFamily.ctx
#check @LeanUrat.MovesX.XFamily.gmn
#check @LeanUrat.MovesX.GMNIndex.inStratum
#check @LeanUrat.MovesX.XCtx.Branch
#check @LeanUrat.MovesX.XCtx.hist
#check @LeanUrat.MovesX.XCtx.children
#check @LeanUrat.MovesX.isPrefixB
#check @LeanUrat.MovesX.XNode
#check @LeanUrat.MovesX.XNode.continuing
#check @LeanUrat.MovesX.popOf?
#check @LeanUrat.MovesX.Pop.recT1
#check @LeanUrat.MovesX.Pop.t4
#check @LeanUrat.MovesX.Pop.incT12
#check @LeanUrat.MovesU.Slot_trackRule

-- Slot_dnLattice (SlotsG6_dnLattice.lean; + the G5 X-vocabulary above):
#check @LeanUrat.MovesU.Cl7Kernel.Dden
#check @LeanUrat.MovesU.Cl7Kernel.wstar
#check @LeanUrat.MovesX.XCtx.threshold
#check @LeanUrat.MovesU.Slot_dnLattice

-- Slot_m1m5Echo (SlotsG7_m1m5Echo.lean):
#check @LeanUrat.MovesSp.Species
#check @LeanUrat.MovesSp.Species.lam
#check @LeanUrat.MovesSp.Species.sel
#check @LeanUrat.MovesSp.InCatalogue
#check @LeanUrat.MovesS.Member.δ
#check @LeanUrat.MovesS.Member.status
#check @LeanUrat.MovesS.TableShape.State
#check @LeanUrat.MovesS.TableShape.Out
#check @LeanUrat.MovesS.TableShape.odata
#check @LeanUrat.MovesS.Outcome.mem
#check @LeanUrat.MovesS.Outcome.c
#check @LeanUrat.MovesU.Slot_m1m5Echo

-- Slot_x1aDict (SlotsG8_x1aDict.lean):
#check @MovesRBase.SpeciesSyntax.shape
#check @LeanUrat.MovesU.KernelCarriers.Sp
#check @LeanUrat.MovesU.KernelCarriers.XF
#check @LeanUrat.MovesX.GMNIndex.ind
#check @LeanUrat.MovesX.certified
#check @LeanUrat.MovesX.XNode.sel
#check @LeanUrat.MovesX.XNode.e
#check @LeanUrat.MovesX.XNode.h
#check @LeanUrat.MovesX.XHistory
#check @LeanUrat.MovesU.Slot_x1aDict

end ClosureManifestB

end LeanUrat.MovesU
