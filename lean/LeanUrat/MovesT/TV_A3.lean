/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_A1
import LeanUrat.MovesT.E10_perShape

/-! # TV-A3 — ripple 1 of the E5 hoist: `treeExp` (E8) / `perShape_law` (E10)
thread the ∀-g (U)∧(R) row

BRIDGE CAMPAIGN unit **TV-A3** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.A + §4; the Q1-ratified hoist's
first ripple). E-PHASE SKELETON — statements pinned, bodies `sorry`.

INFORMAL STATEMENT: `treeExp` (E8_treeExp.lean:615) and `perShape_law`
(E10_perShape.lean:114) restated with the NAMED warranted row
`hUR : ∀ g, TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g`
(owner HC-2/D4R0K). The ∀-g SHAPE is the blueprint's own resolution (approved
with Q1): inside `treeExp` E5 fires at ONE g — the scaffold's root datum
`sc.g` — but that g is produced INSIDE the proof, so the threaded hypothesis
must be ∀-quantified over g; this matches the other owner rows
(`RedCellPartition`, `SibCount`) already quantified over g/cells. Both
re-proved (mechanically: thread `(hUR sc.g).1`/`(hUR sc.g).2` at the
`fiber_root_split` call, E8:636; `perShape_law` passes the row through its
`treeExp` call, E10:152); `#print axioms` on both becomes Lean-core (the E5
sorryAx gone).

PROOF SKETCH: `treeExp_hoisted` = E8's existing 600-line proof with the call
`fiber_root_split Tr T χ trackOf CA hχ hrc hred hsib ⟨x₀, hx₀⟩ sc.g sc.root
sc.hcr sc.hg` extended by the two trailing arguments `(hUR sc.g).1
(hUR sc.g).2` (TV-A2's appended-last convention). `perShape_law_hoisted` =
E10's existing proof with `treeExp … hdet` extended by `hUR` (the row is
Tr-independent, so ONE row serves every class member).

EXECUTION-PHASE NOTE (recorded per the E-phase new-files-only rule): the
ratified end state is the IN-PLACE restatement in E8/E10 (same names, row
appended last) — existing-file edits assigned to the prover/integration phase;
these skeletons pin the exact restated signatures. The rebuild is fragile
(E8 is 600+ lines) — blueprint difficulty hard-fable.

deps: A2 (the restated E5 signature these bodies call). Consumed by: TV-A4
(E11/D12/Defs sweep), TV-A6. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **TV-A3 `treeExp_hoisted`** — T-E8 TREE-EXP (E8_treeExp.lean:615,
byte-identical premise row and conclusion) RESTATED per the ratified Q1 hoist:
gains the ∀-g (U)∧(R) row `hUR` (appended last), consumed at the internal
`fiber_root_split` call at the scaffold's root datum `sc.g`. Sorry-free with
Lean-core footprint at execution. -/
theorem treeExp_hoisted (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA.toCellData χ)
    (sc : TreeScaffold Tr T CA.toCellData χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m := by
  sorry

/-- **TV-A3 `perShape_law_hoisted`** — T-E10b's per-shape law
(E10_perShape.lean:114, byte-identical premise row and conclusion) RESTATED per
the ratified Q1 hoist: threads the SAME ∀-g (U)∧(R) row (appended last) through
its per-class-member `treeExp` calls — the row is Tr-independent, so one row
serves the whole shape class. -/
theorem perShape_law_hoisted (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ)
    (hns₀ : NsFree Tr₀) (hreal₀ : Realizes T χ Tr₀)
    (L₀ : SiteLedger Tr₀ T CA.toCellData χ)
    (Lat : ∀ Tr ∈ shapeClass Tr₀ T χ, SiteLedger Tr T CA.toCellData χ)
    (scat : ∀ Tr h, TreeScaffold Tr T CA.toCellData χ (Lat Tr h) trackOf)
    (hjcm : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ),
      ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ (Lat Tr h))
        (h2 : 2 ≤ (Lat Tr h).sides H),
        JCmultiAt T CA.toCellData χ ((Lat Tr h).parentSt H) H.lastNode
          ((Lat Tr h).splitAt H hH.1 h2))
    (hsibT : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ),
      ∀ H (hH : H ∈ Tr.chains),
        2 ≤ (CA.toCellData.branchSetOf ((Lat Tr h).cellAt H)).card →
        SibCountAt T CA.toCellData χ ((Lat Tr h).parentSt H) H.lastNode
          ((Lat Tr h).cellAt H) ((scat Tr h).splitFrame H hH).S)
    (hdict : ∀ Tr (h : Tr ∈ shapeClass Tr₀ T χ), ∀ H ∈ Tr.chains,
      (Lat Tr h).siteExp H = shapeExp (shapeOfH H n) n)
    (hdict₀ : ∀ H ∈ Tr₀.chains, L₀.siteExp H = shapeExp (shapeOfH H n) n)
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) :
    (∑ Tr ∈ (shapeClass_finite Tr₀ T χ).toFinset,
        Nat.card ↥{x | (Tr : VTree p F).fiberAt T χ x})
        * p ^ (AofTr Tr₀ L₀)
      = Nat.card ↥(shapeClass Tr₀ T χ) * p ^ m := by
  sorry

end LeanUrat.MovesT
