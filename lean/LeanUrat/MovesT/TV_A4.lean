/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_A1
import LeanUrat.MovesT.E11_treeN

/-! # TV-A4 — ripple 2 of the E5 hoist: `treeN` (E11) + the Defs ∀-closures
(`TreeExpFin`/`TreeNStmt`) gain the ∀-g (U)∧(R) row

BRIDGE CAMPAIGN unit **TV-A4** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.A + §4; the Q1-ratified hoist's
second ripple). E-PHASE SKELETON — the theorem statement pinned with a `sorry`
body; the two ∀-closure Prop DEFS pinned (definitional, no sorry).

SCOPE (the blueprint's enumerated sweep; verified at HEAD, the blueprint's own
five-file census `Defs/E8_treeExp/E11_treeN/D12_packages/D15_w3Rekey`):
* `treeN` (E11_treeN.lean:42) — restated below as `treeN_hoisted` (row appended
  last, consumed by its internal `treeExp` call at the working level m = n·N);
* `TreeExpFin` (Defs.lean:1565) / `TreeNStmt` (Defs.lean:1593) — the ∀-closures
  QUOTE the theorems' premise rosters, so they gain the same row INSIDE the
  closure; pinned below as `TreeExpFinHoisted`/`TreeNStmtHoisted`;
* `RS1GivenPackage` rows (D12_packages.lean): `rs1GivenOfMovesT` sets
  `tree_exp_fin := TreeExpFin …` / `tree_n := TreeNStmt … ∧ TreeNStableStmt …`
  — re-keys DEFINITIONALLY to the hoisted closures at execution (D12 carries no
  theorem, so no sorryAx lives there; the package VALUES change bytes only);
* `jc_multi` (D12, G-a's fourth name) — RESOLUTION RECORDED: verified at HEAD,
  `xrbOfMovesT.jc_multi` (D12_packages.lean:114) quotes ONLY the `JCmultiAt`
  hypothesis row, which is (U)∧(R)-free — NO change needed to that field; the
  G-a sorryAx inheritance rides the ∀-closure consumers, not `jc_multi`;
* `D15_w3Rekey` — takes `Pi' : RS1GivenPackage` as a BINDER (parametric):
  no edit;
* MANIFEST/PROJECT_STATE records ("R3 executed") — prover-phase records.

EXECUTION-PHASE NOTE (recorded per the E-phase new-files-only rule): the
ratified end state is the IN-PLACE re-key of E11/Defs/D12 (same names) —
existing-file edits assigned to the prover/integration phase; these skeletons
pin the exact restated shapes. The `treeN_stable`/`TreeNStableStmt` legs of
`RS1GivenPackage.tree_n` are CLUSTER B's (TV-B7), not this unit's.

deps: A3. Consumed by: TV-A6 (the boundary deliverable). difficulty:
routine-opus, wide (~40 lines across ~6 files at execution).

RETIREMENT RECORD (2026-07-31, hoisted-twin retirement round): ripple 2 LANDED
in place at queue item 5 — `treeN` (E11_treeN.lean:42) carries the ∀-g (U)∧(R)
row `hUR` appended last, exactly the pinned signature, sorry-free Lean-core
(and the Defs ∀-closures were re-keyed in place, so the two Hoisted defs below
are the pins' compiled record). `treeN_hoisted` is therefore PROVED by direct
application (the pin checked: the diff is the identity); it stays as the
unit's compiled record per the census's retirement disposition. Statement
byte-unchanged. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **TV-A4 `treeN_hoisted`** — T-E11's TREE-N mass identity (E11_treeN.lean:42,
byte-identical premise row and conclusion) RESTATED per the ratified Q1 hoist:
gains the ∀-g (U)∧(R) row `hUR` (appended last), passed through to its internal
`treeExp` call at the working level m := n·N. -/
theorem treeN_hoisted (Tr : VTree p F) (T : TreeModel p F n N (n * N) pol)
    (χ : Fin n → Fin (n * N)) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N (n * N) pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hreal : Realizes T χ Tr)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hsib : SibCount T CA.toCellData χ)
    (L : SiteLedger Tr T CA.toCellData χ)
    (sc : TreeScaffold Tr T CA.toCellData χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S)
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L
      = p ^ (n * N) := by
  -- The item-5 hoist landed in place: the twin IS the landed E11 row.
  exact treeN Tr T χ trackOf CA hχ hrc hred hreal hdet hsib L sc hjcm
    hsibT hUR

/-- **TV-A4 `TreeExpFinHoisted`** — the TREE-EXP ∀-closure (Defs.lean:1565,
`RS1GivenPackage.tree_exp_fin`'s value) with the ∀-g (U)∧(R) row inserted
(appended last, before the conclusion — the TV-A2 convention); otherwise
byte-identical to `TreeExpFin`. Re-keys `rs1GivenOfMovesT.tree_exp_fin` at
execution. -/
def TreeExpFinHoisted (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf) : Prop :=
  ∀ (Tr : VTree p F) (L : SiteLedger Tr T CA.toCellData χ),
    Function.Injective χ →
    RootCellsOf T CA.toCellData χ →
    RedCellPartition T CA.toCellData χ trackOf →
    SibCount T CA.toCellData χ → Realizes T χ Tr →
    ∀ (sc : TreeScaffold Tr T CA.toCellData χ L trackOf),
    (∀ H (hH : H ∈ Tr.chains) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ
        (L.parentSt H) H.lastNode (L.splitAt H hH h2)) →
    (∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S) →
    (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
    (∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) →
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H) = p ^ m

/-- **TV-A4 `TreeNStmtHoisted`** — the TREE-N mass-leg ∀-closure (Defs.lean:1593,
the first conjunct of `RS1GivenPackage.tree_n`'s value) with the ∀-g (U)∧(R)
row inserted (appended last, before the conclusion); otherwise byte-identical
to `TreeNStmt`. Re-keys `rs1GivenOfMovesT.tree_n`'s mass leg at execution; the
stability leg (`TreeNStableStmt`) is TV-B7's. -/
def TreeNStmtHoisted (pol : CanonPolicy p F) : Prop :=
  ∀ (N' : ℕ) (T : TreeModel p F n N' (n * N') pol)
    (χ : Fin n → Fin (n * N')) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N' (n * N') pol T χ trackOf),
    ∀ (Tr : VTree p F) (L : SiteLedger Tr T CA.toCellData χ),
    Function.Injective χ → RootCellsOf T CA.toCellData χ →
    RedCellPartition T CA.toCellData χ trackOf →
    ∀ (sc : TreeScaffold Tr T CA.toCellData χ L trackOf),
    SibCount T CA.toCellData χ → Realizes T χ Tr →
    (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
    (∀ H (hH : H ∈ Tr.chains) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ
        (L.parentSt H) H.lastNode (L.splitAt H hH h2)) →
    (∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S) →
    Tr.thr n ≤ N' →
    (∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) →
    Nat.card ↥{x : Box p (n * N') | Tr.fiberAt T χ x} * p ^ AofTr Tr L = p ^ (n * N')

end LeanUrat.MovesT
