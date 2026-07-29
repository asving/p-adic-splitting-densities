/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E8 `treeExp` [hard — THE CORPUS CENTERPIECE] — (TREE-EXP) (MOVES 7449–7461):
strong induction on Tr.chains' card via the first-split decomposition; every site
charged exactly once. The unit prices over the DATA layer; its ∀-closure `TreeExpFin`
(Defs §2.10) carries the FULL W4-1 interface. JOINT-SATISFIABILITY RECORD (REV 6,
Fable-5 CRIT-1): with the §2.9 scoping the premise row is jointly satisfiable at F1's
own shape (§0 record 13). `multiSites`/`TreeScaffold` are Defs carriers.

ESCALATION RECORD 2026-07-30 (the assembly-spine round; statement UNCHANGED): the
adjudicated `CellData.child_red_uniform` law (root-cell uniformity) and the ledger's
`spectator_sol` law are LANDED in Defs; T-E6 (`fiber_seg_step`) is now PROVED
Lean-core (the spectator-relativized C4 kernel) and T-E5 (`fiber_root_split`) is
proved modulo the single fenced `hnostray` residual (see E5's header). The remaining
work HERE is the recursion assembly per the blueprint sketch: root step = E5 at
`sc.root`; unbranched runs = E6 iterated through `state_cell` with the spectator
events carrying the other branches' pins (both spectator laws now available); splits
= E7 at `sc.splitFrame` with `hcharge` from E3 (one-side) or `hjcm` (multi-side);
leaves = factor 1; recursion on the halted-branch roster (`Tr.hfin.toFinset`) with
`sc.hscope`/`sc.subtree_part` handing each factor to the strictly smaller subtree.
It inherits E5's `hnostray` genre at the root step. Deferred to a dedicated unit —
this sorry is the LAST assembly-spine core (E10/E11 gate on it). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p))
    (hred : RedCellPartition T CA χ trackOf)
    (hsib : SibCount T CA χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H hH.1 h2))
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m := by
  sorry

end LeanUrat.MovesT
