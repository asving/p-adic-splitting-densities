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
own shape (§0 record 13). `multiSites`/`TreeScaffold` are Defs carriers. -/

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
