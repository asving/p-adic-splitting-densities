/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E8_treeExp

/-! # T-E11 `treeN` [hard] — TREE-N finite-level stability (MOVES 7559–7574): for
every N ≥ thr(T), the fiber is an exact union of level-N residue classes. X.3-FREE
(7047–7048); GIVEN (SIB) + (JC-multi at multi-side sites) "for the mass value". The
unit prices over the DATA layer; the ∀-closure `TreeNStmt` (Defs §2.10) carries the
FULL W4-1 interface. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N : ℕ} {pol : CanonPolicy p F}

theorem treeN (Tr : VTree p F) (T : TreeModel p F n N (n * N) pol)
    (CA : CellData p F n N (n * N) pol T) (χ : Fin n → Fin (n * N))
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p))
    (hred : RedCellPartition T CA χ trackOf)
    (hreal : Realizes T χ Tr)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hthr : Tr.thr n ≤ N) (hsib : SibCount T CA χ)
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA χ (L.parentSt H) (L.cellAt H) (L.splitAt H hH.1 h2)) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L
      = p ^ (n * N) := by
  -- T-E11 is T-E8 (`treeExp`) at the working level m := n·N; `thr`(via `hthr`) only
  -- guarantees we are above the stability threshold, and `AofTr Tr L` unfolds to
  -- `treeExp`'s exponent `n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H` (Defs §2.10).
  change Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x}
      * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H) = p ^ (n * N)
  exact treeExp Tr T CA χ hχ hrc trackOf hred hsib hreal L sc hjcm hdet

end LeanUrat.MovesT
