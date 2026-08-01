/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.E8_treeExp
import LeanUrat.Scaffold.HDischarge.H8.CutPartition

/-! # H8-B1 `SiteExpCut.lean` — the regroup + count-form (†) (Wave 2)

`siteExp_cut` (the total site-exponent sum regrouped along the A2 ownership
partition: shallow layer + one block per minimal entrance) and
`fiber_count_cut` (the count-form (†): `treeExp`'s conclusion re-displayed
with the exponent cut open).  Statements VERBATIM from
`lean/blueprints/HDISCHARGE_H8.md` §4 Wave 2; proof stock §3.3
(`read_cut_exhaustive` + `Finset.sum_union` on `shallow_block_disjoint`
lifted through the biUnion + `Finset.sum_biUnion` on `block_block_disjoint`;
then `treeExp` + `pow_add`/`Finset.prod_pow_eq_pow_sum`).

STATEMENT-FENCE HYGIENE: `fiber_count_cut` carries `treeExp`'s VERBATIM
hypothesis row list UNCHANGED — (H8) must not silently strengthen or weaken
TREE-EXP's conditionality; every row is consumed by the single `treeExp`
invocation, never discharged here.  Deps: H8-A2 (`CutPartition`) +
`MovesT.E8_treeExp`. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- (†)-regroup: the total ledger exponent sum over all read sites, cut along
the A2 ownership partition — the shallow-owned sites plus, for each minimal
entrance `ε`, the sites of its block.  Pure `Finset` algebra over the proved
partition (`read_cut_partition`): exhaustiveness rewrites the index set,
`Finset.sum_union` splits on the shallow/biUnion disjointness, and
`Finset.sum_biUnion` splits the blocks on their pairwise disjointness. -/
theorem siteExp_cut (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CD : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CD χ) (E : History p F → Prop) :
    ∑ H ∈ Tr.hfin.toFinset, L.siteExp H
      = (∑ H ∈ shallowReads Tr E, L.siteExp H)
        + ∑ ε ∈ minEnts Tr E, ∑ H ∈ blockReads Tr E ε, L.siteExp H := by
  classical
  obtain ⟨hexh, hdisj, hpair⟩ := read_cut_partition Tr E
  rw [hexh, Finset.sum_union hdisj, Finset.sum_biUnion hpair]

/-- The count-form (†): `treeExp`'s fiber-count conclusion with the exponent
regrouped along the cut — the shallow factor `p ^ (n + Σ_shallow)` times one
block factor `p ^ (Σ_block ε)` per minimal entrance.  The hypothesis block is
`treeExp`'s VERBATIM row list (statement-fence hygiene: (H8) must not
silently re-price TREE-EXP's conditionality); the proof is `treeExp` +
`siteExp_cut` + exponent algebra (`Finset.prod_pow_eq_pow_sum`, `pow_add`). -/
theorem fiber_count_cut (Tr : VTree p F) (T : TreeModel p F n N m pol)
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
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g)
    (E : History p F → Prop) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * ((p ^ (n + ∑ H ∈ shallowReads Tr E, L.siteExp H))
          * ∏ ε ∈ minEnts Tr E, p ^ (∑ H ∈ blockReads Tr E ε, L.siteExp H))
      = p ^ m := by
  classical
  have htree := treeExp Tr T χ trackOf CA hχ hrc hred hsib hreal L sc hjcm
    hsibT hdet hUR
  rw [siteExp_cut Tr T CA.toCellData χ L E] at htree
  calc Nat.card ↥{x | Tr.fiberAt T χ x}
        * ((p ^ (n + ∑ H ∈ shallowReads Tr E, L.siteExp H))
          * ∏ ε ∈ minEnts Tr E, p ^ (∑ H ∈ blockReads Tr E ε, L.siteExp H))
      = Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ((∑ H ∈ shallowReads Tr E, L.siteExp H)
            + ∑ ε ∈ minEnts Tr E, ∑ H ∈ blockReads Tr E ε, L.siteExp H)) := by
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add, add_assoc]
    _ = p ^ m := htree

end LeanUrat.Scaffold.HDischarge.H8
