/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.CutDefs
import LeanUrat.Scaffold.HDischarge.H8.CutFirst

/-! # H8-A2 `CutPartition.lean` — (CUT-2) + (BDY), the ownership partition (Wave 1)

`read_cut_exhaustive` / `shallow_block_disjoint` / `block_block_disjoint` /
`bdy_display` + the optional `read_cut_partition` packaging.  Statements
VERBATIM from `lean/blueprints/HDISCHARGE_H8.md` §4 Wave 1.

G-2 falsifier channels (§5): #1 (overlapping ownership) ↔
`shallow_block_disjoint` + `block_block_disjoint`; #2 (unowned read) ↔
`read_cut_exhaustive`.  The (BDY) node-vs-edge ownership shift is displayed
as a THEOREM (`bdy_display`), and the §2.2 nested-entrance no-reclassification
fence is a corollary of the partition (ownership is by FIRST entrance), not an
extra clause.  Deps: H8-D0, H8-A1.

HOIST RECORD (SYNTHESIS_PASS3 F1, 2026-08-01): the proofs formerly here
(proof stock `lean/blueprints/HDISCHARGE_H8.md` §3.2 — exhaustive: classical
split on `ShallowRead`, non-shallow reads land at their A1 first entrance,
itself minimal and chain-closed; exclusive: a block member has an entrance
proper prefix — never shallow — and two blocks meeting force two
`FirstEntAbove` witnesses at one `H`, killed by A1 uniqueness) moved
VERBATIM, carrier-generic, to `Scaffold/Shared/FirstEntrance.lean`.  The
statements below are UNCHANGED; each proof is now the instantiation of the
shared theorem at the `Carrier (History p F)` instance of `CutFirst.lean`,
with `(Tr.chains, Tr.hfin, vtree_prefix_closed Tr)` for the chain set — H8's
`minEnts`/`shallowReads`/`blockReads` (`CutDefs.lean`, untouched) are
definitionally the shared ones at this instance. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open Classical in
/-- (CUT-2) exhaustiveness — G-2 falsifier channel #2 (unowned read): every
read site of the tree is owned, shallow-side or by the block of some minimal
entrance.  `⊆`: a chain is shallow or (classically) has an A1 first entrance
`ε`, itself minimal (`firstEntAbove_shallowRead`) and a chain
(`firstEntAbove_mem_chains`), so the read lands in `blockReads ε` of a genuine
`minEnts` member.  `⊇`: filters of `Tr.hfin.toFinset` are subsets. -/
theorem read_cut_exhaustive (Tr : VTree p F) (E : History p F → Prop) :
    Tr.hfin.toFinset
      = shallowReads Tr E ∪ (minEnts Tr E).biUnion (blockReads Tr E) :=
  Shared.FirstEntrance.read_cut_exhaustive Tr.hfin (vtree_prefix_closed Tr) E

/-- (CUT-2) exclusivity, shallow half — G-2 falsifier channel #1 (overlapping
ownership): a member of `blockReads ε` has the entrance `ε` as a PROPER prefix
(`FirstEntAbove` clause 2), refuting `ShallowRead` — no read is charged both
shallow-side and block-side.  (Holds without `hε`; the binder is the
consumption shape.) -/
theorem shallow_block_disjoint (Tr : VTree p F) (E : History p F → Prop)
    {ε : History p F} (hε : ε ∈ minEnts Tr E) :
    Disjoint (shallowReads Tr E) (blockReads Tr E ε) :=
  Shared.FirstEntrance.shallow_block_disjoint Tr.hfin E hε

/-- (CUT-2) exclusivity, block-block half — G-2 falsifier channel #1
(overlapping ownership): a read in two blocks would exhibit two
`FirstEntAbove` witnesses at the same `H`; A1 uniqueness
(`firstEntAbove_unique`) forces `ε₁ = ε₂` — distinct blocks never overlap. -/
theorem block_block_disjoint (Tr : VTree p F) (E : History p F → Prop)
    {ε₁ ε₂ : History p F} (h : ε₁ ≠ ε₂) :
    Disjoint (blockReads Tr E ε₁) (blockReads Tr E ε₂) :=
  Shared.FirstEntrance.block_block_disjoint Tr.hfin E h

/-- (BDY) display — the node-vs-edge ownership shift as a THEOREM, not a
convention: a minimal entrance `ε` is `ShallowRead` by its `minEnts` filter
clause — its OWN entering read is charged shallow-side — while every member
of its block has `ε` STRICTLY above (`FirstEntAbove` clause 2).  With the
partition this also displays the §2.2 nested-entrance fence: entrances inside
block `ε` stay owned by the outermost block. -/
theorem bdy_display (Tr : VTree p F) (E : History p F → Prop)
    {ε : History p F} (hε : ε ∈ minEnts Tr E) :
    ε ∈ shallowReads Tr E ∧ ∀ H ∈ blockReads Tr E ε, ProperPrefix ε H :=
  Shared.FirstEntrance.bdy_display Tr.hfin E hε

open Classical in
/-- Optional packaging (prover's-discretion corollary, §3.2): the full
ownership partition in one display — the union is exhaustive
(`read_cut_exhaustive`), the shallow layer misses every block
(`shallow_block_disjoint` lifted through `Finset.disjoint_biUnion_right`),
and the block family is pairwise disjoint (`block_block_disjoint`). -/
theorem read_cut_partition (Tr : VTree p F) (E : History p F → Prop) :
    Tr.hfin.toFinset
        = shallowReads Tr E ∪ (minEnts Tr E).biUnion (blockReads Tr E)
      ∧ Disjoint (shallowReads Tr E) ((minEnts Tr E).biUnion (blockReads Tr E))
      ∧ ((minEnts Tr E) : Set (History p F)).PairwiseDisjoint
          (blockReads Tr E) :=
  Shared.FirstEntrance.read_cut_partition Tr.hfin (vtree_prefix_closed Tr) E

end LeanUrat.Scaffold.HDischarge.H8
