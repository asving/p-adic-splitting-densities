/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E8_treeExp

/-! # T-E11 `treeN` [hard] — TREE-N (MOVES 7559–7574): the finite-level MASS identity
(`treeN`) + the CROSS-LEVEL STABILITY face (`TreeNStable`/`treeN_stable`). X.3-FREE
(7047–7048); GIVEN (SIB) + (JC-multi at multi-side sites) "for the mass value". The
unit prices over the DATA layer; the ∀-closure `TreeNStmt` (Defs §2.10) carries the
FULL W4-1 interface.

T RATIFICATION REPAIR (2026-07-31; verdict §5: "Lean's `treeN` proves only
[the mass identity] for an independently supplied model, assignment, ledger, and
scaffold at that N. Its `hthr` premise is unused, and there is no cross-level
identification of the tree fiber or proof of cylinder stability"): (i) the unused
`hthr` premise is REMOVED from `treeN` (the mass identity is threshold-free as
proved; `TreeNStmt`'s seam row keeps the contract's declared threshold gate);
(ii) the note's stability theorem is now TYPED as `TreeNStable` and carried as the
NAMED OPEN row `treeN_stable` below. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N : ℕ} {pol : CanonPolicy p F}

/-- RE-KEYED at the T RATIFICATION (2026-07-31 — same row changes as `treeExp`; the
unused `hthr` premise REMOVED per verdict §5, honesty: the mass identity as proved
is threshold-free — the threshold's real content is `treeN_stable` below). -/
theorem treeN (Tr : VTree p F) (T : TreeModel p F n N (n * N) pol)
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
      JCmultiAt T CA.toCellData χ (L.parentSt H) (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (sc.splitFrame H hH).c).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) (L.cellAt H)
        (sc.splitFrame H hH).c (sc.splitFrame H hH).S) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L
      = p ^ (n * N) := by
  -- T-E11 is T-E8 (`treeExp`) at the working level m := n·N; `AofTr Tr L` unfolds
  -- to `treeExp`'s exponent `n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H` (Defs §2.10).
  change Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x}
      * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H) = p ^ (n * N)
  exact treeExp Tr T χ trackOf CA hχ hrc hred hsib hreal L sc hjcm hsibT hdet

/-- **TREE-N's CROSS-LEVEL STABILITY, TYPED** — the note's displayed theorem (MOVES
7559–7574), added at the T RATIFICATION (2026-07-31; verdict §5: "The note states
that a fixed finite tree fiber becomes an exact union of level-N residue classes
for every N ≥ thr(T) … Lean's `treeN` proves only [a] mass identity at one finite
level, not finite-level stability"). Over a pinned level tower of models/charts:
for every N above the tree's threshold `thr(T)` and every working level N' ≥ N,
the tree fiber reads ONLY the level-<N digit block — "the fiber is a FINITE
intersection of finite-level digit-cell conditions … hence an exact union of
level-N residue classes" (7566–7570). Under the standard layout (m = n·N',
coordinate c at level ⌊c/n⌋ + 1) the level-<N block is the first n·N coordinates. -/
def TreeNStable {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N')) (Tr : VTree p F) : Prop :=
  ∀ N : ℕ, Tr.thr n ≤ N →
    ∀ (N' : ℕ) (h' : N₀ ≤ N'), N ≤ N' →
      ∀ x x' : Box p (n * N'),
        (∀ c : Fin (n * N'), (c : ℕ) < n * N → x c = x' c) →
        (Tr.fiberAt (Tat N' h') (χat N') x ↔ Tr.fiberAt (Tat N' h') (χat N') x')

/-- **T-E11b `treeN_stable` — NAMED OPEN ROW** (T RATIFICATION 2026-07-31, verdict
§5's demanded statement; the mass face `treeN` above is PROVED, this stability face
is NOT). Premise row = the note's own: T complete finite realizable (per level)
with all leaves (τ-irr)/(τ-hen), over the pinned tower perimeter (`KBTotTower`).
OWNER: HC-2/D4R0K — the note's proof inputs are "per site: the joint cell's
literal system at its B(iii) level; per branch: D4R.4's exact level-N realization;
per leaf: TB-CAP's level-N_V cylinders" (MOVES 7566–7570); D4R.4's exact level-N
realization and the TB-CAP cap cylinders are OPEN owner content in this corpus, so
the row is carried as an honest `sorry` with this owner tag, NOT silently absorbed.
HONESTY NOTE: the premise ROSTER is itself part of the open content — the owner's
discharge may require strengthening it with the D4R.4 exact-realization face; the
row asserts the note's claim at the note's declared inputs, and NOTHING downstream
consumes it (the (†-AGG) input-vii seam cites the STATEMENT). -/
theorem treeN_stable (pol : CanonPolicy p F) {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p))
    (hcov : KBTotTower pol Tat χat trackOf)
    (Tr : VTree p F)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hreal : ∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr) :
    TreeNStable Tat χat Tr := by
  sorry

end LeanUrat.MovesT
