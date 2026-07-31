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

T RATIFICATION REPAIR (2026-07-29 [date corrected 2026-07-30; original record
mis-dated 2026-07-31]; verdict §5: "Lean's `treeN` proves only
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

/-- RE-KEYED at the T RATIFICATION (2026-07-29 [date corrected 2026-07-30; original
record mis-dated 2026-07-31] — same row changes as `treeExp`; the
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
      JCmultiAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S)
    -- [QUEUE ITEM 5 (E5 hoist ripple 2, TV-A4 shape) 2026-07-31: the ∀-g (U)∧(R)
    --  row, appended last; passed through to the internal `treeExp` call.]
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) :
    Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x} * p ^ AofTr Tr L
      = p ^ (n * N) := by
  -- T-E11 is T-E8 (`treeExp`) at the working level m := n·N; `AofTr Tr L` unfolds
  -- to `treeExp`'s exponent `n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H` (Defs §2.10).
  change Nat.card ↥{x : Box p (n * N) | Tr.fiberAt T χ x}
      * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H) = p ^ (n * N)
  exact treeExp Tr T χ trackOf CA hχ hrc hred hsib hreal L sc hjcm hsibT hdet hUR

/- [2026-08-01 INTEGRATION NOTE: the `TreeNStable` DEF is HOISTED to Defs §2.10
(verbatim), so the ∀-closure `TreeNStableStmt` can ride `RS1GivenPackage.tree_n`
(the re-ratification integration finding: "the stability statement exists but is
not carried by the advertised RS.1 package"). The open theorem row stays HERE.] -/

/-- **T-E11b `treeN_stable` — NAMED OPEN ROW** (T RATIFICATION 2026-07-29 [date
corrected 2026-07-30; original record mis-dated 2026-07-31], verdict
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
consumes it (the (†-AGG) input-vii seam cites the STATEMENT). FENCE-RULE RECORD
(2026-08-01, the negation-attempt duty on sorried universals): NO `KBTotTower`
instance exists anywhere in the corpus (grep: the only occurrence is the
`VPPinned.covering` field declaration — the toys are single-level carriers, no
`Tat` tower), so the premise row is uninhabitable from in-corpus witnesses and no
countermodel is constructible; honest-open stands.
SYN-C2 FENCE-RECORD UPDATE (2026-07-30, C2/N2 ratification,
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "SYNTHESIS PASS 1
ADJUDICATIONS"): the open mathematics behind this sorry is now typed ONCE as
**the one open kernel row `MovesT.ReadLocality`** (MovesT/ReadLocality.lean;
chart_pin + cross-level child locality; owner HC-2/D4R0K unchanged).  Its
derived surfaces: `StableInputs` (TV_B2.lean, `stableInputs_of_readLocality`,
PROVED), `TransferRow` (MovesU/BridgeD5_transferRow.lean,
`transferRow_of_readLocality` at the dressed bridge tower — the (†6) bridge
sibling formerly cited here as an independent row), and THIS row's own
discharge path: TV-B7's hoisted restatement carries `ReadLocality` as the
named hypothesis and closes through TV-B6's composition chain, so supplying
ReadLocality once (the HC-2/D4R0K discharge, or the N3 construction probe)
retires all three faces together.  This sorry stays until the B7 execution
lands the hoisted row in place; statement byte-identical. -/
theorem treeN_stable (pol : CanonPolicy p F) {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p))
    -- [QUEUE ITEM 1 ADAPTER 2026-07-31: `KBTotTower`'s chart carrier is now
    --  guarded; this row's OWN χat binder stays unguarded — its vacuity at n ≥ 1
    --  is the standing TV-B1 fence, repaired by the B7 execution (guard collapse),
    --  not by this adapter. Do NOT discharge by the vacuity.]
    (hcov : KBTotTower pol Tat (fun N' _ => χat N') trackOf)
    (Tr : VTree p F)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hreal : ∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr) :
    TreeNStable Tat χat Tr := by
  sorry

/-- the ∀-closure of `treeN_stable` — the value `RS1GivenPackage.tree_n` carries as
its second conjunct (2026-08-01 integration). Rides `treeN_stable`'s single honest
`sorry`; no second admission. -/
theorem treeN_stable_stmt (pol : CanonPolicy p F) : TreeNStableStmt (n := n) pol :=
  fun Tat χat trackOf hcov Tr hdet hreal =>
    treeN_stable pol Tat χat trackOf hcov Tr hdet hreal

end LeanUrat.MovesT
