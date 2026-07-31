/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_A1
import LeanUrat.MovesT.E5_rootSplit

/-! # TV-A2 — `fiber_root_split` RESTATED: the (U)∧(R) pair as NAMED premises

BRIDGE CAMPAIGN unit **TV-A2** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.A + §4) [FENCE — **Q1 RATIFIED**:
"E5 hoist ratified", `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` BP3 Q1;
PROJECT_STATE §UPDATE 2026-07-30b records R3 (sorry → hypothesis) as the agreed
direction]. E-PHASE SKELETON — statement pinned, body `sorry`.

INFORMAL STATEMENT: T-E5's root-clause count identity
`|fiber| · |rootCell|^t · pⁿ = p^m · ∏ᵢ |rootCell ∩ trackEventᵢ|`, with the
internal fenced pair `hD4R0K` (E5_rootSplit.lean:343-349 — the ONLY gap of the
module) hoisted to the two NAMED warranted premises `hU : TrackUniqOn T χ
trackOf g` / `hR : TrackRepOn T χ trackOf g` (TV-A1's defs = the displayed
(U)/(R) conjuncts VERBATIM; owner HC-2/D4R0K, MOVES 7112–7119, the (c2)
covering case analysis). Everything else is byte-identical to
`fiber_root_split` (E5:203-215).

PROOF SKETCH (mechanical — the ratified R3 hoist): E5's existing proof body
with the `have hD4R0K : … := by sorry` (:343-349) DELETED and
`obtain ⟨hTrkUniq, hTrkRep⟩ := hD4R0K` (:350) replaced by the premises
(`hTrkUniq := hU`, `hTrkRep := hR`). Everything downstream of the pair is
already machine-checked in E5 (hcard6/hheads_eq/the roster injectivity-to-
surjectivity step/hnostray-as-theorem/hconv/hfeq + the SIB counting); the
restated module is sorry-free with a Lean-core footprint.

EXECUTION-PHASE NOTE (recorded per the E-phase new-files-only rule): the unit's
ratified END STATE is the IN-PLACE restatement of `fiber_root_split` in
E5_rootSplit.lean (SAME NAME, premises gained) with the one in-corpus call site
(E8_treeExp.lean:636) threaded by TV-A3 — an existing-file edit assigned to the
prover/integration phase. This skeleton pins the exact restated signature so
the prover's diff is checked against it; it is NOT a second permanent
declaration (retire it when the in-place edit lands).

STATEMENT RESOLUTION (recorded): the blueprint does not fix the new premises'
position in the row; they are APPENDED LAST (after `hfib`) — the minimal-diff
convention (every call site extends by two trailing arguments). The same
convention is used across TV-A3/TV-A4.

deps: A1. Consumed by: TV-A3 (`treeExp`/`perShape_law` threading), TV-A4
(E11/D12/Defs sweep), TV-A6 (boundary record). difficulty: routine-opus,
~10 changed lines at execution.

RETIREMENT RECORD (2026-07-31, hoisted-twin retirement round): the in-place
restatement LANDED at queue item 5 — `fiber_root_split` (E5_rootSplit.lean:212)
now carries `hU`/`hR` appended last, exactly this pinned signature, and E5 is
sorry-free. The twin below is therefore PROVED by direct application (the pin
checked: the diff is the identity); it stays as the unit's compiled record per
the census's retirement disposition. Statement byte-unchanged. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **TV-A2 `fiber_root_split_hoisted`** — T-E5's root clause (E5_rootSplit.lean:203,
byte-identical premise row and conclusion) RESTATED per the ratified Q1 hoist: the
internal fenced (U)∧(R) pair rides as the NAMED warranted premises `hU`/`hR`
(TV-A1's `TrackUniqOn`/`TrackRepOn`, owner HC-2/D4R0K), appended last. At execution
this signature REPLACES `fiber_root_split` in place and E5 goes sorry-free. -/
theorem fiber_root_split_hoisted (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ) (hreal : Realizes T χ Tr)
    (g : Fin n → ZMod p) (htracks : RootSplitData Tr g)
    (hcr : ∀ i, ChildRoot none (htracks.headOf i))
    (hfib : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g)
    (hU : TrackUniqOn T χ trackOf g)
    (hR : TrackRepOn T χ trackOf g) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * (Nat.card ↥(rootCell χ g)) ^ htracks.t * p ^ n
      = p ^ m * ∏ i : Fin htracks.t,
          Nat.card ↥(rootCell χ g ∩ trackEvent Tr T htracks i (hcr i)) := by
  -- The item-5 hoist landed in place: the twin IS the landed E5 row.
  exact fiber_root_split Tr T χ trackOf CA hχ hrc hred hsib hreal g htracks
    hcr hfib hU hR

end LeanUrat.MovesT
