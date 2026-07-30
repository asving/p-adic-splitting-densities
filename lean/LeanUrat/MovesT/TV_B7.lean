/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_B2

/-! # TV-B7 — `treeN_stable` RESTATED per the ratified Q2 ruling (option 2:
the named `StableInputs` hypothesis)

BRIDGE CAMPAIGN unit **TV-B7** (area BP3, cluster B; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.B + §4) [FENCE — **Q2 RULED**:
"named StableInputs hypothesis (not KBTotTower fields)",
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` BP3 Q2 — option 2 executes].
E-PHASE SKELETON — statements pinned; the hoisted theorem's body `sorry`
(execution body := `treeN_stable_of_inputs … SI`, TV-B6).

INFORMAL STATEMENT: T-E11b's NAMED OPEN row `treeN_stable`
(E11_treeN.lean:90-99, the one honest sorry riding
`RS1GivenPackage.tree_n`'s stability conjunct) restated with the typed
stability-input bundle `StableInputs` (TV-B2; owner HC-2/D4R0K, MOVES
7566–7570 — D4R.4 exact level-N realization + TB-CAP cylinders + the B(iii)
joint-cell levels) as a NAMED warranted hypothesis; the ∀-closure
`TreeNStableStmt` (Defs.lean:1637) re-keyed to carry the bundle row; proved
from TV-B6 at the premise. E11 goes sorry-free; the capstone package row stops
riding a sorryAx and the open mathematics surfaces as the typed premise row.

GATE RECORD (scheduling constraint "B1 before B7" — satisfied): TV-B1 ran
first and returned BLOCKED-BY-LAW with the law COMPILED
(`tv_b1_chart_carrier_uninhabited`, TV_B1.lean): the unguarded tower chart
carrier `χat : ∀ N', Fin n → Fin (n * N')` is uninhabited at n ≥ 1, so
`treeN_stable` AS STATED is VACUOUSLY provable — the honest sorry hides a
VACUITY, not open mathematics. CONSEQUENCE FOR THIS UNIT (recorded, returned
to the orchestrator as the Q2-refinement fence item): the hoisted statements
below are typed AT THE CURRENT CARRIERS per the Q2 ruling as literally written,
and they remain vacuously derivable at n ≥ 1 until the χat guard repair (e.g.
`χat : ∀ N' (h : N₀ ≤ N'), Fin n → Fin (n * N')`) ALSO lands — a
statement-shape decision on `TreeNStable`/`KBTotTower`/`TreeExpNs` (Defs
carriers, outside this cluster's authority) that the B7 EXECUTION must carry
in the same commit or explicitly re-adjudicate. Do NOT discharge these sorries
by the vacuity (honest-sorries discipline; TV-B1's soundness note).

EXECUTION-PHASE NOTE (recorded per the E-phase new-files-only rule): the
ratified end state is IN-PLACE — `treeN_stable`/`treeN_stable_stmt`
(E11_treeN.lean) gain the `SI` premise and the `:= treeN_stable_of_inputs …`
body; `TreeNStableStmt` (Defs.lean:1637) gains the bundle row (the hoisted
def below); `RS1GivenPackage.tree_n`'s stability conjunct
(D12_packages.lean:82) re-keys to the hoisted closure — existing-file edits
assigned to the prover/integration phase; these skeletons pin the exact
shapes. Sweep + MANIFEST/PROJECT_STATE records ride the same commit.

deps: B1 (ran — blocked-by-law outcome recorded above), B6, ruling Q2 (RULED).
Consumed by: TV-A6 (names the StableInputs row in theoremU's boundary
documentation). difficulty: routine-opus, ~30 lines. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

/-- **TV-B7 `treeN_stable_hoisted`** — T-E11b's stability row
(E11_treeN.lean:90-98, byte-identical premise row and conclusion) RESTATED per
the ratified Q2 ruling (option 2): gains the NAMED warranted hypothesis
`SI : StableInputs Tat χat Tr` (TV-B2, owner HC-2/D4R0K), appended last.
Execution body := `treeN_stable_of_inputs Tat χat Tr SI` (TV-B6) — `hcov`/
`hdet`/`hreal` stay in the row as the contract's declared premises (the note's
own roster; the transfer itself does not consume them, recorded honesty). -/
theorem treeN_stable_hoisted (pol : CanonPolicy p F) {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p))
    (hcov : KBTotTower pol Tat χat trackOf)
    (Tr : VTree p F)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hreal : ∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr)
    (SI : StableInputs Tat χat Tr) :
    TreeNStable Tat χat Tr := by
  sorry

/-- **TV-B7 `TreeNStableStmtHoisted`** — the stability ∀-closure
(Defs.lean:1637, `RS1GivenPackage.tree_n`'s second conjunct) with the
`StableInputs` bundle row inserted (appended last, before the conclusion —
the TV-A2 convention); otherwise byte-identical to `TreeNStableStmt`.
Re-keys `rs1GivenOfMovesT.tree_n`'s stability leg at execution. -/
def TreeNStableStmtHoisted (pol : CanonPolicy p F) : Prop :=
  ∀ {N₀ : ℕ} (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p)),
    KBTotTower pol Tat χat trackOf →
    ∀ Tr : VTree p F,
      (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
      (∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr) →
      StableInputs Tat χat Tr →
      TreeNStable Tat χat Tr

/-- **TV-B7 `treeN_stable_stmt_hoisted`** — the ∀-closure discharged at the
hoisted row (the E11 `treeN_stable_stmt` pattern: rides `treeN_stable_hoisted`'s
single honest sorry; no second admission). -/
theorem treeN_stable_stmt_hoisted (pol : CanonPolicy p F) :
    TreeNStableStmtHoisted (n := n) pol :=
  fun Tat χat trackOf hcov Tr hdet hreal SI =>
    treeN_stable_hoisted pol Tat χat trackOf hcov Tr hdet hreal SI

end LeanUrat.MovesT
