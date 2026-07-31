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
Consumed by: TV-A6 (names the ReadLocality row in theoremU's boundary
documentation). difficulty: routine-opus, ~30 lines.

SYN-C2 RETYPE (2026-07-30, C2/N2 ratification,
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "SYNTHESIS PASS 1
ADJUDICATIONS"; statement change on this E-phase skeleton, pre-ratification,
executed and recorded by unit SYN-C2): the named warranted hypothesis carried
by the hoisted rows is now `RL : ReadLocality Tat (fun N' _ => χat N') Tr` —
THE one level-locality kernel row (MovesT/ReadLocality.lean, owner
HC-2/D4R0K) — instead of `SI : StableInputs Tat χat Tr`, which is now DERIVED
from it (`stableInputs_of_readLocality`, TV_B2.lean; PROVED).  Execution body
becomes `treeN_stable_of_inputs Tat χat Tr (stableInputs_of_readLocality Tat
χat Tr RL)` (TV-B6 unchanged — the B3–B6 composition chain still speaks
StableInputs internally).  The unguarded-χat adapter `fun N' _ => χat N'` is
the chi-at guard-repair coordination record (ReadLocality header, resolution
1): these rows still bind the AS-IS unguarded Defs carriers and remain
vacuously derivable at n ≥ 1 until the Defs guard sweep lands (the TV-B1
gate record above stands; do NOT discharge by vacuity). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

/-- **TV-B7 `treeN_stable_hoisted`** — T-E11b's stability row
(E11_treeN.lean:90-98, byte-identical premise row and conclusion) RESTATED per
the ratified Q2 ruling (option 2), SYN-C2 RETYPE (module docstring): gains the
NAMED warranted hypothesis `RL : ReadLocality Tat (fun N' _ => χat N') Tr` —
THE one kernel row (MovesT/ReadLocality.lean, owner HC-2/D4R0K) — appended
last.  Execution body := `treeN_stable_of_inputs Tat χat Tr
(stableInputs_of_readLocality Tat χat Tr RL)` (TV-B6 + the SYN-C2 derivation)
— `hcov`/`hdet`/`hreal` stay in the row as the contract's declared premises
(the note's own roster; the transfer itself does not consume them, recorded
honesty). -/
theorem treeN_stable_hoisted (pol : CanonPolicy p F) {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p))
    -- [QUEUE ITEM 1 SEAM ADAPTER 2026-07-31 (appended by the item-1 executor —
    --  the KBTotTower chart carrier is now guarded in Defs; the E11-mirror
    --  adapter. This row's own χat binder stays unguarded pending the B7
    --  execution's guard collapse — module-docstring fence stands).]
    (hcov : KBTotTower pol Tat (fun N' _ => χat N') trackOf)
    (Tr : VTree p F)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hreal : ∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr)
    (RL : ReadLocality Tat (fun N' _ => χat N') Tr) :
    TreeNStable Tat χat Tr := by
  sorry

/-- **TV-B7 `TreeNStableStmtHoisted`** — the stability ∀-closure
(Defs.lean:1637, `RS1GivenPackage.tree_n`'s second conjunct) with the
`ReadLocality` kernel row inserted (appended last, before the conclusion —
the TV-A2 convention; SYN-C2 RETYPE, module docstring: the row is the ONE
kernel, not the derived `StableInputs` bundle); otherwise byte-identical to
`TreeNStableStmt`.  Re-keys `rs1GivenOfMovesT.tree_n`'s stability leg at
execution. -/
def TreeNStableStmtHoisted (pol : CanonPolicy p F) : Prop :=
  ∀ {N₀ : ℕ} (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p)),
    -- [QUEUE ITEM 1 SEAM ADAPTER 2026-07-31 — same as `treeN_stable_hoisted`.]
    KBTotTower pol Tat (fun N' _ => χat N') trackOf →
    ∀ Tr : VTree p F,
      (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
      (∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr) →
      ReadLocality Tat (fun N' _ => χat N') Tr →
      TreeNStable Tat χat Tr

/-- **TV-B7 `treeN_stable_stmt_hoisted`** — the ∀-closure discharged at the
hoisted row (the E11 `treeN_stable_stmt` pattern: rides `treeN_stable_hoisted`'s
single honest sorry; no second admission). -/
theorem treeN_stable_stmt_hoisted (pol : CanonPolicy p F) :
    TreeNStableStmtHoisted (n := n) pol :=
  fun Tat χat trackOf hcov Tr hdet hreal RL =>
    treeN_stable_hoisted pol Tat χat trackOf hcov Tr hdet hreal RL

end LeanUrat.MovesT
