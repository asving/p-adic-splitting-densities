/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # TV-B1 — COUNTERMODEL-ATTEMPT gate for `treeN_stable` AS STATED

BRIDGE CAMPAIGN unit **TV-B1** (area BP3, cluster B; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.B + §4 + risk R1). **GATE UNIT
(countermodel-first duty for the sorried universal `treeN_stable`,
E11_treeN.lean:90-99)** — runs BEFORE the provers TV-B6/B7.

SEALED PREDICTION (risk R1): `treeN_stable` AS CURRENTLY STATED (KBTotTower
premises only) may be FALSE — nothing in `perLevel`/`root_total`/`scale_grow`
bounds the digit level a model's `mem` reads (verified against Defs.lean:920-946),
so a tower whose chain-history `mem` is keyed to a level-≥ n·N coordinate should
defeat `TreeNStable`. Heavy construction legs (blueprint): `KBTot.ns_lumps`
(needs JetSetup + ScaleFaithful + NsLumpFamily witnesses per realized H) and
`scale_grow` (JetTower + Tendsto).

**E-PHASE TYPING-TIME OUTCOME — THE GATE IS ALREADY DECIDED (blocking law
COMPILED below).** The countermodel statement `TVB1Countermodel` is structurally
FALSE, and dually `treeN_stable` is VACUOUSLY PROVABLE as stated: the tower
chart carrier `χat : ∀ N', Fin n → Fin (n * N')` is UNGUARDED in N' (unlike
`Tat`/`Jat`, which carry `N₀ ≤ N'`), and at N' = 0 its type is
`Fin n → Fin 0` — uninhabited for every n ≥ 1 (`tv_b1_chart_carrier_uninhabited`
below, PROVED, no sorry). Consequences, all recorded here for the orchestrator:
(1) the countermodel construction is BLOCKED BY LAW: no χat witness exists at
    n ≥ 1; and at n = 0 all boxes are equal (Fin 0 domains), so `TreeNStable`
    is trivially true — `TVB1Countermodel` is refutable outright;
(2) `treeN_stable`/`treeN_stable_stmt`/`TreeNStableStmt` (and hence the
    `RS1GivenPackage.tree_n` stability conjunct) are VACUOUSLY DISCHARGEABLE:
    from any χat with n ≥ 1 one derives False; the n = 0 leg is separately
    trivial (Fin (0·N') boxes are all equal). MACHINE-CHECKED at E-phase: the
    full vacuous proof of `treeN_stable`'s statement (both legs, sorry-free)
    was compiled TRANSIENTLY and deliberately NOT committed — committing it
    would silently "discharge" the named open row while proving none of the
    note's stability content. The "honest sorry" hides a VACUITY, not open
    mathematics — a STATEMENT-FENCE EVENT: the Q2/B7 repair must ALSO guard
    χat (e.g. `χat : ∀ N' (h : N₀ ≤ N'), Fin n → Fin (n * N')`), else the
    B-cluster's G-b deliverable is contentless;
(3) the same unguarded-χat pattern rides `KBTotTower` (Defs.lean:929-931,
    making the structure uninstantiable at n ≥ 1 — the E11 fence record's
    "no instance exists" is structural, not merely in-corpus) and `TreeExpNs`
    (Defs.lean:1649-1666) — corpus sweep recommended (outside this cluster).
SOUNDNESS NOTE: `tv_b1_chart_carrier_uninhabited` is NOT the negation of any
sorried Prop (it consumes a χat; no sorried declaration supplies one), so the
M1 coexistence rule is respected; nothing in this file asserts
`TVB1Countermodel` (it is a `def`, not a sorried theorem — asserting a
statement already seen to be false would violate the honest-sorries
discipline).

QUARANTINE RULE (carried from the blueprint, for the post-repair re-run): if a
REPAIRED statement's countermodel is ever completed, the compiled negation must
NOT coexist in the build with the un-repaired sorried universal — it lands in
quarantine or in the same commit as the B7 repair.

STATEMENT RESOLUTION (recorded): p := 2, F := ZMod 2 pinned (the in-corpus toy
field; the blueprint leaves the field free), remaining carriers existential.

deps: none. difficulty: hard-fable, ~150 lines or blocked-record — resolved at
typing time as blocked-by-law, with the law compiled. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- **TV-B1, the countermodel statement** (a `def`, NOT asserted): the premise
row of `treeN_stable` (E11_treeN.lean:90-98) inhabited — KBTotTower + a
deterministic realizable tree — together with the FAILURE of `TreeNStable`.
Structurally FALSE as typed: see the module docstring and
`tv_b1_chart_carrier_uninhabited`. Kept as the gate's record of WHAT was
attempted; the post-Q2 repaired statement re-keys this Prop.
[QUEUE ITEM 1 SEAM ADAPTER 2026-07-31 (M1-hygiene note, appended by the item-1
executor — the ONLY touch to this leaf): `KBTotTower`'s chart carrier is now
GUARDED in MovesT/Defs (the ratified chi-at repair this gate demanded), so the
application below reads it through `fun N' _ => χat N'`. The compiled law
`tv_b1_chart_carrier_uninhabited` stands UNCHANGED and refutes the PRE-REPAIR
(unguarded, pre-2026-07-31) carrier form of `KBTotTower`/`TreeExpNs` — it is
the witness that FORCED the repair, not a countermodel of any repaired
statement. The residual unguarded binders (this def's own χat, `TreeNStable`,
`TreeNStableStmt`, `StableInputs`, the E11/B7 rows) remain fenced for the B7
execution's guard collapse.] -/
def TVB1Countermodel : Prop :=
  ∃ (n N₀ : ℕ) (pol : CanonPolicy 2 (ZMod 2))
    (Tat : ∀ N', N₀ ≤ N' → TreeModel 2 (ZMod 2) n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node 2 (ZMod 2) → Polynomial (ZMod 2)),
    KBTotTower pol Tat (fun N' _ => χat N') trackOf ∧
    ∃ Tr : VTree 2 (ZMod 2),
      (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) ∧
      (∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr) ∧
      ¬ TreeNStable Tat χat Tr

/-- **TV-B1, the EXACT BLOCKING LAW — compiled**: the unguarded tower chart
carrier `∀ N', Fin n → Fin (n * N')` is UNINHABITED for every n ≥ 1, because at
N' = 0 it demands a function `Fin n → Fin 0`. This blocks the countermodel
construction at the type level (before any KBTotTower leg is reached) AND makes
every ∀-χat statement over it — `treeN_stable`, `TreeNStableStmt`,
`TreeExpNs`-genre rows — vacuously provable at n ≥ 1. Fence event for the Q2/B7
ruling; see the module docstring. -/
theorem tv_b1_chart_carrier_uninhabited (n : ℕ) (hn : 0 < n)
    (χat : ∀ N' : ℕ, Fin n → Fin (n * N')) : False :=
  Fin.elim0 (χat 0 ⟨0, hn⟩)

end LeanUrat.MovesT
