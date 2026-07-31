# SlotsG2/G3 quarantine disposition — importer census + BLOCKED record (2026-07-31)

Unit: g2g3-quarantine (REMAINING_CENSUS_2026-08-01.md §1 MovesU row "SlotsG2/G3
dead-vocabulary blocked records", §4.1.8 the old Q14 disposition).  Charge: execute
the BP5 Q-5 quarantine-with-record precedent on `MovesU/SlotsG2_relFamily.lean`
(4 sorries: `Slot_rel2a/b/d/e`) and `MovesU/SlotsG3_rel3.lean` (1 sorry:
`Slot_rel3`) — verify zero live importers by rg AT EXECUTION TIME (the A7
discipline), move to `lean/quarantine/` with dated `.txt` suffix + README entries,
reverify the build; **if ANY importer is live, do NOT quarantine — record why and
return BLOCKED for that file**.

## The at-execution-time importer census (rg, 2026-07-31, HEAD = 29b80fd)

Import-statement census (`rg "^import.*(SlotsG2_relFamily|SlotsG3_rel3)"` over the
whole repo, `.lake` excluded):

| importer | imports | consumption |
|---|---|---|
| `LeanUrat/MovesU/SlotsG16_sitedLaws.lean:10` | SlotsG2_relFamily | **LIVE, code-level**: `Slot_rel1 CI` is a conjunct of the FILLED `SitedSlot_rel2b` (:155) and `SitedSlot_rel2e` (:207) |
| `LeanUrat/MovesU/SlotsG12b_closureManifestB.lean:7` | SlotsG2_relFamily | **LIVE**: `#check @LeanUrat.MovesU.Slot_rel1` (:53) is a compiled closure-manifest row |
| `LeanUrat/MovesU/SlotsG12b_closureManifestB.lean:8` | SlotsG3_rel3 | **import line only — ZERO declarations consumed** (G12b's only `Slot_rel3` references are header prose; its own header records "no manifest rows owed yet" for the rel2a/b/d/e + rel3 sorries) |

Identifier census for the five sorried decls (`rg "Slot_rel2a|Slot_rel2b|Slot_rel2d|
Slot_rel2e|Slot_rel3"` outside the two files, `Sited*` names excluded): every hit is
comment/docstring text (SlotsG1:32/39/192-3, SlotsG12:53, SlotsG12b:24,
SlotsG16:15/108/147/161/186, SlotsG17:13/124).  **Zero code-level consumers — the
five sorried Props are genuinely dead vocabulary**, superseded by the FILLED sited
re-types `SitedSlot_rel2a/b/d/e` (SlotsG16) + `SitedSlot_rel3` (SlotsG17).

Downstream of G16 (so transitively downstream of SlotsG2): the whole live D-SC
carrier layer — G17 (`Slot_rel1` at :144) → G18 (`RelRow_rel1` :90) → G19b/c/d/e
(G19b :82/111/134, G19c :67/123 use `Slot_rel1` in probe targets).  Neither file is
in the root import graph (`LeanUrat.lean` imports no SlotsG module) nor in
`AxChk_baseline.lean`; but the lakefile's `LeanUrat` lib compiles the full module
tree, so a dangling import breaks the full build.

## Disposition (per the unit rule: any live importer ⇒ BLOCKED)

**`SlotsG2_relFamily.lean` — BLOCKED, not quarantined.**  The file mixes ONE live
filled Prop with the four dead sorried Props: `Slot_rel1` (the displayed REL.1
ledger clause) is code-consumed by SlotsG16 and manifest-pinned by SlotsG12b, and
through G16 it conditions the entire filled D-SC layer (SitedSlot_rel2b/2e display
`Slot_rel1 CI` per site).  Whole-file quarantine severs the D-SC carrier layer =
build breakage.  UNLOCK PATH (fence-gated, needs Asvin): split the file — hoist
`Slot_rel1` verbatim to its own module (or into SlotsG1's cone) and re-point the
two importers, THEN the residual four-sorry file passes the Q-5 gate.  Moving a
landed, Codex-audited (Q5 gate) definition between modules is a statement-fence
event under the dedup-audit discipline (every new decl a verbatim move, named-decl
scope), not an autonomous unit's call.

**`SlotsG3_rel3.lean` — BLOCKED, not quarantined.**  Sole importer =
`SlotsG12b_closureManifestB.lean:8`, a build-tree module (full `lake build`
compiles it), hence a LIVE importer under the precedent's criterion (contrast the
L6_R3 record, whose only importer was a frozen notes snapshot).  The import
consumes nothing, so the file is ONE dead-import deletion away from a clean Q-5
move.  UNLOCK PATH (adjudication, not fence-scale): delete G12b:8 (+ touch its
header prose), reverify G12b per-module, then execute the Q-5 move of SlotsG3 with
README record.  Not executed by this unit: the unit rule forbids quarantine while
the importer stands, and editing a landed closure manifest's import roster is an
orchestrator call (G12b's roster was deliberate — the manifest imported the
BLOCKED-record files to keep them censused in its build).

## Effects

No files moved, no imports edited, no build impact; the 5 sorries stand as the
honest BLOCKED records they are (SlotsG2 :232/238/246/254, SlotsG3 :98 — in-file
records dated 2026-07-30 unchanged).  Census effect: the "5 dead-vocabulary
blocked records awaiting quarantine disposition" row RESOLVES to two recorded
adjudications (the G2 split fence + the G12b:8 severance), each one step from
execution.  M1 hygiene: n/a (no negation witnesses, no statement changes,
statements byte-unchanged).
