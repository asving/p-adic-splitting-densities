# Verdict — unit RSGN (the capstone-gate unit: amendment A-I.3 + the I.15–I.18 landing)

Date: 2026-08-26.  Stage reached: **3 of 3 (all stages complete)**.
Authorities: `runs/wave-b/verdict_PK12.md` ("Notes for later nodes": the re-sign targets
C130s18's §4.4 bodies AS AMENDED — explicit-universe shape, `(fieldE := fE)`);
`docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §4.4; the A-I.1/A-I.2 amendment conventions
in `leanspec/Leanspec/ChapI.lean`.

## VERDICT: A-I.3 ENACTED + ALL FOUR CAPSTONE-ASSEMBLY THEOREMS LANDED — every footprint
Lean-core, zero sorry, zero new axiom, the leanspec byte-freeze verified by diff.

| item | status |
|---|---|
| Amendment A-I.3 (I.10a/I.10b socket bodies) | **ENACTED** — number checked free by repo-wide grep before use |
| I.15 `drainage_of_capstoneHypotheses` | **LANDED** (`leanfinal/Uniformity/ChapI/I10_I15_I18.lean:188`), Lean-core |
| I.16 `decided_of_capstoneHypotheses` | **LANDED** (`…/I10_I15_I18.lean:199`), Lean-core |
| I.17 `uniformity_of_capstoneHypotheses` | **LANDED** (`…/I10_I15_I18.lean:211`), Lean-core |
| I.18 `totalMassOne_of_capstoneHypotheses` | **LANDED** (`…/I10_I15_I18.lean:219`), Lean-core |

No projection was BLOCKED: none of the four consumes `jd0`/`genhnBox2`/the `w1` debt/the five
I-D12 `True` bodies — they project `a2`/`a0` and apply landed `UniformityStatement.ofDecided`/
`totalMassOne_of_drainage` only, exactly the leanspec proofs.  Nothing guarded was discharged.

## STAGE 1 — the amendment (leanspec/Leanspec/ChapI.lean)

**A-I.3 (2026-08-26): the I.10a/I.10b socket BODIES are typed at chapter C's enacted PK-12
carriers; ONLY the two bodies changed.**

* I.10a `CanonicalLadderConfig` body (`leanspec/Leanspec/ChapI.lean:697-711`):
  `True` → `Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData.{0, uG, uKt, uL}
  C B G Kt L N v ρ q n` — the enacted §4.4 shape (∃ E, Field E, ArisingCore,
  ChainRealization `(fieldE := fE)` at the PK-1 split-node carrier, RealizedInput, CC-12 view
  pins), by direct reference (zero drift — C130s18 composed these Props at the EXACT leanspec
  binder blocks for this re-sign; its §1 note said so).
* I.10b `CanonicalDeepTwistConfig` body (`…ChapI.lean:725-748`):
  `CanonicalLadderConfig … ∧ True` → `CanonicalLadderConfig … ∧ ∃ (dom : IsDomain O)
  (dvr : IsDiscreteValuationRing O), …C130s18.DeepTwistRealizationData.{0, uG, uKt, uL}
  (dom := dom) (dvr := dvr) C B G Kt L N v ρ q A R w r n`.  The frozen refinement shape is
  byte-preserved (first conjunct still literally `CanonicalLadderConfig`, so I.10b → I.10a
  stays `And.left`); the whole body is definitionally C130s18's `CanonicalDeepTwistConfigData`
  (`Iff.rfl` pin).  A-I.2(b)'s `r`-pin demand is now REAL: the joint witness carries
  `core.r = r` inside `DeepTwistRealizationData`.
* **Universe pin, disclosed in-file** (section disclosure at `…ChapI.lean:648-658`): the
  existential-ambient universe is pinned to `0`.  Forced: a `Prop` cannot quantify over
  universes, and a NEW socket universe parameter would be an unconstrained metavariable at
  `CapstoneHypotheses`' byte-frozen field sites (the fields apply the sockets with no universe
  annotation), un-elaborating the frozen structure.  `0` is the universe of every arising
  instance (`E` is built from `O : Type`; at S2, `E := FractionRing (Polynomial O)`) and the
  exact level C130sg's socket applications use (`.{0, uG, 0, uL}`).
* **Non-swallowing fence checked** (disclosure at `…ChapI.lean:659-670`): the bodies constrain
  the CONFIGURATION only; C130s18's mechanized §5 audit (`arenaAgreement_not_uniform`,
  `embeddedValue_not_uniform`) proves no uniform-in-context derivation of either landed trap's
  clause exists.  Unpacking a socket leaves the OM-8 L3 goal — reachable, not supplied.

**BYTE-FREEZE VERIFIED** (git diff -U0, deleted-line audit): `CapstoneHypotheses`' field list,
`UniformityStatement` mentions, and I.15–I.18's statements have ZERO deleted/changed lines.
The 27 deleted lines are exactly: the two `True` bodies, gate items (10)/(11)'s code, the
BLOCKED prose paragraphs (re-added struck `~~…~~` per the A-I.1 convention), two census rows
(re-added amended), and RESUME item (iii) (re-added struck+DONE).

**Gate ripples (the §4 gate, all EXECUTED):**

* item (10) — the I-D13 refutation `¬ CapstoneHypotheses n` via `trivial` — **STRUCK, text and
  term preserved verbatim in comments** (`…ChapI.lean:981-1002`): it NO LONGER ELABORATES,
  which is the amendment's content.  **Defect I-D13's contradiction is LIFTED**: the block is
  no longer provably empty by that route.  NOT claimed: inhabitation (`a0`/`a1` open at
  `n ≥ 3`; supply at arising configurations open; weld debts untouched).
* item (11) — the guarded=unguarded equivalence — **RETIRED to its surviving weakening
  direction** (unguarded ⟹ guarded, `…ChapI.lean:1004-1031`).  **The owner-gate-(a) narrowing
  A-I.1 pre-flagged has now HAPPENED** (weaker hypothesis ⟹ stronger I.15–I.18); re-flagged
  in `docs/REVIEW_QUEUE_2026-08-26.md`'s Tier-2 table, row A-I.3 (top).
* NEW item (15) — two `Iff.rfl` anti-drift pins: the sockets ARE the C130s18 carriers,
  definitionally (`…ChapI.lean:1059-1080`).
* NEW items (16)/(17) — **the S2 non-vacuity teeth** (`…ChapI.lean:1082-1123`): the landed
  SG-1 socket applications `C130sg.s2Frontier_ladder_socket` / `s2Frontier_deepTwist_socket`
  inhabit the re-signed sockets at the concrete `keyAt 2 + 1` occurrence, degree 4, depth
  pinned to the witness's own `r = 2` — conditional on exactly `w : S2LevelOneThreshold` +
  `IsAdicComplete` (no provably-empty premise).  Needed one plumbing import:
  `import Uniformity.ChapC.C130sg` (`…ChapI.lean:40`, dated comment).
* Census rows updated (33 examples + 8 #checks; the I.15–I.18 row's "conditionally VACUOUS"
  annotated lifted); STATE UPDATE paragraph added to the header; I.10 structure header and
  RESUME item (iii) annotated.  Prose-only sites keep their dated historical text.

**Amendment record:** `docs/REVIEW_QUEUE_2026-08-26.md`, Tier-2 amendment table, new top row
`A-I.3 | … | RSGN, 2026-08-26` (the same table carrying A-I.2/A-C.16; newest-first convention).

## STAGE 2 — the leanfinal landing (ONE new file)

**NEW `leanfinal/Uniformity/ChapI/I10_I15_I18.lean`** (namespace `Uniformity.Density`, GC-6.2
flat; statements transcribed BYTE-FROZEN from the A-I.3-amended leanspec):

* `CanonicalLadderConfig` / `CanonicalDeepTwistConfig` — the A-I.3-typed sockets (bodies
  byte-identical to leanspec's, same universe pins and dated comments).
* `CapstoneHypotheses` (I.10) — field list byte-identical to A-I.1's signed form, including
  the ⚠ `jd0 : True` / `genhnBox2 : 6 ≤ n → True` placeholder comments.  The `ns7` field binds
  leanfinal's I01 carrier, whose body was RESOLVED 2026-08-24 against the A-C.6 redraft — the
  theorems below never consume `ns7Termination_of_cite`, so no cite enters any footprint here.
* I.15–I.18 — statements and proofs byte-identical to leanspec's (both sides land them REAL;
  the `towerLocus_iff_budget` byte-discipline, with no axiom→theorem keyword to convert).
* Gate section: the `a2` projection check, the I.10b→I.10a refinement (5a), both `Iff.rfl`
  body pins, and both S2 non-vacuity teeth (items (16)/(17) mirrored).
* Honesty fence honored and documented in the module docstring: block OPEN (not provably
  empty, NOT claimed inhabited); `jd0`/`genhnBox2`/`w1`/I-D12 placeholders carried verbatim,
  discharged nowhere; defect I-D10 recorded unchanged.

**NOT wired into `Uniformity/ChapI.lean`'s roll-up import list** — per the PK12 precedent,
roll-up wiring is the orchestrator's.

## STAGE 3 — verification

| gate | result |
|---|---|
| `lake env lean Leanspec/ChapI.lean` (leanspec) | **exit 0**, zero errors/warnings (`/tmp/rsgn_amended_chapI2.log`) |
| `lake build Leanspec.ChapI` (leanspec) | **green** — "Build completed successfully (9241 jobs)"; the file's 70 in-file `#axiom_core` guards (incl. `CanonicalLadderConfig`/`CanonicalDeepTwistConfig`/`CapstoneHypotheses`/I.15–I.18) ENFORCE Lean-core on build |
| leanspec importers of ChapI | **none** (grep: only the commented `-- import Leanspec.ChapI` in `leanspec/Leanspec.lean:24`) |
| `lake env lean Uniformity/ChapI/I10_I15_I18.lean` (leanfinal) | **exit 0**, zero warnings, zero sorry |
| `lake build Uniformity.ChapI` (leanfinal) | **green** — "Build completed successfully (8710 jobs)" (only the pre-existing roll-up header-linter note) |
| byte-freeze diff audit | **pass** (deleted-line audit above) |

**AxChk footer (leanfinal file, `#print axioms`, all seven):**

```
'Uniformity.Density.CanonicalLadderConfig'              [propext, Classical.choice, Quot.sound]
'Uniformity.Density.CanonicalDeepTwistConfig'           [propext, Classical.choice, Quot.sound]
'Uniformity.Density.CapstoneHypotheses'                 [propext, Classical.choice, Quot.sound]
'Uniformity.Density.drainage_of_capstoneHypotheses'     [propext, Classical.choice, Quot.sound]
'Uniformity.Density.decided_of_capstoneHypotheses'      [propext, Classical.choice, Quot.sound]
'Uniformity.Density.uniformity_of_capstoneHypotheses'   [propext, Classical.choice, Quot.sound]
'Uniformity.Density.totalMassOne_of_capstoneHypotheses' [propext, Classical.choice, Quot.sound]
```

Exactly Lean core — no declared cite anywhere on the path (I.17's design point, now landed).

## Incidents + notes for the orchestrator

1. **Stale-olean incident, RESOLVED in the shared build tree.** leanspec requires leanfinal by
   path, so `leanfinal/.lake/build` is the ONE build tree.  `C130sg.olean` there was
   PRE-PK12 (its `s2Frontier_ladder_socket` still carried the retired `ev`/`lf` premises and
   the old universe arity — C130sg is in NO roll-up, so PK12's four gates never rebuilt it;
   PK12's per-file AxChk used `lake env lean`, which writes no olean).  First elaboration of
   the amended ChapI failed on the S2 teeth with "incorrect number of universe levels" against
   the mixed environment.  Fix: `lake build Uniformity.ChapC.C130sg` (leanfinal) — **green,
   8785 jobs**, every C130sg footprint row Lean-core (build-artifact refresh only; zero source
   edits outside this unit's sanctioned files).  Re-elaboration then green everywhere.
2. **Owner-review flag (gate (a)):** A-I.3 is the narrowing event A-I.1 pre-flagged — the
   Display-A `ladder`/`deepTwist` fields are now demanded at the ARISING configurations only.
   Enacted under the standing statement-change authority; flagged as the top Tier-2 row of
   `docs/REVIEW_QUEUE_2026-08-26.md`.
3. The leanfinal landing means several dated leanspec/notes sentences ("chapter I has landed
   nothing in leanfinal", "no fleet agent may fire on I.10") are now historical; the ChapI
   header's A-I.3 STATE UPDATE says so explicitly.  `Leanspec.lean:24`'s commented
   `import Leanspec.ChapI` (the I-D1 workaround) may now be un-commentable — I-D1 appears
   CURED at HEAD (D62w imports D55/D62/D63 instead of re-declaring; the ChapC roll-up +
   E24 coexist in ChapI's import set).  NOT touched (outside scope); left to a later unit.
4. Files touched (complete list): `leanspec/Leanspec/ChapI.lean` (amendment),
   NEW `leanfinal/Uniformity/ChapI/I10_I15_I18.lean` (the one landing file),
   `docs/REVIEW_QUEUE_2026-08-26.md` (one row), this verdict.  No commits (orchestrator wires).
   `leanfinal/scratch/RSGN_check.lean` was not needed (probes ran from `/tmp`).

## What is now true (the honest bottom line)

* The leanspec I.10a/I.10b sockets are TYPED, non-vacuously inhabitable (S2 teeth), and
  anti-drift-pinned to chapter C's enacted carriers; the I-D13 contradiction is LIFTED.
* All four capstone-assembly theorems (I.15–I.18) are LANDED in leanfinal with Lean-core
  footprints: `UniformityStatement` / `UniformityStatementDecided` / `∀ n, DrainageAt n` /
  `TotalMassOne` each follow from `∀ n, CapstoneHypotheses n` and nothing else.
* NOT claimed: any inhabitant of `CapstoneHypotheses n` (a0/a1 open at `n ≥ 3`; ladder/
  deepTwist supply at arising configurations open; `jd0`/`genhnBox2`/`w1` debts open), and no
  positive unconditional claim from I.17 beyond its footprint.
