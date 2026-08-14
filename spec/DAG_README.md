# PHASE-0c — THE GLOBAL DAG (DRAFT)

**Status: PLANNING ARTIFACT. Opus-drafted 2026-08-14/15. CODEX CROSS-READ OWED**, like
every 0a/0b artifact of this week (`docs/PROJECT_STATE.md` appends #51, #53). Nothing here
proves anything; nothing here is a mathematical claim. It is an *assembly* of edges the
0a effective specs, the 0b hypothesis ledger and the landed `leanfinal` API already
record, plus the measurements the 0c charge asks for.

Charge: `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md` REVISION 2, stage **0c**
("GLOBAL DAG + CHAPTER CUT", fixes B3/R14/R16).

## Files

| file | what it is |
|---|---|
| `spec/DAG.tsv` | the edge list. Contract columns `from-ID, to-ID, edge-kind, chapter, status`, then four provenance columns this draft adds: `edge-class, resolution, kind-basis, evidence` |
| `spec/DAG_NODES.tsv` | the node table: `id, node-kind, note, unit-type, class, chapter, status, source` |
| `spec/DAG_NONIMPORTS.tsv` | the recorded negative-import fences (template v2 rule 3), so they are *checkable* rather than decorative |
| `spec/dag_build.py` | the assembler that produced all three (run from the repo root) |
| `spec/dag_check.py` | the checker: dangling IDs, cycles, capstone reachability, layering, chapter cut, fences, resolution census |
| `spec/dag_check_output.txt` | the committed checker output at HEAD |

Reproduce: `python3 spec/dag_build.py && python3 spec/dag_check.py`.

## Edge direction (read this before reading the TSV)

`from-ID` is the **consumer / dependent**; `to-ID` is the **supplier / dependency**. An
edge `A → B` reads *"A depends on B; B must land first."* Consequently the capstone
**reaches** everything it rests on, and layer 0 of the topological layering is terminal
supply (the landed Lean kernel and the leaf lemmas), not the capstone.

## Node vocabulary

| prefix | count | meaning |
|---|---:|---|
| `EFF.<NOTE>.<nn>` | 2,227 | a 0a statement unit. `EFF.<NOTE>.s<k>of<m>.<nn>` for the two notes with no merge file (see below) |
| `HYP.<nn>` | 149 | a 0b hypothesis-ledger row |
| `lean:<decl>` | 34 | a landed `leanfinal` declaration (CN-01..23 + the P1–P5 landings + the two capstone Props). Status **DONE** — terminal supply |
| `CAP:UniformityStatement`, `CAP:UniformityStatementDecided` | 2 | the capstone targets |
| `COND:<conjunct>` | 3 | a frozen Display-A conjunct that matched no ledger row — a *finding*, not a node the corpus declares |
| `EXT:<file>` | 34 | a note cited by the specs that has **no 0a effective spec**. Outside the chapter cut by construction |

**Spec inventory recount (a tally discrepancy, booked per template rule 39).** Append #53
records "28 consumption-ready specs (12 merged multi-shard + 16 full singles)". A literal
recount of `spec/EFF-*.md` at HEAD gives **11 files headed `(MERGED)` + 17 full singles =
28 files**, covering 28 of the **30** compiled notes. `GENTOW5` and `W12` exist only as
shard pairs (`EFF-GENTOW5-s{1,2}of2.md`, `EFF-W12-s{1,2}of2.md`) with shard-local ID
namespaces and no merge run. Both figures are recorded here; neither is silently
substituted for the other. The DAG carries GENTOW5's and W12's units under their
**shard-local IDs** — a downstream merge will renumber them, and every edge touching them
will need remapping.

## Edge classes and how complete each one is

| class | n | source | completeness |
|---|---:|---|---|
| `xref` | 1,172 | the specs' §XREF / consumption tables: a home unit `.NN` plus a `<target note>:<designation>` pair | **spec-recorded.** Complete relative to those tables; the tables themselves are grep-verified by 0a |
| `reverse-xref` | 165 | reverse-XREF rows ("who consumes this note", template rule 8) | spec-recorded; the *consumer-side* endpoint is usually COARSE (see below) |
| `ledger-path` | 214 | the 0b ledger's own scope sentence — every surviving row is a condition on the capstone path | recorded, but a scope-level edge, not a proof-level one |
| `ledger-loc` | 68 | a HYP row's `WHERE:` field resolved to a unit | partial: many rows point at `leancheck`/`leanfinal` notes with no 0a spec |
| `ledger-cond` | 36 | Display A's frozen conjuncts matched to ledger rows | 3 conjuncts unmatched (below) |
| `ledger-discharge` / `cn-discharge` | 15 / 14 | a `DISCHARGED` stamp, or a certain-node's own HYP reference, to the landed declaration | recorded |
| `supersession` | 8 | `TARGETS:` / `CHAIN:` fields (template rules 24, 25) | **known-incomplete**: the fields exist at ~96 + 78 sites but most name spans in prose rather than unit IDs |
| `ledger-index` | 8 | a note citing its own row in the ledger | **not a dependency** — excluded from every graph computation, kept as provenance |

### THE BIG KNOWN-INCOMPLETE: no intra-note dependency edges exist

The 0a specs record, per unit, a CANONICAL STATEMENT, a DERIVATION, a CONDITIONALITY, a
RESOLUTION TRACE and TEETH. They do **not** record "unit `.14` depends on unit `.09`."
A census of the whole corpus finds essentially zero `EFF.<NOTE>.<nn>` cross-references
inside unit bodies (GENIND: 206 ID occurrences against 206 unit headings — i.e. the
headings themselves and nothing else).

The 0c charge forbids inventing edges ("you are ASSEMBLING recorded edges"), and a
designation-scan over statements and derivations would be exactly that. So this DAG
**has no intra-note edges except the recorded supersession chains**, and the consequence
is measured, not hidden:

* **1,599 of 2,449 nodes (65%) are isolated** — they carry no recorded edge at all.
* Only **850 nodes** sit in the edge-bearing subgraph.
* Capstone reachability is **540 nodes (22.0%)**; of the 1,909 unreachable, 1,599 are
  isolated and only **310 are connected-but-unreachable** — that last set is the real
  candidate out-of-cone list, and even it is contaminated by the missing edges.

**This is the single most consequential finding for the chapter blueprints:** the
statement-level dependency structure *inside* each note does not exist anywhere in the
repo yet. Each chapter blueprint must derive it from the note, and the blueprint stage is
where it gets written down for the first time. The DAG cannot be "completed" by a better
parser.

## Resolution flags — how provisional each edge is

`resolution` reads `from:<how>,to:<how>` with:

* `exact` — the endpoint is a unit ID the source table names literally;
* `stmt` — a designation resolved to the unit whose CANONICAL STATEMENT carries it
  (earliest math-typed unit wins);
* `body` — resolved only outside the statement;
* `ledger` — resolved to a `HYP.<nn>` row;
* `ext` — the target note has no 0a spec;
* **`gov` — COARSE.** The designation named a whole note, or resolved nowhere, so the edge
  lands on that note's **governing unit**, chosen by a documented placeholder rule: *the
  note's first `[theorem]` unit, else its first `[lemma]`, else its first `[definition]`,
  else `.01`.* This is a placeholder, not a claim about what the note's principal theorem
  is.

**647 of 1,700 edges (38.1%) are COARSE.** Every one is a cross-read item.

### edge-kind is only classified where rule 3 could actually be applied

The charge's rule 3 (stmt-dep if the *statement* references the target, proof-dep if only
the *derivation* does) is applied mechanically: the cited designation is searched in the
source unit's own CANONICAL STATEMENT + CONDITIONALITY first, then its DERIVATION (with a
second try after stripping a leading `LEMMA`/`THEOREM`/… keyword). That succeeded for
**439 edges** (431 statement-hits, 8 derivation-hits). The remaining **1,261 edges default
to `stmt-dep`, which is a default and not a classification** — `kind-basis=default` marks
them.

The 431:8 ratio is itself a corpus fact worth the cross-read's attention: in the 0a specs,
cross-note citations sit overwhelmingly in statement text, because the units' DERIVATION
fields are short verbatim proof quotes (median 367 characters for lemma/theorem units,
against a median 1,277-character statement).

## Cycles, and the adjudications

Two graphs are analysed separately, because they answer different questions.

**The EXACT-resolved subgraph (1,050 edges, no COARSE endpoint) has exactly four
non-trivial SCCs**, all small, all adjudicated in `dag_check.py`:

1. `EFF.HE7.{128,129,130}` — HE7's own "HE7 itself (inbound)" ledger rows are read as
   both forward and reverse edges. A direction ambiguity in the source table, not a
   mathematical cycle.
2. `EFF.GENIND.136 ↔ EFF.HEX3.37 ↔ EFF.HMENU3.33` — `HEX3-BOX-1` (the tail-σ certification
   lemma, ledger `HYP.137`) is supplied by HEX3 and consumed by GENIND and HMENU3; HEX3's
   own §4.3 puts supplier and consumer rows under one heading, so one consumer edge is
   read backwards.
3. `EFF.GRTW2.20 ↔ EFF.LIFTCORNER.72` and 4. `EFF.GRTW2.35 ↔ EFF.LIFTCORNER.62` — genuine
   **MUTUAL-RECON pairs**: LIFTCORNER's XREF ledger cites GRTW2's `W2-OPEN-1`/`W2-OPEN-2`,
   and LIFTCORNER's shard-1 reverse-XREF table lists GRTW2 as a consumer of those same
   units. Both directions are recorded. The chapter blueprint must decide which direction
   is the statement dependency; this draft does not.

**The full graph, COARSE edges included, has 7 non-trivial SCCs, the largest of size 78.**
Those are **COARSE-GOV artefacts**: a coarse edge lands on the target note's single
governing unit, so any two notes that cite each other collapse into a 2-cycle regardless
of the mathematics. Cycles that appear only in the full graph are not evidence of mutual
dependence and are reported as such.

**The `HE6 ↔ HE6R1` pair the charge flags: not a statement-level cycle.** The two notes do
cite each other (HE6 → HE6R1 on 15 recorded exact edges, HE6R1 → HE6 on 3), but in the exact
subgraph those land on **disjoint units**, so no unit-level cycle survives. The
mutual-recon flag is a note-level phenomenon here.

## Reachability and the ledger's NOT-REACHED dispositions

Capstone-path edges are drawn from the ledger's own scope sentence ("surviving conditions
on the path from `leanfinal`'s `UniformityStatement`"), so a row gets a capstone edge
**unless the ledger itself stamps it CLOSED/DISCHARGED/MERGED, or signs it NOT-REACHED /
"record OUT of the cone" / "verified UNREACHABLE" / OUT-OF-PATH-BY-POLICY.**

Consistency check, run automatically: the seven rows the weld-face audit and ORPHAN-1
signed out of the cone — `HYP.21`, `HYP.75`, `HYP.76`, `HYP.83`, `HYP.84`, `HYP.85`,
`HYP.86` — are **all unreachable from the capstone in the graph**. Consistent, 7/7.

That check earned its keep once already: a first pass matched Display A's `JD0-BOX-2`
conjunct to `HYP.76` (whose CONSUMED-BY prose mentions `JD0-BOX-2` while *denying* the
reach) and the checker flagged the resulting reachability as INCONSISTENT. The matcher now
skips off-cone rows and prefers title matches. The conjunct's real home is `HYP.39`.

**Three Display-A conjuncts still match no ledger row: `A1_n`, `A2_n`,
`(H-e)-window-pinning`.** They are carried as `COND:` nodes. `A0_n[disc≠0]` does match.
For the cross-read: either the ledger lacks a row for the A1/A2 conjuncts under those
names, or they are named differently there — the frozen capstone display should not carry
a conjunct with no ledger row.

## Layering and the parallelism ceiling

SCCs collapsed, longest-path layering, layer 0 = terminal supply:

| layer | nodes | connected nodes |
|---:|---:|---:|
| 0 | 1,980 | 381 |
| 1 | 174 | 174 |
| 2 | 29 | 29 |
| 3 | 43 | 43 |
| 4 | 82 | 82 |
| 5 | 125 | 125 |
| 6 | 11 | 11 |
| 7 | 2 | 2 |
| 8 | 1 | 1 |
| 9 | 2 | 2 |

**Max layer width = 1,980 nominal, 381 on the edge-bearing subgraph.** The nominal figure
is an artefact of the isolated nodes all landing in layer 0; **381 is the honest reading**,
and even that is an upper bound on parallelism, never a throughput promise (REVISION 2,
R15: report the critical path, and never let stragglers block ready descendants).

## THE CHAPTER CUT

The v1 B–J cut is recorded by the design as known non-topological. This one is read off the
computed condensation, by this method:

1. dependency graph = `DAG.tsv` minus the `ledger-index` class;
2. note-level condensation of the **EXACT-resolved** subgraph, with each external note kept
   distinct (collapsing them into one `EXT` hub manufactures cycles). That condensation is
   clean: four small mutual clusters — `{GRTJA,GRTJB}`, `{GENIND,HEX3,HMENU3}`,
   `{HE3,HE6,HE6R1,HE7}`, `{GRTW2,LIFTCORNER}` — over a 7-layer DAG;
3. chapters are formed so that no mutual cluster is split, the landed Lean kernel is the
   bottom, and the ledger/capstone layer is the top;
4. the two **HARD** chapters are isolated per append #52's fork plan: the σ-ladder master's
   carrier suite, and the tower grammar;
5. the chapter order is then chosen to minimise the weight of edges running against it
   (exhaustive over orders, 9 chapters).

| ch | name | notes | nodes | |
|---|---|---|---:|---|
| **I** | CAPSTONE AND CONDITIONALITY | `HYP.*`, `CAP:*`, `COND:*` | 154 | |
| **E** | **σ-LADDER MASTER** | `T2` | 105 | **HARD** — the carrier suite |
| **D** | GAUGE + CERTIFICATE T-CHAIN | `T1, T3, T4, T5` | 181 | |
| **C** | **TOWER GRAMMAR** | `GENTOW1, GENTOW3, GENTOW4, GENTOW5, GENTOW6, HETOW` | 363 | **HARD** |
| **B** | HENSEL-SLOT CORE | `HE3, HE6, HE6R1, HE7` | 319 | contains the mutual-recon cluster |
| **H** | GENERAL INDUCTION | `GENIND, GENHN, GENH4, W12` | 498 | |
| **F** | GRT WELD LAYER | `GRTJA, GRTJB, GRTJC, GRTW2, WELDMASTER, LIFTCORNER, SIGMALAW` | 538 | |
| **G** | BASE CASES AND MENUS | `HMENU3, HEX3, W11, JD0` | 223 | |
| **A** | LANDED LEAN KERNEL | 34 `lean:` declarations | 34 | **DONE** — terminal supply |

Order, consumer-first: **I > E > D > C > B > H > F > G > A.**

The dominant flows that fix this order: `H→G` 189, `B→H` 65, `H→F` 42, `E→B` 42, `I→D` 34,
`D→C` 31, `I→A` 29, `I→H` 29.

### The cut is not strict, and here is exactly how much

**603 cross-chapter dependency edges; 57 of them (9.5%) run backwards.** Every backward arc
is a place where a chapter blueprint will have to split a note at unit granularity:

| arc | weight | what it is |
|---|---:|---|
| `G → H` | 13 | HEX3/HMENU3 units cite GENIND's induction frame back |
| `H → B` | 12 | GENIND/GENHN cite HE-core results while the HE core consumes GENHN's slot layer — **the clearest mandated split: GENHN's stage/slot infrastructure belongs below chapter B, its count/tower results above it** |
| `C → E` | 11 | tower notes cite T2 |
| `B → E` | 8 | HE-core units cite T2 |
| `H → D`, `C → D` | 4, 4 | induction / tower notes cite the T-chain |
| `H → C` | 3 | |
| `F → B`, `F → D` | 1, 1 | singletons |

A further **114 dependency edges have an endpoint outside the cut** (an `EXT:` note).

## External notes with no 0a effective spec (34 `EXT:` nodes)

The specs cite these files; none has an effective spec, so none can be consumed the way the
28 can. The mathematical ones are the load-bearing list:
`GENTOW2_PROOF`, `ITERLAWN_PROOF`, `ITERLAWLIFT_CORNER`, `RMENGINE`, `DULEMMA_PROOF`,
`DITERSUP_STMT`, `W10_PROOF`, `GRB_ORDER2`, `ILNRES`, `LEDGERLAMBDA`, `WELDZERO`,
`GRT_WELD_BLUEPRINT`, `QSCOUT22`, `N3_CHECK`. (The rest are ledgers, pass reports and
project records: `HYPOTHESIS_LEDGER`, `PROJECT_STATE`, `SOL_CERTIFICATION_LEDGER`,
`TIGHTNESS_CENSUS`, the `CODEX_*RAT`/`*PE1` pass reports, `WELD_FACE_AUDIT`,
`WELD_SYNTHESIS`, `SIMPLIFICATION_BLUEPRINT`, `BRIDGE_ADJUDICATIONS`,
`LEAN_SCOPING_consumption_map`, the `GENTOW2_pass*` reports, three attempt/verify briefs.)
`EXT:EFF-T1*.md` is a glob written as a citation in a source table, not a file — a parse
artefact worth one line of the cross-read.

## Non-import fences

121 fence rows over 90 fenced units, extracted from the specs' NON-IMPORTS sections. A
note name is treated as *banned* only when it appears in a table cell that also states a
prohibition ("not", "no", "never", "excluded", "absent", "free of").

`dag_check.py` reports **82 recorded edges that cross a recorded note-level fence.** A hit
is **not automatically a defect**: a fence names material the note does not *import*, while
an edge may be a citation of record or a fence stated at a different granularity than the
edge. Each hit is a cross-read question. The largest clusters are GENIND → W12/GENH4 and
GENTOW5 → GENHN.

## What is complete, and what is not

**Complete (spec-recorded, assembled without judgement):**
* every XREF / consumption / reverse-XREF table row in all 28 consumption-ready specs and,
  for the merged notes whose merge summarises rather than tabulates (GRTJB, GRTJC), the
  three shard files each, with shard-local IDs remapped through the merge's own SHARD-MAP;
* every ledger row, its capstone-path status, its `WHERE` location and its discharge stamp;
* the 23 certain-nodes and the P1–P5 landings, verified to exist as declarations in
  `leanfinal/Uniformity/`;
* Display A's frozen conjunct list.

**Known-incomplete, in descending order of how much it matters:**
1. **No intra-note statement-level dependencies exist** anywhere in the corpus (68% of
   nodes isolated). The chapter blueprints write these for the first time.
2. **38% of edges are COARSE**, landing on a placeholder governing unit.
3. **1,261 of 1,700 edges carry a defaulted `edge-kind`**, not a classified one.
4. **The HE6 / T2 adjudication is pending** — `spec/EFF-HE6.md` OPEN-CALL 2 (three A3
   corrections outside every T2 pin span; F-1 renders `HE6-SLOT-SEAM`'s frozen slot residue
   vacuous while T2 cites it 48×). The adjudication unit was launched before the DAG
   consumed T2's spec (append #53). All nine HE6 pin units of `EFF-HE6.md` §4.1 —
   `.09 .13 .14 .15 .17 .29 .30 .32 .56` — are present as T2 → HE6 targets (11 edges), but
   **every one of them originates at the COARSE T2 governing-unit placeholder
   `EFF.T2.31`, not at the T2 unit that actually consumes the pin**, and all of them are
   drawn as the specs record them today and will move if the adjudication moves them.
5. **WELD-ZERO's arc is pending** (`HYP.149`, IN-PROGRESS; `EXT:WELDZERO_2026-08-14.md` has
   no spec). Its edges are placeholders.
6. **GENTOW5 and W12 are unmerged**; their unit IDs are shard-local and will be renumbered.
7. **`supersession` edges are almost entirely unharvested** (8 recorded against ~174
   `TARGETS:`/`CHAIN:` field sites).
8. The `A1_n`, `A2_n`, `(H-e)-window-pinning` conjuncts match no ledger row.

## Flagged for the codex cross-read

1. The intra-note-edge gap (finding 1 above) — is deriving it per chapter the right plan,
   or should a 0c′ pass extract it from the DERIVATION fields under an explicit
   inference licence?
2. The four adjudicated SCCs, especially the two GRTW2 ↔ LIFTCORNER mutual-recon pairs:
   which direction is the statement dependency?
3. The 647 COARSE edges, starting with the highest-fan-out governing-unit placeholders
   (`EFF.GENHN.07` 99 edges, `EFF.HE7.13` 67, `EFF.HE3.16` 48, `EFF.T2.31` 44,
   `EFF.W12.s1of2.09` 44, `EFF.GENTOW5.s1of2.06` 42).
4. The 82 fence crossings.
5. The chapter cut's 57 backward arcs, and specifically the GENHN split that `H → B`
   demands.
6. The three unmatched Display-A conjuncts.
7. The 14 mathematical `EXT:` notes with no effective spec — do any of them carry a
   load-bearing statement the capstone rests on?
8. The 11-merged/17-single recount against append #53's 12/16.
