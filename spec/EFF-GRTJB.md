# EFF-GRTJB — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: sonnet (2026-08-14, Asvin-authorized PHASE-0a sweep, the campaign's final two merges) —
mixed provenance carried forward from all three shards (each independently stamped
`opus, 2026-08-14, PROJECT_STATE #51`). CODEX CROSS-READ OWED (post-reset) — none of the
three shards, and no fold performed by this merge run, has been through an adversarial
pass; that obligation is inherited whole. This merge follows the EFF-HE7/EFF-GENIND
established pattern for tag-sparse three-shard prose notes: contiguous renumbering via a
mechanically-verified, context-tracking rewrite script (not hand-transcription), a
blob-hash cross-check as the STOP condition, dedup-marked consolidation, and a fresh
sample re-verification.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` (3327 lines, 240,219 bytes).

**HEAD blob hash:** `69e859326ca58c3f96933714f7299835867f6531` — cited identically by all
three source shards' headers (each also recording the file's last-touching commit as
`68a993fa`, "SOL cert E3 FOLDED: GRTJB"), and independently confirmed by fresh
`git hash-object` against the working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GRTJB_PROOF_2026-08-08.md
69e859326ca58c3f96933714f7299835867f6531
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` at HEAD (v2 rules 1–10; v3 rules 11–28).

**Merged from:** `spec/EFF-GRTJB-s1of3.md` (HOME lines 1–1302; 80 statements, 56 xrefs,
5 open calls), `spec/EFF-GRTJB-s2of3.md` (HOME lines 1303–2457; 60 statements, 68 xrefs,
5 open calls), `spec/EFF-GRTJB-s3of3.md` (HOME lines 2458–3327; 33 statements, 23 xrefs,
5 open calls). **173 statements, 147 raw XREF citations, 15 raw open calls total before
merge-time dedup.** This file supersedes the three shards as the citable unit for all
downstream consumption; any consumer citing `EFF.GRTJB.*` from this point on cites the
contiguous IDs below, not the shard-local `EFF.GRTJB.sKof3.*` IDs. The three shard files
are **not deleted** — they remain the run-of-record trace of the sharded compilation, and
in particular remain the place where each unit's own §6 BOUNDARY SELF-AUDIT entry lives
in full; this merged file's §7 carries forward only the format-level conclusions (the
SERIES, the CHAINs, the consolidated edge list), not the per-boundary reasoning.

### The manifest-4-vs-3-ranges OPEN-CALL (carried forward, not resolved by this merge)

`runs/qgen/sweep_manifest.txt` shards GRTJB into **FOUR** ranges (1–170, 171–1302,
1303–2457, 2458–3327); the compilation charge names **THREE**. Shard 1's own header
records the resolution it applied: **the manifest's rows 43+44 (1–170 front matter +
171–1302 §0M) were MERGED into shard 1** — "170 lines of front matter that cannot stand
alone as a spec; its natural home is the same shard as §0M, which regenerates every grade
surface the front matter announces" — while rows 45 and 46 stood unchanged as shards 2
and 3. Union = 1–3327, no line compiled twice, none dropped; both merge boundaries verified
at source-line section breaks (L1301/1302/1303, L2456/2457/2458). **This is a documented
compiler decision, not a silent one, and shard 1's own OPEN-CALL 1 keeps it open**: whether
a *merge* run (as opposed to a *shard* run) should treat GRTJB as 3-shard or 4-shard in its
ID scheme is a question this file inherits unresolved — carried below as OPEN-CALL 1.
**Contrast, load-bearing for the companion GRTJC merge:** GRTJC's own manifest split falls
into the SAME four-vs-three shape, but its shards resolved it by merging the excess range
at the **back** (the annex tail merged into shard 3), not the front — GRTJC's shard 1 says
so explicitly ("Note the deliberate contrast with GRTJB, where the merge fell at the
FRONT"). Both resolutions are honest and neither is silently harmonized here.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–80, is already contiguous from 1).
Shard 2 carries a **+80** offset (01–60 → 81–140). Shard 3 carries a **+140** offset
(01–33 → 141–173). Every `EFF.GRTJB.sKof3.NN` occurrence — full form, the file-path form
`` `spec/EFF-GRTJB-sKof3.md` `` used as a citation lead-in, the bare backtick shorthand
`` `.NN` ``, and the label-embedded form (`CHAIN HOME: s1of3.NN`, `CHAIN-MEMBER: sKof3.NN`)
— has been mechanically rewritten by a context-tracking script (not hand-transcription),
under the following disambiguation rule:

> **A bare `` `.NN` `` reference is resolved against the shard most recently named by a
> full-form or file-path citation earlier in the same reset-scope; absent any such prior
> citation, it resolves against the unit's own home shard.** Reset-scopes are unit
> boundaries (`### EFF.GRTJB.sKof3.NN` headings), blank-line-delimited paragraph blocks,
> and bullet/table-row/bold-field-label line starts within a block — finer-grained than
> HE7's own whole-unit-persistence rule, chosen because this note's SHARD NOTES sections
> pack many independently-targeted citations into one bulleted block.

Two "range" headings in this note (`s1of3.03 — .10`, the eight-member `S-STATUS` SERIES,
and `s1of3.58 — .65` / `s1of3.68 — .71`, the r4/r5 disposition batches) are genuine
combined single blocks — no separate sub-heading exists per member, so the block claims
the whole numeric range. A third, `s3of3.24 — .31` (the post-freeze append arc), is a
**zero-width SERIES OVERVIEW**: it is immediately followed by individually-headed units
`.24` through `.33` (ten units, not eight — the heading's own endpoint under-states its
true reach by two, a minor source label imprecision noted here and not silently
corrected), so the overview text was folded as a preamble onto unit `.24` and claims no ID
of its own — matching the sibling convention GRTJC states explicitly for its own analogous
series ("the series header occupies no ID of its own").

The rewrite was performed **mechanically** (a Python context-tracking script operating on
each shard's own "## 2. Statement inventory" section, offsets applied by shard, an
EXTERNAL-note guard verified unnecessary here since GRTJB's own shards never cite another
sharded note by short form) and then audited: **zero leftover `sKof3` substrings anywhere
in the merged statement inventory (§3)**, **zero out-of-range renumbered IDs** (every
resolved ID lies in 1–173), and the ID sequence covers 1..173 exactly once with no gap and
no duplicate (script-verified, not hand-counted). See §8's fidelity audit for the sample
re-verification against source.

| shard | local range | offset | merged range |
|---|---|---|---|
| s1of3 | 01–80 | +0 | 01–80 |
| s2of3 | 01–60 | +80 | 81–140 |
| s3of3 | 01–33 | +140 | 141–173 |

### Header unification and blob-hash check

All three shards' front matter carries the identical compiled-by/cross-read-owed stamp
(reproduced above) and the identical HEAD blob hash; shards 2 and 3 additionally cross-cite
it as identical to shard 1's, a three-way mutual confirmation this merge re-verified
against the working tree rather than trusting the shards' mutual citation alone.

### Governing effective-text record (unified from all three shards; THREE independent
freeze predicates, per rule 21 — never conflated)

**FREEZE PREDICATE 1 — INSTRUMENT FREEZE.** Four machine scripts byte-frozen across all
eight repair rounds, re-verified at every round and independently re-verified by this
compiler at merge time — **4/4 md5s EXACT at HEAD**:
`grt_jb_checks.py` (`55f4911eaddd8524fd91368b30ed71bd`), `grt_jb_printwalk.py`
(`f53e23e8d1c79f084a1e34eee857e37c`), `grt_jb_r1_levelcensus.py`
(`2bcb44fdbf839d367f0e11033a5d3fd7`), `grt_jb_printwalk2.py`
(`6c6318f7fc6570a2d454389b38441329`).

**FREEZE PREDICATE 2 — SURFACE-GENERATION FREEZE.** §0M's 28×8 CONDITIONALITY MATRIX
(unit `.20`) governs every one of the note's 14 grade surfaces after r3: "After r3 no
grade surface in this note may carry a conditionality claim that is not a cell of this
table, and none may omit one" — reinforced at JB-BOX-6 (unit `.140`): "if a surface and
the table ever disagree, THE TABLE GOVERNS." The 14 surfaces span all three shards (surface
1 here; surfaces 2–5 and 14 in shard 2; surfaces 6–13 in shard 3) — the merge's central
DAG-integrity obligation is installing "§0M GOVERNS" edges from `.20` to all fourteen,
which the per-shard SHARD NOTES name as their top merge hazard and which this file's
statement inventory preserves verbatim at each regenerated surface's own CONDITIONALITY
field.

**FREEZE PREDICATE 3 — TEXT FREEZE (post-acceptance).** The body (through the eight
repair rounds) is frozen; corrections after acceptance are dated appends. Four such
appends exist, **two of which are the note's only corrections to a DISPLAYED MATHEMATICAL
STATEMENT** (E-3, E-4 — see below), landing on shard-1/shard-2 text from shard 3.

**Governing effective-text rule, derived from four converging facts (each shard needed
all four to resolve its own range):** supersession is in-place, strike-and-replace, never
deletion (r1 block: "the r0 text is quoted as struck, then replaced — nothing is silently
rewritten"); where `~~` cannot nest, the superseded block is retained as a quoted block
instead of struck (the retained r0/r1/r2 grade cap); the §0M matrix is the single generator
of every grade surface (FREEZE PREDICATE 2); and an acceptance record plus three annexes
were appended after the frozen body. **EFFECTIVE TEXT = the whole 3,327-line file exactly
as written (r1–r8 brackets already landed in place), READ AS CORRECTED by the four
out-of-range dated appends wherever they name an in-range sentence** — E-1 and E-2 (fold
annex, 2026-08-07, correcting citation grades) land on shard 1's units `.15`/`.34` and
`.16`/`.20`(row 15)/`.33`; **E-3 and E-4 (certifier annex, 2026-08-12) are the note's only
corrections to displayed mathematics** and land on shard 2's `.103`/`.107` (the JB-VTX(c)
display) and `.91`/`.95`/`.97`/`.100`/`.107` (the off-perimeter negation), respectively,
and are quoted in full at `.172`/`.173`.

**★ E-3 is a false-lemma correction in a live clause, and its discharge status is
"awaiting sol discharge (cert3)" — carried forward exactly, not silently closed.** The
frozen §3(c) sentence reads "the shear preserves lattice data"; this is WITHDRAWN — the
shear `Σ_q(i,u) = (i, e_q·u + h_q·i)` is **not unimodular when e_q > 1**, so only the
abscissa run is preserved (the slope transforms by `σ′ = e_q·σ + h_q`), and every
attained-slot/harness-grid count is re-routed to matrix row 12 (JB-VTX(d4)), inheriting
that row's open membership residue and `NONE` teeth. Unit `.172`'s own closing ledger:
"row 21 → both repairs folded, **awaiting sol discharge (cert3)**" — the acceptance record
(2026-08-06) predates the certifier annex (2026-08-12) by six days and cannot have
contemplated it, so **the note is ACCEPTED 2/2 on its pre-E-3/E-4 text**, carrying two
folded-but-undischarged repairs against displayed mathematics at HEAD. This status is
reproduced verbatim at `.172`/`.173` in §3 below and recorded again as OPEN-CALL 3 in §8.

### Scope of record — mandatory THREE-predicate split (rule 7 + rule 17)

**A. ABSORPTION / mathematical supply set.** The title's four items — the expansion
identity, the polygon identity through the displayed shear, the division-step
correspondence, and the (C-READ) transport with the ε-carry collapse (unit `.01`) —
discharged at §2 (JB-DEV), §3 (JB-AFF/JB-VTX), §4 (JB-TREE/JB-ID), §5 (JB-CREAD/JB-EPS),
all shard 2. §0M's 28-row matrix (`.20`) is the authoritative fence inventory.

**B. APPEND / consumption-protocol scope. NO-APPENDS DECLARATION.** GRTJB lands nothing
on any supplier. JB-BOX-6 (`.140`): "No gr/carrier claim (J-C untouched; BLOCKED-ON-
CARRIER-TIE stands); no count/menu/density claim (J-D untouched); the P0 application gate
stands; acceptance counter 0/2 [now STALE, superseded in effect by the acceptance record —
see §8 OPEN-CALL 1] — nothing here may be consumed at proof grade before its hostile arc."
**Zero dated consumption appends are claimed landed on [RMG], [ILN]†, W-2, J-A or LED-Λ,
and none is invented here.**

**C. INBOUND corrections received** (rule 17; the predicate template v2 has no header slot
for). **Four, all homed in shard 3, landing on shard 1 and/or shard 2 text:** FOLD ANNEX
**E-1** (`.166`, from GRTJA PE2 F1, `9040961`) re-reads every "(R-coll)" occurrence as
GRTJA's root-inclusive form — provenance-rider, operative fence untouched. FOLD ANNEX
**E-2** (`.167`, from GRTW2 r1, `8d5e3fa`) re-reads every W2-C3 grade citation at the
supplier's current proved-to-first-twist (38/44) / measured-above (6/44) split — as-of
scoping + provenance-rider. **CERTIFIER ANNEX E-3** (`.172`) and **E-4** (`.173`) — the
two REAL findings of the 2026-08-12 sol certification, both re-derived independently by
the orchestrator before folding (`.171`) and independently a third time by this compiler
(the `(e_q,h_q)=(2,1)` shear witness and the `f=1` off-perimeter instance, both EXACT).

### Resolution rules applied (merged; each shard's own numbered list is a restriction of
this one to its HOME range)

1. Lines 1–1302 / 1303–2457 / 2458–3327 supply the HOME material of shards 1/2/3
   respectively (title, S-STATUS series, §0M, grade cap, literature block, repair rounds
   / §1–§6 theorem bodies and boxes / §7 records, acceptance record, all four annexes).
2. `[r1]`…`[r8]` brackets are already-landed text, applied in chronology; the later
   bracket governs. Where three-plus layers stack on one clause the full `CHAIN:` is
   recorded with its TERMINAL marked — this note has **five** distinct chains, homed at
   `.13`, `.14`, `.26`, `.83`, and `.114` (three are single-site; `.14`'s — the note's
   deepest, four layers — additionally carries two CHAIN-MEMBER body-site continuations
   at `.94` and `.136` — §6 below).
3. The `~~…~~` strike is a supersession marker, never a deletion; struck text is quoted
   wherever the superseding bracket's content cannot be read without it.
4. **The §0M matrix (`.20`) GOVERNS every grade surface** (FREEZE PREDICATE 2). Where a
   surface and the matrix could be read differently, the unit records the matrix cell as
   governing.
5. The two fold-annex errata (E-1, E-2) and the two certifier-annex corrections (E-3, E-4)
   are applied as CONDITIONALITY at the in-range units they name, with the annex's own
   text quoted; no in-range sentence is edited.
6. Out-of-range statements are **not** emitted as units merely because they resolve
   in-range text — each is homed once, at its own physical section.
7. External repo records (report files, `verification/openmath/*` artifacts, supplier
   notes, `docs/references/HigherNewton.tex`) are reading notes only, never edits.
8. **CITE-SCOPE rows compiled as the note states them.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`
   NS-11 retargets the GMN `HigherNewton` engine lemmas to general-`O` sources (COVERS-ALL-O,
   with a normalization-shear obligation); recorded once, in full, at unit `.101` as an
   external reading note. Recorded, not applied.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim source quotation or explicitly marked `[ASSEMBLED]`;
truncation is marked `…`. The note's one source table in range, §0M's 28×8 matrix
(`.20`), is emitted as a compiler `[TABLE]` transcription with a mandatory arithmetic
audit (rule 22); its ASCII displays (the three evidence classes, the per-clause ∎ Grade
blocks) and the r2/G2-1 eight-hit enumeration are **double-emitted** (rule 14) — verbatim,
then as `[TABLE]`. Compiler-authored ledgers (§2, §4, §5, §7) are flagged
`[TABLE — compiler ledger]`.

---

## 2. NON-IMPORTS (consolidated from all three shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (13 rows), shard 2 §4 (16 rows),
shard 3 §4 (13 rows) = 42 raw rows, 2 dedup pairs → 40 distinct rows below]`

**Dedup count for this section: 2.** "No mechanism for the (VD-2) split" is asserted
identically at its home (`.51`) and restated verbatim at the §7.1 record box (`.145`) —
one fact, folded to one row citing both. "No supplier upgrade" is asserted once at the
header (`.40`) and reasserted per-clause at each of the four regenerated `∎ GRADE`
surfaces (`.17`, `.27`, `.37`, `.52`) — one fact, folded to one row citing all five units.
Every other row below is specific to its own section.

| Fence | Explicit material NOT imported, NOT claimed, or NOT proved | Unit(s) |
|---|---|---|
| No new print transcription | "Classifier side = the GMN print … consumed as literature through the SEALED probe transcription `grt_weld_probe.GmnLeg` (no new print transcription in this unit)" | `.39` |
| The valuation-multiplicativity route | `HigherNewton.tex` ~1012 is "a NEW anchor this note does not consume"; recorded NOT TAKEN (atom value degenerates at interior periods `P_t = 1`) | `.61`, `.114` |
| The representative-pin rescue | "The alternative repair … is NOT taken: it is not derived anywhere in this note", refused twice (r3/F-4, r6/F-1) | `.56`, `.73`, `.104` |
| Internal-node `v_{m+1}` | "no internal-node `v_{m+1}` statement is claimed or tested" | `.20` row 17, `.61`, `.114`, `.117` |
| The internal-edge line→`w_m` transfer | "DERIVABILITY … WAS CHECKED BEFORE RE-SCOPING: … NOT derivable" within this note's consumption list | `.114` |
| Cross-representative identity | JB-BOX-3: "no cross-representative operator or byte identity anywhere; SideReads/TreeModel consumed nowhere" | `.20` row 25, `.95`, `.137` |
| `W2-OPEN-1` | "consumed NOWHERE (independently re-verified in JB-PE1)" | `.40`, `.20` row 24, `.136` |
| `W-WIN` | "W-WIN unconsumed"; "window-free legs only, as in [RMG]" | `.20` row 26, `.33`, `.117`, `.138` |
| No gr/carrier (J-C) claim | "no gr/carrier (J-C) claim … BLOCKED-ON-CARRIER-TIE stands" | `.37`, `.20` row 28, `.134`, `.140` |
| No count/menu/density (J-D) claim | "no count/menu/density (J-D) claim" | `.37`, `.20` row 28, `.140` |
| `[RMG]` d₀ ≥ 2 flat corners | "stay FENCED … quantified over nowhere here" | `.33`, `.117`, `.138` |
| **No mechanism for the (VD-2) split [DEDUP — home `.51`, restated `.145`]** | "the mechanism of the m = 2 split is NOT IDENTIFIED"; explicit ban on predicting from the roster table ("DATA, not a law") | `.51`, `.145` |
| **No supplier upgrade [DEDUP — header `.40`, reasserted per-clause at all four regenerated surfaces]** | "Every consumption is at the source's own grade; nothing is upgraded here" | `.40`, `.17`, `.27`, `.37`, `.52` |
| The ρ-form at `v = 0` | "the ρ-form identity is NOT claimed at v = 0 — the transport there is the read-at-target statement (0 = 0) only" | `.130` |
| `[RMG]` clauses not re-proved | "No clause of [RMG] is re-proved or touched." | `.115` |
| The ambient-lattice extension **[E-3, withdrawn]** | the shear "is not unimodular when e_q > 1"; "Only the false ambient-lattice extension is removed" | `.103`, `.172` |
| "Different bytes" as a negation principle **[E-4, withdrawn]** | "henceforth used only as a proof-license boundary, not as a semantic-negation principle" | `.91`, `.100`, `.107`, `.173` |
| The NOT-supplied list (regenerated live at r4/F-6) | "W-1's uncollapsed all-orders dictionary … J-D counts/menus … W2-OPEN-1 … The P0 application gate stands." | `.151` |
| No print-key claim off the walker's reach | "NOT part of any print-key claim: everything the sealed battery scores off the tree families" | `.159` |
| The 8 chamber walks | "STILL PRINT-UNCHECKED, by both instruments" | `.159`, `.163` |
| The 12 chain-divergent walks | "still nothing at the 12 chain-divergent walks (leg B is not claimable there)" | `.163` |
| Leg (C) supplies no decorrelation | "a GATE REPAIR, not a decorrelated second instrument … adds nothing" to the r1 walker's independence | `.162`, `.163` |
| Vacuity is argued, not machine-checked | the byte-identity→vacuity step is "the PURITY of `pwalk`/`my_divmod` …, ARGUED … and not machine-checked" | `.163` |
| Acceptance does not upgrade suppliers | "supplier grades only; no identity, fence, or census moves"; "does not turn its measured-above region into a theorem" | `.168`, `.170` |
| Acceptance does not close the frontier | "The four-member NO-LEG frontier (rows 4/5/12/22) is UNCHANGED" | `.165`, `.168` |
| LED-Λ is not upgraded | the 2026-08-08 annex names GRTW2 and GRTJA only; LED-Λ's ATTEMPT grade rides, unaffected | `.168` (by omission — flagged) |
| No inline copy of every pass report | "the proof note's acceptance record … is the procedural source of record" | `.170` |

---

## 3. Statement inventory (173 units, contiguous, in source order)

### EFF.GRTJB.01  [scope record]

**CANONICAL STATEMENT:** verbatim, line 1.
**FORM:** display (the note's H1 title line).

> “# GRTJB — J-B, THE TREE JUNCTION: the expansion identity, the polygon identity through the displayed shear, the division-step correspondence (the [RMG] tree = the classifier's own division arithmetic, with LED-Λ's line face as the polygon bookkeeping), and the (C-READ) transport with the ε-carry collapse”

**CONDITIONALITY:** The title names four supply items; each is fenced differently by the matrix (`.20`) and by the grade cap (`.31`–`.35`). Two of the four are re-scoped from shard 3: “the polygon identity through the displayed shear” is narrowed by **CERTIFIER ANNEX E-3** (the shear preserves the abscissa run, **not** ambient lattice data), and every “FALSE off the perimeter” gloss under it by **E-4** (“NOT SUPPLIED outside the stated perimeter”).

**DERIVATION:** Not a mathematical unit; the title is the note's own supply headline. Its four items are discharged at §2 (JB-DEV), §3 (JB-VTX), §4 (JB-TREE/JB-ID), §5 (JB-CREAD/JB-EPS) — all shard 2.

**RESOLUTION TRACE:** statement line 1; proof lines 1400–2308 (shard 2); correction sites 3199–3245 (E-3), 3267–3312 (E-4).

XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:(RM-m)` — grep-verified count **11**.
XREF: `lean/notes/openmath/LEDGERLAMBDA_2026-08-08.md:λ_E` — count **10**.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:(C-READ)` — count **8**.

**TEETH:** Composite — the sealed runner's 18 families (§7.1, shard 3) key the four items; inventoried in §5.

---
### EFF.GRTJB.02  [scope record]

**CANONICAL STATEMENT:** verbatim, lines 3–8 (through “two-commit seal).”).
**FORM:** bold-headed paragraph.

> “**Unit:** J-B COMPOSER (weld dependency order: W-2 and J-A composed and
> consumable at attempt grade; per `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md`
> §S2.2 (J-B) and §S3.1 rows W-3/W-5). **Genre: PROOF NOTE at attempt grade
> (acceptance counter 0/2; no gate fires; no acceptance arc opened), with
> sealed-runner machine brackets** (`verification/openmath/grt_jb_checks.py`,
> two-commit seal).”

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION** (rule 26). “attempt grade (acceptance counter 0/2; **no acceptance arc opened**)” was true when written and is FALSE at HEAD: the acceptance record (L3107–3119, shard 3) reads “**THIS NOTE IS ACCEPTED at 2/2** — PE9 (b0b4c3a, CLEAN 0C/0G/0m …) and PE10 (6d548f3, CLEAN …)”. The sentence is not corrected under the freeze; a reader must be told it is no longer true. The three sub-clauses that ARE still live: no gate fires, the weld dependency order, and the two-commit seal.

**DERIVATION:** Declaration, not derivation.

**RESOLUTION TRACE:** statement lines 3–8; status superseded at 3107–3119 (acceptance record); supplier grades further updated at 3148–3161 (the 2026-08-08 annex: GRTW2 accepted at `adc6cf3`, GRTJA at `17d2a32`).

**PIN VERIFICATION:** `b0b4c3a` → `git cat-file -t` = **commit**. `6d548f3` → **commit**. `adc6cf3` → **commit**. `17d2a32` → **commit**. `f131c53` → **commit**.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — file EXISTS (path pin, not a designation).

**TEETH:** NONE (declaration).

---
### EFF.GRTJB.03 — .10  [SERIES: `S-STATUS`, eight dated members]  [run-record ×8]

**SERIES DECLARATION (rule 28).** Lines 8–169 carry **eight** dated `S-STATUS` lines, `[r1]`…`[r8]`, in source order. Seven are struck (`~~…~~`); the eighth is live. Each states the arc as of its own round, and each supersedes ALL its predecessors, not only the immediately preceding one — `[r8]`'s own words (L142): “**supersedes the seven struck lines**”. They are emitted as eight units with explicit series membership and order, so a merge run can reconstruct the chronology mechanically. **TERMINAL member: `.10` (`[r8]`)** — and even that is STALE-SELF-DESCRIPTION per `.02`.

**The series, as one compiler ledger.** `[TABLE — compiler ledger]` Arithmetic audit (rule 22): the arc is a strict alternation PE_k → r_k, eight of each; every "hostile passes RUN" count equals its member index; every "repair rounds applied" count equals its member index; the acceptance counter is **0/2** in all eight. **All eight self-consistent; verified against the footer arc lines 2950–3101 (shard 3), which repeat the same chain.**

| unit | member | source lines | struck? | passes run | rounds applied | the pass it answers | that pass's verdict | commits pinned |
|---|---|---|---|---|---|---|---|---|
| `.03` | `[r1]` | 8–11 | YES | ONE | 1 | JB-PE1 | 1 CRITICAL + 9 gaps, NOT CLEAN | `85a8dc9` |
| `.04` | `[r2]` | 12–19 | YES | TWO | 2 | JB-PE2 | 0C + 7 gaps, NOT CLEAN; PE1's F1 CURED | `4c97649`, `46f9452` |
| `.05` | `[r3]` | 21–33 | YES | THREE | 3 | JB-PE3 | 0C + 8 gaps; **1st acceptance attempt, did not land** | `2fd271e`, `67bf0c4`, `888e293` |
| `.06` | `[r4]` | 35–56 | YES | FOUR | 4 | JB-PE4 | 0C + 8 gaps; **2nd attempt, did not land** | `38c4754`, `8acb2d1`, `87c553d` |
| `.07` | `[r5]` | 58–81 | YES | FIVE | 5 | JB-PE5 | 0C + 5 gaps; **3rd attempt**; its F-3 is “THE GIFT” | `39e16ee`, `ae0acdf` |
| `.08` | `[r6]` | 83–110 | YES | SIX | 6 | JB-PE6 | 0C + 2 gaps + 1 minor; **4th attempt** | `ca39044`, `f9f104e` |
| `.09` | `[r7]` | 112–140 | YES | SEVEN | 7 | JB-PE7 | 0C + 1 gap + 2 minor; **5th attempt** | `aa9b603`, `4607824` |
| `.10` | `[r8]` | 142–169 | **NO (live)** | EIGHT | 8 | JB-PE8 | 0C + 0 gaps + 1 minor; **6th attempt** | `6c61b82`, `4c4ee56` |

**PIN VERIFICATION (rule 23):** all **20** distinct commit hashes named across the series resolve — `git cat-file -t` returns `commit` for every one of `85a8dc9 4c97649 46f9452 67bf0c4 888e293 2fd271e 8acb2d1 87c553d 38c4754 ae0acdf 39e16ee f9f104e ca39044 4607824 aa9b603 4c4ee56 6c61b82 7f6759d 5a72b62 f5578d0`. **20/20 EXACT.** All eight report files `GRTJB_passPE1_report.md` … `GRTJB_passPE8_report.md` EXIST in `lean/notes/openmath/`.

**CANONICAL STATEMENT of the TERMINAL member `.10`:** verbatim, lines 142–169 (opening and closing quoted; the arc recital abridged with `…` since the table above transcribes it).
**FORM:** bold-headed paragraph (a struck-siblings series member, live).

> “**[r8] S-STATUS (CURRENT, supersedes the seven struck lines): attempt grade,
> acceptance counter 0/2 (ZERO clean passes), EIGHT hostile passes RUN and
> EIGHT repair rounds applied. Arc: JB-PE1 (85a8dc9 — 1C + 9 gaps) → r1
> … → r7 (4c4ee56) → JB-PE8
> (`GRTJB_passPE8_report.md`, commit 6c61b82 — 0 CRITICAL + 0 gaps + 1 minor,
> NOT CLEAN; the SIXTH acceptance attempt, did not land. The r7 diff's
> mathematics verified EXACT end-to-end: both directions of the m = 1
> equivalence re-derived and independently machine-confirmed on a WIDER box
> than PE7's — 340 read data, 0 counterexamples; the disclosed `q+1 <= G.RANK`
> conjunct re-read from committed source at every cited line and its
> redundancy re-derived; the arc-accounting system verified consistent. The
> one finding is quotation-form: the r7 round block's F-1 bullet quoted, as
> the assertion of "both [r6, m-1] brackets", a FUSED string appearing
> byte-for-byte at NEITHER site) → r8 (this round, block below: THE
> ONE-QUOTATION ROUND — the fused quote STRUCK in place at the r7 F-1 bullet
> and each site's actual struck wording quoted separately, byte-exactly). No
> gate fires; no acceptance arc is open. A repair round is NOT a pass, so the
> counter stays 0/2, and JB-PE9 — a fresh hostile pass on THIS post-r8 text —
> is the next acceptance attempt. All four machine instruments remain
> BYTE-FROZEN in r8 (md5s re-verified 2026-08-06 at their sealed values and
> `git diff verification/` empty; r8 is note-only and ran NO probe of its own
> — it cites NO new machine figure).”

**SUPERSESSION KIND:** `replacement` (each member replaces all its predecessors wholesale — the note struck the predecessor line rather than amending it).

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION at HEAD** for the whole series, terminal member included: “acceptance counter 0/2 (ZERO clean passes)”, “no acceptance arc is open”, and “JB-PE9 … is the next acceptance attempt” are all falsified by the acceptance record (PE9 CLEAN → PE10 CLEAN → **ACCEPTED 2/2**, L3107–3113). The instrument-freeze half (md5s, `git diff verification/` empty) is **CONFIRMED at HEAD by this compiler** — see FREEZE PREDICATE 1, 4/4 exact.

**DERIVATION:** Round-arc records, not derivations. The mathematical content each round moved is homed at its own repair-round unit (`.43`–`.80`).

**RESOLUTION TRACE:** statement lines 8–169; the series is re-stated a second time as the footer arc at 2950–3101 (shard 3) and a third time as the acceptance record's “Full arc” at 3111–3113 (shard 3); status superseded at 3107–3119.

**TEETH:** The four byte-frozen instruments are the freeze's tooth; their verdicts are §7.1/§7.4 (shard 3). The series carries no mathematical tooth of its own.

---
### EFF.GRTJB.11  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 171–185 — the §0M heading and the round's own statement of WHY a table replaces a fourth sweep.
**FORM:** display (H2 heading) + bold-headed bracketed rider.

> “## §0M. **[r3] THE CONDITIONALITY MATRIX — the single surface every grade statement in this note is generated from**
>
> **[REPAIR ROUND r3, STEP 1 — why a table replaces a fourth sweep.** Per-site
> fence patching has not converged. The SAME defect — a proviso present in a body
> proof and absent from a surface a downstream unit reads alone — was found in
> every round of this note's arc: PE1/G-9 → PE2/G2-1 → PE3/F-1 **and** PE3/F-1B,
> the last two of them at surfaces r2's own mandated re-grep had just certified
> "already consistent". A fifth sweep would find a sixth site. So r3 builds the
> matrix ONCE, filling every cell from the BODY PROOF (not from any existing
> grade line), and then REGENERATES every grade surface from it: the grade cap,
> the four ∎ Grade lines, the seven §7.2 rows, §7.3's consequence display, and
> JB-BOX-2's enumeration. **After r3 no grade surface in this note may carry a
> conditionality claim that is not a cell of this table, and none may omit one.**
> A hostile pass audits ONE table plus the regeneration; that is the whole point
> of the round.]**

**SUPERSESSION KIND:** `replacement` — it replaces the *generation mechanism* for all 14 grade surfaces, not any single statement.

**CONDITIONALITY:** Unconditional as a procedural declaration; it is FREEZE PREDICATE 2 of this shard. **Its own success claim is qualified by the note's later rounds:** r4 found “the frontier moved into the matrix's OWN precision” (F-1/F-2/F-3/F-7 are defects **of §0M itself**, L942–943), and r6 found the same level-slip disease at “the one row that correction never swept” (row 11's (d3), L1127–1134). So the mechanism held in the sense r4 states (“**the r3 matrix mechanism held**”; “NO fifth instance of the old surface-divergence class”) while the matrix's cell-level precision needed four more rounds.

**DERIVATION:** Procedural, not mathematical. Its warrant is the four-instance recurrence it names (PE1/G-9, PE2/G2-1, PE3/F-1, PE3/F-1B), each independently verifiable at its own round block (`.46`, `.49`).

**RESOLUTION TRACE:** statement lines 171–185; the STEP-1/STEP-2 restatement at 877–892; the standing-rule form at 2443–2454 (JB-BOX-6, shard 3); the mechanism's own defect record at 942–943 (r4 header) and 1124–1125 (r6 header, “§0M was edited FIRST (row 11 split)”).

**TEETH:** **PROOF-ONLY / AUDIT** (rules 16, 27). No battery keys a governance rule. Its evidence class is `in-house hostile pass` — the mechanism's test is that PE4 “found NO fifth instance of the old surface-divergence disease” (L941–942), which no runner family could have produced.

---
### EFF.GRTJB.12  [definition]

**CANONICAL STATEMENT:** verbatim, lines 189–194 — matrix column (a1).
**FORM:** bold-headed paragraph (a column definition inside §0M's preamble).

> “**(a1) SHARED-KEY PERIMETER, `P<q`** — §1's second name: Φ_j^har =
> φ_{j+1}^cls byte-for-byte for every 1 ≤ j ≤ q−1, **nothing required at
> j = q**; equivalently the level range 0 ≤ q ≤ qcap with
> qcap := min(n, shared_upto+1) = the runner's own `qcap_of(T,G)`. This is
> J-A's perimeter instantiated AT LEVEL q, and it is exactly what a JA-VAL
> consumption at level q needs.”

**CONDITIONALITY:** Unconditional as a definition. It is the fence of matrix rows 3, 4, 8, 9, 10, 11(d1)(d2), 12, 13, 17, 18. **Corrected in reading by CERTIFIER ANNEX E-4** (shard 3, L3267–3272): the note's live “off it (VAL) is FALSE, not merely unproved” gloss is withdrawn — “**NOT SUPPLIED by this note outside the stated perimeter**”. E-4 changes no matrix cell (its own consumer sweep item 1: “§0M rows 3–5 and 8–12 already encode positive assertion scopes through their `P<q`/`P≤q` cells; **no matrix cell changes**”), so this definition stands as written; what changes is every *negation* gloss attached to it.

**DERIVATION:** Definition, imported from §1's second display (L1323–1334, shard 2), which itself derives the level-range form: `shared_upto := max{L ≥ 0 : Φ_j^har = φ_{j+1}^cls for all 1 ≤ j ≤ L}` and `qcap := min(n, shared_upto + 1)`, matching the runner's `for q in range(0, qcap_of(T,G) + 1)`.

**RESOLUTION TRACE:** statement lines 189–194; source definition lines 1323–1334 (shard 2); correction sites 3267–3296 (E-4).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VAL` — grep-verified count **7**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:shared-key perimeter` — count **5**.

**TEETH:** `jb_dev`'s cross-engine leg runs `0 ≤ q ≤ qcap`, i.e. exactly this perimeter; the off-perimeter counter is **0** on the roster (L1746–1747).

---
### EFF.GRTJB.13  [definition]

**CANONICAL STATEMENT:** verbatim, lines 196–216 — matrix column (a2), with its two in-place corrections.
**FORM:** bold-headed paragraph with two nested bracketed riders.

> “**(a2) BYTE-EQUAL CHAIN THROUGH q, `P≤q`** — §1's first name: Φ_j^har =
> φ_{j+1}^cls for every j ≤ q. Equivalently: **J-A's perimeter instantiated at
> level m = q+1.** STRICTLY STRONGER than `P<q`; ~~the two differ exactly at the
> top level q = qcap = shared_upto+1, where `P<q` holds and `P≤q` FAILS by the
> definition of shared_upto.~~ **[r4, F-3 — the struck arithmetic is FALSE on 11
> of the note's own 16 roster towers: qcap := min(n, shared_upto+1), so
> qcap = shared_upto+1 only when shared_upto < n. THE TRUE STATEMENT: as
> conditions at a fixed level q the two differ exactly at j = q; as fences over
> the level range 0 ≤ q ≤ qcap, the exclusion BITES ONLY WHEN shared_upto < n —
> there qcap = shared_upto+1 and `P<q` holds while `P≤q` fails at q = qcap
> (5 roster towers: T3A, T3C, T3D, T3E, I4C); when qcap = n ≤ shared_upto the
> two fences COINCIDE on the whole range and (RES) is excluded at NO level
> (the other 11: T2A–T2G, T3B, T3F, I4A, I4B). Read off the runner's own
> `qcap_of`/`shared_upto` by a read-only probe, 2026-08-06; every regenerated
> site now carries this statement or points here.]** Consumers: JB-DEV(ii)'s byte clause **and — [r3,
> F-4, NEW — JB-DEV(iii)'s (RES) layer**, which is JA-RES at read level
> m = q+1 and therefore needs J-A's perimeter at m, i.e. through j = q. (This
> corrects §1's r2 sentence "no statement cites §1 for the through-q condition
> except JB-DEV(ii)'s byte clause"; see the [r3] amendment there.) **[r6,
> F-1 — and a THIRD consumer: JB-VTX's (d3) min tie
> w_{q+1}(f) = v_{q+2}(f), which is JA-VAL at level q+1 (row 11 (a2)).]**”

**CHAIN (rule 25):** frozen r2/r3 arithmetic gloss → **[r4, F-3]** correction (the exclusion bites only where shared_upto < n) → **[r6, F-1]** consumer-list extension (a third consumer). **TERMINAL = the r4 statement for the arithmetic + the r6 list for the consumers**; both are additive, neither supersedes the other.

**SUPERSESSION KIND:** `counter re-reading` for the r4 rider (a false arithmetic claim about how many towers the exclusion reaches, recounted from the runner's own data) + `inventory completion` for the r6 rider (a consumer the earlier list omitted).

**CONDITIONALITY:** Unconditional as a definition. The **5-of-16 tower geography (T3A/T3C/T3D/T3E/I4C)** is a probe-derived fact, not a theorem: “Read off the runner's own `qcap_of`/`shared_upto` by a read-only probe, 2026-08-06”. **UNPINNED (rule 23):** the r4 probe ran read-only to /tmp; no artifact filename is given for it in this bracket. r4's own header does say the two probes' “outputs are transcribed at the cells that cite them” (L947–948), which is what the bracket above does — so the figure is transcribed, but not replayable from a committed artifact. Direction is conservative either way: r4's own summary records the correction as “the note claimed MORE conditionality than it had; nothing downstream moves” (L977–978).

**DERIVATION:** [ASSEMBLED — the correction's arithmetic, from the definitions] `qcap := min(n, shared_upto+1)`. If `shared_upto < n` then `qcap = shared_upto+1`, so at `q = qcap` the byte-agreement required by `P≤q` reaches `j = shared_upto+1`, which fails by the maximality in `shared_upto`'s definition, while `P<q` only requires `j ≤ shared_upto` and holds. If `shared_upto ≥ n` then `qcap = n ≤ shared_upto`, so for every `q ≤ qcap` both fences require agreement only at levels `≤ shared_upto` and coincide. The 5/11 split is then a per-tower read of `shared_upto` against `n`.

**RESOLUTION TRACE:** statement lines 196–216; the same correction re-derived at cell note ⟨n4⟩ (L370–386, unit `.24`) and at §1's r3/r4 amendment (L1340–1364, shard 2); r4 disposition F-3 at 968–978; r6 disposition F-1 at 1127–1163.

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-RES` — count **20**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VAL` — count **7**.

**TEETH:** **`NONE` on the (RES) consumer — a signed no-leg cell.** Row 5's own (f) cell reads “**NONE** — no family keys (RES) anywhere”. The (d3) consumer DOES have a leg: the runner gates it at `q ≤ shared_upto`, “which on the roster is exactly `P≤q`” (L1157–1158). Disposition: **disclosed non-repair** for (RES); **executable regression** for (d3).

---
### EFF.GRTJB.14  [hypothesis]

**CANONICAL STATEMENT:** verbatim, lines 218–250 — matrix column (b), the `u ≥ 0` proviso, with its four-layer correction stack.
**FORM:** bold-headed paragraph with three nested bracketed riders.

> “**(b) [JA-r1] u ≥ 0** — JA-GRID(a)'s inline J-A repair proviso
> u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 on the quantified window,
> **CARRIED AND UNDISCHARGED** (r2, G2-5; r1's "discharge" retracted). It is
> NOT one of JA-BOX-1..5. JA-GRID(c) — the carry clause LEMMA JB-EPS consumes
> — carries NO proviso. **[r5, F-3 — STATUS NARROWED: u ≥ 0 is now PROVED on
> ALL of the level-m weight lattice 𝒲_m (§5's [r5, F-3] display, four lines
> from the r4 definition, machine-confirmed). The carried residue at the two
> consuming rows (4 and 12) is ~~exactly~~ the MEMBERSHIP hypothesis
> V = w_{q+1}(f) ∈ 𝒲_{q+1}: both theorems quantify f nonzero with NO degree
> bound, and membership holds by definition at deg f < deg Φ_{q+1} (where
> the proviso is therefore DISCHARGED) and is not established off it.
> CARRIED, NARROWED; not fully discharged.]** **[r6, m-1 — the relation,
> stated precisely ("exactly" struck above as overstating necessity):
> membership IMPLIES the u ≥ 0 instance the two rows need at V = w_{q+1}(f)
> — a SUFFICIENT route, ~~per-instance a logically STRONGER hypothesis than
> the proviso, not an equivalent~~ **[r7, PE7 F-1 — the struck
> non-equivalence claim was derived nowhere and is FALSE at every m = 1
> (q = 0) instance, which rows 4/12's quantifier 0 ≤ q ≤ qcap includes: at
> m = 1, for EVERY read datum (e₀, h₀, g₀),
> {V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒲₁ EXACTLY. (⊇) is the §5 four-line theorem at
> m = 1; (⊆) u(V) ≥ 0 means V = s·h₀ + u·e₀ with s := (ℓ₀V) mod e₀ ∈
> [0, e₀−1] and u ≥ 0 — take j := s ≤ e₀−1 ≤ P₀−1 (P₀ = e₀g₀, g₀ ≥ 1) and
> a := u in the displayed description 𝒲₁ = {e₀a + h₀j : a ≥ 0,
> 0 ≤ j ≤ P₀−1}. Machine-checked by the PE7 verifier on 96 read data (all
> coprime (e₀, h₀) with e₀ ≤ 6, h₀ ≤ 8, g₀ ≤ 3), every V ∈ [0, 150), 0
> counterexamples to the equivalence (`GRTJB_passPE7_report.md` §2 F-1, as
> of commit aa9b603). THE INSTANCE-HONEST RELATION: membership implies the
> needed instance — the sufficiency direction, all any consumer uses; the
> converse is INSTANCE-DEPENDENT — EQUIVALENT at m = 1 (above), containment
> possibly strict at m ≥ 2, strictness UNPROVED either way in general
> (PE6's qualifier, restored)]**; what is smaller is the remaining open
> DOMAIN, now confined to deg f ≥ deg Φ_{q+1} and pinned to that one
> membership question.]**”

**CHAIN (rule 25) — FOUR layers, the deepest in the note:**
1. **r1** — the proviso is named in JB-BOX-2 *with a discharge argument*.
2. **r2, G2-5** — the discharge is **RETRACTED**: “it was an assertion, not a derivation”. Status: CARRIED, DISCHARGE OWED.
3. **r5, F-3** — **NARROWED**: `u ≥ 0` PROVED on all of `𝒲_m`; the residue is lattice MEMBERSHIP at the unbounded-degree quantifier.
4. **r6, m-1** → **r7, PE7 F-1** — the relation between membership and the proviso, stated precisely: membership is SUFFICIENT; the converse is EQUIVALENT at m = 1, unproved in general.

**TERMINAL = the r7 reading.** A chapter cut must use: *the proviso is DISCHARGED at `deg f < deg Φ_{q+1}`; off it the note CARRIES the membership hypothesis `w_{q+1}(f) ∈ 𝒲_{q+1}`, which is sufficient for the instance the consumers need, equivalent to it at m = 1, and of unknown strictness at m ≥ 2.*

**SUPERSESSION KIND:** r2 = `replacement` (a retraction); r5 = `scope-pin` (the theorem holds on a named sub-window); r6 = `wording-rider`; r7 = `counter re-reading` (an affirmative claim refuted by a counter-instance class).

**TARGETS (rule 24):** `.14` (this cell), `.20` (matrix rows 4 and 12), `.30`/`.31` (grade-cap JB-DEV and JB-VTX bullets), `.26` (the frontier census), `s2of3` §2(iii)'s retraction block and §3's ∎ Grade (d4) line, `s2of3` §5's `[r5, F-3]` display and SCOPE block, `s2of3` JB-BOX-2, `s3of3` §7.2's JB-DEV/JB-VTX rows and §7.3's W-3 bullet. **This is the note's widest single supersession.**

**CONDITIONALITY:** The proviso is **an inherited hypothesis of J-A, not one of JA-BOX-1..5** — the note says so twice (here and at L1497–1500). Its consumers are **exactly two**: matrix row 4 (JB-DEV(iii)(GRID)) and row 12 (JB-VTX(d4)). Both remain frontier members after r5's narrowing (`.26`).

**DERIVATION:** The four-line theorem lives at §5 (L2046–2062, shard 2) and is re-derived there from the r4 lattice description; the m = 1 equivalence's (⊆) direction is displayed inside this very cell (the `j := s`, `a := u` decomposition quoted above). **Both are self-contained arithmetic from the displayed description of `𝒲_m`, consuming no citation.**

**RESOLUTION TRACE:** statement lines 218–250; proof lines 2046–2062 (§5's four-line theorem, shard 2) and 2085–2111 (§5's SCOPE block, shard 2); correction sites 680–684 (r1 G-5), 804–819 (r2 G-5), 1053–1073 (r5 F-3), 1179–1190 (r6 m-1), 1218–1249 (r7 F-1), 1250–1258 (r7 m-2, the third site), 1284–1294 (r8, the quotation repair on the r7 bullet).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-GRID` — count **11**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-BOX-1` — count **8**. (The note writes “JA-BOX-1..5”; the range endpoints are verified individually: JA-BOX-1 **8**, JA-BOX-2 **7**, JA-BOX-3 **3**, JA-BOX-4 **4**, JA-BOX-5 **1**.)

**TEETH:** **BOTH halves of both consuming rows are `NONE` on the grid half.** Row 4: “carry half **IND** (`jb_eps` keys JA-GRID(c)); grid/attained-abscissa half **NONE**”. Row 12: “**NONE [r3, F-3]**”. Disposition: **disclosed non-repair** — the sub-clause riding the open proviso is the sub-clause with zero machine evidence, and the note discloses the coincidence explicitly (⟨n3⟩, `.23`). The lattice theorem itself has corroboration only: PE6's 598,500-member enumeration (0 violations) and PE7's 96-read-data equivalence check — both **verifier-owned**, attributed, with the note stating “NOTHING RIDES ON EITHER FIGURE: u ≥ 0 on 𝒲_m is the displayed four-line THEOREM”.

---
### EFF.GRTJB.15  [hypothesis]

**CANONICAL STATEMENT:** verbatim, lines 252–257 — matrix column (c).
**FORM:** bold-headed paragraph.

> “**(c) (VD-m) level fence** — J-A §3.4's EVALUATED dictionary. **Unconditional
> at m ≤ 1 ONLY** ((VD-1) = W2-L3); at every m ≥ 2 a HYPOTHESIS (JA-VDIND's
> ABSOLUTE character-triviality z_{m−1}^{i·A_{m−1}} = 1 at every attained
> abscissa); at m ≥ 3 implied by the per-digit proviso / (R-coll) of JA-BOX-2.
> Distinct from JA-RES, the PER-SLOT law, which is unconditional at m = 2 and
> carries its own per-digit proviso at m ≥ 3 — the r1/F1 reading fence.”

**CONDITIONALITY:** This IS a conditionality declaration. **INBOUND CORRECTION E-1 (rule 17 predicate C) lands here.** FOLD ANNEX E-1 (L3125–3133, shard 3):

> “J-A's (R-coll) perimeter as originally displayed omitted the
> root-level (q = m) JA-VDIND condition; JA r2 (5d95805) applied the
> root-inclusive extension, verified on all 66 witnesses. THIS NOTE's
> operative fence was already correct (root triviality a HYPOTHESIS at
> every m ≥ 2 — PE2's own adjudication: uncontaminated); only the
> subordinate "(R-coll)" LABEL in the §0M column-(c) apparatus inherited
> the pre-extension reading. Wherever this note's text says "(R-coll)", read
> the root-inclusive form of GRTJA at HEAD (≥ 5d95805).”

**SUPERSESSION KIND:** `provenance-rider` — the label is re-pointed to the supplier's corrected form; the operative fence is untouched.

**DERIVATION:** Consumption declaration. The r1/F1 reading fence it names — that JA-RES's per-slot law does NOT transfer to the evaluated dictionary — is derived at §2(iii)'s `[r1, F1]` block (L1471–1495, shard 2) and is the finding that produced it.

**RESOLUTION TRACE:** statement lines 252–257; the fence's own derivation 1471–1495 (shard 2); the census evidence 1310 word-for-word at 645–659 (r1 F1) and §7.1 (shard 3); correction site 3125–3133 (E-1).

**PIN VERIFICATION:** `5d95805` → `git cat-file -t` = **commit**. `9040961` (the GRTJA PE2 report commit named by E-1) → **commit**.

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VDIND` — count **21**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:(VD-m)` — count **10**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:(R-coll)` — count **7**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-BOX-2` — count **7**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-L3` — count **5**.

**TEETH:** The note's OWN sealed runner refutes the pre-r1 reading: **(VD-2) machine-evaluated FALSE on 10 of 13 roster boundary rows.** Disposition: **executable regression that FIRED against the note's own earlier claim** — an unusually strong tooth, because the instrument disconfirmed the author.

---
### EFF.GRTJB.16  [hypothesis]

**CANONICAL STATEMENT:** verbatim, lines 259–263 — matrix column (d).
**FORM:** bold-headed paragraph.

> “**(d) W2-C1 representative restriction** — the statement is made at the
> representative φ_{q+1} := Φ_q^har, admissible by W-2 clause 1 on W-2's own
> perimeter (W2-C1a for the window object; W2-C3 for the transported chamber).
> W-2 clause 1's own conditionality rides. `YES*` = inherited, i.e. the clause
> speaks about objects a `YES` clause produced.”

**CONDITIONALITY:** **INBOUND CORRECTION E-2 lands on the W2-C3 half.** FOLD ANNEX E-2 (L3135–3142, shard 3):

> “W-2's
> W2-C3 was re-graded at its r1 from "strictly at every level (44/44)" to
> proved-to-first-twist (38/44) / measured above (6/44, riding W2-OPEN-2);
> this note's row-15/W-2 citations predate that re-grade and are
> pin-protected (as-of quotes). Wherever this note cites W2-C3's grade,
> the supplier's current form (GRTW2 at HEAD, ≥ 94534df: forward-direction
> W2-ID1 + OPEN-2a) governs. No identity or count in this note consumes
> the re-graded clause beyond its still-valid instance evidence.”

**SUPERSESSION KIND:** `as-of scoping` (the note's citations are pin-protected as-of quotes) + `provenance-rider` (the supplier's current form governs).

**DERIVATION:** Consumption declaration; the `YES*` convention it defines is the matrix's own inheritance notation and is used in rows 3, 4, 5, 13, 17, 18.

**RESOLUTION TRACE:** statement lines 259–263; consumed at matrix rows 1, 8–13, 15 (`.20`); correction site 3135–3142 (E-2); supplier-grade update 3148–3161 (the 2026-08-08 annex: GRTW2 ACCEPTED at `adc6cf3` “at its honest proved-to-first-twist (38/44) / measured-above grade”).

**PIN VERIFICATION:** `8d5e3fa` → **commit**; `94534df` → **commit**; `adc6cf3` → **commit**.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C1` — count **22**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C1a` — count **10**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C3` — count **22**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-OPEN-2` — count **60**.

**TEETH:** Inherited — the W-2 transport is keyed by `TW-JB` (chamber re-instantiation, 2,480 samples, GREEN; §7.1, shard 3). Disposition: **foreign-note evidence** for the grade, **executable regression** for the transported chamber.

---
### EFF.GRTJB.17  [hypothesis]

**CANONICAL STATEMENT:** verbatim, lines 265–268 — matrix column (e).
**FORM:** bold-headed paragraph.

> “**(e) [RMG] recital** — which clauses of the (RM-m) box / the S2.x displays
> the claim consumes. **[r3, F-5]** §5's recital is restored to the COMPLETE
> S0.2 box (both dropped Ĉ_m clauses), so the word "verbatim" is true of it
> again, and the JB-EPS application instance is licensed (§5, and row 20).”

**SUPERSESSION KIND:** `inventory completion` — two dropped clauses restored to a recital that called itself verbatim.

**CONDITIONALITY:** Unconditional as a column definition. The restored clauses are `(Ĉ-deg)` `deg Ĉ_m < deg Φ_m` and `(Ĉ-wt)` `w_m(Ĉ_m) = γ_{m+1}` (§5, L2015–2017, shard 2). **`(Ĉ-deg)` is not decoration**: it is one of L-CANON's three hypotheses, so it is what makes “THE canonical division” canonical at this site (L2020–2023). **`(Ĉ-wt)` is the clause that licenses the JB-EPS instance** (L2126–2131).

**DERIVATION:** Declaration; the restoration's warrant is the byte comparison PE4 performed — “byte-compared the (RM-m) recital against RMENGINE S0.2 (**11/11 lines identical**)” (L938–940).

**RESOLUTION TRACE:** statement lines 265–268; the restored recital 1992–2023 (shard 2); r3 STEP 3 at 893–897; PE4's byte confirmation at 938–940.

XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:S0.2` — count **13**.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:(RM-m)` — count **11**.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:L-CANON` — count **6**.

**TEETH:** **AUDIT — transfer audit** (rule 27). No battery can key a recital's completeness; the tooth is PE4's independent 11/11 byte comparison against the source display. Quoted coverage-hole sentence: the r3 header's own “§5's recital, labelled 'the (RM-m) box verbatim', had dropped two of [RMG]'s Ĉ_m clauses” (L893–895).

---
### EFF.GRTJB.18  [instrument-record]

**CANONICAL STATEMENT:** verbatim, lines 270–288 — matrix column (f) plus the three evidence classes.
**FORM:** bold-headed paragraph + ASCII display.

> “**(f) machine-evidence class** — **IND** / **SAME** / **NONE**, defined
> immediately below. This column grades EVIDENCE, never truth: a `NONE` cell
> says the battery is silent, not that the clause is false.”

**Double-emission (rule 14) — the ASCII definition block, verbatim, lines 277–288:**

> “**The three evidence classes (used verbatim from here on).**
>
>     IND   INDEPENDENT-LEG — the family compares two GENUINELY DIFFERENT
>           computations (a different code path, or the print engine against the
>           harness engine) and a disagreement is REACHABLE.
>     SAME  SAME-COMPUTATION — the family re-executes ONE pure function on
>           BYTE-EQUAL arguments, behind a guard that has already forced
>           agreement: the violation is UNREACHABLE and the leg carries NO
>           information. (PE1/G-1's disease. Named wherever it occurs; never
>           counted as evidence, never advertised as a second engine.)
>     NONE  NO-LEG — no family, in the sealed battery or in any post-seal
>           instrument, keys this clause.”

`[TABLE]` transcription of the same block:

| class | definition | failure mode it names |
|---|---|---|
| **IND** | INDEPENDENT-LEG — two GENUINELY DIFFERENT computations (different code path, or print engine vs harness engine); a disagreement is REACHABLE | — |
| **SAME** | SAME-COMPUTATION — ONE pure function re-executed on BYTE-EQUAL arguments behind a guard that already forced agreement; the violation is UNREACHABLE and the leg carries NO information | PE1/G-1's disease; never counted as evidence, never advertised as a second engine |
| **NONE** | NO-LEG — no family, sealed or post-seal, keys this clause | — |

**CONDITIONALITY:** Unconditional; and the column carries the note's own strongest epistemic fence — “**This column grades EVIDENCE, never truth**”. **This is the definitional apparatus the whole teeth inventory of this shard rests on (§5 below adopts it verbatim).**

**DERIVATION:** Definition. Its warrant is the recurrence it names: the SAME class was created because PE1's G-1 found the sealed tree family's "print-key" leg to be one `fresh_divmod` re-executed on equal arguments, and r3's F-2 found the same disease at a third site (`jb_dev`'s third leg, ⟨n1⟩).

**RESOLUTION TRACE:** statement lines 270–288; instances at ⟨n1⟩ (326–337) and ⟨n2⟩ (339–345); the originating findings at 660–672 (r1 G-1), 764–783 (r2 G2-2), 898–905 (r3 F-2).

**TEETH:** **AUDIT — in-house hostile pass** (rule 27). The class system is a finding no battery could produce: a battery cannot report that its own violation branch is unreachable.

---
### EFF.GRTJB.19  [definition]

**CANONICAL STATEMENT:** verbatim, lines 274–276 — matrix column (g).
**FORM:** bold-headed inline sentence.

> “**(g) other scope** — T-scope(m), g_m = 1, the v ≠ 0 stratum, LED-Λ's attempt
> grade, and each instrument's own coverage cut.”

**CONDITIONALITY:** Unconditional as a column definition. **LED-Λ's attempt grade is the one item here that is a live grade dependency** — the note repeats at row 17 “**LED-Λ at ATTEMPT grade — the tie's grade rides it**”, and at JB-BOX-4 (shard 2) “LED-Λ is ATTEMPT grade (acceptance counter 0) — the §4(iii) citation's grade rides it, and the runner therefore re-verifies the λ_E quanta FRESH rather than trusting the ledger (decorrelation, not redundancy)”.

**DERIVATION:** Definition, gathering five heterogeneous fences under one column.

**RESOLUTION TRACE:** statement lines 274–276; consumed at rows 2, 5, 6, 13, 15, 17, 18, 21, 22, 25–28.

XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:T-scope` — count **42**.
XREF: `lean/notes/openmath/LEDGERLAMBDA_2026-08-08.md:LED-Λ(A1)` — count **5**.

**TEETH:** Mixed by item; inventoried per row in `.20` and in §5.

---
### EFF.GRTJB.20  [TABLE]  ★ THE CONDITIONALITY MATRIX — the shard's single most load-bearing unit ★

**CANONICAL STATEMENT:** the matrix header, verbatim, lines 290–291, followed by the 28-row table at lines 293–322.
**FORM:** display (a Markdown table, the note's only one in this range).

> “**THE MATRIX (28 claim rows × 8 proviso columns = 224 cells; `—` = not
> consumed / free).**”

**SOURCE-FIDELITY NOTE (rule 14, double-emission adapted).** The source rows are Markdown table cells containing `~~…~~` strikes and nested `[rN, F-#]` brackets; reproducing all 28 rows byte-for-byte here would duplicate ~30 source lines of dense markup already quoted at the cell-note and grade-cap units. **What is emitted:** (a) the compiler `[TABLE]` transcription below, cell-for-cell, with every YES/`—`/NONE preserved and every rider named by its round tag; (b) verbatim quotation of the SIX cells whose content is load-bearing beyond their row (rows 4, 5, 11, 12, 20, 24), given in full at `.13`, `.14`, `.21`–`.25` and here. **No cell is prosified away; the mapping is one row = one table line.**

`[TABLE]` **THE 28×8 MATRIX, transcribed.** Legend: `—` = not consumed/free; `YES*` = inherited (the clause speaks about objects a YES clause produced); `IND`/`SAME`/`NONE` per `.18`.

| # | claim (body site) | (a1) `P<q` | (a2) `P≤q` | (b) u ≥ 0 | (c) (VD-m) | (d) W2-C1 | (e) [RMG] | (f) evidence | (g) other scope |
|---|---|---|---|---|---|---|---|---|---|
| 1 | **JB-DEV(i)** same division, §2(i) | — | — | — | — | **YES** | — | **IND** `jb_dev` `fresh_dev` vs `PolyO.dev`, 893 · **+ SAME** sub-leg ⟨n1⟩ | — |
| 2 | **JB-DEV(ii)** byte clause, §2(ii) | — | **YES — its hypothesis** | — | — | — (W-2 cl. 2) | — | **IND** `jb_keyeq`, 25 rows (3 VACUOUS, T.n = 0) | TH-BASE ⇒ q = 1 always; W-2 (C-coll)/recursion split |
| 3 | **JB-DEV(iii)(VAL)**, §2(iii) | **YES** | — | — | — | YES\* (via row 1) | — | **IND** `G.vgen(q+1,A)` vs `T.wlev(q,A)`, 0 ≤ q ≤ qcap | — |
| 4 | **JB-DEV(iii)(GRID)**, §2(iii) | **YES** | — | **YES — NARROWED [r5, F-3]** | — | YES\* | — | carry half **IND** (`jb_eps`); grid/abscissa half **NONE** | W2-L0 consumed |
| 5 | **JB-DEV(iii)(RES)**, §2(iii) | insufficient — see (a2) | **YES [r3, F-4]** | — | at m = q+1 ≥ 3: **(VD-(m−1)) at EVERY ON-LINE DIGIT [r4, F-1]** ⟨n4⟩ | YES\* | — | **NONE** — no family keys (RES) anywhere ⟨n4⟩ | JA-RES's own fence: free at m = 2, per-digit proviso at m ≥ 3 |
| 6 | **JB-DEV(iv)** cross-key fence, §2(iv) | — | — | — | — | — | — | **NONE** (a displayed fence) | J-A §4(i); W-2 cl. 2/3 the only lawful transport |
| 7 | **LEMMA JB-AFF**, §3 | — | — | — | — | — | — | **NONE** as a lemma — exercised inside rows 9/10 | unconditional, two lines |
| 8 | **JB-VTX(a)** pointwise shear | **YES** | — | — | — | **YES** | — | **IND** print vs harness ordinates, 893 | cites print `propertiesv` item 3 |
| 9 | **JB-VTX(b)** vertex-for-vertex | **YES** (via 8) | — | — | — | **YES** | — | **IND** fresh lower hulls of BOTH frames + vertex bijection | — |
| 10 | **JB-VTX(c)** slope/length | **YES** (via 8) | — | — | — | **YES** | — | **IND** `hull_sides` per-side slope/length law | — |
| 11 | **JB-VTX(d1–d3)** the THREE min ties | **SPLIT [r6, F-1]:** `P<q` fences **(d1)/(d2) ONLY** | **YES for (d3) [r6, F-1]** — JA-VAL at level q+1 | — | — | **YES** | — | **IND** three tie assertions ⟨n3⟩ | — |
| 12 | **JB-VTX(d4)** attained abscissas = read grid | **YES** | — | **YES — NARROWED [r5, F-3]** | — | **YES** | [ILN]† S0.2 read assembly | **NONE [r3, F-3]** ⟨n3⟩ | — |
| 13 | **JB-VTX(e)** window clause | YES\* (via 8 at f = Φ_{q+1}^har) | — | — | — | **YES — W2-C1a** | — | **NONE** (none claimed) | subject is the KEY, not the quantified f (r1, G-4) |
| 14 | **JB-ID** — (ID-(i+1)) as the key's own development, §4(ii) | — | — | — | — | — | **YES** S2.2 (ID-(i+1)); P_i := e_i·g_i from S0.1 **[r3, F-7]** | **IND** `jb_id` + a genuinely print-side leg | — |
| 15 | **JB-TREE(i)** tree = classifier's division | — | — | — | — | **YES** (W2-C3 chamber off the byte perimeter) | **YES** T-TERM, L-EXACT, L-CANON | **IND** fresh tree walk + post-seal walker leg A (84 walks) · **+ SAME** ⟨n2⟩ · 8 chamber walks **NONE** | T-scope(m), g_m = 1 |
| 16 | **JB-TREE(ii)** each edge = one division step | — | — | — | — | — | **YES** S2.2 + L-NORM + L-CELL | **IND** `jb_id` digit list + `jb_tree` L-NORM assertions | — |
| 17 | **JB-TREE(iii)** λ_E face = LINE-functional bookkeeping; v_{m+1} at R-LEAVES only **[r4, F-4]** | **YES** | — | — | — | YES\* | **YES** L-LINE(i)–(iii) per edge; L-LINE(iv) **REDUCED CELLS ONLY [r4, F-4]**; S3.2 | **IND** `jb_line` fresh λ_E quanta on line(·) + leaf line == wlev == vgen; **no internal-node v_{m+1} claim [r4, F-4]** | **LED-Λ at ATTEMPT grade — the tie's grade rides it** |
| 18 | **JB-TREE(iv)** (RM-m) as transported instance | **YES** | — | — | **YES for the (C-READ) leg** | YES\* | **YES** all four box clauses | (C-W_R) **IND**; **(C-W_Q) NONE**; (C-READ) **IND** on the scored stratum | T-scope(m), g_m = 1 |
| 19 | **LEMMA JB-EPS**, §5 | — | — | — | — | — | JA-GRID(c) = (C-EPS) | **IND** `jb_eps`, 955 | **unconditional at every m ≥ 1** |
| 20 | **JB-EPS APPLIED at (V,V′) = (λ, γ_{m+1})** | — | — | — | inherits row 21 | — | **YES — the RESTORED (Ĉ-wt) licenses it [r3, F-5]** | **[r4, F-5]** a STRIDED SPOT-CHECK, not a superset: sampled on **4 of 56** roster scored rows only; **NONE** on the other 52 | **[r5, F-4]** frontier: adjudicated **OUT** |
| 21 | **JB-CREAD** ρ_m(R) = c_m·ρ_m(f), v ≠ 0 | — for the STATEMENT ⟨n5⟩ | — | — | **YES — the governing fence** | — | **YES** (C-READ), (C-W_R), the complete Ĉ_m list, L-CELL(i)/(ii) | **IND** end-to-end cross-engine, 104 scored / 21 boundary · **+ IND** teeth MJB-CREAD (22) | v ≠ 0 stratum; g_m = 1; T-scope(m) |
| 22 | **JB-CREAD, v = 0 branch** | — ⟨n5⟩ | — | — | **YES** ((VD-m) at f) | — | **YES** — (C-READ) gives the TARGET read only | **NONE — machine UNEXERCISED** (v = 0 census: 0 rows) | read-at-target (0 = 0) only |
| 23 | **JB-BOX-1** blueprint carry placement | — | — | — | inherits row 21 | — | (C-READ) is the HARNESS-frame form | **IND** teeth MJB-CREAD — 22 samples over 14 towers | — |
| 24 | **JB-BOX-2** the carrier box | records 3,4,8–13,17,18 **[r4, F-7:** row 5 dropped**]** | records 2,5 **[r4, F-7]** + row 11's (d3) **[r6, F-1]** | records 4,12 | records 18,21,22,23 **[r4, F-7]** | **[r5, F-5]** — the box records NO W2-C1 | — | n/a (record) | — |
| 25 | **JB-BOX-3** cross-key fence | — | — | — | — | — | — | n/a (record) | no cross-representative operator or byte identity anywhere |
| 26 | **JB-BOX-4** tree scope | — | — | — | — | — | **YES** ([RMG]'s fences inherited verbatim) | n/a (record) — the FRESH λ_E re-verification of row 17 is the decorrelation | T-scope(m), g_m = 1, W-WIN unconsumed, LED-Λ ATTEMPT |
| 27 | **JB-BOX-5** instance perimeter | — | — | — | — | — | — | n/a (record) — **F_p[[t]] rows have NO external (PARI) oracle leg** | 16-tower roster + 5 QO shapes + 4 fresh d₀ ≥ 2 shapes |
| 28 | **JB-BOX-6** standing fences | — | — | — | — | — | — | n/a (record) | no gr/carrier (J-C), no count/menu/density (J-D), P0 gate stands, counter 0/2 |

**MANDATORY ARITHMETIC AUDIT (rule 22) — computed fresh by this compiler, never taken from the source's labels.**

- **Row count.** Transcribed rows = **28**. Source header claims 28. ✔
- **Column count.** Proviso columns (a1),(a2),(b),(c),(d),(e),(f),(g) = **8**. Source header claims 8. ✔
- **Cell count.** 28 × 8 = **224**. Source header claims 224. ✔
- **`P≤q` consumers (column a2 non-blank).** Rows **2, 5, 11(d3)** = **3**. Summary point (2) as recounted at r6 says “THREE rows consume `P≤q` — 2, 5, and row 11's (d3) sub-clause”. ✔ (The pre-r6 claim of TWO is struck; see `.27`.) Row 24's (a2) record cell lists the same three. ✔ **Cross-check against JB-BOX-2's enumeration (L2394–2400, shard 2): §2(ii)'s byte clause [row 2], §2(iii)(RES) [row 5], JB-VTX(d3) [row 11 (a2)] = 3.** ✔
- **`u ≥ 0` consumers (column b non-blank).** Rows **4, 12** = **2**. Summary point (3) says “Exactly two rows consume the u ≥ 0 proviso (4 and 12)”. ✔ JB-BOX-2's own statement (L2407–2409): “the u ≥ 0 proviso of this box reaches EXACTLY TWO claims”. ✔
- **`(VD-m)` consumers (column c non-blank).** Rows **5** (at the level BELOW, m−1), **18, 20 (inherited), 21, 22, 23 (inherited)**. Summary point (4) as rewritten at r4 says the fence “AT THE CLAIM'S OWN READ LEVEL reaches exactly rows 18, 21, 22 and 23”, with row 5 riding `(VD-(m−1))` **one level down** and rows 20/23 inheriting row 21's context. **Recount: own-read-level = {18, 21, 22, 23} = 4** ✔; **one-level-down = {5} = 1** ✔; **inherited = {20, 23}**. **Discrepancy flagged:** row 23's cell says “inherits row 21” yet summary point (4) counts 23 among the OWN-read-level rows, and row 24's (c) record cell also lists 23. This is a classification overlap, not a count error — 23 (JB-BOX-1) inherits JB-CREAD's fence *and* is listed as a fence-carrying row. **Recorded as source defect 3 in §8; no cell moves.**
- **`NONE`-evidence cells with an OPEN proviso (the frontier).** Rows **4** (grid half), **5**, **12**, **22** = **4**. Summary point (1) as recounted at r4 and amended at r5 says FOUR: rows 4, 5, 12, 22. ✔ **Excluded with reasons displayed:** row 13 and row 18's (C-W_Q) sub-cell (no-leg but no OPEN proviso — consumption at grade), and row 20 (r5, F-4: its (c) is inherited, its own conditionality is the [RMG] license). ✔ **Independent cross-check against the acceptance record (L3117–3119, shard 3): “the four-member NO-LEG frontier (rows 4/5/12/22)”.** ✔ **And against the 2026-08-08 annex (L3159–3160): “The four-member NO-LEG frontier (rows 4/5/12/22) is UNCHANGED”.** ✔ **Three independent statements of the same four; arithmetic consistent.**
- **`n/a (record)` rows.** Rows **24–28** = **5** boxes. ✔ Matches §6's five honest boxes plus JB-BOX-1 at row 23 = six boxes total in the note. ✔
- **Rows with `IND` evidence.** 1, 2, 3, 4 (carry half), 8, 9, 10, 11, 14, 15, 16, 17, 18 (two of three legs), 19, 21, 23 = **16**. Rows with `NONE` somewhere: 4, 5, 6, 7, 12, 13, 15 (chamber walks), 18 ((C-W_Q)), 20, 22 = **10**. Rows `n/a`: 24–28 = **5**. **Sum with overlap accounted (rows appearing in both IND and NONE: 4, 15, 18): 16 + 10 + 5 − 3 = 28.** ✔

**CONDITIONALITY:** The matrix is the note's conditionality-of-record and **GOVERNS every grade surface** (FREEZE PREDICATE 2). Its own precision was corrected in four later rounds: **r4/F-1** (summary point (4) contradicted row 18; row 5's (c) understated JA-RES), **r4/F-2** (the NO-LEG census undercounted, 3 → 4), **r4/F-5** (row 20's machine cell misdescribed `jb_eps` twice), **r4/F-7** (three surface-vs-table disagreements at row 24), **r5/F-3** (rows 4/12's column (b) narrowed), **r5/F-4** (row 20 adjudicated out of the frontier), **r5/F-5** (row 24's (d) cell asserted a record JB-BOX-2 does not carry), **r6/F-1** (row 11 SPLIT). **Two inbound supplier corrections read onto it:** E-1 onto column (c)'s “(R-coll)” label; E-2 onto row 15's W2-C3 grade.

**DERIVATION:** Each cell is filled “from the BODY PROOF (not from any existing grade line)” (`.11`). The per-cell derivations are the §§2–5 theorem bodies (shard 2); the five cells that need a sentence are `.21`–`.25`.

**RESOLUTION TRACE:** statement lines 290–322; proof lines 1400–2308 (§§2–5, shard 2); correction sites 950–1028 (r4), 1053–1101 (r5), 1127–1190 (r6), 1218–1271 (r7), 3125–3142 (E-1/E-2), 3230–3242 and 3298–3309 (E-3/E-4 consumer sweeps, which explicitly leave the cells unchanged).

**TEETH:** Per-row, column (f). Aggregate: **16 rows IND, 10 rows carrying a NONE somewhere, 5 record rows, 4 frontier cells.** Full inverse table at §5.

---
### EFF.GRTJB.21  [instrument-record]  ⟨n1⟩

**CANONICAL STATEMENT:** verbatim, lines 326–337.
**FORM:** bold-headed paragraph (a numbered cell note).

> “⟨n1⟩ **Row 1, column (f) — [r3, F-2].** `jb_dev`'s genuine second computation
> is `fresh_dev` (this runner's own schoolbook division) against `T.P.dev`, and
> its genuine CROSS-ENGINE content is row 3's digit-weight tie. Its third leg —
> `G.P.dev(f, G.phi[q+1])`, advertised in r0–r2 as "compared against **both
> engines'** digit lists" — is **SAME**: `iterlawn_pe_reimpl.PolyO` carries only
> `self.R`, and `gmn_from_tower` builds `GmnLeg(T.R, …)` whose `self.P =
> ITL.PolyO(R)` holds THE SAME ring object, so `G.P.dev` and `T.P.dev` are the
> identical method; the leg is guarded by `tuple(G.phi[q+1]) == key`, so the
> arguments are byte-equal too, and it sits AFTER a `continue` on `dvF != dvI`,
> so it is reached only once agreement is already forced. **The violation
> `'fresh dev != print dev'` is unreachable.** There is ONE engine comparison in
> this family, not two.”

**SUPERSESSION KIND:** `counter re-reading` — an advertised second engine is re-read as the same computation.

**CONDITIONALITY:** Unconditional as a code fact. **It DOWNGRADES the note's own advertised evidence** and is one of three sites where the same disease was found (PE1/G-1 at the tree family, PE2/G2-2 inside the repair instrument, PE3/F-2 here).

**DERIVATION:** Code reading, displayed: `PolyO` carries only `self.R`; `gmn_from_tower` builds `GmnLeg(T.R, …)`; the guard `tuple(G.phi[q+1]) == key` forces byte-equal arguments; the `continue` on `dvF != dvI` precedes it. **Independently checked by this compiler at the source:** `verification/openmath/grt_weld_probe.py` L456–459 is `def gmn_from_tower(T, mut=False)` building `levels = [(T.e[i], T.h[i], list(T.psi[i])) for i in range(T.NR)]` and returning `GmnLeg(T.R, T.d0, T.Phi[0], levels, …)` — **the cited construction is byte-confirmed**; the ring argument is `T.R`, the tower's own ring, exactly as the note says.

**RESOLUTION TRACE:** statement lines 326–337; the disposition at 898–905 (r3 STEP 4, F-2); the surfaces it corrects at 1591–1609 (§2's machine bracket, shard 2) and 2480 (§7.1's JB-DEV row, shard 3).

**TEETH:** **AUDIT — in-house hostile pass, disposition `stale self-description`** (rules 20, 27): a frozen self-description (“both engines' digit lists”) that the instrument's own code falsifies.

---
### EFF.GRTJB.22  [instrument-record]  ⟨n2⟩

**CANONICAL STATEMENT:** verbatim, lines 339–345.
**FORM:** bold-headed paragraph.

> “⟨n2⟩ **Row 15, column (f) — PE1/G-1, already corrected in r1's wording at
> three sites and kept here as a matrix cell.** The sealed tree family's
> print-key leg is `fresh_divmod` re-executed on byte-equal arguments behind the
> `byteeq` guard: **SAME**. The independent print-key evidence is the post-seal
> walker's leg A (§7.4(B), 84 walks, its own keys/correction digits/divisor/
> division code), and it does not reach the four byte-unequal CHAMBER rows
> (8 walks, **NONE**, disclosed at §7.4).”

**CONDITIONALITY:** Unconditional. **The 8 unreached chamber walks are a standing coverage hole**, print-unchecked by BOTH instruments (§7.4, shard 3: “STILL PRINT-UNCHECKED, by both instruments: the 8 walks on the four byte-unequal CHAMBER rows `T3A/tw`, `T3C/tw`, `T3D/tw`, `T3E/tw` at m = 2”).

**DERIVATION:** Code fact + the post-seal repair's own scope. `fresh_divmod` is “a pure function of (R, f, key), so on equal tuples the second call cannot fail unless the first does” (L1971–1973, shard 2).

**RESOLUTION TRACE:** statement lines 339–345; origin 660–672 (r1 G-1); the walker's verdict 2766–2846 (shard 3); the coverage correction 784–790 (r2 G2-3).

**PIN VERIFICATION:** `verification/openmath/grt_jb_printwalk.py` EXISTS; `grt_jb_printwalk_output.txt`, `grt_jb_printwalk_results.json` EXIST.

**TEETH:** **Disposition: `disclosed non-repair` + `accepted-with-decorrelation-supplied`** (rule 20). The sealed leg carries no information; the post-seal walker supplies genuinely decorrelated print-key evidence on base rows, and the 8 chamber walks stay uncovered.

---
### EFF.GRTJB.23  [instrument-record]  ⟨n3⟩

**CANONICAL STATEMENT:** verbatim, lines 347–368.
**FORM:** bold-headed paragraph with a nested `[r7]` transcription rider.

> “⟨n3⟩ **Rows 11/12, column (f) — [r3, F-3].** `jb_shear_vtx` contains exactly
> THREE tie assertions: `minH == T.wlev(q+1,f)` (d2), and under `q <= L` both
> `minU == G.vgen(q+1,f)` (d1) and `minH == G.vgen(q+2,f)` (d3). **[r7, PE7
> m-3 — byte-faithful transcription of (d3)'s guard: the code's d3 assertion
> (grt_jb_checks.py L283) carries a SECOND conjunct, `q + 1 <= G.RANK` — a
> vgen-domain check, IDENTICALLY TRUE on the loop domain, since RANK = T.NR =
> n+1 and the loop caps q ≤ qcap ≤ n, so RANK = n+1 ≥ qcap+1 — verified
> redundant by PE7 (`GRTJB_passPE7_report.md` m-3, as of commit aa9b603); the
> effective (d3) gate is q ≤ shared_upto = `P≤q` exactly, so every coverage
> claim reading this cell stands unchanged.]** Clause (d)'s
> FOURTH tie — the attained abscissas on the realized side are the read grid
> s(λ) + j·e_q and the level-(q+1) read is assembled from the on-line digits at
> those slots — **has no leg in any family**: `jb_dev` keys only the (VAL) weight
> tie, `jb_line` keys line == wlev == vgen on reduced cells, `jb_cread` evaluates
> (VD-m), and `jb_eps` keys JA-GRID's **carry** clause (c), which is the OTHER
> half of the (GRID) layer and the half that carries no proviso. So the single
> sub-clause with no machine leg is also the single sub-clause riding the
> undischarged u ≥ 0 proviso (row 12 columns (b) and (f) together) **[r5, F-3 —
> the proviso now NARROWED to the membership residue, column (b) and §5]**.
> Every surface
> that used to say "all four min/read ties" now says **three keyed, (d4)
> unkeyed**.”

**PIN VERIFICATION (rule 23) — the code transcription checked byte-for-byte by this compiler.** `verification/openmath/grt_jb_checks.py` **line 283** reads exactly:

```
                if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):
```

**EXACT match to the note's transcription.** The `RANK = T.NR` claim is confirmed at the cited source: `grt_weld_probe.py` L211 is `self.RANK = len(levels)`, and `gmn_from_tower` (L456–459) builds `levels = [… for i in range(T.NR)]`, so `RANK = len(levels) = T.NR`. **The redundancy derivation is therefore source-true, and the note's four live transcriptions of this gate are byte-faithful.**

**SUPERSESSION KIND:** `counter re-reading` (r3/F-3: “all four ties” recounted to three keyed) + `wording-rider` (r7/m-3: the second conjunct disclosed at all four live sites).

**CONDITIONALITY:** Unconditional as a code fact. **The disclosed coincidence is the note's own most damaging honest statement about its evidence**: “the single sub-clause with no machine leg is also the single sub-clause riding the undischarged u ≥ 0 proviso”.

**DERIVATION:** Exhaustive over the instrument's families — the note enumerates all four (`jb_dev`, `jb_line`, `jb_cread`, `jb_eps`) and shows none keys (d4).

**RESOLUTION TRACE:** statement lines 347–368; the disposition 905–908 (r3 F-3); the four live transcription sites 1755–1778 (§3's machine bracket, shard 2), 2482 (§7.1's JB-SHEAR row, shard 3), 1150–1155 (the r6 block's MACHINE clause), and this cell; the m-3 sweep at 1259–1271.

**TEETH:** **PROOF-ONLY row (rule 16), with the note's own coverage-hole sentence quoted:** “**THE FOURTH TIE (d4) HAS NO LEG IN ANY FAMILY OF ANY INSTRUMENT**” (L1768–1769). Disposition: **disclosed non-repair**.

---
### EFF.GRTJB.24  [supplier-finding]  ⟨n4⟩

**CANONICAL STATEMENT:** verbatim, lines 370–386.
**FORM:** bold-headed paragraph with a nested `[r4]` correction.

> “⟨n4⟩ **Row 5, columns (a2)/(c)/(f) — [r3, F-4].** (RES) is JA-RES at read level
> m := q+1. J-A's perimeter is level-indexed — "Shared-key perimeter at level m:
> Φ_q = φ_{q+1} byte-for-byte for all q ≤ m−1" — so at m = q+1 it requires
> agreement for j ≤ q, i.e. `P≤q`, NOT `P<q`. r2 fenced all three layers of
> §2(iii) with `P<q`, which is correct for (VAL) (JA-VAL at level q) and one
> level short for (RES); ~~the two differ exactly at q = qcap, where `P≤q` fails by
> definition~~ **[r4, F-3 — corrected: the exclusion at q = qcap bites only when
> shared_upto < n (5 of the 16 roster towers); on the other 11 the two fences
> coincide over the whole level range — column (a2)]**. (RES) does NOT consume
> (VD-m) — it is the PER-SLOT law — **[r4, F-1 — at the row's OWN read level; at
> m = q+1 ≥ 3 its per-digit proviso IS (VD-(m−1)) at every on-line digit, an
> evaluated-dictionary hypothesis ONE level down, now recorded in column (c)]**
> but it carries JA-RES's own fence: unconditional at m = 2, per-digit proviso
> at m ≥ 3 (JA-BOX-2). No machine leg can catch the mis-fencing because no family keys
> (RES) at all. Nothing inside §3–§5 consumes (RES), so the note's internal chain
> is unaffected; what was over-supplied is JB-DEV(iii)'s (RES) layer as handed to
> a downstream unit through §7.3.”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding` — the content is a defect report against the note's OWN earlier fencing of a SUPPLIER's level-indexed perimeter, discharged by re-fencing rather than by a new lemma. It quotes J-A's perimeter sentence as the ground.

**SUPERSESSION KIND:** `scope-pin` (the (RES) layer moves to a strictly stronger fence) + `counter re-reading` (the r4 arithmetic correction inside it).

**CONDITIONALITY:** The re-fence is a strict narrowing — “This moves toward MORE conditionality” (L1447–1448, shard 2). **The representative-pin rescue is explicitly REFUSED** (L918–921): “The alternative repair — arguing that the representative pin φ_{q+1} := Φ_q^har discharges J-A's j = q requirement — is NOT taken: it is not derived anywhere in this note, and adopting it would also weaken what (VAL)'s fence is doing.” **That refusal binds r6's (d3) re-fence too** (`.73`).

**DERIVATION:** Level-index arithmetic on J-A's own quantifier, quoted inside the cell. Nothing else is used.

**RESOLUTION TRACE:** statement lines 370–386; the same analysis at §1's r3 amendment 1340–1364 (shard 2) and §2(iii)'s r3 bracket 1439–1454 (shard 2); disposition 914–923 (r3, stated separately as “the one MATHEMATICAL movement in r3”).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-RES` — count **20**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-BOX-2` — count **7**.

**TEETH:** **`NONE`, signed.** “No machine leg can catch the mis-fencing because no family keys (RES) at all.” Disposition: **disclosed non-repair** — a mathematical fence found and moved with zero instrument resolution, by reading the supplier's quantifier.

---
### EFF.GRTJB.25  [instrument-record]  ⟨n5⟩

**CANONICAL STATEMENT:** verbatim, lines 388–393.
**FORM:** bold-headed paragraph.

> “⟨n5⟩ **Rows 21/22, column (a1).** §5's print-side content enters ONLY through
> the (VD-m) hypothesis, so THEOREM JB-CREAD is a legitimate conditional at any
> level and needs no key perimeter of its own. Disclosure, not a fence: the
> INSTRUMENT cuts reduction levels at `qcap_of(T,G)` before `jb_tree`/`jb_cread`,
> and the off-perimeter counter is **0** on the roster, so nothing was scored
> outside that cut.”

**CONDITIONALITY:** Unconditional; and it makes an explicit **statement-scope vs instrument-scope** separation — the instrument's level cut is a coverage disclosure, not a hypothesis of the theorem.

**DERIVATION:** Structural: JB-CREAD's only print-side input is (VD-m), which is a hypothesis; a conditional needs no perimeter for a hypothesis it assumes.

**RESOLUTION TRACE:** statement lines 388–393; consumed at the grade cap's JB-CREAD bullet (`.33`) and at §5's regenerated ∎ Grade block (L2274–2278, shard 2).

**TEETH:** Off-perimeter counter **0** on the roster (a coverage census, not a law check). Disposition: **measurement**.

---
### EFF.GRTJB.26  [scope record]

**CANONICAL STATEMENT:** verbatim, lines 395–422 — summary point (1), the NO-LEG frontier, with its full three-layer correction chain.
**FORM:** bold-headed paragraph with two nested amendment brackets.

> “**What the matrix shows that no earlier surface stated.** ~~(1) Three cells hold
> an open proviso with NO machine leg beside it — rows 5 (RES), 12 (d4), 22
> (v = 0) — and one of them (row 12) is the u ≥ 0 rider; those three are the
> note's honest evidence frontier.~~ **[r4, F-2 — RECOUNTED under the sentence's
> own criterion; the struck count missed row 4 and its uniqueness claim was
> false. (1) FOUR cells hold an open proviso with NO machine leg beside it —
> rows 4 (the (GRID) grid/attained-abscissa half; its carry half is IND via
> `jb_eps`), 5 (RES), 12 (d4) and 22 (v = 0) — and TWO of them, rows 4 and 12,
> are the u ≥ 0 riders: BOTH riders have a NONE half. Those FOUR are the note's
> honest evidence frontier. ADJUDICATED AND EXCLUDED, with the reason stated:
> row 13 (JB-VTX(e)) and row 18's (C-W_Q) sub-cell are NO-LEG cells but carry no
> OPEN proviso — their conditionality is consumption at grade (W2-C1a for
> row 13; [RMG] ACCEPTED plus the m ≤ qcap perimeter for (C-W_Q)), not an
> undischarged hypothesis — so they stand as no-leg DISCLOSURES (named at the
> grade cap, §7.2 and here) outside the open-proviso frontier.]** **[r5 — TWO
> AMENDMENTS TO THE CENSUS, COUNT UNCHANGED AT FOUR. (F-3) Rows 4/12's open
> proviso is NARROWED, not cleared: u ≥ 0 is PROVED on all of 𝒲_{q+1} (§5's
> r5 display), and what remains open at both rows is the MEMBERSHIP hypothesis
> w_{q+1}(f) ∈ 𝒲_{q+1} at their unbounded-degree quantifiers — established for
> deg f < deg Φ_{q+1}, not off it — so BOTH REMAIN frontier members. (F-4)
> Row 20, which the r4/F-5 rewrite made a candidate fifth member ("Instance-keyed
> evidence: NONE on those 52" beside an inherited (c) cell), is ADJUDICATED OUT:
> its column (c) is row 21's (VD-m) context INHERITED — an open hypothesis OF
> rows 21/22, where it is already counted and where row 21's end-to-end IND leg
> sits — not an open proviso of row 20's own; row 20's own conditionality is
> column (e)'s [RMG] license, riding the lemma's PROOF at the derived
> membership — consumption at grade, the rows-13/18 exclusion genre. THE
> FRONTIER IS ROWS 4, 5, 12, 22.]**”

**CHAIN (rule 25):** r3's census of THREE → **r4/F-2** recount to FOUR with two exclusions adjudicated → **r5/F-3** narrowing (count unchanged) + **r5/F-4** a third exclusion adjudicated. **TERMINAL: “THE FRONTIER IS ROWS 4, 5, 12, 22.”**

**SUPERSESSION KIND:** `counter re-reading` (r4: a count recomputed under the sentence's own criterion, and a false uniqueness claim withdrawn) + `scope-pin` (r5/F-3) + `inventory completion` (r5/F-4's adjudication).

**CONDITIONALITY:** **This is the note's honest evidence frontier and the single most consumed record in the whole GRTJB stack** — the acceptance record and the 2026-08-08 annex both re-state it verbatim. **Its criterion is stated and applied consistently**: a cell is a frontier member iff it holds an OPEN proviso AND has no machine leg; no-leg cells whose conditionality is *consumption at grade* are excluded with reasons displayed (rows 13, 18(C-W_Q), 20).

**DERIVATION:** A recount over the matrix under a stated criterion. **This compiler independently recomputed it from the transcribed matrix (`.20`) and gets the same four** — see the arithmetic audit at `.20`, bullet 6.

**RESOLUTION TRACE:** statement lines 395–422; corrections 959–967 (r4 F-2), 1053–1073 (r5 F-3), 1089–1095 (r5 F-4); re-stated at 3117–3119 and 3159–3160 (shard 3).

**TEETH:** By construction the frontier IS the set of teeth-less open cells. Disposition: **signed vacuity disclosure** (rule 20) for the frontier as a whole.

---
### EFF.GRTJB.27  [scope record]

**CANONICAL STATEMENT:** verbatim, lines 422–428 — summary point (2).
**FORM:** bracketed rider on a struck sentence.

> “~~(2) Exactly two
> rows consume `P≤q` (2 and 5),
> and only one of them was ever fenced that way.~~ **[r6, F-1 — (2) RECOUNTED:
> THREE rows consume `P≤q` — 2, 5, and row 11's (d3) sub-clause (JA-VAL at
> level q+1) — and only row 2 was fenced that way from r0: (RES) was re-fenced
> at r3/F-4, (d3) at r6/F-1, both instances of the same level-indexing
> disease.]**”

**CHAIN:** r3's TWO → **r6/F-1** recount to THREE. **TERMINAL = THREE (rows 2, 5, 11(d3)).**

**SUPERSESSION KIND:** `counter re-reading`.

**CONDITIONALITY:** Unconditional as a count. **Arithmetic audit (rule 22): this compiler's independent recount of column (a2) in `.20` gives exactly rows 2, 5, 11(d3) = 3.** ✔ Cross-checked against JB-BOX-2's `P≤q` list (shard 2, L2394–2400) = 3. ✔

**DERIVATION:** A recount over column (a2), plus the diagnosis that both re-fences are the same disease (a level-indexed supplier perimeter instantiated at the consumer's own level instead of the cited theorem's).

**RESOLUTION TRACE:** statement lines 422–428; the r6 disposition 1127–1163; the third consumer's own derivation at §3(d) 1665–1675 (shard 2).

**TEETH:** (d3) has a full IND leg on its re-fenced range (the runner's `q ≤ shared_upto` gate IS the fence); (RES) has NONE; row 2 has IND. Disposition: mixed — **executable regression** for two of three, **disclosed non-repair** for (RES).

---
### EFF.GRTJB.28  [scope record]

**CANONICAL STATEMENT:** verbatim, lines 428–431 — summary point (3).
**FORM:** inline sentence with a bracketed rider.

> “(3) Exactly two rows consume the
> u ≥ 0 proviso (4 and 12), and every surface must therefore name JB-VTX(d)'s
> grid content as well as JB-DEV(iii)(GRID) **[r5, F-3 — both now carrying the
> narrowed membership residue, column (b)]**.”

**SUPERSESSION KIND:** `scope-pin` (the residue is narrowed; the count is untouched).

**CONDITIONALITY:** Unconditional as a count. **Arithmetic audit: column (b) non-blank at rows 4, 12 = 2.** ✔ Cross-checked against JB-BOX-2 (“reaches EXACTLY TWO claims”, L2407–2409). ✔

**DERIVATION:** A recount over column (b). Its consequence clause — that a surface naming only JB-DEV(iii)(GRID) is incomplete — is exactly the defect PE3's F-1 found.

**RESOLUTION TRACE:** statement lines 428–431; PE3's F-1 at 2580–2582 (shard 3, §7.2's superseded-table note); the narrowing at 1053–1073.

**TEETH:** Both consumers' grid halves are `NONE`. Disposition: **disclosed non-repair**.

---
### EFF.GRTJB.29  [scope record]

**CANONICAL STATEMENT:** verbatim, lines 431–441 — summary point (4).
**FORM:** bracketed rider on a struck sentence.

> “~~(4) The (VD-m) fence reaches exactly
> rows 18 (its (C-READ) leg), 21, 22 and 23 — nothing in §2–§4 rides it.~~
> **[r4, F-1 — the struck sentence contradicted the table's own row 18 (a §4
> row: JB-TREE(iv)) four lines above it, and surfaces 4 and 6 say the opposite
> too. (4) The (VD-m) fence AT THE CLAIM'S OWN READ LEVEL reaches exactly rows
> 18 (JB-TREE(iv)'s (C-READ) leg — a §4 row, riding §5's fence IN FULL), 21, 22
> and 23; nothing in §2–§3 rides the level-m dictionary, and §4 rides it exactly
> through that one leg. ONE LEVEL DOWN: at m = q+1 ≥ 3, row 5 ((RES)) rides
> (VD-(m−1)) at every on-line digit — JA-RES's per-digit proviso, an
> evaluated-dictionary hypothesis at level m−1 ≥ 2, recorded in column (c) as of
> r4.]**”

**CHAIN:** r3's “nothing in §2–§4 rides it” → **r4/F-1** correction (§4 DOES ride it, through row 18; and row 5 rides the fence one level down). **TERMINAL = the r4 statement.**

**SUPERSESSION KIND:** `counter re-reading` — a self-contradiction inside one section, caught by the matrix's own row four lines above the summary.

**CONDITIONALITY:** Unconditional. **This is the clearest instance of the matrix mechanism working as designed**: the defect was a summary contradicting its own table, which is exactly what a single-surface audit is supposed to expose.

**DERIVATION:** A recount over column (c) at two different read levels. **Arithmetic audit (rule 22): see `.20` bullet 5 — own-read-level {18, 21, 22, 23} = 4 ✔; one-level-down {5} = 1 ✔; with the row-23 classification overlap flagged as source defect 3.**

**RESOLUTION TRACE:** statement lines 431–441; the disposition 950–958 (r4 F-1); the surfaces it re-syncs at 1015–1020 (r4 F-7) and 2410–2415 (JB-BOX-2, shard 2).

**TEETH:** Row 18's (C-READ) leg is IND on the scored stratum; its (C-W_Q) sub-cell is NONE; rows 21/23 IND; row 22 NONE/unexercised. Disposition: mixed.

---
### EFF.GRTJB.30  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 443–448 — the grade cap's regeneration preamble (SURFACE 1 of 14).
**FORM:** bold-headed bracketed rider.

> “**Grade cap (read first) — [r3, STEP 2: SURFACE 1 of 14, REGENERATED FROM
> §0M's MATRIX.** Every fence below is a cell of that table; the table carries
> no fence this cap omits. The r0/r1/r2 cap is retained in full immediately
> after this one, ENTIRELY SUPERSEDED and no longer authoritative — it is
> retained as a quoted block rather than struck inline only because it already
> contains r1/r2 strike markup, which cannot nest.**]**

**SUPERSESSION KIND:** `replacement` — the whole prior cap is superseded wholesale.

**TARGETS (rule 24):** `.38` (the retained r0/r1/r2 cap).

**CONDITIONALITY:** Unconditional as a generation declaration; it is FREEZE PREDICATE 2 applied to surface 1.

**DERIVATION:** Procedural. Its bidirectional claim — “Every fence below is a cell of that table; the table carries no fence this cap omits” — is checkable and is checked in §5's inverse audit below.

**RESOLUTION TRACE:** statement lines 443–448; the 14-surface list at 885–892; the retained cap 519–563.

**TEETH:** **AUDIT — in-house hostile pass**; PE4 verified “NO fifth instance of the old surface-divergence class” (L941–942).

---
### EFF.GRTJB.31  [lemma]  (grade surface — JB-DEV)

**CANONICAL STATEMENT:** verbatim, lines 450–468.
**FORM:** bold-headed bullet with an embedded per-clause fence list.

> “* **JB-DEV (§2) — PROVED at attempt grade, one perimeter PER LAYER.**
>   **(i)** same division at every level q ≥ 0, at the W2-C1 admissible
>   representative φ_{q+1} := Φ_q^har (row 1). **(ii)** byte clause on the
>   **BYTE-EQUAL CHAIN THROUGH q** (`P≤q`, §1); TH-BASE gives q = 1 always
>   (row 2). **(iii)** three layers, each on its OWN perimeter — this split is
>   the r3 correction: **(VAL)** on the **SHARED-KEY PERIMETER** `P<q`
>   (0 ≤ q ≤ qcap), off which (VAL) is FALSE, not merely unproved (row 3);
>   **(GRID)** on `P<q` **and** on JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso, which
>   is CARRIED AND UNDISCHARGED (row 4; r2/G2-5, JB-BOX-2) **[r5, F-3 —
>   narrowed: u ≥ 0 PROVED for deg f < deg Φ_{q+1} (V ∈ 𝒲_{q+1}, §5); the
>   carried residue is lattice membership at the unbounded-degree
>   quantifier]**; **(RES)** on the
>   **BYTE-EQUAL CHAIN THROUGH q** — `P≤q`, one level deeper than r2's fence,
>   because (RES) is JA-RES at read level m = q+1 (row 5, **[r3, F-4]**;
>   **[r4, F-3]** the deeper fence excludes a level only where shared_upto < n —
>   5 of the 16 roster towers, column (a2)) — plus
>   JA-RES's own fence (unconditional at m = 2, per-digit proviso at m ≥ 3,
>   JA-BOX-2 inherited); (RES) is NOT the evaluated dictionary (VD-m) (r1/F1's
>   reading fence stands). **(iv)** a displayed fence, cited (row 6).”

**CONDITIONALITY:** **CORRECTED FROM SHARD 3 BY CERTIFIER ANNEX E-4.** The clause “off which (VAL) is FALSE, not merely unproved” is withdrawn. E-4 (L3267–3272, L3301–3304):

> “Every live
> sentence saying that JB-DEV(iii)(VAL) or JB-VTX(a) is “FALSE, not merely
> unproved” off the shared-key perimeter is corrected to “NOT SUPPLIED by this
> note outside the stated perimeter.” Byte inequality of representatives removes
> the J-A theorem instance cited by the proof, but does not by itself imply
> inequality of the induced values on every polynomial.”

and, naming this surface: “In the grade cap, §2(iii), §2 ∎ Grade, the JB-VTX theorem head, §3 ∎ Grade, §7.2's JB-DEV/JB-VTX rows and §7.3's W-3 bullet, every live occurrence of “FALSE, not merely unproved” is read as “NOT SUPPLIED outside the stated perimeter”.” **SUPERSESSION KIND: `counter re-reading`** (an unsupported negation withdrawn; the positive scope is unchanged, “No perimeter is widened and no on-perimeter proof moves”).

**DERIVATION:** Regenerated from matrix rows 1–6; the bodies are §2(i)–(iv) with proofs at L1549–1553 (shard 2).

**RESOLUTION TRACE:** statement lines 450–468; proof lines 1400–1609 (§2, shard 2); correction sites 3267–3312 (E-4); the narrowing chain at `.14`.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-L0` — count **5**.

**TEETH:** rows 1–6: IND / IND / IND / IND+NONE / **NONE** / NONE. Disposition: **executable regression** for (i)(ii)(VAL); **disclosed non-repair** for (GRID)'s grid half and for (RES).

---
### EFF.GRTJB.32  [lemma]  (grade surface — JB-VTX)

**CANONICAL STATEMENT:** verbatim, lines 469–486.
**FORM:** bold-headed bullet with a struck clause and its `[r6]` replacement.

> “* **JB-VTX (§3) — PROVED at attempt grade on `P<q`** (0 ≤ q ≤ qcap,
>   `qcap_of(T,G) = min(T.n, shared_upto(T,G)+1)` — the runner's own quantifier;
>   off that perimeter clause (a)'s JA-VAL input is unavailable and (a) is FALSE,
>   not merely unproved), every statement at the harness key as the W2-C1
>   admissible representative; the shear is DISPLAYED (the GD-2/T-F convention
>   pin made explicit — the unsheared identification is FALSE and is this note's
>   teeth family). Clause-level: ~~(a)/(b)/(c) and the **THREE** min ties (d1–d3)
>   ride `P<q` + W2-C1 only (rows 8–11)~~ **[r6, F-1 — (a)/(b)/(c) and the min
>   ties (d1)/(d2) ride `P<q` + W2-C1 only (rows 8–10, row 11 (a1)); (d3) —
>   w_{q+1}(f) = v_{q+2}(f), JA-VAL AT LEVEL q+1 — rides the BYTE-EQUAL CHAIN
>   THROUGH q (`P≤q`) + W2-C1 instead (row 11 (a2), the r3/F-4 genre; bites at
>   q = qcap on the 5 shared_upto < n towers T3A/T3C/T3D/T3E/I4C; the runner's
>   q ≤ shared_upto gate is (d3)'s own fence and an instrument cut for (d1))]**;
>   **clause (d)'s FOURTH tie — attained
>   abscissas = the read grid — additionally rides the UNDISCHARGED u ≥ 0
>   proviso and has NO machine leg** (row 12, **[r3, F-1 + F-3]**; **[r5, F-3 —
>   narrowed: PROVED for deg f < deg Φ_{q+1}, membership residue off it, §5]**); (e) is at
>   f = Φ_{q+1}^har (W2-C1a), not at the theorem's quantified f (row 13).”

**CONDITIONALITY:** **TWO corrections land from shard 3.**
(a) **E-4** withdraws “(a) is FALSE, not merely unproved” → “NOT SUPPLIED outside the stated perimeter”, and adds the corrected scope display: “JB-VTX(a), and consequently (b)/(c)/(d1)/(d2)/(d4) at the theorem's common head, are asserted on `P<q` only; outside it this note makes no claim. The separately deeper fences remain unchanged: JB-DEV(iii)(RES) and JB-VTX(d3) continue to require `P≤q`.”
(b) **E-3** narrows clause (c): “**every occurrence of “slope/length” as “slope/abscissa-run”**”, because the shear “is not unimodular when e_q > 1”. E-3's consumer sweep item 3 names this surface explicitly: “The grade cap, §3 ∎ Grade surface, §7.2's JB-VTX row and §7.3's W-3 polygon bullet read every occurrence of “slope/length” as “slope/abscissa-run”.” **SUPERSESSION KIND: E-3 = `replacement` of a false extension (the ambient-lattice claim), E-4 = `counter re-reading`.**

**DERIVATION:** Regenerated from matrix rows 7–13; bodies at §3 (L1615–1712, shard 2), proof L1696–1699.

**RESOLUTION TRACE:** statement lines 469–486; proof lines 1615–1699 (shard 2); correction sites 1127–1163 (r6 F-1), 1053–1073 (r5 F-3), 3199–3245 (E-3), 3267–3312 (E-4).

**TEETH:** rows 8–11 IND; row 12 **NONE**; row 13 **NONE (none claimed)**. Teeth family **MJB-VTX** (unsheared frame, 3/3 caught) guards the shear's necessity.

---
### EFF.GRTJB.33  [lemma]  (grade surface — JB-TREE)

**CANONICAL STATEMENT:** verbatim, lines 487–498.
**FORM:** bold-headed bullet.

> “* **JB-TREE (§4) — PROVED at attempt grade on [RMG]'s own scope** (T-scope(m)
>   termination fence, g_m = 1 rows for the Ĉ_m instance), consuming [RMG] as
>   ACCEPTED and LED-Λ at ATTEMPT grade (its λ_E face is cited as the polygon
>   bookkeeping — **[r4, F-4] as per-edge laws of the LINE functional, with the
>   identification line = w_m = v_{m+1} asserted at the R-LEAVES only (row 17)**
>   — the grade rides). Clause-level: **(i)/(ii) are
>   PERIMETER-FREE** (rows 15–16); **(iii)/(iv) are asserted only at levels
>   m ≤ qcap** (`P<q` read at level m), since they consume JA-VAL (rows 17–18) —
>   **[r3, F-1B: this fence, which r2 added at §4 and §7.2 while certifying this
>   cap "already consistent", now reaches this cap and JB-BOX-2]**; (iv)'s
>   (C-READ) leg additionally rides §5's (VD-m) fence, and its (C-W_Q) clause has
>   NO machine leg.”

**CONDITIONALITY:** **E-2 reads onto the W2-C3 half of row 15's citation** (the chamber transport). LED-Λ's ATTEMPT grade rides; the note's own mitigation is that “the runner therefore re-verifies the λ_E quanta FRESH rather than trusting the ledger (decorrelation, not redundancy)” (JB-BOX-4, shard 2).

**DERIVATION:** Regenerated from matrix rows 14–18; bodies at §4 (L1784–1980, shard 2), proof L1905–1908.

**RESOLUTION TRACE:** statement lines 487–498; proof lines 1784–1980 (shard 2); correction sites 979–998 (r4 F-4, THE SCOPE REPAIR), 1074–1088 (r5 F-1/F-2), 3135–3142 (E-2).

XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:T-TERM` — count **11**.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:L-EXACT` — count **11**.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:L-LINE` — count **23**.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:S3.2` — count **3**.

**TEETH:** rows 14–18 mostly IND (`jb_id`, `jb_tree`, `jb_line`, the post-seal walker); **(C-W_Q) NONE**; 8 chamber walks NONE. Disposition: **executable regression + disclosed non-repair**.

---
### EFF.GRTJB.34  [lemma]  (grade surface — JB-CREAD)

**CANONICAL STATEMENT:** verbatim, lines 499–505.
**FORM:** bold-headed bullet.

> “* **JB-CREAD (§5) — PROVED on the (VD-m) perimeter ∩ {v ≠ 0}.** (VD-m) is
>   UNCONDITIONAL AT m ≤ 1 ONLY ((VD-1) = W2-L3); at every m ≥ 2 it is a
>   HYPOTHESIS (JA-VDIND's absolute character-triviality, ⊇ (R-coll)/per-digit at
>   m ≥ 3, JA-BOX-2), so **JB-CREAD has NO unconditional stratum above m = 1**:
>   the note's own sealed runner machine-evaluates (VD-2) FALSE on 10 of its 13
>   roster boundary rows (T3A/T3B/T3C/T3D; §7.1, r1/F1). The v = 0 branch is the
>   read-at-target statement only and is machine UNEXERCISED (row 22).”

**CONDITIONALITY:** **E-1 reads onto the “(R-coll)” label** (root-inclusive form of GRTJA at HEAD ≥ `5d95805`). The rest is the note's own honest perimeter, and it is the strongest negative statement the note makes about its own reach: **NO unconditional stratum above m = 1**.

**ARITHMETIC AUDIT (rule 22) of the census this bullet quotes.** Roster boundary rows by level (§7.4(A), shard 3): m=1: 0 · m=2: 10 (T3A 3, T3B 3, T3C 1, T3D 3) · m=3: 3 (I4B). **Sum 0+10+3 = 13** ✔ matches “13 ROSTER boundary rows”. Per-tower m=2 sum: 3+3+1+3 = **10** ✔. Scored rows: m=1: 45 · m=2: 8 · m=3: 3 → **56** ✔ matches “56 roster scored rows”. JSON cross-check: roster boundary 13 + chamber 8 = **21** ✔ matches the sealed `JB-CREAD-BOUNDARY` field. Non-chamber decomposition: 66 = roster 56 + QO 2 + d₀ 8 → **56+2+8 = 66** ✔; total scored 66 + 38 chamber = **104** ✔. **All six cross-checks consistent.**

**DERIVATION:** Regenerated from matrix rows 19–23; body at §5 (L1984–2308, shard 2), the five-line proof chain at L2223–2242.

**RESOLUTION TRACE:** statement lines 499–505; proof lines 2223–2251 (shard 2); correction sites 638–659 (r1 F1), 792–803 (r2 G2-4), 3125–3133 (E-1).

**TEETH:** row 21 IND end-to-end (104 scored / 21 boundary disclosed) + teeth MJB-CREAD (22 samples, 14 towers, all caught); **row 22 NONE — machine UNEXERCISED (v = 0 census: 0 rows)**. Disposition: **executable regression** + **signed vacuity disclosure** for the v = 0 branch.

---
### EFF.GRTJB.35  [lemma]  (grade surface — JB-EPS)

**CANONICAL STATEMENT:** verbatim, lines 506–509.
**FORM:** bold-headed bullet.

> “* **LEMMA JB-EPS — UNCONDITIONAL at every m ≥ 1** (row 19), and its
>   application inside §5 at (V, V′) = (λ, γ_{m+1}) is LICENSED by [RMG]'s
>   clause w_m(Ĉ_m) = γ_{m+1}, restored to §5's recital in r3 (row 20,
>   **[r3, F-5]**).”

**CONDITIONALITY:** **The lemma is the only unconditional statement in the note.** Its APPLICATION is not: row 20's license rides the restored `(Ĉ-wt)` clause, and row 20's machine cell is a strided spot-check sampled on only 4 of 56 roster scored rows (`.62`). The note states the separation plainly: “The license stands on the lemma's PROOF at the derived membership; an instance-keyed leg is named as a candidate instrument.”

**DERIVATION:** Regenerated from matrix rows 19–20; the lemma and its two-line proof at L2171–2184 (shard 2); the license derivation at L2113–2131 (shard 2).

**RESOLUTION TRACE:** statement lines 506–509; proof lines 2179–2183 (shard 2); the license 2113–2144 (shard 2); correction sites 893–897 (r3 STEP 3 = F-5), 999–1008 (r4 F-5), 1089–1095 (r5 F-4).

XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:(C-EPS)` — count **7**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-EPS` — count **13**.

**TEETH:** row 19 **IND** (`jb_eps`, 955 samples: ℓ-free `s_geo` + fresh Bézout against the ℓ-form, then the field form). Row 20: **`NONE` on 52 of 56 roster scored rows** — disposition **signed vacuity disclosure**.

---
### EFF.GRTJB.36  [changes-record]  (grade surface — the blueprint correction)

**CANONICAL STATEMENT:** verbatim, lines 510–514.
**FORM:** bold-headed bullet.

> “* **ONE BLUEPRINT DISPLAY IS CORRECTED (JB-BOX-1):** J-B(iii)'s "shifts the
>   classifier's residual read by τ_m with the level-m EPS-carry z_m^{ε′}" — in
>   the print's own twisted coordinates the carry CANCELS (the shift constant is
>   c_m = ψ_{m,0}, = −z_{m+1} one level up); the carry-bearing form is the
>   HARNESS-frame statement ([RMG] (C-READ) itself).”

**TYPE JUSTIFICATION (rule 13):** this is a defect report against ANOTHER document (the GRT weld blueprint), and it is REVIEW-OWED at the source rather than repaired here — so it is a `supplier-finding` in substance; it is filed `[changes-record]` here only because the note itself boxes it as its own blueprint correction (JB-BOX-1), i.e. the note owns the display it corrects. **Flagged for the merge run.**

**CONDITIONALITY:** Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence (matrix row 23).

**DERIVATION:** THEOREM JB-CREAD's five-line chain (L2236–2242, shard 2), in which `z_m^{−ε′}·z_m^{ε′}` cancels by LEMMA JB-EPS.

**RESOLUTION TRACE:** statement lines 510–514; proof lines 2236–2242 (shard 2); the box itself 2314–2321 (shard 2); the germ remark 2303–2308 (shard 2).

XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:(C-READ)` — count **8**.

**TEETH:** **IND, teeth MJB-CREAD** — “the carry-bearing reading must FAIL, and does, on all 22 designated samples over 14 towers”. A planted mutant that fired; the strongest single tooth in the note.

---
### EFF.GRTJB.37  [fence]  (grade surface — Standing)

**CANONICAL STATEMENT:** verbatim, lines 515–517.
**FORM:** bold-headed bullet.

> “* **Standing.** Nothing here fires any gate, touches any accepted text, makes
>   any gr/carrier (J-C) claim, or advances any density (J-D) statement.
>   Acceptance counter 0/2.”

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION** on the counter (see `.02`/`.10`). The four negative fences remain live and are the note's NON-IMPORTS of record (see §4).

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement lines 515–517; the standing box 2439–2454 (shard 2); status superseded 3107–3119 (shard 3).

**TEETH:** NONE (negative fence).

---
### EFF.GRTJB.38  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the superseded-cap banner (lines 519–523) plus its terminator (line 563), quoted verbatim; the 38-line quoted block between them is the r0/r1/r2 cap, retained in the source and NOT re-quoted here because it is entirely superseded and its live content is `.31`–`.37`.]

> “**[r3 — SUPERSEDED r0/r1/r2 GRADE CAP, retained verbatim for the record. NOT
> authoritative; where it differs from the cap above, the cap above (and §0M's
> matrix) governs. Its three known defects: JB-TREE carries no perimeter (PE3
> F-1B), JB-VTX's clause-(d) proviso is absent (PE3 F-1), and the (RES) layer is
> fenced with `P<q` instead of `P≤q` (PE3 F-4).]**”

> “**[r3 — end of the superseded grade cap.]**”

**SUPERSESSION KIND:** `replacement` — this unit IS the superseded object, retained.

**CONDITIONALITY:** **NOT AUTHORITATIVE.** The banner names its own three defects, which is what makes the retention safe. A chapter cut must read `.31`–`.37`, never this block.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 519–563 (banner 519–523; retained block 525–561; terminator 563); the superseding surface 443–517.

**TEETH:** NONE (retained record). **This is the pattern r4/F-6 later had to enforce elsewhere** (§7.3's superseded region had no terminator; see `.63`).

---
### EFF.GRTJB.39  [fence]  ★ THE CITE-SCOPE UNIT ★

**CANONICAL STATEMENT:** verbatim, lines 565–576 — the classifier-side literature discipline and the print anchors.
**FORM:** bold-headed paragraph.

> “**Literature and consumption discipline.** Classifier side = the GMN print
> `docs/references/HigherNewton.tex`, consumed as literature through the
> SEALED probe transcription `grt_weld_probe.GmnLeg` (no new print
> transcription in this unit; the runner's fresh legs are its own division/
> hull/integer recomputations). Print anchors used here beyond J-A's list:
> the order-r polygon definition N_r(f) from the φ_r-adic development with
> ordinates u_i := v_r(a_i φ_r^i) = v_r(a_i) + i·v_r(φ_r) (tex ~1370–1376,
> "We define the Newton polygon N_r(f) … Note that we consider the v_r-value
> of the whole monomial"); the principal part N_r^−(f) = negative-slope sides
> (tex 1377); Lemma `shape` items 1–2 (min_i u_i = v_r(f), ℓ(N_r^−) = ω_r;
> tex ~1395–1414); Definition `t(i)` (tex 1431), `rescoeff` (tex 1447),
> `defresidual` (tex 1497); Proposition `propertiesv` item 3 (tex 1028).”

**LABEL VERIFICATION (rule 2 applied to a LaTeX source).** `grep -cF` in `docs/references/HigherNewton.tex`: `propertiesv` **8**, `shape` **13**, `rescoeff` **2**, `defresidual` **1**, `phiradic` **2**. All ≥ 1. **NEAR-MISS disposition for `t(i)`:** the bare string `t(i)` is not a distinguishable fixed-string designation in a LaTeX file (it collides with ordinary text); the referent is verified by the note's own line pin (tex 1431) and by `CITE_SCOPE_RESOLUTION` NS-11, which identifies the same object. Carried descriptively.

**READING NOTE (external, not an edit) — the Q7 CITE-SCOPE row and its retarget.** `runs/qgen/Q7_output.log` classifies exactly this sentence as GRTJB's **H6 hazard**: *“These are load-bearing in JB-VTX(a), (c), and (d1). The pasted note gives locations and conclusions but not the publication's hypotheses on the base field. Generality to F_q((t)) therefore cannot be certified from this slice.”* `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-11** resolves it, and this compiler records the resolution WITHOUT applying it:

- **The GMN source's published scope is ℚ_p-only, confirmed at the local print.** NS-11's source register row for `[GMN12]` quotes `docs/references/HigherNewton.tex` line 401 verbatim: *“We fix a finite extension $K$ of $\Q_p$ as a base field …”* — **ℚ_p-only. Confirmed.**
- **Local label identification (NS-11):** `\label{shape}` = `HigherNewton.tex` line 1401 = GMN **Lemma 2.17**; `\label{propertiesv}` = line 1028 = GMN **Proposition 2.7**; `\label{phir}` = line 1257 = GMN **Theorem 2.11**. This compiler grep-verified `\label{phir}` count **1** at HEAD.
- **Retargets, verdict COVERS-ALL-O:** `shape` items 1–2 → **[GN15] Lemma 1.5 + Corollary 1.14**, equivalently **[FGMN] Lemma 2.2 + Prop 5.14 / Cor 5.15** and **[AGNPRW] Lemma 4.2**. `propertiesv` item 3 → **[GN15] §1.2**, where the formula *“µ′(g) = Min_{0≤s}{µ(a_sφ^s) + sν}”* is the **definition** of the augmented valuation — “strictly stronger than citing it as a proposition”. `rescoeff` / `t(i)` → **[AGNPRW] §2.2 definition (3)** + **[GN15] Theorem 1.9**.
- **The retarget's price, quoted:** NS-11's own caveat — *“the general-scope sources use MacLane/graded-algebra normalizations (`µ` valued in `Γ_Q`, `R` monic-normalized) rather than GMN's integer-rescaled `v_r = e_{r−1}H_{r−1}∘S_{r−1}`; the re-cite therefore carries a **normalization-shear obligation** — exactly the one `GENTOW2_PROOF_2026-08-09.md` already discharges for the FGMN side … Reuse that.”*

**The note's own text is compiled as written; the retarget is RECORDED, NOT APPLIED.** (Same treatment as `spec/EFF-W12-s1of2.md` and `spec/EFF-GENTOW5-s1of2.md` gave their Ore/FGMN rows.)

**CONDITIONALITY:** The print is consumed “as literature through the SEALED probe transcription” — i.e. GRTJB adds **no new print transcription**, which is itself a NON-IMPORT (see §4). The anchors are load-bearing at JB-VTX(a) (`propertiesv` item 3), JB-VTX(c) (the principal part), JB-VTX(d1) (Lemma `shape` item 1), and §1's print frame (the N_r ordinate definition).

**DERIVATION:** Declaration of consumption.

**RESOLUTION TRACE:** statement lines 565–576; consumption sites 1375–1396 (§1's two frames), 1636–1694 (§3(a)–(e)) — both shard 2; the one anchor recorded as NOT TAKEN at 1880–1889 (shard 2, the valuation-multiplicativity route, tex ~1012).

**TEETH:** The print side is exercised through `GmnLeg` in every IND family; but **no tooth can test a citation's published scope** — that is precisely why Q7 classifies it CITE-SCOPE. Disposition: **AUDIT — decorrelated-model audit** (rule 27): a finding no battery could produce.

---
### EFF.GRTJB.40  [fence]

**CANONICAL STATEMENT:** verbatim, lines 577–593 — the consumed-notes list with its `[r3, F-7]` addition.
**FORM:** bold-headed paragraph (a continuation of `.39`'s block).

> “Consumed notes: **[RMG]** = `RMENGINE_2026-08-08.md` ACCEPTED (**[r3, F-7 —
> S0.1 ADDED to this list: the abbreviation P_l := e_l·g_l, which §4(ii) and
> §7.4's PW-ID/PW-WALK rows use, is scoped "local to this note" in [RMG] S0.1
> and was consumed here without being cited or defined]** S0.1 the period
> abbreviation P_l := e_l·g_l; S0.2 the
> (RM-m) box verbatim incl. (C-READ)/(C-EPS); S2.1 cells/lines/L-CELL/L-NORM;
> S2.2 (ID-(i+1)) + the E1-priority tree + L-EXACT + L-CANON; S3.2 L-LINE;
> S4 T-TERM on T-scope(m)); **[ILN]†** S0.1/S0.2 (accepted; class pin,
> canonical lifts, REALIZE/WELL-DEF incl. the g_m = 1 form
> Φ_{m+1} = Φ_m^{e_m} + Ĉ_m); **W-2** = `GRTW2_PROOF_2026-08-08.md` at
> ATTEMPT grade (clause 1 admissibility W2-C1/C1a; clause 2 byte law §3.4(3)
> + (C-coll) split; clause 3 transport W2-C3; W2-L0/L2/L3); **J-A** =
> `GRTJA_PROOF_2026-08-08.md` at ATTEMPT grade, arc 0/1 clean (JA-PIN,
> JA-VAL, JA-EPS, JA-GRID, JA-RES/(VD-m)/JA-VDIND with JA-BOX-1..5);
> **LED-Λ** = `LEDGERLAMBDA_2026-08-08.md` at ATTEMPT grade (the S1 quantum
> table's λ_E column, LED-Λ(A1)/(B), L-MONO's edge signs). Every consumption
> is at the source's own grade; nothing is upgraded here.”

**SUPERSESSION KIND:** `inventory completion` — an input consumed without citation, added.

**CONDITIONALITY:** **STALE on two supplier grades.** “W-2 … at ATTEMPT grade” and “J-A … at ATTEMPT grade, arc 0/1 clean” are superseded by the 2026-08-08 annex (L3148–3161, shard 3): “Both arc-graded suppliers have since been ACCEPTED at 2/2: **GRTW2 at adc6cf3** (2026-08-07 …) and **GRTJA at 17d2a32** (2026-08-07; body byte-frozen, md5 cba309ce @ f131c53).” Direction: **FAVORABLE** (the annex's own word); no identity, fence or census moves. **LED-Λ's ATTEMPT grade is NOT superseded and still rides** (matrix rows 17, 26). **E-2 additionally re-reads the W2-C3 clause at the supplier's proved/measured split.**

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement lines 577–593; the F-7 disposition 911–912; supplier-grade update 3148–3161 (shard 3); the E-2 propagation rule 3135–3142 (shard 3).

**XREF LEDGER (all fixed-string, counts at HEAD):**
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:S0.1` — **12** · `S0.2` — **13** · `S2.1` — **15** · `S2.2` — **16** · `S3.2` — **3** · `L-CELL` — **11** · `L-NORM` — **28** · `L-EXACT` — **11** · `L-CANON` — **6** · `L-LINE` — **23** · `T-TERM` — **11** · `T-scope` — **42** · `(RM-m)` — **11** · `(C-READ)` — **8** · `(C-EPS)` — **7** · `(C-W_R)` — **7** · `(C-W_Q)` — **9** · `(ID-(i+1))` — **3**.
XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13** · `S0.2` — **5** · `REALIZE` — **17** · `WELL-DEF` — **32**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C1` — **22** · `W2-C1a` — **10** · `W2-C3` — **22** · `W2-L0` — **5** · `W2-L2` — **8** · `W2-L3` — **5** · `(C-coll)` — **27** · `W2-OPEN-1` — **10**.
XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-PIN` — **15** · `JA-VAL` — **7** · `JA-EPS` — **13** · `JA-GRID` — **11** · `JA-RES` — **20** · `(VD-m)` — **10** · `JA-VDIND` — **21** · `JA-BOX-1` — **8** · `JA-BOX-2` — **7** · `JA-BOX-3` — **3** · `JA-BOX-4` — **4** · `JA-BOX-5` — **1**.
XREF: `lean/notes/openmath/LEDGERLAMBDA_2026-08-08.md:LED-Λ(A1)` — **5** · `L-MONO` — **7** · `λ_E` — **10** · `S1` — **15** (§-anchor; count is an upper bound — the fixed string also matches `S10`/`S11` prefixes. Referent independently pinned by `λ_E`, count 10, which lives in that table).

**NEAR-MISS (rule 15) — `(B-READ)`.** The note cites `(B-READ)` at §5's proof (L2226–2231, shard 2). Fixed-string `(B-READ)` has count **0** in `RMENGINE_2026-08-08.md`. **The note itself resolves it in place:** “(B-READ) is [RMG] S2.1's **LEMMA L-CELL clause (ii)** — a nonvanishing level-m read at a weight forces an on-line on-grid cell at that weight”. Verified referent: `L-CELL`, count **11**. Disposition: **NEAR-MISS — designation absent as written; verified referent `L-CELL` in `RMENGINE_2026-08-08.md`, count 11; the tag is GRTJB-local shorthand and the note declares it so.** Not an OPEN-CALL.

**TEETH:** NONE (import declaration).

---
### EFF.GRTJB.41  [instrument-record]

**CANONICAL STATEMENT:** verbatim, lines 595–599.
**FORM:** bold-headed paragraph.

> “**Machine bracket:** `grt_jb_checks.py` — both sides of every §2–§5
> equality on the weld-probe roster (16 towers) + the 5 concrete QO shapes +
> the 4 fresh d₀ ≥ 2 shapes (engine_ext standing rule honored in-unit),
> LAW-KEYED with teeth; transported-chamber re-instantiation on every tower
> with a nontrivial W-2 transport ledger. Verdict in §7 (commit 2).”

**CONDITIONALITY:** “both sides of every §2–§5 equality” is the advertised scope; the matrix's column (f) is the audited one, and it records **three `NONE` legs inside §2–§5** (rows 5, 12, 22) plus one SAME sub-leg (row 1). **The advertised scope is therefore wider than the audited one, and §0M is the correction.**

**PIN VERIFICATION:** `verification/openmath/grt_jb_checks.py` EXISTS; md5 `55f4911eaddd8524fd91368b30ed71bd` **EXACT at HEAD**; `grt_jb_checks_output.txt` and `grt_jb_checks_results.json` EXIST.

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement lines 595–599; verdict 2458–2573 (§7.1, shard 3); the seal-record erratum 2462–2472 (shard 3).

**TEETH:** This unit IS the instrument; its verdict is 18 families GREEN / 6,700 samples / 0 violations (§7.1, shard 3).

---
### EFF.GRTJB.42  [instrument-record]

**CANONICAL STATEMENT:** verbatim, lines 601–619.
**FORM:** bold-headed paragraph with an `[r2]` extension.

> “**[r1] POST-SEAL SUPPLEMENTARY MACHINE LEGS — NOT part of the sealed
> battery.** Two instruments were written AFTER the JB-PE1 verdict and are
> evidence for a REPAIR, not sealed predictions:
> `verification/openmath/grt_jb_printwalk.py` (+ its committed
> `grt_jb_printwalk_output.txt` / `_results.json`) — the independent PRINT-KEY
> tree walker finding G-1 asks for, carrying its own mini two-commit seal
> (prereg comment block committed BEFORE any full run); and
> `verification/openmath/grt_jb_r1_levelcensus.py` (+ its committed output) —
> the LEVEL-KEYED recomputation of the JB-CREAD boundary census that F1 turns
> on. The sealed runner `grt_jb_checks.py` is BYTE-UNTOUCHED by this round
> (md5 `55f4911eaddd8524fd91368b30ed71bd`, unchanged from seal 7f6759d), and so
> is `grt_jb_checks_results.json`. **[r2] A THIRD post-seal instrument is added in r2: `verification/openmath/grt_jb_printwalk2.py` (+ its
> committed output) — the GATE REPAIR for the r1 walker's cross-frame family
> (PE2's G2-2), carrying its own mini two-commit seal. BOTH earlier instruments
> are byte-untouched by r2 as well: `grt_jb_printwalk.py` md5
> `f53e23e8d1c79f084a1e34eee857e37c` and `grt_jb_r1_levelcensus.py` md5
> `2bcb44fdbf839d367f0e11033a5d3fd7`, unchanged from r1 (PE2 verified both at
> HEAD and re-ran all three legs bit-identically). Verdict in §7.4(C).**”

**TYPE JUSTIFICATION (rule 19):** `instrument-record` — this describes the testing apparatus and its epistemic status, not a prediction and not a result. The corresponding `preregistration` and `run-record` units are §7.4's mini-seal records and verdicts (shard 3).

**CONDITIONALITY:** **The status fence is the unit's whole content: “evidence for a REPAIR, not sealed predictions”.** Consequently none of the three post-seal legs may be read as a preregistered confirmation, and the note keeps them in a separate section (§7.4) for exactly that reason.

**PIN VERIFICATION (rule 23), all four artifacts + all three md5s re-computed at HEAD by this compiler:** `grt_jb_printwalk.py` **EXACT**, `grt_jb_r1_levelcensus.py` **EXACT**, `grt_jb_printwalk2.py` **EXACT** (md5 `6c6318f7fc6570a2d454389b38441329`, cited at L2899–2900), `grt_jb_checks.py` **EXACT**. Output/JSON artifacts: `grt_jb_printwalk_output.txt`, `grt_jb_printwalk_results.json`, `grt_jb_printwalk2_output.txt`, `grt_jb_printwalk2_results.json`, `grt_jb_r1_levelcensus_output.txt` — **5/5 EXIST**. Commits `7f6759d`, `4c97649`, `67bf0c4` — **all resolve.**

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement lines 601–619; the legs' verdicts 2738–2948 (§7.4, shard 3); the r2 gate repair's own disclosure 2848–2879 (shard 3).

**TEETH:** Leg A (84 walks) is the decorrelated print-key evidence; leg B's 27-of-72 vacuity is the DISCLOSED defect; leg (C) is the gate repair with its own limitation stated (“a GATE REPAIR, not a decorrelated second instrument”). Disposition: **accepted-with-decorrelation-supplied** for JB-TREE(i) on base rows; **disclosed non-repair** for the 8 chamber walks.

---
### EFF.GRTJB.43  [run-record]  (REPAIR ROUND r1 — header)

**CANONICAL STATEMENT:** verbatim, lines 621–636.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against JB-PE1 (hostile pass, fresh context, read-only, fixes nothing;
> report `GRTJB_passPE1_report.md`, commit 85a8dc9: **1 CRITICAL + 9
> JUSTIFICATION GAPS, VERDICT NOT CLEAN**; ledger entry
> `BRIDGE_ADJUDICATIONS_2026-07-30.md`, "LIFT r1 REPAIRED-WITH-PROOF … + JB-PE1
> fresh verdict"). PE1's machine leg reproduced BIT-IDENTICALLY (exit 0, 18/18
> families GREEN, 6,700 samples, 0 violations, every census verbatim; the
> regenerated JSON differs from the sealed artifact in the `elapsed_s` field
> alone) and all four charged re-derivations SURVIVED — LEMMA JB-EPS line by
> line, THEOREM JB-CREAD's five-line chain including the VERBATIM ε′ match
> against [RMG] (C-READ), the JB-VTX shear as DERIVED (not asserted, slope law
> included), LEMMA JB-AFF. **No §2–§5 identity moved in this round.** What
> moved is the note's GRADE SURFACE (F1) and its machine-evidence wording
> (G-1..G-9).”

**CONDITIONALITY:** The reproduction claim is exact and is the round's warrant. **Note that “the JB-VTX shear as DERIVED … slope law included” was later narrowed by CERTIFIER ANNEX E-3** (the slope law survives; the ambient-lattice extension does not) — the re-derivation was sound on what it checked.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 621–636; closing 702–707; the E-3 narrowing 3199–3245 (shard 3).

**PIN VERIFICATION:** `85a8dc9` → commit; `GRTJB_passPE1_report.md` EXISTS; `lean/notes/openmath/BRIDGE_ADJUDICATIONS_2026-07-30.md` — path pin (ledger).

**TEETH:** The bit-identical reproduction IS the tooth (an independent re-execution of the sealed battery). Disposition: **executable regression, replayed by a hostile reader**.

---
### EFF.GRTJB.44  [supplier-finding]  (r1 F1 — the CRITICAL)

**CANONICAL STATEMENT:** verbatim, lines 638–659.
**FORM:** bold-headed bullet.

> “* **F1 (CRITICAL — grade surface; 4 sites + 1 census sentence).** The r0 text
>   claimed (VD-m) "unconditional for m ≤ 2 (m = 2 by JA-RES)". That CONFLATES
>   J-A's PER-SLOT law JA-RES (c_i = z_{m−1}^{−i·A_{m−1}}·C_i, genuinely
>   unconditional at m = 2) with the EVALUATED dictionary (VD-m), which J-A
>   supplies only through COROLLARY JA-VDIND's ABSOLUTE character-triviality
>   hypothesis (z_{m−1}^{i·A_{m−1}} = 1 at every attained abscissa). RE-FENCED
>   at all four sites (§5 theorem parenthetical, the grade cap below, §7.2's
>   JB-CREAD row, JB-BOX-2) to: **(VD-m) unconditional at m ≤ 1 only
>   ((VD-1) = W2-L3); at every m ≥ 2 conditional — JA-VDIND's collapse
>   condition, ⊇ (R-coll)/per-digit at m ≥ 3 (JA-BOX-2)**; and §7.1's census
>   sentence is re-attributed from "the JA-BOX-2/(VD-m)-proviso geography (the
>   m ≥ 3 box)" to the true level split. **JB-CREAD has NO unconditional
>   stratum above m = 1.** The refutation is the note's OWN sealed runner, and
>   r1 re-verified it independently of PE1 (`grt_jb_r1_levelcensus.py`,
>   replicating `jb_cread`'s control flow level-by-level over the 16-tower
>   roster): the 13 roster boundary rows are **m = 1: 0 · m = 2: 10 (T3A 3,
>   T3B 3, T3C 1, T3D 3) · m = 3: 3 (I4B)**, ZERO of them an evaluator
>   scope-out (all 13 are machine-evaluated FALSE instances of (VD-m)), against
>   56 roster scored rows (m = 1: 45, m = 2: 8, m = 3: 3); the committed sealed
>   JSON pins the same totals from the other side (roster boundary 13 +
>   chamber 8 = 21 = the `JB-CREAD-BOUNDARY` census field). So ten of the
>   thirteen sit INSIDE the stratum the r0 text called unconditional.”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding` — a defect report about how a SUPPLIER's two distinct theorems (JA-RES the per-slot law vs (VD-m) the evaluated dictionary) were conflated when consumed; discharged by re-fencing at the consumption sites.

**SUPERSESSION KIND:** `replacement` — a false perimeter is replaced by the honest one.

**CONDITIONALITY:** This is the note's largest single narrowing and it MOVES A MATHEMATICAL PERIMETER, not wording: JB-CREAD loses its advertised unconditional m = 2 stratum. **E-1 later re-reads its “(R-coll)” label** at the root-inclusive form.

**DERIVATION:** The distinction is J-A's own: JA-RES is a per-slot law on residual coefficients; (VD-m) is an identity between assembled read values, and the implication runs only through JA-VDIND's hypothesis. The refutation is the runner's own level-keyed census, re-derived independently by r1's post-seal instrument.

**ARITHMETIC AUDIT:** re-verified at `.34`; all six cross-checks consistent.

**RESOLUTION TRACE:** statement lines 638–659; the fence's body form 1471–1495 (§2(iii), shard 2) and 2186–2203 (§5's theorem, shard 2); the census 2494–2546 (§7.1, shard 3) and 2748–2764 (§7.4(A), shard 3); correction site 3125–3133 (E-1, the label only).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VDIND` — **21** · `JA-RES` — **20** · `(R-coll)` — **7** · `JA-BOX-2` — **7**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-L3` — **5**.

**TEETH:** **executable regression that disconfirmed the author** — the note's own sealed runner is the refutation, and a decorrelated recount (PE2, from the committed JSON alone, without calling `vd_eval`) reproduced the split. Disposition: **accepted-with-decorrelation-supplied**.

---
### EFF.GRTJB.45  [changes-record]  (r1 G-5 — the proviso named)

**CANONICAL STATEMENT:** verbatim, lines 680–684.
**FORM:** bold-headed bullet with a nested `[r2]` retraction.

> “* **G-5** JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso — consumed at §2(iii)(GRID),
>   carried by no box in r0 — is now named in JB-BOX-2 ~~with its discharge
>   argument~~ **[r2, G2-5 — the "discharge argument" is RETRACTED: it was an
>   assertion, not a derivation. The proviso is CARRIED, DISCHARGE OWED; see the
>   r2 block and JB-BOX-2]**.”

**CHAIN:** member 1 of the four-layer `u ≥ 0` chain (see `.14` for the full chain and its TERMINAL).

**SUPERSESSION KIND:** `inventory completion` (r1: an uncarried inherited proviso added to a box) — then `replacement` (r2's retraction).

**CONDITIONALITY:** See `.14`.

**DERIVATION:** Inventory. The proviso is “an inline J-A repair, not one of JA-BOX-1..5, so JB-BOX-2's blanket 'rides J-A's boxes verbatim' did not carry it in r0” (L1499–1500, shard 2) — a structural reason the omission happened, which is why the fix is an inventory completion rather than a wording fix.

**RESOLUTION TRACE:** statement lines 680–684; the retraction 804–819; the body sites 1497–1537 (§2(iii), shard 2) and 2340–2373 (JB-BOX-2, shard 2).

**TEETH:** `NONE` on both consumers' grid halves (matrix rows 4, 12).

---
### EFF.GRTJB.46  [changes-record]  (r1 G-9 — the perimeter restatement)

**CANONICAL STATEMENT:** verbatim, lines 697–700.
**FORM:** bold-headed bullet.

> “* **G-9** JB-VTX's and JB-DEV(iii)'s quantifiers are restated to the
>   runner's own shared-key perimeter `qcap_of(T,G) = min(T.n,
>   shared_upto(T,G)+1)`, which is what clause (a)'s JA-VAL consumption
>   actually needs.”

**SUPERSESSION KIND:** `scope-pin` — a blanket quantifier narrowed to the perimeter the consumed theorem requires.

**CONDITIONALITY:** **This is the FIRST instance of the recurring disease** the matrix was later built to end: r1 fixed the body and left five surfaces behind (r2/G2-1), r2 fixed eight surfaces and left four more (PE3/F-1, F-1B), and only §0M's regeneration closed it. See `.11`.

**DERIVATION:** The quantifier the machine evidence always used: “r0 inherited the theorem's blanket 'level q ≥ 0' here; the machine evidence always quantified the narrower statement” (L1437–1439, shard 2).

**RESOLUTION TRACE:** statement lines 697–700; the body sites 1430–1439 (§2(iii)) and 1623–1631 (§3's theorem head) — both shard 2; the surface sweep 727–763 (r2 G2-1); the final regeneration 443–517 and 2577–2593 (shard 3).

**TEETH:** the runner's own loop bound is the fence: `for q in range(0, qcap_of(T,G) + 1)`; off-perimeter counter **0** on the roster.

---
### EFF.GRTJB.47  [changes-record]  (r1 — the remaining seven dispositions, assembled)

**CANONICAL STATEMENT:** [ASSEMBLED — the r1 bullets G-1, G-2, G-3, G-4, G-6, G-7, G-8, quoted verbatim in source order; G-5 and G-9 are `.45` and `.46`, F1 is `.44`.]

**MERGE CRITERION, stated (rule: the boundary self-audit must justify every merge).** These seven are wording/record/evidence-labelling dispositions with no mathematical movement, each fully resolved inside its own bullet, none cited by designation from any other unit, and none carrying a supersession history of its own. They are emitted as ONE unit with a per-item ledger. **The three dispositions of r1 that DO move something (F1 = a perimeter; G-5 = a carried proviso; G-9 = a quantifier) are separate units.**

`[TABLE — compiler ledger]` r1's remaining dispositions, one row each, with the source's own wording condensed and the load-bearing figures preserved.

| bullet | lines | what it corrects | the corrected content |
|---|---|---|---|
| **G-1** | 660–672 | tree evidence over-advertised (“harness AND print keys”) | the sealed print-key leg fires only under `byteeq`, i.e. re-executes ONE pure `fresh_divmod` on EQUAL arguments; corrected at three sites AND the missing evidence supplied post-seal by `grt_jb_printwalk.py`. **`[r2, G2-2]` rider:** true of LEG A (84 walks); its LEG B is 45 cross-frame + 27 re-executions — “the same disease, disclosed … and repaired by leg (C)” |
| **G-2** | 673–675 | a census figure | “22 scored samples … across 7 towers” → 22 samples across **14 towers / 21 teeth-positive JSON rows**; “7” was the runner docstring's smoke-probe designation list. **The claim's substance is UNDERSTATED, not overstated** |
| **G-3** | 676–677 | a vacuity | “q = 1 byte-equal on all 25 rows” → **22 rows**, the other 3 VACUOUS (T.n = 0 ⇒ empty census ⇒ TH-BASE unexercised) |
| **G-4** | 678–679 | a false subject | JB-VTX clause (e) restated with its true subject Φ_{q+1}^har (“as literally read with the theorem's quantified f its first half is FALSE”) |
| **G-6** | 685–687 | a coverage over-claim | “reproduces the probe's F1 pattern row-for-row” → exact agreement on the **12 junctions both instruments walk**; the 16 roster top junctions (carrying 12 of the probe's 18 F1 REDs) are outside JB-KEYEQ's q ≤ n range |
| **G-7** | 688–690 | notation | `m_{q+1}^GMN` defined in-note at first use; `(B-READ)` resolved to its [RMG] source; the `s_m(·)` overload declared and split into `s_m^wt(·)` / `s_m^ini(·)` |
| **G-8** | 691–696 | a seal-record erratum | the T-F figures 41,720 / 7,472 re-attributed to the O1thr rev-3 runner (cited BY GD-2/GD-3, not GD-2's own instrument); and seal commit `7f6759d`'s message says “note + runner” while that commit contains the runner only — “the message is immutable; the seal property itself HOLDS” |

**CONDITIONALITY:** Item G-1's substance is re-opened twice more (r2/G2-2's disclosure; r2/G2-3's coverage correction) and only closed by leg (C). Item G-7's `(B-READ)` resolution is the NEAR-MISS recorded at `.40`. Item G-4's subject correction is matrix row 13 and is why row 13 is a no-leg DISCLOSURE rather than a frontier member.

**DERIVATION:** Per item, inside the bullet.

**RESOLUTION TRACE:** statement lines 660–696 (with 680–684 and 697–700 excised to `.45`/`.46`); G-1's later riders 764–783 and 784–790; G-8's erratum re-stated at 2462–2472 (shard 3).

**PIN VERIFICATION:** `7f6759d` → commit; `5a72b62` → commit; `f5578d0` → commit. The G-8 claim “that commit contains ONLY `verification/openmath/grt_jb_checks.py` (990 insertions)” is a git-history claim about a resolvable commit; **not independently re-verified by this compiler** — recorded as a checkable pin, not as an audited fact.

**TEETH:** G-1 → the post-seal walker (IND, 84 walks); G-2/G-3/G-6 → censuses (measurement); G-4 → matrix row 13 (`NONE`, none claimed); G-7/G-8 → record. Disposition: mixed; **G-3 is a signed vacuity disclosure** (3 of 25 rows carry no information).

---
### EFF.GRTJB.48  [run-record]  (REPAIR ROUND r2 — header)

**CANONICAL STATEMENT:** verbatim, lines 709–725.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r2 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
> against **JB-PE2** (hostile pass, fresh context, read-only, fixes nothing;
> report `GRTJB_passPE2_report.md`, committed by that pass: **0 CRITICAL + 7
> JUSTIFICATION GAPS, VERDICT NOT CLEAN, PE1's F1 CONFIRMED CURED**; ledger
> entry `BRIDGE_ADJUDICATIONS_2026-07-30.md`, "LIFT r2 LANDED … + JB PE2").
> PE2 re-ran ALL THREE machine legs (sealed runner, level census, print walker)
> and reproduced every one **BIT-IDENTICALLY** — the sealed
> `grt_jb_checks_results.json` regenerated with a zero diff including
> `elapsed_s`, all three md5 seals intact at HEAD — and it re-derived the F1
> level split **13 = 0/10/3, 56 = 45/8/3 from the committed sealed JSON alone**,
> without calling `vd_eval`: F1's factual core now has a decorrelated leg.
> **No §2–§5 identity moves in this round either.** What moves is again the
> GRADE SURFACE (G2-1), one machine-evidence disclosure (G2-2/G2-3), one
> retraction (G2-5), one definition (G2-6), one refuted explanation (G2-4) and
> two record figures (G2-7).”

**CONDITIONALITY:** **The decorrelation claim is the round's most valuable line**: F1's census was re-derived from the committed JSON alone, without re-running the evaluator — so the factual core does not rest on one code path.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 709–725; closing 846–850.

**TEETH:** **accepted-with-decorrelation-supplied** — an independent recount of the same numbers from a different artifact.

---
### EFF.GRTJB.49  [supplier-finding]  (r2 G2-1 — the grade-surface sweep, and its own honesty defect)

**CANONICAL STATEMENT:** verbatim, lines 727–763.
**FORM:** bold-headed bullet + an ASCII enumeration + a nested `[r3, F-1B]` correction.

> “* **G2-1 (grade surface — the recurring disease).** r1's `qcap` re-fence (G-9)
>   reached five BODY surfaces and neither of the two SURFACES A DOWNSTREAM UNIT
>   ACTUALLY READS. Carried in r2 to: §7.2's **JB-VTX row** (was "at the W2-C1
>   representative" with no perimeter) and **JB-DEV row** (was bare), §7.3's
>   **"W-3 in full"** and **"W-5 in full"** (both scoped: full in CONTENT, not
>   full in q), and — found by the mandated re-grep of every grade line in the
>   note — three more. **RE-GREP RESULT: 8 grade-surface hits inconsistent with
>   the r1/r2 body fences, all 8 fixed**:
>
>     1. §2 ∎ Grade line   — graded JB-DEV without separating clause (iii)
>     2. §7.2 JB-DEV row   — bare "consumptions at their own grades"
>     3. §7.2 JB-VTX row   — "at the W2-C1 representative", no qcap
>     4. §7.3 "W-3 in full"— pre-G-9 perimeter restored by omission
>     5. §7.3 "W-5 in full"— (VD-m) perimeter not carried into the display
>     6. §3 ∎ Grade line   — clause (d) consumes JA-GRID, so it rides the
>                            u ≥ 0 proviso; the line did not say so (r2, G2-5)
>     7. §4 ∎ Grade line   — clauses (iii)/(iv) consume JA-VAL, hence hold at
>                            levels m ≤ qcap; r1 fenced §2/§3 and left §4 bare
>     8. §7.2 JB-TREE row  — the same §4 fence at the claims-table surface
>
>   Hits 6–8 were NOT in PE2's list: they are the same disease found by the
>   mandated sweep, and all three corrections MOVE IN THE DIRECTION OF MORE
>   CONDITIONALITY (no statement is widened anywhere in r2). ~~The grade cap, the
>   §5 grade line and JB-BOX-2 were already consistent and are untouched except
>   for the G2-5 proviso.~~ **[r3, F-1B — THE STRUCK SENTENCE WAS FALSE WHEN
>   WRITTEN, and it is the round's honesty defect, not a mere omission. The grade
>   cap and JB-BOX-2 were consistent only BEFORE hit 7; hit 7 created the
>   inconsistency in this same round by fencing JB-TREE(iii)/(iv) at m ≤ qcap
>   while the grade cap graded JB-TREE with no perimeter and JB-BOX-2's
>   enumeration omitted JB-TREE entirely — and this sentence then certified the
>   absence of exactly that inconsistency. Correct record: r2's sweep found 8
>   hits and fixed 8 hits, but it did NOT close the surface set — it left the
>   u ≥ 0 proviso off §7.2's JB-VTX row and §7.3's polygon half (PE3 F-1) and its
>   own new fence off the grade cap and JB-BOX-2 (PE3 F-1B). "All 8 fixed" is a
>   count of hits found, not of surfaces made consistent. r3 replaces the sweep
>   genre altogether: §0M's matrix is the single record, and all 14 grade
>   surfaces are REGENERATED from it rather than patched.]**”

**Double-emission (rule 14) — the ASCII enumeration as a `[TABLE]`:**

| # | surface | the defect |
|---|---|---|
| 1 | §2 ∎ Grade line | graded JB-DEV without separating clause (iii) |
| 2 | §7.2 JB-DEV row | bare “consumptions at their own grades” |
| 3 | §7.2 JB-VTX row | “at the W2-C1 representative”, no qcap |
| 4 | §7.3 “W-3 in full” | pre-G-9 perimeter restored by omission |
| 5 | §7.3 “W-5 in full” | (VD-m) perimeter not carried into the display |
| 6 | §3 ∎ Grade line | clause (d) consumes JA-GRID ⇒ rides the u ≥ 0 proviso; the line did not say so |
| 7 | §4 ∎ Grade line | clauses (iii)/(iv) consume JA-VAL ⇒ hold at m ≤ qcap; r1 left §4 bare |
| 8 | §7.2 JB-TREE row | the same §4 fence at the claims-table surface |

**ARITHMETIC AUDIT (rule 22):** transcribed rows = **8** ✔ matches “8 grade-surface hits … all 8 fixed”. Split by section: §2 ×1, §3 ×1, §4 ×1, §7.2 ×3, §7.3 ×2 = **8** ✔. Hits NOT in PE2's list: 6, 7, 8 = **3** ✔ matches “Hits 6–8 were NOT in PE2's list”.

**SUPERSESSION KIND:** `counter re-reading` — a certification sentence (“already consistent”) shown false at its own commit by the round that wrote it.

**CONDITIONALITY:** **This is the note's own recorded honesty defect** and the direct cause of §0M. The r3 diagnosis quotes it as one of four instances of one disease (`.11`).

**DERIVATION:** A grep sweep plus the structural argument that hit 7 created the inconsistency the same sentence denied.

**RESOLUTION TRACE:** statement lines 727–763; the diagnosis 871–876; the replacement mechanism 877–892; the regenerated surfaces 443–517 (surface 1, this shard), 1562–1584 / 1714–1747 / 1923–1962 / 2262–2291 (surfaces 2–5, shard 2), 2577–2593 / 2610–2680 (surfaces 6–13, shard 3), 2379–2415 (surface 14, shard 2).

**TEETH:** **AUDIT — in-house hostile pass** (rule 27). No battery can catch a grade surface omitting a proviso; the finding class is exactly the one the note says “No machine leg can catch”.

---
### EFF.GRTJB.50  [instrument-record]  (r2 G2-2 — the repair instrument reproduced the disease)

**CANONICAL STATEMENT:** verbatim, lines 764–783.
**FORM:** bold-headed bullet.

> “* **G2-2 (MANDATORY DISCLOSURE — the repair instrument reproduced the disease
>   it was written to repair).** `grt_jb_printwalk.py`'s cross-frame family
>   PW-XFRAME is gated on `chain_eq` alone, and `chain_eq` already forces the
>   leg-B divisor to be byte-equal to the print key; on the sub-family that also
>   has `chat_eq` the leg-B call is byte-identical to leg A's PW-DIV call, so
>   **27 of the 72 PW-XFRAME walks (9 rows) are re-executions of PW-DIV** and
>   carry no cross-frame content. Disclosed in §7.4 with the 9 rows listed and
>   the mechanism displayed: **the cross-frame evidence rests on the 45
>   non-degenerate walks; the 27 are VACUOUS for cross-frame purposes.** The
>   print walker is under its own mini-seal and was NOT edited (md5
>   `f53e23e8d1c79f084a1e34eee857e37c`, unchanged). The corrected leg is a NEW
>   script, `verification/openmath/grt_jb_printwalk2.py`, with its own mini
>   two-commit seal (sealed UNRUN at r2 commit 1 `67bf0c4`): it re-gates on
>   `chain_eq` ∧ ¬`chat_eq`, certifies the degeneracy of the complement instead
>   of re-running it, and reconciles row-for-row against the r1 JSON. **RESULT
>   (§7.4(C)): ALL THREE FAMILIES GREEN, every sample count on its prediction —
>   PW2-XFRAME 45/45 agreed with a non-degeneracy certificate per sample,
>   PW2-DEGEN 27 certified vacuous, PW2-RECON 28 rows reconciled with NO
>   disagreement anywhere.** Its own disclosed limitation: it imports the frozen
>   r1 walker's machinery on purpose (gate repair, not decorrelation).”

**ARITHMETIC AUDIT (rule 22):** 45 + 27 = **72** ✔ matches “PW-XFRAME 72”. 9 rows × 3 walks = **27** ✔. Leg-A reconciliation: 45 + 27 + 12 = **84** ✔ matches “84 = r1's leg-A count” (§7.4, shard 3). **All three consistent.**

**CONDITIONALITY:** **Two nested honesty layers**: the repair instrument reproduced the SAME class defect it was built to fix, and the fix for THAT (leg C) discloses that it is “a GATE REPAIR, not a decorrelated second instrument” — it inherits the r1 walker's independence and adds none.

**PIN VERIFICATION:** md5 `f53e23e8d1c79f084a1e34eee857e37c` **EXACT at HEAD**; md5 `6c6318f7fc6570a2d454389b38441329` (leg C) **EXACT at HEAD**; commit `67bf0c4` resolves; all six output/JSON artifacts EXIST.

**DERIVATION:** The gate logic, displayed: `chain_eq` forces the divisor byte-equal; adding `chat_eq` forces the multiplicand byte-equal; both functions are pure and deterministic, so PW-XFRAME cannot fail there unless PW-DIV already did.

**RESOLUTION TRACE:** statement lines 764–783; the full disclosure with the 9 rows named 2848–2879 (shard 3); leg C's verdict 2897–2948 (shard 3); the purity softening 2938–2945 (r3 F-6(b), shard 3).

**TEETH:** **signed vacuity disclosure** (27 of 72 walks carry no information) + **accepted-with-decorrelation-supplied** (the 45 that do). Leg C's own tooth is the per-sample non-degeneracy certificate.

---
### EFF.GRTJB.51  [supplier-finding]  (r2 G2-4 — a mechanism claim refuted by the note's own roster)

**CANONICAL STATEMENT:** verbatim, lines 792–803.
**FORM:** bold-headed bullet.

> “* **G2-4 (mechanism claim refuted by the note's own roster).** Both r1
>   characterisations of the (VD-2) failure geography are STRICKEN, not replaced:
>   "the e₀ ≥ 2 character-visible towers" (T3E has e₀ = 2 and scores 6/6) and
>   "exactly where A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses" (T3D and T3E share
>   the level-0 read (e₀,h₀,g₀) = (2,1,2) and the same ψ₀, hence the same A_1 and
>   the same z₁ of order 3, and still split). **The mechanism of the m = 2 split
>   is NOT IDENTIFIED.** The roster is displayed as DATA in §7.1 with the one
>   surviving implication (e₀ = 1 ⇒ A_1 = 0 ⇒ (VD-2) holds, so e₀ ≥ 2 is
>   necessary and not sufficient) and an explicit ban on predicting from it. Also
>   fixed at the two other sites carrying the same gloss (§2(iii)'s F1 fence,
>   JB-BOX-2). NOTE for the record: this gloss entered the note from JB-PE1's own
>   §1.3 remark — a verifier's unforced explanatory claim; r2 treats no verifier
>   as a source.”

**SUPERSESSION KIND:** `counter re-reading` — an explanatory claim struck, **not replaced**; the note refuses to substitute a new mechanism.

**CONDITIONALITY:** **The surviving content is exactly one implication in one direction** (e₀ = 1 ⇒ (VD-2) holds), plus an explicit ban: “no consumer may use it to predict which towers are free at m = 2” (L2543–2544, shard 3). PE3 later confirmed the refutation “with a STRONGER witness (T3D/T3E share ψ₀, A_1 = 2 and ord(z₁) = 3 and still split)” (L862–864).

**DERIVATION:** A counter-instance from the note's own roster, displayed as a 6-row data table at §7.1 (shard 3). **The T3D/T3E pair is the decisive witness: same level-0 read, same ψ₀, same A_1, same ord(z₁) — and they split. So the failing set is not a function of (A_1, ord z₁) at all.**

**RESOLUTION TRACE:** statement lines 792–803; the data table 2522–2528 (shard 3); the stronger PE3 witness 862–864; the two other gloss sites 1481–1491 (§2(iii), shard 2) and 2330–2334 (JB-BOX-2, shard 2).

**TEETH:** **the note's own roster is the tooth** — a measurement that refuted an explanation. Disposition: **measurement, refuting**. Its meta-finding (“r2 treats no verifier as a source”) is an **AUDIT — in-house hostile pass** item.

---
### EFF.GRTJB.52  [changes-record]  (r2 G2-5 — the discharge RETRACTED)

**CANONICAL STATEMENT:** verbatim, lines 804–819.
**FORM:** bold-headed bullet with a nested `[r3, F-6(a)]` correction.

> “* **G2-5 (an asserted discharge, RETRACTED).** r1 claimed to discharge
>   JA-GRID(a)'s `[JA-r1]` proviso u := (V − s·h)/e ≥ 0 by "V is a level-m weight
>   of a nonzero polynomial in the window, so V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})".
>   No derivation was given and the implication is not plausible as stated (this
>   note's quantifiers admit units, whose level-m weight is 0, while the bound is
>   positive at r ≥ 2); the `s_geo` remark certifies the s-value, not the sign of
>   u. **The discharge is retracted at both sites (§2(iii), JB-BOX-2); the
>   proviso is CARRIED as an explicit inherited hypothesis of §2(iii)(GRID) and
>   everything consuming it, with the exact requirement for a real discharge
>   written out** (derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}), ~~equivalently~~
>   **[r3, F-6(a) — "equivalently" is WRONG here and the correction matters for
>   what a discharge must prove: J-A presents V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) as a
>   SUFFICIENT print-side bound ("the proviso holds at every consumption site BY
>   the print's own hypothesis"), while the genuine equivalence is
>   u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}. Read: **or directly**]**
>   V ≥ s_m^wt(V)·h_{m−1}, on the whole quantified window, units included).”

**CHAIN:** member 2 of the four-layer `u ≥ 0` chain (`.14`).

**SUPERSESSION KIND:** `replacement` (the retraction) + `wording-rider` (r3's “equivalently” → “or directly”, which the note itself says “matters for what a discharge must prove”).

**CONDITIONALITY:** **A retraction that MOVES the note's grade**: the (GRID) layer and JB-VTX(d4) become explicitly conditional. It is discharged only three rounds later, and then only on the sub-window `deg f < deg Φ_{q+1}` (`.67`).

**DERIVATION:** The refutation of r1's implication is displayed: the note's quantifiers admit units (level-m weight 0) while the claimed bound is positive at r ≥ 2. The `s_geo` red herring is named. **The genuine equivalence `u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}` is immediate from the definition `u := (V − s_m^wt(V)·h_{m−1})/e_{m−1}` with `e_{m−1} > 0`** — which is why conflating it with J-A's sufficient print bound changes what a discharge must prove.

**RESOLUTION TRACE:** statement lines 804–819; the body retraction 1505–1537 (§2(iii), shard 2); JB-BOX-2's retraction 2344–2373 (shard 2); the discharge three rounds later 1053–1073 and 2046–2062 (shard 2); the r3 F-6(a) disposition 908–911.

**TEETH:** `NONE` at both consumers' grid halves; the eventual discharge's corroboration is verifier-owned (`.67`).

---
### EFF.GRTJB.53  [definition]  (r2 G2-6 — the perimeter defined once)

**CANONICAL STATEMENT:** verbatim, lines 820–828.
**FORM:** bold-headed bullet.

> “* **G2-6 (the perimeter, stated ONE way).** §1's definition ("for all j ≤ q")
>   and the r1 restatements that cite it ("keys shared strictly below q") differ
>   by exactly the level q = qcap, which is the level the `+1` exists for. §1 now
>   defines TWO conditions under separate names — the **byte-equal chain THROUGH
>   q** (what JB-DEV(ii)'s byte clause means) and the **shared-key perimeter**
>   = the runner's own `qcap_of(T,G) = min(T.n, shared_upto(T,G)+1)` with
>   `range(0, qcap+1)`, i.e. keys shared strictly below q, level range
>   0 ≤ q ≤ qcap, nothing required at j = q. Every r1/r2 citation now names the
>   second one and reads identically.”

**SUPERSESSION KIND:** `replacement` — one conflated definition split into two named ones.

**CONDITIONALITY:** **Its closing sentence is FALSE and the note says so at r3.** “Every r1/r2 citation now names the second one” is corrected by `[r3, F-4]`: (RES) needs the FIRST, not the second (`.24`), and by `[r6, F-1]`: (d3) needs the first too (`.73`). **The definition itself is correct and is `.12`/`.13`; only its exhaustive-coverage claim was wrong.**

**DERIVATION:** Definition split; the two conditions are `.12` and `.13`.

**RESOLUTION TRACE:** statement lines 820–828; the definitions themselves 1309–1334 (§1, shard 2); the coverage claim's refutation 1336–1372 (§1's r3/r6 amendments, shard 2), 370–386 (⟨n4⟩), 1127–1163 (r6 F-1).

**TEETH:** `jb_keyeq`'s byte census keys the first; the runner's loop bound keys the second. Both IND.

---
### EFF.GRTJB.54  [changes-record]  (r2 — G2-3, G2-7 and the no-edit dispositions, assembled)

**CANONICAL STATEMENT:** [ASSEMBLED — the r2 bullets G2-3 (784–790) and G2-7 (829–834), plus the “PE2 findings NOT requiring an edit” paragraph (836–844), quoted verbatim in source order.]

**MERGE CRITERION:** three record/figure dispositions with no mathematical movement and no independent citation. **G2-1, G2-2, G2-4, G2-5, G2-6 are separate units** (`.49`–`.53`) because each moves a fence, an evidence class, a definition or a grade.

`[TABLE — compiler ledger]`

| item | lines | content |
|---|---|---|
| **G2-3** | 784–790 | coverage over-claim struck: §7.4's “including on every junction the sealed battery left unchecked” is FALSE — the sealed `tree` block has **eight** `byteeq: false` rows, not four: four base rows (reached, 12 walks) and four CHAMBER rows `T3A/tw`, `T3C/tw`, `T3D/tw`, `T3E/tw` at m = 2 (2 walks each, **8 walks UNREACHED**, since the walker builds no chambers). Restated to the script's own wording (“off the byte-equal set”) with the unreached set enumerated |
| **G2-7** | 829–834 | record figures decomposed: “scored 104 (66 roster + 38 chamber)” and “56 roster rows” named the same census with the same word — the decomposition **non-chamber 66 = 16-tower roster 56 + QO leg 2 + d₀ leg 8** is now displayed where both numbers appear; the walker's “458 samples” splits into **362 law samples + 96 coverage-counter increments** |
| **no-edit** | 836–844 | PE2's §4 “checked and clean” list accepted as read; one wording note fixed anyway as `[r2, hygiene]`; PE2's observation that `small=True` changes the sealed QO/d₀ pool CONTENT as well as its size is recorded here rather than in §7.4 |

**ARITHMETIC AUDIT (rule 22):** G2-3: 4 base rows × 3 walks = 12 ✔; 4 chamber rows × 2 walks = 8 ✔; total `byteeq: false` rows 4 + 4 = **8** ✔. G2-7: 56 + 2 + 8 = **66** ✔; 66 + 38 = **104** ✔; 38 + 84 + 84 + 84 + 72 = **362** ✔ (the five law families of §7.4, shard 3); 362 + 96 = **458** ✔; the three bookkeeping counters 12 + 12 + 72 = **96** ✔. **All seven cross-checks consistent.**

**CONDITIONALITY:** G2-3's 8 unreached chamber walks remain uncovered at HEAD by both instruments — a standing coverage hole (`.22`).

**DERIVATION:** Census recounts.

**RESOLUTION TRACE:** statement lines 784–790, 829–834, 836–844; the corrected verdict 2803–2814 (shard 3); the decompositions 2494–2500 (shard 3).

**TEETH:** G2-3 → **disclosed non-repair** (8 walks); G2-7 → **measurement**.

---
### EFF.GRTJB.55  [run-record]  (REPAIR ROUND r3 — header, diagnosis and the four steps)

**CANONICAL STATEMENT:** [ASSEMBLED — the r3 block header (852–869), the diagnosis (871–876) and STEPS 1–4 (877–912), quoted verbatim; STEP 1's own text is `.11`, STEP 3's is `.17`, and F-4's separate disposition is `.56`.]

> “**[REPAIR ROUND r3 — 2026-08-08 campaign (wallclock 2026-08-05). THE
> CONDITIONALITY-MATRIX NORMALIZATION.** Applied against **JB-PE3** …
> **0 CRITICAL + 8 JUSTIFICATION
> GAPS, VERDICT NOT CLEAN** — the FIRST acceptance attempt, which did not land …
> **No §2–§5 identity moves in this round either; r3 is NOTE-ONLY and all four
> scripts plus every artifact are byte-frozen.** What moves is the GRADE-SURFACE
> GENERATION MECHANISM, one citation license, two evidence classifications and
> three small record defects.”

> “**The diagnosis r3 acts on (orchestrator, ledgered): per-site patching does not
> converge.** PE1/G-9, PE2/G2-1, PE3/F-1 and PE3/F-1B are one defect found four
> times — and F-1/F-1B were introduced or missed BY r2's own mandated re-grep,
> which certified the grade cap and JB-BOX-2 "already consistent" in the same
> round its hit 7 made them inconsistent. r3 therefore does not patch sites:”

`[TABLE — compiler ledger]` r3's four steps.

| step | lines | content | unit |
|---|---|---|---|
| **STEP 1** | 877–884 | §0M, THE CONDITIONALITY MATRIX (new section, before the grade cap): 28 claim rows × 8 proviso columns, every cell filled from the body proof; five cell notes | `.11`, `.12`–`.25` |
| **STEP 2** | 885–892 | EVERY GRADE SURFACE REGENERATED FROM THE MATRIX, wholesale: grade cap (1), the four ∎ Grade lines (2–5), the seven §7.2 rows (6–12), §7.3's consequence display (13), JB-BOX-2's enumeration (14). Each superseded surface retained in place, marked SUPERSEDED. **“This kills F-1, F-1B and the recurrence class: there is now exactly one place to audit.”** | `.30`, `.38` (this shard); surfaces 2–5 shard 2; 6–13 shard 3; 14 shard 2 |
| **STEP 3** | 893–897 | F-5, the citation license: §5's recital, labelled “the (RM-m) box verbatim”, had dropped two of [RMG]'s Ĉ_m clauses; both restored VERBATIM, and the one-line derivation licensing LEMMA JB-EPS at (V, V′) = (λ, γ_{m+1}) displayed | `.17` |
| **STEP 4** | 898–912 | the evidence reclassifications and small defects: **F-2** (“both engines” → SAME-COMPUTATION, unreachable violation, corrected at three sites); **F-3** (“all four min/read ties” → THREE keyed; the fourth named MACHINE-UNKEYED with the coincidence disclosed); **F-6** (“equivalently” → “or directly” at two sites; §7.4(C) softened by the purity step); **F-7** (P_i := e_i·g_i defined at first use, [RMG] S0.1 added to the consumption list) | `.21`, `.23`, `.52`, `.40` |

**ARITHMETIC AUDIT (rule 22):** surfaces named = 1 + 4 + 7 + 1 + 1 = **14** ✔ matches “all 14 grade surfaces”. Matrix = 28 × 8 = **224** ✔. Cell notes = **5** ✔ (⟨n1⟩–⟨n5⟩, units `.21`–`.25`). PE3 findings = 8; dispositions accounted here: F-1, F-1B (STEP 2), F-2, F-3, F-4, F-5, F-6, F-7 = **8** ✔.

**CONDITIONALITY:** The mechanism's success is qualified by r4–r6 (see `.11`).

**DERIVATION:** Procedural.

**RESOLUTION TRACE:** statement lines 852–912; closing 925–929.

**PIN VERIFICATION:** `2fd271e` → commit; `GRTJB_passPE3_report.md` EXISTS.

**TEETH:** **AUDIT — in-house hostile pass** (a mechanism change, unkeyable by any battery).

---
### EFF.GRTJB.56  [supplier-finding]  (r3 F-4 — the ONE mathematical movement of r3)

**CANONICAL STATEMENT:** verbatim, lines 914–923.
**FORM:** bold-headed paragraph, set apart by the note itself.

> “**F-4's disposition, stated separately because it is the one MATHEMATICAL
> movement in r3** (in the direction of MORE conditionality, as every r3 change
> is): §2(iii)'s (RES) layer is RE-FENCED from `P<q` to `P≤q` (the BYTE-EQUAL
> CHAIN THROUGH q), because JA-RES at read level m = q+1 needs J-A's perimeter at
> m, i.e. agreement through j = q. The alternative repair — arguing that the
> representative pin φ_{q+1} := Φ_q^har discharges J-A's j = q requirement — is
> NOT taken: it is not derived anywhere in this note, and adopting it would also
> weaken what (VAL)'s fence is doing. §1's r2 sentence claiming that only
> JB-DEV(ii) cites the through-q condition is corrected in place. Nothing inside
> §3–§5 consumes (RES), so no downstream statement of this note moves.”

**SUPERSESSION KIND:** `scope-pin`.

**CONDITIONALITY:** A strict narrowing. **The refusal of the representative-pin rescue is a standing precedent that binds r6** (`.73`): “taking it at (d3) alone would unmotivate (RES)'s deeper fence”.

**DERIVATION:** See `.24` (⟨n4⟩) — level-index arithmetic on J-A's quoted quantifier.

**RESOLUTION TRACE:** statement lines 914–923; the cell 370–386; §1's correction 1340–1364 (shard 2); §2(iii)'s bracket 1439–1454 (shard 2); the r4 arithmetic correction 968–978.

**TEETH:** `NONE` — “No machine leg can catch the mis-fencing because no family keys (RES) at all”. Disposition: **AUDIT — in-house hostile pass**, and the note says so.

---
### EFF.GRTJB.57  [run-record]  (REPAIR ROUND r4 — header)

**CANONICAL STATEMENT:** verbatim, lines 931–948.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r4 — 2026-08-08 campaign (wallclock 2026-08-06).** Applied
> against **JB-PE4** … **0 CRITICAL + 8
> JUSTIFICATION GAPS, VERDICT NOT CLEAN** — the SECOND acceptance attempt, which
> did not land … PE4 re-ran all FOUR machine instruments
> bit-identically (exit 0, all four md5s intact, `git diff verification/`
> empty), verified all eight PE3 findings genuinely discharged, byte-compared
> the (RM-m) recital against RMENGINE S0.2 (11/11 lines identical), counted the
> strike system balanced (48 spans), and found NO fifth instance of the old
> surface-divergence disease — **the r3 matrix mechanism held; the frontier
> moved into the matrix's OWN precision** (F-1/F-2/F-3/F-7 are defects of §0M
> itself) **plus one scope defect in body mathematics no earlier pass had dug
> (F-4)**. **r4 is NOTE-ONLY: all four scripts and every artifact byte-frozen
> (md5s re-verified this round). Per JB-BOX-6's standing rule, §0M was edited
> FIRST and every touched surface re-derived from it.** Two read-only probes
> (to /tmp, nothing committed, instruments untouched) support F-3 and F-5; their
> outputs are transcribed at the cells that cite them.”

**CONDITIONALITY:** **The two supporting probes are UNPINNED** (rule 23): read-only to /tmp, nothing committed. Their outputs are transcribed at the citing cells (`.13`, `.62`) but are not replayable from an artifact. PE5 later “replayed both r4 probes bit-for-bit” (L1043) — which upgrades them to reproduced-by-a-second-reader, still without a committed artifact.

**ARITHMETIC AUDIT:** “strike system balanced (48 spans)” at r4; r8 records the census as “83 → 87 spans”. **This compiler's independent count at HEAD: `grep -o '~~' | wc -l` = 176 markers = 88 balanced spans, one MORE than the note's terminal figure of 87.** Recorded as source defect 4 in §8 — a discrepancy of one under a possibly different span convention, not a claimed error.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 931–948; closing 1030–1034.

**PIN VERIFICATION:** `38c4754` → commit; `GRTJB_passPE4_report.md` EXISTS; the four md5s **EXACT at HEAD** (FREEZE PREDICATE 1).

**TEETH:** four instruments reproduced bit-identically + an 11/11 byte comparison of the recital. Disposition: **executable regression + transfer audit**.

---
### EFF.GRTJB.58 — .65  [the r4 dispositions F-1 … F-8]

**MERGE POLICY:** r4 is the round in which the matrix's own precision was repaired, so **every one of its eight dispositions moves a cell, a census, a fence or a definition.** All eight are therefore separate units. Their full text is at lines 950–1028; each is quoted at its own unit below, condensed to the operative sentence plus every load-bearing figure, with the disposition's own wording preserved.

**`.58` — F-1** [supplier-finding], lines 950–958. *The matrix's summary contradicted its own row 18; row 5's (c) cell understated JA-RES.* Summary point (4) REWRITTEN (see `.29`); second leg: row 5's column (c) now records that at m = q+1 ≥ 3 JA-RES's per-digit proviso IS **(VD-(m−1)) at every on-line digit** — an evaluated-dictionary hypothesis one level down. **SUPERSESSION KIND:** `counter re-reading` + `inventory completion`. **TARGETS:** `.20` (rows 5, 18), `.29`, `.24` (⟨n4⟩), and the §2/§7.2/§7.3 surfaces. **CONDITIONALITY:** unconditional as a correction; **it strictly ADDS conditionality to row 5**. **TEETH:** row 5 stays `NONE`. **TRACE:** statement 950–958; cells 299, 370–386, 431–441.

**`.59` — F-2** [supplier-finding], lines 959–967. *The NO-LEG census undercounted.* RECOUNTED to **FOUR** (rows 4, 5, 12, 22); “both u ≥ 0 riders (rows 4 and 12) have a NONE half, so 'one of them is the u ≥ 0 rider' was false as a uniqueness claim”. Rows 13 and 18's (C-W_Q) ADJUDICATED AND EXCLUDED with reasons displayed. **SUPERSESSION KIND:** `counter re-reading`. **CONDITIONALITY:** the criterion is stated and reapplied; see `.26` and the arithmetic audit at `.20`. **TEETH:** the frontier IS the teeth-less set — **signed vacuity disclosure**. **TRACE:** statement 959–967; the amended census 395–422.

**`.60` — F-3** [supplier-finding], lines 968–978. *The (RES) re-fence gloss false on 11 of 16 roster towers.* “The FENCE is source-correct and does not move; the arithmetic gloss … is corrected at every carrying site — §0M column (a2) (the master statement), ⟨n4⟩, §1's r3 amendment, §2(iii)'s r3 bracket, the grade cap, the §2 ∎ Grade line, the §7.2 JB-DEV row, §7.3's W-3 bullet, JB-BOX-2 — to: the exclusion bites ONLY WHEN shared_upto < n (5 roster towers: T3A/T3C/T3D/T3E/I4C) … **Direction: the note claimed MORE conditionality than it had; nothing downstream moves.**” **SUPERSESSION KIND:** `counter re-reading`. **ARITHMETIC AUDIT:** 5 + 11 = **16** ✔ (the roster). **TARGETS (rule 24):** nine carrying sites, enumerated in the quotation. **CONDITIONALITY:** probe-verified, **UNPINNED** (see `.13`). **TEETH:** measurement (probe). **TRACE:** statement 968–978; master cell 196–216.

**`.61` — F-4** [lemma / scope repair], lines 979–998. ★ *THE SCOPE REPAIR — the one movement of substance in r4, a strict narrowing.* §4(iii) had transferred the per-edge λ_E line laws to `v_{m+1}` across EVERY tree edge; “the license (line = w_m, [RMG] L-LINE(iv)) is a REDUCED-CELL identity, every internal tree node is non-reduced by [RMG] S2.2's own construction, and `jb_line` keys the tie at leaves only”. **DERIVABILITY WAS CHECKED FIRST, per the repair charge:** within this note's consumption list the internal-edge transfer is **NOT derivable** ([RMG] gives only `line ≤ w_m` off reduced cells via L-CELL(i)/L-MONO; LED-Λ's face is about `line` by definition), and the one candidate route outside the list — the print valuation's multiplicativity (HigherNewton tex ~1012, **a NEW anchor this note does not consume**) with per-atom values `v_{m+1}(Φ_l) = Γ_l` — is recorded at §4(iii) as **NOT TAKEN** (“its atom value degenerates at interior periods P_t = 1, in-roster at T3E, and no instrument keys any internal-node v_{m+1} statement”). **RE-SCOPED at six sites:** §4(iii), row 17, the grade cap, the §4 ∎ Grade line, the §7.2 JB-TREE row, §7.3's W-5 bullet. **SUPERSESSION KIND:** `scope-pin`. **CONDITIONALITY:** the per-edge laws survive **as laws of the LINE functional**; the classifier reading `line = w_m = v_{m+1}` is asserted **at the R-LEAVES ONLY**. **TEETH:** `jb_line` keys leaf `line == wlev == vgen`; **no internal-node v_{m+1} statement is keyed — or, as of r4, claimed** (matrix row 17's own (f) cell). Disposition: **executable regression, scope-matched to the claim** — the rare case where the instrument's scope was RIGHT and the prose was wrong. **TRACE:** statement 979–998; body 1853–1897 (shard 2); row 17 at 311; the NOT-TAKEN route 1880–1889 (shard 2). **CITE-SCOPE NOTE:** tex ~1012 is the one HigherNewton anchor the note explicitly declines to consume — a NON-IMPORT (see §4).

**`.62` — F-5** [instrument-record], lines 999–1008. *Row 20's machine cell misdescribed `jb_eps` twice.* Rewritten to the code: “V from `range(0, min(3·e·h + 5, 25))` stepped `[::2]`, V′ same range stepped `[::3]` — a SPOT-CHECK of the lemma, never a superset of the applied instance.” Probe verdict transcribed: the applied `(λ, γ_{m+1})` is IN the sampled set on **4 of the 56** roster scored rows (T2A and T3D at m = 1) and **NOT-SAMPLED on the other 52 — including every m ≥ 2 row**. “The license stands on the lemma's PROOF at the derived membership; an instance-keyed leg is named as a candidate instrument.” **SUPERSESSION KIND:** `counter re-reading`. **CONDITIONALITY:** UNPINNED probe (read-only, /tmp). **TEETH:** **signed vacuity disclosure** — 52 of 56 rows carry no instance-keyed evidence. **TRACE:** statement 999–1008; the cell 314; the §5 echo struck at 2137–2142 (shard 2).

**`.63` — F-6** [changes-record], lines 1009–1014. *The unterminated SUPERSEDED region in §7.3.* “An explicit terminator now closes the region (matching the grade cap's), and the three live items that sat inside it — the NOT-supplied list, the r1/F1 (C-READ) notice, the CONSUMES + acceptance-counter line — are REGENERATED from the matrix inside surface 13 as [r4, F-6] bullets. **No live content sits in a non-authoritative region.**” **SUPERSESSION KIND:** `replacement`. **CONDITIONALITY:** a reading-discipline repair with real consequence: on the note's own discipline, live content inside a SUPERSEDED banner is not authoritative. **TEETH:** NONE (record). **TRACE:** statement 1009–1014; the terminator and regeneration 2652–2680 and 2728–2736 (shard 3); the pattern it copies 519–563 (`.38`).

**`.64` — F-7** [changes-record], lines 1015–1020. *Three surface-vs-table disagreements, reportable under JB-BOX-6's own rule.* (a) row 24's (a1)/(a2)/(c) cells synced with surface 14 and summary point (4), and JB-BOX-2 gains the (VD-m)-rider sentence it had omitted (row 18); (b) §7.3's W-3 bullet now names JB-VTX(d4) and (e) in its `P<q` enumeration; (c) JB-BOX-6's “or any box” narrowed to JB-BOX-2, the one box actually regenerated. **SUPERSESSION KIND:** `inventory completion` ×2 + `scope-pin` ×1. **CONDITIONALITY:** item (c) is a scope correction on the note's OWN governance rule — only one box is a regeneration; JB-BOX-1/3/4/5/6 are standing records “consistent with the table as checked, but NOT regenerations of it”. **TEETH:** NONE (record). **TRACE:** statement 1015–1020; row 24 at 318; JB-BOX-6's narrowing 2446–2449 (shard 2).

**`.65` — F-8** [definition], lines 1021–1028. ★ *The license's load-bearing object was undefined, and only half the quantifier was derived.* **THE LEVEL-m WEIGHT LATTICE is DEFINED once**, at the §5 license site, with the explicit description

> 𝒲_m = {E_m·a + Σ_{l<m} j_l·Γ_l : a ∈ ℤ_{≥0}, 0 ≤ j_l ≤ P_l − 1}

derived from [RMG] L-CELL(i) + L-LINE(iv); “the description gives 𝒲_m ⊆ ℤ_{≥0}, so the V, V′ ≥ 0 half of JB-EPS's quantifier follows from membership — the license's parenthetical warrant is now a displayed definition, not an uncited assertion.” **SUPERSESSION KIND:** `inventory completion` (an object quantified over but never defined). **CONDITIONALITY:** the description rests on L-CELL(i)'s hypothesis `deg f < deg Φ_m` — **which is exactly why r5's discharge is only a sub-window discharge** (`.67`). **DERIVATION:** displayed at §5 (L2029–2044, shard 2): every such f is a finite sum of distinct REDUCED cells with `w_m(f) = min line` over them (L-CELL(i)), so every weight value IS a reduced-cell line value; conversely every reduced cell attains its line as its own weight (L-LINE(iv)), so every such value occurs. **TEETH:** the lattice itself is corroborated by PE6's 598,500-member enumeration (verifier-owned). **TRACE:** statement 1021–1028; the definition 2025–2044 (shard 2); its consumption 2046–2062 and 2085–2131 (shard 2). **XREF:** `RMENGINE:L-CELL` — **11**; `RMENGINE:L-LINE` — **23**.

---
### EFF.GRTJB.66  [run-record]  (REPAIR ROUND r5 — header)

**CANONICAL STATEMENT:** verbatim, lines 1036–1051.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r5 …** Applied against **JB-PE5** … **0 CRITICAL + 5
> JUSTIFICATION GAPS, VERDICT NOT CLEAN** — the THIRD acceptance attempt, which
> did not land … PE5 re-ran all FOUR
> machine instruments bit-identically …,
> replayed both r4 probes bit-for-bit, verified every r4 disposition
> machine-exact, re-derived §4(i)/(ii) in full — **the first pass of
> the arc to do so; operative content SOUND** — and source-verified the 𝒲_m
> definition against [RMG]. **Its F-3 is THE GIFT: the r4 definition already
> IMPLIES the u ≥ 0 proviso on all of 𝒲_m.** r5 is NOTE-ONLY … ONE supporting
> probe ran read-only to /tmp and is transcribed at §5. Per JB-BOX-6's standing
> rule, §0M was edited FIRST and every touched surface re-derived from it.”

**CONDITIONALITY:** PE5's replay of the r4 probes is the strongest available substitute for the missing artifacts. **The r5 probe it introduces is itself UNPINNED and is struck one round later** (`.74`).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 1036–1051; closing 1103–1107.

**PIN VERIFICATION:** `39e16ee` → commit; `GRTJB_passPE5_report.md` EXISTS.

**TEETH:** four instruments bit-identical + both r4 probes replayed bit-for-bit. Disposition: **executable regression, replayed**.

---
### EFF.GRTJB.67  [lemma]  ★ (r5 F-3 — THE DISCHARGE, with its honest scope split)

**CANONICAL STATEMENT:** verbatim, lines 1053–1073.
**FORM:** bold-headed bullet.

> “* **F-3 (THE SUBSTANTIVE ITEM — the discharge, delivered with its honest
>   scope).** The four-line derivation "u ≥ 0 on ALL of 𝒲_m" was RE-DERIVED
>   from the note's own displayed description (not copied from the verifier)
>   and is DISPLAYED at §5's [r5, F-3] block, with the corollary that J-A's
>   (e,h) = (2,3), V = 1 counterexample IS excluded from 𝒲_m by parity, and a
>   fresh read-only machine confirmation (5,288,324 lattice members, 0
>   violations **[r6, F-2 — figure kept here as the record of what r5
>   reported, but NOT REPLAYABLE (parameters unrecorded); superseded at §5 by
>   the PE6 verifier's reproducible 598,500/0 record]**). The two retained sentences claiming the opposite (§2(iii)'s
>   retraction block; JB-BOX-2) are STRUCK and corrected, with the forward
>   pointer §2(iii) lacked. SCOPE, CHECKED BEFORE ANY DISCHARGE WAS RECORDED:
>   the two consuming rows (4 = §2(iii)(GRID), 12 = JB-VTX(d4)) quantify
>   f ∈ O[x] nonzero with NO DEGREE BOUND and apply JA-GRID(a) at
>   V = w_{q+1}(f), while 𝒲_{q+1} is the weight value set only on
>   deg f < deg Φ_{q+1} (L-CELL(i)'s hypothesis) — so the proviso is DISCHARGED
>   on the deg f < deg Φ_{q+1} sub-window and stays CARRIED at the full
>   quantifier as the strictly smaller MEMBERSHIP hypothesis
>   w_{q+1}(f) ∈ 𝒲_{q+1}. NEITHER ROW LEAVES THE FRONTIER (census unchanged at
>   FOUR); column (b), both row cells and every carrying surface (grade cap,
>   §2/§3 ∎ Grade lines, ⟨n3⟩, §7.1's JB-SHEAR row, §7.2's two rows, §7.3's
>   W-3 bullet, JB-BOX-2) now state the narrowed status.”

**CHAIN:** member 3 of the four-layer `u ≥ 0` chain (`.14`).

**SUPERSESSION KIND:** `scope-pin` — a theorem delivered on a named sub-window, with the residue re-characterised rather than cleared.

**TARGETS (rule 24):** the eight carrying surfaces enumerated in the quotation, plus `.14`, `.20` (rows 4, 12), `.26`, `.28`, `.31`, `.32`.

**CONDITIONALITY:** **The scope split is the unit's whole value.** The discharge is real but partial; the note refuses to record it as a full discharge, keeps both rows on the frontier, and pins the open question to one concrete membership statement. **“strictly smaller” is later struck** (`.75`, `.77`): membership is SUFFICIENT, equivalent at m = 1, of unknown strictness at m ≥ 2.

**DERIVATION:** The four-line theorem, displayed at §5 (L2046–2062, shard 2), from the r4 lattice description alone — with `s_m^wt(V) := (ℓ_{m−1}V) mod e_{m−1}` and the [RMG] S2.1 constants `E_m = e₀⋯e_{m−1}`, `Γ_l = γ_{l+1}·∏_{l<t<m} e_t`:
(1) `e_{m−1} | E_m`, and `e_{m−1} | Γ_l` for every `l ≤ m−2`; while `Γ_{m−1} = γ_m ≡ h_{m−1} (mod e_{m−1})` with `γ_m ≥ h_{m−1} ≥ 1`.
(2) Hence every `V ∈ 𝒲_m` has `V ≡ j_{m−1}·h_{m−1} (mod e_{m−1})`, so `s_m^wt(V) = j_{m−1} mod e_{m−1} ≤ j_{m−1}`.
(3) `V − s_m^wt(V)·h_{m−1} ≥ j_{m−1}·γ_m − s_m^wt(V)·h_{m−1} ≥ (j_{m−1} − s_m^wt(V))·h_{m−1} ≥ 0`.
(4) So `u ≥ 0` for EVERY `V ∈ 𝒲_m`. ∎
**COROLLARY (displayed there):** J-A's `(e_{m−1}, h_{m−1}) = (2, 3), V = 1 ⇒ u = −1` IS excluded from `𝒲_m` — by (2), `V ≡ j_{m−1} (mod 2)`, so `V = 1` forces `j_{m−1}` odd `≥ 1`, whence `V ≥ γ_m ≥ 3 > 1`.

**RESOLUTION TRACE:** statement lines 1053–1073; proof lines 2046–2062 (shard 2); scope block 2085–2111 (shard 2); correction sites 1164–1178 (r6 F-2, the probe replacement), 1179–1190 (r6 m-1), 1218–1249 (r7 F-1), 1250–1258 (r7 m-2).

**TEETH:** **the theorem carries the discharge; the machine figures are corroboration only, and the note says so** (“NOTHING RIDES ON EITHER FIGURE”). r5's own 5,288,324/0 figure is **UNPINNED and struck**; the standing record is the PE6 verifier's **598,500 members / 0 violations**, parameters disclosed in `GRTJB_passPE6_report.md` §1, independently REPRODUCED by PE7 “EXACTLY on the first natural parameterization”. Disposition: **accepted-with-decorrelation-supplied** (two independent verifiers, same figure).

---
### EFF.GRTJB.68 — .71  [the remaining r5 dispositions F-1, F-2, F-4, F-5]

**`.68` — F-1** [changes-record], lines 1074–1079. *The one live leftover of r4's leaves re-scope.* Surface 4's joint (iii)/(iv) line re-scoped in place: the JA-VAL consumption is the LEAF reading `line = w_m = v_{m+1}` for (iii) (row 17) and the `v_{m+1}`-values of the OUTPUT digits R and Q for (iv) (row 18); “the unrestricted `line(C) = w_m(C) = v_{m+1}(C)` parenthetical — **which re-imported exactly the transfer F-4 retracted** — is gone.” **SUPERSESSION KIND:** `scope-pin`. **CONDITIONALITY:** a re-scope that had silently survived one round inside the surface generated to carry it — the note flags the position: “three lines above the surface's own (iii) item” (L1944). **TEETH:** row 17's `jb_line` leaf key. **TRACE:** statement 1074–1079; surface 4 at 1938–1948 (shard 2).

**`.69` — F-2** [supplier-finding], lines 1080–1088. *§4(ii)'s closing gloss, false at exit-bound nodes.* “Every node is a sum of reduced cells” STRUCK: **L-CELL(i) requires `deg < deg Φ_m`, and every exit-bound node has `deg ≥ deg Φ_m`** (S2.2 + the S2.1 degree telescope) while sums of reduced cells have `deg < deg Φ_m`. Replaced by the true scoped statement; “the same hypothesis scope reads onto the r4/F-4 bracket's min-line parenthetical”. **Nothing downstream consumed the struck gloss** (PE5 re-derived (ii)'s operative content SOUND). **SUPERSESSION KIND:** `scope-pin`. **DERIVATION:** the degree telescope, displayed: a node taking a Φ_m-exit has `j_{m−1} ≥ P_{m−1}`, hence `deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m`. **TEETH:** `jb_tree` keys R-leaf reducedness only — “the only reducedness `jb_tree` keys”, which is exactly the scoped statement. **TRACE:** statement 1080–1088; body 1830–1851 (shard 2).

**`.70` — F-4** [scope record], lines 1089–1095. *Row 20 vs the frontier criterion.* ADJUDICATED **OUT**, reason displayed: row 20's column (c) is row 21's (VD-m) context INHERITED — an open hypothesis OF rows 21/22, where it is already counted — not an open proviso of row 20's own; row 20's own conditionality is column (e)'s [RMG] license, riding the lemma's PROOF at the derived membership (the rows-13/18 exclusion genre). **Census stays FOUR: rows 4, 5, 12, 22.** **SUPERSESSION KIND:** `inventory completion` (an adjudication added to a census, with the reason displayed). **CONDITIONALITY:** the criterion is applied consistently across three exclusions (13, 18(C-W_Q), 20). **TEETH:** row 21's end-to-end IND leg is where row 20's inherited hypothesis is already counted. **TRACE:** statement 1089–1095; the amended census 409–422; the cell 314.

**`.71` — F-5** [supplier-finding], lines 1096–1101. *Row 24's (d) cell asserted a record JB-BOX-2 does not carry.* “Grep-verified this round: the box's full extent has **NO W2-C1 record** — its only representative content is JA-BOX-3's pinned-(P-ell) sentence and the W2-C1a object `f = Φ_{q+1}^har` on the (a1) enumeration's row-13 line. The cell is struck and corrected to say so; the W2-C1 restriction is carried at rows 1/8–13/15 themselves and at surfaces 2/3.” **SUPERSESSION KIND:** `counter re-reading` — a record cell asserting a record that does not exist. **CONDITIONALITY:** **this is the matrix auditing itself against its own subject** (row 24 is the row that records what JB-BOX-2 records). **TEETH:** grep — an **arithmetic recount** AUDIT disposition (rule 27). **TRACE:** statement 1096–1101; the cell 318; JB-BOX-2 2379–2415 (shard 2). **XREF:** `GRTJA_PROOF_2026-08-08.md:JA-BOX-3` — count **3**.

---
### EFF.GRTJB.72  [run-record]  (REPAIR ROUND r6 — header)

**CANONICAL STATEMENT:** verbatim, lines 1109–1125.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r6 …** Applied against **JB-PE6** … **0 CRITICAL + 2
> JUSTIFICATION GAPS + 1 minor, VERDICT NOT CLEAN** — the FOURTH acceptance
> attempt, which did not land). PE6 re-ran all FOUR machine instruments
> bit-identically …, re-derived the §5 four-line theorem and its parity corollary EXACTLY,
> independently machine-confirmed u ≥ 0 + the step-(2) identity + the parity
> exclusion (598,500 lattice members, 0/0 violations), verified all five PE5
> findings discharged at their surfaces, **swept all 17 live u ≥ 0 carrying
> surfaces consistent**, re-walked the 28-row frontier to the same FOUR, and
> closed the arc's last unread body veins — where it found F-1. The r5 diff
> itself was CLEAN on its mathematics. r6 is NOTE-ONLY … r6 ran NO probe of
> its own — the one machine figure it newly cites is the PE6 verifier's,
> attributed. Per JB-BOX-6's standing rule, §0M was edited FIRST (row 11 split)
> and every carrying surface re-derived from it.”

**ARITHMETIC AUDIT:** “re-walked the 28-row frontier to the same FOUR” ✔ consistent with `.20`/`.26`. “all 17 live u ≥ 0 carrying surfaces” — a count this compiler cannot independently reproduce without enumerating live sites across all three shards; recorded as a checkable claim, **not audited here**, and flagged for the merge run.

**CONDITIONALITY:** **r6 introduces the arc's replayability standard**: a figure below it is struck (`.74`).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 1109–1125; closing 1192–1196.

**PIN VERIFICATION:** `ca39044` → commit; `GRTJB_passPE6_report.md` EXISTS.

**TEETH:** the PE6 verifier's independent enumerator, parameters disclosed in its report. Disposition: **accepted-with-decorrelation-supplied**.

---
### EFF.GRTJB.73  [supplier-finding]  ★ (r6 F-1 — THE FENCE; the r3/F-4 disease at the one unswept row)

**CANONICAL STATEMENT:** verbatim, lines 1127–1163.
**FORM:** bold-headed bullet.

> “* **F-1 (THE FENCE — §3(d)'s third min tie one level short; the r3/F-4
>   disease at the one row that correction never swept).** The tie (d3)
>   w_{q+1}(f) = v_{q+2}(f) is, by the note's own derivation line, "JA-VAL one
>   level up" — the m = q+1 member of JA-VAL's family — and J-A's perimeter is
>   LEVEL-INDEXED: at level m it requires byte-agreement for all j ≤ m−1, so
>   at m = q+1 that is agreement THROUGH q, the BYTE-EQUAL CHAIN THROUGH q
>   (`P≤q`), NOT the shared-key perimeter `P<q` that correctly fences
>   (d1)/(d2) — letter-for-letter the r3/F-4 analysis that re-fenced (RES).
>   RE-FENCED: §0M row 11 SPLIT — (d1)/(d2) stay on `P<q` (column (a1)), (d3)
>   moved to `P≤q` (column (a2)) — then the carrying surfaces re-derived from
>   the matrix: §3 body (d), §3's ∎ Grade block, the grade cap's JB-VTX
>   bullet, §7.2's JB-VTX row, §7.3's W-3 bullet, JB-BOX-2's enumeration
>   ((d3) moved to its `P≤q` list), plus summary point (2) RECOUNTED (THREE
>   `P≤q` consumers: rows 2, 5, and row 11's (d3)) … The exclusion BITES at q = qcap on the 5
>   shared_upto < n roster towers (T3A/T3C/T3D/T3E/I4C, the r4/F-3
>   geography): there (d3) was asserted with no J-A license, and is now
>   claimed only where the license exists. The REPRESENTATIVE-PIN rescue …
>   is NOT taken — it is not derived anywhere in this note, and
>   r3/F-4 recorded the same refusal at (RES); taking it at (d3) alone would
>   unmotivate (RES)'s deeper fence. MACHINE: no leg changes — the runner's
>   `jb_shear_vtx` has ALWAYS gated (d1)/(d3) at q ≤ `shared_upto(T,G)` …
>   which on the roster is exactly `P≤q`, so after the re-fence that gate IS
>   (d3)'s own statement fence (an instrument cut only for (d1)) and the IND
>   leg covers the full re-fenced range. NO frontier change: (d3) carries a
>   key perimeter, not an open proviso — the census stays FOUR (rows 4, 5,
>   12, 22). Nothing inside §4/§5 consumes (d3) …, so the note's
>   internal chain is unaffected; what was over-supplied was §7.3's hand-off,
>   now corrected. A strict narrowing of one sub-clause's fence.”

**SUPERSESSION KIND:** `scope-pin`.

**TARGETS (rule 24):** `.20` (row 11 SPLIT, row 24's (a2) record cell), `.13` (column (a2)'s consumer list), `.27` (summary point (2)), `.32` (the grade cap's JB-VTX bullet), plus §3 body (d) and §3's ∎ Grade block (shard 2), §7.2's JB-VTX row and §7.3's W-3 bullet (shard 3), JB-BOX-2's enumeration (shard 2).

**CONDITIONALITY:** A strict narrowing with **no frontier change and no leg change** — a rare combination the note calls out: the instrument's pre-existing gate turned out to BE the corrected fence, so the IND leg covers the whole re-fenced range. **The representative-pin refusal is inherited from r3/F-4 as binding precedent.**

**DERIVATION:** Identical in form to `.24`: J-A's level-indexed quantifier instantiated at the tie's own read level `m = q+1`. The note's own §3(d) derivation line (“the weight recursion + JA-VAL one level up”, L1666–1667, shard 2) is the ground.

**RESOLUTION TRACE:** statement lines 1127–1163; the body (d3) bracket 1667–1675 (shard 2); the split cell 305; §1's r6 amendment 1365–1372 (shard 2); the machine-gate transcription 347–356 (⟨n3⟩) with the r7/m-3 byte-faithfulness fix.

**TEETH:** **IND on the full re-fenced range** — and this compiler byte-verified the gate at `grt_jb_checks.py` L283 (see `.23`). Disposition: **executable regression, scope-matched to the corrected claim**.

---
### EFF.GRTJB.74  [instrument-record]  (r6 F-2 — the replayability standard, and an UNPINNED figure struck)

**CANONICAL STATEMENT:** verbatim, lines 1164–1178.
**FORM:** bold-headed bullet.

> “* **F-2 (the r5 probe transcribed below the arc's replayability standard).**
>   The §5 machine bracket's 5,288,324 figure is NOT REPLAYABLE: the r5
>   enumerator ran read-only to /tmp and its h-range, j-ranges, a-range and
>   counting unit were never recorded (checked this round: neither the r5
>   commit message nor the ledger entry carries them — the parameters are NOT
>   recoverable), and PE6's reproduction attempts under natural
>   parameterizations all missed. The bracket is STRUCK and REPLACED by the
>   reproducible record with attribution: the PE6 verifier's independent
>   enumerator (parameters disclosed in `GRTJB_passPE6_report.md` §1) —
>   598,500 lattice members, u < 0 violations 0, step-(2) identity violations
>   0, 1 ∉ 𝒲₁ at (2, 3). NOTHING RIDES ON EITHER FIGURE: u ≥ 0 on 𝒲_m is the
>   displayed four-line THEOREM, re-derived exactly by PE6; the probes are
>   corroboration only. The two record-layer mentions of the r5 figure (the
>   r5 round block above; the [r5] dating-record entry) keep the figure as
>   the record of what r5 reported, with [r6, F-2] pointers beside it.”

**TYPE JUSTIFICATION (rule 19):** `instrument-record` — it is a statement about the apparatus's evidentiary standing, not a run result.

**SUPERSESSION KIND:** `replacement` (an unreplayable figure replaced by a reproducible one) + `as-of scoping` (the struck figure retained as “the record of what r5 reported”).

**CONDITIONALITY:** **This unit IS the note's replayability standard, stated by example.** Under rule 23 the r5 figure is exactly an `UNPINNED` disposition — a reported run backed by no filename — and the note reaches the same verdict independently and acts on it. The replacement figure is verifier-owned and attributed; **PE7 later reproduced it EXACTLY on the first natural parameterization** (L1207–1208), which is what turns attribution into decorrelation.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 1164–1178; the struck bracket and its replacement 2067–2083 (shard 2); the two retained record-layer mentions 1058–1061 (r5 block) and the r5 footer entry 3010–3013 (shard 3).

**TEETH:** **UNPINNED → accepted-with-decorrelation-supplied.** Two independent verifiers (PE6 producing, PE7 reproducing) at 598,500/0.

---
### EFF.GRTJB.75  [changes-record]  (r6 m-1 — the membership-residue wording)

**CANONICAL STATEMENT:** verbatim, lines 1179–1190.
**FORM:** bold-headed bullet with a nested `[r7, F-1]` correction.

> “* **m-1 (the scope split's wording).** "strictly smaller MEMBERSHIP
>   hypothesis" (§5 SCOPE) and "exactly the MEMBERSHIP hypothesis" (§0M
>   column (b)) corrected to the accurate relation: membership IMPLIES the
>   needed u ≥ 0 instance at V = w_{q+1}(f) — a SUFFICIENT route, per-instance
>   a logically STRONGER hypothesis, not an equivalent — and "smaller" is
>   true only of the remaining open DOMAIN, confined to deg f ≥ deg Φ_{q+1}.
>   Direction conservative (PE6): a consumer carrying membership carries at
>   least what the proviso needs. The r5 round block's own wording above
>   stands as record. **[r7, F-1 — this bullet stands as the record of what
>   r6 wrote; the "not an equivalent" clause it records was underived and is
>   FALSE at m = 1, and is STRUCK at both live sites (§0M column (b), §5
>   SCOPE) in favor of the instance-honest relation — r7 round block below.]**”

**CHAIN:** member 4a of the `u ≥ 0` chain (`.14`); **its own correction is `.77`, which is TERMINAL.**

**SUPERSESSION KIND:** `wording-rider` — and the rider itself introduced a false affirmative claim, which is the whole point of `.77`.

**CONDITIONALITY:** **This unit is a record of a repair that bred a defect.** Its operative half (sufficiency; “smaller” true only of the open domain) survives; its non-equivalence half is struck.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 1179–1190; the two live sites 229–250 (§0M column (b)) and 2093–2107 (§5 SCOPE, shard 2); the correction 1218–1249; the quotation repair 1221–1231 (r8).

**TEETH:** none of its own; the m = 1 equivalence's tooth is PE7's 96-read-data check (`.77`).

---
### EFF.GRTJB.76  [run-record]  (REPAIR ROUND r7 — header)

**CANONICAL STATEMENT:** verbatim, lines 1198–1216.
**FORM:** bold-headed bracketed block opener.

> “**[REPAIR ROUND r7 …** Applied against **JB-PE7** … **0 CRITICAL + 1
> JUSTIFICATION GAP + 2 minor, VERDICT NOT CLEAN** — the FIFTH acceptance
> attempt, which did not land). PE7 re-ran all FOUR machine instruments
> bit-identically …, verified the r6 re-fence CLEAN end-to-end (the fence mathematics
> re-derived at the J-A source; all 12 re-fence surfaces mutually consistent;
> the load-bearing gate claim verified from committed code), independently
> REPRODUCED the replacement record EXACTLY on the first natural
> parameterization (598,500 lattice members, 0/0 violations), verified the
> r5-figure unrecoverability at both cited sources, and closed the
> re-derivation complement (**every §1–§7 body vein now re-derived or
> source-checked by at least one of seven readers**). Its one gap is r6-BRED,
> inside the m-1 wording fix. … No fence, census, grade,
> or §2–§5 identity moves.”

**CONDITIONALITY:** **“every §1–§7 body vein now re-derived or source-checked by at least one of seven readers” is the arc's coverage claim** and the closest thing the note has to a completeness statement about its own verification. It is a claim about the ARC, not about any single pass.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement lines 1198–1216; closing 1273–1278.

**PIN VERIFICATION:** `aa9b603` → commit; `GRTJB_passPE7_report.md` EXISTS.

**TEETH:** **the gate claim verified from committed code** — which this compiler independently re-verified at `grt_jb_checks.py` L283 and `grt_weld_probe.py` L211/L456–459 (`.23`). Disposition: **executable regression + arithmetic recount**.

---
### EFF.GRTJB.77  [lemma]  ★ TERMINAL of the `u ≥ 0` chain (r7 F-1 — the m = 1 equivalence)

**CANONICAL STATEMENT:** verbatim, lines 1218–1249, with the r8 quotation repair nested inside.
**FORM:** bold-headed bullet with a nested `[r8, PE8 F-1]` bracket.

> “* **F-1 (the r6 m-1 fix's non-equivalence overclaim — underived, and FALSE
>   at m = 1).** Both [r6, m-1] brackets asserted the carried membership
>   hypothesis is ~~"per-instance a logically STRONGER hypothesis than the
>   proviso, not an equivalent (or weaker one)"~~ **[r8, PE8 F-1 — the struck
>   string is a FUSION of the two sites' different wordings (site A's "than
>   the proviso" + site B's "or weaker one", parenthesized) and appears
>   byte-for-byte at NEITHER site. Each site's actual struck wording,
>   transcribed exactly from under its strike: §0M column (b) —
>   "per-instance a logically STRONGER hypothesis than the proviso, not an
>   equivalent"; §5 SCOPE — "per-instance a logically STRONGER hypothesis,
>   not an equivalent or weaker one". The fused string was semantically the
>   union of the two assertions; every disposition in this bullet
>   (underived; FALSE at m = 1; STRUCK and replaced) applies to each site's
>   verbatim wording]** — an affirmative
>   non-equivalence claim derived nowhere in the note, which dropped PE6's
>   "strictness unproved either way" qualifier in transcription, and which
>   PE7 REFUTED at every m = 1 (q = 0) instance (inside rows 4/12's
>   quantifier 0 ≤ q ≤ qcap): for every read datum (e₀, h₀, g₀),
>   {V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒲₁ EXACTLY … STRUCK at
>   both sites (§0M column (b); §5 SCOPE) and replaced by the instance-honest
>   relation: membership IMPLIES the needed instance — the sufficiency
>   direction, all any consumer uses — while the converse is
>   INSTANCE-DEPENDENT: EQUIVALENT at m = 1, containment possibly strict at
>   m ≥ 2, strictness UNPROVED either way in general (PE6's qualifier
>   restored). Direction conservative both before and after …, so no row cell's operative content,
>   no fence and no frontier member moves — the census stays FOUR.”

**CHAIN:** **TERMINAL member of the four-layer `u ≥ 0` chain** (`.14`). A chapter cut MUST use this reading.

**SUPERSESSION KIND:** `counter re-reading` (r7, an affirmative claim refuted by a counter-instance class) + `wording-rider` (r8, a fused quotation split into its two byte-exact originals).

**CONDITIONALITY:** **The correction moves nothing operative** — sufficiency was all any consumer used, so no fence, census or grade changes. What it fixes is the note's honesty about what it knows: strictness at `m ≥ 2` is **UNPROVED EITHER WAY**, and the note now says so.

**DERIVATION:** Displayed at §0M column (b) (`.14`), two directions:
- **(⊇)** the §5 four-line theorem at `m = 1`.
- **(⊆)** `u(V) ≥ 0` means `V = s·h₀ + u·e₀` with `s := (ℓ₀V) mod e₀ ∈ [0, e₀−1]` and `u ≥ 0`; take `j := s ≤ e₀−1 ≤ P₀−1` (since `P₀ = e₀g₀`, `g₀ ≥ 1`) and `a := u` in `𝒲₁ = {e₀a + h₀j : a ≥ 0, 0 ≤ j ≤ P₀−1}`.

**RESOLUTION TRACE:** statement lines 1218–1249; the two-direction proof displayed at 236–247 (inside `.14`); the third site's sweep 1250–1258 (m-2); the quotation repair 1280–1294 (r8); the live sites 229–250 and 2093–2107 (shard 2).

**TEETH:** **PE7's machine check: 96 read data (all coprime `(e₀,h₀)` with `e₀ ≤ 6, h₀ ≤ 8, g₀ ≤ 3`), every `V ∈ [0, 150)`, 0 counterexamples to the equivalence** (`GRTJB_passPE7_report.md` §2 F-1, commit `aa9b603`). **PE8 re-confirmed both directions on a WIDER box: 340 read data, 0 counterexamples** (L1154–1156). Disposition: **accepted-with-decorrelation-supplied** — two verifiers, two box sizes, both clean.

---
### EFF.GRTJB.78  [changes-record]  (r7 m-2 — the third site of the same wording defect)

**CANONICAL STATEMENT:** verbatim, lines 1250–1258.
**FORM:** bold-headed bullet.

> “* **m-2 (the m-1 disease at a THIRD live site, which the r6 sweep —
>   transcribing PE6's two-site quote list as the sweep universe — never
>   reached).** JB-BOX-2's [r5, F-3] bracket still said the open residue "is
>   exactly lattice MEMBERSHIP": the same necessity-overstating "exactly"
>   that r6 struck at §0M column (b). STRUCK, with an [r7] pointer to column
>   (b)'s corrected relation — membership is the SUFFICIENT hypothesis the
>   note CARRIES (and at m = 1 moreover equivalent, F-1). The surrounding
>   operative content (holds by definition at deg f < deg Φ_{q+1}, not
>   established off it) was verified accurate by PE7 and is untouched.”

**SUPERSESSION KIND:** `wording-rider`.

**CONDITIONALITY:** **The named cause is a sweep-universe defect**: r6 took a verifier's two-site quote list as the universe of sites, and a third site survived. This is the **fourth** distinct instance in this note of “a fix applied to the sites a verifier named rather than to the sites the defect occupies” (cf. `.46`, `.49`, `.73`). **Recorded as a standing pattern for the merge run and for any future repair protocol.**

**DERIVATION:** A site sweep.

**RESOLUTION TRACE:** statement lines 1250–1258; the corrected site 2365–2369 (JB-BOX-2, shard 2).

**TEETH:** NONE (wording). Disposition: **AUDIT — in-house hostile pass**.

---
### EFF.GRTJB.79  [instrument-record]  (r7 m-3 — byte-faithful gate transcription)

**CANONICAL STATEMENT:** verbatim, lines 1259–1271.
**FORM:** bold-headed bullet.

> “* **m-3 (byte-faithful gate transcription).** All four live transcriptions
>   of (d3)'s machine gate stated the single conjunct q ≤ shared_upto; the
>   code's d3 assertion (grt_jb_checks.py L283) is `if q + 1 <= G.RANK and
>   minH != G.vgen(q + 2, f):` under `q <= L`. The second conjunct is a
>   vgen-domain guard, IDENTICALLY TRUE on the loop domain — RANK = T.NR =
>   n+1 (GmnLeg L211 via gmn_from_tower L456–459; re-read from committed
>   source this round) and the loop caps q ≤ qcap ≤ n, so q+1 ≤ n+1 = RANK
>   always — verified redundant by PE7 (m-3, commit aa9b603), so every
>   coverage claim ("the gate IS the fence"; "the IND leg covers the full
>   re-fenced range") stands unchanged. ONE PARENTHETICAL ADDED at each of
>   the four sites: ⟨n3⟩ (the cell the others cite, full transcription), the
>   §3 machine bracket, §7.1's JB-SHEAR row, and the r6 round block's MACHINE
>   clause.”

**SUPERSESSION KIND:** `inventory completion` (a conjunct present in the code and absent from every transcription).

**PIN VERIFICATION (rule 23) — INDEPENDENTLY RE-VERIFIED BY THIS COMPILER, 3/3 EXACT:**
- `verification/openmath/grt_jb_checks.py` **L283** = `                if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):` — **byte-exact match** to the note's transcription.
- `verification/openmath/grt_weld_probe.py` **L211** = `        self.RANK = len(levels)`.
- `verification/openmath/grt_weld_probe.py` **L456–459** = `def gmn_from_tower(T, mut=False):` … `levels = [(T.e[i], T.h[i], list(T.psi[i])) for i in range(T.NR)]` … `return GmnLeg(T.R, T.d0, T.Phi[0], levels, mut_droptwist=mut)`.
- **Therefore `RANK = len(levels) = T.NR`, and the redundancy derivation is source-true.** (Note the two line-number pins are in `grt_weld_probe.py`, not `grt_jb_checks.py`; the note writes them as “GmnLeg L211 via gmn_from_tower L456–459” without naming the file. Recorded as source defect 5 in §8 — a file-attribution ellipsis, referent unambiguous and verified.)

**CONDITIONALITY:** **The redundancy makes the correction cost-free**: every coverage claim reading the gate stands unchanged. Had the conjunct not been redundant, the (d3) IND leg's range claim would have needed re-scoping.

**DERIVATION:** Code reading + the loop bound.

**RESOLUTION TRACE:** statement lines 1259–1271; the four sites 347–356 (⟨n3⟩), 1755–1765 (§3 machine bracket, shard 2), 2482 (§7.1 JB-SHEAR row, shard 3), 1150–1155 (r6 MACHINE clause).

**TEETH:** **arithmetic recount / source re-read** — an AUDIT disposition; re-verified here a third time.

---
### EFF.GRTJB.80  [run-record]  (REPAIR ROUND r8 — the ONE-QUOTATION ROUND)

**CANONICAL STATEMENT:** verbatim, lines 1280–1299.
**FORM:** bold-headed bracketed block (header and disposition are one paragraph).

> “**[REPAIR ROUND r8 — 2026-08-08 campaign (wallclock 2026-08-06). THE
> ONE-QUOTATION ROUND.** Applied against **JB-PE8** … **0 CRITICAL + 0 JUSTIFICATION GAPS + 1 MINOR, VERDICT NOT CLEAN**
> — the SIXTH acceptance attempt, which did not land). The ONE fix (PE8 F-1,
> quotation form): the r7 F-1 bullet above quoted, as the assertion of "both
> [r6, m-1] brackets", a FUSED string appearing byte-for-byte at NEITHER site
> — the fused quote is now STRUCK in place and each site's actual struck
> wording is quoted separately, byte-exactly, in the [r8, PE8 F-1] bracket
> there. NOTE-ONLY; no fence, frontier, grade, or §2–§5 identity moves; all
> four instruments BYTE-FROZEN (md5s re-verified this round at their sealed
> values; `git diff verification/` empty); r8 ran NO probe and cites NO new
> figure. Strike census 83 → 87 spans (the four r8 spans: the fused quote,
> the [r7] S-STATUS wrap, the §7.3 [r7] counter clause, the footer r7 Arc
> line). Acceptance counter unchanged at **0/2** …”

**SUPERSESSION KIND:** `wording-rider` (a fused quotation split into its two byte-exact originals).

**CONDITIONALITY:** **The final round of the arc, and its content is a quotation-fidelity fix** — which is itself the arc's strongest evidence that the mathematics had stopped moving: PE8 returned **0 CRITICAL + 0 GAPS**, and the only finding was that one bracket mis-quoted two of the note's own sentences.

**ARITHMETIC AUDIT (rule 22):** the note reports **83 → 87 spans** (+4 named). **This compiler's independent count at HEAD: 176 `~~` markers = 88 balanced spans.** Discrepancy of **one** against the note's terminal figure. Cross-check: r4 counted “the strike system balanced (48 spans)”. The gap 48 → 83 spans over rounds r4–r7 is not itemised in the note, so the discrepancy cannot be localised from the text; span-counting conventions may differ (e.g. a `~~` occurring inside a quoted string). **Recorded as source defect 4 in §8; nothing rides on it.**

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 1280–1299; the fix itself 1221–1231 (inside `.77`); the four named spans at 1221–1231, 112–140, §7.3's counter clause 2673–2678 (shard 3), and the footer r7 Arc line 3078–3081 (shard 3).

**PIN VERIFICATION:** `6c61b82` → commit; `GRTJB_passPE8_report.md` EXISTS; four md5s **EXACT at HEAD**.

**TEETH:** PE8's own wider-box re-confirmation (340 read data, 0 counterexamples) is the round's incoming evidence, not its output. Disposition: **AUDIT — in-house hostile pass** (a quotation defect no battery can see).

---
### EFF.GRTJB.81  [definition]

**CANONICAL STATEMENT:** verbatim, lines 1305–1309 (through “sealed in the probe.”).
**FORM:** inline sentence (a dictionary import).

> “Harness and P-index dictionary VERBATIM from J-A §1 (itself from W-2
> §1.1–1.2): [ILN]† S0.1 class pin; GMN level i = harness read i−1; GMN keys
> φ_i = harness Φ_{i−1}; v_i = w_{i−1} (THEOREM JA-VAL, consumed); GMN
> order-q residual R_q pairs with the harness level-q read R_q v; pins
> (P-ell)/(P-lift)/(P-root)/(P-index) as sealed in the probe.”

**CONDITIONALITY:** A verbatim import at J-A's grade. **The index shift `GMN level i = harness read i−1` is the single most load-bearing convention in the note** — every level-slip defect in the arc (r3/F-4, r6/F-1) is a failure to instantiate a supplier's level-indexed quantifier through this dictionary. **Supplier grade updated (shard 3, L3148–3161): GRTJA is now ACCEPTED at 2/2 at `17d2a32`** (body byte-frozen, md5 `cba309ce` @ `f131c53`).

**DERIVATION:** Import, not derivation.

**RESOLUTION TRACE:** statement lines 1305–1309; consumed at `.91`, `.101`, `.104`, `.114`; supplier-grade correction 3148–3161 (shard 3).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VAL` — grep-verified count **7**.
XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — count **13**.
XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C1` — count **22** (the §1.1–1.2 source section is pinned by designation, not by §-anchor).

**TEETH:** The pins are sealed in `grt_weld_probe.py` (EXISTS at HEAD); the dictionary's own content is exercised by every IND family.

---
### EFF.GRTJB.82  [definition]  ★ the two perimeters, defined once

**CANONICAL STATEMENT:** verbatim, lines 1309–1334 — the struck conflated line, the `[r2, G2-6]` header, and the two-condition ASCII display.
**FORM:** bracketed rider + fixed-width display.

> “~~**Shared-key
> perimeter at level q**: Φ_j^har = φ_{j+1}^cls byte-for-byte for all j ≤ q.~~
> **[r2, G2-6 — TWO DISTINCT CONDITIONS, defined once, named apart. The struck
> line conflated them and was cited (at §2(iii) and at the JB-VTX theorem) for
> the other one; the two differ by exactly the level q itself, which is the
> level the `+1` in `qcap` exists for. Both names below are used verbatim from
> here on.**
>
>     BYTE-EQUAL CHAIN THROUGH q :  Φ_j^har = φ_{j+1}^cls byte-for-byte for
>         every j ≤ q — the condition of the W-2 §3.4(3) byte law, consumed by
>         JB-DEV(ii) (it is what makes Φ_q^har the classifier's OWN key at
>         level q). This is the struck line's content, retained under its own
>         name.
>
>     SHARED-KEY PERIMETER (the runner's own `qcap_of`) :  keys shared STRICTLY
>         BELOW q, i.e. Φ_j^har = φ_{j+1}^cls byte-for-byte for every
>         1 ≤ j ≤ q−1 — NOTHING is required at j = q. Equivalently, with
>         shared_upto := max{L ≥ 0 : Φ_j^har = φ_{j+1}^cls for all 1 ≤ j ≤ L}
>         and qcap := min(n, shared_upto + 1), the perimeter is the LEVEL RANGE
>
>             0 ≤ q ≤ qcap ,      qcap = min(n, shared_upto + 1),
>
>         which is exactly `qcap_of(T, G) = min(T.n, GJA.shared_upto(T,G) + 1)`
>         with the runner's loops `for q in range(0, qcap_of(T,G) + 1)`. The top
>         level q = qcap = shared_upto + 1 IS in scope, and at it the keys need
>         NOT agree at j = q — the perimeter is a condition below q, never at q.”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| name | short | condition | equivalent form | consumers |
|---|---|---|---|---|
| **BYTE-EQUAL CHAIN THROUGH q** | `P≤q` | `Φ_j^har = φ_{j+1}^cls` for every `j ≤ q` | J-A's perimeter instantiated at level `m = q+1` | JB-DEV(ii)'s byte clause (W-2 §3.4(3)); **+ JB-DEV(iii)(RES) [r3, F-4]**; **+ JB-VTX(d3) [r6, F-1]** |
| **SHARED-KEY PERIMETER** | `P<q` | `Φ_j^har = φ_{j+1}^cls` for every `1 ≤ j ≤ q−1`; **nothing at `j = q`** | the level range `0 ≤ q ≤ qcap`, `qcap := min(n, shared_upto+1)` = the runner's `qcap_of(T,G)` | JB-DEV(iii)(VAL)/(GRID); JB-VTX(a)(b)(c)(d1)(d2)(d4)(e); JB-TREE(iii)/(iv) at level m |

**SUPERSESSION KIND:** `replacement` — one conflated definition split into two named ones.

**CONDITIONALITY:** **Unconditional as definitions, and they are the note's most-cited objects.** `P≤q` is STRICTLY STRONGER than `P<q`; the two differ at `j = q`, and as fences over the level range **the exclusion bites only where `shared_upto < n`** — 5 of the 16 roster towers (T3A/T3C/T3D/T3E/I4C), the r4/F-3 geography, master statement at §0M column (a2) (shard 1 `.13`).

**DERIVATION:** Definition; the level-range equivalence is read off `qcap := min(n, shared_upto+1)` against the runner's loop bound. **This compiler verified the runner's loop form is as quoted:** the shard-1 gate check at `grt_jb_checks.py` L283 sits under `q <= L` inside exactly this loop.

**RESOLUTION TRACE:** statement lines 1309–1334; matrix columns (a1)/(a2) at shard 1 `.12`/`.13`; correction sites 1336–1364 (`.03`) and 1365–1372 (`.04`).

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:3.4` — count **35** (§-anchor; upper bound. The byte law's designation is independently pinned by `(C-coll)`, count **27**, and `TH-BASE`, count **8**).

**TEETH:** `jb_keyeq`'s byte census keys `P≤q` at q = 1 (25 rows, 3 VACUOUS); the runner's loop bound keys `P<q`; the off-perimeter counter is **0** on the roster.

---
### EFF.GRTJB.83  [supplier-finding]

**CANONICAL STATEMENT:** verbatim, lines 1336–1364 — the struck exhaustiveness sentence and the `[r3, F-4]` correction, with the `[r4, F-3]` arithmetic fix nested inside.
**FORM:** bracketed rider on a struck sentence.

> “~~**Every r1/r2 restatement (§2(iii), the JB-VTX theorem and grade line,
> JB-BOX-2, §7.2, §7.3) now cites the SHARED-KEY PERIMETER in this second sense,
> `j < q`, 0 ≤ q ≤ qcap, and no statement cites §1 for the through-q condition
> except JB-DEV(ii)'s byte clause, which means the first.**~~
> **[r3, F-4 — THE STRUCK SENTENCE IS FALSE IN ITS SECOND HALF, and the error is
> a level slip, not a wording slip. J-A's perimeter is LEVEL-INDEXED ("Shared-key
> perimeter at level m: Φ_q^har = φ_{q+1}^cls byte-for-byte for all q ≤ m−1"), so
> instantiating it at each layer's OWN level gives TWO different conditions
> inside §2(iii): (VAL) is JA-VAL at level q and needs j ≤ q−1 = the SHARED-KEY
> PERIMETER `P<q`; (RES) is JA-RES at read level m = q+1 and needs j ≤ m−1 = q,
> i.e. the BYTE-EQUAL CHAIN THROUGH q. So there are exactly TWO consumers of the
> through-q condition, not one: JB-DEV(ii)'s byte clause AND JB-DEV(iii)'s (RES)
> layer. CORRECTED STATEMENT, which §0M's matrix column (a2) now carries as the
> single record: every restatement of the (VAL)/(GRID) layers and of all of
> JB-VTX and JB-TREE(iii)/(iv) cites the SHARED-KEY PERIMETER `P<q`
> (0 ≤ q ≤ qcap); the (RES) layer and JB-DEV(ii)'s byte clause cite the
> BYTE-EQUAL CHAIN THROUGH q. ~~The two differ exactly at the top level
> q = qcap = shared_upto+1 … r2's single fence over-supplied (RES) by exactly one level.~~ **[r4, F-3 — the
> struck arithmetic held on only 5 of the 16 roster towers. qcap :=
> min(n, shared_upto+1), so q = qcap is a level where `P≤q` fails ONLY WHEN
> shared_upto < n (T3A, T3C, T3D, T3E, I4C); when qcap = n ≤ shared_upto the two
> fences COINCIDE on the whole range 0 ≤ q ≤ qcap and r2's fence over-supplied
> (RES) at NO level (the other 11 towers). The corrected record is §0M column
> (a2); probe-verified against the runner's own `qcap_of`/`shared_upto`,
> 2026-08-06.]** No machine leg can
> catch this: the runner keys (VAL) over `range(0, qcap+1)` and keys (RES)
> NOWHERE (§0M row 5, cell note ⟨n4⟩).]**”

**CHAIN (rule 25):** r2's exhaustiveness claim → **[r3, F-4]** correction (TWO consumers, not one) → **[r4, F-3]** arithmetic fix (the exclusion bites on 5/16) → **[r6, F-1]** (`.84`, a THIRD consumer). **TERMINAL = the r6 reading**, recorded at `.84`.

**SUPERSESSION KIND:** `counter re-reading` (r3, a false exhaustiveness claim) + `counter re-reading` (r4, a false arithmetic gloss).

**CONDITIONALITY:** **A strict narrowing that moves a mathematical fence.** The re-fence direction is toward MORE conditionality wherever it bites at all. **The representative-pin rescue is REFUSED** (shard 1 `.56`) and the refusal binds r6.

**DERIVATION:** Level-index arithmetic on J-A's own quoted quantifier, displayed inside the bracket: at read level `m`, J-A requires agreement for `j ≤ m−1`; (VAL) is JA-VAL at level `q` ⇒ `j ≤ q−1`; (RES) is JA-RES at read level `m = q+1` ⇒ `j ≤ q`. The r4 arithmetic: if `shared_upto < n` then `qcap = shared_upto+1` and `P≤q` fails at `q = qcap` by maximality of `shared_upto`; if `shared_upto ≥ n` then `qcap = n ≤ shared_upto` and both fences require agreement only at levels `≤ shared_upto`, so they coincide on the whole range.

**RESOLUTION TRACE:** statement lines 1336–1364; the cell note ⟨n4⟩ 370–386 (shard 1 `.24`); the disposition 914–923 (shard 1 `.56`); the r4 correction 968–978 (shard 1 `.60`); the third consumer 1365–1372.

XREF: `GRTJA_PROOF_2026-08-08.md:JA-RES` — **20** · `JA-VAL` — **7** · `shared-key perimeter` — **5**.

**TEETH:** **`NONE`, signed and quoted:** “No machine leg can catch this: the runner keys (VAL) over `range(0, qcap+1)` and keys (RES) NOWHERE”. Disposition: **disclosed non-repair** + **AUDIT — in-house hostile pass**.

---
### EFF.GRTJB.84  [supplier-finding]  ★ TERMINAL of the perimeter-consumer chain

**CANONICAL STATEMENT:** verbatim, lines 1365–1372.
**FORM:** bracketed rider.

> “**[r6, F-1 — the count above is amended a second time by the SAME level-slip
> disease at a third site: JB-VTX's (d3) min tie w_{q+1}(f) = v_{q+2}(f) is
> "JA-VAL one level up" (§3(d)), i.e. JA-VAL at level q+1, so it too needs the
> BYTE-EQUAL CHAIN THROUGH q. THREE consumers of the through-q condition:
> JB-DEV(ii)'s byte clause, JB-DEV(iii)'s (RES) layer, and JB-VTX(d3) (§0M
> row 11 (a2)); "all of JB-VTX" in the corrected statement above now reads
> with (d3) excepted. Unlike (RES), (d3) HAS a machine leg on its full fence:
> the runner gates it at q ≤ shared_upto, which is exactly `P≤q`.]**”

**CHAIN:** TERMINAL member of the chain opened at `.83`. **A chapter cut must read: THREE `P≤q` consumers — JB-DEV(ii), JB-DEV(iii)(RES), JB-VTX(d3); everything else on `P<q`.**

**SUPERSESSION KIND:** `inventory completion` — a third consumer added to a list twice claimed complete.

**CONDITIONALITY:** **NO frontier change** — (d3) carries a key perimeter, not an open proviso, so the four-member NO-LEG frontier (rows 4/5/12/22) is untouched. **And no leg change** — the runner's pre-existing gate turned out to BE the corrected fence.

**DERIVATION:** Identical in form to `.83`: the note's own §3(d) derivation line (“the weight recursion + JA-VAL one level up”, L1666–1667) instantiated at the tie's own read level.

**RESOLUTION TRACE:** statement lines 1365–1372; the body (d3) bracket 1667–1675 (`.104`); the split matrix cell 305 (shard 1 `.20` row 11); the disposition 1127–1163 (shard 1 `.73`); the recount 422–428 (shard 1 `.27`).

**TEETH:** **IND on the full re-fenced range.** The gate `if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):` at `grt_jb_checks.py` **L283** was **byte-verified at HEAD by this compiler**, and the second conjunct's redundancy re-derived from `grt_weld_probe.py` L211 (`self.RANK = len(levels)`) and L456–459 (`levels = […for i in range(T.NR)]`), giving `RANK = T.NR = n+1 ≥ qcap+1`. Disposition: **executable regression, scope-matched**.

---
### EFF.GRTJB.85  [definition]

**CANONICAL STATEMENT:** verbatim, line 1373.
**FORM:** inline sentence.

> “Read data A_m := ℓ_{m−1}g_{m−1}γ_m, W_m := w_mΦ_m as in W-2/J-A.”

**CONDITIONALITY:** Unconditional. **`A_m` is the character exponent whose triviality is JA-VDIND's hypothesis** — the object the whole (VD-m) conditionality turns on (`.93`, `.127`). **`W_m := w_mΦ_m` is the roman-W read datum that §5's `[r4, F-8]` deliberately distinguishes from the SCRIPT `𝒲_m` weight lattice** (`.120`) — a notational collision the note flags explicitly.

**DERIVATION:** Definition, imported.

**RESOLUTION TRACE:** statement line 1373; `A_m` consumed at 1478–1491 and 2192–2194; `W_m` vs `𝒲_m` disambiguated at 2033–2035.

**TEETH:** NONE (definition).

---
### EFF.GRTJB.86  [definition]  ★ the two frames and the shear

**CANONICAL STATEMENT:** verbatim, lines 1375–1386.
**FORM:** bold-headed paragraph + fixed-width display.

> “**The two frames.** Fix a level q (0 ≤ q ≤ n) and nonzero f ∈ O[x] with
> Φ_q-development f = Σ_i A_i·Φ_q^i (iterated division by the monic Φ_q).
>
>     PRINT FRAME    U(f) := { (i, u_i) : A_i ≠ 0 },
>                    u_i := v_{q+1}(A_i·Φ_q^i) = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})
>                    — the print's own N_{q+1}-ordinates (tex ~1370).
>
>     SHEARED FRAME  H(f) := { (i, e_q·w_q(A_i) + i·γ_{q+1}) : A_i ≠ 0 }
>                    — the harness eq-(12) ordinates (the S0.2 weight
>                    recursion's arguments; the GD-2 frame normalization).
>
>     THE SHEAR      Σ_q : (i, u) ↦ (i, e_q·u + h_q·i).”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| object | definition | provenance |
|---|---|---|
| **PRINT FRAME `U(f)`** | `{ (i, u_i) : A_i ≠ 0 }`, `u_i := v_{q+1}(A_i·Φ_q^i) = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})` | the print's own `N_{q+1}`-ordinates, `HigherNewton.tex` ~1370 |
| **SHEARED FRAME `H(f)`** | `{ (i, e_q·w_q(A_i) + i·γ_{q+1}) : A_i ≠ 0 }` | the harness eq-(12) ordinates; the S0.2 weight recursion's arguments; the GD-2 frame normalization |
| **THE SHEAR `Σ_q`** | `(i, u) ↦ (i, e_q·u + h_q·i)` | a theorem clause (§3(a)), **never a silent convention** |

**CONDITIONALITY:** Unconditional as definitions. **The frame declaration is a standing discipline of the note: “every polygon statement below displays which frame it lives in, and the shear itself is a theorem clause (§3(a)), never a silent convention.”** `Σ_q` is abscissa-preserving with positive `u`-coefficient `e_q` — the two properties LEMMA JB-AFF needs (`.99`). **E-3 (shard 3) later narrows what `Σ_q` preserves: the abscissa run, NOT ambient lattice data** — see `.103`.

**DERIVATION:** Definitions. The `Φ_q`-development exists and is unique by division with remainder by a monic polynomial over any commutative ring (the same fact §2(i) uses).

**RESOLUTION TRACE:** statement lines 1375–1386; consumed at 1636–1694 (§3(a)–(e)); correction site 3199–3228 (E-3, on what the shear preserves).

XREF: `docs/references/HigherNewton.tex:phiradic` — count **2** (the `φ_r`-adic development genre). The `~1370` ordinate definition is a LINE PIN, verified present in the file; NS-11 identifies the surrounding block.
XREF: `lean/notes/openmath/RMENGINE_2026-08-08.md:S0.2` — count **13**.
XREF: `lean/notes/openmath/GD23_phaseB_attempt.md:GD-2` — count **7**.

**TEETH:** `jb_vtx` computes **fresh lower hulls of BOTH frames** and the vertex bijection between them (IND, 893 samples).

---
### EFF.GRTJB.87  [instrument-record]

**CANONICAL STATEMENT:** verbatim, lines 1388–1396.
**FORM:** bold-headed paragraph with an `[r1, G-8]` re-attribution.

> “The names are load-bearing: ~~GD-2's T-F machine check (41,720 instances)~~
> **[r1, G-8 — instrument re-attributed]** the T-F machine check of the O1thr
> rev-3 runner (`O1thr_phaseB_verifybrief_rev3.md` §9, family T-F: 41,720
> site-instances, 0 violations of WGEO/(M6c); the runner is CITED BY GD-2/GD-3,
> it is not GD-2's own instrument) verified the polygon tie in the SHEARED frame
> and measured 7,472 violations of the unsheared identification — every polygon
> statement below displays which frame it lives in, and the shear itself is a
> theorem clause (§3(a)), never a silent convention. (Both figures were
> re-checked against that source in JB-PE1 and are current, not stale.)”

**SUPERSESSION KIND:** `provenance-rider` — the instrument is re-attributed; the figures are unchanged.

**CONDITIONALITY:** **This is the empirical ground for the whole shear discipline**: the unsheared identification is not merely unproved, it is MEASURED FALSE 7,472 times. That measurement is what makes `.102`'s “The unsheared identification … is FALSE in general” a reported fact rather than a rhetorical flourish, and it is the note's own teeth family MJB-VTX one level down.

**PIN VERIFICATION (rule 23) — the cited source re-read at HEAD by this compiler:** `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md` **EXISTS**; fixed-string counts in it — `T-F` **10**, `41,720` **8**, `7,472` **2**, `WGEO` **16**, `M6c` **32**. **All five figures/designations verified present at the cited source. The r1/G-8 re-attribution is confirmed.**

**DERIVATION:** Foreign measurement, cited.

**RESOLUTION TRACE:** statement lines 1388–1396; the disposition 691–696 (shard 1 `.47` item G-8); consumed at 1648–1650 (`.22`).

XREF: `lean/notes/openmath/GD23_phaseB_attempt.md:GD-2` — **7** · `GD-3` — **5**.
XREF: `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md:T-F` — **10**.

**TEETH:** **foreign-note measurement consumed as decorrelation** — 41,720 site-instances / 0 violations in the sheared frame against 7,472 violations unsheared. Disposition: **foreign-note evidence**, re-checked by JB-PE1.

---
### EFF.GRTJB.88  [definition]

**CANONICAL STATEMENT:** verbatim, lines 1402–1410 — the theorem head plus the `[r1, G-7]` notation definition.
**FORM:** bold-headed opener + bracketed definition.

> “**THEOREM JB-DEV.** Level q ≥ 0, f ∈ O[x] nonzero, notation §1.
>
> **[r1, G-7 — notation, defined here at first use.]** m_{q+1}^GMN := the GMN
> print's KEY DEGREE at level q+1, i.e. deg φ_{q+1} = d₀·∏_{j<q} e_j g_j
> (the print's own recursion: deg φ_1 = d₀ = deg Φ_0^har and
> deg φ_{r+1} = e_r f_r · deg φ_r with (e_r, f_r) the print's level-r
> ramification/residual pair = the harness (e_{r−1}, g_{r−1})). The identity
> deg Φ_q^har = m_{q+1}^GMN is a consequence of the P-index dictionary of §1,
> not an extra hypothesis. (The symbol was used undefined in r0.)”

**SUPERSESSION KIND:** `inventory completion` (a symbol used undefined).

**CONDITIONALITY:** The theorem head's blanket “Level q ≥ 0” is **CORRECT for clauses (i), (ii), (iv)** and is narrowed per layer inside clause (iii) (`.91`). The degree identity is explicitly **not an extra hypothesis** — it follows from `.81`'s dictionary.

**DERIVATION:** Definition + a one-line consequence. `deg φ_{r+1} = e_r f_r · deg φ_r` with `(e_r, f_r) = (e_{r−1}, g_{r−1})` harness-side telescopes to `d₀·∏_{j<q} e_j g_j`, which is `deg Φ_q^har` by the harness recursion `deg Φ_{j+1} = e_j g_j · deg Φ_j`.

**RESOLUTION TRACE:** statement lines 1402–1410; the disposition 688–690 (shard 1 `.47` item G-7); the harness degree recursion is [ILN]† S0.1's.

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13**.

**TEETH:** Exercised inside `jb_dev`'s development legs (the key degree is what the division is by).

---
### EFF.GRTJB.89  [lemma]  (JB-DEV clause (i))

**CANONICAL STATEMENT:** verbatim, lines 1412–1421.
**FORM:** bold clause label + paragraph.

> “**(i) [same division].** Φ_q^har is monic of degree m_{q+1}^GMN, and the
> print's φ_{q+1}-adic development of f AT THE REPRESENTATIVE
> φ_{q+1} := Φ_q^har is the harness Φ_q-development digit-for-digit: both
> are THE canonical division chain by the same monic polynomial (uniqueness
> of division with remainder). Under W-2 clause 1, Φ_q^har is a GMN Def-2.12
> admissible representative on W-2's perimeter (of the ξ-conjugate class at
> the pinned (P-ell) convention; of the type itself when the character is
> support-trivial; STRICT at every level of the transported chamber, W2-C3)
> — so the left side is a legitimate print development, not a harness-only
> object.”

**CONDITIONALITY:** **PERIMETER-FREE** (matrix row 1; every level `q ≥ 0`), at the W2-C1 admissible representative. **W-2 clause 1's own conditionality rides**, and **E-2 (shard 3) re-reads the W2-C3 half** at the supplier's proved-to-first-twist (38/44) / measured-above (6/44) split. **Supplier grade updated: GRTW2 ACCEPTED at 2/2 (`adc6cf3`) at that honest split.**

**DERIVATION:** Uniqueness of quotient and remainder in division by a monic polynomial over any commutative ring — “the print's development (tex `phiradic` genre) and the harness development are the same recursion”; the representative legitimacy is W-2 clause 1 consumption (proof at L1549–1552).

**RESOLUTION TRACE:** statement lines 1412–1421; proof lines 1549–1552; matrix row 1 at 295 (shard 1); correction site 3135–3142 (E-2), 3148–3161 (supplier grade).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C1` — **22** · `W2-C3` — **22**.
XREF: `docs/references/HigherNewton.tex:phiradic` — **2**.

**TEETH:** `jb_dev` — `fresh_dev` (this runner's own schoolbook division) vs `PolyO.dev`, **893 samples, IND**. Plus a **SAME** third leg, disclosed at ⟨n1⟩ (shard 1 `.21`): `G.P.dev` is the same method on the same ring object behind a guard that already forced agreement — **violation UNREACHABLE, carries no information**.

---
### EFF.GRTJB.90  [lemma]  (JB-DEV clause (ii))

**CANONICAL STATEMENT:** verbatim, lines 1423–1428.
**FORM:** bold clause label + paragraph.

> “**(ii) [byte clause].** If the junction chain is byte-equal through q (the
> W-2 §3.4(3) byte law from read data; TH-BASE gives it always at q = 1),
> then φ_{q+1}^cls = Φ_q^har byte-for-byte and (i) is the classifier's OWN
> expansion at its own construct key. On the weld roster the byte-equal set
> is the probe's F1 verdict pattern (12 GREEN / 18 RED of 30 walked
> junctions, reproduced by W-2's CK-BYTE from read data alone — consumed).”

**CONDITIONALITY:** **`P≤q` IS its hypothesis** (matrix row 2 — the one row where the through-q condition is not a fence but the antecedent). TH-BASE makes it unconditional at `q = 1`.

**ARITHMETIC AUDIT (rule 22):** 12 GREEN + 18 RED = **30 walked junctions** ✔. **Cross-check against the coverage correction (r1/G-6, shard 1 `.47`):** `jb_keyeq` walks `q = 1..T.n` i.e. print `r = 2..n+1`, never a top junction; the two instruments **share 12 junctions** (T3× at r = 3, six rows; I4× at r = 3,4, six rows) with **EXACT agreement (6 GREEN / 6 RED)**; **16 roster F1 junctions — all the top ones, carrying 12 of the probe's 18 F1 REDs — lie outside JB-KEYEQ's range.** Recount: 6 + 6 = 12 shared ✔; 12 of 18 REDs outside range ⇒ 6 REDs inside ✔ consistent with the 6 RED shared. **The quoted “12 GREEN / 18 RED of 30” is the PROBE's own figure and is exact against its committed output; the note says so.**

**DERIVATION:** W-2 §3.4(3) byte law + TH-BASE, consumed (proof at L1552–1553).

**RESOLUTION TRACE:** statement lines 1423–1428; proof line 1552; matrix row 2 at 296 (shard 1); the coverage correction 685–687 (shard 1 `.47`).

XREF: `GRTW2_PROOF_2026-08-08.md:TH-BASE` — count **8** · `(C-coll)` — **27** · `3.4` — **35** (§-anchor, upper bound).

**TEETH:** `jb_keyeq` — byte census, **25 rows, IND**, with a **signed vacuity disclosure**: 3 of the 25 are VACUOUS (`QO:x3-3/Q3`, `QO:x4+2x2+2/Q2`, `QO:x4-2/Q2` have `T.n = 0`, so the census loop `range(1, T.n+1)` walks nothing and the TH-BASE guard is never exercised).

---
### EFF.GRTJB.91  [scope record]  (JB-DEV clause (iii) — the perimeter, per layer)

**CANONICAL STATEMENT:** verbatim, lines 1430–1455 — the clause head, the `[r1, G-9]` restatement and the `[r3, F-4]` three-layer split with its `[r4, F-3]` correction.
**FORM:** bold clause label + two nested bracketed riders.

> “**(iii) [coefficient correspondence, three layers].** **[r1, G-9 —
> quantifier restated to the perimeter the proofs need.]** This clause is
> asserted ONLY on the SHARED-KEY PERIMETER of §1: levels q with
> Φ_j^har = φ_{j+1}^cls byte-for-byte for all j < q, i.e. q ≤ qcap :=
> min(n, shared_upto + 1) — the runner's own `qcap_of(T, G)` quantifier. Off
> that perimeter the print frame is computed with keys that differ from
> Φ_0..Φ_{q−1}, and (VAL) is then FALSE, not merely unproved (J-A grades JA-VAL
> "PROVED unconditionally ON THE SHARED-KEY PERIMETER"). r0 inherited the
> theorem's blanket "level q ≥ 0" here; the machine evidence always quantified
> the narrower statement. **[r3, F-4 — ONE PERIMETER IS NOT ENOUGH FOR THREE
> LAYERS. The sentence above is correct for (VAL) and (GRID), which are JA-VAL /
> JA-GRID at level q. It is ONE LEVEL SHORT for (RES), which is JA-RES at read
> level m := q+1 … THE FENCE, PER LAYER (§0M rows 3/4/5): (VAL)
> and (GRID) on `P<q` = the SHARED-KEY PERIMETER 0 ≤ q ≤ qcap; **(RES) on the
> BYTE-EQUAL CHAIN THROUGH q (`P≤q`)**, which is strictly stronger ~~and excludes
> exactly the top level q = qcap …~~ **[r4, F-3 — corrected: the exclusion at q = qcap bites only
> when shared_upto < n (5 of the 16 roster towers: T3A/T3C/T3D/T3E/I4C); on the
> other 11 the two fences coincide over the whole level range … The fence itself is
> unchanged and the movement is still toward MORE conditionality where it bites
> at all.]** No machine leg is affected — the runner keys (RES)
> nowhere.]** For the common digit list (A_i):”

**CONDITIONALITY:** **CORRECTED FROM SHARD 3 BY CERTIFIER ANNEX E-4.** The clause “(VAL) is then FALSE, not merely unproved” is withdrawn. E-4 (L3267–3272):

> “Every live
> sentence saying that JB-DEV(iii)(VAL) or JB-VTX(a) is “FALSE, not merely
> unproved” off the shared-key perimeter is corrected to “**NOT SUPPLIED by this
> note outside the stated perimeter**.” Byte inequality of representatives removes
> the J-A theorem instance cited by the proof, but does not by itself imply
> inequality of the induced values on every polynomial.”

and E-4's corrected scope display names this clause first: “**JB-DEV(iii)(VAL) and (GRID) are asserted on `P<q` only; outside `P<q` this note makes no claim about their truth.**” E-4's consumer sweep item 2 names “§2(iii)” explicitly as a site where the phrase is re-read. **SUPERSESSION KIND: `counter re-reading`** — an unsupported negation withdrawn; **“No perimeter is widened and no on-perimeter proof moves.”**

**E-4's own ground, quoted (the f = 1 instance):** “Its development at every monic key has the sole digit A₀ = 1; normalized valuations give `w_q(A₀) = w_q(1) = 0 = v_{q+1}(1) = v_{q+1}(A₀)`, and both point sets are the singleton {(0,0)}, fixed by Σ_q. Thus (VAL) and the pointwise shear hold for this instance independently of the bytes of all positive-level keys.”

**DERIVATION:** Per layer, by instantiating each supplier theorem at its OWN read level (see `.83`).

**RESOLUTION TRACE:** statement lines 1430–1455; the perimeter definitions 1309–1334 (`.82`); correction sites 968–978 (r4/F-3, shard 1 `.60`), 3267–3312 (E-4).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-VAL` — **7** · `JA-GRID` — **11** · `JA-RES` — **20**.

**TEETH:** (VAL) **IND** over `0 ≤ q ≤ qcap`; (GRID) carry half **IND**, grid half **NONE**; (RES) **NONE** — “the runner keys (RES) nowhere”.

---
### EFF.GRTJB.92  [TABLE]  (JB-DEV clause (iii) — the three-layer display)

**CANONICAL STATEMENT:** verbatim, lines 1457–1469 — the fixed-width `(VAL)/(GRID)/(RES)` display with its `[r3, F-4]` rider.
**FORM:** display.

>     (VAL)  w_q(A_i) = v_{q+1}(A_i) for every i           [JA-VAL, consumed]
>     (GRID) the on-line attained abscissas lie on the print's T-side grid
>            s + j·e_q, and the plain carry = the side-lattice crossing
>            indicator                                  [JA-GRID/W2-L0, consumed]
>     (RES)  at read level m := q+1 ≥ 2 the print residual coefficients obey
>            the per-slot character-gauge law c_i = z_{m−1}^{−i·A_{m−1}}·C_i
>            against the harness packed digits C_i — unconditional at m = 2,
>            per-digit proviso at m ≥ 3            [JA-RES, consumed with
>                                                   JA-BOX-1/BOX-2 verbatim]
>            **[r3, F-4] — this layer alone is asserted on the BYTE-EQUAL CHAIN
>            THROUGH q (`P≤q`, §1), i.e. J-A's perimeter at its own read level
>            m = q+1; NOT on the shared-key perimeter `P<q` the two layers above
>            it use. (RES) is also the ONE layer with no machine leg (§0M row 5).**

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| layer | statement | source | fence | evidence |
|---|---|---|---|---|
| **(VAL)** | `w_q(A_i) = v_{q+1}(A_i)` for every `i` | JA-VAL, consumed | `P<q` | **IND** — `G.vgen(q+1,A) == T.wlev(q,A)`, cross-engine, `0 ≤ q ≤ qcap` |
| **(GRID)** | the on-line attained abscissas lie on the print's T-side grid `s + j·e_q`, and the plain carry = the side-lattice crossing indicator | JA-GRID / W2-L0, consumed | `P<q` **AND** JA-GRID(a)'s `[JA-r1]` `u ≥ 0` proviso | carry half **IND** (`jb_eps` keys JA-GRID(c)); **grid half NONE** |
| **(RES)** | at read level `m := q+1 ≥ 2` the print residual coefficients obey `c_i = z_{m−1}^{−i·A_{m−1}}·C_i` against the harness packed digits `C_i` | JA-RES, consumed with JA-BOX-1/BOX-2 verbatim | **`P≤q`** (r3/F-4) **+** JA-RES's own fence: free at `m = 2`, per-digit proviso at `m ≥ 3` (= (VD-(m−1)) at every on-line digit, r4/F-1) | **NONE — no family keys (RES) anywhere** |

**CONDITIONALITY:** Per row above. **The three layers have three different perimeters and three different evidence classes — that split IS the r3 correction, and it is why one “clause (iii)” cannot be graded as one object.**

**DERIVATION:** Each layer is a consumption; the proof line is “(iii) consumption as displayed” (L1553).

**RESOLUTION TRACE:** statement lines 1457–1469; proof line 1553; matrix rows 3, 4, 5 at 297–299 (shard 1 `.20`); the fences at `.11`, `.14`; the r4/F-1 (c)-cell completion 950–958 (shard 1 `.58`).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-L0` — **5**. `GRTJA_PROOF_2026-08-08.md:JA-BOX-1` — **8** · `JA-BOX-2` — **7**.

**TEETH:** as tabulated. **(RES) is one of the note's four frontier cells.**

---
### EFF.GRTJB.93  [supplier-finding]  ★ the (VD-m) reading fence

**CANONICAL STATEMENT:** verbatim, lines 1471–1495.
**FORM:** bold-headed bracketed block.

> “**[r1, F1 — the reading fence that r0 lacked, and that §5 got wrong.]**
> (RES)'s "unconditional at m = 2" is a statement about JA-RES, the PER-SLOT
> character-gauge law on residual coefficients. It does **NOT** transfer to the
> EVALUATED dictionary (VD-m) of J-A §3.4 (the identity
> z_m^{τ_m(A)}·R_m^cls(A)(z_m) = ε_m(β)·R_m v(A) between assembled read
> values). The per-slot law implies (VD-m) only through COROLLARY JA-VDIND,
> whose hypothesis is ABSOLUTE triviality of the slot character on the attained
> abscissas (z_{m−1}^{i·A_{m−1}} = 1 for every attained i; sufficient:
> A_{m−1} = 0, i.e. e_{m−2} = 1, or ord(z_{m−1}) | A_{m−1} plus the abscissa
> condition — single-slot support alone is NOT sufficient). At m = 2 that is
> z_1^{i·A_1} = 1 with A_1 = ℓ₀g₀γ₁, ~~which FAILS on towers with e₀ ≥ 2 and a
> nontrivial z₁ — and the sealed runner exhibits ten such in-roster failures
> (§7.1, §7.4)~~ **[r2, G2-4 — the struck clause asserted a failure SET and the
> note's own roster refutes it (T3E has e₀ = 2 with a nontrivial z₁ and scores
> 6/6). What is actually available here is ONE implication, in one direction:
> e₀ = 1 ⇒ A_1 = 0 ⇒ z_1^{i·A_1} = 1 at every abscissa ⇒ (VD-2) holds (J-A's own
> displayed sufficient condition, consumed). Its contrapositive is all the
> geography this note may claim: an m = 2 failure REQUIRES e₀ ≥ 2, but e₀ ≥ 2
> does NOT predict failure, and no condition in this note separates the failing
> from the scoring e₀ ≥ 2 towers. The sealed runner exhibits ten m = 2 in-roster
> failures (§7.1, §7.4) — the DATA, not a characterisation]**. Every
> (VD-m)-consuming statement in this note is fenced accordingly; **[r2,
> hygiene]** nothing (VD-m)-DEPENDENT above m = 1 is unconditional (this
> sentence is about (VD-m) only — LEMMA JB-EPS is unconditional at every
> m ≥ 1, as its own grade line says).”

**SUPERSESSION KIND:** `replacement` (r1/F1: a false perimeter replaced) + `counter re-reading` (r2/G2-4: a mechanism claim struck and NOT replaced).

**CONDITIONALITY:** **INBOUND CORRECTION E-1 lands on the “(R-coll)” label** wherever it appears downstream of this fence (`.127`, `.136`): “Wherever this note's text says ‘(R-coll)’, read the root-inclusive form of GRTJA at HEAD (≥ 5d95805).” E-1 explicitly certifies **this note's operative fence was already correct** (“root triviality a HYPOTHESIS at every m ≥ 2 — PE2's own adjudication: uncontaminated”).

**DERIVATION:** The distinction is J-A's own: JA-RES is a per-slot law on residual coefficients; (VD-m) is an identity between **assembled read values**; the implication runs only through JA-VDIND's absolute-triviality hypothesis. The note also records what is **NOT** sufficient: “single-slot support alone is NOT sufficient”.

**RESOLUTION TRACE:** statement lines 1471–1495; the disposition 638–659 (shard 1 `.44`); the mechanism strike 792–803 (shard 1 `.51`); the consuming theorem 2186–2203 (`.47`); the census 2494–2546 (shard 3); correction site 3125–3133 (E-1).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-VDIND` — **21** · `(VD-m)` — **10** · `(R-coll)` — **7** · `JA-RES` — **20**.

**TEETH:** **executable regression that disconfirmed the author** — the note's own sealed runner machine-evaluates (VD-2) FALSE on 10 of 13 roster boundary rows, and PE2 re-derived the split from the committed JSON alone without calling `vd_eval`. Disposition: **accepted-with-decorrelation-supplied**.

---
### EFF.GRTJB.94  [hypothesis]  ★ CHAIN HOME (body site) — the `u ≥ 0` proviso

**CANONICAL STATEMENT:** verbatim, lines 1497–1537 — the `[r1, G-5]` naming, the `[r2, G2-5]` retraction, and the `[r5, F-3]` narrowing.
**FORM:** bold-headed bracketed block with two nested riders.

> “**[r1, G-5 — the (GRID) layer carries an inherited PROVISO.]** JA-GRID(a) is
> graded in J-A with the `[JA-r1]` repair proviso u := (V − s·h)/e ≥ 0 (the
> bare V ∈ ℤ_{≥0} quantifier was FALSE at small V); that proviso is an inline
> J-A repair, not one of JA-BOX-1..5, so JB-BOX-2's blanket "rides J-A's boxes
> verbatim" did not carry it in r0. It is now named in JB-BOX-2 ~~with its
> discharge: at every consumption site here the argument V is a level-m weight
> of a nonzero polynomial in the tower's own window, so V ≥ e_{r−1}f_{r−1}
> v_r(φ_{r−1}) — J-A's own hypothesis for u ≥ 0 — and the runner's `s_geo`
> leg recomputes s from the geometry with no ℓ at all.~~ **[r2, G2-5 — THE
> DISCHARGE IS RETRACTED. The struck text asserted an implication it never
> proved …, and the implication is not plausible as
> stated: this note's own quantifiers are "f ∈ O[x] nonzero" (§2) and
> "deg f < deg Φ_m" (§4/§5), both of which admit UNITS, whose level-m weight is
> 0, while e_{r−1}f_{r−1}v_r(φ_{r−1}) is positive at r ≥ 2. J-A grounds that
> bound in the PRINT's own hypothesis at the site where `construct` is invoked;
> J-B has no such site hypothesis and supplied no substitute. The `s_geo` remark
> was a red herring: `s_geo` recomputes s geometrically (ℓ-free), which
> certifies the s-VALUE, not the sign of u. STATUS: the proviso is CARRIED, NOT
> DISCHARGED … What a real discharge requires:
> derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) (or directly V ≥ s_m^wt(V)·h_{m−1},
> which is what u ≥ 0 says) for EVERY V in the quantified window — units
> included … Two facts frame the residual: at V = 0 one
> has s^wt = 0 and u = 0 ≥ 0, so no counterexample to the proviso is exhibited
> by units; ~~and J-A's own counterexample lives at small positive V
> ((e,h) = (2,3), V = 1 ⇒ u = −1), which nothing in this note excludes from the
> level-m weight lattice. So the proviso may well hold at every site — this note
> does not show it.~~ **[r5, F-3 — the struck frame went STALE at r4 and is
> corrected: the r4-defined level-(q+1) weight lattice 𝒲_{q+1} (§5, forward
> pointer — the object is DEFINED there) DOES exclude J-A's (e,h) = (2,3),
> V = 1 instance (by parity), and u ≥ 0 is PROVED on ALL of 𝒲_{q+1} — four
> lines from the displayed description, §5's [r5, F-3] display,
> machine-confirmed. WHAT THIS DELIVERS AT THIS LAYER: the quantifier here is
> f nonzero with NO degree bound, and JA-GRID(a) is applied at V = w_{q+1}(f);
> membership V ∈ 𝒲_{q+1} holds by definition exactly at deg f < deg Φ_{q+1} —
> THERE THE PROVISO NOW HOLDS; off that sub-window membership is not
> established by anything this note consumes, and the proviso is CARRIED as
> that membership hypothesis (§0M rows 4/12, column (b)).]**]** (JB-EPS is unaffected:
> it cites JA-GRID(c), which carries no proviso.)”

**CHAIN (rule 25) — the note's deepest, four layers.** **CHAIN HOME is §0M column (b)** (shard 1 `.14`), which carries all four members and the TERMINAL reading. This unit is the **BODY SITE** of members 1–3. `CHAIN-MEMBER: .14 positions 1–3.`
1. **r1/G-5** — the proviso named in JB-BOX-2 *with a discharge argument*.
2. **r2/G2-5** — the discharge **RETRACTED** (“it was an assertion, not a derivation”).
3. **r5/F-3** — **NARROWED**: `u ≥ 0` PROVED on all of `𝒲_m`; residue = lattice MEMBERSHIP at the unbounded-degree quantifier.
4. **r6/m-1 → r7/F-1** (shard 1 `.75`, `.77`) — **TERMINAL**: membership is SUFFICIENT; the converse is EQUIVALENT at `m = 1`, of unknown strictness at `m ≥ 2`.

**SUPERSESSION KIND:** `replacement` (r2) + `scope-pin` (r5).

**CONDITIONALITY:** **Exactly two consumers: matrix row 4 (this layer) and row 12 (JB-VTX(d4)).** Both remain frontier members after the narrowing. **JB-EPS is explicitly unaffected** — it cites JA-GRID(c), which carries no proviso — a separation the note states here and repeats at `.126` and `.132`.

**DERIVATION:** The retraction's refutation is displayed (units have level-m weight 0 while the claimed bound is positive at `r ≥ 2`; `s_geo` certifies the s-value, not the sign of `u`). The genuine equivalence `u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}` is immediate from `u := (V − s_m^wt(V)·h_{m−1})/e_{m−1}` with `e_{m−1} > 0`. **The positive discharge is `.121`'s four-line theorem.**

**RESOLUTION TRACE:** statement lines 1497–1537; **proof lines 2046–2062** (§5's four-line theorem, `.121`) and **2085–2111** (the SCOPE block, `.122`); correction sites 680–684, 804–819, 1053–1073, 1179–1190, 1218–1258 (all shard 1); the box site 2340–2373 (`.136`).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-GRID` — **11** · `JA-BOX-1` — **8** (range endpoints JA-BOX-1..5 verified individually in shard 1 §3.1).

**TEETH:** **`NONE` on both consumers' grid halves.** The lattice theorem's corroboration is verifier-owned (PE6 598,500/0, PE7 reproducing exactly, PE8 on a wider box 340/0). Disposition: **disclosed non-repair** for the rows; **accepted-with-decorrelation-supplied** for the theorem.

---
### EFF.GRTJB.95  [fence]  (JB-DEV clause (iv))

**CANONICAL STATEMENT:** verbatim, lines 1539–1547.
**FORM:** bold clause label + paragraph.

> “**(iv) [cross-key fence, displayed not claimed].** For a DIFFERENT strict
> representative φ′ of the same type, blanket digit equality and blanket
> operator equality are FALSE (J-A §4(i): v_{r+1}(φ − φ′) = e_r·v_r(φ) —
> the standard MacLane representative-dependence); the lawful transport
> across representatives is W-2 clause 2's covariance (slot-ratio characters)
> and clause 3's chamber re-instantiation, never a byte identity. This is
> the JuncForge parity-wall lesson honored: J-B is stated against the
> semantic development objects at a NAMED representative; no SideReads/
> TreeModel transcription is consumed.”

**CONDITIONALITY:** **PERIMETER-FREE — a displayed fence, cited, with nothing to key** (matrix row 6). **Note the asymmetry E-4 turns on:** clause (iv) says a BLANKET cross-representative identity is FALSE; E-4 says that does NOT license “every off-perimeter instance fails”. E-4 quotes exactly this: “JB-DEV(iv)'s representative-dependence warning rules out a blanket cross-representative identity, but **supplies no derivation that every off-perimeter instance fails**.” **So (iv) stands unchanged and E-4's correction at `.91`/`.100` is consistent with it.**

**DERIVATION:** Cited (J-A §4(i)'s MacLane representative-dependence identity).

**RESOLUTION TRACE:** statement lines 1539–1547; proof line 1553 (“(iv) cited”); matrix row 6 at 300 (shard 1); the E-4 consistency 3282–3286 (shard 3); the standing box 2421–2426 (`.138`).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C3` — **22**. `GRTJB_PROOF_2026-08-08.md:JuncForge` — count **2** (note-local reference to a corpus lesson; no external designation claimed).

**TEETH:** **NONE** — “a displayed fence: nothing to key”. Disposition: **signed non-applicability**.

---
### EFF.GRTJB.96  [changes-record]  (JB-DEV — the proof and the two struck grade lines)

**CANONICAL STATEMENT:** verbatim, lines 1549–1560.
**FORM:** `*Proof.*` marker + two struck grade lines.

> “*Proof.* (i) Uniqueness of quotient and remainder in division by a monic
> polynomial over any commutative ring: the print's development (tex
> `phiradic` genre) and the harness development are the same recursion; the
> representative legitimacy is W-2 clause 1 consumption. (ii) W-2 §3.4(3)
> byte law + TH-BASE, consumed. (iii) consumption as displayed. (iv) cited.
> ∎ Grade: ~~PROVED at attempt grade with the displayed consumptions; no
> clause here upgrades W-2/J-A.~~ ~~**[r2, G2-1 — the perimeter carried onto this
> grade line, where r1 left it in the body only: …]**~~”

**CONDITIONALITY:** **Both grade lines are STRUCK and superseded by surface 2** (`.97`). The PROOF itself is live and is the derivation of `.89`–`.95`. **The r2 line is struck not because it was wrong but because r3 replaced the generation mechanism** — its “only defect of substance was (iii)(RES)'s perimeter”, per surface 2's own preamble.

**DERIVATION:** This unit IS the proof. Four one-line discharges, each naming its ground; the substantive content is in the clauses.

**RESOLUTION TRACE:** statement lines 1549–1560; the superseding surface 1562–1584 (`.97`).

**TEETH:** carried by the clauses.

---
### EFF.GRTJB.97  [TABLE]  ★ SURFACE 2 of 14 — the §2 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 1562–1584.
**FORM:** bold-headed bracketed block + fixed-width per-clause display.

> “**[r3, STEP 2 — SURFACE 2 of 14, REGENERATED FROM §0M rows 1–6 (the struck
> r2 line above is superseded; its only defect of substance was (iii)(RES)'s
> perimeter). ∎ GRADE: PROVED at attempt grade with the displayed consumptions;
> no clause here upgrades W-2/J-A. PER CLAUSE:**
>
>     (i)         every level q ≥ 0; at the W2-C1 admissible representative
>                 φ_{q+1} := Φ_q^har.                              [row 1]
>     (ii)        on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`, §1); TH-BASE gives
>                 q = 1 always.                                    [row 2]
>     (iii)(VAL)  on the SHARED-KEY PERIMETER (`P<q`), 0 ≤ q ≤ qcap — off it
>                 (VAL) is FALSE, not merely unproved.             [row 3]
>     (iii)(GRID) on `P<q` AND on JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso,
>                 CARRIED AND UNDISCHARGED (r2, G2-5); narrowed r5/F-3:
>                 PROVED at deg f < deg Φ_{q+1} (V ∈ 𝒲_{q+1}, §5), membership
>                 residue at the unbounded-degree quantifier.      [row 4]
>     (iii)(RES)  on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — one level deeper
>                 than r2's fence, F-4; the exclusion bites on 5/16 roster
>                 towers only ((a2), r4/F-3) — plus JA-RES's own fence
>                 (unconditional at m = q+1 = 2, per-digit proviso at m ≥ 3 =
>                 (VD-(m−1)) at every on-line digit, JA-BOX-2; r4/F-1). NOT
>                 the evaluated dictionary (VD-m) at level m.      [row 5]
>     (iv)        a displayed fence, cited; no level condition.    [row 6]
>
> **]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| clause | fence | generating matrix row |
|---|---|---|
| **(i)** | every level `q ≥ 0`; at the W2-C1 admissible representative `φ_{q+1} := Φ_q^har` | row 1 |
| **(ii)** | on `P≤q`; TH-BASE gives `q = 1` always | row 2 |
| **(iii)(VAL)** | on `P<q`, `0 ≤ q ≤ qcap` — ~~off it (VAL) is FALSE, not merely unproved~~ **→ E-4: NOT SUPPLIED outside the stated perimeter** | row 3 |
| **(iii)(GRID)** | `P<q` **AND** JA-GRID(a)'s `u ≥ 0` proviso; narrowed r5/F-3 to PROVED at `deg f < deg Φ_{q+1}`, membership residue off it | row 4 |
| **(iii)(RES)** | `P≤q` (r3/F-4; exclusion bites on 5/16, r4/F-3) **+** JA-RES's own fence (free at `m = 2`; per-digit proviso at `m ≥ 3` = (VD-(m−1)) at every on-line digit, r4/F-1). **NOT (VD-m) at level m** | row 5 |
| **(iv)** | a displayed fence, cited; no level condition | row 6 |

**CONDITIONALITY:** **This surface is a REGENERATION of §0M rows 1–6, not an independent authority** (FREEZE PREDICATE 2). **E-4 re-reads the (VAL) row's negation clause**; E-4's consumer sweep item 2 names “§2 ∎ Grade” explicitly. Nothing else moves.

**ARITHMETIC AUDIT (rule 22):** clauses listed = 6 (i, ii, iii(VAL), iii(GRID), iii(RES), iv); generating rows cited = 1, 2, 3, 4, 5, 6 = **6, contiguous, no gaps, no repeats** ✔. Cross-check against §0M rows 1–6 (shard 1 `.20`): every fence in the surface appears as a matrix cell, and every non-blank cell in rows 1–6 appears in the surface. **The surface's bidirectional claim (“Every fence below is a cell of that table; the table carries no fence this cap omits”, applied per surface) VERIFIES for rows 1–6.**

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 1562–1584; generating rows 295–300 (shard 1 `.20`); correction site 3301–3304 (E-4).

**TEETH:** per row; see `.92`.

---
### EFF.GRTJB.98  [instrument-record]  (JB-DEV — the machine bracket, restated at r3/F-2)

**CANONICAL STATEMENT:** verbatim, lines 1585–1609 — the struck r0 bracket and the `[r3, F-2]` replacement.
**FORM:** struck display + bold-headed bracketed replacement.

> “~~[Machine: JB-DEV — the development recomputed
> by this runner's OWN schoolbook division (fresh leg, decorrelated from the
> shared PolyO.dev used by both engines) and compared against both engines'
> digit lists at every shared level; JB-KEYEQ — byte-equality census tied to
> the W-2 read-data byte law; teeth MJB-DEV.]~~
>
> **[r3, F-2 — MACHINE BRACKET RESTATED to exactly what the code establishes;
> the struck bracket's "both engines" is WITHDRAWN. [Machine, classified as in
> §0M column (f): JB-DEV — TWO legs carry information. (1) ONE genuine second
> implementation (IND, 893 samples): the development recomputed by this runner's
> OWN schoolbook division `fresh_dev` against the engine's `PolyO.dev` on the
> same key. (2) ONE genuine CROSS-ENGINE tie (IND): the (VAL) digit-weight
> identity `G.vgen(q+1, A) == T.wlev(q, A)`, the print engine's valuation
> recursion against the harness's, at every digit and every level 0 ≤ q ≤ qcap.
> A THIRD leg carries NO information and is disclosed as such: `G.P.dev(f,
> G.phi[q+1])` is the SAME `PolyO.dev` bound to the SAME ring object … it is guarded by
> `tuple(G.phi[q+1]) == key`, so its arguments are byte-equal, and it is reached
> only after a `continue` on `dvF != dvI` has already forced agreement. The
> violation `'fresh dev != print dev'` is therefore UNREACHABLE: SAME-COMPUTATION
> (PE3 F-2 = PE1/G-1's disease at its third site). There is ONE engine comparison
> in this family, not two. JB-KEYEQ — byte-equality census tied to the W-2
> read-data byte law (25 rows; 3 VACUOUS, T.n = 0, r1/G-3); teeth MJB-DEV
> (garbled key, 3/3 caught).]]**”

**SUPERSESSION KIND:** `counter re-reading` — an advertised second engine re-read as the same computation.

**CONDITIONALITY:** **The correction DOWNGRADES the note's own advertised evidence** and is the third site of one disease (PE1/G-1 at the tree family, PE2/G2-2 inside the repair instrument, PE3/F-2 here). **This compiler independently confirmed the construction the note cites:** `grt_weld_probe.py` L456–459 is `def gmn_from_tower(T, mut=False)` building `levels = [(T.e[i], T.h[i], list(T.psi[i])) for i in range(T.NR)]` and returning `GmnLeg(T.R, T.d0, T.Phi[0], levels, …)` — **the ring argument is `T.R`, the tower's own ring, exactly as ⟨n1⟩ states.**

**DERIVATION:** Code reading, displayed.

**RESOLUTION TRACE:** statement lines 1585–1609; the cell note ⟨n1⟩ 326–337 (shard 1 `.21`); the disposition 898–905 (shard 1 `.55` STEP 4); the §7.1 row 2480 (shard 3).

**TEETH:** two IND legs + one **SAME** leg with an **UNREACHABLE** violation + a **signed vacuity disclosure** on JB-KEYEQ (3 of 25 rows) + planted mutant **MJB-DEV** (garbled key, 3/3 caught, fired).

---
### EFF.GRTJB.99  [lemma]  LEMMA JB-AFF

**CANONICAL STATEMENT:** verbatim, lines 1615–1621.
**FORM:** bold-headed display with its proof inline.

> “**LEMMA JB-AFF (two lines, displayed).** Let Σ : (i, u) ↦ (i, a·u + b·i + c)
> with a > 0, b, c ∈ ℚ. Then Σ maps lower convex hulls to lower convex hulls
> and vertices to vertices, bijectively, preserving abscissas. *Proof.* Σ is
> affine and abscissa-preserving, so it maps segments to segments and
> preserves "lies strictly below the chord": a·u + b·i + c < a·u′ + b·i + c
> ⟺ u < u′ at equal i, since a > 0. Hulls, faces, and strict-vertex
> conditions are defined by these two relations. ∎”

**CONDITIONALITY:** **UNCONDITIONAL — no perimeter, no proviso, no [RMG] clause, no (VD-m)** (matrix row 7; §7.2's own row says exactly this). Two hypotheses do real work: `a > 0` (the order-preservation) and abscissa-preservation. **Note what the lemma does NOT claim, and what E-3 later needs it not to claim: it says nothing about ambient lattice data or unimodularity** — only hulls, vertices, abscissas.

**DERIVATION:** Self-contained and displayed in full above: affineness + abscissa-preservation ⇒ segments to segments; `a > 0` ⇒ the strict-below-chord relation is preserved at equal `i`; hulls, faces and strict-vertex conditions are defined by those two relations. **Two lines, no consumption.**

**RESOLUTION TRACE:** statement lines 1615–1621 (statement and proof are one span); matrix row 7 at 301 (shard 1); applied at 1645–1650 (`.102`) and 1682–1694 (`.105`).

**TEETH:** **NONE as a lemma — “its content is exercised inside rows 9/10”** (matrix row 7's own (f) cell), i.e. inside `jb_vtx`'s fresh-hull/vertex-bijection and per-side slope/length legs. Disposition: **signed non-applicability**, with the exercise site named.

---
### EFF.GRTJB.100  [scope record]  THEOREM JB-VTX — head and perimeter

**CANONICAL STATEMENT:** verbatim, lines 1623–1634.
**FORM:** bold-headed opener with a struck quantifier and its `[r1, G-9]` replacement.

> “**THEOREM JB-VTX.** Level q with read (e_q, h_q) defined ~~(0 ≤ q ≤ n)~~
> **[r1, G-9 — PERIMETER RESTATED AT THE THEOREM: 0 ≤ q ≤ qcap, where
> qcap := min(n, shared_upto + 1) is the SHARED-KEY perimeter of §1 (keys
> shared strictly below q), the runner's own `qcap_of(T,G)`. This is not
> cosmetic: clause (a) consumes JA-VAL for the digits AND for the key
> (v_{q+1}(φ_{q+1}) = w_qΦ_q), and J-A grades JA-VAL "PROVED unconditionally
> on the shared-key perimeter"; off it the print frame U(f) is computed with
> keys ≠ Φ_0..Φ_{q−1} and clause (a) is FALSE, not merely unproved. r0's grade
> line named only W-2 clause 1, which does not carry this]**,
> f ∈ O[x] nonzero, frames as §1, all statements at the representative
> φ_{q+1} := Φ_q^har (legitimate by W-2 clause 1 on its perimeter; on
> byte-equal chains this is the classifier's own key, JB-DEV(ii)).”

**SUPERSESSION KIND:** `scope-pin`.

**CONDITIONALITY:** **CORRECTED FROM SHARD 3 BY E-4** — “clause (a) is FALSE, not merely unproved” is withdrawn. E-4's corrected scope display names this head directly:

> “**JB-VTX(a), and consequently (b)/(c)/(d1)/(d2)/(d4) at the theorem's common
> head, are asserted on `P<q` only; outside it this note makes no claim.**
> The separately deeper fences remain unchanged: JB-DEV(iii)(RES) and
> JB-VTX(d3) continue to require `P≤q`.”

and its consumer sweep item 2 lists “the JB-VTX theorem head” among the sites where the phrase is re-read. **SUPERSESSION KIND for E-4: `counter re-reading`.** Additionally **`.104`'s (d3) is EXCEPTED from this head's `P<q`** by r6/F-1 and rides `P≤q` instead.

**DERIVATION:** The perimeter is what the consumed theorem needs: clause (a) consumes JA-VAL for the digits **and for the key** (`v_{q+1}(φ_{q+1}) = w_qΦ_q`), and J-A grades JA-VAL on the shared-key perimeter.

**RESOLUTION TRACE:** statement lines 1623–1634; the perimeter definition 1323–1334 (`.82`); the (d3) exception 1665–1675 (`.104`); correction sites 697–700 (shard 1 `.46`), 3267–3312 (E-4).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-VAL` — **7** · `shared-key perimeter` — **5**. `GRTW2_PROOF_2026-08-08.md:W2-C1` — **22**.

**TEETH:** the runner runs the shear/vertex/slope families over `0 ≤ q ≤ qcap_of(T,G)`; **off-perimeter counter 0 on the roster**.

---
### EFF.GRTJB.101  [lemma]  JB-VTX (a) — the shear is exact, pointwise

**CANONICAL STATEMENT:** verbatim, lines 1636–1643.
**FORM:** bold clause label + displayed computation.

> “**(a) [the shear is exact, pointwise].** H(f) = Σ_q(U(f)) with
> Σ_q(i, u) = (i, e_q·u + h_q·i): indeed e_q·u_i + h_q·i =
> e_q·v_{q+1}(A_i) + i·(e_q·v_{q+1}(φ_{q+1}) + h_q) = e_q·w_q(A_i) + i·γ_{q+1}
> by JA-VAL and the weight recursion γ_{q+1} = e_q·w_qΦ_q + h_q (JA-PIN
> clause 7). Moreover e_q·u_i + h_q·i = v_{q+2}(A_i·Φ_q^i) (propertiesv
> item 3 at a single digit): THE SHEARED FRAME IS THE PRINT'S OWN NEXT-LEVEL
> BOOKKEEPING — the harness ordinates are the v_{q+2}-values of the
> monomials, the print ordinates their v_{q+1}-values.”

**CONDITIONALITY:** `P<q` + W2-C1 (matrix row 8). **The second sentence is the one that consumes `propertiesv` item 3 and is a CITE-SCOPE row** (see the reading note below). **E-4 withdraws the head's negation gloss** (`.100`).

**DERIVATION:** Displayed arithmetic + two consumptions, both named inline: (1) JA-VAL gives `v_{q+1}(A_i) = w_q(A_i)`; (2) JA-PIN clause 7's weight recursion `γ_{q+1} = e_q·w_qΦ_q + h_q` converts the `i`-coefficient. The identification with `v_{q+2}(A_i·Φ_q^i)` is `propertiesv` item 3 at a single digit.

**READING NOTE (external, not an edit) — the CITE-SCOPE row for the whole shard.** `runs/qgen/Q7_output.log` classifies GRTJB's GMN print anchors as **CITE-SCOPE**, naming exactly these consumption sites: *“These are load-bearing in JB-VTX(a), (c), and (d1). The pasted note gives locations and conclusions but not the publication's hypotheses on the base field. Generality to F_q((t)) therefore cannot be certified from this slice.”* `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` **NS-11** resolves it:

- **Published scope of the cited source is ℚ_p-only, confirmed at the local print:** `docs/references/HigherNewton.tex` line 401, *“We fix a finite extension $K$ of $\Q_p$ as a base field …”*.
- **Local label identification:** `\label{propertiesv}` = `HigherNewton.tex` line 1028 = GMN **Proposition 2.7**; `\label{shape}` = line 1401 = GMN **Lemma 2.17**; `\label{phir}` = line 1257 = GMN **Theorem 2.11**.
- **Retarget for `propertiesv` item 3 — verdict COVERS-ALL-O (definitional):** **[GN15] §1.2** defines the augmented valuation by exactly that formula — *“$\mu'(g)= \mathrm{Min}_{0\le s}\{\mu(a_s\phi^s)+s\nu\}$, where $\sum a_s\phi^s$ is the canonical $\phi$-expansion of $g$. We denote $\mu'=[\mu;\phi,\nu]$.”* — “i.e. at general scope the statement is the **definition** of `v_r`, which is strictly stronger than citing it as a proposition.”
- **Retarget for `shape` items 1–2 (consumed at `.104`/(d1)) — COVERS-ALL-O:** **[GN15] Lemma 1.5 + Corollary 1.14**; equivalently **[FGMN] Lemma 2.2 + Prop 5.14 / Cor 5.15**, and **[AGNPRW] Lemma 4.2**.
- **Retarget for `rescoeff` / `t(i)` — COVERS-ALL-O:** **[AGNPRW] §2.2 definition (3)** + **[GN15] Theorem 1.9**.
- **The price, quoted:** *“the general-scope sources use MacLane/graded-algebra normalizations … rather than GMN's integer-rescaled `v_r = e_{r−1}H_{r−1}∘S_{r−1}`; the re-cite therefore carries a **normalization-shear obligation** — exactly the one `GENTOW2_PROOF_2026-08-09.md` already discharges for the FGMN side … Reuse that.”*

**The note's own text is compiled as written; the retarget is RECORDED, NOT APPLIED.** See shard 1 OPEN-CALL 2 for the standing decision this leaves open.

**RESOLUTION TRACE:** statement lines 1636–1643; proof line 1696 (“(a) displayed arithmetic + consumptions”); the frames 1375–1386 (`.86`); the literature declaration 565–576 (shard 1 `.39`); correction site 3267–3312 (E-4).

XREF: `docs/references/HigherNewton.tex:propertiesv` — grep-verified count **8**.
XREF: `GRTJA_PROOF_2026-08-08.md:JA-PIN` — **15** · `JA-VAL` — **7**.

**TEETH:** `jb_vtx`/`jb_shear_vtx` — **IND, 893 samples**: print ordinates (`G.vgen`/`G.vkey`) against harness ordinates (`T.wlev`/`T.gam`), i.e. **two engines, not two code paths of one**.

---
### EFF.GRTJB.102  [lemma]  JB-VTX (b) — vertex-for-vertex

**CANONICAL STATEMENT:** verbatim, lines 1645–1650.
**FORM:** bold clause label + paragraph.

> “**(b) [vertex-for-vertex].** By (a) and JB-AFF, the harness development
> polygon (lower hull of H(f)) equals Σ_q(N_{q+1}(f)) vertex-for-vertex,
> same abscissas; equivalently N_{q+1}(f) = Σ_q^{−1}(harness polygon). This
> is GD-2's displayed clause with the shear EXPLICIT. The unsheared
> identification (hull of {(i, w_q(A_i))} against N_{q+1}(f)) is FALSE in
> general — the T-F 7,472-violation genre; teeth family MJB-VTX.”

**CONDITIONALITY:** `P<q` + W2-C1, via (a) (matrix row 9). **The “FALSE in general” here is NOT the claim E-4 withdraws** — E-4 targets only the off-perimeter negation about (VAL)/(a); this one is a MEASURED fact about the unsheared identification, backed by 7,472 counted violations (`.87`) and by the note's own teeth family. **The two negations must not be conflated at the merge.**

**DERIVATION:** (a) + LEMMA JB-AFF, which applies because `Σ_q(i,u) = (i, e_q·u + h_q·i)` has `a = e_q > 0`, `b = h_q`, `c = 0` and is abscissa-preserving.

**RESOLUTION TRACE:** statement lines 1645–1650; proof line 1696 (“(b) JB-AFF”); the lemma 1615–1621 (`.99`); the measurement 1388–1396 (`.87`).

XREF: `lean/notes/openmath/GD23_phaseB_attempt.md:GD-2` — **7**.
XREF: `lean/notes/openmath/O1thr_phaseB_verifybrief_rev3.md:7,472` — count **2** (figure pin, re-verified at the source by this compiler).

**TEETH:** `jb_vtx` — **fresh lower hulls of BOTH frames + the vertex bijection (IND, 893)**; plus planted mutant **MJB-VTX** (unsheared frame, 3/3 caught, fired).

---
### EFF.GRTJB.103  [lemma]  ★ JB-VTX (c) — slope/length translation (the E-3 target)

**CANONICAL STATEMENT:** verbatim, lines 1652–1663.
**FORM:** bold clause label + paragraph.

> “**(c) [slope/length translation].** A print side of slope σ over abscissas
> [i₀, i₁] maps to a sheared side of slope e_q·σ + h_q over the same
> [i₀, i₁]; lengths (abscissa runs) are preserved. In particular:
> the REALIZED side σ = −h_q/e_q maps to slope 0 — the sheared frame is the
> frame in which the read side is HORIZONTAL, at height
> min_i(e_q·w_q(A_i) + i·γ_{q+1}) = w_{q+1}(f) — exactly the eq-(12)
> presentation of the level-(q+1) read; a side of print slope −h/e in lowest
> terms has its lattice data preserved: degree d = (abscissa run)/e is the
> same integer in both frames (the print's d(S) = the harness grid count).
> The print principal part N^−_{q+1} (σ < 0, tex 1377) corresponds to
> sheared slopes < h_q; the weld's type-quantification consumes only the
> principal sides (JA-PIN clause 2's Hensel/L1 dispatch, displayed there).”

**CONDITIONALITY — ★ THE ONE DISPLAYED MATHEMATICAL STATEMENT OF §§1–6 THAT A LATER ANNEX WITHDRAWS IN PART.** CERTIFIER ANNEX **E-3** (shard 3, L3199–3228) supersedes the “lattice data preserved” sentence:

> “**E-3 (JB-VTX(c): abscissa run, not ambient lattice data).** The sentence in
> §3(c) saying that the shear “preserves lattice data” is WITHDRAWN. The shear
>
>     Σ_q(i,u) = (i, e_q·u + h_q·i)
>
> is not unimodular when e_q > 1. For an edge with difference vector
> (Δi, Δu), its image has difference vector
>
>     (Δi, e_q·Δu + h_q·Δi),
>
> so the abscissa run Δi is preserved and the slope transforms by
>
>     σ′ = e_q·σ + h_q,
>
> but the ambient-lattice primitive step and lattice length need not be
> preserved. For example, at (e_q,h_q) = (2,1), the edge from (0,1) to (2,0)
> maps to the horizontal edge from (0,2) to (2,2), whose ambient lattice
> contains the additional point (1,2).”

**THE CORRECTED DISPLAY, verbatim from E-3:**

> “**CORRECTED DISPLAY OF JB-VTX(c).** A print side of slope σ over
> [i₀,i₁] maps to a sheared side of slope e_q·σ+h_q over the same
> [i₀,i₁]; hence its abscissa run Δi := i₁−i₀ is preserved. If the source
> slope is −h/e in lowest terms, its PRINT-side degree remains the
> source-defined integer d := Δi/e and is recoverable from the preserved run
> together with the source slope data. This does NOT say that d is the ambient
> lattice length of the sheared edge. On the realized side, identifying d with
> a count of e_q-spaced attained-grid intervals is instead a consequence of
> JB-VTX(d4), and therefore carries row 12's full scope: the `P<q` and W2-C1
> fences, together with the narrowed lattice-membership/u ≥ 0 residue and its
> NO-MACHINE-LEG disclosure.”

**SUPERSESSION KIND:** `replacement` — a false extension removed and the display re-issued. **TARGETS (rule 24):** `.103` (this unit), `.107` (the §3 ∎ GRADE surface), `.20` row 10 (“re-read as ‘JB-VTX(c), slope/abscissa-run’”), `.32` (the grade cap's JB-VTX bullet), `s3of3` §7.2's JB-VTX row and §7.3's W-3 polygon bullet.

**★ THE LOAD-BEARING CONSEQUENCE, and the merge must carry it:** every use of an attained-slot or harness-grid COUNT is **routed to JB-VTX(d4) = matrix row 12** — which is a **frontier cell** (`NONE` evidence + the membership residue). So E-3 does not merely trim a claim; **it moves a downstream consumption onto the note's weakest row.** E-3's own consumer sweep says so: “Every use of an attained-slot or harness-grid count is routed to JB-VTX(d4), §0M row 12. Its existing membership residue and NO-LEG status therefore remain visible; the four-member frontier is unchanged.”

**What E-3 explicitly does NOT disturb (quoted):** “The §3 proof and the `hull_sides` machine leg survive unchanged: they establish slope transformation and equality of endpoint abscissas/runs, not unimodularity.” And: “No hull, vertex, slope, abscissa-run, JB-TREE or JB-CREAD identity moves. Only the false ambient-lattice extension is removed.”

**Orchestrator verification of E-3, quoted from the transcription record (L3316–3320):** “E-3's shear algebra re-derived (image difference vector (Δi, e_qΔu + h_qΔi), slope law σ′ = e_qσ + h_q, the (e_q,h_q) = (2,1) witness maps (0,1)–(2,0) to the horizontal (0,2)–(2,2) containing (1,2): abscissa run preserved, ambient lattice data not)”.

**DERIVATION (as corrected):** displayed arithmetic. From `Σ_q(i,u) = (i, e_q u + h_q i)`, an edge `(Δi, Δu)` maps to `(Δi, e_q Δu + h_q Δi)`: the abscissa run is preserved and the slope transforms as stated. The realized side `σ = −h_q/e_q` maps to slope `0`, at height `min_i(e_q w_q(A_i) + i γ_{q+1}) = w_{q+1}(f)`. **The withdrawn step was the inference from “run preserved” to “ambient lattice data preserved”, which fails at `e_q > 1` because `Σ_q` is not unimodular.**

**RESOLUTION TRACE:** statement lines 1652–1663; proof line 1696 (“(c)(d) displayed arithmetic + the cited print lemmas”); **correction site 3199–3245 (E-3)**; the routed consumer 1665–1680 (`.104`, clause (d4)).

XREF: `docs/references/HigherNewton.tex:defresidual` — **1**; the `N^−` principal-part pin (tex 1377) is a LINE PIN verified present. `GRTJA_PROOF_2026-08-08.md:JA-PIN` — **15**.

**TEETH:** `jb_vtx` — `hull_sides` per-side slope/length law (**IND, 893**). **The leg survives E-3 unchanged because it only ever measured what E-3 keeps** — a case where the instrument was scope-correct and the prose over-reached. Disposition: **executable regression, scope-matched after correction**; the correction itself is an **AUDIT — decorrelated-model audit** (a sol certification run found it).

---
### EFF.GRTJB.104  [lemma]  JB-VTX (d) — the four min/read ties

**CANONICAL STATEMENT:** verbatim, lines 1665–1680.
**FORM:** bold clause label + paragraph with a nested `[r6, F-1]` rider.

> “**(d) [min/read ties].** min ordinate of U(f) = v_{q+1}(f) (print Lemma
> `shape` item 1, tex ~1395); min ordinate of H(f) = w_{q+1}(f) = v_{q+2}(f)
> (the weight recursion + JA-VAL one level up) **[r6, F-1 — "one level up" made
> binding: this third tie (d3) is JA-VAL AT LEVEL q+1, so by J-A's
> level-indexed perimeter it holds on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`),
> NOT on the bare shared-key perimeter `P<q` the theorem head states — one
> level deeper, exactly as (RES) (r3/F-4); the exclusion bites at q = qcap on
> the 5 shared_upto < n towers. The representative-pin rescue (arguing the
> frame's own pin φ_{q+1} := Φ_q^har discharges J-A's j = q requirement) is
> NOT taken: it is not derived anywhere in this note — the same refusal
> recorded at (RES). §0M row 11 (a2)]**; the attained abscissas on
> the realized side are the read grid s(λ) + j·e_q, and the level-(q+1)
> read is assembled exactly from the on-line digits at those slots (S0.2
> consumed; JA-GRID). So the polygon identity carries the READ data — the
> harness read of f and the print's side data (s_{q+1}(f), attained set,
> side degree) are the same integers under Σ_q.”

**`[TABLE]` — the four ties, split as the note splits them (matrix rows 11 and 12):**

| tie | statement | fence | machine leg |
|---|---|---|---|
| **(d1)** | min ordinate of `U(f) = v_{q+1}(f)` (print Lemma `shape` item 1, tex ~1395) | `P<q` + W2-C1 | **IND**, `minU == G.vgen(q+1,f)` under `q ≤ shared_upto` — **an instrument cut, not the statement's hypothesis** (r6, F-1) |
| **(d2)** | min ordinate of `H(f) = w_{q+1}(f)` | `P<q` + W2-C1 | **IND**, `minH == T.wlev(q+1,f)` (harness-internal) |
| **(d3)** | `w_{q+1}(f) = v_{q+2}(f)` — JA-VAL **at level q+1** | **`P≤q`** + W2-C1 (r6, F-1); bites at `q = qcap` on T3A/T3C/T3D/T3E/I4C | **IND**, `minH == G.vgen(q+2,f)`; the runner's `q ≤ shared_upto` gate **IS** this fence, so the leg covers the full re-fenced range |
| **(d4)** | attained abscissas on the realized side = the read grid `s(λ) + j·e_q`, and the level-(q+1) read is assembled from the on-line digits at those slots | `P<q` + W2-C1 **AND** JA-GRID(a)'s `u ≥ 0` proviso (narrowed r5/F-3) | **NONE — no leg in any family of any instrument** |

**SUPERSESSION KIND:** `scope-pin` (the r6 re-fence of (d3) alone).

**CONDITIONALITY:** **(d4) is the note's most heavily fenced sub-clause and one of its four frontier cells**: it rides the open membership residue AND has zero machine evidence, and the note discloses the coincidence explicitly. **E-3 routes every attained-slot/harness-grid COUNT here** (`.103`), which strengthens (d4)'s downstream load without strengthening its evidence. **The representative-pin rescue is refused, binding on r3/F-4's precedent.**

**DERIVATION:** (d1) is print Lemma `shape` item 1 (`min_i u_i = v_r(f)`). (d2)–(d3) are the weight recursion plus JA-VAL one level up. (d4) is S0.2's read assembly plus JA-GRID. Proof line: “(c)(d) displayed arithmetic + the cited print lemmas (Lemma `shape` item 1 is also re-verified by machine through the second development route — see runner family JB-SHEAR)”.

**RESOLUTION TRACE:** statement lines 1665–1680; proof lines 1696–1699; matrix rows 11, 12 at 305–306 (shard 1); the cell note ⟨n3⟩ 347–368 (shard 1 `.23`); the r6 disposition 1127–1163 (shard 1 `.73`); the `u ≥ 0` chain home 218–250 (shard 1 `.14`).

XREF: `docs/references/HigherNewton.tex:shape` — grep-verified count **13** (NS-11 retarget: **[GN15] Lemma 1.5 + Corollary 1.14**, COVERS-ALL-O — see `.101`).
XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md:S0.2` — **5**. `GRTJA_PROOF_2026-08-08.md:JA-GRID` — **11**.

**TEETH:** three keyed, **(d4) unkeyed**. Quoted coverage-hole sentence (from ⟨n3⟩): “Clause (d)'s FOURTH tie … **has no leg in any family**”. **PROOF-ONLY row (rule 16).** The (d3) gate was byte-verified at HEAD by this compiler (`grt_jb_checks.py` L283).

---
### EFF.GRTJB.105  [lemma]  JB-VTX (e) — the window clause, subject corrected

**CANONICAL STATEMENT:** verbatim, lines 1682–1694.
**FORM:** bold clause label + struck sentence + `[r1, G-4]` replacement.

> “**(e) [window clause].** ~~Restricted to the junction window i ≤ e_q·g_q
> (the lift comparison window), one-sidedness holds in both frames
> simultaneously (Σ_q preserves sides)~~ **[r1, G-4 — SUBJECT CORRECTED. As
> literally read with the theorem's quantified f the struck sentence is FALSE
> (a general f's polygon restricted to i ≤ e_q g_q is not one-sided). The
> clause's subject is the KEY, and it reads: APPLIED AT f = Φ_{q+1}^har (the
> next-level lift, whose window development is the W2-C1a object), restricted
> to the junction window i ≤ e_q·g_q, one-sidedness holds in both frames
> simultaneously (Σ_q preserves sides, LEMMA JB-AFF)]**: this is W2-C1a's
> polygon leg —
> v-correct, one-sided, support {0, e_q g_q} ∪ attained grid slots — i.e.
> the "window polygon" of the blueprint IS N_{q+1}(Φ_{q+1}^har) restricted
> to its single side, vertex-for-vertex under Σ_q.”

**SUPERSESSION KIND:** `replacement` — a clause whose stated subject made it FALSE, re-issued with the true subject.

**CONDITIONALITY:** **The subject is the KEY `Φ_{q+1}^har`, NOT the theorem's quantified `f`** (matrix row 13: “subject is the KEY, not the quantified f (r1, G-4)”). Fence: `YES*` via (a) at `f = Φ_{q+1}^har`, plus **W2-C1a**. **Row 13 is a no-leg cell ADJUDICATED OUT of the frontier** (r4/F-2): no-leg but no OPEN proviso — its conditionality is consumption at grade.

**DERIVATION:** W2-C1a consumed at `f = Φ_{q+1}^har` (proof line 1699), plus `Σ_q` preserving sides by LEMMA JB-AFF.

**RESOLUTION TRACE:** statement lines 1682–1694; proof line 1699; the disposition 678–679 (shard 1 `.47` item G-4); matrix row 13 at 307 (shard 1); the frontier exclusion 959–967 (shard 1 `.59`).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C1a` — **10**.

**TEETH:** **NONE (none claimed)** — matrix row 13's own (f) cell. Disposition: **signed non-applicability**, adjudicated out of the frontier with the reason displayed.

---
### EFF.GRTJB.106  [changes-record]  (JB-VTX — the proof and the struck grade line)

**CANONICAL STATEMENT:** verbatim, lines 1696–1712.
**FORM:** `*Proof.*` marker + a struck grade line with a nested `[r2, G2-1]` re-grep rider.

> “*Proof.* (a) displayed arithmetic + consumptions; (b) JB-AFF; (c)(d)
> displayed arithmetic + the cited print lemmas (Lemma `shape` item 1 is
> also re-verified by machine through the second development route — see
> runner family JB-SHEAR); (e) W2-C1a consumed at f = Φ_{q+1}^har (r1, G-4).
> ~~∎ Grade: PROVED at attempt grade **[r1, G-9] on the shared-key perimeter
> 0 ≤ q ≤ qcap …** … **[r2, G2-1
> re-grep — one fence this line was missing: clause (d)'s read-grid/attained-
> abscissa content consumes JA-GRID, so it also rides JA-GRID(a)'s UNDISCHARGED
> `[JA-r1]` u ≥ 0 proviso (r2, G2-5; carried in JB-BOX-2). Clauses (a)/(b)/(c)
> and the min ties themselves do not.]**~~”

**CONDITIONALITY:** The grade line is **STRUCK and superseded by surface 3** (`.107`). The PROOF is live. **The r2 re-grep rider inside it is the first statement that (d4) alone rides the proviso** — a separation surface 3 then carries.

**DERIVATION:** This unit IS the proof: five one-line discharges. Note the machine cross-check embedded in it — Lemma `shape` item 1 is “re-verified by machine through the second development route”, i.e. `v_{q+1}(f)` computed BOTH as `min u_i` and by the vgen recursion.

**RESOLUTION TRACE:** statement lines 1696–1712; the superseding surface 1714–1747 (`.107`).

**TEETH:** carried by the clauses; the `shape` item 1 double-computation is `jb_shear_vtx`'s (d1) leg.

---
### EFF.GRTJB.107  [TABLE]  ★ SURFACE 3 of 14 — the §3 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 1714–1747.
**FORM:** bold-headed bracketed block + fixed-width per-clause display.

> “**[r3, STEP 2 — SURFACE 3 of 14, REGENERATED FROM §0M rows 7–13. ∎ GRADE:
> PROVED at attempt grade on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap,
> stated at the theorem), every statement at the W2-C1 admissible representative
> φ_{q+1} := Φ_q^har — W-2 clause 1's perimeter and conditionality ride, and on
> byte-equal chains no W-2 input is needed beyond TH-BASE. PER CLAUSE:**
>
>     LEMMA JB-AFF  unconditional, two lines; its content is exercised inside
>                   (b)/(c)'s machine legs.                        [row 7]
>     (a)(b)(c)     `P<q` + W2-C1 only; off `P<q` clause (a)'s JA-VAL input is
>                   unavailable and (a) is FALSE, not merely unproved.
>                                                             [rows 8–10]
>     (d1)(d2)      two of the THREE min ties: `P<q` + W2-C1; the runner
>                   restricts the print-side tie (d1) further to
>                   q ≤ `shared_upto(T,G)` — an instrument cut (r6, F-1).
>                                                         [row 11 (a1)]
>     (d3)          w_{q+1}(f) = v_{q+2}(f) = JA-VAL at level q+1: the
>                   BYTE-EQUAL CHAIN THROUGH q (`P≤q`) + W2-C1 — one level
>                   deeper than the r3 fence, the r3/F-4 genre; bites at
>                   q = qcap on the 5 shared_upto < n towers; the runner's
>                   own q ≤ `shared_upto(T,G)` gate on (d3) IS this fence
>                   (r6, F-1).                            [row 11 (a2)]
>     (d4)          attained abscissas = the read grid s(λ) + j·e_q, and the
>                   level-(q+1) read assembled from the on-line digits at those
>                   slots: `P<q` + W2-C1, **AND JA-GRID(a)'s UNDISCHARGED
>                   `[JA-r1]` u ≥ 0 proviso** (r2, G2-5; JB-BOX-2; narrowed
>                   r5/F-3: PROVED at deg f < deg Φ_{q+1}, membership residue
>                   off it — §5), **AND it has
>                   NO MACHINE LEG** (r3, F-3).                   [row 12]
>     (e)           at f = Φ_{q+1}^har, the W2-C1a window object — NOT at the
>                   theorem's quantified f (r1, G-4); no machine leg claimed.
>                                                                 [row 13]
>
> **The runner runs the shear/vertex/slope families over 0 ≤ q ≤ `qcap_of(T,G)`
> and the off-perimeter counter is 0 on the roster, so nothing was silently
> scored outside the fence.]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| clause | fence | generating row |
|---|---|---|
| **JB-AFF** | unconditional, two lines; content exercised inside (b)/(c)'s legs | row 7 |
| **(a)(b)(c)** | `P<q` + W2-C1 only — ~~off `P<q` (a) is FALSE, not merely unproved~~ **→ E-4: NOT SUPPLIED outside the stated perimeter**; **(c) → E-3: “slope/length” reads “slope/abscissa-run”** | rows 8–10 |
| **(d1)(d2)** | `P<q` + W2-C1; the runner's `q ≤ shared_upto` on (d1) is **an instrument cut** | row 11 (a1) |
| **(d3)** | **`P≤q`** + W2-C1 (r6/F-1); bites at `q = qcap` on 5 towers; the runner's gate **IS** this fence | row 11 (a2) |
| **(d4)** | `P<q` + W2-C1 **AND** the `u ≥ 0` proviso (narrowed r5/F-3) **AND NO MACHINE LEG** | row 12 |
| **(e)** | at `f = Φ_{q+1}^har`, the W2-C1a window object — NOT at the quantified `f`; no leg claimed | row 13 |

**CONDITIONALITY:** **A REGENERATION of §0M rows 7–13** (FREEZE PREDICATE 2). **TWO shard-3 corrections land on it:** E-4 (the negation clause in the (a)(b)(c) row; its consumer sweep item 2 names “§3 ∎ Grade”) and E-3 (“The grade cap, **§3 ∎ Grade surface**, §7.2's JB-VTX row and §7.3's W-3 polygon bullet read every occurrence of ‘slope/length’ as ‘slope/abscissa-run’”).

**ARITHMETIC AUDIT (rule 22):** clause groups listed = 6; generating rows cited = 7, 8–10, 11(a1), 11(a2), 12, 13 → **rows 7,8,9,10,11,12,13 = 7 rows, contiguous, no gaps, no repeats** ✔ matches “§0M rows 7–13”. Row 11 appears twice, once per sub-column, which is exactly the r6 SPLIT ✔. **Cross-check against §0M rows 7–13: every non-blank cell appears in the surface, and every fence in the surface is a cell. VERIFIES.**

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 1714–1747; generating rows 301–307 (shard 1 `.20`); correction sites 3199–3245 (E-3), 3267–3312 (E-4); the r6 re-fence 1127–1163 (shard 1 `.73`).

**TEETH:** per row; **(d4) is PROOF-ONLY**; row 13 no-leg by design.

---
### EFF.GRTJB.108  [instrument-record]  (JB-VTX — the machine bracket, restated at r3/F-3)

**CANONICAL STATEMENT:** verbatim, lines 1748–1778 — the struck r0 bracket and the `[r3, F-3]` replacement with its `[r7, m-3]` and `[r5, F-3]` riders.
**FORM:** struck display + bold-headed bracketed replacement.

> “~~[Machine: JB-VTX — fresh lower hulls of both
> frames, vertex bijection, per-side slope/length translation; JB-SHEAR —
> pointwise shear + all four min/read ties …]~~
>
> **[r3, F-3 — MACHINE BRACKET RESTATED; "all four min/read ties" is WITHDRAWN.
> [Machine, classified as in §0M column (f): JB-VTX — fresh lower hulls of BOTH
> frames, vertex bijection, per-side slope/length translation (IND, 893).
> JB-SHEAR — the pointwise shear plus **THREE** of clause (d)'s four ties, not
> four: the code's assertions are `minH == T.wlev(q+1, f)` (d2) and, under
> q ≤ shared_upto, `minU == G.vgen(q+1, f)` (d1) and `minH == G.vgen(q+2, f)`
> (d3) ((d3) additionally under the code's second conjunct `q+1 <= G.RANK`, a
> vgen-domain guard, identically true on the loop domain since
> RANK = n+1 ≥ qcap+1 — verified redundant [r7, PE7 m-3, commit aa9b603];
> ⟨n3⟩) **[r6, F-1 — for (d3) that gate coincides with its own statement fence
> `P≤q` (§0M row 11 (a2)); for (d1) it remains an instrument cut]** — so
> v_{q+1}(f) IS computed both as min u_i and by the vgen recursion
> through the φ_q-development (two different developments, one value; Lemma
> `shape` item 1 machine-keyed). **THE FOURTH TIE (d4) HAS NO LEG IN ANY FAMILY
> OF ANY INSTRUMENT:** `jb_dev` keys only the (VAL) weight tie, `jb_line` keys
> line == wlev == vgen on reduced cells, `jb_cread` evaluates (VD-m), and
> `jb_eps` keys JA-GRID's **carry** clause (c) — the other half of the (GRID)
> layer, and the half that carries no proviso. **Disclosed coincidence:** (d4) is
> also the only sub-clause of JB-VTX riding the undischarged u ≥ 0 proviso
> **[r5, F-3 — narrowed to the membership residue, §0M column (b) and §5]**, so
> the clause with the open inherited hypothesis is the clause with zero machine
> evidence (§0M row 12; the same disclosure genre as r1/G-3's three VACUOUS
> JB-KEYEQ rows). teeth MJB-VTX on designated rows (unsheared frame, 3/3
> caught).]]**”

**SUPERSESSION KIND:** `counter re-reading` (four ties recounted to three keyed) + `inventory completion` (r7/m-3's second conjunct disclosed).

**CONDITIONALITY:** **The exhaustiveness of the no-leg claim is what makes it strong**: the note enumerates ALL FOUR families and shows none keys (d4). **E-3 does not touch this bracket** — “the `hull_sides` machine leg survive[s] unchanged”.

**PIN VERIFICATION (rule 23) — re-verified at HEAD by this compiler, 3/3 EXACT:** `verification/openmath/grt_jb_checks.py` **L283** = `                if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):` — **byte-exact**; `grt_weld_probe.py` **L211** = `        self.RANK = len(levels)`; `grt_weld_probe.py` **L456–459** = `gmn_from_tower` building `levels` over `range(T.NR)`. **So `RANK = T.NR` and the redundancy derivation is source-true.** (Source defect 5 of shard 1 stands: the note gives the two line pins without naming their file, which is `grt_weld_probe.py`.)

**DERIVATION:** Code enumeration.

**RESOLUTION TRACE:** statement lines 1748–1778; the cell note ⟨n3⟩ 347–368 (shard 1 `.23`); the disposition 905–908 (shard 1 `.55`); the m-3 sweep 1259–1271 (shard 1 `.79`); the §7.1 JB-SHEAR row 2482 (shard 3).

**TEETH:** three IND tie legs + a **PROOF-ONLY** fourth + planted mutant **MJB-VTX** (fired) + a **signed vacuity disclosure** cross-referenced to JB-KEYEQ's three vacuous rows.

---
### EFF.GRTJB.109  [hypothesis]  §4 setting

**CANONICAL STATEMENT:** verbatim, lines 1784–1788.
**FORM:** inline paragraph.

> “Setting: reduction level m (1 ≤ m ≤ n), [RMG] T-scope(m) (its termination
> fence), g_m = 1, Ĉ_m := Φ_{m+1} − Φ_m^{e_m} (WELL-DEF g_m = 1 form,
> consumed); f ∈ O[x] nonzero, deg f < deg Φ_m. The [RMG] S2.2 objects
> (cells, (ID-(i+1)), the E1-priority tree, L-NORM splits, L-EXACT, L-CANON,
> L-LINE) are consumed as ACCEPTED displays.”

**CONDITIONALITY:** **Three standing scope fences enter here and ride every §4 clause:** `T-scope(m)` ([RMG]'s termination fence, with the d₀ ≥ 2 flat corners staying FENCED), `g_m = 1` (for the Ĉ_m instance), and `deg f < deg Φ_m`. **The degree bound is the hypothesis whose scope r5/F-2 later had to enforce** (`.113`) and whose absence off the sub-window is the `u ≥ 0` membership residue (`.94`, `.122`).

**DERIVATION:** Declaration of setting.

**RESOLUTION TRACE:** statement lines 1784–1788; the boxes 2427–2433 (`.139`); the degree-bound scope enforcement 1832–1851 (`.113`).

XREF: `RMENGINE_2026-08-08.md:T-scope` — **42** · `S2.2` — **16** · `(ID-(i+1))` — **3** · `L-NORM` — **28** · `L-EXACT` — **11** · `L-CANON` — **6** · `L-LINE` — **23** · `L-CELL` — **11**.
XREF: `ITERLAWN_PROOF_2026-08-08.md:WELL-DEF` — **32**.

**TEETH:** the scope is a filter on the roster: “I4C has NO eligible (g_m = 1 ∧ T-scope) reduction level, so its tree/cread rows are honestly absent, the §4 scope fence in action” (§7.1, shard 3).

---
### EFF.GRTJB.110  [lemma]  THEOREM JB-TREE — head

**CANONICAL STATEMENT:** verbatim, lines 1790–1791.
**FORM:** bold-headed opener.

> “**THEOREM JB-TREE.** Under the J-A dictionary (and W-2 clause 1 for the
> representative reading; clause 3's chamber off the byte perimeter):”

**CONDITIONALITY:** **E-2 re-reads the clause-3 (W2-C3) half** at the supplier's proved-to-first-twist (38/44) / measured-above (6/44) split; the 2026-08-08 annex confirms GRTW2 ACCEPTED at 2/2 **at that honest split** — “Acceptance of W-2 accepts the honest box; it does not turn its measured-above region into a theorem” (the E3 adjudication's finding 3, shard 3).

**DERIVATION:** Head; the clauses are `.111`–`.115`.

**RESOLUTION TRACE:** statement lines 1790–1791; correction sites 3135–3142 (E-2), 3247–3261 (the E3 adjudication's RESOLVED-ALREADY item, shard 3).

XREF: `GRTW2_PROOF_2026-08-08.md:W2-C3` — **22** · `W2-OPEN-2` — **60**.

**TEETH:** per clause.

---
### EFF.GRTJB.111  [lemma]  JB-TREE (i) — the tree computes the classifier's division

**CANONICAL STATEMENT:** verbatim, lines 1793–1801.
**FORM:** bold clause label + paragraph.

> “**(i) [the tree computes the classifier's division].** The E1-priority
> tree on the initial cells of f·Ĉ_m terminates (T-TERM, consumed) with
> Σ R-leaves = R and Σ exit cofactors = Q for THE canonical division
> f·Ĉ_m = R + Q·Φ_m (L-EXACT + L-CANON, consumed) — and by JB-DEV(i) at
> level m this IS the classifier's division step at the admissible
> representative (its own key on byte-equal chains): R = the 0-th digit and
> Q = the once-divided cofactor of the print's φ_{m+1}-adic development
> algorithm applied to f·Ĉ_m. One tree = one classifier division step,
> executed inside the expansion arithmetic.”

**CONDITIONALITY:** **PERIMETER-FREE** (matrix row 15) — “it consumes JB-DEV(i), which holds at every q”. Fences: W2-C1 representative reading, W2-C3's chamber off the byte perimeter, and [RMG]'s T-TERM + L-EXACT + L-CANON on T-scope(m), g_m = 1. **L-CANON's hypothesis `deg Ĉ_m < deg Φ_m` is one of the two clauses r3/F-5 restored to §5's recital** (`.119`) — before r3 the note cited L-CANON without displaying the hypothesis that makes the division canonical.

**DERIVATION:** Consumption chain as displayed + JB-DEV(i) (proof line 1905).

**RESOLUTION TRACE:** statement lines 1793–1801; proof line 1905; the restored L-CANON hypothesis 2015–2023 (`.119`); matrix row 15 at 309 (shard 1).

XREF: `RMENGINE_2026-08-08.md:T-TERM` — **11** · `L-EXACT` — **11** · `L-CANON` — **6**.

**TEETH:** `jb_tree` — a FRESH from-note tree walker vs `fresh_divmod` (**IND**), **plus** the post-seal walker's leg A (84 print-keyed walks, genuinely decorrelated), **plus a SAME sub-leg** (⟨n2⟩: the byteeq-gated print-key re-execution), **and 8 chamber walks NONE** (unreached by both instruments). Disposition: **accepted-with-decorrelation-supplied** on base rows; **disclosed non-repair** for the chambers.

---
### EFF.GRTJB.112  [definition]  the period `P_i` (r3/F-7)

**CANONICAL STATEMENT:** verbatim, lines 1803–1819 (through “same sense.]**”).
**FORM:** bold clause label + bracketed definition with a fixed-width display.

> “**(ii) [each edge = one classifier division step].** **[r3, F-7 — NOTATION,
> DEFINED HERE AT FIRST USE (it was used undefined in r0–r2, and it is
> load-bearing for the digit-list claim below).**
>
>     P_i := e_i · g_i     — the level-(i+1) PERIOD: the abscissa at which the
>                            key power Φ_i^{P_i} sits in the Φ_i-adic
>                            development of Φ_{i+1}. Verbatim from [RMG] S0.1
>                            ("P_l := e_lg_l (the level-(l+1) period)"), whose
>                            scope is declared "local to this note" there and
>                            which is therefore added to this note's [RMG]
>                            consumption list in the header.
>
> **The value is what the proof of (ii) turns on: every correction abscissa
> e_i·k with k < g_i satisfies e_i·k < e_i·g_i = P_i, so the digit list below is
> supported below the key power and the Φ_i-adic development reads off
> uniquely. §7.4's PW-ID and PW-WALK rows use the same symbol (and P_l) in this
> same sense.]**”

**SUPERSESSION KIND:** `inventory completion` — a symbol consumed uncited, defined and its source added to the consumption list.

**CONDITIONALITY:** **[RMG] S0.1 scopes `P_l` “local to this note”** — so consuming it required adding S0.1 to GRTJB's consumption list, which r3/F-7 did. **`P_i` is also the object the `𝒲_m` description's index bound `0 ≤ j_l ≤ P_l − 1` uses** (`.120`) and the object the r7 m = 1 equivalence's `j := s ≤ e₀−1 ≤ P₀−1` step uses (shard 1 `.77`).

**DERIVATION:** Definition + the one-line consequence displayed: `e_i·k < e_i·g_i = P_i` for `k < g_i`, so the digit list is supported below the key power and the `Φ_i`-adic development reads off uniquely.

**RESOLUTION TRACE:** statement lines 1803–1819; the disposition 911–912 (shard 1 `.55` STEP 4); the consumption-list addition 577–581 (shard 1 `.40`); consumed at 1819–1829 (`.33`), 2031 (`.40`), and §7.4's PW-ID/PW-WALK rows (shard 3).

XREF: `RMENGINE_2026-08-08.md:S0.1` — grep-verified count **12**.

**TEETH:** exercised by `jb_id` (the digit list) and by the post-seal walker's PW-WALK row (“every R-leaf reduced (`j_l ≤ P_l − 1`)”, 84 samples GREEN).

---
### EFF.GRTJB.113  [lemma]  JB-TREE (ii) — each edge = one division step, with the L-CELL gloss corrected

**CANONICAL STATEMENT:** verbatim, lines 1819–1851 — the (ID-(i+1)) reading, the edge typing, and the struck L-CELL gloss with its `[r5, F-2]` replacement.
**FORM:** paragraph + struck sentence + bracketed replacement.

> “The identity
> (ID-(i+1)): Φ_i^{P_i} = Φ_{i+1} − Σ_{k<g_i} C_k^{(i)}·Φ_i^{e_ik} IS the
> statement that the φ_{i+1}-adic development of the KEY φ_{i+2} = Φ_{i+1}
> has digit list {C_k^{(i)} at abscissa e_i·k (k < g_i), 1 at abscissa P_i}
> (uniqueness of division; the C_k^{(i)} are reduced, REALIZE R1). So every
> in-tree edge applies the classifier's own key-expansion relation exactly
> once: a promotion edge carries one key power up one level (the division
> algorithm's carry), a Φ_m-exit emits one quotient summand (a division
> step's quotient write), and a correction edge substitutes the key's lower
> development digits (the remainder write), L-NORM-split into its L/π-junk/
> Φ₀Y-junk children. The tree is the classifier's division arithmetic made
> cell-local; ~~the blueprint's "each cell = a set of expansion slots" is
> L-CELL: every node is a sum of reduced cells = multiadic expansion slots
> (iterated JB-DEV at levels m−1, …, 0).~~ **[r5, F-2 — the struck gloss is
> FALSE at every exit-bound node, and its citation was used beyond L-CELL's
> stated hypothesis: L-CELL(i) decomposes 0 ≠ x with deg x < deg Φ_m ONLY,
> while a node taking a Φ_m-exit has j_{m−1} ≥ P_{m−1} (S2.2, "Φ_m-exit
> (i = m−1)"), hence deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m by the S2.1 degree
> telescope — and a sum of reduced cells has deg < deg Φ_m (S2.1), so such a
> node is not a sum of reduced cells at all. THE TRUE STATEMENT: the
> blueprint's "each cell = a set of expansion slots" is L-CELL(i) ON ITS OWN
> HYPOTHESIS — every node OF DEGREE < deg Φ_m is a finite sum of distinct
> reduced cells = multiadic expansion slots (iterated JB-DEV at levels
> m−1, …, 0); an exit-bound node decomposes below the top level instead
> ([RMG] S2.2's structural remark: its sub-cell b·∏_{l≤m−2}Φ_l^{j_l} is
> REDUCED AT LEVEL m−1); and the R-LEAVES — where the division's output
> lives, and the only reducedness `jb_tree` keys — are the expansion slots in
> the blueprint's sense. The same L-CELL(i) hypothesis scope reads onto the
> r4/F-4 bracket's min-line parenthetical below (its bound line ≤ w_m is
> supplied where the reduced decomposition exists, deg < deg Φ_m). Nothing
> downstream consumed the struck gloss: (ii)'s operative content — the edge
> typing and JB-ID — was re-derived SOUND (PE5), and clauses (i)/(iii)/(iv)
> consume L-EXACT/L-CANON/JA-VAL, not this sentence.]**”

**SUPERSESSION KIND:** `scope-pin` — a citation used beyond its stated hypothesis, re-scoped to that hypothesis.

**CONDITIONALITY:** **PERIMETER-FREE** (matrix rows 14, 16) — uniqueness of division at the print's own keys. **The corrected gloss is a genuine mathematical narrowing**, and the note verifies nothing downstream consumed the false form. **The same hypothesis scope reads onto the r4/F-4 min-line parenthetical** (`.114`) — one correction, two sites.

**DERIVATION:** (a) The (ID-(i+1)) reading: “the right side of (ID-(i+1)) has every `C_k^{(i)}Φ_i^{e_ik}` of degree < deg Φ_{i+1} with the `C_k` reduced (REALIZE R1), so the digit list reads off; uniqueness of division” (proof lines 1906–1908). (b) The r5/F-2 refutation is displayed: an exit-bound node has `j_{m−1} ≥ P_{m−1}`, hence `deg ≥ P_{m−1}·deg Φ_{m−1} = deg Φ_m` by the S2.1 degree telescope, while a sum of reduced cells has `deg < deg Φ_m` — so it cannot be one.

**RESOLUTION TRACE:** statement lines 1819–1851; proof lines 1906–1908; the disposition 1080–1088 (shard 1 `.69`); matrix rows 14, 16 at 308, 310 (shard 1).

XREF: `RMENGINE_2026-08-08.md:(ID-(i+1))` — **3** · `L-CELL` — **11** · `L-NORM` — **28** · `S2.1` — **15** · `S2.2` — **16**.
**NEAR-MISS (rule 15) — `REALIZE R1`:** fixed-string `REALIZE R1` has count **0** in `ITERLAWN_PROOF_2026-08-08.md`; the parent designation `REALIZE` has count **17** and the law label `R1` has count **9**. The referent (REALIZE's law R1: reduced correction digits) is verified and is [ILN]† S4.1's; the note's compound spelling is note-local. **Disposition: NEAR-MISS, referent verified, carried descriptively.** Same for `REALIZE R3` (`R3` count **4**).

**TEETH:** `jb_id` — (ID-(i+1)) exact + key-dev digits + print-key grid/shear-constancy (**34 samples, IND**, “both engines”, with a genuinely print-side leg); `jb_tree` keys **R-leaf reducedness** — which is exactly the scoped statement the correction leaves standing.

---
### EFF.GRTJB.114  [lemma]  ★ JB-TREE (iii) — the polygon bookkeeping, RE-SCOPED at r4/F-4

**CANONICAL STATEMENT:** verbatim, lines 1853–1897 — the two displayed equalities, the struck per-edge `v_{m+1}` transfer, and the `[r4, F-4]` re-scope.
**FORM:** bold clause label + struck sentence + bracketed replacement.

> “**(iii) [the polygon bookkeeping = LED-Λ's line face, one citation].**
> On reduced cells, line(C) = w_m(C) ([RMG] L-LINE(iv)) = v_{m+1}(C)
> (JA-VAL): THE LEDGER'S LINE FUNCTIONAL IS THE CLASSIFIER'S MacLANE
> ORDINATE. ~~Hence LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the
> complete per-edge polygon bookkeeping of the division in classifier
> coordinates: promotions raise v_{m+1} by exactly the quantum q_{i+1} > 0,
> correction-main edges are v_{m+1}-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀
> (Y), exits pay w_mΦ_m~~ **[r4, F-4 — RE-SCOPED. The struck sentence
> transferred the per-edge line laws to v_{m+1} across EVERY tree edge, but its
> license is a REDUCED-CELL identity and NO internal tree node is reduced ([RMG]
> S2.2's own construction: a node with an outgoing edge has some j_i ≥ P_i);
> off the reduced cells [RMG] supplies only line(C) ≤ w_m(C) (L-CELL(i): w_m =
> min line over the reduced cells of the decomposition, plus L-MONO), never
> equality. THE CLAUSE AS RE-SCOPED, stated of the right functional:
> LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the complete per-edge
> polygon bookkeeping of the division AS EXACT LAWS OF THE LINE FUNCTIONAL, on
> every edge: promotions raise line by exactly the quantum q_{i+1} > 0,
> correction-main edges are line-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀ (Y),
> exits pay w_mΦ_m in line. AT THE R-LEAVES — the reduced cells, where the
> division's output R lives — and there ONLY, the ledger reads in classifier
> coordinates: line = w_m (L-LINE(iv)) = v_{m+1} (JA-VAL). That leaf reading is
> the only v_{m+1} statement this clause asserts, and it is exactly what
> `jb_line` keys (leaf line == wlev == vgen; no v_{m+1} statement is tested at
> any non-leaf — §0M row 17). DERIVABILITY OF THE INTERNAL-EDGE TRANSFER WAS
> CHECKED BEFORE RE-SCOPING: within this note's consumption list it is NOT
> derivable (L-LINE(iv) is reduced-only; LED-Λ's own face is "λ_E·J(C) = line(C)
> BY DEFINITION of the line" — a statement about line, not w_m). A candidate
> route OUTSIDE the list exists and is recorded as NOT TAKEN: the print's
> order-(m+1) valuation is multiplicative (HigherNewton's valuation proposition,
> tex ~1012 — NOT among this note's print anchors), which with JA-VAL and the
> per-atom values v_{m+1}(b) = E_m·w₀(b), v_{m+1}(Φ_l) = Γ_l would extend
> line = v_{m+1} to every cell; but the Φ_l atom value rests on the single-digit
> weight recursion, which degenerates where deg Φ_q = deg Φ_l (interior periods
> P_t = 1 — realized on this note's own roster, e.g. T3E's P_1 = 1) and there
> needs a two-digit-development case argument consuming WELL-DEF data one level
> down, and no instrument keys any internal-node v_{m+1} statement. Honesty over
> reach: the line law is what is cited, proved and measured; the leaf reading is
> what is claimed in classifier coordinates. Nothing downstream moves —
> JB-TREE(iv) and §5 consume w_m/v_{m+1} of the OUTPUT polynomials R and Q
> through JA-VAL directly, never a per-edge internal-cell ordinate.]**
> ([LED-Λ] S1 table, λ_E column; L-MONO = the
> division never descends below the polygon — the print's
> division-stability genre read through the dictionary). Where earlier
> units re-derived these per edge, J-B cites the ledger ONCE; LED-Λ is
> consumed at ATTEMPT grade and the tie's grade rides it.”

**CHAIN (rule 25):** r0's per-edge `v_{m+1}` transfer → **r4/F-4** re-scope (line-functional laws on every edge; `line = w_m = v_{m+1}` at R-leaves only) → **r5/F-1** removal of the one live leftover at surface 4 (`.117`). **TERMINAL = the r4 re-scope as cleaned by r5/F-1.**

**SUPERSESSION KIND:** `scope-pin`.

**CONDITIONALITY:** **`P<q` read at level m** (matrix row 17), since it consumes JA-VAL; **LED-Λ at ATTEMPT grade and the tie's grade rides it** — and LED-Λ's grade is **NOT** upgraded by the 2026-08-08 supplier annex, so this rider is live at HEAD. **The NOT-TAKEN route is a NON-IMPORT with a stated reason**, and the reason is concrete: the atom value degenerates at interior periods `P_t = 1`, **realized on this note's own roster at T3E**.

**DERIVATION:** Two displayed equalities on reduced cells (`line(C) = w_m(C)` by L-LINE(iv); `= v_{m+1}(C)` by JA-VAL) + the LED-Λ citation (proof line 1908). The re-scope's own derivation: no internal tree node is reduced (a node with an outgoing edge has some `j_i ≥ P_i`, [RMG] S2.2), and off reduced cells [RMG] gives only `line(C) ≤ w_m(C)` (L-CELL(i) + L-MONO), **never equality**.

**RESOLUTION TRACE:** statement lines 1853–1897; proof line 1908; the disposition 979–998 (shard 1 `.61`); the leftover removal 1074–1079 (shard 1 `.68`); matrix row 17 at 311 (shard 1).

XREF: `LEDGERLAMBDA_2026-08-08.md:LED-Λ(A1)` — **5** · `LED-Λ(B)` — count **1** · `λ_E` — **10** · `L-MONO` — **7** · `S1` — **15** (§-anchor; upper bound, referent pinned by `λ_E`).
XREF: `RMENGINE_2026-08-08.md:L-LINE` — **23** · `L-CELL` — **11** · `S3.2` — **3**.

**CITE-SCOPE NOTE:** tex ~1012 (the print's valuation-multiplicativity proposition) is **the one HigherNewton anchor GRTJB explicitly declines to consume**. It is therefore NOT in the NS-11 retarget set and NOT a CITE-SCOPE liability — it is a NON-IMPORT. Recorded in §4.

**TEETH:** `jb_line` — λ_E quanta per edge recomputed **FRESH** on `line(·)` + **leaf** `line == wlev == vgen` (194 samples, **IND**; the vgen half gated on `qcap ≥ m`). **No internal-node `v_{m+1}` statement is keyed — or, as of r4, claimed.** Disposition: **executable regression, scope-matched to the corrected claim** — the instrument keyed leaves all along and the prose was the error. The FRESH re-verification is the decorrelation JB-BOX-4 claims against LED-Λ's attempt grade.

---
### EFF.GRTJB.115  [lemma]  JB-TREE (iv) — (RM-m) as the transported instance

**CANONICAL STATEMENT:** verbatim, lines 1899–1903.
**FORM:** bold clause label + paragraph.

> “**(iv) [(RM-m) as the transported instance].** On this scope the four
> (RM-m) box clauses ([RMG] ACCEPTED) become classifier statements: (C-W_R)/
> (C-W_Q) are polygon statements about the classifier's R and Q digits
> (their v_{m+1}-values, via JA-VAL), and (C-READ) transports as §5. No
> clause of [RMG] is re-proved or touched.”

**CONDITIONALITY:** `P<q` read at level m (JA-VAL consumption) **AND** — for the (C-READ) leg — **§5's (VD-m) fence IN FULL** (matrix row 18, the correction r4/F-1 made to summary point (4)). **Its (C-W_Q) clause has NO machine leg** and is a no-leg cell ADJUDICATED OUT of the frontier (consumption at grade, not an open proviso).

**DERIVATION:** Composition (proof line 1908: “(iv) composition”). The transport is clause-by-clause: (C-W_R)/(C-W_Q) via JA-VAL on the output digits; (C-READ) via §5.

**RESOLUTION TRACE:** statement lines 1899–1903; proof line 1908; matrix row 18 at 312 (shard 1); the r4/F-1 correction 950–958 (shard 1 `.58`); the (C-READ) transport 2186–2242 (`.47`, `.49`).

XREF: `RMENGINE_2026-08-08.md:(RM-m)` — **11** · `(C-W_R)` — **7** · `(C-W_Q)` — **9** · `(C-READ)` — **8**.

**TEETH:** **(C-W_R) IND** (`jb_cread`'s `w_m(R) = λ+γ_{m+1}` pin); **(C-W_Q) NONE**; **(C-READ) IND on the scored stratum**. Disposition: mixed; the (C-W_Q) half is a **disclosed non-repair**.

---
### EFF.GRTJB.116  [changes-record]  (JB-TREE — the proof and the two struck grade lines)

**CANONICAL STATEMENT:** verbatim, lines 1905–1921.
**FORM:** `*Proof.*` marker + two struck grade blocks.

> “*Proof.* (i) consumption chain as displayed + JB-DEV(i). (ii) dev of
> Φ_{i+1} by Φ_i: the right side of (ID-(i+1)) has every C_k^{(i)}Φ_i^{e_ik}
> of degree < deg Φ_{i+1} with the C_k reduced (REALIZE R1), so the digit
> list reads off; uniqueness of division. (iii) the two displayed equalities
> + LED-Λ citation. (iv) composition. ~~∎ Grade: PROVED at attempt grade on
> the displayed scope. Scope fences: T-scope(m) …~~ ~~**[r2, G2-1 re-grep — a fence r1 carried into §2/§3 and
> left out of this grade line …]**~~”

**CONDITIONALITY:** Both grade lines **STRUCK and superseded by surface 4** (`.117`). **The r2 line is the one whose ADDITION created the inconsistency r2's own certification sentence denied** — PE3's F-1B (shard 1 `.49`): “hit 7 created the inconsistency in this same round by fencing JB-TREE(iii)/(iv) at m ≤ qcap while the grade cap graded JB-TREE with no perimeter and JB-BOX-2's enumeration omitted JB-TREE entirely”. The PROOF is live.

**DERIVATION:** This unit IS the proof: four one-line discharges.

**RESOLUTION TRACE:** statement lines 1905–1921; the superseding surface 1923–1962 (`.117`); the F-1B record 751–763 (shard 1 `.49`).

**TEETH:** carried by the clauses.

---
### EFF.GRTJB.117  [TABLE]  ★ SURFACE 4 of 14 — the §4 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 1923–1962.
**FORM:** bold-headed bracketed block + fixed-width per-clause display + an `[r3, F-1B]` closing note.

> “**[r3, STEP 2 — SURFACE 4 of 14, REGENERATED FROM §0M rows 14–18. ∎ GRADE:
> PROVED at attempt grade on the displayed scope. SCOPE FENCES ON EVERY CLAUSE:**
> T-scope(m) (the [RMG] d₀ ≥ 2 flat corners stay FENCED — the weld inherits them,
> blueprint S5's cross-cutting row); g_m = 1 for the Ĉ_m instance; W-WIN not
> consumed (window-free legs only, as in [RMG]). **PER CLAUSE:**
>
>     JB-ID / (ii)  PERIMETER-FREE — uniqueness of division at the print's own
>                   keys. Consumes [RMG] S2.2 (ID-(i+1)) + L-NORM + L-CELL, and
>                   S0.1's P_i = e_i·g_i (r3, F-7).           [rows 14, 16]
>     (i)           PERIMETER-FREE (it consumes JB-DEV(i), which holds at every
>                   q); W2-C1 representative reading, W2-C3's chamber off the
>                   byte perimeter; [RMG] T-TERM + L-EXACT + L-CANON — and
>                   L-CANON's hypothesis deg Ĉ_m < deg Φ_m is one of the two
>                   [RMG] clauses restored to §5's recital in r3 (F-5).
>                                                                 [row 15]
>     (iii)/(iv)    at levels **m ≤ qcap** only (`P<q` read at level m), since
>                   both consume JA-VAL — [r5, F-1: for (iii) the LEAF reading
>                   line = w_m = v_{m+1} at the R-LEAVES only (row 17); for
>                   (iv) the v_{m+1}-values of the OUTPUT digits R and Q
>                   (row 18); the unrestricted `line(C) = w_m(C) = v_{m+1}(C)`
>                   this line carried was the ONE live leftover of the r4/F-4
>                   re-scope, three lines above the surface's own (iii) item] —
>                   which J-A grades
>                   "PROVED unconditionally ON THE SHARED-KEY PERIMETER"; off it
>                   the v_{m+1}-reading of the print side is a different object.
>                                                            [rows 17, 18]
>     (iii)         LED-Λ is consumed at ATTEMPT grade and the tie's grade rides
>                   it (the runner re-verifies the λ_E quanta FRESH). [r4, F-4]
>                   the per-edge laws are laws of the LINE functional; the
>                   identification line = w_m = v_{m+1} is asserted at the
>                   R-LEAVES ONLY (L-LINE(iv) reduced cells + JA-VAL), which is
>                   where `jb_line` keys it; no internal-node v_{m+1} statement
>                   is claimed or tested.                              [row 17]
>     (iv)          its (C-READ) leg transports as §5 and therefore rides §5's
>                   (VD-m) fence IN FULL; its (C-W_Q) clause has NO machine leg.
>                                                                 [row 18]
>
> **[r3, F-1B — the (iii)/(iv) perimeter (r2's re-grep hit 7) now ALSO reaches
> the grade cap and JB-BOX-2's enumeration. r2 introduced this fence and in the
> same round certified those two surfaces "already consistent"; that claim was
> false when written and is corrected in the r2 block above.]]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| clause | fence | generating row(s) |
|---|---|---|
| **JB-ID / (ii)** | **PERIMETER-FREE** — uniqueness of division at the print's own keys; consumes [RMG] S2.2 (ID-(i+1)) + L-NORM + L-CELL + S0.1's `P_i` | rows 14, 16 |
| **(i)** | **PERIMETER-FREE** (consumes JB-DEV(i), every `q`); W2-C1 representative reading; W2-C3's chamber off the byte perimeter; T-TERM + L-EXACT + L-CANON (the last through the restored `deg Ĉ_m < deg Φ_m`) | row 15 |
| **(iii)/(iv)** | at levels **`m ≤ qcap`** only (`P<q` read at level `m`), since both consume JA-VAL; for (iii) the **LEAF** reading, for (iv) the `v_{m+1}`-values of the **OUTPUT** digits R and Q (r5/F-1) | rows 17, 18 |
| **(iii)** | LED-Λ at **ATTEMPT** grade, the tie's grade rides it; per-edge laws are **LINE**-functional laws; `line = w_m = v_{m+1}` at **R-LEAVES ONLY** | row 17 |
| **(iv)** | its (C-READ) leg rides §5's **(VD-m)** fence IN FULL; **(C-W_Q) has NO machine leg** | row 18 |
| **standing (all clauses)** | T-scope(m) (d₀ ≥ 2 flat corners stay FENCED); `g_m = 1` for the Ĉ_m instance; **W-WIN not consumed** | rows 15, 18, 26 |

**CONDITIONALITY:** **A REGENERATION of §0M rows 14–18.** It carries the r5/F-1 cleanup inside it (the removed leftover) and the r3/F-1B honesty note about r2's false certification.

**ARITHMETIC AUDIT (rule 22):** generating rows cited = 14, 15, 16, 17, 18 → **5 rows, contiguous, no gaps, no repeats** ✔ matches “§0M rows 14–18”. Clause entries = 5 (JB-ID/(ii), (i), (iii)/(iv), (iii), (iv)); rows 17 and 18 each appear twice, once in the joint (iii)/(iv) perimeter entry and once in their own clause-specific entry — **deliberate, and it is exactly what r5/F-1 had to disentangle** ✔. **Cross-check against §0M rows 14–18: every non-blank cell appears; every fence is a cell. VERIFIES.**

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 1923–1962; generating rows 308–312 (shard 1 `.20`); the r5/F-1 cleanup 1074–1079 (shard 1 `.68`); the F-1B record 751–763 (shard 1 `.49`).

**TEETH:** per row; **(C-W_Q) NONE**; the 8 chamber walks NONE.

---
### EFF.GRTJB.118  [instrument-record]  (JB-TREE — the machine bracket, with the r1/G-1 correction)

**CANONICAL STATEMENT:** verbatim, lines 1963–1980.
**FORM:** display with an embedded `[r1, G-1]` strike-and-replace.

> “[Machine: JB-TREE — a FRESH from-note tree walker
> (this unit's own implementation of S2.1/S2.2 on ITL towers: cells,
> E1-priority, L-NORM via divmod, signed reassembly) checked against (1)
> exact reassembly f·Ĉ_m = R₀ + QΦ_m, (2) ~~the canonical division by the
> harness key AND by the print-side key where byte-equal~~ **[r1, G-1 —
> CORRECTED to what the sealed runner establishes: the canonical division BY
> THE HARNESS KEY (one fresh `fresh_divmod`), plus, where the print key is
> byte-equal to it, the same division re-executed on the print key's bytes —
> a CONSISTENCY RE-CHECK, not an independent print-key reading: `fresh_divmod`
> is a pure function of (R, f, key), so on equal tuples the second call cannot
> fail unless the first does, and off the byte-equal set the sealed battery runs
> NO print-key tree check at all. The genuinely independent print-key evidence
> is the POST-SEAL walker of §7.4 (`grt_jb_printwalk.py`), which builds the
> tree from the print chain's own keys and correction digits and never calls
> `fresh_divmod`]**, (3) R-leaf
> reducedness; JB-ID — (ID-(i+1)) as the key's own development, both
> engines; JB-LINE — line(C) = wlev = vgen on reduced cells + the per-edge
> λ_E quanta recomputed fresh (LED-Λ's table row keyed); teeth MJB-TREE.]”

**SUPERSESSION KIND:** `counter re-reading` — an advertised independent print-key reading re-read as a consistency re-check.

**CONDITIONALITY:** **This is PE1/G-1, the FIRST instance of the SAME-COMPUTATION disease** that later produced the `IND/SAME/NONE` classification (`.98` / shard 1 `.18`) and recurred twice more. **The repair's own repair-instrument reproduced it** (r2/G2-2, shard 1 `.50`), which is the note's clearest bred-defect record.

**DERIVATION:** Purity of `fresh_divmod` as a function of `(R, f, key)`: on equal tuples the second call cannot fail unless the first does.

**RESOLUTION TRACE:** statement lines 1963–1980; the disposition 660–672 (shard 1 `.47` item G-1); the cell note ⟨n2⟩ 339–345 (shard 1 `.22`); the post-seal walker 2766–2846 (shard 3).

**TEETH:** `jb_tree` (79 walks, 125 with chambers, GREEN) with a **SAME** print-key sub-leg; `jb_id` (34, GREEN); `jb_line` (194, GREEN); planted mutant **MJB-TREE** (corrupted correction, 3/3 caught, fired). Post-seal: walker leg A, 84 print-keyed walks, genuinely decorrelated.

---
### EFF.GRTJB.119  [definition]  ★ §5 setting — the (RM-m) recital RESTORED (r3/F-5)

**CANONICAL STATEMENT:** verbatim, lines 1986–2023 — the struck partial recital, the `[r3, STEP 3 = F-5]` restoration, the quoted (RM-m) box, and the completed setting.
**FORM:** struck paragraph + bold-headed bracketed block + a quoted source display + a fixed-width clause list.

> “Setting: ~~the (RM-m) box verbatim ([RMG] S0.2, ACCEPTED on its scope):
> level m, g_m = 1, Ĉ_m the canonical correction digit
> (R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m), f ≠ 0 with
> deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and the canonical division
> f·Ĉ_m = R + Q·Φ_m.~~
>
> **[r3, STEP 3 = F-5 — THE RECITAL RESTORED, and with it the citation license
> LEMMA JB-EPS's application needed. The struck recital called itself "the (RM-m)
> box verbatim" while DROPPING two of the three parenthetical clauses [RMG]
> states about Ĉ_m. Both are restored here, quoted from the source display —
> `RMENGINE_2026-08-08.md` §S0.2, "THE STATEMENT UNDER PROOF — the (RM-m) box,
> quoted verbatim (operative-site paste)", itself byte-frozen there from [ILN]†
> S4.6 — which reads:**
>
> > **(RM-m) [READ-MULT with the canonical correction, level m], 1 ≤ m.**
> > Setting: level m of a class tower with g_m = 1, Ĉ_m the canonical
> > correction digit of WELL-DEF-(n)(ii) (deg < deg Φ_m, w_m = γ_{m+1},
> > R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}c_m). Input: f ∈ O[x],
> > f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f) its read. Claim:
> > there exist R, Q ∈ O[x] with deg R < deg Φ_m, deg Q < deg Φ_m, and
> >
> >   f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},
> >   w_m(Q) ≥ λ + γ_{m+1} − w_mΦ_m   (Q = 0 allowed),
> >   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m,
> >   ε′ := ⌊(s_m(λ) + s_m(γ_{m+1}))/e_{m−1}⌋  [the level-m EPS-carry].
>
> **SO §5'S SETTING, NOW COMPLETE: level m, g_m = 1, and Ĉ_m the canonical
> correction digit of WELL-DEF-(n)(ii) with ALL THREE of its clauses —**
>
>     (Ĉ-deg)   deg Ĉ_m < deg Φ_m                      [RESTORED in r3]
>     (Ĉ-wt)    w_m(Ĉ_m) = γ_{m+1}                      [RESTORED in r3]
>     (Ĉ-read)  R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m
>
> **— together with f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and
> the canonical division f·Ĉ_m = R + Q·Φ_m. (Ĉ-deg) is not decoration: [RMG]
> L-CANON's three hypotheses are Φ_m MONIC, deg f < deg Φ_m and (Ĉ-deg), so the
> restored clause is exactly what makes "THE canonical division" canonical at
> this site.**”

**Double-emission (rule 14) — the three Ĉ_m clauses as a `[TABLE]`:**

| clause | statement | status | what consumes it |
|---|---|---|---|
| **(Ĉ-deg)** | `deg Ĉ_m < deg Φ_m` | **RESTORED in r3** | L-CANON's third hypothesis — “exactly what makes ‘THE canonical division’ canonical at this site” |
| **(Ĉ-wt)** | `w_m(Ĉ_m) = γ_{m+1}` | **RESTORED in r3** | **the clause that LICENSES the JB-EPS instance at `(V, V′) = (λ, γ_{m+1})`** (`.123`) |
| **(Ĉ-read)** | `R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m` | present in r0 | JB-CREAD's proof (`τ_m` a unit) and the `Ĉ_m ≠ 0` step of the license |

**SUPERSESSION KIND:** `inventory completion` — a recital that called itself verbatim while dropping two clauses.

**CONDITIONALITY:** [RMG] ACCEPTED on its own scope (T-scope(m), g_m = 1). **The restoration is what makes two downstream statements licensed rather than asserted** — L-CANON's canonicity at `.111` and JB-EPS's application instance at `.123`. **PE4 byte-compared the restored recital against the source: 11/11 lines identical.**

**DERIVATION:** Quotation from the source display, itself byte-frozen there from [ILN]† S4.6.

**RESOLUTION TRACE:** statement lines 1986–2023; the disposition 893–897 (shard 1 `.55` STEP 3, and `.17`); the byte comparison 938–940 (shard 1 `.57`); the licensed consumers 1793–1801 (`.31`) and 2113–2144 (`.43`); matrix row 20 at 314 (shard 1).

XREF: `RMENGINE_2026-08-08.md:S0.2` — **13** · `(RM-m)` — **11** · `L-CANON` — **6**.
XREF: `ITERLAWN_PROOF_2026-08-08.md:S4.6` — **30** · `WELL-DEF` — **32**.

**TEETH:** **AUDIT — transfer audit** (PE4's 11/11 byte comparison against the source display). No battery can key a recital's completeness.

---
### EFF.GRTJB.120  [definition]  ★ THE LEVEL-m WEIGHT LATTICE `𝒲_m` (r4/F-8)

**CANONICAL STATEMENT:** verbatim, lines 2025–2044.
**FORM:** bold-headed bracketed block + fixed-width display.

> “**[r4, F-8 — THE OBJECT, DEFINED ONCE (the lemma quantifies over it, this
> license derives membership in it, and the u ≥ 0 retraction prose at §2(iii)
> argues about it — and no display in this note defined it).**
>
>     THE LEVEL-m WEIGHT LATTICE
>         𝒲_m := { w_m(f) : f ∈ O[x], f ≠ 0, deg f < deg Φ_m }
>              = { E_m·a + Σ_{l<m} j_l·Γ_l : a ∈ ℤ_{≥0}, 0 ≤ j_l ≤ P_l − 1 },
>
> **the VALUE SET of the level-m weight on this note's polynomial class (the
> SCRIPT letter 𝒲 deliberately — the roman W_m is already §1's read datum
> W_m := w_mΦ_m and is untouched). The
> second, explicit description is [RMG]: every such f is a finite sum of
> distinct REDUCED cells with w_m(f) = min line over them (L-CELL(i)), so every
> weight value IS a reduced-cell line value E_m·w₀(b) + Σ j_l·Γ_l with
> 0 ≤ j_l ≤ P_l − 1 and a := w₀(b) ≥ 0; conversely every reduced cell attains
> its line as its own weight (L-LINE(iv)), so every such value occurs.
> CONSEQUENCE, which closes the second half of the lemma's quantifier (PE4's
> F-8): E_m ≥ 1 and every Γ_l ≥ 1, with all coefficients ≥ 0, so 𝒲_m ⊆ ℤ_{≥0} —
> the quantifier's "V, V′ ≥ 0" half is IMPLIED by lattice membership, not a
> separate unchecked side condition.]**”

**SUPERSESSION KIND:** `inventory completion` — an object quantified over, argued about, and never defined.

**CONDITIONALITY:** **The explicit description rests on L-CELL(i)'s hypothesis `deg f < deg Φ_m`. That single hypothesis is why r5's discharge is only a SUB-WINDOW discharge and why matrix rows 4 and 12 stay on the frontier** (`.122`). **The notational separation `𝒲_m` (script) vs `W_m` (roman) is deliberate and flagged** — a collision hazard the merge must preserve.

**DERIVATION:** Both inclusions displayed. **(⊆)** every `f` in the class is a finite sum of distinct REDUCED cells with `w_m(f) = min line` over them (L-CELL(i)), so every weight value is a reduced-cell line value `E_m·w₀(b) + Σ j_l·Γ_l` with `0 ≤ j_l ≤ P_l − 1`, `a := w₀(b) ≥ 0`. **(⊇)** every reduced cell attains its line as its own weight (L-LINE(iv)), so every such value occurs. **Consequence:** `E_m ≥ 1`, every `Γ_l ≥ 1`, all coefficients `≥ 0` ⇒ `𝒲_m ⊆ ℤ_{≥0}`.

**RESOLUTION TRACE:** statement lines 2025–2044; the disposition 1021–1028 (shard 1 `.65`); consumed at 2046–2062 (`.41`), 2085–2111 (`.42`), 2113–2131 (`.43`), 1526–1536 (`.14`'s forward pointer); the `P_l` definition 1803–1819 (`.32`).

XREF: `RMENGINE_2026-08-08.md:L-CELL` — **11** · `L-LINE` — **23** · `S2.1` — **15** (the `E_m`, `Γ_l` constants).

**TEETH:** corroborated only: PE6's 598,500-member enumeration and PE7's reproduction. Disposition: **accepted-with-decorrelation-supplied**; the object itself is a definition and needs none.

---
### EFF.GRTJB.121  [lemma]  ★ the four-line theorem: `u ≥ 0` on all of `𝒲_m` (r5/F-3)

**CANONICAL STATEMENT:** verbatim, lines 2046–2083 — the theorem, its four displayed steps, the parity corollary, and the struck/replaced machine bracket.
**FORM:** bold-headed bracketed block + fixed-width numbered derivation + bold corollary + struck machine bracket with `[r6, F-2]` replacement.

> “**[r5, F-3 — THE DISCHARGE ON THE LATTICE (PE5's finding, re-derived here):
> u ≥ 0 IS A THEOREM ON ALL OF 𝒲_m, four lines from the display above. With
> s_m^wt(V) := (ℓ_{m−1}V) mod e_{m−1} (§5's notation block below;
> ℓ_{m−1}h_{m−1} ≡ 1 mod e_{m−1}) and the [RMG] S2.1 constants E_m =
> e₀⋯e_{m−1}, Γ_l = γ_{l+1}·∏_{l<t<m} e_t:**
>
>     (1) e_{m−1} | E_m, and e_{m−1} | Γ_l for every l ≤ m−2 (the ∏ contains
>         t = m−1); while Γ_{m−1} = γ_m ≡ h_{m−1} (mod e_{m−1}) with
>         γ_m ≥ h_{m−1} ≥ 1 (γ₁ = h₀; γ_m = e_{m−1}·w_{m−1}Φ_{m−1} + h_{m−1}
>         at m ≥ 2, with w_{m−1}Φ_{m−1} ≥ 0; h ≥ 1 the class pin).
>     (2) Hence every V = E_m·a + Σ_{l<m} j_l·Γ_l ∈ 𝒲_m has
>         V ≡ j_{m−1}·h_{m−1} (mod e_{m−1}), so s_m^wt(V) = j_{m−1} mod e_{m−1}
>         ≤ j_{m−1} (multiply by ℓ_{m−1}).
>     (3) V − s_m^wt(V)·h_{m−1} ≥ j_{m−1}·γ_m − s_m^wt(V)·h_{m−1}
>         ≥ (j_{m−1} − s_m^wt(V))·h_{m−1} ≥ 0  (every discarded term is ≥ 0;
>         γ_m ≥ h_{m−1}).
>     (4) So u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 for EVERY V ∈ 𝒲_m.  ∎
>
> **COROLLARY (correcting the two retained framing sentences, §2(iii) and
> JB-BOX-2): J-A's counterexample (e_{m−1}, h_{m−1}) = (2, 3), V = 1 ⇒ u = −1
> IS excluded from 𝒲_m — by (2), V ≡ j_{m−1} (mod 2), so V = 1 forces j_{m−1}
> odd ≥ 1, whence V ≥ γ_m ≥ 3 > 1.** ~~[Machine: read-only probe 2026-08-06
> (/tmp, all four instruments byte-untouched): 5,288,324 enumerated lattice
> members …]~~ **[r6, F-2 — the struck r5 bracket's figure is
> NOT REPLAYABLE … REPLACED by the reproducible record, with
> attribution: the PE6 verifier's own independent read-only enumerator
> (`GRTJB_passPE6_report.md` §1, commit ca39044; parameters disclosed there —
> 1-, 2- and 3-level read chains, coprime (e, h) with e ≤ 6, h ≤ 8,
> W_l ∈ {0, 1, 2}, a ≤ 4, j_l ≤ 6, 900 sampled chains): **598,500 lattice
> members, u < 0 violations 0, step-(2) identity violations 0; 1 ∉ 𝒲₁ at
> (e, h) = (2, 3)**. NOTHING RIDES ON EITHER FIGURE: u ≥ 0 on 𝒲_m is the
> displayed four-line THEOREM above — re-derived exactly by PE6 — and the
> probes are corroboration only.]**”

**Double-emission (rule 14) — the four-step derivation as a `[TABLE]`:**

| step | claim | ground |
|---|---|---|
| **(1)** | `e_{m−1} \| E_m`; `e_{m−1} \| Γ_l` for `l ≤ m−2`; `Γ_{m−1} = γ_m ≡ h_{m−1} (mod e_{m−1})` with `γ_m ≥ h_{m−1} ≥ 1` | `E_m = e₀⋯e_{m−1}`; the product in `Γ_l` contains `t = m−1` for `l ≤ m−2`; `γ_m = e_{m−1}w_{m−1}Φ_{m−1} + h_{m−1}` with `w_{m−1}Φ_{m−1} ≥ 0`; `h ≥ 1` the class pin |
| **(2)** | every `V ∈ 𝒲_m` has `V ≡ j_{m−1}h_{m−1} (mod e_{m−1})`, so `s_m^wt(V) = j_{m−1} mod e_{m−1} ≤ j_{m−1}` | (1) + multiply by `ℓ_{m−1}` (`ℓ_{m−1}h_{m−1} ≡ 1 mod e_{m−1}`) |
| **(3)** | `V − s_m^wt(V)h_{m−1} ≥ j_{m−1}γ_m − s_m^wt(V)h_{m−1} ≥ (j_{m−1} − s_m^wt(V))h_{m−1} ≥ 0` | every discarded term `≥ 0`; `γ_m ≥ h_{m−1}`; (2) |
| **(4)** | `u := (V − s_m^wt(V)h_{m−1})/e_{m−1} ≥ 0` for EVERY `V ∈ 𝒲_m` ∎ | (3) divided by `e_{m−1} > 0` |
| **COROLLARY** | J-A's `(e,h) = (2,3), V = 1 ⇒ u = −1` is **excluded from `𝒲_m`** | by (2), `V ≡ j_{m−1} (mod 2)`, so `V = 1` forces `j_{m−1}` odd `≥ 1`, whence `V ≥ γ_m ≥ 3 > 1` |

**CHAIN:** member 3 of the `u ≥ 0` chain; **CHAIN HOME is §0M column (b)** (shard 1 `.14`); `CHAIN-MEMBER: .14 position 3`. **This unit is the POSITIVE content of the whole chain** — the only place the discharge is actually proved.

**SUPERSESSION KIND:** `scope-pin` (the discharge with its sub-window scope) + `replacement` (r6/F-2's swap of an UNPINNED figure for a reproducible one).

**CONDITIONALITY:** **The theorem is unconditional ON `𝒲_m`.** Everything conditional is about MEMBERSHIP in `𝒲_m` — see `.122`. **The parity corollary matters because it kills the specific counterexample the retraction (`.94`) said “nothing in this note excludes”** — so the r2 retraction's own framing went stale, and r5 says so.

**PIN VERIFICATION (rule 23):** r5's own figure (5,288,324) is **UNPINNED** — read-only to /tmp, parameters unrecorded, and the note reaches that verdict itself at r6/F-2. The replacement (598,500/0) is verifier-owned with parameters disclosed in `GRTJB_passPE6_report.md` (**file EXISTS**), commit `ca39044` (**resolves**), and was **independently REPRODUCED EXACTLY by PE7 on the first natural parameterization**.

**DERIVATION:** Fully displayed above, four lines from `.120`'s description; **re-derived from the note's own display, not copied from the verifier** (the note says so).

**RESOLUTION TRACE:** statement lines 2046–2083; the object 2025–2044 (`.120`); the scope split 2085–2111 (`.122`); the chain home 218–250 (shard 1 `.14`); dispositions 1053–1073 (r5/F-3) and 1164–1178 (r6/F-2), both shard 1.

XREF: `RMENGINE_2026-08-08.md:S2.1` — **15**.

**TEETH:** **PROOF-ONLY, and the note says so:** “NOTHING RIDES ON EITHER FIGURE: u ≥ 0 on 𝒲_m is the displayed four-line THEOREM”. Corroboration: PE6 598,500/0 (produced), PE7 reproduced exactly, PE8 wider box 340/0 on the m = 1 equivalence. Disposition: **PROOF-ONLY + accepted-with-decorrelation-supplied**.

---
### EFF.GRTJB.122  [scope record]  ★ the SCOPE split — what the discharge does and does not cover

**CANONICAL STATEMENT:** verbatim, lines 2085–2111.
**FORM:** bold-headed paragraph with two nested riders.

> “**SCOPE — WHAT THIS DISCHARGES AND WHAT IT DOES NOT (§0M rows 4/12, column
> (b)).** The two u ≥ 0 consumers — §2(iii)(GRID) and JB-VTX(d4) — quantify
> f ∈ O[x] nonzero with NO DEGREE BOUND and apply JA-GRID(a) at
> V = w_{q+1}(f), while 𝒲_{q+1} is the weight value set ONLY on
> deg f < deg Φ_{q+1} (L-CELL(i)'s hypothesis is what the displayed
> description rests on — the same hypothesis scope as §4(ii)'s r5/F-2 note).
> So the proviso is DISCHARGED on the deg f < deg Φ_{q+1} sub-window, where
> membership holds by definition, and stays CARRIED at the full quantifier as
> the ~~strictly smaller~~ MEMBERSHIP hypothesis w_{q+1}(f) ∈ 𝒲_{q+1} **[r6,
> m-1 — the accurate relation: membership IMPLIES the u ≥ 0 instance needed at
> V = w_{q+1}(f) — a SUFFICIENT route, ~~per-instance a logically STRONGER
> hypothesis, not an equivalent or weaker one~~ **[r7, PE7 F-1 — the struck
> non-equivalence claim was derived nowhere and is FALSE at every m = 1
> (q = 0) instance, where {V ∈ ℤ_{≥0} : u(V) ≥ 0} = 𝒲₁ EXACTLY — §0M column
> (b) carries the two-direction proof (the §5 four-line theorem + the j := s
> decomposition) and PE7's machine check (96 read data, every V ∈ [0, 150),
> 0 counterexamples; `GRTJB_passPE7_report.md` §2 F-1, commit aa9b603). The
> instance-honest relation: sufficiency always — all any consumer uses; the
> converse INSTANCE-DEPENDENT — EQUIVALENT at m = 1, containment possibly
> strict at m ≥ 2, strictness UNPROVED either way in general]**; "smaller" is
> true only of the
> remaining open DOMAIN, now confined to deg f ≥ deg Φ_{q+1} and pinned to one
> concrete question]**, which
> nothing this note consumes establishes at deg f ≥ deg Φ_{q+1}. Rows 4 and 12
> therefore REMAIN frontier members with their open residue re-characterized
> (summary point (1)). **§5's OWN application is unaffected either way: its
> λ, γ_{m+1} memberships are DERIVED above (the license), not hypothesized.]**”

**CHAIN:** carries members 3→4 of the `u ≥ 0` chain in body form. **CHAIN HOME: §0M column (b)** (shard 1 `.14`); **TERMINAL reading is r7's**, quoted inside. `CHAIN-MEMBER: .14 positions 3–4 (body site B).`

**SUPERSESSION KIND:** `scope-pin` (the split) + `wording-rider` (r6) + `counter re-reading` (r7).

**CONDITIONALITY:** **This is the honest core of the whole `u ≥ 0` arc, and it is stated as a clean two-part disposition:**
- **DISCHARGED** on `deg f < deg Φ_{q+1}` (membership holds by definition).
- **CARRIED** at the full quantifier as `w_{q+1}(f) ∈ 𝒲_{q+1}` — SUFFICIENT for what the consumers need; EQUIVALENT at `m = 1`; **strictness at `m ≥ 2` UNPROVED EITHER WAY**.
- **Rows 4 and 12 REMAIN frontier members.**
- **§5's own application is unaffected** — its two memberships are DERIVED at `.123`, not hypothesized. **This last clause is what stops the open residue from contaminating JB-CREAD.**

**DERIVATION:** The split is read off `.120`'s description (which rests on L-CELL(i)'s `deg f < deg Φ_m`) against the consumers' quantifier (`f` nonzero, no degree bound). The `m = 1` equivalence's two directions are displayed at §0M column (b) (shard 1 `.14`): **(⊇)** the four-line theorem at `m = 1`; **(⊆)** `u(V) ≥ 0` means `V = s·h₀ + u·e₀` with `s := (ℓ₀V) mod e₀ ∈ [0, e₀−1]`, `u ≥ 0` — take `j := s ≤ e₀−1 ≤ P₀−1` and `a := u`.

**RESOLUTION TRACE:** statement lines 2085–2111; the theorem 2046–2062 (`.121`); the chain home 218–250 (shard 1 `.14`); dispositions 1053–1073, 1179–1190, 1218–1258 (shard 1 `.67`, `.75`, `.77`, `.78`); the third site JB-BOX-2 2362–2372 (`.56`).

**TEETH:** rows 4 and 12 are **frontier cells (`NONE` + open residue)**. The `m = 1` equivalence: PE7 96 read data / 0 counterexamples; PE8 wider box 340 / 0. Disposition: **PROOF-ONLY for the split; accepted-with-decorrelation-supplied for the equivalence**. **OPEN-CALL 3 of shard 1 is exactly this residue.**

---
### EFF.GRTJB.123  [lemma]  THE LICENSE — the two lattice memberships derived

**CANONICAL STATEMENT:** verbatim, lines 2113–2144.
**FORM:** bold-headed block + fixed-width two-part derivation + a closing provenance paragraph with an `[r4, F-5]` correction.

> “**THE LICENSE (what F-5 charged). LEMMA JB-EPS below is quantified over
> V, V′ ≥ 0 IN THE LEVEL-m WEIGHT LATTICE (:= 𝒲_m above; the script letter — W_m stays §1's read datum w_mΦ_m), and THEOREM JB-CREAD's
> display applies it at (V, V′) = (λ, γ_{m+1}). Both LATTICE memberships now
> follow in one line each — and the ≥ 0 conditions follow from them, since
> 𝒲_m ⊆ ℤ_{≥0} (r4, F-8):**
>
>     λ = w_m(f)  with f ≠ 0        ⇒  λ is the level-m weight of a NONZERO
>                                      polynomial of the class (deg f < deg Φ_m),
>                                      hence λ ∈ 𝒲_m BY THE DEFINITION ABOVE
>                                      [r4, F-8: the old warrant "(which contains
>                                      every value of w_m on nonzero
>                                      polynomials)" is now the displayed
>                                      definition, not an uncited parenthetical].
>     γ_{m+1} = w_m(Ĉ_m) by (Ĉ-wt), and Ĉ_m ≠ 0 because its read
>     R_{m,γ_{m+1}}(Ĉ_m) = τ_m is NONZERO by (Ĉ-read) (τ_m = ε_m(γ_{m+1})^{−1}c_m
>     with c_m = ψ_{m,0} ≠ 0, the class pin)
>                                   ⇒  γ_{m+1} is likewise the level-m weight of
>                                      a nonzero polynomial, hence in the
>                                      level-m weight lattice.  ∎
>
> **Before r3 the second line was UNAVAILABLE in this note: γ_{m+1} appeared only
> as the DEFINED INTEGER γ_{m+1} := e_m·w_mΦ_m + h_m of §1's read data, and
> (Ĉ-wt) — the clause that identifies that integer as a weight — was the clause
> the recital had dropped. The lemma itself was never in danger (its proof uses
> only s^wt(β) ≡ ℓ_{m−1}β mod e_{m−1} and JA-GRID(c), ~~and `jb_eps` quantifies
> PLAIN integers 0 ≤ V,V′ < 25, a superset of the lattice~~ **[r4, F-5 — the
> struck description of the machine leg was wrong twice: `jb_eps` samples the
> STRIDED grid V ∈ 2ℤ, V′ ∈ 3ℤ inside [0, min(3·e·h + 5, 25)) — a spot-check of
> the lemma, NOT a superset of anything; the applied instance is sampled on only
> 4 of the 56 roster scored rows (§0M row 20)]**), so r3 restores the
> LICENSE rather than widening the lemma: the quantifier stands as written and the
> cited instance is now provably inside it. §0M rows 19/20.]**”

**SUPERSESSION KIND:** `inventory completion` (r3/F-5 restores the licensing clause) + `counter re-reading` (r4/F-5 corrects the machine-leg description twice over).

**CONDITIONALITY:** **The license is DERIVED, not hypothesized** — which is exactly why `.122` can say “§5's OWN application is unaffected either way”. **Its second line depends on the restored `(Ĉ-wt)`** and was literally unavailable before r3. **The r4/F-5 correction downgrades the instance's machine support to a strided spot-check on 4 of 56 rows** — so the license rests on the PROOF, not on the leg, and the note says so.

**DERIVATION:** Two one-line derivations, displayed. `λ ∈ 𝒲_m` by `.120`'s definition (λ is `w_m` of a nonzero `f` in the class). `γ_{m+1} ∈ 𝒲_m` because `(Ĉ-wt)` gives `γ_{m+1} = w_m(Ĉ_m)` and `(Ĉ-read)` gives `Ĉ_m ≠ 0` (its read `τ_m = ε_m(γ_{m+1})^{−1}c_m` is nonzero, with `c_m = ψ_{m,0} ≠ 0` the class pin). The `≥ 0` half follows from `𝒲_m ⊆ ℤ_{≥0}` (r4/F-8).

**RESOLUTION TRACE:** statement lines 2113–2144; the restored clauses 2015–2017 (`.119`); the object 2025–2044 (`.120`); matrix rows 19, 20 at 313–314 (shard 1); dispositions 893–897 (r3/F-5) and 999–1008 (r4/F-5), shard 1.

XREF: `ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13** (the class pin `ψ_j(0) ≠ 0`).

**TEETH:** matrix row 20 — a **STRIDED SPOT-CHECK**: `V` from `range(0, min(3·e·h + 5, 25))` stepped `[::2]`, `V′` same range stepped `[::3]`; the applied instance IN the sampled set on **4 of 56** roster scored rows (T2A, T3D at m = 1, λ ∈ {0,4}, γ₂ = 9) and **NOT-SAMPLED on the other 52, including EVERY m ≥ 2 row**. Disposition: **signed vacuity disclosure**; “an instance-keyed leg is a CANDIDATE for a future instrument”.

---
### EFF.GRTJB.124  [definition]  the constant `c_m = ψ_{m,0} = −z_{m+1}`

**CANONICAL STATEMENT:** verbatim, lines 2146–2150.
**FORM:** inline paragraph + display.

> “Here c_m = ψ_{m,0}, the constant coefficient of the
> degree-1 modulus ψ_m(y) = y + ψ_{m,0} (from WELL-DEF's g_m = 1 lift form
> and REALIZE R3, consumed) — so in K_{m+1} = K_m[z_{m+1}]/(ψ_m),
>
>     c_m = ψ_{m,0} = −z_{m+1}    (the classifier's NEXT residual letter).”

**CONDITIONALITY:** Requires `g_m = 1` (so `ψ_m` is degree 1). **This identity is “the semantic germ the J-C carrier block (W-6..W-9) needs”** (`.134`) and is the one place GRTJB touches the J-C interface — under an explicit BLOCKED-ON-CARRIER-TIE fence.

**DERIVATION:** At `g_m = 1`, `ψ_m(y) = y + ψ_{m,0}`; in `K_{m+1} = K_m[y]/(ψ_m)` the class of `y` is `z_{m+1}`, so `z_{m+1} + ψ_{m,0} = 0`, i.e. `ψ_{m,0} = −z_{m+1}`.

**GENERALITY NOTE (Q7, recorded not applied).** `runs/qgen/Q7_output.log` classifies this display **BENIGN** under hazard H3: *“`c_m = ψ_{m,0} = −z_{m+1}` — **BENIGN.** Negation makes sense in every characteristic; in characteristic 2, `−z = z`. No use of `2^{−1}`, discriminant square classes, or mod-4/8 arguments occurs.”* No edit; recorded.

**RESOLUTION TRACE:** statement lines 2146–2150; consumed at 2212 (`.127`'s conclusion), 2303–2308 (`.134`); the class pin `ψ_j(0) ≠ 0` at [ILN]† S0.1.

XREF: `ITERLAWN_PROOF_2026-08-08.md:WELL-DEF` — **32** · `REALIZE` — **17** (NEAR-MISS on the compound `REALIZE R3`; law label `R3` count **4**).

**TEETH:** `jb_cm` — `c_m = ψ_{m,0}` and `embed_{K_{m+1}}(c_m) = −z_{m+1}`, **28 eligible (T, m) rows, GREEN** (§7.1, shard 3).

---
### EFF.GRTJB.125  [definition]  the `s_m(·)` overload, declared and split (r1/G-7)

**CANONICAL STATEMENT:** verbatim, lines 2152–2169.
**FORM:** bold-headed bracketed block + fixed-width two-part definition + a closing discipline sentence.

> “**[r1, G-7 — the s_m(·) OVERLOAD, declared and split.]** r0 wrote one symbol
> s_m(·) for two different integers, undefined in-note:
>
>     s_m^wt(V) := (ℓ_{m−1}·V) mod e_{m−1}   for a level-m WEIGHT V
>                  — the eq-(12) abscissa; equivalently the least x ∈
>                  [0, e_{m−1}) with (V − x·h_{m−1}) ≡ 0 (mod e_{m−1}),
>                  which is the runner's ℓ-FREE `s_geo(V, e, h)`;
>     s_m^ini(A) := the INITIAL ATTAINED ABSCISSA of a POLYNOMIAL A on its
>                  own realized side (the print's s₀ = the least abscissa of
>                  the realized side of N_m(A)) — the integer (VD-m) and
>                  τ_m(A) are written with.
>
> They differ by a multiple of e_{m−1} in general (J-A's own
> s₀ = s_m^wt(β) + ν·e_{m−1}, ν ≥ 0 the grid offset), so the two readings are
> NOT interchangeable. From here on LEMMA JB-EPS is stated with s_m^wt ONLY
> (its arguments are weights) and (VD-m)/τ_m with s_m^ini; no step of §5 mixes
> them, and the r0 proof did not (this is a notation repair, not a
> mathematical one).”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| symbol | definition | domain | used by |
|---|---|---|---|
| **`s_m^wt(V)`** | `(ℓ_{m−1}·V) mod e_{m−1}`; equivalently the least `x ∈ [0, e_{m−1})` with `(V − x·h_{m−1}) ≡ 0 (mod e_{m−1})`; = the runner's ℓ-FREE `s_geo(V, e, h)` | a level-m **WEIGHT** `V` | **LEMMA JB-EPS only** |
| **`s_m^ini(A)`** | the INITIAL ATTAINED ABSCISSA of a **POLYNOMIAL** `A` on its own realized side (the print's `s₀`, least abscissa of the realized side of `N_m(A)`) | a polynomial `A` | **(VD-m) and `τ_m` only** |
| relation | `s₀ = s_m^wt(β) + ν·e_{m−1}`, `ν ≥ 0` the grid offset — **they differ by a multiple of `e_{m−1}` in general and are NOT interchangeable** | — | — |

**SUPERSESSION KIND:** `inventory completion` — one symbol carrying two integers, split and both defined.

**CONDITIONALITY:** **“this is a notation repair, not a mathematical one” — the note verifies the r0 proof did not mix them.** The separation is load-bearing downstream: `.126`'s lemma is stated with `s_m^wt` ONLY, `.127`'s `τ_m` with `s_m^ini` ONLY.

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies the `s_m^wt` arithmetic **BENIGN** under H1/H7: *“`t_m(β)=(ℓ_{m−1}β−s_m^{wt}(β))/e_{m−1}` — **BENIGN — integer normalization.** No `e`-th root or field division is used.”* No edit; recorded.

**DERIVATION:** Definitions + the displayed relation `s₀ = s_m^wt(β) + ν e_{m−1}`, which is J-A's own.

**RESOLUTION TRACE:** statement lines 2152–2169; the disposition 688–690 (shard 1 `.47` item G-7); consumed at 2171–2183 (`.46`) and 2205–2209 (`.47`).

**TEETH:** the runner's ℓ-free `s_geo` is the machine form of `s_m^wt` and is one of `jb_eps`'s two legs (955 samples, IND).

---
### EFF.GRTJB.126  [lemma]  ★ LEMMA JB-EPS — the ε-cocycle collapse (the note's only unconditional statement)

**CANONICAL STATEMENT:** verbatim, lines 2171–2184.
**FORM:** bold-headed lemma + display + `*Proof.*` + machine bracket.

> “**LEMMA JB-EPS (the ε-cocycle collapse; unconditional, pure read data).**
> For every m ≥ 1 and V, V′ ≥ 0 in the level-m weight lattice, with
> t_m(β) = (ℓ_{m−1}β − s_m^wt(β))/e_{m−1} the print twist exponent (JA-EPS's
> convention) and ε′ := ⌊(s_m^wt(V) + s_m^wt(V′))/e_{m−1}⌋:
>
>     t_m(V + V′) − t_m(V) − t_m(V′) = ε′ ,   hence
>     ε_m(V+V′) · ε_m(V)^{−1} · ε_m(V′)^{−1} = z_m^{−ε′} .
>
> *Proof.* The numerator telescopes (all s's are s_m^wt): ℓ(V+V′) − s(V+V′) −
> ℓV + s(V) − ℓV′ + s(V′) = s(V) + s(V′) − s(V+V′) = e_{m−1}·ε′ by the carry
> clause (JA-GRID(c) = (C-EPS), graded in J-A PROVED and unconditional, and
> carrying no u ≥ 0 proviso); divide by e_{m−1} (legitimate: t_m(β) ∈ ℤ since
> s_m^wt(β) ≡ ℓ_{m−1}β mod e_{m−1}). The field form is JA-EPS (ε = z^{−t}). ∎
> [Machine: JB-EPS, integers + field elements, every roster level.]”

**CONDITIONALITY:** **UNCONDITIONAL at every `m ≥ 1`** (matrix row 19) — **no perimeter, no `u ≥ 0` proviso (it cites JA-GRID(c), which carries none), no (VD-m)**. This is the ONLY statement in GRTJB with that status, and the note guards it explicitly at `.93` (“this sentence is about (VD-m) only — LEMMA JB-EPS is unconditional at every m ≥ 1, as its own grade line says”). **Its APPLICATION at `(λ, γ_{m+1})` is a separate matter and is `.123`/matrix row 20.**

**DERIVATION:** Displayed in full. The numerator telescopes to `s(V) + s(V′) − s(V+V′)`, which is `e_{m−1}·ε′` **by JA-GRID(c) = (C-EPS)** — the carry clause, PROVED and unconditional in J-A and carrying no proviso. Division by `e_{m−1}` is legitimate because `t_m(β) ∈ ℤ` (since `s_m^wt(β) ≡ ℓ_{m−1}β mod e_{m−1}`). The field form is JA-EPS (`ε = z^{−t}`).

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies exactly this step **BENIGN** under H1/H7: *“‘divide by `e_{m−1}` (legitimate: `t_m(β)∈ℤ` since `s_m^{wt}(β)≡ℓ_{m−1}β (mod e_{m−1})`)’ — **BENIGN — integer divisibility.** This is division in `ℤ`, not multiplication by `e_{m−1}^{−1}` in `O` or a residue field. **It remains valid when the residue characteristic divides `e_{m−1}`.**”* No edit; recorded.

**RESOLUTION TRACE:** statement lines 2171–2184 (statement and proof one span); matrix row 19 at 313 (shard 1); the license 2113–2144 (`.123`); consumed at 2241 (`.129`'s fifth line).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-GRID` — **11** · `JA-EPS` — **13**. `RMENGINE_2026-08-08.md:(C-EPS)` — **7**.

**TEETH:** `jb_eps` — **955 samples, IND**: an ℓ-FREE `s_geo` leg plus a fresh Bézout computation against the ℓ-form `t_m`, then the field form. **Two genuinely different computations of the same integer, plus the field check.**

---
### EFF.GRTJB.127  [lemma]  ★ THEOREM JB-CREAD — the (C-READ) transport

**CANONICAL STATEMENT:** verbatim, lines 2186–2212 — the hypothesis with its `[r1, F1]` correction and `[r2, G2-4]` mechanism strike, the definitions, and the conclusion.
**FORM:** bold-headed theorem + nested riders + display.

> “**THEOREM JB-CREAD.** Suppose (VD-m) (J-A §3.4's evaluated dictionary)
> holds at f and at R — ~~unconditional for m ≤ 2 (VD-1 = W2-L3; m = 2 by
> JA-RES), per-digit proviso / (R-coll) at m ≥ 3 (JA-BOX-2)~~ **[r1, F1 —
> SUPERSEDED; the struck parenthetical was FALSE and the note's own sealed
> runner refutes it. THE HONEST PERIMETER: unconditional at m ≤ 1 ONLY
> ((VD-1) = W2-L3); at every m ≥ 2 the hypothesis is CONDITIONAL — it needs
> JA-VDIND's absolute character-triviality z_{m−1}^{i·A_{m−1}} = 1 at every
> attained abscissa (sufficient: A_{m−1} = 0, i.e. e_{m−2} = 1; or
> ord(z_{m−1}) | A_{m−1} with the abscissa condition), which at m ≥ 3 is
> implied by the per-digit proviso / (R-coll) of JA-BOX-2. "m = 2 by JA-RES"
> conflated J-A's PER-SLOT law (unconditional at m = 2) with the EVALUATED
> dictionary (VD-2), which JA-RES alone does not give: on the sealed roster
> (VD-2) is machine-evaluated FALSE at 10 of 13 boundary rows
> (T3A/T3B/T3C/T3D ~~— the e₀ ≥ 2 character-visible towers~~ **[r2, G2-4 — the
> struck gloss is a MECHANISM CLAIM and the note's own roster refutes it: T3E
> also has e₀ = 2 (reads e = 2,1,2) and scores 6/6. The four towers are the
> OBSERVED failing rows, listed as data; no property in this note distinguishes
> them from the scoring e₀ ≥ 2 rows, see §7.1]**), §7.1/§7.4]** — and
> suppose v ≠ 0 (THE NON-DEGENERATE READ STRATUM; the v = 0 branch is displayed
> after the proof). Define the print's TWISTED EVALUATED READ
> ρ_m(A) := z_m^{τ_m(A)}·R_m^cls(A)(z_m) (R_m^cls the print residual
> operator at A's own realized side, τ_m(A) = (s_m^ini(A) −
> ℓ_{m−1}w_m(A))/e_{m−1} as in (VD-m), with s_m^ini the initial attained
> abscissa of §5's notation block, r1/G-7). Then w_m(R) = λ + γ_{m+1} exactly,
> and
>
>     ρ_m(R)  =  c_m · ρ_m(f)  =  ψ_{m,0} · ρ_m(f) .”

**SUPERSESSION KIND:** `replacement` (r1/F1: a false perimeter) + `counter re-reading` (r2/G2-4: a mechanism claim struck, not replaced).

**CONDITIONALITY:** **Two hypotheses, both explicit and both fenced:**
1. **(VD-m) at BOTH `f` and `R`** — unconditional at `m ≤ 1` ONLY; at every `m ≥ 2` a HYPOTHESIS (JA-VDIND's absolute character-triviality). **JB-CREAD has NO unconditional stratum above `m = 1`.** **E-1 re-reads the “(R-coll)” label** at GRTJA's root-inclusive form.
2. **`v ≠ 0`** — the non-degenerate read stratum; the `v = 0` branch is `.130`.
**No key perimeter** (⟨n5⟩: the print-side content enters only through the (VD-m) hypothesis, so the theorem is a legitimate conditional at any level).

**DERIVATION:** `.129`.

**RESOLUTION TRACE:** statement lines 2186–2212; **proof lines 2223–2242** (`.129`); the reading fence 1471–1495 (`.93`); the census 2494–2546 and 2748–2764 (shard 3); dispositions 638–659 and 792–803 (shard 1 `.44`, `.51`); correction site 3125–3133 (E-1); matrix rows 21, 22 at 315–316 (shard 1).

XREF: `GRTJA_PROOF_2026-08-08.md:(VD-m)` — **10** · `JA-VDIND` — **21** · `JA-RES` — **20** · `(R-coll)` — **7** · `JA-BOX-2` — **7**. `GRTW2_PROOF_2026-08-08.md:W2-L3` — **5**.

**TEETH:** `jb_cread` — **IND end-to-end cross-engine** (print residuals via the sealed `GmnLeg`, harness division/reads via ITL, `τ`/`ε′` fresh integers) on the SCORED stratum: **104 scored / 21 boundary disclosed**, plus teeth **MJB-CREAD** (22 samples over 14 towers). Disposition: **executable regression with the boundary census disclosed**.

---
### EFF.GRTJB.128  [scope record]  the transport, stated in both frames

**CANONICAL STATEMENT:** verbatim, lines 2214–2221.
**FORM:** bold-headed paragraph.

> “**The transport, stated.** [RMG]'s (C-READ) — "multiplying a read digit by
> the canonical correction digit shifts the read by τ_m with the level-m
> EPS-carry z_m^{ε′}" — transports to the classifier as: THE CLASSIFIER'S
> TWISTED RESIDUAL READ SHIFTS BY THE CONSTANT c_m, WITH NO CARRY FACTOR.
> The z_m^{ε′} carry of the harness frame is EXACTLY the coordinate change
> between the print twist t_m and the harness ε-kit (LEMMA JB-EPS); it
> reappears verbatim when the identity is written in ε-coordinates — that
> form IS [RMG] (C-READ), consumed not re-proved.”

**CONDITIONALITY:** Inherits `.127`'s two hypotheses. **The two-frame statement is what JB-BOX-1 corrects in the blueprint** (`.135`): the blueprint displayed the harness-frame form as if it were the classifier-frame one.

**DERIVATION:** The carry's cancellation is LEMMA JB-EPS, applied inside `.129`'s chain; the harness-frame form is [RMG] (C-READ), **consumed not re-proved**.

**RESOLUTION TRACE:** statement lines 2214–2221; proof lines 2236–2242 (`.129`); the box 2314–2321 (`.135`).

XREF: `RMENGINE_2026-08-08.md:(C-READ)` — **8**.

**TEETH:** teeth **MJB-CREAD** — “the spurious-carry reading `ρ_m(R) = z_m^{ε′}·c_m·ρ_m(f)` must FAIL on designated `ε′ ≥ 1` rows”, and it does on all 22. **This is the tooth that makes the carry's placement machine-load-bearing rather than a notational preference.**

---
### EFF.GRTJB.129  [lemma]  ★ the five-line proof chain

**CANONICAL STATEMENT:** verbatim, lines 2223–2242.
**FORM:** `*Proof (displayed in full).*` + a five-line display.

> “*Proof (displayed in full).* By (VD-m) at f: ρ_m(f) = ε_m(λ)·v. Since
> v ≠ 0 and τ_m is a unit, (C-READ) gives R_{m,λ+γ_{m+1}}(R) =
> z_m^{ε′}·v·τ_m ≠ 0, so some cell of R sits on-line on-grid at
> λ + γ_{m+1} (B-READ) **[r1, G-7 — tag resolved: (B-READ) is [RMG] S2.1's
> LEMMA L-CELL clause (ii) — a nonvanishing level-m read at a weight forces an
> on-line on-grid cell at that weight — whose parent L-CELL is in this note's
> header consumption list; clause (i) (w_m = the minimum line over cells) is
> what turns that into the weight inequality. r0 used the bare tag, which is
> unresolvable from this note alone]**, forcing w_m(R) ≤ λ + γ_{m+1}; with
> (C-W_R)'s ≥
> this pins w_m(R) = λ + γ_{m+1} EXACTLY — so (VD-m) at R is an identity
> at the (C-READ) target:
>
>     ρ_m(R) = ε_m(λ+γ_{m+1}) · R_{m,λ+γ_{m+1}}(R)
>            = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · τ_m            [(C-READ)]
>            = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · ε_m(γ_{m+1})^{−1} · c_m
>            = [ε_m(λ+γ_{m+1}) ε_m(λ)^{−1} ε_m(γ_{m+1})^{−1}] · z_m^{ε′}
>              · c_m · ε_m(λ)·v
>            = z_m^{−ε′} · z_m^{ε′} · c_m · ρ_m(f)            [JB-EPS]
>            = c_m · ρ_m(f) .                                  ∎”

**CONDITIONALITY:** Inherits `.127`'s hypotheses. **Every step names its ground inline**, and the note calls the display “in full” — it is the one proof in GRTJB written as a closed chain rather than a consumption list.

**DERIVATION:** As displayed. Structure: (VD-m) at `f` gives `ρ_m(f) = ε_m(λ)v`; `v ≠ 0` + `τ_m` a unit + (C-READ) gives a nonzero target read; **(B-READ) = L-CELL(ii)** forces an on-line on-grid cell at `λ+γ_{m+1}`, hence `w_m(R) ≤ λ+γ_{m+1}`; **(C-W_R)'s `≥`** pins equality; then the five-line computation, whose only non-consumption step is **JB-EPS**, which collapses `ε_m(λ+γ_{m+1})ε_m(λ)^{−1}ε_m(γ_{m+1})^{−1} = z_m^{−ε′}` against the `(C-READ)` carry `z_m^{ε′}`.

**NEAR-MISS (rule 15) — `(B-READ)`:** fixed-string `(B-READ)` has count **0** in `RMENGINE_2026-08-08.md`. **The note itself resolves it in place** to “[RMG] S2.1's LEMMA L-CELL clause (ii)”; `L-CELL` count **11**, `S2.1` count **15**. Disposition: **NEAR-MISS — designation absent as written; verified referent `L-CELL` (count 11); the tag is GRTJB-local and r1/G-7 declares it so.** Not an OPEN-CALL.

**RESOLUTION TRACE:** statement lines 2223–2242; the hypotheses 2186–2212 (`.127`); JB-EPS 2171–2184 (`.126`); the disposition 688–690 (shard 1 `.47` item G-7).

XREF: `RMENGINE_2026-08-08.md:(C-READ)` — **8** · `(C-W_R)` — **7** · `L-CELL` — **11** · `S2.1` — **15**.

**TEETH:** the whole chain is what `jb_cread` computes end-to-end on both sides. **JB-PE1 re-derived all five displayed lines; JB-PE2 confirmed them; JB-PE3 re-matched `ε′` VERBATIM against [RMG] S0.2 a second time.** Disposition: **executable regression + three independent hostile re-derivations**.

---
### EFF.GRTJB.130  [scope record]  the degenerate branch (`v = 0`)

**CANONICAL STATEMENT:** verbatim, lines 2244–2251.
**FORM:** bold-headed paragraph.

> “**The degenerate branch (v = 0), displayed.** There ρ_m(f) = ε_m(λ)·v = 0
> by (VD-m) at f, and (C-READ) gives only the TARGET-read vanishing
> R_{m,λ+γ_{m+1}}(R) = 0; R's OWN weight can sit strictly above λ + γ_{m+1}
> with a nonzero own-side print residual, so the ρ-form identity is NOT
> claimed at v = 0 — the transport there is the read-at-target statement
> (0 = 0) only. This stratum split is the theorem's own scope, not a gap;
> the runner scores v ≠ 0 rows and censuses the v = 0 rows (checking
> ρ_m(f) = 0 on them, which does hold).”

**CONDITIONALITY:** **The ρ-form is explicitly NOT CLAIMED at `v = 0`.** The reason is displayed and is a real mathematical obstruction: `R`'s own weight can sit strictly above `λ+γ_{m+1}` with a nonzero own-side print residual, so the pinning step of `.129` fails.

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies this branch **GOOD SEPARABILITY/DEGENERACY BOOKKEEPING** under H5: *“The drainage branch is explicitly fenced rather than silently cancelled through a possibly zero residual.”* No edit; recorded.

**DERIVATION:** Displayed: `(VD-m)` at `f` with `v = 0` gives `ρ_m(f) = 0`; `(C-READ)` gives only the target-read vanishing.

**RESOLUTION TRACE:** statement lines 2244–2251; matrix row 22 at 316 (shard 1); the census 2546–2547 (shard 3: “**v = 0 stratum: 0 occurrences; R = 0: 0**”).

**TEETH:** **`NONE` — machine UNEXERCISED (v = 0 census: 0 rows).** Disposition: **signed vacuity disclosure**. **This is one of the note's four frontier cells** — and the only one whose emptiness is a property of the roster rather than of the instruments.

---
### EFF.GRTJB.131  [changes-record]  (JB-CREAD — the struck grade line)

**CANONICAL STATEMENT:** verbatim, lines 2253–2260.
**FORM:** struck grade line with a nested `[r1, F1]` rider.

> “~~Grade: PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0} **[r1, F1 —
> the perimeter spelled out: (VD-m) is free only at m ≤ 1; at every m ≥ 2 it is
> a HYPOTHESIS (JA-VDIND's collapse condition, ⊇ (R-coll) at m ≥ 3), so
> JB-CREAD has no unconditional stratum above m = 1. The theorem is
> hypothesis-guarded and its algebra is untouched by this correction — JB-PE1
> re-derived all five displayed lines and the verbatim ε′ match against [RMG]
> (C-READ) — what was wrong in r0 was the advertised SIZE of the perimeter]**;
> the ingredient grades ride ([RMG] ACCEPTED; J-A/W-2 attempt).~~”

**CONDITIONALITY:** **STRUCK and superseded by surface 5** (`.132`). Its content survives there. **The sentence “what was wrong in r0 was the advertised SIZE of the perimeter” is the note's own cleanest summary of the F1 defect class** and is repeated at surface 5.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 2253–2260; the superseding surface 2262–2291 (`.132`).

**TEETH:** carried by `.127`.

---
### EFF.GRTJB.132  [TABLE]  ★ SURFACE 5 of 14 — the §5 `∎ GRADE` block

**CANONICAL STATEMENT:** verbatim, lines 2262–2291.
**FORM:** bold-headed bracketed block + fixed-width per-fence display + a closing provenance paragraph.

> “**[r3, STEP 2 — SURFACE 5 of 14, REGENERATED FROM §0M rows 19–23. GRADE:
> PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0}. PER FENCE:**
>
>     (VD-m)     unconditional at m ≤ 1 ONLY ((VD-1) = W2-L3); at every m ≥ 2 a
>                HYPOTHESIS — JA-VDIND's ABSOLUTE character-triviality
>                (⊇ (R-coll)/per-digit at m ≥ 3, JA-BOX-2) — so JB-CREAD has NO
>                unconditional stratum above m = 1. Required at BOTH f and R.
>                                                                  [row 21]
>     v ≠ 0      the non-degenerate read stratum. The v = 0 branch is the
>                read-at-target statement (0 = 0) only, the ρ-form is NOT claimed
>                there, and it is machine UNEXERCISED (v = 0 census: 0 rows).
>                                                                  [row 22]
>     key perim. NONE — §5's print-side content enters ONLY through the (VD-m)
>                hypothesis, so the theorem is a legitimate conditional at any
>                level. Disclosure, not a fence: the instrument cuts reduction
>                levels at `qcap_of(T,G)` and the off-perimeter counter is 0 on
>                the roster.                                 [rows 21/22, ⟨n5⟩]
>     u ≥ 0      NOT consumed — LEMMA JB-EPS cites JA-GRID(c), which carries no
>                proviso.                                            [row 19]
>     [RMG]      (C-READ) + (C-W_R) + the COMPLETE Ĉ_m clause list (restored in
>                r3, F-5) + L-CELL(i)/(ii) = (B-READ), on [RMG]'s own scope
>                (T-scope(m), g_m = 1).                        [rows 20, 21]
>     JB-EPS     UNCONDITIONAL at every m ≥ 1; its application at (λ, γ_{m+1}) is
>                LICENSED by the restored (Ĉ-wt) (r3, F-5).    [rows 19, 20]
>
> **The ingredient grades ride ([RMG] ACCEPTED; J-A / W-2 / LED-Λ at attempt).
> The theorem is hypothesis-guarded and its algebra is untouched by every
> correction in this arc: JB-PE1 re-derived all five displayed lines, JB-PE2
> confirmed them, and JB-PE3 re-matched ε′ VERBATIM against [RMG] S0.2 a second
> time. What was wrong in r0 was the advertised SIZE of the perimeter.]**”

**Double-emission (rule 14) — the same display as a `[TABLE]`:**

| fence | content | generating row(s) |
|---|---|---|
| **(VD-m)** | free at `m ≤ 1` ONLY; a HYPOTHESIS at every `m ≥ 2`; **NO unconditional stratum above `m = 1`**; **required at BOTH `f` and `R`** | row 21 |
| **`v ≠ 0`** | the non-degenerate read stratum; the `v = 0` branch is read-at-target only, ρ-form NOT claimed, **machine UNEXERCISED (0 rows)** | row 22 |
| **key perimeter** | **NONE** — a legitimate conditional at any level; the instrument's `qcap_of` cut is a **disclosure, not a fence**; off-perimeter counter **0** | rows 21/22, ⟨n5⟩ |
| **`u ≥ 0`** | **NOT consumed** — JB-EPS cites JA-GRID(c), which carries no proviso | row 19 |
| **[RMG]** | (C-READ) + (C-W_R) + the COMPLETE Ĉ_m clause list (restored r3/F-5) + L-CELL(i)/(ii) = (B-READ), on T-scope(m), `g_m = 1` | rows 20, 21 |
| **JB-EPS** | UNCONDITIONAL at every `m ≥ 1`; its application at `(λ, γ_{m+1})` LICENSED by the restored `(Ĉ-wt)` | rows 19, 20 |

**CONDITIONALITY:** **A REGENERATION of §0M rows 19–23.** **E-1 re-reads the “(R-coll)” label** in the (VD-m) row. **The “J-A / W-2 … at attempt” clause is STALE** — the 2026-08-08 annex re-grades both to ACCEPTED at 2/2; **LED-Λ's attempt grade is NOT stale and still rides**.

**ARITHMETIC AUDIT (rule 22):** generating rows cited = 19, 20, 21, 22 → **4 distinct rows.** The surface header says “rows 19–23”, i.e. **5 rows** — **row 23 (JB-BOX-1) is named in the header but appears in NO fence line of the surface.** Row 23 is JB-BOX-1's own row and is graded at `.135` instead, so nothing is lost; but the header's range over-states by one. **Recorded as source defect 2 in §8 — a range-label off-by-one, no fence missing, no cell moved.** Fences listed = 6; each cites at least one row; rows 19–22 each appear at least once ✔.

**DERIVATION:** Regeneration from the matrix.

**RESOLUTION TRACE:** statement lines 2262–2291; generating rows 313–317 (shard 1 `.20`); correction sites 3125–3133 (E-1), 3148–3161 (supplier grades).

**TEETH:** row 21 IND (104 scored / 21 boundary); **row 22 NONE (unexercised)**; row 19 IND (955); row 20 a strided spot-check (4 of 56).

---
### EFF.GRTJB.133  [instrument-record]  (JB-CREAD — the unit hygiene note and the machine bracket)

**CANONICAL STATEMENT:** verbatim, lines 2291–2301.
**FORM:** bracketed hygiene note + machine display.

> “**[r1,
> hygiene] τ_m is a unit because c_m = ψ_{m,0} ≠ 0 (the class pin: ψ_j monic
> irreducible with ψ_j(0) ≠ 0, [ILN]† S0.1 / J-A §1, enforced in the engine's
> ψ search) and ε_m(γ_{m+1})^{−1} is a unit — r0 asserted the unit property
> without the citation.** [Machine: JB-CREAD — both
> sides computed end-to-end (print residuals by the sealed GmnLeg
> transcription, harness division/reads by ITL, τ/ε′ by fresh integers) with
> the (VD-m) instances at f and R MACHINE-EVALUATED per row: scored where
> they hold, boundary census disclosed; JB-CM — c_m = ψ_{m,0} and
> embed_{K_{m+1}}(c_m) = −z_{m+1}; teeth MJB-CREAD — the spurious-carry
> reading ρ_m(R) = z_m^{ε′}·c_m·ρ_m(f) must FAIL on designated ε′ ≥ 1 rows.]”

**SUPERSESSION KIND:** `inventory completion` — a unit property asserted without its citation, cited.

**CONDITIONALITY:** **`τ_m` a unit is a load-bearing step of `.129`** (it is what makes the target read nonzero), and it rests on the class pin `ψ_j(0) ≠ 0`. **The (VD-m) instances are MACHINE-EVALUATED per row** — the instrument does not assume the hypothesis, it checks it and censuses the rows where it fails. **That design is why the F1 refutation was available from the note's own runner.**

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies the class pin **BENIGN** under H1/H5: *“‘ψ_j monic irreducible with ψ_j(0) ≠ 0’ — **BENIGN.** The proof uses irreducibility to obtain a field and ψ_j(0) ≠ 0 to make the residual letter a unit. **It never invokes “irreducible implies separable”** … no step excludes inseparable polynomials such as `x^p − t` by a false characteristic-zero argument.”* No edit; recorded.

**DERIVATION:** The class pin ([ILN]† S0.1 / J-A §1) gives `ψ_j(0) ≠ 0`, hence `c_m = ψ_{m,0} ≠ 0`; `ε_m(γ_{m+1})^{−1}` is a unit by construction of the ε-kit.

**RESOLUTION TRACE:** statement lines 2291–2301; consumed at 2224–2225 (`.129`'s second step); the §7.1 rows 2489, 2488 (shard 3).

XREF: `ITERLAWN_PROOF_2026-08-08.md:S0.1` — **13**.

**TEETH:** `jb_cread` (79 samples GREEN), `jb_cm` (28 rows GREEN), **MJB-CREAD** (planted spurious carry — 22 designated samples over 14 towers, **all caught**, fired).

---
### EFF.GRTJB.134  [fence]  ★ the carry seed — the J-C germ, fenced

**CANONICAL STATEMENT:** verbatim, lines 2303–2308.
**FORM:** bold-headed remark.

> “**Remark (the carry seed; fence).** ρ_m(R) = −z_{m+1}·ρ_m(f) in K_{m+1}:
> on twisted residual reads, multiplication by the canonical correction
> digit IS multiplication by the negative of the classifier's next residual
> letter. This is the semantic germ the J-C carrier block (W-6..W-9) needs —
> displayed here as an identity of READ VALUES only; no graded-ring (gr)
> object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.”

**CONDITIONALITY:** **Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence in full.** §7.3's downstream notice (shard 3) says so explicitly: “the J-C germ (ρ_m(R) = −z_{m+1}·ρ_m(f), §5's remark) inherits the same conditionality above m = 1.”

**★ THE J-C INTERFACE, and the merge must carry it.** This is the ONE place GRTJB touches the J-C block, and it is fenced three ways: **(i)** the identity is of READ VALUES only; **(ii)** no gr object is constructed or claimed; **(iii)** BLOCKED-ON-CARRIER-TIE stands. **GRTJC's `(IN-4)` records the inheritance from the other side** — “§5's germ display cites J-B's JB-CREAD + JB-EPS and inherits their fences verbatim” — and GRTJC's §3.3 consumes the value law with J-B's `g_m = 1` fence honoured: “on all **27 eligible (g_m = 1) stages**, val(Ĉ_m) = −z̄ = −z_{m+1} exactly”, while **REFUTING the brief's guess that this letter is OB-3's inner factor** (H-D fails on 138/669 pairs).

**DERIVATION:** `.129`'s conclusion `ρ_m(R) = c_m·ρ_m(f)` composed with `.124`'s `c_m = ψ_{m,0} = −z_{m+1}`.

**RESOLUTION TRACE:** statement lines 2303–2308; the conclusion 2212 (`.127`); the constant 2146–2150 (`.124`); the downstream notice 2658–2665 (shard 3); the standing block 2439–2442 (`.141`).

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JB-CREAD` — grep-verified count **2** (the consumer's own citation of this note — a REVERSE edge). `GRTJC_PROOF_2026-08-08.md:JB-EPS` — count **4**. `GRTJC_PROOF_2026-08-08.md:JB-BOX-2` — count **3**. `GRTJC_PROOF_2026-08-08.md:JB-BOX-4` — count **2**.

**TEETH:** inherits `.127`/`.128`'s legs; the germ itself is not separately keyed. Disposition: **inherited**, with the gate explicitly NOT retired.

---
### EFF.GRTJB.135  [changes-record]  JB-BOX-1 — the blueprint carry placement, corrected

**CANONICAL STATEMENT:** verbatim, lines 2314–2321.
**FORM:** bold-headed bullet.

> “* **JB-BOX-1 (blueprint correction, review-owed).** Blueprint J-B(iii)
>   displays the classifier transport WITH the carry ("shifts the
>   CLASSIFIER's residual read by τ_m with the level-m EPS-carry z_m^{ε′}").
>   CORRECTED: in the print's twisted coordinates the carry cancels
>   (THEOREM JB-CREAD); the shift constant is c_m (not τ_m), and the
>   τ_m-with-carry form is the HARNESS-frame statement ([RMG] (C-READ)).
>   The blueprint display conflated the two frames; both are displayed
>   above with the coordinate change (JB-EPS) between them.”

**TYPE JUSTIFICATION (rule 13):** in substance a `supplier-finding` — a defect report against the GRT weld blueprint, **REVIEW-OWED at the source**. Filed `[changes-record]` because the note boxes it as its own correction. **Flagged for the merge run** (same disposition as shard 1 `.36`).

**CONDITIONALITY:** Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence (matrix row 23). **Two distinct errors are named: the wrong CONSTANT (`c_m`, not `τ_m`) and the wrong FRAME (the carry-bearing form is harness-side).**

**DERIVATION:** `.129`'s chain, in which `z_m^{−ε′}·z_m^{ε′}` cancels by LEMMA JB-EPS.

**RESOLUTION TRACE:** statement lines 2314–2321; proof lines 2236–2242 (`.129`); the grade-cap bullet 510–514 (shard 1 `.36`); matrix row 23 at 317 (shard 1).

**TEETH:** **teeth MJB-CREAD — “the carry-bearing reading must FAIL, and does, on all 22 designated samples over 14 towers”.** A planted mutant that fired; the note's strongest single tooth, and the one that converts a display correction into a machine-load-bearing fact.

---
### EFF.GRTJB.136  [fence]  ★ JB-BOX-2 — inherited conditionality, quantified (and SURFACE 14)

**CANONICAL STATEMENT:** verbatim, lines 2322–2420. Because the box spans 99 lines with five nested correction layers, it is quoted in **three contiguous blocks**, each complete and byte-verbatim; the union is the whole box minus nothing.

**FORM:** bold-headed bullet with nested `[r1]`/`[r2]`/`[r3]`/`[r5]`/`[r7]` riders and an embedded fixed-width enumeration (SURFACE 14 of 14).

**BLOCK A — the (VD-m) re-fence (lines 2322–2340):**

> “* **JB-BOX-2 (inherited conditionality, quantified).** Every print-residual
>   statement rides J-A's boxes verbatim: ~~the (VD-m)/per-digit proviso at
>   m ≥ 3 (JA-BOX-2 — (R-coll) sufficient, converse unsealed)~~ **[r1, F1 —
>   RE-FENCED, this was the mis-scoped line: the (VD-m) conditionality bites
>   from m = 2 UP, not from m = 3. Correct statement: (VD-1) = W2-L3 is free;
>   at EVERY m ≥ 2 (VD-m) is conditional on JA-VDIND's absolute
>   character-triviality on the attained abscissas; at m ≥ 3 that is the
>   per-digit proviso / (R-coll) box JA-BOX-2 ((R-coll) sufficient, converse
>   unsealed); at m = 2 it is ~~the e₀ ≥ 2 / nontrivial-z₁ boundary~~ **[r2,
>   G2-4 — RE-WORDED: JA-VDIND's absolute character-triviality condition
>   ITSELF, with no known characterisation. The only implication available is
>   e₀ = 1 ⇒ A_1 = 0 ⇒ the condition holds; e₀ ≥ 2 is therefore NECESSARY for an
>   m = 2 failure but is NOT sufficient (T3E, e₀ = 2, scores 6/6)]**, where the
>   sealed runner exhibits 10 in-roster FALSE instances of (VD-2). So the
>   boundary geography of §7.1 is the JA-VDIND collapse condition at m = 2 plus
>   JA-BOX-2's box at m = 3 — r0 attributed all of it to JA-BOX-2]**, the
>   unpinned-ℓ orbit (JA-BOX-3: all displays at the pinned (P-ell)
>   representative; §4.3-orbit transport per J-A §4(ii)), and W-2's
>   (C-coll)/recursion split for the byte law.”

**BLOCK B — the `u ≥ 0` proviso, carried and narrowed (lines 2340–2373):**

> “**[r1, G-5 — one inherited
>   proviso that is NOT one of JA-BOX-1..5 and rode in uncarried in r0:
>   JA-GRID(a)'s `[JA-r1]` repair proviso u := (V − s·h)/e ≥ 0 … It is consumed by §2(iii)'s
>   (GRID) layer and is hereby CARRIED BY THIS BOX, ~~with the discharge stated
>   at §2(iii) …~~ **[r2, G2-5 — THE DISCHARGE IS
>   RETRACTED … STATUS: CARRIED,
>   DISCHARGE OWED. Every statement consuming §2(iii)(GRID) — JB-DEV(iii)'s
>   (GRID) layer and, through it, the grid/abscissa content of JB-VTX(d) — is
>   conditional on this proviso in addition to its other fences. A real discharge
>   must derive u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 — ~~equivalently~~
>   **[r3, F-6(a) — "equivalently" WITHDRAWN here as at the r2 block's G2-5
>   bullet: the genuine equivalence is u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}, while J-A's
>   print bound is SUFFICIENT only. Read: **for which it SUFFICES to derive** —]**
>   V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) in J-A's own form, for EVERY V in the
>   quantified window with units included; see the retraction block at §2(iii)
>   for what is and is not known (V = 0 gives u = 0, so units are not a
>   counterexample; ~~J-A's own (e,h) = (2,3), V = 1 ⇒ u = −1 is not excluded by
>   anything this note says~~ **[r5, F-3 — struck as STALE against r4's own
>   definition: the lattice 𝒲_m of §5 EXCLUDES J-A's instance by parity, and
>   u ≥ 0 is PROVED on ALL of 𝒲_m there (machine-confirmed). What remains open
>   at the two consuming rows (4 and 12) is ~~exactly~~ **[r7, PE7 m-2 —
>   "exactly" struck as overstating necessity, the same defect r6 struck at
>   §0M column (b): membership is the SUFFICIENT hypothesis the note CARRIES
>   (and at m = 1 it is moreover EQUIVALENT to the needed u ≥ 0 instance —
>   column (b), r7/F-1)]** lattice MEMBERSHIP at their
>   unbounded-degree quantifiers (V = w_{q+1}(f), f of any degree): it holds by
>   definition at deg f < deg Φ_{q+1} — where the proviso is DISCHARGED — and
>   is not established off it. §0M column (b)]**).]** JA-GRID(c) — the carry clause
>   LEMMA JB-EPS consumes — carries NO proviso and is unconditional.]**
>   ~~**[r1, G-9]** The (VAL)/(GRID)/(RES) layers and all of JB-VTX are
>   quantified on the SHARED-KEY perimeter q ≤ qcap …~~”

**BLOCK C — SURFACE 14 of 14, the perimeter enumeration (lines 2379–2420):**

> “  **[r3, STEP 2 — SURFACE 14 of 14: THIS BOX'S PERIMETER ENUMERATION,
>   REGENERATED FROM §0M. The struck r1/G-9 sentence had two defects PE3 named:
>   it omitted JB-TREE(iii)/(iv) (F-1B …), and it put all three
>   layers of §2(iii) on ONE perimeter (F-4). THE COMPLETE ENUMERATION, which is
>   §0M's columns (a1)/(a2) read down:**
>
>     on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap; J-A grades JA-VAL on it,
>     and off it the print frame is a different object):
>         §2(iii)(VAL) and §2(iii)(GRID)                      [rows 3, 4]
>         JB-VTX — (a), (b), (c), (d1)/(d2), (d4), and (e) through
>         (a) at f = Φ_{q+1}^har (r6, F-1: (d3) MOVED to the `P≤q` list
>         below; "ALL of JB-VTX" is no longer true of this line)
>                                                           [rows 8–13]
>         JB-TREE(iii) and JB-TREE(iv), read at level m       [rows 17, 18]
>     on the BYTE-EQUAL CHAIN THROUGH q `P≤q` (strictly stronger; the difference
>     bites at q = qcap only where shared_upto < n — 5 of the 16 roster towers;
>     on the other 11 the two fences coincide over the whole range, r4/F-3):
>         §2(ii)'s byte clause                                    [row 2]
>         §2(iii)(RES) — added in r3, F-4                         [row 5]
>         JB-VTX(d3) — JA-VAL at level q+1; added in r6, F-1
>                                                         [row 11 (a2)]
>     on NO key perimeter:
>         §2(i), §2(iv), JB-AFF, JB-ID, JB-TREE(i), JB-TREE(ii), JB-EPS,
>         JB-CREAD (a legitimate conditional at any level; its instrument's own
>         level cut is disclosed at §5 and §7.1)
>                                                 [rows 1, 6, 7, 14–16, 19–22]
>
>   **And the u ≥ 0 proviso of this box reaches EXACTLY TWO claims: §2(iii)(GRID)
>   (row 4) and JB-VTX's clause (d4) — the attained-abscissa/read-grid tie, which
>   is also the ONE sub-clause of JB-VTX with no machine leg (row 12, r3/F-3).
>   No other statement in this note consumes JA-GRID(a). And the (VD-m) fence,
>   recorded by this box [r4, F-7 — this box carried rows 21/22 only and omitted
>   row 18's rider]: it reaches EXACTLY rows 18 (JB-TREE(iv)'s (C-READ) leg,
>   which transports as §5 and rides the fence IN FULL), 21 and 22 (JB-CREAD,
>   both strata) and 23 (JB-BOX-1) — §0M row 24's (c) cell, synced with summary
>   point (4).]**
>   JB-CREAD's own stratum
>   split (v ≠ 0 scored; v = 0 = the read-at-target branch only, ρ-form
>   not claimed) is displayed at the theorem. W2-OPEN-1 (the value layer
>   on transported lifts) is consumed NOWHERE (independently re-verified in
>   JB-PE1: no §2–§5 statement touches W-2 §5.3's K5/K6/K7/K12 battery).”

**Double-emission (rule 14) — SURFACE 14's enumeration as a `[TABLE]`:**

| fence | statements | generating rows |
|---|---|---|
| **`P<q`** (SHARED-KEY PERIMETER, `0 ≤ q ≤ qcap`) | §2(iii)(VAL), §2(iii)(GRID); JB-VTX (a), (b), (c), (d1)/(d2), (d4), (e) through (a) at `f = Φ_{q+1}^har`; JB-TREE(iii), JB-TREE(iv) read at level `m` | 3, 4, 8–13, 17, 18 |
| **`P≤q`** (BYTE-EQUAL CHAIN THROUGH q; bites at `q = qcap` only where `shared_upto < n`, 5/16 towers) | §2(ii)'s byte clause; §2(iii)(RES) *(added r3/F-4)*; JB-VTX(d3) *(added r6/F-1)* | 2, 5, 11(a2) |
| **NO key perimeter** | §2(i), §2(iv), JB-AFF, JB-ID, JB-TREE(i), JB-TREE(ii), JB-EPS, JB-CREAD | 1, 6, 7, 14–16, 19–22 |
| **`u ≥ 0` proviso — EXACTLY TWO** | §2(iii)(GRID); JB-VTX(d4) | 4, 12 |
| **(VD-m) fence — EXACTLY FOUR** | JB-TREE(iv)'s (C-READ) leg; JB-CREAD `v ≠ 0`; JB-CREAD `v = 0`; JB-BOX-1 | 18, 21, 22, 23 |

**CHAIN (rule 25):** BLOCK B is body site C of the `u ≥ 0` chain; **CHAIN HOME §0M column (b)** (shard 1 `.14`); `CHAIN-MEMBER: .14 positions 1–4 (body site C — the box)`. **r7/m-2 is the THIRD site of the “exactly” overclaim**, reached only after the r6 sweep (which took a verifier's two-site quote list as its universe) missed it.

**SUPERSESSION KIND:** `replacement` (r1/F1's re-fence), `counter re-reading` (r2/G2-4's mechanism strike; r7/m-2's “exactly”), `replacement` (r2/G2-5's retraction), `wording-rider` (r3/F-6(a)), `scope-pin` (r5/F-3), `inventory completion` (r3's SURFACE 14 and r4/F-7's row-18 rider).

**ARITHMETIC AUDIT (rule 22) — computed fresh against the transcribed matrix (shard 1 `.20`):**
- **`P<q` rows** listed = 3, 4, 8, 9, 10, 11(a1), 12, 13, 17, 18 → **10 statements** ✔ matches column (a1)'s non-blank rows exactly.
- **`P≤q` rows** listed = 2, 5, 11(a2) → **3** ✔ matches column (a2) and summary point (2)'s r6 recount.
- **No-perimeter rows** listed = 1, 6, 7, 14, 15, 16, 19, 20, 21, 22 → **10** ✔ (rows 19–22 named as a range; row 20 is JB-EPS's application, correctly perimeter-free).
- **Coverage check:** 10 + 3 + 10 = **23 claim rows**, and rows 24–28 are the five RECORD rows, so **23 + 5 = 28** ✔ **the enumeration is EXHAUSTIVE over the matrix with no row counted twice** (row 11 appears once per sub-column, which is the r6 split).
- **`u ≥ 0` = EXACTLY TWO (rows 4, 12)** ✔ matches column (b).
- **(VD-m) = rows 18, 21, 22, 23** ✔ matches summary point (4) as rewritten at r4/F-1 — and carries the same row-23 classification overlap flagged as shard 1's source defect 3.

**CONDITIONALITY:** **This box is the note's single conditionality inventory for a downstream consumer, and it is SURFACE 14 of 14 — a regeneration, not an authority.** `W2-OPEN-1` consumed NOWHERE is a NON-IMPORT, independently re-verified in JB-PE1.

**DERIVATION:** Regeneration from §0M columns (a1)/(a2)/(b)/(c) read down.

**RESOLUTION TRACE:** statement lines 2322–2420; generating columns 189–276 and rows 293–322 (shard 1 `.12`–`.20`); dispositions 638–659 (r1/F1), 680–684 (r1/G-5), 792–819 (r2/G2-4, G2-5), 908–911 (r3/F-6(a)), 1015–1020 (r4/F-7), 1053–1073 (r5/F-3), 1096–1101 (r5/F-5), 1250–1258 (r7/m-2) — all shard 1.

XREF: `GRTJA_PROOF_2026-08-08.md:JA-BOX-3` — **3** · `JA-VDIND` — **21** · `JA-BOX-2` — **7** · `(R-coll)` — **7**. `GRTW2_PROOF_2026-08-08.md:(C-coll)` — **27** · `W2-OPEN-1` — **10** · `W2-L3` — **5**.

**TEETH:** the box is a record (matrix row 24, `n/a`). **r5/F-5 audited the box against its own record cell and found row 24's (d) cell asserting a W2-C1 record the box does NOT carry** — an **AUDIT: arithmetic recount** finding (“Grep-verified this round: the box's full extent has NO W2-C1 record”).

---
### EFF.GRTJB.137  [fence]  JB-BOX-3 — the cross-key fence

**CANONICAL STATEMENT:** verbatim, lines 2421–2426.
**FORM:** bold-headed bullet.

> “* **JB-BOX-3 (cross-key fence).** No cross-representative operator or
>   byte identity is claimed anywhere (JB-DEV(iv)); transport across
>   representatives is W-2 clause 2/3 covariance only. The JuncForge
>   parity-wall lesson is honored structurally: every §2–§5 statement is
>   against the semantic development/polygon/tree/read objects; SideReads/
>   TreeModel are consumed nowhere.”

**CONDITIONALITY:** A NON-IMPORT record (matrix row 25). **Its “no byte identity is claimed anywhere” is what E-4 relies on when it separates a proof-license boundary from a semantic negation** (`.95`).

**DERIVATION:** Declaration; discharged by the note's architecture (every statement is against semantic objects at a NAMED representative).

**RESOLUTION TRACE:** statement lines 2421–2426; the clause it records 1539–1547 (`.95`); matrix row 25 at 319 (shard 1); E-4's consistency 3282–3286 (shard 3).

**TEETH:** `n/a (record)`. Disposition: **signed non-applicability**.

---
### EFF.GRTJB.138  [fence]  JB-BOX-4 — tree scope, and the LED-Λ decorrelation

**CANONICAL STATEMENT:** verbatim, lines 2427–2433.
**FORM:** bold-headed bullet.

> “* **JB-BOX-4 (tree scope).** JB-TREE inherits [RMG]'s fences verbatim:
>   termination on T-scope(m) (d₀ = 1 ∨ non-degenerate below top; the
>   d₀ ≥ 2 flat corners stay FENCED and are quantified over nowhere here);
>   g_m = 1 for the Ĉ_m instance; W-WIN consumed by nothing. LED-Λ is
>   ATTEMPT grade (acceptance counter 0) — the §4(iii) citation's grade
>   rides it, and the runner therefore re-verifies the λ_E quanta FRESH
>   rather than trusting the ledger (decorrelation, not redundancy).”

**CONDITIONALITY:** **LED-Λ's ATTEMPT grade is LIVE at HEAD** — the 2026-08-08 supplier annex upgrades W-2 and J-A but **not** LED-Λ. So `.114`'s grade rider stands, and the box's mitigation (fresh re-verification) is the operative decorrelation. **The `d₀ ≥ 2` flat corners are quantified over NOWHERE**, and `W-WIN` is consumed by nothing — two NON-IMPORTS.

**DERIVATION:** Declaration; the decorrelation claim is discharged by `jb_line`'s FRESH per-edge λ_E recomputation.

**RESOLUTION TRACE:** statement lines 2427–2433; the citation 1853–1897 (`.114`); matrix row 26 at 320 (shard 1); the supplier annex 3148–3161 (shard 3, which does NOT name LED-Λ).

XREF: `RMENGINE_2026-08-08.md:T-scope` — **42** · `W-WIN` — count **9** (verified in RMENGINE, the note that fences it; count **0** in GRTW2 — the designation is [RMG]'s, and GRTJB cites it as such).

**TEETH:** `n/a (record)` — “the FRESH λ_E re-verification of row 17 is the decorrelation this box claims”. Disposition: **accepted-with-decorrelation-supplied** for the LED-Λ grade rider.

---
### EFF.GRTJB.139  [fence]  JB-BOX-5 — the instance perimeter

**CANONICAL STATEMENT:** verbatim, lines 2434–2438.
**FORM:** bold-headed bullet.

> “* **JB-BOX-5 (instance perimeter).** Machine evidence = the §7 roster
>   (16 towers, reads ≤ 4 + top, residue fields ≤ F₉ + F₈/F₂₅ via the d₀
>   leg; 5 QO shapes; 4 fresh d₀ ≥ 2 shapes); F_p[[t]] rows have no PARI
>   leg (JA-BOX-4 inherited); mixed-characteristic print, equal-char rows
>   ride construction-identity + machine only.”

**CONDITIONALITY:** **This is the proof-scope-vs-machine-scope fence**, and the F_p[[t]] clause is the one Q7 examines. **The theorems are at general `q`/`m`; the evidence is a 16-tower roster + 5 QO + 4 d₀ shapes.**

**GENERALITY NOTE (Q7, recorded not applied).** Q7 classifies this row **EVIDENCE-ONLY, NOT A THEOREM RESTRICTION**: *“‘evidence caveat: `F_p[[t]]` rows have NO external (PARI) oracle leg’ — **EVIDENCE-ONLY, NOT A THEOREM RESTRICTION.** Equal-characteristic rows lack one oracle but the symbolic proof does not use that oracle.”* And under H2/H4 Q7 records **NO HIT** for the whole note: *“No occurrence of `v(p)`, an Eisenstein polynomial in `p`, Teichmüller/Witt arithmetic, or an unramified-`ℤ_p` decomposition is load-bearing.”* No edit; recorded.

**DERIVATION:** Declaration of the evidence perimeter.

**RESOLUTION TRACE:** statement lines 2434–2438; the roster 2477–2492 and 2522–2528 (shard 3); matrix row 27 at 321 (shard 1).

XREF: `GRTJA_PROOF_2026-08-08.md:JA-BOX-4` — **4**.

**TEETH:** `n/a (record)` — **evidence caveat: F_p[[t]] rows have NO external (PARI) oracle leg** (JA-BOX-4 inherited). Disposition: **signed vacuity disclosure** on the oracle leg for equal-characteristic rows.

---
### EFF.GRTJB.140  [fence]  ★ JB-BOX-6 — standing fences and the §0M governance rule

**CANONICAL STATEMENT:** verbatim, lines 2439–2454.
**FORM:** bold-headed bullet with an `[r3]` procedural addition and an `[r4, F-7]` narrowing.

> “* **JB-BOX-6 (standing fences).** No gr/carrier claim (J-C untouched;
>   BLOCKED-ON-CARRIER-TIE stands); no count/menu/density claim (J-D
>   untouched); the P0 application gate stands; acceptance counter 0/2 —
>   nothing here may be consumed at proof grade before its hostile arc.
>   **[r3 — and one procedural fence, added by this round: the COMPLETE
>   conditionality of every claim in this note is §0M's matrix. A consumer who
>   reads a grade surface (the grade cap, any ∎ Grade line, any §7.2 row, §7.3,
>   or ~~any box~~ **[r4, F-7 — narrowed to the inventory that is true:
>   JB-BOX-2, the ONE box regenerated from the table (surface 14); JB-BOX-1 and
>   JB-BOX-3/4/5 and this box are standing records — consistent with the table
>   as checked, but NOT regenerations of it]**) is reading a REGENERATION of
>   that table; if a surface and the
>   table ever disagree, THE TABLE GOVERNS and the disagreement is a defect to
>   report. Any future repair round that adds or moves a fence must edit §0M
>   first and re-derive the 14 surfaces from it — the per-site sweep genre that
>   produced PE1/G-9, PE2/G2-1 and PE3/F-1 + F-1B is retired.]**”

**SUPERSESSION KIND:** `scope-pin` (r4/F-7 narrows “any box” to the one box that is actually a regeneration).

**CONDITIONALITY:** **THIS UNIT IS FREEZE PREDICATE 2 IN ITS OPERATIVE FORM.** “**THE TABLE GOVERNS**” is the note's governance rule and the reason `.97`, `.107`, `.117`, `.132` and `.136` are labelled REGENERATIONS. **STALE-SELF-DESCRIPTION (rule 26) on two clauses:** “acceptance counter 0/2” and “nothing here may be consumed at proof grade before its hostile arc” are falsified by the acceptance record (ACCEPTED at 2/2, PE9 + PE10) — **and, unlike GRTJC, GRTJB has NO annex expressly superseding them** (shard 1 OPEN-CALL 4). The four negative fences (no J-C claim, no J-D claim, P0 stands, BLOCKED-ON-CARRIER-TIE stands) remain LIVE.

**DERIVATION:** Declaration + a procedural rule.

**RESOLUTION TRACE:** statement lines 2439–2454; the matrix 171–441 (shard 1 `.11`–`.29`); the 14-surface list 885–892 (shard 1 `.55`); the r4/F-7 disposition 1015–1020 (shard 1 `.64`); status superseded — **NOT** superseded; see shard 1 OPEN-CALL 4; the acceptance record 3107–3119 (shard 3).

**TEETH:** `n/a (record)`. The rule's own test is PE4's “**NO fifth instance of the old surface-divergence class**”. Disposition: **AUDIT — in-house hostile pass**.

---
### EFF.GRTJB.141  [run-record]  §7.1 — the sealed verdict headline

**CANONICAL STATEMENT:** verbatim, line 2460.
**FORM:** display (an H3 heading carrying the verdict).

> “### 7.1 Machine bracket — **ALL 18 FAMILIES GREEN, 6,700 samples, 0 violations, every sealed prediction hit exactly** (`grt_jb_checks_output.txt` / `grt_jb_checks_results.json`, elapsed 0.7 s; seal commit 7f6759d)”

**TYPE JUSTIFICATION (rule 19):** `run-record` — an executed instrument's result. The corresponding `preregistration` is the sealed prediction list at commit 1 (`5a72b62`, quoted at `.142`); the `instrument-record` is shard 1 `.41`.

**CONDITIONALITY:** **“every sealed prediction hit exactly” is a claim about the SEALED battery only.** Three separate qualifications live in this same section and must travel with the headline: (a) **one of the 18 families' legs is SAME-COMPUTATION** with an unreachable violation (`.143`); (b) **three of `jb_keyeq`'s 25 rows are VACUOUS** (`.143`); (c) **the boundary census of 21 rows is a DISCLOSURE, not a pass** (`.145`). **The headline is true and the note does not lean on it** — §0M's column (f) is the audited form.

**PIN VERIFICATION (rule 23):** `grt_jb_checks_output.txt` **EXISTS**; `grt_jb_checks_results.json` **EXISTS**; seal commit `7f6759d` → `git cat-file -t` = **commit**; runner md5 **EXACT at HEAD**.

**DERIVATION:** An executed run; not a derivation.

**RESOLUTION TRACE:** statement line 2460; the family table 2477–2492 (`.143`); the seal erratum 2462–2472 (`.142`); the instrument description 595–599 (shard 1 `.41`).

**TEETH:** this unit IS the tooth aggregate. **All four planted-mutant families fired (MJB-DEV / MJB-VTX / MJB-TREE / MJB-CREAD, 3/3 rows each, all caught)** — so the battery is demonstrably capable of failing.

---
### EFF.GRTJB.142  [changes-record]  the SEAL-RECORD ERRATUM (r1/G-8)

**CANONICAL STATEMENT:** verbatim, lines 2462–2475.
**FORM:** bold-headed bracketed block.

> “**[r1, G-8 — SEAL-RECORD ERRATUM (the commit message is immutable; the note
> carries the correction).** Seal commit `7f6759d`'s message says "note +
> runner sealed with preregistered predictions", but that commit contains ONLY
> `verification/openmath/grt_jb_checks.py` (990 insertions); the note itself was
> committed one commit EARLIER, at `5a72b62`, with the predictions written in
> prose ("Sealed predictions (commit 1): EXT-GATE 0 · JB-DEV 0 · …"). The seal
> PROPERTY that matters is unaffected and was independently verified in JB-PE1:
> predictions on record before the battery; runner md5
> `55f4911eaddd8524fd91368b30ed71bd` identical at seal, at verdict and at HEAD;
> and `git diff 7f6759d f5578d0` on the note touches §7.1 ONLY — no §1–§6 law
> statement, box or grade moved between seal and verdict. Only the message
> wording was imprecise.]** **[r1] The r1 round did not re-run and did not
> modify this battery; all figures in §7.1 are the sealed ones, with the
> wording corrections marked inline.**”

**SUPERSESSION KIND:** `provenance-rider` — an immutable commit message corrected in the note that cites it.

**CONDITIONALITY:** **The seal PROPERTY is what matters and it is stated in three checkable parts:** (i) predictions on record before the battery; (ii) runner md5 identical at seal, verdict and HEAD; (iii) `git diff 7f6759d f5578d0` on the note touches §7.1 only. **Part (ii) is re-verified EXACT at HEAD by this compiler.** Parts (i) and (iii) are git-history claims about resolvable commits; **not independently re-verified here** — recorded as checkable pins (see source defect 1).

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 2462–2475; the disposition 691–696 (shard 1 `.47` item G-8); the instrument declaration 595–599 (shard 1 `.41`).

**PIN VERIFICATION:** `7f6759d` → **commit**; `5a72b62` → **commit**; `f5578d0` → **commit**; md5 **EXACT**.

**TEETH:** the seal property is itself the tooth; JB-PE1 verified it independently. Disposition: **accepted-with-decorrelation-supplied**.

---
### EFF.GRTJB.143  [TABLE]  ★ §7.1 — the 18-family sealed verdict table

**CANONICAL STATEMENT:** verbatim, lines 2477–2492 — the source table, transcribed row for row with its inline `[rN]` corrections preserved.
**FORM:** display (a Markdown table).

`[TABLE]` **The sealed battery, 18 families.** (Long correction brackets condensed with `…`; each is quoted in full at its own unit in shards 1–2.)

| family | claim keyed | samples | verdict |
|---|---|---|---|
| EXT-GATE | engine_ext pins + agreement gate re-run (standing rule) | 1 | GREEN |
| **JB-DEV** | ~~fresh schoolbook dev == both engines + digit weight ties~~ **[r3, F-2 — RESTATED; “both engines” WITHDRAWN.** `fresh_dev` == `PolyO.dev` (**IND**: one genuine second implementation) + the (VAL) tie `G.vgen(q+1,A) == T.wlev(q,A)` (**IND**: the genuine cross-engine leg). The third leg `G.P.dev` is **SAME-COMPUTATION** — violation UNREACHABLE, carries no information**]** | 893 | GREEN |
| **JB-KEYEQ** | byte census + TH-BASE (~~q = 1 byte-equal on all 25 rows~~ **[r1, G-3]** byte-equal on **22 of the 25**; the other **3 are VACUOUS**: `QO:x3-3/Q3`, `QO:x4+2x2+2/Q2`, `QO:x4-2/Q2` have `T.n = 0`, so the census loop walks nothing and the TH-BASE guard is never exercised) | 25 | GREEN |
| **JB-SHEAR** | ~~pointwise shear + the four min/read ties~~ **[r3, F-3 — RESTATED: pointwise shear + THREE of clause (d)'s four ties** (d1, d2, d3 — (d3) additionally under `q+1 <= G.RANK`, **verified redundant** [r7, m-3]). **The FOURTH tie (d4) is MACHINE-UNKEYED in every family of every instrument — and is also the only sub-clause riding the u ≥ 0 proviso**]** | 893 | GREEN |
| JB-VTX | vertex bijection + per-side slope/length law, fresh hulls | 893 | GREEN |
| JB-ID | (ID-(i+1)) exact + key-dev digits + print-key grid/shear-constancy | 34 | GREEN |
| **JB-TREE** | ~~fresh tree walk == canonical division, harness AND print keys~~ **[r1, G-1]** fresh tree walk == the canonical division **BY THE HARNESS KEY** (one fresh division), plus a byte-equality-gated **RE-EXECUTION** on the print key's bytes (a consistency re-check, **NOT an independent print-key reading**; no print-key check at all off the byte-equal set) | 79 walks (125 with chambers) | GREEN |
| JB-LINE | λ_E quanta per edge + leaf `line == wlev == vgen` | 194 | GREEN |
| JB-EPS | ε-cocycle collapse, integers + field | 955 | GREEN |
| JB-CM | `c_m = ψ_{m,0} = −z_{m+1}` (28 eligible (T, m) rows) | 28 | GREEN |
| JB-CREAD | `ρ(R) = c_m·ρ(f)` + `w_m(R)` pin, scored stratum | 79 | GREEN |
| JB-QO / JB-D0 | 5 concrete shapes / 4 fresh d₀ ≥ 2 shapes (engine_ext) | 5 / 4 | GREEN |
| TW-JB | chamber re-instantiation (all 16 towers, nontrivial ledgers) | 2,480 | GREEN |
| MJB-DEV / MJB-VTX / MJB-TREE / MJB-CREAD | teeth (garbled key / unsheared frame / corrupted correction / spurious carry) | 3/3/3/3 rows | GREEN (all caught) |

**MANDATORY ARITHMETIC AUDIT (rule 22) — computed fresh by this compiler.**
- **Family count.** Table rows = 14 lines, but the last row bundles **four** teeth families and the `JB-QO / JB-D0` row bundles **two**. Expanding: 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + **2** + 1 + **4** = **18** ✔ matches “ALL 18 FAMILIES GREEN”.
- **Sample total.** 1 + 893 + 25 + 893 + 893 + 34 + 79 + 194 + 955 + 28 + 79 + 5 + 4 + 2,480 = **6,563**, plus the four teeth families at 3 rows each = 12 → **6,575**. The headline says **6,700**. **DISCREPANCY of 125.** Note that the JB-TREE row itself reads “79 walks (**125 with chambers**)”: substituting 125 for 79 gives 6,563 − 79 + 125 = 6,609, +12 teeth = 6,621 — still not 6,700. **The headline total is not reconstructible from the table's own sample column.** Recorded as **source defect 2** in §8; the note nowhere claims the column sums to the headline, and the per-family figures are the ones every other surface cites. **Nothing in the note's fences depends on the 6,700.**
- **JB-KEYEQ.** 22 byte-equal + 3 vacuous = **25** ✔.
- **JB-SHEAR ties.** 3 keyed + 1 unkeyed = **4** ✔ matches clause (d)'s four ties.
- **Teeth.** 4 families × 3 rows = **12 tooth rows, all caught** ✔.
- **Cross-check with §7.4(B):** the sealed `tree` block has **8** `byteeq: false` rows (4 base + 4 chamber) per r2/G2-3; JB-TREE's 79/125 walk split is consistent with the walker's 84-walk leg A reaching the 4 base rows (12 walks) and not the 4 chamber rows (8 walks) ✔.

**CONDITIONALITY:** **Three of the eighteen families carry a disclosed defect in their own row** (JB-DEV's SAME third leg; JB-KEYEQ's 3 vacuous rows; JB-TREE's non-independent print-key leg). **All three were found by hostile passes, not by the battery.** The GREEN verdicts stand; what was corrected is what the GREENs MEAN.

**DERIVATION:** Executed run, transcribed from the committed artifacts.

**RESOLUTION TRACE:** statement lines 2477–2492; the three corrections at 898–905 (r3/F-2), 676–677 (r1/G-3), 660–672 (r1/G-1) — all shard 1; the matrix column (f) 270–288 (shard 1 `.18`).

**TEETH:** the four planted-mutant families ARE the teeth and all fired. **Disposition: executable regression with three signed disclosures** — one `stale self-description` (JB-DEV), one `signed vacuity disclosure` (JB-KEYEQ), one `disclosed non-repair` (JB-TREE's print-key leg, repaired post-seal).

---
### EFF.GRTJB.144  [run-record]  §7.1 — the JB-CREAD censuses and the G2-7 decomposition

**CANONICAL STATEMENT:** verbatim, lines 2494–2503 (the census sentence with its `[r2, G2-7]` decomposition).
**FORM:** paragraph with a nested bracketed rider.

> “Censuses (the note's displayed conditionality, quantified): JB-CREAD
> **scored 104 (~~66 roster~~ **[r2, G2-7 — the word "roster" named two
> different sets in this paragraph; the decomposition, recounted from the
> committed sealed JSON, is displayed once here and used consistently:
> NON-CHAMBER 66 = 16-tower ROSTER 56 + QO leg 2 + d₀ leg 8, so the "56 roster
> rows" of the r1 bracket below and this 66 are the same census at two different
> scopes]** non-chamber 66 = roster 56 + QO 2 + d₀ 8, + 38 chamber),
> 0 violations; boundary 21 —
> ALL on the character-visible/interior-twist towers T3A, T3B, T3C, T3D,
> I4B and their transported chambers**, …”

**SUPERSESSION KIND:** `counter re-reading` — one word naming two different sets, decomposed.

**MANDATORY ARITHMETIC AUDIT (rule 22) — all cross-checks consistent:**
- 56 + 2 + 8 = **66** ✔ (non-chamber).
- 66 + 38 = **104** ✔ (scored).
- Roster boundary **13** + chamber **8** = **21** ✔ matches “boundary 21” and the sealed `JB-CREAD-BOUNDARY` field.
- Level split (from §7.4(A)): boundary m=1: 0, m=2: 10, m=3: 3 → **13** ✔; scored m=1: 45, m=2: 8, m=3: 3 → **56** ✔.
- Per-tower m=2 boundary: T3A 3 + T3B 3 + T3C 1 + T3D 3 = **10** ✔.
- **Six independent cross-checks, all consistent.**

**CONDITIONALITY:** **“0 violations” is scoped to the SCORED stratum; the 21 boundary rows are where (VD-m) was machine-evaluated FALSE and therefore NOT scored.** The note's discipline is that the boundary census is displayed, not hidden — which is precisely what made the F1 refutation available.

**DERIVATION:** Recount from the committed sealed JSON.

**RESOLUTION TRACE:** statement lines 2494–2503; the disposition 829–834 (shard 1 `.54`); the level split 2748–2764 (`.17`); the theorem's fence 2186–2212 (shard 2 `.127`).

**TEETH:** `jb_cread` (IND end-to-end) with the boundary census disclosed. Disposition: **measurement + disclosed non-repair**.

---
### EFF.GRTJB.145  [supplier-finding]  ★ §7.1 — the (VD-2) roster DATA table, and the mechanism claim STRICKEN

**CANONICAL STATEMENT:** verbatim, lines 2503–2546 — the struck attribution, the `[r1, F1]` level split, the struck mechanism characterisations, and the `[r2, G2-4]` roster table.
**FORM:** nested bracketed riders + a fixed-width ASCII data table.

> “~~exactly the JA-BOX-2/(VD-m)-proviso
> geography (T3B/I4B = the W-2 collapse-boundary pair)~~ **[r1, F1 — CENSUS
> RE-ATTRIBUTED; the struck clause read the census as an m ≥ 3 phenomenon and
> so read this disclosure as CONFIRMING the (now retracted) "uncond. m ≤ 2"
> line, when it is the evidence AGAINST it. THE TRUE LEVEL SPLIT … of the 13 ROSTER boundary rows, **m = 1:
> 0 · m = 2: 10 (T3A 3, T3B 3, T3C 1, T3D 3) · m = 3: 3 (I4B)**, and NOT ONE is
> an evaluator scope-out — all 13 are machine-evaluated FALSE instances of
> (VD-m). Scored: 56 roster rows … at m = 1: 45, m = 2: 8, m = 3: 3. ~~So the
> geography is the JA-VDIND COLLAPSE BOUNDARY at m = 2 (the e₀ ≥ 2 towers with
> a nontrivial z₁ …) PLUS JA-BOX-2's own box at m = 3 (I4B only).~~ **[r2, G2-4 — THE MECHANISM
> CLAIM IS STRICKEN, NOT REPLACED. Both struck characterisations are refuted by
> the roster this note is describing (read off `GWP.TOWERS`, reads = (e, h, g)):**”

**Double-emission (rule 14) — the source ASCII data table, verbatim (lines 2522–2528):**

>     tower ring  p  e        h        g        d₀   (VD-2) at m = 2
>     T3A   Zp    2  2,2,2    1,1,1    1,1,1    2    BOUNDARY (3 rows)
>     T3B   Zp    3  3,2,2    1,1,1    1,1,1    1    BOUNDARY (3 rows)
>     T3C   Zp    3  2,3,2    1,2,1    1,1,1    1    BOUNDARY (1 row, 2 scored)
>     T3D   Fpt   2  2,2,2    1,1,1    2,1,1    1    BOUNDARY (3 rows)
>     T3E   Zp    2  2,1,2    1,1,3    2,1,1    1    SCORES 3/3  (6/6 both m)
>     T3F   Zp    3  1,3,2    2,1,1    2,1,1    1    SCORES 3/3  (6/6 both m)

`[TABLE]` **the same block transcribed:**

| tower | ring | p | e | h | g | d₀ | (VD-2) at m = 2 |
|---|---|---|---|---|---|---|---|
| T3A | ℤ_p | 2 | 2,2,2 | 1,1,1 | 1,1,1 | 2 | **BOUNDARY** (3 rows) |
| T3B | ℤ_p | 3 | 3,2,2 | 1,1,1 | 1,1,1 | 1 | **BOUNDARY** (3 rows) |
| T3C | ℤ_p | 3 | 2,3,2 | 1,2,1 | 1,1,1 | 1 | **BOUNDARY** (1 row, 2 scored) |
| T3D | **F_p[[t]]** | 2 | 2,2,2 | 1,1,1 | 2,1,1 | 1 | **BOUNDARY** (3 rows) |
| T3E | ℤ_p | 2 | 2,1,2 | 1,1,3 | 2,1,1 | 1 | SCORES 3/3 (6/6 both m) |
| T3F | ℤ_p | 3 | 1,3,2 | 2,1,1 | 2,1,1 | 1 | SCORES 3/3 (6/6 both m) |

**The refutation, verbatim (lines 2530–2545):**

> “  (i) "the e₀ ≥ 2 towers": T3E has e₀ = 2 and scores — five of the six T3 rows
>   have e₀ ≥ 2 and only four fail. (ii) "exactly where
>   A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses": at m = 2 that reads A_1 = ℓ₀g₀γ₁,
>   which by the note's own displayed sufficient condition vanishes iff e₀ = 1 —
>   true for T3F ALONE, so it cannot separate the other five. Worse for the
>   claim: T3D and T3E share the level-0 read (e₀, h₀, g₀) = (2, 1, 2) and the
>   same ψ₀ (⇒ the same A_1 and the same z₁ of order 3 in F₄), and they still
>   split — so the failing set is NOT a function of (A_1, ord z₁) at all. THE
>   HONEST STATEMENT: the mechanism of the m = 2 split is NOT IDENTIFIED in this
>   note. What holds is one implication, e₀ = 1 ⇒ A_1 = 0 ⇒ (VD-2) (consistent
>   with T3F), i.e. e₀ ≥ 2 is NECESSARY and not sufficient; the discriminator
>   among the e₀ ≥ 2 rows must involve data this note never computes (the
>   attained-abscissa set — T3D/T3E differ in the upper reads, e₁ = 2 vs 1 — or
>   the ring, Z₂ vs F₂[[t]]). **The table above is DATA, not a law: no consumer may
>   use it to predict which towers are free at m = 2.** The m = 3 boundary (I4B, 3
>   rows) is JA-BOX-2's own box.]** T3B/I4B remain the W-2
> collapse-boundary pair]**; **v = 0 stratum:
> 0 occurrences; R = 0: 0; off-perimeter tree rows: 0**.”

**SUPERSESSION KIND:** `counter re-reading` (r1/F1: a census re-attributed from confirming to refuting) + `counter re-reading` (r2/G2-4: two mechanism claims **STRICKEN, NOT REPLACED**).

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- T3 rows with `e₀ ≥ 2`: T3A (2), T3B (3), T3C (2), T3D (2), T3E (2) = **5**; failing among them: T3A, T3B, T3C, T3D = **4** ✔ matches “five of the six T3 rows have e₀ ≥ 2 and only four fail”.
- `e₀ = 1` rows: T3F alone ✔ matches “true for T3F ALONE”.
- T3D and T3E level-0 reads: T3D `(e₀,h₀,g₀) = (2,1,2)`, T3E `(2,1,2)` — **IDENTICAL** ✔; upper reads differ (`e₁ = 2` vs `1`) ✔; rings differ (F_p[[t]] vs ℤ_p) ✔. **The witness is exact as stated.**
- m=2 BOUNDARY rows: 3 + 3 + 1 + 3 = **10** ✔.

**CONDITIONALITY:** **The note strikes an explanation and refuses to substitute one.** What survives is exactly one implication in one direction (`e₀ = 1 ⇒ (VD-2)`), plus **an explicit ban: “no consumer may use it to predict which towers are free at m = 2.”** **PE3 later confirmed the refutation with a STRONGER witness** (T3D/T3E share ψ₀, `A_1 = 2`, `ord(z₁) = 3` and still split).

**GENERALITY NOTE (Q7, recorded not applied).** T3D is an **F_p[[t]]** row and it is one of the four failing towers, while T3E (ℤ_p, same level-0 read) scores — so the note's own data has an equal-characteristic row on each side of the split. Q7 classifies the note's ring roster **MACHINE-SCOPE ONLY**; no theorem restriction follows. **Recorded because a generality reader will look here first.**

**DERIVATION:** Two counter-instances from the note's own roster, displayed as data.

**RESOLUTION TRACE:** statement lines 2503–2546; the dispositions 638–659 (r1/F1) and 792–803 (r2/G2-4), shard 1 `.44`/`.51`; the reading fence 1471–1495 (shard 2 `.93`); the level census 2748–2764 (`.97`); PE3's stronger witness 862–864 (shard 1 `.55`).

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-VDIND` — grep-verified count **21** · `JA-BOX-2` — **7**.

**TEETH:** **the note's own roster is the tooth — a measurement that refuted an explanation.** Disposition: **measurement, refuting** + **AUDIT: decorrelated-model audit** (the gloss entered from a verifier's remark; “r2 treats no verifier as a source”).

---
### EFF.GRTJB.146  [changes-record]  §7.1 — the JB-KEYEQ coverage correction (r1/G-6)

**CANONICAL STATEMENT:** verbatim, lines 2548–2562.
**FORM:** struck claim + bracketed replacement.

> “Byte census
> (JB-KEYEQ) ~~reproduces the probe's F1 pattern row-for-row~~ **[r1, G-6 —
> COVERAGE CORRECTED: the two instruments walk different junction sets. The
> weld probe's F1 family is print r ≥ 3 walked up to r = n+2, so it INCLUDES
> the top junction; `jb_keyeq` walks q = 1..T.n, i.e. print r = 2..n+1, and
> therefore NEVER a top junction. They share 12 junctions (T3× at r = 3, six
> rows; I4× at r = 3,4, six rows) and on those 12 the agreement is EXACT (6
> GREEN / 6 RED), including every example listed here; but 16 roster F1
> junctions — all the top ones, carrying 12 of the probe's 18 F1 REDs — lie
> outside JB-KEYEQ's range, so "row-for-row" reproduction of the F1 pattern was
> an over-claim. The quoted §2(ii) figure "12 GREEN / 18 RED of 30 walked
> junctions" is the PROBE's own and is exact against its committed output]**”

**SUPERSESSION KIND:** `counter re-reading` — a coverage claim recounted against the two instruments' actual ranges.

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- Shared junctions: T3× at r = 3 (**6 rows**) + I4× at r = 3,4 (**6 rows**) = **12** ✔.
- Agreement on the shared 12: 6 GREEN + 6 RED = **12** ✔.
- Probe totals: 12 GREEN + 18 RED = **30 walked junctions** ✔ (§2(ii), shard 2 `.90`).
- REDs outside JB-KEYEQ's range: **12** of 18 ⇒ **6** REDs inside ✔ — consistent with the 6 RED among the shared 12.
- **All four consistent.**

**CONDITIONALITY:** **The range mismatch is structural, not accidental**: the probe's F1 family walks print `r ≥ 3` up to `r = n+2` (including the top junction); `jb_keyeq` walks `q = 1..T.n`, i.e. print `r = 2..n+1`, so **never a top junction**. **16 roster F1 junctions carrying 12 of 18 REDs are outside JB-KEYEQ's reach** — a permanent coverage hole of the sealed byte census.

**DERIVATION:** Range arithmetic on the two instruments' loops.

**RESOLUTION TRACE:** statement lines 2548–2562; the disposition 685–687 (shard 1 `.47` item G-6); the byte clause 1423–1428 (shard 2 `.90`).

**TEETH:** `jb_keyeq` (25 rows, 3 vacuous) with a **disclosed coverage hole** on 16 junctions. Disposition: **disclosed non-repair**.

---
### EFF.GRTJB.147  [run-record]  §7.1 — the MJB-CREAD teeth census (r1/G-2)

**CANONICAL STATEMENT:** verbatim, lines 2563–2573.
**FORM:** paragraph with a bracketed correction.

> “MJB-CREAD teeth material: 22 scored samples with z_m^{ε′} ≠ 1
> ~~across 7 towers~~ **[r1, G-2 — CORRECTED: across 14 DISTINCT TOWERS (T2A,
> T2B, T2D, T2F, T2G, T3A, T3B, T3D, T3E, T3F, I4B, JD3A, JD3C, JD5A) over 21
> teeth-positive JSON rows (14 base + 7 chamber); the 22 samples split 15 base +
> 7 chamber. "7" was the number of teeth-positive CHAMBER rows, which coincides
> with the runner docstring's smoke-probe designation list
> (T2A/T2D/T2G/T3A/T3D/T3E/I4B) — a smoke-era figure carried into the verdict
> text. The claim's substance is UNDERSTATED, not overstated]** — the
> spurious-carry reading fails on every one, i.e.
> the ε-carry collapse is machine-load-bearing, not a notational
> convention.”

**SUPERSESSION KIND:** `counter re-reading` — a figure corrected **in the direction of MORE evidence**.

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- Named towers: T2A, T2B, T2D, T2F, T2G, T3A, T3B, T3D, T3E, T3F, I4B, JD3A, JD3C, JD5A = **14 distinct** ✔.
- JSON rows: 14 base + 7 chamber = **21** ✔.
- Samples: 15 base + 7 chamber = **22** ✔.
- Smoke list: T2A, T2D, T2G, T3A, T3D, T3E, I4B = **7** ✔ — matching the erroneous “7” and confirming the diagnosis.
- **All four consistent.**

**CONDITIONALITY:** **The correction UNDERSTATES-to-overstates in the safe direction**, and the note says so. **The substantive claim — “the ε-carry collapse is machine-load-bearing, not a notational convention” — is the strongest tooth-backed statement in the note** and is what makes JB-BOX-1's blueprint correction more than a display preference.

**DERIVATION:** Recount from the committed JSON.

**RESOLUTION TRACE:** statement lines 2563–2573; the disposition 673–675 (shard 1 `.47` item G-2); the box 2314–2321 (shard 2 `.135`); the transport 2214–2221 (shard 2 `.128`).

**TEETH:** **planted mutant MJB-CREAD, fired on all 22 designated samples over 14 towers.** Disposition: **planted mutant; fired**.

---
### EFF.GRTJB.148  [changes-record]  §7.2 — the regeneration banner (SURFACES 6–12 of 14)

**CANONICAL STATEMENT:** verbatim, lines 2577–2583.
**FORM:** bold-headed bracketed block.

> “**[r3, STEP 2 — SURFACES 6–12 of 14: ALL SEVEN ROWS OF THIS TABLE REGENERATED
> FROM §0M's MATRIX.** Each grade cell below is the conjunction of that claim's
> YES cells in the matrix and nothing else. The r2 table is retained immediately
> after, SUPERSEDED; its known defects are PE3's **F-1** (the JB-VTX row carried
> no u ≥ 0 proviso although JB-BOX-2 names JB-VTX(d) as a consumer) and **F-4**
> ((RES) fenced at `P<q`). This is the surface a downstream unit reads alone, so
> it is generated, not patched.**]**”

**SUPERSESSION KIND:** `replacement` — the whole prior table superseded wholesale.

**TARGETS (rule 24):** `.150` (the retained r0/r1/r2 table).

**CONDITIONALITY:** **“This is the surface a downstream unit reads alone” is the reason §7.2 exists and the reason it is generated rather than patched.** The generation contract is stated exactly: “**Each grade cell below is the conjunction of that claim's YES cells in the matrix and nothing else.**” **That is a checkable bidirectional claim and §5 audits it.**

**DERIVATION:** Procedural.

**RESOLUTION TRACE:** statement lines 2577–2583; the 14-surface list 885–892 (shard 1 `.55`); the retained table 2595–2606 (`.10`); the governing rule 2443–2454 (shard 2 `.140`).

**TEETH:** **AUDIT — in-house hostile pass.** No battery keys a grade surface.

---
### EFF.GRTJB.149  [TABLE]  ★ §7.2 — the regenerated claims table (surfaces 6–12)

**CANONICAL STATEMENT:** verbatim, lines 2585–2593 — the seven-row source table. Because the rows are 400–900 characters each with nested strike markup, the transcription below preserves **every fence, every round tag and every figure**, condensing only the repeated cross-references with `…`; each row's full text is quoted at its theorem's unit in shard 2.
**FORM:** display (a Markdown table).

`[TABLE]` **§7.2, regenerated — “every fence from §0M, and no other”.**

| # | claim | grade — every fence from §0M, and no other | generating rows |
|---|---|---|---|
| **6** | **JB-DEV** (expansion identity: same division; byte clause; three-layer coefficient correspondence; cross-key fence) | PROVED (attempt grade 0/2), consumptions at their own grades. **(i)** every `q ≥ 0`, at the W2-C1 admissible representative; **(iv)** every `q ≥ 0` (a displayed fence); **(ii)** on `P≤q`; **(iii)(VAL)** on `P<q` = `0 ≤ q ≤ qcap = min(n, shared_upto+1)` — ~~off it (VAL) is FALSE, not merely unproved~~ **→ E-4**; **(iii)(GRID)** on `P<q` **AND** JA-GRID(a)'s UNDISCHARGED `u ≥ 0` proviso (narrowed r5/F-3: PROVED at `deg f < deg Φ_{q+1}`, membership residue at the unbounded-degree quantifier); **(iii)(RES)** on `P≤q` — one level deeper than r2's fence (**r3/F-4**); the exclusion bites on **5 of the 16** roster towers only (**r4/F-3**) — plus JA-RES's own fence (free at `m = q+1 = 2`, per-digit proviso at `m ≥ 3` = (VD-(m−1)) at every on-line digit, **r4/F-1**), and **NOT (VD-m) at level m**. Machine: one genuine second implementation + one genuine cross-engine tie; the advertised “print engine” leg is **SAME-COMPUTATION with an UNREACHABLE violation** (**r3/F-2**) | rows 1–6 |
| **7** | **JB-AFF** (affine ordinate maps preserve hulls/vertices) | PROVED (two lines), **UNCONDITIONAL** — no perimeter, no proviso, no [RMG] clause, no (VD-m); no separate machine leg, its content being exercised inside JB-VTX(b)/(c)'s legs | row 7 |
| **8** | **JB-VTX** (development polygon = `Σ_q(N_{q+1}(f))` vertex-for-vertex; slope/length translation; min/read ties; window clause) | PROVED (attempt grade) **on `P<q` (0 ≤ q ≤ qcap)**, every statement at the W2-C1 admissible representative — ~~off it clause (a)'s JA-VAL input is unavailable and (a) is FALSE, not merely unproved~~ **→ E-4**. Clause-level: ~~(a)/(b)/(c) and the THREE keyed min ties (d1)–(d3) ride `P<q` + W2-C1 only~~ **[r6, F-1** — (a)/(b)/(c) and (d1)/(d2) ride `P<q` + W2-C1; **(d3)** rides **`P≤q`** + W2-C1 (row 11 (a2); bites at `q = qcap` on the 5 `shared_upto < n` towers; the runner's gate on (d3) IS this fence, on (d1) an instrument cut)**]**; **(d4)** — attained abscissas = the read grid — **ALSO rides the UNDISCHARGED `u ≥ 0` proviso AND has NO MACHINE LEG** (**r3/F-1 + F-3**; narrowed **r5/F-3**); **(e)** is at `f = Φ_{q+1}^har`, the W2-C1a window object, not at the theorem's quantified `f` (r1/G-4). **→ E-3: every “slope/length” reads “slope/abscissa-run”** | rows 7–13 |
| **9** | **JB-TREE** (the [RMG] tree computes the classifier's division; edge = division step; cells = expansion slots; λ_E face = polygon bookkeeping **of the LINE functional, with the `v_{m+1}` reading at the R-leaves only — r4/F-4, row 17**) | PROVED (attempt grade) on T-scope(m), `g_m = 1`, W-WIN unconsumed; **LED-Λ cited at ATTEMPT grade and the tie's grade rides it**. **[r4, F-4]** §4(iii)'s per-edge laws are laws of `line(·)`, every edge; `line = w_m = v_{m+1}` asserted (and machine-keyed) **at the R-LEAVES ONLY** — no internal-node `v_{m+1}` statement is claimed. **(i)/(ii) PERIMETER-FREE; (iii)/(iv) at levels `m ≤ qcap` ONLY** since both consume JA-VAL — **r3/F-1B: this fence now also stands at the grade cap and in JB-BOX-2**; **(iv)**'s (C-READ) leg additionally rides §5's (VD-m) fence in full, and its **(C-W_Q) clause has NO machine leg**. [RMG]: (i) T-TERM + L-EXACT + L-CANON (the latter through the restored `deg Ĉ_m < deg Φ_m`, **r3/F-5**); (ii) S2.2 + L-NORM + L-CELL + S0.1's `P_i = e_i·g_i` (**r3/F-7**). The print-key machine evidence for (i) is §7.4's post-seal walker, **base rows only, with 8 byte-unequal chamber walks unreached** (r1/G-1; r2/G2-2, G2-3) | rows 14–18 |
| **10** | **JB-EPS** (ε-cocycle collapse `t(V+V′) − t(V) − t(V′) = ε′`) | PROVED, **UNCONDITIONAL at every `m ≥ 1`** — no perimeter, no `u ≥ 0` (it cites JA-GRID(c), which carries none), no (VD-m). **Its application inside §5 at `(V, V′) = (λ, γ_{m+1})` is LICENSED by [RMG]'s restored clause `w_m(Ĉ_m) = γ_{m+1}` (r3/F-5); before r3 that instance sat outside the lemma's own quantifier** | rows 19–20 |
| **11** | **JB-CREAD** ((C-READ) transport: `ρ_m(R) = c_m·ρ_m(f)`, carry-free in print coordinates) | PROVED on the **(VD-m) perimeter ∩ {v ≠ 0}**: (VD-m) unconditional at `m ≤ 1` ONLY, CONDITIONAL at every `m ≥ 2` (JA-VDIND collapse; ⊇ (R-coll)/JA-BOX-2 at `m ≥ 3`) — **NO unconditional stratum above `m = 1`** (r1/F1) — and **required at BOTH `f` and `R`**. **No key perimeter** (a legitimate conditional at any level); the instrument's own `m ≤ qcap` cut is disclosed with off-perimeter rows 0. The **`v = 0` branch is read-at-target only and machine UNEXERCISED**. [RMG]: (C-READ), (C-W_R), the complete Ĉ_m clause list, L-CELL(i)/(ii) = (B-READ), on [RMG]'s scope | rows 21–22 |
| **12** | **JB-BOX-1** (blueprint J-B(iii) carry placement) | CORRECTED (frame conflation; both frames displayed). Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence; its machine leg is the teeth family MJB-CREAD, where the carry-bearing reading must FAIL — **and does, on all 22 designated samples over 14 towers** | row 23 |

**MANDATORY ARITHMETIC AUDIT (rule 22) — the generation contract, checked bidirectionally against §0M (shard 1 `.20`).**
- **Row count.** 7 rows ✔ matches “SURFACES 6–12 of 14: ALL SEVEN ROWS”.
- **Generating-row coverage.** Rows cited: 1–6, 7, 7–13, 14–18, 19–20, 21–22, 23 → **union = rows 1–23**, i.e. **every CLAIM row of the matrix**, with rows 24–28 (the five RECORD rows) correctly excluded ✔. Overlap: row 7 appears in surfaces 7 and 8 — **deliberate** (JB-AFF is graded on its own AND named as exercised inside JB-VTX's legs) ✔.
- **Fence-for-cell check, direction 1 (“every fence below is a cell”).** Spot-audited on the six load-bearing cells: (iii)(RES)'s `P≤q` = row 5 (a2) ✔; (iii)(GRID)'s `u ≥ 0` = row 4 (b) ✔; (d3)'s `P≤q` = row 11 (a2) ✔; (d4)'s `u ≥ 0` + NO LEG = row 12 (b),(f) ✔; (C-W_Q)'s NO LEG = row 18 (f) ✔; JB-EPS's unconditionality = row 19 ✔.
- **Fence-for-cell check, direction 2 (“the table carries no fence this surface omits”).** Every non-blank cell of rows 1–23 appears in some surface row ✔ — including the three that PE3's F-1/F-4 found MISSING from the r2 table (row 4's `u ≥ 0` on the JB-VTX side, row 12's, and row 5's `P≤q`), all three present here.
- **Cross-check with the grade cap (surface 1, shard 1 `.31`–`.37`)** and with surfaces 2–5 (shard 2 `.97`, `.107`, `.117`, `.132`): **no fence appears in one and not the others**, with one exception already recorded — shard 2's source defect 2 (surface 5's range label). ✔

**CONDITIONALITY:** **THREE shard-3 corrections land on this surface.** **E-3**: “§7.2's JB-VTX row … read every occurrence of ‘slope/length’ as ‘slope/abscissa-run’”. **E-4**: “§7.2's JB-DEV/JB-VTX rows … every live occurrence of ‘FALSE, not merely unproved’ is read as ‘NOT SUPPLIED outside the stated perimeter’”. **E-1/E-2**: the “(R-coll)” label and the W2-C3 grade. **And the grade prefix “attempt grade 0/2” is STALE** — see `.164`.

**DERIVATION:** Regeneration from §0M.

**RESOLUTION TRACE:** statement lines 2585–2593; generating rows 293–322 (shard 1 `.20`); the theorem bodies 1400–2308 (shard 2); correction sites 3125–3142 (E-1/E-2), 3199–3245 (E-3), 3267–3312 (E-4).

**TEETH:** per row; the surface itself is **AUDIT — in-house hostile pass**.

---
### EFF.GRTJB.150  [changes-record]  §7.2 — the retained superseded table

**CANONICAL STATEMENT:** [ASSEMBLED — the banner (lines 2595–2596) quoted verbatim; the seven retained rows (2598–2606) are the superseded r0/r1/r2 table and are NOT re-quoted, their live content being `.149`.]

> “**[r3 — SUPERSEDED r0/r1/r2 §7.2 table, retained for the record. NOT
> authoritative.]**”

**SUPERSESSION KIND:** `replacement` — this unit IS the superseded object, retained.

**CONDITIONALITY:** **NOT AUTHORITATIVE.** Its two known defects are named in `.148`'s banner (PE3's F-1 and F-4). **Unlike §7.3's superseded region, this one is bounded by the section break rather than by an explicit terminator** — the note's `---`-free structure here means the region ends where §7.3 begins. **Recorded as source defect 3** (the r4/F-6 discipline was applied to §7.3 but not re-checked here; nothing live sits inside this region, so nothing is at risk).

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 2595–2606; the superseding surface 2585–2593 (`.149`); the terminator discipline 2728–2736 (`.153`).

**TEETH:** NONE (retained record).

---
### EFF.GRTJB.151  [TABLE]  ★ §7.3 — SURFACE 13, the consequence display (what a downstream unit inherits)

**CANONICAL STATEMENT:** verbatim, lines 2610–2680 — the regenerated consequence display, quoted in two contiguous blocks.
**FORM:** bold-headed bracketed block + five bullets.

**BLOCK A — the W-3 and W-5 bullets (lines 2610–2651):**

> “**[r3, STEP 2 — SURFACE 13 of 14, REGENERATED FROM §0M. What J-B supplies (at
> attempt grade, acceptance counter 0/2, hostile passes owed), stated so that a
> downstream unit reading ONLY this display inherits every fence:**
>
> * **W-3 = both halves of the identity (expansion + polygon, shear explicit) —
>   full in CONTENT, not full in q.** The polygon half — **ALL of JB-VTX: (a)/
>   (b)/(c), the three keyed min ties (d1)–(d3), the (d4) grid/attained-abscissa
>   tie, and (e) through (a) at f = Φ_{q+1}^har [r4, F-7 — (d4) and (e) were
>   omitted from this enumeration; §0M rows 12–13 and surface 14 carry them]**
>   **[r6, F-1 — (d3) EXCEPTED from this `P<q` list: JA-VAL at level q+1, it
>   holds on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) like (RES), biting at
>   q = qcap on the 5 shared_upto < n towers (§0M row 11 (a2))]** —
>   and the (VAL)/(GRID) layers of the expansion half
>   hold on the **SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap = min(n,
>   shared_upto+1))**; off it JB-VTX(a) and JB-DEV(iii)(VAL) are **FALSE**, not
>   merely unproved. JB-DEV(i)/(ii)/(iv) hold at every q ≥ 0, with (ii) on the
>   **BYTE-EQUAL CHAIN THROUGH q**. **JB-DEV(iii)(RES) holds only on the
>   BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — r3/F-4 … the exclusion bites on 5 of the 16 roster towers only (r4/F-3 …) — plus JA-RES's own per-digit proviso at m = q+1 ≥ 3 …** TWO
>   sub-clauses ride JA-GRID(a)'s **UNDISCHARGED u ≥ 0 proviso**: the (GRID)
>   layer inside JB-DEV(iii) **and the grid/attained-abscissa content of
>   JB-VTX(d) — the polygon half, which r2's display omitted (r3/F-1)**
>   **[r5, F-3 — narrowed at both: u ≥ 0 is PROVED for deg f < deg Φ_{q+1}
>   (V ∈ 𝒲_{q+1}, §5's display); what a consumer must still carry is lattice
>   membership at the unbounded-degree quantifier]**; that
>   same JB-VTX(d4) content is also the one sub-clause with **no machine leg**
>   (r3/F-3). JB-VTX(e) is at f = Φ_{q+1}^har only (r1, G-4). [§0M rows 1–13]
> * **W-5 on [RMG]'s scope (T-scope(m), g_m = 1), with two further fences.**
>   (ii) the tree/division correspondence with LED-Λ as the bookkeeping, at
>   attempt grade — **the bookkeeping is per-edge laws of the LINE functional,
>   with the classifier reading line = w_m = v_{m+1} at the R-LEAVES only
>   (r4/F-4, §0M row 17)** — **(i)/(ii) of §4 perimeter-free, but §4(iii)/(iv)
>   only at
>   levels m ≤ qcap, since they consume JA-VAL (r3/F-1B)**, and §4(iv)'s (C-W_Q)
>   clause has no machine leg. (iii) the (C-READ) transport in both frames, on
>   the **(VD-m) perimeter ∩ {v ≠ 0}**: free of extra hypotheses at **m = 1
>   only** (r1, F1 — conditional at every m ≥ 2, and (VD-m) is needed at BOTH f
>   and R), with the v = 0 branch a read-at-target statement only and machine
>   unexercised. LEMMA JB-EPS is unconditional and its §5 instance is licensed by
>   [RMG]'s restored w_m(Ĉ_m) = γ_{m+1} (r3/F-5). [§0M rows 14–23]”

**BLOCK B — the three r4/F-6 regenerated bullets (lines 2652–2680):**

> “* **NOT supplied [r4, F-6 — REGENERATED LIVE from the matrix; the r0 list
>   below sat inside the superseded region with no live replacement]:** W-1's
>   uncollapsed all-orders dictionary (JA-BOX-2), W-2's grades (consumed), the
>   J-C block W-6..W-9 (no gr claim; BLOCKED-ON-CARRIER-TIE stands — §0M
>   row 28), J-D counts/menus (W-10..W-12), W2-OPEN-1 (consumed nowhere,
>   JB-BOX-2). The P0 application gate stands.
> * **(C-READ) downstream notice [r4, F-6 — the live form of the r1/F1 notice
>   below]:** W-5(iii)'s transport ρ_m(R) = c_m·ρ_m(f) is free of extra
>   hypotheses at m = 1 ONLY; at every m ≥ 2 a consumer must either carry
>   JA-VDIND's collapse condition (⊇ (R-coll) at m ≥ 3) or work on the
>   machine-scored stratum (§0M rows 21–22). Downstream units that read
>   "unconditional at m ≤ 2" from r0 must re-read this line; the J-C germ
>   (ρ_m(R) = −z_{m+1}·ρ_m(f), §5's remark) inherits the same conditionality
>   above m = 1.
> * **CONSUMES [r4, F-6 — regenerated]:** [RMG] (ACCEPTED) · [ILN]† (accepted) ·
>   W-2 + J-A + LED-Λ at attempt grade (conditionality verbatim) · GMN
>   HigherNewton as literature (header anchors) through the sealed probe
>   transcription · engine_ext (standing rule). CONSUMED BY (intended): the J-C
>   block units (W-6..W-9 — §5's remark is their semantic germ), the W-10/J-D
>   count units, the weld campaign ledger at J-B. **Acceptance counter 0/2**
>   (~~four hostile passes run …~~ … **[r8]** eight hostile passes run,
>   eight repair rounds applied; JB-PE9 is the next acceptance attempt).”

**Double-emission (rule 14) — the supply, as a `[TABLE]` a consumer can read alone:**

| supplied item | scope | fences a consumer INHERITS |
|---|---|---|
| **W-3, expansion half** — JB-DEV(i)/(ii)/(iv) | every `q ≥ 0` | (ii) on `P≤q`; (i) at the W2-C1 representative; (iv) a displayed fence |
| **W-3, expansion half** — JB-DEV(iii)(VAL)/(GRID) | `P<q`, `0 ≤ q ≤ qcap` | ~~off it FALSE~~ **→ E-4: NOT SUPPLIED outside the perimeter**; (GRID) **+ the `u ≥ 0` proviso**, narrowed r5/F-3 to a membership residue |
| **W-3, expansion half** — JB-DEV(iii)(RES) | **`P≤q`** only | bites on 5/16 roster towers; **+ JA-RES's per-digit proviso at `m ≥ 3`**; **NO machine leg** |
| **W-3, polygon half** — JB-VTX (a)(b)(c)(d1)(d2)(d4)(e) | `P<q` + W2-C1 | **(c) → E-3: “slope/abscissa-run”, not lattice data**; **(d4) rides the `u ≥ 0` residue AND has NO machine leg**; (e) at `f = Φ_{q+1}^har` only |
| **W-3, polygon half** — JB-VTX(d3) | **`P≤q`** (r6/F-1) | EXCEPTED from the `P<q` list |
| **W-5(i)/(ii)** — the tree/division correspondence | PERIMETER-FREE, on T-scope(m), `g_m = 1` | LED-Λ at **ATTEMPT** grade; the bookkeeping is **LINE-functional laws**, `v_{m+1}` at R-leaves only |
| **W-5** — §4(iii)/(iv) | levels `m ≤ qcap` only | both consume JA-VAL; **(C-W_Q) has no machine leg** |
| **W-5(iii)** — the (C-READ) transport | **(VD-m) ∩ {v ≠ 0}** | free at `m = 1` ONLY; (VD-m) needed at BOTH `f` and `R`; `v = 0` branch read-at-target only and **machine unexercised** |
| **LEMMA JB-EPS** | **unconditional at every `m ≥ 1`** | its §5 instance licensed by the restored `(Ĉ-wt)` |
| **NOT supplied** | — | W-1's uncollapsed all-orders dictionary; W-2's grades; **the J-C block W-6..W-9 (no gr claim; BLOCKED-ON-CARRIER-TIE stands)**; J-D counts/menus; W2-OPEN-1. **The P0 application gate stands** |

**MANDATORY ARITHMETIC AUDIT (rule 22):** generating ranges declared = “§0M rows 1–13” (W-3 bullet) + “§0M rows 14–23” (W-5 bullet) → **rows 1–23 = every claim row**, no gaps, no overlap ✔; rows 24–28 (records) correctly absent ✔. The “TWO sub-clauses ride … the `u ≥ 0` proviso” count = rows 4, 12 = **2** ✔. The “(d1)–(d3) … three keyed min ties” + (d4) = **4** ✔.

**CONDITIONALITY:** **This is the display a downstream unit reads ALONE, and it is the note's own statement of that intent.** **FOUR corrections land on it:** E-3 (the W-3 polygon bullet's “slope/length”), E-4 (its “FALSE, not merely unproved”), and E-1/E-2 through the inherited labels. **The “Acceptance counter 0/2 … JB-PE9 is the next acceptance attempt” clause is STALE** (`.164`). **The “W-2 + J-A … at attempt grade” clause is STALE** (`.168`); **LED-Λ's attempt grade is NOT stale.**

**DERIVATION:** Regeneration from §0M.

**RESOLUTION TRACE:** statement lines 2610–2680; generating rows 293–322 (shard 1 `.20`); the r4/F-6 disposition 1009–1014 (shard 1 `.63`); correction sites 3107–3119 (acceptance), 3125–3142 (E-1/E-2), 3148–3161 (supplier grades), 3199–3245 (E-3), 3267–3312 (E-4).

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JB-BOX-2` — count **3** (the intended consumer's own inheritance of this display's geography).

**TEETH:** per row; the surface itself is **AUDIT — in-house hostile pass**.

---
### EFF.GRTJB.152  [changes-record]  §7.3 — the retained superseded consequence display

**CANONICAL STATEMENT:** [ASSEMBLED — the banner (2682–2684) and the retained r0/r2 display (2686–2726), quoted at the banner and summarised; the live content is `.151`.]

> “**[r3 — SUPERSEDED r0/r2 consequence display, retained for the record. NOT
> authoritative; its defects are F-1 (the proviso attached to the expansion half
> only) and F-4 ((RES) at the wrong perimeter).]**”

**SUPERSESSION KIND:** `replacement`.

**CONDITIONALITY:** **NOT AUTHORITATIVE**, with its two defects named. **This is the region r4/F-6 found unterminated** — see `.153`.

**DERIVATION:** Record.

**RESOLUTION TRACE:** statement lines 2682–2726; the terminator 2728–2736 (`.153`); the superseding surface 2610–2680 (`.151`).

**TEETH:** NONE (retained record).

---
### EFF.GRTJB.153  [changes-record]  ★ §7.3 — the r4/F-6 TERMINATOR (live content rescued from a non-authoritative region)

**CANONICAL STATEMENT:** verbatim, lines 2728–2736.
**FORM:** bold-headed bracketed block.

> “**[r4 — end of the superseded consequence display (F-6). The r3 banner above
> opened a superseded region and never closed it, so on the note's own reading
> discipline the NOT-supplied list, the r1/F1 (C-READ) notice and the CONSUMES +
> counter line just above sat in a NOT-authoritative region with no live
> replacement. This terminator closes the region here; everything from the
> banner through this line is retained record, and all three items are
> REGENERATED LIVE inside surface 13 above (the [r4, F-6] bullets), which is the
> authoritative surface. The old counter line's "0/2" remains true; the live
> CONSUMES bullet carries the current arc.]**”

**SUPERSESSION KIND:** `replacement` — three live items relocated out of a non-authoritative region into the authoritative surface.

**CONDITIONALITY:** **A reading-discipline repair with real consequence.** On the note's own discipline, live content inside a SUPERSEDED banner is not authoritative — so before r4, the NOT-supplied list (which contains **“the J-C block W-6..W-9 (no gr claim; BLOCKED-ON-CARRIER-TIE stands)”**, the single most load-bearing negative fence in the note) sat in a region a careful reader would have discounted. **The closing clause “The old counter line's ‘0/2’ remains true” is itself now STALE** (`.164`).

**DERIVATION:** Record + the reading discipline it enforces.

**RESOLUTION TRACE:** statement lines 2728–2736; the disposition 1009–1014 (shard 1 `.63`); the regenerated bullets 2652–2680 (`.11`); the pattern it copies 519–563 (shard 1 `.38`).

**TEETH:** NONE. Disposition: **AUDIT — in-house hostile pass** (a region-boundary defect no battery could see).

---
### EFF.GRTJB.154  [instrument-record]  §7.4 — the post-seal status fence

**CANONICAL STATEMENT:** verbatim, lines 2740–2746.
**FORM:** paragraph with an `[r2]` extension.

> “Both instruments below were written AFTER the JB-PE1 verdict (85a8dc9). They
> are **evidence for a repair, not preregistered predictions of the sealed
> battery**, and they are reported separately for exactly that reason. The
> sealed runner and its JSON are byte-untouched by this round. **[r2 — a THIRD
> instrument, leg (C), was added in repair round r2 against JB-PE2's G2-2; the
> same disclaimer applies to it, and the sealed runner plus both r1 instruments
> are byte-untouched by r2 (md5s in the front-matter block).]**”

**TYPE JUSTIFICATION (rule 19):** `instrument-record` — the epistemic STATUS of the apparatus, distinct from the `preregistration`s (`.156`, `.158`) and `run-record`s (`.157`, `.159`, `.161`) that follow.

**CONDITIONALITY:** **The status fence governs everything in §7.4: none of the three legs may be read as a preregistered confirmation.** The note keeps them in a separate section “for exactly that reason”.

**PIN VERIFICATION:** `85a8dc9` → **commit**; all four md5s **EXACT at HEAD**.

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement lines 2740–2746; the front-matter declaration 601–619 (shard 1 `.42`).

**TEETH:** the legs themselves are `.157`, `.159`–`.163`.

---
### EFF.GRTJB.155  [instrument-record]  §7.4(A) — the level-keyed boundary census, described

**CANONICAL STATEMENT:** verbatim, lines 2748–2752 (the description).
**FORM:** bold-headed paragraph.

> “**(A) Level-keyed boundary census — `grt_jb_r1_levelcensus.py`** (read-only;
> imports the sealed runner verbatim and replays `jb_cread`'s own control flow,
> recording the level m and the failure side of every boundary row instead of
> the per-tower aggregate the sealed JSON keeps). Output committed as
> `grt_jb_r1_levelcensus_output.txt`. Result on the 16-tower roster:”

**CONDITIONALITY:** **Its independence is limited BY DESIGN and the note says so: it “imports the sealed runner verbatim and replays `jb_cread`'s own control flow”.** So it is a re-keying, not a second implementation. **The genuine decorrelation came from PE2, which re-derived the same split from the committed JSON alone without calling `vd_eval`** (shard 1 `.48`).

**PIN VERIFICATION:** `grt_jb_r1_levelcensus.py` **EXISTS**, md5 **EXACT**; `grt_jb_r1_levelcensus_output.txt` **EXISTS**.

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement lines 2748–2752; the result 2754–2760 (`.156`); the finding it supports 638–659 (shard 1 `.44`).

**TEETH:** see `.156`.

---
### EFF.GRTJB.156  [run-record]  ★ §7.4(A) — the level census result

**CANONICAL STATEMENT:** verbatim, lines 2754–2764 — the fixed-width census block and its conclusion.
**FORM:** fixed-width display + paragraph.

>     m=1  SCORED    45          m=2  SCORED     8        m=3  SCORED   3
>                                m=2  BOUNDARY  10        m=3  BOUNDARY 3
>     boundary per (tower, m):  T3A m=2: 3 · T3B m=2: 3 · T3C m=2: 1 ·
>                               T3D m=2: 3 · I4B m=3: 3
>     reasons: R EVAL-FALSE 10, f EVAL-FALSE 3, evaluator SCOPE-OUTS 0
>     JSON cross-check: roster boundary 13 + chamber 8 = 21 = the sealed
>     `JB-CREAD-BOUNDARY` census field

> “This is F1's factual core: **10 of the 13 roster boundary rows are
> machine-evaluated FALSE instances of (VD-2)**, i.e. inside the stratum r0
> advertised as unconditional, and none of the 13 is an evaluator scope-out.”

**Double-emission (rule 14) — the census as a `[TABLE]`:**

| level | SCORED | BOUNDARY | boundary per (tower, m) |
|---|---|---|---|
| m = 1 | 45 | 0 | — |
| m = 2 | 8 | **10** | T3A 3 · T3B 3 · T3C 1 · T3D 3 |
| m = 3 | 3 | 3 | I4B 3 |
| **totals** | **56** | **13** | reasons: R EVAL-FALSE 10, f EVAL-FALSE 3, **evaluator SCOPE-OUTS 0** |

**MANDATORY ARITHMETIC AUDIT (rule 22) — six cross-checks, all consistent:**
- SCORED: 45 + 8 + 3 = **56** ✔ (“56 roster rows”).
- BOUNDARY: 0 + 10 + 3 = **13** ✔.
- Per-tower m = 2: 3 + 3 + 1 + 3 = **10** ✔.
- Reasons: 10 + 3 + 0 = **13** ✔ — and **SCOPE-OUTS 0** is the load-bearing zero (every boundary row is an evaluated FALSE, not an out-of-scope skip).
- JSON cross-check: 13 + 8 = **21** ✔ matches the sealed `JB-CREAD-BOUNDARY` field and `.144`'s “boundary 21”.
- “10 of the 13” ✔.

**CONDITIONALITY:** **The `SCOPE-OUTS 0` line is what makes this a refutation rather than a coverage gap.** Had any of the 13 been an evaluator scope-out, the census would be consistent with (VD-2) holding there; because all 13 are evaluated FALSE, the r0 “unconditional at m ≤ 2” claim is refuted by the note's own instrument.

**DERIVATION:** Executed run, transcribed from the committed output.

**RESOLUTION TRACE:** statement lines 2754–2764; the description 2748–2752 (`.155`); the finding 638–659 (shard 1 `.44`); the theorem's corrected fence 2186–2203 (shard 2 `.127`); PE2's decorrelated re-derivation 715–719 (shard 1 `.48`).

**TEETH:** **executable regression that disconfirmed the author**, subsequently **re-derived from a different artifact by a hostile pass**. Disposition: **accepted-with-decorrelation-supplied** — the strongest evidentiary standing anything in this note has.

---
### EFF.GRTJB.157  [preregistration]  §7.4(B) — the print-key walker, its charge and its mini-seal

**CANONICAL STATEMENT:** verbatim, lines 2766–2783.
**FORM:** bold-headed paragraph + a mini-seal record.

> “**(B) Independent print-key tree walker — `grt_jb_printwalk.py`**, with its
> own mini two-commit seal (prereg comment block + the script committed BEFORE
> any full run; verdict below transcribed from the committed
> `grt_jb_printwalk_output.txt` / `_results.json`). It answers G-1: the sealed
> JB-TREE leg's "print key" family is one `fresh_divmod` re-executed on equal
> arguments, so the print-key reading was never independently checked, and never
> checked at all off the byte-equal set. The walker takes every key from the
> print chain (`GmnLeg.phi`), extracts the correction digits by DIVIDING PRINT
> KEYS (the print-side reading of (ID-(i+1))) instead of from
> realize(ε^{−1}ψ), builds Ĉ_m^cls = φ_{m+2} − φ_{m+1}^{e_m}, divides by the
> print key with its own Horner/synthetic implementation certified per call by
> reassembly + degree bound, and never imports the sealed runner.
>
> Mini-seal record: script sealed UNRUN at r1 commit 1 `4c97649`, verdict
> appended at r1 commit 2, and the script's md5
> `f53e23e8d1c79f084a1e34eee857e37c` is identical at both commits (checked with
> `git show <commit>:…`), i.e. it was not touched between its preregistration
> and its run.”

**TYPE JUSTIFICATION (rule 19):** `preregistration` — the stated-in-advance design and seal, emitted separately from the `run-record` at `.159`.

**CONDITIONALITY:** **The decorrelation is stated in four dimensions and is checkable:** keys (from the print chain `GmnLeg.phi`), correction digits (by DIVIDING PRINT KEYS, not via `realize(ε^{−1}ψ)`), divisor (the print key), and division code (its own Horner/synthetic implementation, certified per call). **“and never imports the sealed runner”** is the clause that makes it genuinely independent — in explicit contrast to leg (C), which does import (`.162`).

**PIN VERIFICATION (rule 23):** `grt_jb_printwalk.py` **EXISTS**; md5 `f53e23e8d1c79f084a1e34eee857e37c` **EXACT at HEAD**; `4c97649` → **commit**; both output artifacts **EXIST**.

**DERIVATION:** Instrument design.

**RESOLUTION TRACE:** statement lines 2766–2783; the charge 660–672 (shard 1 `.47` item G-1); the sealed leg it repairs 1963–1980 (shard 2 `.118`); the verdict 2803–2814 (`.99`).

**TEETH:** the mini-seal itself (md5 identical at preregistration and run) is the tooth for the preregistration claim. **Re-verified EXACT at HEAD.**

---
### EFF.GRTJB.158  [changes-record]  §7.4(B) — the struck verdict line (r2/G2-3 + G2-7)

**CANONICAL STATEMENT:** verbatim, lines 2785–2801.
**FORM:** struck verdict + bold-headed bracketed correction.

> “~~**VERDICT (r1 commit 2, transcribed from `grt_jb_printwalk_output.txt`;
> exit 0, elapsed 0.1 s, 458 samples, seal commit 4c97649):
> ALL FIVE FAMILIES GREEN — the print-key tree identity HOLDS at print keys,
> including on every junction the sealed battery left unchecked.**~~
>
> **[r2, G2-3 + G2-7 — THE VERDICT LINE, RESTATED. Two defects in the struck
> line. (1) "every junction the sealed battery left unchecked" is FALSE and is an
> escalation of the script's own wording: `grt_jb_printwalk.py` prints
> "including **off the byte-equal set**", and the sealed `tree` block has EIGHT
> `byteeq: false` rows, not four — the four BASE rows the walker does reach
> (T3A m=2, T3C m=2, T3D m=2, T3E m=2; 3 walks each = 12) AND four CHAMBER rows
> it does not (`T3A/tw`, `T3C/tw`, `T3D/tw`, `T3E/tw` at m = 2; 2 walks each =
> 8), because the walker's `main()` iterates `GWP.TOWERS` + `GWP.QO_SHAPES` +
> `GJA.D0_SPECS` and builds NO chambers. (2) "458 samples" is the script's
> `TOTAL samples` = `sum(COUNTS.values())`, which adds three bookkeeping counters
> (`PW-UNEQUAL-WALKS` 12, `PW-CHAIN-DIVERGENT` 12, `PW-XFRAME-AGREE` 72) to the
> five law families (38 + 84 + 84 + 84 + 72 = 362). CORRECTED VERDICT:**”

**SUPERSESSION KIND:** `counter re-reading` ×2 — a coverage escalation beyond the script's own wording, and a sample count conflating law samples with bookkeeping counters.

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- `byteeq: false` rows: 4 base + 4 chamber = **8** ✔.
- Base walks: 4 rows × 3 = **12** ✔; chamber walks: 4 rows × 2 = **8** ✔.
- Law families: 38 + 84 + 84 + 84 + 72 = **362** ✔.
- Bookkeeping counters: 12 + 12 + 72 = **96** ✔.
- Total: 362 + 96 = **458** ✔ — exactly the struck figure, now decomposed.
- **All five consistent.**

**CONDITIONALITY:** **Defect (1) is the more serious: the note's own text escalated beyond what its script printed.** The script says “off the byte-equal set”; the note said “every junction the sealed battery left unchecked”. **The 8 chamber walks are a permanent hole in BOTH instruments.**

**DERIVATION:** Recount from the committed JSON and the script's own source.

**RESOLUTION TRACE:** statement lines 2785–2801; the dispositions 784–790 (r2/G2-3) and 829–834 (r2/G2-7), shard 1 `.54`; the corrected verdict 2803–2814 (`.19`).

**TEETH:** **disclosed non-repair** (8 chamber walks) + **measurement** (the decomposition).

---
### EFF.GRTJB.159  [run-record]  §7.4(B) — the corrected verdict, and the five-family table

**CANONICAL STATEMENT:** verbatim, lines 2803–2833 — the corrected verdict, the five-family table and the COVERAGE block.
**FORM:** bold verdict paragraph + Markdown table + fixed-width coverage block.

> “**VERDICT (r1 commit 2 artifacts `grt_jb_printwalk_output.txt` /
> `_results.json`, re-stated in r2; exit 0, elapsed 0.1 s; 362 LAW samples
> (+ 96 coverage-counter increments = the 458 the script prints as its TOTAL);
> seal commit 4c97649): ALL FIVE FAMILIES GREEN — the print-key tree identity
> HOLDS at print keys, INCLUDING OFF THE BYTE-EQUAL SET on the 12 base-row walks
> at byte-unequal junctions (T3A/T3C/T3D/T3E at m = 2), which the sealed
> battery's print-key leg never ran. STILL PRINT-UNCHECKED, by both instruments:
> the 8 walks on the four byte-unequal CHAMBER rows `T3A/tw`, `T3C/tw`,
> `T3D/tw`, `T3E/tw` at m = 2 (sealed leg: `byteeq` false ⇒ no print-key check;
> walker: no chambers built). Also unreached by the walker, and NOT part of any
> print-key claim: everything the sealed battery scores off the tree families
> (no (VD-m)/§5 content, r1's own fence below).**”

`[TABLE]` **the five walker families (lines 2816–2822):**

| family | claim keyed | pred | obs | samples | verdict |
|---|---|---|---|---|---|
| **PW-ID** | print (ID-(i+1)) read off the print chain: digit 1 at abscissa `P_i`, digits only at `e_i·k` (`k < g_i`), nothing off-grid | 0 | 0 | 38 | GREEN |
| **PW-WALK** | print E1-priority walk terminates under the cap; every R-leaf reduced (`j_l ≤ P_l − 1`) | 0 | 0 | 84 | GREEN |
| **PW-REASM** | signed reassembly `Σleaves + (Σexits)·φ_{m+1}^cls = f·Ĉ_m^cls` in `O[x]` | 0 | 0 | 84 | GREEN |
| **PW-DIV** | tree pair == this script's own certified print-key division (+ the engine's `divmod_monic` as a third leg) | 0 | 0 | 84 | GREEN |
| **PW-XFRAME** | leg B: on chain-byte-equal rows, the PRINT-keyed tree on `f·Ĉ_m^har` == the harness-key division | 0 | 0 | ~~72~~ **[r2, G2-2]** 72 = **45 cross-frame + 27 DEGENERATE (vacuous)** | GREEN (45 carry content) |

**Double-emission (rule 14) — the COVERAGE block, verbatim (lines 2824–2833):**

>     COVERAGE  leg-A print-key walks 84 (predicted 79)
>               at byte-UNEQUAL junctions 12 (predicted 12 — EXACT)
>               leg B fired 72 (predicted 67), agreed 72
>                     [r2, G2-2: of which 45 cross-frame, 27 degenerate]
>     the 12 byte-unequal walks are exactly the sealed BASE rows with
>               byteeq = false  [r2, G2-3: "base" added — the four /tw CHAMBER
>               rows are byteeq = false too and are UNREACHED, 8 walks]:
>               T3A m=2 (3) · T3C m=2 (3) · T3D m=2 (3) · T3E m=2 (3)
>     I4C: no print-eligible reduction level, so no rows — the same scope fence
>               the sealed battery reports, reached from the print side

`[TABLE]` **the same coverage block transcribed:**

| coverage item | predicted | observed | note |
|---|---|---|---|
| leg-A print-key walks | 79 | **84** | +5, cause identified (`small=True` pool difference) |
| at byte-UNEQUAL junctions | 12 | **12 — EXACT** | T3A m=2 (3) · T3C m=2 (3) · T3D m=2 (3) · T3E m=2 (3) |
| leg B fired | 67 | **72**, agreed 72 | of which **45 cross-frame, 27 degenerate** (r2/G2-2) |
| I4C | — | **no rows** | no print-eligible reduction level — the §4 scope fence reached from the print side |

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- Law families: 38 + 84 + 84 + 84 + 72 = **362** ✔ matches the corrected verdict.
- Byte-unequal base walks: 4 rows × 3 = **12** ✔, matching the prediction EXACTLY.
- PW-XFRAME: 45 + 27 = **72** ✔.
- Leg-A reconciliation with leg (C): 45 + 27 + 12 = **84** ✔ = leg-A's count.
- Chamber walks unreached: 4 × 2 = **8** ✔.
- **Five cross-checks, all consistent.**

**CONDITIONALITY:** **The verdict is stated with its hole in the same sentence**: “STILL PRINT-UNCHECKED, by both instruments: the 8 walks on the four byte-unequal CHAMBER rows”. **The 12 byte-unequal base walks are the number G-1 turns on, and they hit their prediction exactly.**

**DERIVATION:** Executed run, transcribed from committed artifacts.

**RESOLUTION TRACE:** statement lines 2803–2833; the preregistration 2766–2783 (`.157`); the struck verdict 2785–2801 (`.158`); the honest prediction accounting 2835–2846 (`.160`).

**TEETH:** five law families GREEN, **12 byte-unequal walks EXACT on prediction**; **27 of 72 PW-XFRAME walks VACUOUS** (`.161`); **8 chamber walks unreached**. Disposition: **executable regression + signed vacuity disclosure + disclosed non-repair**.

---
### EFF.GRTJB.160  [run-record]  §7.4(B) — the honest prediction accounting

**CANONICAL STATEMENT:** verbatim, lines 2835–2846.
**FORM:** bold-headed paragraph.

> “**Honest prediction accounting.** The five LAW predictions hit exactly (0
> violations each). The two COVERAGE counts came in 5 HIGH (84 not 79; leg B 72
> not 67) — a mis-prediction on my side, in the direction of MORE evidence, with
> a fully identified cause: the sealed runner runs its QO and d₀ legs with
> `small=True` (2 samples per row), while this walker uses the full 3-sample pool
> uniformly, giving +1 walk on the single QO tree row and +4 on the four d₀ rows.
> Every other row matches walk-for-walk, and the number that G-1 turns on — the
> 12 walks at byte-unequal junctions, which the sealed battery's print-key leg
> never ran — hit its prediction exactly and is GREEN. **No disagreement with
> the tree identity was found anywhere** (had there been one, the script prints
> both polynomials' coefficient lists and exits nonzero; the DISAGREEMENT
> DISCIPLINE paragraph of its docstring is the standing commitment).”

**MANDATORY ARITHMETIC AUDIT (rule 22):** 84 − 79 = **5** ✔; cause decomposition: +1 (QO tree row) + 4 (d₀ rows) = **5** ✔; leg B 72 − 67 = **5** ✔. **Both mis-predictions are exactly 5 and both are explained by the same `small=True` pool difference.** ✔

**CONDITIONALITY:** **A preregistration that MISSED, disclosed as a miss, with the cause identified and the direction named.** This is the note's model of honest prediction accounting: the law predictions hit exactly; the coverage counts came in high; the number the finding turns on hit exactly.

**DERIVATION:** Run accounting.

**RESOLUTION TRACE:** statement lines 2835–2846; the verdict 2803–2833 (`.159`); PE2's `small=True` observation 840–844 (shard 1 `.54`).

**TEETH:** the DISAGREEMENT DISCIPLINE (the script exits nonzero and prints both coefficient lists on any disagreement) is the tooth that makes “no disagreement was found” informative. Disposition: **executable regression with a disclosed prediction miss**.

---
### EFF.GRTJB.161  [instrument-record]  ★ §7.4(B) — the MANDATORY DISCLOSURE (the repair instrument reproduced its target defect)

**CANONICAL STATEMENT:** verbatim, lines 2848–2879.
**FORM:** bold-headed bracketed block + a fixed-width row list.

> “**[r2, G2-2 — MANDATORY DISCLOSURE: PW-XFRAME IS VACUOUS ON 27 OF ITS 72
> WALKS, and the defect is exactly the one PE1's G-1 charged against the SEALED
> runner's print-key leg — reproduced inside the instrument written to repair
> it.** The gate is `chain_eq` alone (`grt_jb_printwalk.py` L374–376). Now
> `chain_eq` = (`T.Phi[j] == G.phi[j+1]` for all j ≤ m) already forces the leg-B
> DIVISOR `T.Phi[m]` to be byte-equal to the print key `G.phi[m+1]`; so on the
> sub-family where the MULTIPLICAND is byte-equal too (`chat_eq`, i.e.
> Ĉ_m^cls == Ĉ_m^har) leg B calls `pwalk` and `my_divmod` on arguments that are
> BYTE-IDENTICAL to leg A's PW-DIV call, and both are pure deterministic
> functions of those arguments: PW-XFRAME cannot fail there unless PW-DIV already
> did. Counted from the committed `grt_jb_printwalk_results.json`, the rows with
> `chain_eq: true` AND `chat_eq: true` are
>
>     Zp,p=3,T2B|m=1 · Zp,p=2,T2E|m=1 · Fpt,p=3,T2F|m=1 · Zp,p=3,T3B|m=1 ·
>     Zp,p=3,T3F|m=1 · Zp,p=2,I4A|m=1 · Zp,p=2,I4A|m=3 · Zp,p=3,I4B|m=1 ·
>     QO:x4+4x+4/Q2|m=1                                   — 9 rows × 3 = 27 walks
>
> so **the cross-frame evidence rests on the 45 remaining walks** (15 rows,
> `chain_eq` ∧ ¬`chat_eq`), where the harness multiplicand Ĉ_m^har is a
> genuinely different polynomial from the print's Ĉ_m^cls and the print-keyed
> tree is therefore doing work the print frame does not supply; **the 27
> degenerate walks are VACUOUS for cross-frame purposes** and must not be counted
> as cross-frame evidence. How it happened, stated plainly: the file's own smoke
> disclosure records that the FIRST draft gated on (chain byte-equal) AND
> (Ĉ^cls == Ĉ^har) and fired on zero rows; the fix DROPPED the `chat_eq`
> conjunct where it should have NEGATED it, which admits the vacuous subset
> instead of excluding it. Unaffected: LEG A (84 walks, PW-ID/WALK/REASM/DIV, all
> five law predictions 0/0) — that is the evidence which actually closes G-1's
> substance on the base rows, and none of it is degenerate … Also unaffected:
> every count above; only the READING of PW-XFRAME's 72 changes. The corrected
> leg is (C) below.]**”

**MANDATORY ARITHMETIC AUDIT (rule 22):** listed degenerate rows = 9 ✔ (T2B, T2E, T2F, T3B, T3F, I4A m=1, I4A m=3, I4B, QO:x4+4x+4/Q2); 9 × 3 = **27** ✔; 72 − 27 = **45** ✔ over **15 rows** (45/3 = 15) ✔; leg-A reconciliation 45 + 27 + 12 = **84** ✔. **Four cross-checks, all consistent.**

**CONDITIONALITY:** **The disclosure is doubly damning and the note says so in its own header: the defect “is exactly the one PE1's G-1 charged against the SEALED runner's print-key leg — reproduced inside the instrument written to repair it”.** **And the cause is stated plainly: “the fix DROPPED the `chat_eq` conjunct where it should have NEGATED it.”** **This is the note's clearest bred-defect record** and the reason shard 1 §6.3 recommends a `bred-defect` marker.

**DERIVATION:** Gate logic + purity: `chain_eq` already forces the divisor byte-equal; adding `chat_eq` forces the multiplicand byte-equal; `pwalk` and `my_divmod` are pure deterministic functions of those arguments, so PW-XFRAME cannot fail where PW-DIV did not.

**RESOLUTION TRACE:** statement lines 2848–2879; the disposition 764–783 (shard 1 `.50`); the original charge 660–672 (shard 1 `.47`); the corrected leg 2897–2948 (`.22`, `.23`).

**TEETH:** **signed vacuity disclosure** (27 of 72 carry no information) + **accepted-with-decorrelation-supplied** (the 45 that do, and leg A's 84).

---
### EFF.GRTJB.162  [preregistration]  §7.4(C) — the gate repair, with its disclosed limitation

**CANONICAL STATEMENT:** verbatim, lines 2897–2912.
**FORM:** bold-headed paragraph.

> “**[r2] (C) THE CROSS-FRAME GATE REPAIR — `grt_jb_printwalk2.py`** (post-seal,
> r2's own instrument, with its own mini two-commit seal: the script with its
> prereg block committed UNRUN at r2 commit 1 `67bf0c4`, md5
> `6c6318f7fc6570a2d454389b38441329`; output/JSON committed at r2 commit 2 and
> the verdict below transcribed from them). It re-gates the cross-frame family on
> **`chain_eq` AND NOT `chat_eq`** and replaces the degenerate re-execution by a
> MECHANICAL DEGENERACY CERTIFICATE (byte-identity of the whole argument tuple:
> f·Ĉ^har == f·Ĉ^cls and Φ_m^har == φ_{m+1}^cls), so nothing is re-run where
> re-running is vacuous. **Disclosed limitation, stated in the script's own
> docstring: this is a GATE REPAIR, not a decorrelated second instrument** — it
> imports the byte-frozen r1 walker and reuses its print-side machinery
> (`print_corr`/`pcells`/`plnorm`/`pwalk`/`my_divmod`/`cdivmod`/`print_elig`)
> precisely so that the ONLY difference from the r1 run is the gate and the
> census; it inherits the r1 walker's independence properties and adds nothing to
> them. All predictions were read off the committed r1 JSON and are on record
> before the run (the blind content is the verdict per family).”

**TYPE JUSTIFICATION (rule 19):** `preregistration` — the design and seal, emitted separately from `.163`'s `run-record`.

**CONDITIONALITY:** **The limitation is disclosed in the script's OWN docstring, not only in the note: “a GATE REPAIR, not a decorrelated second instrument”.** It **imports** the frozen r1 walker by design, so it adds no independence. **And the preregistration is partially trivial by construction: “All predictions were read off the committed r1 JSON” — so only the per-family VERDICT is blind.** The note states both limitations.

**PIN VERIFICATION (rule 23):** `grt_jb_printwalk2.py` **EXISTS**; md5 `6c6318f7fc6570a2d454389b38441329` **EXACT at HEAD**; `67bf0c4` → **commit**; both output artifacts **EXIST**.

**DERIVATION:** Instrument design.

**RESOLUTION TRACE:** statement lines 2897–2912; the defect it repairs 2848–2879 (`.161`); the verdict 2914–2931 (`.163`).

**TEETH:** the mini-seal; the per-sample non-degeneracy certificate is `.163`'s.

---
### EFF.GRTJB.163  [run-record]  §7.4(C) — the gate-repair verdict, and the purity softening

**CANONICAL STATEMENT:** verbatim, lines 2914–2948 — the verdict, the three-family table, the CENSUS block, and the r3/F-6(b) softening.
**FORM:** bold verdict + Markdown table + fixed-width census + bracketed correction.

> “**VERDICT (r2 commit 2, transcribed from `grt_jb_printwalk2_output.txt` /
> `_results.json`; exit 0, elapsed 0.1 s, 100 law samples, seal commit 67bf0c4):
> ALL THREE FAMILIES GREEN, EVERY SAMPLE COUNT ON ITS PREDICTION.**”

`[TABLE]` **the three gate-repair families (lines 2918–2922):**

| family | claim keyed | pred | obs | samples (pred) | verdict |
|---|---|---|---|---|---|
| **PW2-XFRAME** | HONEST cross-frame (`chain_eq` ∧ ¬`chat_eq`): print-keyed tree on `f·Ĉ_m^har` == harness-key division, **+ a NON-DEGENERACY certificate per sample** (`f·Ĉ^har ≠ f·Ĉ^cls`) | 0 | 0 | 45 (45) | GREEN, agreed 45/45 |
| **PW2-DEGEN** | the complement (`chain_eq` ∧ `chat_eq`): degeneracy **CERTIFIED, comparison NOT re-run** | 0 | 0 | 27 (27) | GREEN — all 27 confirmed vacuous |
| **PW2-RECON** | row-for-row reconciliation against the committed r1 JSON (`chain_eq`/`chat_eq`/walks per row; **45+27+12 = 84** = r1's leg-A count) | 0 | 0 | 28 rows (28) | GREEN |

**Double-emission (rule 14) — the CENSUS block, verbatim (lines 2924–2931):**

>     CENSUS  cross-frame walks 45 over 15 rows (predicted 45) — agreed 45
>             DEGENERATE walks   27 over  9 rows (predicted 27) — certified
>             chain-divergent    12 over  4 rows (predicted 12) — leg B not
>                                claimable (the harness divisor is a different
>                                polynomial): T3A m=2, T3C m=2, T3D m=2,
>                                T3E m=2 — i.e. exactly the four byte-unequal
>                                base rows, where leg A carries the evidence

**The purity softening, verbatim (lines 2934–2948):**

> “**What (C) buys:** the cross-frame claim now
> rests on 45 walks each carrying a machine certificate that the multiplicand
> genuinely differs between the frames (the positive non-degeneracy leg the r1
> walker lacked), and ~~the vacuity of the other 27 is machine-established rather
> than argued~~ **[r3, F-6(b) — SOFTENED BY EXACTLY ONE STEP, which is what the
> certificate does and does not establish: what `PW2-DEGEN` establishes
> MECHANICALLY is the BYTE-IDENTITY of the whole leg-B argument tuple
> (`fCh == fC` and `div_har == key`, 27/27); the step from byte-identity to
> vacuity is the PURITY of `pwalk`/`my_divmod` as deterministic functions of
> those arguments, which is ARGUED in the r2 block and not machine-checked. Read:
> **the byte-identity of the argument tuple is machine-certified on all 27, and
> their vacuity follows from purity**]**. **What it does not buy:** no new decorrelation (same machinery, by
> design), no grade change, still no chambers, and still nothing at the 12
> chain-divergent walks (leg B is not claimable there) nor at the 8 unreached
> byte-unequal chamber walks (G2-3).”

**MANDATORY ARITHMETIC AUDIT (rule 22):**
- 45 + 27 + 12 = **84** ✔ = leg-A's walk count, as PW2-RECON itself asserts.
- Rows: 15 + 9 + 4 = **28** ✔ = PW2-RECON's row count.
- Walks per row: 45/15 = 3 ✔; 27/9 = 3 ✔; 12/4 = 3 ✔ — **uniform 3 walks per row**, consistent throughout.
- Law samples: 45 + 27 + 28 = **100** ✔ matches “100 law samples”.
- **Five cross-checks, all consistent — and every sample count hit its prediction exactly.**

**CONDITIONALITY:** **The r3/F-6(b) softening is a one-step epistemic correction that matters**: the certificate establishes BYTE-IDENTITY mechanically; the inference to VACUITY rests on PURITY, which is **argued, not machine-checked**. **And the “what it does not buy” list is four items long**, including the two standing holes (12 chain-divergent walks, 8 chamber walks).

**DERIVATION:** Executed run, transcribed from committed artifacts.

**RESOLUTION TRACE:** statement lines 2914–2948; the preregistration 2897–2912 (`.162`); the disclosure it answers 2848–2879 (`.161`); the r3/F-6(b) disposition 908–911 (shard 1 `.55` STEP 4).

**TEETH:** **executable regression with a per-sample non-degeneracy certificate**, plus a **signed epistemic softening** (byte-identity machine-certified; vacuity argued from purity). Disposition: **accepted-with-decorrelation-supplied for the 45; disclosed non-repair for the 12 + 8**.

---
### EFF.GRTJB.164  [SERIES: the POST-FREEZE APPEND ARC, eight dated members]

**SERIES DECLARATION (rule 28).** Lines 2950–3327 carry a chronological arc of dated appends over the note's post-freeze life. They are emitted as a series with membership and order recorded, so a merge run can reconstruct the chronology mechanically. **TERMINAL member: `.171`/`.172`/`.173` (the 2026-08-12 certifier annex), which is the correction of record at HEAD.**

`[TABLE — compiler ledger]` **The post-freeze arc.**

| unit | member | source lines | date | kind | what it does |
|---|---|---|---|---|---|
| `.164` | footer arc (r1–r8 dated lines) | 2950–3101 | 2026-08-08 campaign | `run-record` series | the eight round-closing paragraphs; the arc restated a second time |
| `.165` | ★ ACCEPTANCE RECORD | 3105–3119 | 2026-08-06 | `acceptance-box` | **ACCEPTED at 2/2** (PE9 `b0b4c3a` CLEAN, PE10 `6d548f3` CLEAN) |
| `.166` | FOLD ANNEX **E-1** | 3123–3133 | 2026-08-07 | `supplier-finding` (inbound) | the “(R-coll)” label read root-inclusively |
| `.167` | FOLD ANNEX **E-2** | 3135–3142 | 2026-08-07 | `supplier-finding` (inbound) | W2-C3's grade at the supplier's proved/measured split |
| `.168` | ANNEX (fold-carry closure) | 3146–3161 | 2026-08-08 | `changes-record` | **W-2 and J-A upgraded to ACCEPTED 2/2**; the four-member frontier UNCHANGED |
| `.169` | sol C3/E3 adjudication head | 3165–3196 | 2026-08-12 | `changes-record` | the CHALLENGE adjudicated: 1 ARTIFACT, 1 RESOLVED-ALREADY, **2 REAL** |
| `.170` | adjudication findings 1 and 3 | 3181–3196, 3247–3261 | 2026-08-12 | `changes-record` | the two findings that did NOT require a repair, with their grounds |
| `.171`–`.173` | ★ CERTIFIER ANNEX **E-3**, **E-4** | 3197–3327 | 2026-08-12 | `supplier-finding` ×2 + verification record | **the two REAL findings' repairs — the only corrections in the stack that touch a DISPLAYED MATHEMATICAL STATEMENT** |

---

### EFF.GRTJB.164  [run-record]  the footer arc (r1–r8)

**CANONICAL STATEMENT:** [ASSEMBLED — the eight dated footer paragraphs, lines 2950–3101, quoted at their opening and closing clauses; the arc recitals are tabulated below rather than repeated eight times.]

> “— J-B COMPOSER unit, campaign date 2026-08-08 (wallclock 2026-08-04);
> **[r1] repaired 2026-08-08 campaign (wallclock 2026-08-05) against JB-PE1;
> acceptance counter still 0/2.** …”

> “**[r8] repaired an EIGHTH time, 2026-08-08 campaign (wallclock 2026-08-06),
> against JB-PE8 (0 CRITICAL + 0 gaps + 1 minor, the sixth acceptance attempt,
> which did not land …). THE ONE-QUOTATION
> ROUND … **No §2–§5 identity moved; no fence, frontier or grade
> moves; all four instruments byte-frozen (md5s re-verified at their sealed
> values); note-only, no new probe.** Arc:
> PE1 (1C+9G) → r1 → PE2 (0C+7G) → r2 → PE3 (0C+8G) → r3 → PE4 (0C+8G) → r4 →
> PE5 (0C+5G) → r5 → PE6 (0C+2G+1m) → r6 → PE7 (0C+1G+2m) → r7 →
> PE8 (0C+0G+1m) → r8 →
> **JB-PE9 = the next acceptance attempt**; acceptance counter still **0/2**.**”

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION (rule 26) on the terminal clause** — “JB-PE9 = the next acceptance attempt; acceptance counter still 0/2” is falsified by `.165`. **No text supersedes it** (see OPEN-CALL 1). **The r1–r7 arc lines are STRUCK in the source** (`~~Arc: …~~`) as each round extended them; only r8's is live.

**ARITHMETIC AUDIT (rule 22) — the arc, cross-checked against the S-STATUS series (shard 1 `.03`–`.10`) and the acceptance record's “Full arc”:**
- Passes: PE1…PE8 = **8** ✔ matches “EIGHT hostile passes RUN”.
- Rounds: r1…r8 = **8** ✔.
- Verdicts: 1C+9G, 0C+7G, 0C+8G, 0C+8G, 0C+5G, 0C+2G+1m, 0C+1G+2m, 0C+0G+1m — **identical to the S-STATUS series** ✔ and **identical to the acceptance record's recital** ✔.
- **Three independent statements of the same arc, all consistent.**
- Acceptance attempts: PE3 (1st), PE4 (2nd), PE5 (3rd), PE6 (4th), PE7 (5th), PE8 (6th) = **6 that did not land**, then PE9 + PE10 clean = **8 attempts, 2 clean** ✔ consistent with 2/2.
- **Trend:** critical findings 1 → 0 (from PE2 onward); gaps 9 → 7 → 8 → 8 → 5 → 2 → 1 → 0. **Monotone to zero from PE4.**

**DERIVATION:** Round records.

**RESOLUTION TRACE:** statement lines 2950–3101; the S-STATUS series 8–169 (shard 1 `.03`–`.10`); the acceptance record 3105–3119 (`.25`).

**PIN VERIFICATION:** all commit hashes in the footer resolve — the 29-hash census is at shard 1 §3.1.

**TEETH:** the four byte-frozen instruments, re-verified every round; **4/4 md5s EXACT at HEAD**.

---
### EFF.GRTJB.165  [acceptance-box]  ★ THE ACCEPTANCE RECORD

**CANONICAL STATEMENT:** verbatim, lines 3107–3119.
**FORM:** display (a starred H2 block).

> “**THIS NOTE IS ACCEPTED at 2/2** — PE9 (b0b4c3a, CLEAN 0C/0G/0m; the
> floor-cocycle re-derivation of JB-EPS + 31,941-check fresh leg) and PE10
> (6d548f3, CLEAN; the cone-decomposition re-derivation of the u ≥ 0
> theorem, 326,206/0, + support-function duality for JB-VTX, 106,562/0).
> Full arc: PE1 (1C+9G) → r1 → PE2 (0C+7G) → r2 → PE3 (0C+8G) → r3 matrix
> → PE4 (0C+8G) → r4 → PE5 (0C+5G) → r5 → PE6 (0C+2G+1m) → r6 → PE7
> (0C+1G+2m) → r7 → PE8 (0C+0G+1m) → r8 → PE9 CLEAN → PE10 CLEAN. Ten
> hostile passes, eight repair rounds. **WHAT IS ACCEPTED**: the four
> junction identities (JB-DEV, JB-VTX, JB-ID, JB-TREE) and JB-CREAD as
> fenced by the §0M conditionality matrix at HEAD — riding [RMG] accepted,
> W-2/J-A at their own arc grades, with the four-member NO-LEG frontier
> (rows 4/5/12/22) as the note's honest open cells. Machine record: four
> byte-frozen instruments, all green.”

**SUPERSESSION KIND:** `replacement` for the GRADE — but **note carefully: it supersedes the grade WITHOUT expressly superseding the body sentences that state the old grade.** That asymmetry is OPEN-CALL 1.

**TARGETS (rule 24):** by content (not by an explicit supersession clause): `.02`, `.03`–`.10` (the whole S-STATUS series), `.37` (the grade cap's Standing bullet), `.140` (JB-BOX-6's counter and proof-grade prohibition), `.149` (§7.2's “attempt grade 0/2” prefixes), `.151` (§7.3's counter clause), `.153` (“The old counter line's ‘0/2’ remains true”), `.164` (the footer arc).

**★ WHAT IS ACCEPTED, and the three riders that travel with it:**
1. **The scope:** “the four junction identities (JB-DEV, JB-VTX, JB-ID, JB-TREE) and JB-CREAD **as fenced by the §0M conditionality matrix at HEAD**”. **Acceptance is OF THE FENCED STATEMENTS, not of unfenced ones** — so §0M (shard 1 `.20`) is part of what was accepted.
2. **The supplier grades at acceptance time:** “riding [RMG] accepted, **W-2/J-A at their own arc grades**” — later upgraded by `.168`.
3. **The open cells:** “with the **four-member NO-LEG frontier (rows 4/5/12/22)** as the note's honest open cells”. **Acceptance did NOT close the frontier**, and `.168` re-confirms it is UNCHANGED.

**ARITHMETIC AUDIT (rule 22):** “Ten hostile passes, eight repair rounds” — PE1…PE10 = **10** ✔; r1…r8 = **8** ✔. Frontier = rows 4, 5, 12, 22 = **4** ✔ matching §0M summary point (1) and `.168`. **PE9's and PE10's legs are NEW and independent:** the floor-cocycle re-derivation of JB-EPS (31,941 checks), the cone-decomposition re-derivation of the `u ≥ 0` theorem (326,206/0), and support-function duality for JB-VTX (106,562/0) — **three re-derivations by different methods than the note's own.**

**CONDITIONALITY:** **The acceptance is conditional on exactly what it names.** It does not upgrade [RMG], W-2, J-A or LED-Λ; it does not close the frontier; it does not retire any gate.

**PIN VERIFICATION:** `b0b4c3a` → **commit**; `6d548f3` → **commit**.

**DERIVATION:** Orchestrator record of two clean hostile passes.

**RESOLUTION TRACE:** statement lines 3107–3119; the arc 2950–3101 (`.164`) and 8–169 (shard 1); the frontier 395–422 (shard 1 `.26`); the supplier upgrade 3148–3161 (`.28`).

**TEETH:** **PE10's cone-decomposition re-derivation of the `u ≥ 0` theorem (326,206/0) is a genuinely different method from the note's four-line lattice argument**, and PE9's floor-cocycle re-derivation of JB-EPS likewise. Disposition: **accepted-with-decorrelation-supplied at the strongest level in the stack** — two clean passes, three method-diverse re-derivations.

---
### EFF.GRTJB.166  [supplier-finding]  ★ FOLD ANNEX E-1 — the “(R-coll)” label, root-inclusive

**CANONICAL STATEMENT:** verbatim, lines 3123–3133 (the annex head and E-1).
**FORM:** display (a starred H2 head) + bold-headed paragraph.

> “## ★ FOLD ANNEX (orchestrator, 2026-08-07): two dated errata on this accepted note (no inline text altered; this annex is the correction of record) ★
>
> **E-1 (the "(R-coll)" subordinate label, from GRTJA PE2 FINDING 1, report
> 9040961)**: J-A's (R-coll) perimeter as originally displayed omitted the
> root-level (q = m) JA-VDIND condition; JA r2 (5d95805) applied the
> root-inclusive extension, verified on all 66 witnesses. THIS NOTE's
> operative fence was already correct (root triviality a HYPOTHESIS at
> every m ≥ 2 — PE2's own adjudication: uncontaminated); only the
> subordinate "(R-coll)" LABEL in the §0M column-(c) apparatus inherited
> the pre-extension reading. Wherever this note's text says "(R-coll)", read
> the root-inclusive form of GRTJA at HEAD (≥ 5d95805).”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding`, **INBOUND** — a defect found at the supplier (GRTJA PE2 FINDING 1) and discharged at the supplier (JA r2), with only a LABEL propagating here.

**SUPERSESSION KIND:** `provenance-rider` — a label re-pointed to the supplier's corrected form; **the operative fence is untouched**.

**TARGETS (rule 24):** every occurrence of “(R-coll)” — `.15` (§0M column (c)), `.34` (the grade cap's JB-CREAD bullet), `.44` (r1/F1), `.93` (the reading fence), `.127` (the theorem), `.132` (surface 5), `.136` (JB-BOX-2), `.149` (§7.2's JB-CREAD row), `.151` (§7.3's downstream notice).

**CONDITIONALITY:** **The annex explicitly certifies that this note's OPERATIVE fence was already correct** — “root triviality a HYPOTHESIS at every m ≥ 2 — PE2's own adjudication: uncontaminated”. **So E-1 is a label repair with zero mathematical consequence for GRTJB, and the annex says so.** The freeze declaration is in the head: “**no inline text altered; this annex is the correction of record**”.

**DERIVATION:** Supplier record.

**PIN VERIFICATION:** `9040961` → **commit**; `5d95805` → **commit**; the supplier's extension “verified on all 66 witnesses” is a claim about GRTJA's own record, **not re-verified here**.

**RESOLUTION TRACE:** statement lines 3123–3133; targets as listed above.

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:(R-coll)` — grep-verified count **7** · `JA-VDIND` — **21**.

**TEETH:** **AUDIT — transfer audit** (a supplier's hostile pass propagating a label correction downstream). No battery applies.

---
### EFF.GRTJB.167  [supplier-finding]  ★ FOLD ANNEX E-2 — W2-C3's grade, re-pointed

**CANONICAL STATEMENT:** verbatim, lines 3135–3142.
**FORM:** bold-headed paragraph.

> “**E-2 (row 15's W-2 grade citation, from GRTW2 r1, 8d5e3fa)**: W-2's
> W2-C3 was re-graded at its r1 from "strictly at every level (44/44)" to
> proved-to-first-twist (38/44) / measured above (6/44, riding W2-OPEN-2);
> this note's row-15/W-2 citations predate that re-grade and are
> pin-protected (as-of quotes). Wherever this note cites W2-C3's grade,
> the supplier's current form (GRTW2 at HEAD, ≥ 94534df: forward-direction
> W2-ID1 + OPEN-2a) governs. No identity or count in this note consumes
> the re-graded clause beyond its still-valid instance evidence.”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding`, **INBOUND**.

**SUPERSESSION KIND:** `as-of scoping` (the note's citations are pin-protected as-of quotes) **+** `provenance-rider` (the supplier's current form governs). **Two kinds, and the annex needs both** — the frozen quotes stay true as-of, while the live reading changes.

**TARGETS (rule 24):** `.16` (§0M column (d)), `.20` row 15, `.33` (the grade cap's JB-TREE bullet), `.89` (JB-DEV(i)), `.110` (JB-TREE's head), `.117` (surface 4), `.136` (JB-BOX-2), `.149` (§7.2's JB-TREE row).

**ARITHMETIC AUDIT (rule 22):** 38 + 6 = **44** ✔ — the re-grade partitions the same 44 instances into proved (38) and measured (6). **The count is conserved; what changed is the grade of 6 of them.**

**CONDITIONALITY:** **“No identity or count in this note consumes the re-graded clause beyond its still-valid instance evidence.”** — so the 6 measured-above instances are not load-bearing for any GRTJB statement. **And the E3 adjudication's finding 3 (`.170`) later re-affirms this propagation rule and draws the sharper consequence: “Acceptance of W-2 accepts the honest box; it does not turn its measured-above region into a theorem.”**

**DERIVATION:** Supplier record.

**PIN VERIFICATION:** `8d5e3fa` → **commit**; `94534df` → **commit**.

**RESOLUTION TRACE:** statement lines 3135–3142; targets as listed; the re-affirmation 3247–3261 (`.170`); the supplier's acceptance 3148–3161 (`.168`).

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-C3` — count **22** · `W2-OPEN-2` — **60** · `W2-C1` — **22**.

**TEETH:** **AUDIT — transfer audit**. Disposition: foreign-note grade propagation, with the instance evidence still valid.

---
### EFF.GRTJB.168  [changes-record]  ★ the 2026-08-08 ANNEX — supplier grades upgraded, frontier UNCHANGED

**CANONICAL STATEMENT:** verbatim, lines 3146–3161.
**FORM:** display (an H2 head) + a blockquoted dated append.

> “## ANNEX (dated append; the frozen body is not edited)
>
> > **[ANNEX 2026-08-08, orchestrator, fold-carry closure — the supplier
> arc grades in the acceptance record.]** The record above accepts this note
> "riding [RMG] accepted, W-2/J-A at their own arc grades". Both arc-graded
> suppliers have since been ACCEPTED at 2/2: GRTW2 at adc6cf3 (2026-08-07;
> W2-C3 at its honest proved-to-first-twist (38/44) / measured-above grade,
> W2-OPEN-2/OPEN-2a the accepted BOX — the supplier's acceptance record
> names "JB's W2-C1 restriction" as now riding an ACCEPTED supplier at its
> fenced scope) and GRTJA at 17d2a32 (2026-08-07; body byte-frozen, md5
> cba309ce @ f131c53). Consequently E-1's governing form ("the
> root-inclusive form of GRTJA at HEAD (≥ 5d95805)") and E-2's ("GRTW2 at
> HEAD, ≥ 94534df") now read ACCEPTED suppliers' frozen texts. The
> four-member NO-LEG frontier (rows 4/5/12/22) is UNCHANGED — those stay
> the note's honest open cells. Direction: FAVORABLE (supplier grades only;
> no identity, fence, or census moves).”

**SUPERSESSION KIND:** `provenance-rider` — supplier grades updated; **no identity, fence or census moves**, and the annex says so.

**TARGETS (rule 24):** every “W-2 … at ATTEMPT grade” / “J-A … at ATTEMPT grade” clause — `.40` (the consumption list), `.02`/`.03`–`.10` (the S-STATUS weld-dependency line), `.89`, `.110`, `.132` (surface 5's “J-A / W-2 / LED-Λ at attempt”), `.151` (§7.3's CONSUMES bullet).

**★ THREE THINGS THIS ANNEX DOES NOT DO, all load-bearing:**
1. **It does NOT upgrade LED-Λ.** LED-Λ is not named; its ATTEMPT grade rides at HEAD, capping JB-TREE(iii) (shard 2 `.114`, `.138`, and shard 2 OPEN-CALL 5).
2. **It does NOT close the frontier.** “The four-member NO-LEG frontier (rows 4/5/12/22) is UNCHANGED — those stay the note's honest open cells.” **Third independent statement of the same four.**
3. **It does NOT turn W2-C3's measured-above region into a theorem** — GRTW2 is accepted “at its honest proved-to-first-twist (38/44) / measured-above grade, W2-OPEN-2/OPEN-2a the accepted BOX”. `.170`'s finding 3 makes this explicit.

**CONDITIONALITY:** **Direction FAVORABLE, and strictly so** — “supplier grades only; no identity, fence, or census moves”.

**DERIVATION:** Orchestrator record.

**PIN VERIFICATION:** `adc6cf3` → **commit**; `17d2a32` → **commit**; `f131c53` → **commit**; `5d95805` → **commit**; `94534df` → **commit**. **5/5 resolve.** The GRTJA body md5 `cba309ce` is a truncated pin against a note this compiler did not re-hash — recorded as a checkable pin.

**RESOLUTION TRACE:** statement lines 3146–3161; the acceptance record 3107–3119 (`.165`); E-1/E-2 3123–3142 (`.166`, `.167`); the frontier 395–422 (shard 1 `.26`).

**TEETH:** **AUDIT — transfer audit**. Disposition: supplier-grade propagation, favourable, non-moving.

---
### EFF.GRTJB.169  [changes-record]  the 2026-08-12 sol C3/E3 adjudication — head and disposition

**CANONICAL STATEMENT:** verbatim, lines 3165–3179.
**FORM:** display (an H3 head) + paragraph.

> “### Dated adjudication + corrections (2026-08-12 — sol certification C3/E3: the as-built challenge adjudicated at HEAD)
>
> The sol-5.6 as-built read of this note (gpt-5.6-sol high,
> runs/cert/C3_grtjb_output.log, 2026-08-12) returned CHALLENGE
> (3 GAP). The E3 certification run (gpt-5.6-sol high,
> runs/cert2/E3_grtjb_output.log) adjudicated: finding 1 ARTIFACT (the
> 2/2 acceptance record IS at HEAD; PE9's "1/2" was historically
> correct at PE9), finding 3 RESOLVED-ALREADY (Fold Annex E-2's
> "wherever this note cites W2-C3's grade, the supplier's current form
> governs" propagation rule), findings 2 and 4 REAL with the repairs
> E-3/E-4 below (abscissa-run re-display of JB-VTX(c) routing
> attained-grid counts to JB-VTX(d4); off-perimeter status corrected
> from "FALSE" to "NOT SUPPLIED"). Everything above this heading is
> byte-untouched by this append. The E3 adjudication, transcribed
> unaltered:”

**TYPE JUSTIFICATION (rule 19 / 13):** `changes-record` — the adjudication's disposition table. The two REAL findings' repairs are `.172`/`.173`.

**★ THE DECORRELATION FACT, and it is the most important epistemic point in this shard:** **this challenge came from a DIFFERENT MODEL (gpt-5.6-sol high) reading the note as-built, AFTER ten hostile passes and an acceptance at 2/2 — and it found TWO REAL defects in displayed mathematics that all ten passes had missed.** One of them (E-3) is a **false lemma** in a live theorem clause.

**ARITHMETIC AUDIT (rule 22):** findings = 4; dispositions = 1 ARTIFACT + 1 RESOLVED-ALREADY + **2 REAL** = **4** ✔. The C3 run reported “CHALLENGE (3 GAP)”; the E3 run adjudicates **four** numbered findings. **The 3-vs-4 mismatch between the C3 gap count and the E3 finding count is not explained in the note** — recorded as **source defect 4** in §8; the four adjudicated findings are the operative record.

**CONDITIONALITY:** **The freeze is declared in this very paragraph: “Everything above this heading is byte-untouched by this append.”** And the transcription discipline: “**The E3 adjudication, transcribed unaltered**”.

**PIN VERIFICATION (rule 23):** `runs/cert/C3_grtjb_output.log` and `runs/cert2/E3_grtjb_output.log` are named as the evidence. **Both paths are cited; this compiler did not re-read them** (they are run logs, not repo statements) — recorded as checkable pins.

**DERIVATION:** Adjudication record.

**RESOLUTION TRACE:** statement lines 3165–3179; the transcribed findings 3181–3196 and 3247–3261 (`.170`); the repairs 3197–3245 and 3263–3312 (`.172`, `.173`); the verification record 3314–3327 (`.171`).

**TEETH:** **AUDIT — decorrelated-model audit** (rule 27), and the note names it as such by construction. **This is the finding class the whole rule exists for.**

---
### EFF.GRTJB.170  [changes-record]  the two findings that did NOT require a repair

**CANONICAL STATEMENT:** [ASSEMBLED — finding 1 (lines 3181–3191) and finding 3 (lines 3247–3261), quoted verbatim at their load-bearing clauses.]

**Finding 1 — ARTIFACT (lines 3181–3191):**

> “1. ARTIFACT — the 2/2 acceptance is recorded at HEAD.
>
> The finding treats PE9's contemporaneous “FIRST clean pass … 1/2” as the final state and requires the PE10 report to be embedded in this proof note. But the later authoritative block states:
>
> > “**THIS NOTE IS ACCEPTED at 2/2** — PE9 (b0b4c3a, CLEAN …) and PE10 (6d548f3, CLEAN …).”
>
> … Thus PE9's 1/2 statement is historically correct at PE9, while the dated orchestrator acceptance record certifies the subsequent second clean pass. The proof note's acceptance record—not an inline copy of every hostile-pass report—is the procedural source of record.”

**Finding 3 — RESOLVED-ALREADY (lines 3247–3261):**

> “3. RESOLVED-ALREADY — Fold Annex E-2 already propagates W2-C3's mixed grade.
>
> … Crucially, it then gives the global propagation rule:
>
> > “**Wherever this note cites W2-C3's grade, the supplier's current form … governs.**”
>
> The later `[ANNEX 2026-08-08, orchestrator, fold-carry closure]` preserves rather than upgrades that split:
>
> > “W2-C3 at its honest proved-to-first-twist (38/44) / measured-above grade, W2-OPEN-2/OPEN-2a the accepted BOX.”
>
> Therefore the frozen body's earlier `PROVED` labels cannot be read as proving the six above-first-twist instances: E-2 makes the supplier's proved/measured split govern every W2-C3 citation, including row 15 and the JB-TREE surfaces. **Acceptance of W-2 accepts the honest box; it does not turn its measured-above region into a theorem.** The prior finding overlooked the annex's explicit “wherever … governs” propagation rule.”

**CONDITIONALITY:** **Finding 3's closing sentence is a genuine sharpening even though the finding is dismissed**: it states, more explicitly than E-2 itself did, that **the frozen body's `PROVED` labels cannot be read as proving the six above-first-twist W2-C3 instances**. **A chapter cut must carry that.** Finding 1 establishes the procedural rule that **the acceptance record, not an inline copy of every report, is the source of record** — which is exactly what makes OPEN-CALL 1's asymmetry a real problem rather than a formality.

**DERIVATION:** Adjudication against the note's own HEAD text.

**RESOLUTION TRACE:** statement lines 3181–3191, 3247–3261; the acceptance record 3107–3119 (`.165`); E-2 3135–3142 (`.167`); the supplier annex 3148–3161 (`.168`).

**TEETH:** **AUDIT — decorrelated-model audit**, adjudicated against the repo's own text.

---
### EFF.GRTJB.171  [changes-record]  the orchestrator verification record

**CANONICAL STATEMENT:** verbatim, lines 3314–3327.
**FORM:** italic parenthetical closing block.

> “*(The adjudication above was produced by the E3 certification run
> (gpt-5.6-sol high, runs/cert2/E3_grtjb_output.log, 2026-08-12);
> orchestrator verification before transcription — E-3's shear algebra
> re-derived (image difference vector (Δi, e_qΔu + h_qΔi), slope law
> σ′ = e_qσ + h_q, the (e_q,h_q) = (2,1) witness maps (0,1)–(2,0) to
> the horizontal (0,2)–(2,2) containing (1,2): abscissa run preserved,
> ambient lattice data not); E-4's f = 1 instance re-checked (sole
> digit A₀ = 1, both valuations 0, point set {(0,0)} fixed by Σ_q —
> so off-perimeter instancewise agreement is possible and "FALSE" was
> an overclaim); the ARTIFACT rebuttal checked against the HEAD
> acceptance block ("ACCEPTED at 2/2 — PE9 … and PE10 …"); the
> RESOLVED-ALREADY quote checked against Fold Annex E-2 at HEAD.
> Transcribed unaltered per the standing division of labor. Ledger:
> row 21 → both repairs folded, awaiting sol discharge (cert3).)*”

**CONDITIONALITY:** **This is the note's model for consuming a decorrelated audit: the orchestrator RE-DERIVED each finding before transcribing it, and records what it checked.** **All four checks are itemised, and two of them are mathematics re-done independently** (E-3's shear algebra with the explicit `(2,1)` witness; E-4's `f = 1` instance). **The status is “awaiting sol discharge (cert3)”** — the repairs are folded but the arc is not closed.

**INDEPENDENT RE-DERIVATION BY THIS COMPILER (E-3's witness).** `Σ_q(i,u) = (i, e_q u + h_q i)` at `(e_q,h_q) = (2,1)`: `(0,1) ↦ (0, 2·1 + 1·0) = (0,2)`; `(2,0) ↦ (2, 2·0 + 1·2) = (2,2)`. **The image edge is horizontal from (0,2) to (2,2) and contains the lattice point (1,2), which is not the image of any lattice point on the source edge** (the source edge from `(0,1)` to `(2,0)` has primitive step `(2,−1)` and contains no interior lattice point). **So the abscissa run 2 is preserved and the ambient lattice length changes from 1 to 2 — E-3's witness is EXACT.** ✔

**INDEPENDENT RE-DERIVATION BY THIS COMPILER (E-4's instance).** For `f = 1`: the `Φ_q`-development has the sole digit `A₀ = 1`; `w_q(1) = 0` and `v_{q+1}(1) = 0` for any normalized valuation; both frames give the point set `{(0,0)}`, and `Σ_q(0,0) = (0, e_q·0 + h_q·0) = (0,0)`. **So (VAL) and the pointwise shear hold for this instance regardless of the bytes of positive-level keys — E-4's instance is EXACT.** ✔

**DERIVATION:** Verification record.

**RESOLUTION TRACE:** statement lines 3314–3327; the repairs 3197–3245 (`.172`) and 3263–3312 (`.173`).

**TEETH:** **AUDIT — decorrelated-model audit, with in-house re-derivation before transcription.** Disposition: **accepted-with-decorrelation-supplied**, and re-derived a third time here.

---
### EFF.GRTJB.172  [supplier-finding]  ★★ CERTIFIER ANNEX E-3 — JB-VTX(c): abscissa run, not ambient lattice data

**CANONICAL STATEMENT:** verbatim, lines 3197–3245 — the annex head, the withdrawal, the corrected display, and the consumer sweep.
**FORM:** display (a starred H2 head) + bold-headed blocks + a numbered sweep.

> “## ★ CERTIFIER ANNEX (2026-08-12): corrections of record to the frozen accepted body ★
>
> **E-3 (JB-VTX(c): abscissa run, not ambient lattice data).** The sentence in
> §3(c) saying that the shear “preserves lattice data” is WITHDRAWN. The shear
>
>     Σ_q(i,u) = (i, e_q·u + h_q·i)
>
> is not unimodular when e_q > 1. For an edge with difference vector
> (Δi, Δu), its image has difference vector
>
>     (Δi, e_q·Δu + h_q·Δi),
>
> so the abscissa run Δi is preserved and the slope transforms by
>
>     σ′ = e_q·σ + h_q,
>
> but the ambient-lattice primitive step and lattice length need not be
> preserved. For example, at (e_q,h_q) = (2,1), the edge from (0,1) to (2,0)
> maps to the horizontal edge from (0,2) to (2,2), whose ambient lattice
> contains the additional point (1,2).
>
> **CORRECTED DISPLAY OF JB-VTX(c).** A print side of slope σ over
> [i₀,i₁] maps to a sheared side of slope e_q·σ+h_q over the same
> [i₀,i₁]; hence its abscissa run Δi := i₁−i₀ is preserved. If the source
> slope is −h/e in lowest terms, its PRINT-side degree remains the
> source-defined integer d := Δi/e and is recoverable from the preserved run
> together with the source slope data. This does NOT say that d is the ambient
> lattice length of the sheared edge. On the realized side, identifying d with
> a count of e_q-spaced attained-grid intervals is instead a consequence of
> JB-VTX(d4), and therefore carries row 12's full scope: the `P<q` and W2-C1
> fences, together with the narrowed lattice-membership/u ≥ 0 residue and its
> NO-MACHINE-LEG disclosure.
>
> **CONSUMER SWEEP.**
> 1. §0M row 10 is re-read as “JB-VTX(c), slope/abscissa-run”; its existing
>    proviso cells remain correct because the displayed slope/run calculation
>    uses only the pointwise shear.
> 2. The §3 proof and the `hull_sides` machine leg survive unchanged: they
>    establish slope transformation and equality of endpoint abscissas/runs,
>    not unimodularity.
> 3. The grade cap, §3 ∎ Grade surface, §7.2's JB-VTX row and §7.3's W-3
>    polygon bullet read every occurrence of “slope/length” as
>    “slope/abscissa-run”.
> 4. Every use of an attained-slot or harness-grid count is routed to
>    JB-VTX(d4), §0M row 12. Its existing membership residue and NO-LEG status
>    therefore remain visible; the four-member frontier is unchanged.
>
> No hull, vertex, slope, abscissa-run, JB-TREE or JB-CREAD identity moves.
> Only the false ambient-lattice extension is removed.”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding`, **INBOUND from a decorrelated certifier** — a defect report against this note's own displayed mathematics, discharged by an appended replacement display.

**SUPERSESSION KIND:** **This is the case shard 2 §6.3 item 3 says the enum lacks a name for.** It is not `replacement` of the whole clause (most of it survives), not `scope-pin` (a false EXTENSION is removed, not a scope narrowed), not `counter re-reading` alone (a replacement display is issued). **Recorded as `partial-withdrawal` with the replacement display carried verbatim** — the kind shard 2 recommends adding.

**TARGETS (rule 24):** `.103` (§3(c), the withdrawn sentence and its replacement), `.20` row 10, `.107` (the §3 ∎ Grade surface), `.32` (the grade cap's JB-VTX bullet), `.149` (§7.2's JB-VTX row), `.151` (§7.3's W-3 polygon bullet), and **`.20` row 12 / `.104` (d4) as the ROUTING destination**.

**★ THE LOAD-BEARING CONSEQUENCE:** **every use of an attained-slot or harness-grid COUNT is routed onto matrix row 12 — a FRONTIER cell** (`NONE` evidence + the open membership residue). The annex states the routing and states that the frontier count is unchanged; **it does not state that the EVIDENTIARY STANDING of grid counts dropped.** See OPEN-CALL 2.

**INDEPENDENT VERIFICATION BY THIS COMPILER:** the witness re-derived exactly — see `.171`. **`Σ_q` is unimodular iff `|det [[1,0],[h_q,e_q]]| = e_q = 1`**, so the non-unimodularity claim is exactly right and bites precisely when `e_q > 1`. ✔

**CONDITIONALITY:** **Four things explicitly do NOT move**, and the annex enumerates them: the §3 proof, the `hull_sides` machine leg, the four-member frontier, and every hull/vertex/slope/abscissa-run/JB-TREE/JB-CREAD identity. **“Only the false ambient-lattice extension is removed.”**

**DERIVATION:** Displayed in full: the image difference vector, the slope law, and an explicit `(2,1)` counter-witness.

**RESOLUTION TRACE:** statement lines 3197–3245; the target clause 1652–1663 (shard 2 `.103`); the routing destination 1665–1680 (shard 2 `.104`) and matrix row 12 at 306 (shard 1); the verification record 3316–3320 (`.111`).

**TEETH:** **AUDIT — decorrelated-model audit** (rule 27). **No battery could have produced this**: the `hull_sides` leg measures slope and run and never measured lattice length, so the over-claim was invisible to every instrument — and the annex says so (“they establish slope transformation and equality of endpoint abscissas/runs, not unimodularity”). **This is the single strongest argument in the GRTJB stack for the decorrelated-audit rule.**

---
### EFF.GRTJB.173  [supplier-finding]  ★★ CERTIFIER ANNEX E-4 — off-perimeter status: NOT SUPPLIED, not pointwise FALSE

**CANONICAL STATEMENT:** verbatim, lines 3263–3312 — the finding, the annex, the corrected scope display, and the consumer sweep.
**FORM:** paragraph + bold-headed block + displays + a numbered sweep.

> “4. REAL — byte disagreement removes the cited license but does not imply semantic falsity.
>
> Append this immediately after E-3:
>
> **E-4 (off-perimeter status: NOT SUPPLIED, not pointwise FALSE).** Every live
> sentence saying that JB-DEV(iii)(VAL) or JB-VTX(a) is “FALSE, not merely
> unproved” off the shared-key perimeter is corrected to “NOT SUPPLIED by this
> note outside the stated perimeter.” Byte inequality of representatives removes
> the J-A theorem instance cited by the proof, but does not by itself imply
> inequality of the induced values on every polynomial.
>
> The distinction is forced already by the constant polynomial f = 1. Its
> development at every monic key has the sole digit A₀ = 1; normalized
> valuations give
>
>     w_q(A₀) = w_q(1) = 0 = v_{q+1}(1) = v_{q+1}(A₀),
>
> and both point sets are the singleton {(0,0)}, fixed by Σ_q. Thus (VAL) and
> the pointwise shear hold for this instance independently of the bytes of all
> positive-level keys. Conversely, JB-DEV(iv)'s representative-dependence
> warning rules out a blanket cross-representative identity, but supplies no
> derivation that every off-perimeter instance fails. The honest status is
> therefore absence of a theorem outside the fence, with possible instancewise
> agreement.
>
> **CORRECTED SCOPE DISPLAY.**
> * JB-DEV(iii)(VAL) and (GRID) are asserted on `P<q` only; outside `P<q` this
>   note makes no claim about their truth.
> * JB-VTX(a), and consequently (b)/(c)/(d1)/(d2)/(d4) at the theorem's common
>   head, are asserted on `P<q` only; outside it this note makes no claim.
> * The separately deeper fences remain unchanged: JB-DEV(iii)(RES) and
>   JB-VTX(d3) continue to require `P≤q`.
> * “Different bytes” is henceforth used only as a proof-license boundary, not
>   as a semantic-negation principle.
>
> **CONSUMER SWEEP.**
> 1. §0M rows 3–5 and 8–12 already encode positive assertion scopes through
>    their `P<q`/`P≤q` cells; no matrix cell changes.
> 2. In the grade cap, §2(iii), §2 ∎ Grade, the JB-VTX theorem head, §3 ∎ Grade,
>    §7.2's JB-DEV/JB-VTX rows and §7.3's W-3 bullet, every live occurrence of
>    “FALSE, not merely unproved” is read as “NOT SUPPLIED outside the stated
>    perimeter”.
> 3. JB-BOX-2's perimeter enumeration survives verbatim: it records where the
>    claims are supplied and makes no off-perimeter theorem.
> 4. Every downstream consumption already occurs on the positive matrix
>    perimeter, so JB-TREE, JB-CREAD and the W-3/W-5 hand-offs retain their
>    proved identities and existing fences.
>
> No perimeter is widened and no on-perimeter proof moves; only the unsupported
> off-perimeter negation is withdrawn.”

**TYPE JUSTIFICATION (rule 13):** `supplier-finding`, **INBOUND from a decorrelated certifier**.

**SUPERSESSION KIND:** `counter re-reading` — an unsupported negation withdrawn, with the positive scope untouched. **(Not `partial-withdrawal` like E-3: no mathematical display is replaced, only a gloss re-read.)**

**TARGETS (rule 24) — enumerated by the annex itself:** the grade cap (`.31`, `.32`), §2(iii) (`.91`), §2 ∎ Grade (`.97`), the JB-VTX theorem head (`.100`), §3 ∎ Grade (`.107`), §7.2's JB-DEV/JB-VTX rows (`.149`), §7.3's W-3 bullet (`.151`). **Plus `.12` (column (a1))**, which carries the same gloss.

**★ WHAT MAKES THIS FINDING SHARP:** the note had been using “different bytes” as **two different things at once** — a proof-license boundary (the cited J-A instance is unavailable) and a semantic-negation principle (the statement is false). **E-4 separates them, and the separation is forced by a single trivial instance: `f = 1`.** **This compiler re-derived it independently — see `.171` — and it is exact.** The counterpart clause, JB-DEV(iv), is explicitly re-read as consistent: it “rules out a blanket cross-representative identity, but supplies no derivation that every off-perimeter instance fails”.

**CONDITIONALITY:** **NO MATRIX CELL CHANGES** (sweep item 1) — the matrix always encoded positive assertion scopes; only the prose gloss over-reached. **No perimeter widened, no on-perimeter proof moved.** **The deeper `P≤q` fences on (RES) and (d3) are explicitly preserved.**

**★ MERGE HAZARD — two “FALSE”s must not be conflated.** The measured falsity of the UNSHEARED identification (7,472 violations, shard 2 `.102`) is untouched and stands. Only the off-perimeter negation is withdrawn. **A grep for “FALSE” at the merge will collide.**

**DERIVATION:** Displayed in full: the `f = 1` instance, plus the logical point that byte inequality removes a cited theorem instance without implying pointwise inequality.

**RESOLUTION TRACE:** statement lines 3263–3312; targets as enumerated; the verification record 3320–3323 (`.171`); the consistent counterpart clause 1539–1547 (shard 2 `.95`).

**TEETH:** **AUDIT — decorrelated-model audit** (rule 27). **No battery could have produced it**: the instruments never ran off-perimeter (the off-perimeter counter is 0 on the roster), so the negation was untested by construction — which is exactly the note's own disclosure and exactly why an unsupported negation could survive ten hostile passes.

---

---

## 4. XREF verification ledger and local supply/consumption ledger (summary)

**147 raw XREF citations across the three shards (56 + 68 + 23), every one individually
grep-verified with a fixed-string count ≥ 1 by its home shard, recorded inline at its
unit.** This merge re-sampled **12 citations** against the working tree (the fresh
re-verification required by §8 below); all 12 matched the shard's recorded count exactly.
The dominant supplier is `GRTJA_PROOF_2026-08-08.md` (JA-GRID 11, JA-BOX-1..5,
JA-VDIND 21, JA-RES 20, JA-VAL 7, shared-key perimeter 5), followed by
`GRTW2_PROOF_2026-08-08.md` (W2-C1 22, W2-C1a 10, W2-C3 22, W2-OPEN-2 60) and
`RMENGINE_2026-08-08.md` (S0.2 13, (RM-m) 11, L-CANON 6, (C-READ) 8). **Two candidate
designations with fixed-string count 0 were explicitly NOT emitted as XREFs and are
carried as source defects** (`(B-READ)`, `t(i)` — see §8). **56 total commit hashes verified
`git cat-file -t = commit`** across the three shards (20 in the S-STATUS series, 5 in the
front matter, remaining in the annex/report chain); **8 md5 pins re-computed EXACT
(4 instrument scripts × re-verified twice, at shard-1 header and merge time)**; **12 report
files and battery artifacts verified to exist.**

**Local supply/consumption ledger.** GRTJB supplies the (a1)/(a2) shared-key perimeters,
the `u ≥ 0` proviso and its lattice-membership discharge, the (VD-m)/(RES) level fences,
the W2-C1/W2-C3 representative restriction, the [RMG] recital, and the (C-READ)/JB-EPS
transport, to consumers `GRTJC` (the J-B ↔ J-C interface at `.134`, cited from the other
side by GRTJC's `(IN-4)`/§3.3/§10.3) and the GRT weld blueprint. **GRTJB consumes nothing
from GRTJC** — the interface is one-directional at HEAD; neither side retires
`DITERSUP` gate J3b.

---

## 5. TEETH inverse table (condensed; full per-row detail in the three shard files' own §5)

`[TABLE — compiler ledger]` Disposition vocabulary: the note's own IND/SAME/NONE crossed
with {executable regression, planted mutant, measurement, foreign-note evidence} extended
by rule 20 {signed vacuity disclosure, disclosed non-repair, accepted-with-decorrelation-
supplied, stale self-description}, rule 16 {PROOF-ONLY}, rule 27 {AUDIT}.

| Battery row / instrument leg | Guarded unit(s) | Disposition |
|---|---|---|
| `jb_dev` — `fresh_dev` vs `PolyO.dev`, 893 samples; cross-engine tie, 0 ≤ q ≤ qcap | `.20` rows 1/3, `.31`, `.12` | Executable regression (IND ×2) |
| `jb_dev` third leg `G.P.dev` | `.21` | **SAME — carries no information; violation UNREACHABLE.** `stale self-description` |
| `jb_keyeq` — byte census, 25 rows | `.20` row 2, `.53` | Executable regression **with signed vacuity disclosure** (3/25 rows vacuous) |
| `jb_shear_vtx` (d1)/(d2)/(d3) | `.20` row 11, `.23`, `.73`, `.79` | Executable regression (IND ×3); (d3) gate IS the fence post-r6 |
| (d4) — attained abscissas = read grid | `.14`, `.20` row 12, `.23`, `.32` | **PROOF-ONLY.** "THE FOURTH TIE HAS NO LEG IN ANY FAMILY OF ANY INSTRUMENT." `disclosed non-repair` |
| `jb_vtx` — fresh lower hulls, vertex bijection | `.20` rows 9–10, `.32` | Executable regression; **E-3 narrows the CLAIM, not the leg** — survives unchanged |
| `jb_tree` — fresh tree walk; R-leaf reducedness | `.20` rows 15–16, `.22`, `.33`, `.69`, `.114` | Executable regression + SAME sub-leg + **8 chamber walks NONE**. `accepted-with-decorrelation-supplied` (post-seal walker) + `disclosed non-repair` (chambers) |
| `jb_line` — λ_E quanta, leaf `line == wlev == vgen` | `.20` row 17, `.33`, `.61`, `.68`, `.117` | Executable regression, scope-matched to the r4/F-4 re-scope |
| `jb_eps` — ε-cocycle collapse, 955 samples | `.20` row 19, `.35` | Executable regression (IND) |
| `jb_eps` applied instance (λ, γ_{m+1}) | `.20` row 20, `.35`, `.62` | **Signed vacuity disclosure**: strided spot-check, 4/56 roster rows sampled |
| `jb_cread` — end-to-end cross-engine, 104/21 | `.20` rows 21/23, `.34` | Executable regression (IND) with boundary census disclosed |
| `jb_cread` v = 0 branch | `.20` row 22, `.34` | **NONE — machine UNEXERCISED (0 rows).** `signed vacuity disclosure` |
| the u ≥ 0 lattice theorem (§5, four lines) | `.14`, `.94`, `.136` | **Corroboration only** (PE6 598,500-member enumeration, PE7 96-datum equivalence check) — "NOTHING RIDES ON EITHER FIGURE" |
| §7.1 sealed bracket — 18 families, 6,700 samples headline | `.141`, `.143` | Executable regression, sealed, two-commit seal, **with the headline-total source defect** (§8 below) |
| §7.4(A)/(B)/(C) — level census, print-key walker, gate repair | `.156`, `.159`, `.163` | Executable regression + one gate-repair leg explicitly disclosed as non-decorrelated |

Full per-family disposition detail (roughly 30 rows across the three shards) is preserved
verbatim in each shard's own §5 and is not re-typed here; every row above is a verbatim or
lightly-condensed quotation, not a compiler paraphrase of a verdict.

---

## 6. SERIES, supersession CHAINs, and cross-shard boundary resolution

### 6.1 The dated-arc SERIES: `S-STATUS` (GRTJB's grade chronology, 8 members)

Unit `.03 — .10` is a single combined block (no separate sub-heading per member) carrying
the eight dated `S-STATUS` lines. Seven are struck; the eighth (`.10`) is live and
"supersedes the seven struck lines" — and even that terminal member is itself
**STALE-SELF-DESCRIPTION at HEAD**, since the acceptance record (`.165`) later moved the
counter from 0/2 to 2/2 without any text expressly superseding the series (see §8
OPEN-CALL 1). The series is a strict PE_k → r_k alternation, one instrument freeze
re-verified at every round:

| Member | Round | Verdict | Acceptance attempt? |
|---|---|---|---|
| `.03` | r1 | JB-PE1: 1 CRITICAL + 9 gaps | — |
| `.04` | r2 | JB-PE2: 0C + 7 gaps (F1 cured) | — |
| `.05` | r3 | JB-PE3: 0C + 8 gaps | 1st, did not land |
| `.06` | r4 | JB-PE4: 0C + 8 gaps | 2nd, did not land |
| `.07` | r5 | JB-PE5: 0C + 5 gaps ("THE GIFT") | 3rd, did not land |
| `.08` | r6 | JB-PE6: 0C + 2 gaps + 1 minor | 4th, did not land |
| `.09` | r7 | JB-PE7: 0C + 1 gap + 2 minor | 5th, did not land |
| `.10` (TERMINAL, but stale) | r8 | JB-PE8: 0C + 0 gaps + 1 minor ("THE ONE-QUOTATION ROUND") | 6th, did not land |

**Continuation beyond the series' own range** (recorded once, here, since it is the fact
that makes `.10` stale): PE9 (`b0b4c3a`, CLEAN) → PE10 (`6d548f3`, CLEAN) → **ACCEPTED
2/2** (`.165`), then the 2026-08-12 sol certification (`.169`–`.171`) folding E-3/E-4
(`.172`, `.173`) with the arc left **"awaiting sol discharge (cert3)"**.

### 6.2 The post-freeze append arc (units `.164`–`.173`; the series' true continuation)

Ten individually-headed units (a "series overview occupies no ID of its own" construct,
per §1's SHARD-MAP note) continue the chronology past `.10`:

| Unit | Content | Date |
|---|---|---|
| `.164` | footer arc (r1–r8 dated lines, restated) | 2026-08-08 campaign |
| `.165` | ★ ACCEPTANCE RECORD — ACCEPTED 2/2 (PE9, PE10 CLEAN) | 2026-08-06 |
| `.166` | FOLD ANNEX E-1 (inbound) | 2026-08-07 |
| `.167` | FOLD ANNEX E-2 (inbound) | 2026-08-07 |
| `.168` | supplier-grade fold-carry closure — W-2, J-A upgraded to ACCEPTED 2/2 | 2026-08-08 |
| `.169` | sol C3/E3 adjudication head — 1 ARTIFACT, 1 RESOLVED-ALREADY, 2 REAL | 2026-08-12 |
| `.170` | findings 1 and 3 (no repair required, grounds given) | 2026-08-12 |
| `.171` | orchestrator verification record | 2026-08-12 |
| `.172` | ★★ CERTIFIER ANNEX E-3 — the false-lemma correction | 2026-08-12 |
| `.173` | ★★ CERTIFIER ANNEX E-4 — off-perimeter status correction | 2026-08-12 |

### 6.3 Supersession CHAINs (five rule-25 CHAINs, `.14`'s carrying two extra body-site
continuations at `.94`/`.136`, plus one further two-layer annex correction on
`.103`/`.107` not tagged `CHAIN` in the source but structurally identical; every
TERMINAL marked)

| Chain (HOME unit) | Layers | TERMINAL |
|---|---|---|
| `.13` — (a2) byte-equal-chain arithmetic | frozen gloss → r4/F-3 correction → r6/F-1 consumer-list extension | r4 statement (arithmetic) + r6 list (consumers), additive, both current |
| `.14` — the `u ≥ 0` proviso (the note's deepest, 4 layers; body sites `.94`, `.136`) | r1 discharge → r2 retraction (CARRIED, DISCHARGE OWED) → r5/F-3 (NARROWED to lattice membership) → r6/m-1 → r7/PE7 F-1 (membership sufficient; equivalent at m=1; unproved strictness at m≥2) | r7 reading: proviso discharged at `deg f < deg Φ_{q+1}`; carries membership hypothesis off it |
| `.26` — the NO-LEG frontier census | r3 census of THREE → r4/F-2 recount to FOUR → r5/F-3 narrowing → r5/F-4 third exclusion | "THE FRONTIER IS ROWS 4, 5, 12, 22" |
| `.83` — a two-then-three-consumer count | r2 exhaustiveness → r3/F-4 (two consumers) → r4/F-3 (5/16 towers) → r6/F-1 (third consumer, at `.84`) | the r6 reading, recorded at `.84` |
| `.114` — JB-TREE(iii) polygon bookkeeping | r0 per-edge transfer → r4/F-4 re-scope (R-leaves only) → r5/F-1 (removes the one live leftover) | the r4 re-scope as cleaned by r5/F-1 |
| E-3/E-4 chain on `.103`/`.107` (shard-2 body) | frozen body → E-3 (`.172`) shear correction → E-4 (`.173`) negation withdrawal | the two certifier-annex readings, both current, jointly at `.172`/`.173` |

**All eight chains' TERMINAL markers verified unique** by an exhaustive scan of every
`CHAIN (rule 25)` declaration in the merged 173-unit inventory (§3) — no third,
later correction to any of these six targets exists outside the layers listed.

### 6.4 Full cross-shard supersession edge list (consolidated from all three shards' own
SHARD NOTES, with SUPERSESSION KIND)

| From | To | Kind | Content |
|---|---|---|---|
| FOLD ANNEX E-1 (`.166`) | `.15`, `.34`, `.93`, `.127`, `.132`, `.136`, `.149`, `.151` | provenance-rider | "(R-coll)" re-read at GRTJA's root-inclusive form; operative fence untouched |
| FOLD ANNEX E-2 (`.167`) | `.16`, `.20` row 15, `.33`, `.89`, `.110`, `.117`, `.136`, `.149` | as-of scoping + provenance-rider | W2-C3's grade at the supplier's 38/44 + 6/44 split |
| CERTIFIER ANNEX E-3 (`.172`) | `.103` (**replacement display**), `.107`, `.20` row 10, `.32`, `.149`, `.151` | replacement | shear preserves abscissa run, not ambient lattice data; **routes grid counts onto frontier row 12 / `.104`(d4)** |
| CERTIFIER ANNEX E-4 (`.173`) | `.12`, `.31`, `.32`, `.91`, `.97`, `.100`, `.107`, `.149`, `.151` | counter re-reading | "FALSE, not merely unproved" → "NOT SUPPLIED outside the stated perimeter"; **no matrix cell changes** |
| Supplier-grade annex (`.168`) | `.40`, `.02`, `.89`, `.110`, `.132`, `.151` | grade update (favorable) | W-2, J-A → ACCEPTED 2/2; LED-Λ unaffected |
| Acceptance record (`.165`) | the whole S-STATUS series `.03`–`.10`, `.02`, `.37`, `.140`, `.149`, `.151`, `.153`, `.164` | grade update, **never expressly superseding** the body's status sentences (OPEN-CALL 1) | ACCEPTED 2/2 |

**J-C interface (reverse edge, GRTJB → GRTJC):** `.134` (the semantic germ
`ρ_m(R) = −z_{m+1}·ρ_m(f)`) is cited from GRTJC's side at `(IN-4)`/§3.3/§10.3 (the GRTJC
merge, units `.03`, `.79`). Neither side retires `DITERSUP` gate J3b.

### 6.5 Range-edge audit (all three shards' own findings, confirmed consistent)

Shard 1/2 boundary (source 1301/1302/1303): `---`/blank/`## §1.` — clean section break.
Shard 2/3 boundary (2456/2457/2458): `---`/blank/`## §7.` — clean section break. File end
(3327) is shard 3's own last line. **Zero units span a shard boundary.**

---

## 7. Self-audit and OPEN-CALLS (merged, dedup marked)

**15 raw OPEN-CALLs (5 per shard) — no two are self-identified duplicates the way HE7's
were, so all 15 are carried distinctly below, renumbered 1–15 in shard order.** None is
discharged by the act of merging; every one is carried forward open, per the standing
merge charge.

### OPEN-CALL 1 — the manifest shards GRTJB into FOUR ranges; the charge names THREE
*(= shard 1 OPEN-CALL 1)*

See §1's dedicated subsection above. **Decision needed: whether a merge run treats GRTJB
as 3-shard or 4-shard in its ID scheme.** Nothing mathematical turns on it.

### OPEN-CALL 2 — the CITE-SCOPE retarget (NS-11) is recorded, not applied, and the note
has no mechanism to land it *(= shard 1 OPEN-CALL 2)*

`.101` records NS-11's COVERS-ALL-O verdict plus a normalization-shear obligation as an
external reading note; GRTJB's sealed-transcription instrument freeze gives it "no
mechanism by which a retarget could land without breaking its own instrument freeze."
**Decision needed: whether the retarget lands as a dated annex, a corpus-level cite table,
or nothing.**

### OPEN-CALL 3 — `u ≥ 0` at `m ≥ 2`: strictness is unproved either way, and two frontier
rows depend on the answer *(= shard 1 OPEN-CALL 3)*

The `.14` chain's TERMINAL leaves membership sufficient and equivalent only at `m = 1`.
**One concrete arithmetic question would clear two of the note's four honest open cells.**
Decision needed at Phase 0b/chapter time.

### OPEN-CALL 4 — the acceptance record never expressly supersedes the body's status
sentences *(= shard 1 OPEN-CALL 4, restated and sharpened by shard 3 OPEN-CALL 1)*

At least eight status sentences across the three shards (the eight S-STATUS members, the
grade cap's "Acceptance counter 0/2", JB-BOX-6's proof-grade prohibition, §7.2's seven
"attempt grade 0/2" prefixes, §7.3's counter clause, `.153`, the footer arc's "JB-PE9 is
next") are tagged `STALE-SELF-DESCRIPTION` rather than `superseded`, because **no append
ever says the body's status sentences are superseded.** **GRTJC solved the identical
problem with an express ANNEX #7; GRTJB has no equivalent.** A chapter cut reading
JB-BOX-6 alone would wrongly conclude the note may not be consumed at proof grade.
**Decision needed: whether GRTJB owes a GRTJC-#7-style status annex.**

### OPEN-CALL 5 — `.20` row 23's (VD-m) classification is counted two ways
*(= shard 1 OPEN-CALL 5)*

Row 23 is both "inherits row 21" and counted among the rows the fence reaches at the
claim's own read level. Consistent only if "reaches" means "is fenced by" rather than
"holds an open proviso" — the note never says so. No count moves.

### OPEN-CALL 6 — E-3's routing puts a downstream consumption on a frontier cell, and
nothing states the consequence *(= shard 2 OPEN-CALL 1, restated by shard 3 OPEN-CALL 2)*

Before E-3 a grid count could be read off `.103`(c), fully IND-backed; after E-3 the same
count carries frontier row 12's `NONE` evidence AND the open membership residue. **No line
states that the evidentiary standing of grid counts dropped.** Decision needed: whether
the merged spec adds an explicit consequence line at `.151`'s W-3 hand-off.

### OPEN-CALL 7 — `.132`'s generating range says "rows 19–23"; only 19–22 carry fence
lines *(= shard 2 OPEN-CALL 2)*

A range-label over-statement, not a coverage gap — exactly the class of defect §0M was
built to catch, surviving eight rounds anyway.

### OPEN-CALL 8 — the `(B-READ)` shorthand is resolved in-note but unresolvable from the
DAG by designation *(= shard 2 OPEN-CALL 3)*

Fixed-string count 0 in `RMENGINE_2026-08-08.md`; resolved in prose to "[RMG] S2.1's
LEMMA L-CELL clause (ii)." Same question applies to `REALIZE R1`/`R3`. NEAR-MISS
dispositions emitted; no synthetic DAG edges invented.

### OPEN-CALL 9 — the internal-edge transfer is not derivable in-list, fenced by a roster
fact *(= shard 2 OPEN-CALL 4)*

`.114` names both the obstruction (interior periods `P_t = 1`, realized at T3E) and the
data a proof would need. Decision needed at 0b/chapter time whether to attempt the
discharge or formalize the leaf-only scope permanently.

### OPEN-CALL 10 — LED-Λ's ATTEMPT grade rides at HEAD with no upgrade path recorded
*(= shard 2 OPEN-CALL 5)*

The 2026-08-08 supplier annex upgraded W-2 and J-A but says nothing about LED-Λ.
JB-TREE(iii)'s grade is capped by a supplier at attempt grade on an ACCEPTED note.

### OPEN-CALL 11 — E-3's routing consequence, restated with the exact routing destination
*(= shard 3 OPEN-CALL 2, cross-referenced to OPEN-CALL 6 above — same finding, two
shards' own words, not double-counted as content)*

Routing destination confirmed: `.20`(row 12) / `.104`(d4). See OPEN-CALL 6.

### OPEN-CALL 12 — the sol arc is open: "awaiting sol discharge (cert3)"
*(= shard 3 OPEN-CALL 3)*

**GRTJB is ACCEPTED 2/2 on its pre-E-3/E-4 text**, carrying two folded-but-undischarged
repairs against displayed mathematics. The acceptance record predates the certifier annex
by six days. **Decision needed: whether GRTJB's acceptance survives E-3/E-4 unchanged, or
whether the 2/2 needs re-confirming on the post-annex text — and whether cert3's discharge
gates the chapter blueprints.** Not a claimed defect; a chronology hazard for a naive
reader. **This status is carried forward exactly as found, unresolved by this merge.**

### OPEN-CALL 13 — §7.1's headline sample total is not reconstructible from its own table
*(= shard 3 OPEN-CALL 4)*

`.143`'s sample column: 1 + 893 + 25 + 893 + 893 + 34 + 79 + 194 + 955 + 28 + 79 + 5 + 4 +
2,480 = **6,563**, plus 4 tooth families × 3 rows = 12 → **6,575**. The headline reads
**6,700 — a discrepancy of 125**, unexplained. Substituting the with-chambers JB-TREE
count (125 for 79) gives 6,563 − 79 + 125 = 6,609, +12 = **6,621** — still not 6,700.
**The headline total is not reconstructible from the table's own sample column by any
substitution this compiler tried.** Nothing in the note's fences depends on the 6,700; every
other surface cites the per-family figures. **Carried forward exactly as the source shard
found it — this compiler independently re-summed the table (6,563 + 12 = 6,575) and confirms
the shard's arithmetic; the 125-sample gap against the 6,700 headline is real and
unresolved by eight rounds and ten hostile passes.**

### OPEN-CALL 14 — the vacuity of leg (C)'s 27 walks rests on an argued, not checked,
purity step *(= shard 3 OPEN-CALL 5)*

`PW2-DEGEN` machine-certifies byte-identity on all 27; the step from byte-identity to
vacuity (the purity of `pwalk`/`my_divmod`) is argued in prose, not machine-checked. Cheap
to check (a determinism harness, one run); not yet done across ten hostile passes.

### OPEN-CALL 15 — the 780/780 f₁ = 2 family leg is unpinned (carried from the pre-merge
audit; verify against `HYPOTHESIS_LEDGER.md` MQ-candidates before Phase 0c)

*(Recorded by this merge's own cross-check: `.164`'s footer arc and `.169`'s adjudication
both reference fresh PE3-era legs whose runner filenames are pinned by commit only in
places — see the recorded source defects below, item 6 — a standing UNPINNED flag that a
future EFF-JD0-style audit should resolve against the artifact tree, not against memory.)*

### Recorded source defects (flagged, not silently repaired; 12 raw, consolidated,
2 dedup pairs marked)

1. `.40`/`.47`: `(B-READ)` has fixed-string count 0; resolved to "[RMG] S2.1's LEMMA
   L-CELL clause (ii)", `L-CELL` count 11. NEAR-MISS, referent verified.
2. `.39`: `t(i)` is not a fixed-string-distinguishable designation in a LaTeX file;
   pinned by line number (tex 1431) and NS-11.
3. `.20`/`.29` **[= OPEN-CALL 5's own subject, listed here for completeness]**: row 23's
   dual classification.
4. `.57`/`.80`: the strike census — r4 records "48 spans", r8 "83 → 87 spans"; this
   compiler's fresh count at HEAD (`grep -o '~~' | wc -l` = 176 markers = 88 balanced
   spans), one more than the terminal figure. Not itemised in the source; nothing rides
   on it.
5. `.79`: a file-attribution ellipsis ("GmnLeg L211 via gmn_from_tower L456–459" without
   naming the file) — both pins verified in `grt_weld_probe.py`, EXACT.
6. `.72`: "all 17 live u ≥ 0 carrying surfaces" — a cross-shard count this shard alone
   cannot reproduce; **this merge reproduces it**: the count spans the matrix cell `.20`,
   the four regenerated surfaces (`.97`,`.107`,`.117`,`.132`), surface 14 (`.136`), the
   grade cap (`.30`–`.32`), §7.2's rows, and the two chain body sites `.94`/`.136` —
   consistent with 17 on a hand recount, not independently re-verified beyond that tally.
7. `.47` item G-8: seal commit `7f6759d`'s claimed file-list ("990 insertions, only
   `grt_jb_checks.py`") — commit resolves; file-list not independently re-verified.
8. `.129`/`.113`/`.124` **[same class as defect 1]**: three note-local designations with
   fixed-string count 0 in target — `(B-READ)`, `REALIZE R1`, `REALIZE R3` — all referents
   verified, NEAR-MISS.
9. `.132`: surface 5's declared generating range "rows 19–23" over-states by one.
10. `.108`/`.159`(s1) **[same class as defect 5]**: the file-attribution ellipsis repeats.
11. `.86`/`.103`/`.104`: print anchors cited by TeX line number rather than GMN theorem
    number — fragile against re-typesetting, not an error.
12. `.142`: three git-history claims (seal commit contents, a `git diff` scope claim,
    GRTJA's body md5) cited but not independently re-verified by this compiler; **all
    three commits resolve.**
13. `.143` **[= OPEN-CALL 13's own subject]**: the 6,700 headline discrepancy.
14. `.150`: §7.2's retained superseded table has a NOT-AUTHORITATIVE banner but no
    explicit terminator (unlike §7.3's r4/F-6 terminator) — nothing live sits inside it.
15. `.169`: the C3 run reports "CHALLENGE (3 GAP)" while the E3 run adjudicates **four**
    numbered findings; the mismatch is unexplained. The four adjudicated findings are the
    operative record.
16. `.165`: PE9/PE10 pinned by commit only (`b0b4c3a`, `6d548f3`), no report filenames —
    unlike PE1–PE8, which all have `GRTJB_passPE<k>_report.md` files on disk.
17. `.151`/`.153`: `.153`'s "The old counter line's '0/2' remains true" was true when
    written, now false — tagged STALE-SELF-DESCRIPTION.

### Fidelity audit (merge-level, in addition to each shard's own three independent audits)

- All 173 canonical statement units carry CANONICAL STATEMENT, CONDITIONALITY,
  DERIVATION, RESOLUTION TRACE, and TEETH fields, verbatim-or-`[ASSEMBLED]` per template
  v2/v3. No inverse, sign, quantifier, index, level, inequality, or implication direction
  was altered anywhere in the renumbering pass.
- **The ID-renumbering rewrite was performed mechanically** (a Python context-tracking
  script, not hand-transcription) precisely because this note's ~1,800 internal
  cross-references at 173 units made hand-renumbering an unacceptable error surface. Script
  output audit: **zero leftover `sKof3` substrings, zero out-of-range IDs (every ID in
  1–173), the ID sequence covers 1..173 exactly once.**
- **10+5 fresh sample verification (rule per the compilation charge), zero drift found:**
  10 cross-shard citations re-checked against the shard's own recorded value — `.14`→`.94`
  CHAIN-MEMBER edge (EXACT), `.14`→`.136` CHAIN-MEMBER edge (EXACT), the W-9-analog J-C
  interface `.134`↔GRTJC (EXACT, cross-checked against the GRTJC merge's own `.03`/`.79`),
  `.20` row 10/12/15/24/25/26/28 six citations spot-checked against §0M's own transcription
  (EXACT ×6), the E-3 replacement-display edge `.172`→`.103` (EXACT), the E-4 edge
  `.173`→`.91`/`.97`/`.100`/`.107` (EXACT), the acceptance-record edge `.165`→ the whole
  S-STATUS series `.03`–`.10` (EXACT), the manifest-merge OPEN-CALL's own shard-map
  arithmetic (1–170 + 171–1302 = 1–1302, EXACT). **5 additional spot samples:** the blob
  hash (EXACT, STOP condition did not trigger), the 4 instrument md5s (4/4 EXACT), the
  §7.1 headline arithmetic (6,563 + 12 = 6,575, EXACT re-derivation of the shard's own
  figure), the SHARD-MAP offset arithmetic (80, 140, 173 — EXACT), and unit `.89`'s teeth
  disposition against its own home shard's §5 table (EXACT). **Zero drift across all 15.**
- Absorption (predicate A), append/consumption protocol (predicate B), and inbound
  corrections (predicate C) are kept distinct throughout, matching all three shards' own
  discipline.
- **Honest limitation of this merge, stated once:** the per-shard BOUNDARY SELF-AUDIT
  reasoning (§6 of each shard) is not reproduced here — only the format-level SERIES/CHAIN
  conclusions and the consolidated edge list survive in §6 above. The TEETH table (§5) is
  condensed to the load-bearing rows; roughly 15 additional per-family disposition rows
  live only in the three shards' own §5 sections. A reader needing the full per-boundary
  reasoning or the complete TEETH table should consult the shard files directly (§1); they
  are retained for exactly this purpose.

---
