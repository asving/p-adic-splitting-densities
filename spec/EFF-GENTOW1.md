# EFF-GENTOW1 — CANONICAL EFFECTIVE SPECIFICATION v2 (full compilation)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Header

**Source note:** `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md` (975 lines / 53,913 bytes).

**HEAD blob hash:** `024d44afeec944d394b39486edb4e05334966f2b` (fresh `git hash-object` at compile time; last touched by commit `4caf0fb8`).

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a; governing template `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). IDs `EFF.GENTOW1.<nn>`, contiguous, in effective-text order.

**GENRE: TAG-SPARSE ASCII PROSE PROOF + SEALED BATTERY + FIVE-LAYER DATED APPEND STACK.** `grep -c '\tag{'` = **0**; the note is written in ASCII mathematical notation throughout (`Phi'`, `mu2`, `kappa2`, `eta`) with Unicode appearing only in the last two append blocks — a genre fact that matters for pinning (see §3.2). Three unit populations (v3 rule 19): **preregistrations** (P-1…P-9 and the five teeth, sealed at `982abe7`), **run-records** (S5's verdict and the four supplementary runs), **proof units** (S2–S4).

### FREEZE PREDICATES (v3 rule 21 — FIVE, and **all five verified**)

The note states five byte-level pins across its append stack. Every one was independently recomputed at compile time. This is the densest freeze ledger in the queue and it reproduces without exception:

`[TABLE — compiler ledger]`

| # | Predicate, as stated | Stated md5 | Stated commit / bytes | Compile-time verification |
|---:|---|---|---|---|
| F-1 | S7.4: “Body state before this round: md5 dc99fc250094a4db96c66c8aa93c3187 = the PE1 target (verdict commit 5eca905)” | `dc99fc25…3187` | `5eca905` | **`git cat-file -p 5eca905:<file> \| md5sum` = `dc99fc250094a4db96c66c8aa93c3187`** ✓ — not a prefix of HEAD (r1 inserted brackets INTO the body), and correctly stated as a whole-body pin, not a prefix pin |
| F-2 | post-PE2: “pre-append body md5 c2f4f3d1 … = commit 477b1b1, 38,204 bytes, re-verified by prefix” | `c2f4f3d1…e139` | `477b1b1` / 38,204 | **lines 1–692 hash to `c2f4f3d148b1ab94c5f9f95aa01de139`, measure 38,204 bytes; blob size at `477b1b1` = 38204** ✓ (three quantities) |
| F-3 | post-PE3: “pre-append body md5 3b204e4a … = commit 0bb7610, 40,228 bytes” | `3b204e4a…872e` | `0bb7610` / 40,228 | **lines 1–731 → `3b204e4a08f11249c3bb901a6773872e`, 40,228 bytes; blob size 40228** ✓ |
| F-4 | S3-correction: “pre-append body md5 06ee4edb … = commit 31388f4, 42,255 bytes” | `06ee4edb…6e88` | `31388f4` / 42,255 | **lines 1–767 → `06ee4edb86527692f82902a497646e88`, 42,255 bytes; blob size 42255** ✓ |
| F-5 | TOWERRAT batch: “pre-append body md5 29908cb4 … = commit 4e81a57, 46,567 bytes” | `29908cb4…89d3` | `4e81a57` / 46,567 | **lines 1–845 → `29908cb47cfc4e8a82ae8adad23889d3`, 46,567 bytes; blob size 46567** ✓ |

**Thirteen independent quantities stated, thirteen reproduced, zero discrepancies.** The practical consequence: lines 1–845 of the note are provably byte-untouched since `4e81a57`, and each earlier prefix since its own commit — so every span-pin into this note (there are none at HEAD, but T2-style pinning would work) is stable.

A sixth predicate is asserted of INSTRUMENTS, not text: S7's “Sealed machine artifacts (`gentow1_checks.py`, `gentow1_checks_output.txt`, `gentow1_pe1_fresh.py`, `gentow1_pe1_fresh_output.txt`) are BYTE-UNTOUCHED by this round.” All four exist; the two with stated md5s match (`6df4b213`, `25667bf6`).

### Effective-text rule (DERIVED)

**(i) The r1 round was applied as bracketed INSERTIONS into the body, not as an append**, and the note supplies its own diff manifest (S7.4): “Edit shape: [GT1-r1]-bracketed INSERTIONS plus this S7 — checkable as `git diff 5eca905..HEAD` on this file”. So every `[GT1-r1 …]` bracket in §S0–§S6 is already-landed text.

**(ii) The statement displays were held outside the r1 edit.** S7.4: “the statement displays of LEMMA GENTOW-1, LEMMA GENTOW-2, LEMMA GENTOW-5, and COR GENTOW-1.1 sit outside the inserted brackets (the pins fix the consumed chat_t reading; the floors, bounds, and clause texts are the composed ones).”

**(iii) After PE2/PE3 the note is frozen and every later correction is a dated append that GOVERNS a quoted display without editing it.** The post-PE3 record: “The note is FROZEN as of this record; dated appends only.” The S3 correction: “the S3 display sentence itself stays byte-frozen — this dated correction GOVERNS its reading.” The TOWERRAT batch: “the body is BYTE-FROZEN; each correction below GOVERNS the reading of its quoted display.”

**EFFECTIVE TEXT = the note as written (GT1-r1 brackets already landed), READ AS GOVERNED by the five dated append blocks in date order.** Critically, **four of the five appends supersede a DISPLAYED STATEMENT of a numbered lemma** — this note is unusual in the queue in that its post-acceptance corrections reach into lemma statements rather than only into prose. All four are tabulated below.

### Supersessions REACHING INTO the frozen lemma statements

`[TABLE]`

| Frozen display | Home | Governing append | SUPERSESSION KIND | Effective reading |
|---|---:|---|---|---|
| LEMMA GENTOW-1(b)'s free-count `Σ_{j,a,b} (N − floor)` | 165 | **R2a** (860–884) | **replacement** | `Σ_{j,a,b} max(0, N − floor(j,a,b))` — the clip; sealed form “is false whenever N < floor at some slot” |
| LEMMA GENTOW-2(iii)'s “onto by cardinality” | 331–334 | **R2b** (886–917) | **inventory completion** (the two sets and the counting lemma, previously undefined, are supplied) | ONTO via `DOM_N`/`COD_N` + equal clipped cardinality + injectivity |
| LEMMA GENTOW-5(a)'s “LIFT-STABLE **iff** < e1e2*N” | 415–416 | **R2c** (919–955) | **replacement** (the iff is refuted by the clause's own first-band sentence) | THREE BANDS: `m < e₁e₂N` stable; `m = e₁e₂N` value-exact but residue-undetermined at f₁f₂ ≥ 2; `m > e₁e₂N` unstable |
| §S3's K2-DIGIT LIFT display (fixed-base) | 310–317 | **the 2026-08-10 S3 correction** (769–845) | **replacement** | the base RE-SOLVES per flavor: `M_{r,t}(m) := n2hat(m − Δ(r,t))·x^{e₁r}·Φ′^{e₂t}`, `Δ(r,t) := e₁e₂h·r + e₂u₂·t` |
| GENTOW-2(i) proof's “constant term untouched” | 355 | **F-4** (957–968) | **wording-rider** | what is untouched is the constant term's **x-side digit**, not its coefficient |
| the S0 `chat_t` display (gauge-naive) | 48–49 | **[GT1-r1] S7.1** (in-body pin + dated annex) | **replacement** | `chat_t := lift(c_t·eta^{W(t)})`, `W(t) = floor((f2−t)·i(u2)/e1)` |

### Supersession CHAINS (v3 rule 25 — TERMINALs marked)

`[TABLE]`

| Chain | Layers | TERMINAL |
|---|---|---|
| **CHAIN-GAUGE** | GENHN-T(b)′'s gauge-naive `chat_t` (consumed as composed) → HETOW PE1 F-1 finds the seam → GENHN erratum `59c1966` corrects it at the source → **[GT1-r1] S7.1** pins the corrected display at nine sites here | **[GT1-r1] S7.1** (`.52`) |
| **CHAIN-FRAMES** | S7.1's η ≠ 1 coverage sentence (reads as five frames) → **post-PE2 m-1**: THREE distinct frames, three instruments, with a seam-diversity caveat “i(u2) = 1 … at X, Z and W alike” → **PE3 m-1 CURE**: that caveat's i(u₂) leg is FALSE at frame W (i(u₂) = 2); the honest residual axis is **W(0) ≥ 2 only** | **PE3 m-1 CURE** (`.60`) |
| **CHAIN-BOX1** | GENTOW-BOX-1 opened (μ₂ ≥ 3 graded-frame consumption) → **[GT1-r1] back-pointer**: GENTOW5 S1.5 RETIRES it as a mathematical box, residue grade-only, at GENTOW5's own 0/2 | **the back-pointer** (`.47`) — with the retirement's conditionality carried, not erased |
| **CHAIN-GRADE** | “0/2 (attempt; composed this session, no hostile arc)” → PE1 NOT CLEAN, stays 0/2 → **PE2 CLEAN, 0/2 → 1/2 and HOLDS** → **PE3 CLEAN, 1/2 → 2/2 ACCEPTED** → the TOWERRAT batch: “The 2/2 acceptance stands” | the TOWERRAT batch (`.64`) |

### SERIES declared (v3 rule 28)

**SERIES ARC** — `.02` ([GT1-r1] header record) → `.51`–`.57` (the S7 repair round) → `.58` (post-PE2, 0/2 → 1/2) → `.59` (post-PE3, 1/2 → 2/2 ACCEPTED) → `.62` (the S3 correction, post-GENTOW5-r2) → `.64` (TOWERRAT-R2a/b/c + F-4). Five dated blocks after acceptance, three of which change a displayed lemma.

**SERIES FREEZE** — the five byte-freeze pins, tabulated in §1 above and emitted as one ledger unit `.69` (fold audited in §7.2).

**SERIES TOWERRAT** — `.65` (R2a) → `.66` (R2b) → `.67` (R2c) → `.68` (F-4), one unit per numbered correction, all sharing one provenance (`.64`) and one machine leg.

### Scope split — THREE predicates (rule 7 + v3 rule 17)

**A. Mathematical absorption / supply SET.** The CHARGE fixes it exactly:

> “PROVE [GENHN-TOW-1] items
> (1) composed entry budgets (the GENHN-1 analogue at the composed key
> Phi_2, + the depth-3 node floor rider = item (6)(beta)), (2) the inner
> refine transfer (GENHN-4 one level up), (5) the composed window ledger
> (GENHN-3 at dv_2).”

Delivered: **three lemmas (GENTOW-1 with four clauses, GENTOW-2 with four clauses, GENTOW-5 with five clauses) + one corollary (GENTOW-1.1)**, per the STATUS TABLE (`.04`). Item (6)(β) is discharged INTO item (1); (6)(α) is untouched.

**B. Append / consumption PROTOCOL scope — what this note has LANDED elsewhere.** The note declares zero and it verifies:

> “**Consumption path (not executed here):** discharge of items
> (1)/(2)/(5) into GENHN_PROOF's [GENHN-TOW-1] box text is the
> orchestrator's dated consumption update after this note's own
> hostile arc; GENHN_PROOF is byte-untouched by this unit.”

Verified: `grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` = **0** (N1) — GENHN carries no reference to this note at all, while `GENHN-TOW-1` itself appears **19** times there (X01). So the box is live and its discharge is unlanded. Also `grep -cF '59c1966' GENHN_PROOF_2026-08-08.md` = **0** (N2): GENHN's own erratum is not self-identified by that commit hash inside GENHN, so the note's citation is to a COMMIT, not to a designation resolvable inside the supplier — recorded, not faulted.

**C. Inbound corrections RECEIVED — four sources, an unusually wide inbound set:**
1. **HETOW PE1 F-1** (a sibling note's CRITICAL) → the gauge seam, via GENHN's erratum → `.52`.
2. **This note's own PE1/PE2/PE3** → `.51`–`.60`.
3. **GENTOW5's r2** (a sibling's own repair, which flagged this note's S3 for the same defect) → `.62`. The provenance is explicit: “GENTOW5's r2 (PE2 F-2) corrected ITS lift display and flagged this note's S3 for the same defect”.
4. **The codex TOWERRAT ratification** (decorrelated, post-acceptance, CHALLENGE with two Codex-CRITICALs adjudicated GAP-with-repair) → `.64`–`.68`.

### Resolution rules applied

1. `[GT1-r1 …]` brackets are already-landed in-body text; the pre-erratum `chat_t` reading they replace is DEAD.
2. Where a dated append GOVERNS a frozen display, the unit carries the frozen display as CANONICAL STATEMENT (it is byte-frozen and must remain quotable) and the governing reading in CONDITIONALITY with its KIND declared — **except** where the append supplies a replacement display verbatim, in which case both are quoted and the effective one is marked.
3. **Every number in the note's tables was recomputed from the note's own displayed formulas**, not transcribed. All forty budget-table entries, all five node-floor pairs, all five mutant bases and the R2a counter-instance reproduce; see §6.3.
4. Machine figures are re-read from the committed artifacts.
5. Cross-note claims (GENTOW5's retirement, GENHN's erratum, hetowr1_supp's source lines) are grep-verified at their targets.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; `…` marks truncation. **The note's ASCII displays are reproduced in ASCII** — no transliteration to Unicode, since the source's own later appends mix the two and a merge run must be able to tell which span it is quoting. The four source tables (STATUS, families, budget tables, refine table) are emitted as tables and flagged `[TABLE]`; the budget and refine tables are fixed-width ASCII blocks inside prose, so per v3 rule 14 each is emitted TWICE — verbatim, then transcribed.

---
