# EFF-GRTW2-s1of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` (1632 lines).

**HOME range:** source lines **1–1260** inclusive, per `runs/qgen/sweep_manifest.txt` row 33 (`GRTW2|lean/notes/openmath/GRTW2_PROOF_2026-08-08.md|1|1260|s1of2`). That covers: title + Genre line + the `[r4]` S-STATUS arc block + Object/three clauses + Grade cap + Literature consumption + Machine bracket · §1 setting/indexing/junction notation · §2 the three base lemmas (W2-L0/L1/L2/L3 + TH-BASE) · §3 CLAUSE 2 (HR-REC, the conjugation and (C-coll), THEOREM W2-C2, the (ξ,w) closed form with its three remarks, the I4B boundary witness and W2-BOX-1) · §4 CLAUSE 1 (W2-C1a, THEOREM W2-C1, the unpinned-ℓ analysis) · §5 CLAUSE 3 (the transported type, W2-C3, the `[r1, F1]` honest re-scope, LEMMA W2-ID1, the converse's honest boundary, W2-OPEN-2/OPEN-2a with its four-route derivability adjudication, W2-OPEN-1, LEMMA W2-T3E) · §6 records (machine bracket, claims table, consequence display, dependency line) · §7 r1 · §8 r2 · §9 r3. Later text (§10 r4, the ACCEPTANCE RECORD, the five-annex stack, and the 2026-08-12 sol C5/E5 adjudication with its four certifier corrections — lines 1261–1632) is used ONLY to resolve material homed in this range.

**HEAD blob hash:** `ef6af0a5f8734d04d3d5d5c67135b8ec9e481fa0` (clean in the working tree; last touched by commit `8584db40`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). Temporary IDs `EFF.GRTW2.s1of2.<nn>`.

**GENRE: TAG-SPARSE PROSE PROOF with blockquoted clause displays, in-place strike-through, and DEEPLY NESTED round brackets.** `grep -c '\tag{'` = **0** over the whole note. The distinguishing feature — and the shard's dominant boundary problem — is **bracket nesting depth**: a single sentence in the Grade cap carries `[r1, F1]` inside which sits `[r2, P1]` inside which sits `[r3, PE3-P1]`, each superseding the last (`.05`). Four repair rounds were applied **in place** to a note that was then **accepted and frozen**, after which **five orchestrator annexes and four certifier corrections** were appended. Reading any displayed sentence therefore requires resolving up to four nested layers plus two out-of-range append layers.

### Governing effective-text record

**FREEZE PREDICATES (rule 21 — three, and the third is the one that matters most for this note):**

**(F1) TEXT-FREEZE at acceptance (out of range, governing).** Lines 1336–1337:

> “**THIS NOTE IS ACCEPTED at 2/2** — PE5 (ba2c47c, CLEAN; the 17-theorem
> Lean leg) and PE6 (9d8aba0, CLEAN; …)”

and the annex header at 1357: “## ANNEX (dated append; **the frozen body is not edited**)”, re-asserted by the sol append at 1456: “Everything above this heading is byte-untouched by this append.” **Before acceptance the four rounds r1–r4 were applied IN PLACE** — each round block says “NOTE-ONLY” and the S-STATUS block (`.03`) records all four.

**(F2) INSTRUMENT-FREEZE — the runner and both artifacts, byte-frozen from composition and verified at every round.** Lines 68–70:

> “The runner `grt_w2_checks.py` (sha256
> 71f8fc90f7543fd3…, PE4-verified byte-identical across working tree, 5463f2a,
> and HEAD) and both artifacts remain BYTE-FROZEN; r4 touches only this note.”

**The freeze is verified FOUR separate times by four different hostile passes** (§7–§10's Freeze paragraphs), including one recovery: r1 records “a stray working-tree drift on `grt_w2_checks_results.json` (elapsed_s only, left by a prior pass's re-run) was restored to the committed bytes before this round's edits” (1113–1116). **That is the most carefully policed instrument freeze in this sweep.**

**(F3) ACCEPTANCE-SCOPE FENCE — what the acceptance covers is enumerated, and an OPEN BOX is inside it.** Lines 1344–1350 (out of range, governing every grade claim here):

> “**WHAT IS ACCEPTED**: the
> (ξ,w) covariance closed form, HR-REC, W2-L0–L3, W2-C1 (chamber-qualified),
> W2-C2, W2-C3 at its honest grade (proved-to-first-twist 38/44 = 36
> derived + 2 instance-warranted; measured above), LEMMA W2-ID1 (forward
> direction, with the converse's counter-instance displayed), and
> **W2-OPEN-2/OPEN-2a as the note's fenced OPEN box — the weld's one open
> lemma, accepted AS A BOX, not as a theorem.**”

**This is a distinct freeze predicate from (F1)**: (F1) freezes the *bytes*; (F3) enumerates *which claims the 2/2 covers*, and it explicitly accepts an OPEN box as a box. A chapter cut that reads “ACCEPTED 2/2” without (F3)'s enumeration would over-report.

**EFFECTIVE TEXT FOR THIS SHARD = lines 1–1260 as written (r1–r4 already landed in place; struck text is refuted-but-preserved), READ AS CORRECTED by the out-of-range annexes and certifier corrections wherever they name an in-range sentence.** **Nine such corrections land inside this range** — five orchestrator annexes and four certifier corrections — each applied at its unit and listed in §7.

**Reading rule for nested brackets (compiler-declared; the note states no rule).** In `X ~~Y~~ **[rN, F: Z]** **[rM, G: W]**`, later rounds govern earlier ones and struck text is refuted. **Where a bracket itself contains a struck sub-bracket, the innermost surviving text is current.** Every unit's CONDITIONALITY states the current reading explicitly and gives the CHAIN with a TERMINAL marker (rule 25); this shard needed CHAINs of length **five** (`.05`).

### Scope split (rules 7 + 17 — three predicates)

**A. ABSORPTION / supply SET.** The three clauses of the W-2 junction (`.04`): admissible representative, unit covariance with the (ξ,w) closed form, ψ-transport through the tower. Supporting: **W2-L0/L1/L2/L3, TH-BASE, HR-REC, W2-C1a, W2-C1, W2-C2, W2-C3, W2-ID1, W2-T3E**, with three fenced boxes — **W2-BOX-1** (the scalar form off (C-coll)), **W2-OPEN-1** (the value layer), **W2-OPEN-2/OPEN-2a** (the chain level above a first twist) — and one **review-owed convention fence** (§4.3).

**B. APPEND / consumption PROTOCOL scope — what GRTW2 lands on other notes.** **Nothing, and the note says so twice in identical words**: “**accepted texts are NEVER edited by this unit**” (1100–1101, 1180–1181). It *records fold implications for the orchestrator* and leaves them owed. **Both were later EXECUTED — by the orchestrator, not by this note** (the 2026-08-08 fold-carry annex, out of range): GRTJB §0M row 15 at `5054d69`, WELDMASTER (M4) at the annex's own fold. **Zero dated consumption appends are claimed landed on any supplier or consumer by this note, and none is invented here.**

**C. INBOUND CORRECTIONS RECEIVED — six streams:**

| # | Source | Landing form | Count | In-range targets |
|---|---|---|---|---|
| 1 | W2-PE1 @ `083adff` | in-place `[r1]` | 2 GAP + 5 minor | `.05`, `.18`, `.22`, `.23`, `.24`, `.29`, `.30`, `.36`, `.37`, `.38`, `.39`, `.40` |
| 2 | W2-PE2 @ `79e796b` | in-place `[r2]` | 2 GAP + 1 minor | `.05`, `.13`, `.26`, `.30`, `.31`, `.33`, `.38`, `.40` |
| 3 | W2-PE3 @ `9bd938f` | in-place `[r3]` | 1 GAP (minor) | `.05`, `.31`, `.32`, `.33`, `.38`, `.40`, `.02` |
| 4 | W2-PE4 @ `e92cb22` | in-place `[r4]` (out of range) + riders | 1 GAP + 1 minor | `.30`, `.32`, `.33`, `.38`, `.39`, `.40` |
| 5 | Orchestrator annexes (2026-08-08 ×5) | dated appends, out of range | — | `.33` (OPEN-2a narrowed, then PROVED), `.40` |
| 6 | **sol certification C5/E5 (2026-08-12)** | dated appends, out of range | 1 CRITICAL + 3 REAL + 1 ARTIFACT | `.25` (W2-C1-CORR), `.29` (W2-C3 equivalence scope), `.33` (the key-carry index; the OPEN-2 status withdrawal), `.38` |

### Resolution rules applied

1. Lines 1–1260 supply the HOME material; r1–r4 tags are already-landed base text; struck spans are refuted-but-preserved.
2. **The out-of-range annexes/corrections never edit; they quote and rider.** Nine land in range.
3. **Three out-of-range events CHANGE a status in range and must be applied**: (i) the Σ-LAW annex + its supplier upgrade **PROVE (OPEN-2a)'s forward direction at m ≥ 2**; (ii) the E5 finding 1 **WITHDRAWS** the annex sentence that had over-read that proof as closing W2-OPEN-2; (iii) E5 finding 2 **SUPERSEDES** THEOREM W2-C1's universal reading. Each is a `license`, `replacement` or `counter re-reading` at its unit.
4. **The acceptance-scope enumeration (F3) governs every grade sentence in range**, several of which predate it and read “counter 0/2”.
5. Out-of-range statements are NOT emitted here. §10, the ACCEPTANCE RECORD, all five annexes and the four certifier corrections are homed in shard 2.
6. Every cited commit hash verified with `git cat-file -t` (22/22); every artifact verified present; truncated hashes marked **UNPINNED** (rule 23).

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; **strike-through and nested brackets are reproduced exactly**; truncations marked `…`. Every unit carries `FORM:`. The two source tables in range (§6.1's machine bracket, §6.2's claims table) are Markdown and are emitted once as `[TABLE]` with rule-22 arithmetic audits. Compiler ledgers (§3–§5) are flagged `[TABLE — compiler ledger]`.

---

## 2. Statement inventory

### EFF.GRTW2.s1of2.01  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 1.

**FORM:** display (H1 heading).

> “# GRTW2 — W-2, THE LIFT JUNCTION, in its corrected three-clause form: admissible representative + unit covariance (the (ξ,w) closed form) + ψ-transport threaded through the tower”

**CONDITIONALITY:** “in its **corrected** three-clause form” refers to the probe's falsification of W-2's byte-equality branch (`.04`). The headline is untouched by every round and every append (verified) — **the only title in this sweep that needed no rider.** Its three clauses' *grades*, however, all moved: clause 1 is superseded outside (C-coll) by W2-C1-CORR (`.25`); clause 2's scalar form is boxed off (C-coll) (`.23`); clause 3 is re-scoped proved-to-first-twist/measured-above (`.30`) and its equivalence wording is superseded (`.29`).

**DERIVATION:** Index of `.04`, `.25`, `.18`, `.29`.

**RESOLUTION TRACE:** statement line 1 · the clause grades 95–129 (`.05`) · out-of-range supersessions 1484–1531, 1568–1594.

**TEETH:** NONE (headline).

---

### EFF.GRTW2.s1of2.02  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 3–8.

**FORM:** bold-headed paragraph with an in-place strike-through.

> “**Unit:** W-2 COMPOSER (the first weld-junction composition of the Q4 campaign;
> per the corrected target of the probe verdict, ledger 874d26b). **Genre:
> PROOF NOTE at attempt grade (acceptance counter 0/2; no gate fires; ~~no
> acceptance arc opened by this note~~ **[r3, o2: r0 composition-time wording,
> superseded — the acceptance arc is OPEN; S-STATUS below]**), with
> sealed-runner machine brackets.**”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` (rule 26) on “acceptance counter 0/2”.** The `[r3, o2]` strike fixed one half (the arc IS open); the other half — the counter — is superseded by the out-of-range ACCEPTANCE RECORD: **2/2, ACCEPTED** (1336). `SUPERSESSION KIND: as-of scoping`. SERIES `GRTW2-GRADE-ARC`: member 1 = this line (0/2); member 2 = S-STATUS (`.03`, 0/2 after four rounds); members 3–6 = the four round-block Freeze paragraphs (`.41`–`.43` + §10, all 0/2); **member 7 = the ACCEPTANCE RECORD (2/2, TERMINAL, shard 2)**.
**One observation worth preserving:** the `[r3, o2]` strike is an *ungraded observation* (“o2”), not a finding — the note fixed a stale parenthetical two hostile passes had seen and not flagged.

**DERIVATION:** Status record.

**RESOLUTION TRACE:** statement 3–8 · S-STATUS 10–70 · acceptance 1334–1353 (shard 2).

PIN: ledger `874d26b` ✓ commit.

**TEETH:** NONE.

---

### EFF.GRTW2.s1of2.03  [changes-record] · SERIES: GRTW2-GRADE-ARC, member 2 of 7

**CANONICAL STATEMENT:** verbatim, lines 10–70 (the `[r4]` S-STATUS block — the note's own complete arc narrative, 61 lines).

**FORM:** bold display block, one sentence per arc step, with parenthetical evidence at each.

> “**[r4] S-STATUS (CURRENT): attempt grade, acceptance counter 0/2 (ZERO clean
> passes), FOUR hostile passes RUN and FOUR repair rounds applied. Arc:
> composed at 5463f2a → W2-PE1 (`GRTW2_passPE1_report.md`, 083adff — 0
> CRITICAL + 2 JUSTIFICATION GAPS + 5 minor, NOT CLEAN; core mathematics
> CONFIRMED by full independent re-derivation; machine leg bit-identical,
> 6,403/0, exit 0) → r1 (8d5e3fa, NOTE-ONLY: the W2-C3 HONEST RE-SCOPE —
> proved to each chamber's first ξ ≠ 1 junction, MEASURED above it — with the
> open box W2-OPEN-2 after a four-route derivability adjudication; the W2-C1a
> chamber qualifier; minors F3–F7; round block §7) → W2-PE2
> (`GRTW2_passPE2_report.md`, 79e796b — 0 CRITICAL + 2 JUSTIFICATION GAPS +
> 1 minor, NOT CLEAN; the four-route adjudication HELD at source under a
> deliberate fifth-route hunt; machine leg byte-identical; fresh leg 16/16 at
> m = 1 plus hand T3B/T3F r = 4) → r2 (ffa1e57, NOTE-ONLY: **P1** — LEMMA
> W2-ID1 displayed (§5.2), the m ≥ 2 case folded into W2-OPEN-2 as its premise
> sub-clause (OPEN-2a), the grade sentence scoped to the instance census;
> **P2** — the [r1, F6] §4.3 sign flip REVERTED to the r0 sign t ↦ t − k·u_i,
> faithful to tex 1431's literal Def-`t(i)`, the naming conflation split at
> §2.3; **P3** — W2-OPEN-2's premise pairing corrected to Φ_{q−1}; round
> block §8) → W2-PE3 (`GRTW2_passPE3_report.md`, 9bd938f — 0 CRITICAL + 1
> JUSTIFICATION GAP (minor, CONFIRMED by construction), NOT CLEAN; W2-ID1's
> statement and proof CONFIRMED sound by re-derivation; (OPEN-2a) confirmed
> exactly the m ≥ 2 step the warrant needs; the 36+2 census recomputed exact;
> the P2 revert verified faithful at source; machine leg re-run exit 0,
> 6,403/0, bit-identical mod timing; FRESH full-roster leg — own tower-field
> arithmetic vs the committed ledger modulo the support stabilizer — 22/22
> plus the I4B r = 5 boundary reproduced from scratch) → r3 (79d1d9c,
> NOTE-ONLY: **P1** — the two-sided "identification PROVED at m = 1" claims
> SCOPED to the proved direction at all four sites: LEMMA W2-ID1 proves
> recorded ξ = 1 ⟹ byte-equal at m = 1 (so NO byte-divergence strictly below
> the first recorded twist); the CONVERSE — recorded ξ ≠ 1 ⟹ byte-RED — is
> UNPROVED at every m, riding the never-pinned recorded-pair selection rule,
> and PE3's class-pin m = 1 counter-instance to it under the sealed scan's
> own enumeration-order selection (K₁ = F₄, ψ₁ = y³ + ζ, e₀ = 1: byte-equal
> junction, recorded pair (ζ, 1); roster-invisible at the g ≤ 2 builder
> limit) is RECORDED at §5.2 as the lemma's honest boundary; converse flag
> added inside W2-OPEN-2's premise; the §5.2 warrant, (OPEN-2a), and the
> 36+2 census re-checked — each consumes ONLY the proved direction; plus the
> two ungraded observations (o1 WM line drift, o2 the stale Genre
> parenthetical); round block §9) → W2-PE4 (`GRTW2_passPE4_report.md`,
> e92cb22 — 0 CRITICAL + 1 JUSTIFICATION GAP (minor) + 1 minor, NOT CLEAN;
> everything r3 set out to do verified done correctly and faithfully, edit
> site by edit site; the counter-instance re-derived TRUE from scratch by
> own field arithmetic; the W2-OPEN-2 converse flag adjudicated SUFFICIENT —
> NO finding; machine leg re-run exit 0, 6,403/0, results JSON byte-identical
> incl. elapsed_s; FRESH selection-geography leg 33,408/0 over 4,173 monic
> irreducibles × 7 fields — the r3 disclosure condition confirmed the EXACT
> characterization, W2-ID1's forward direction 29,223 grid points / 0
> violations) → r4 (this round, NOTE-ONLY: **P1** — the one-directional
> scoping COMPLETED across the species: the three same-species surfaces the
> r3 sweep missed (§6.3(d)'s carry item, the §5.2 (OPEN-2a) opening gloss,
> §6.4's [r2] record) scoped to the proved direction, one clause each, PLUS
> the sweep-completing sites found by this round's full-note grep (the §6.2
> W2-ID1-row appositive (PE4 o-d), the adjacent W2-OPEN-2-row label, the
> [r1, F1] block's roster-instance qualifier (PE4 o-b)); **P2** — the footer
> dateline extended (r3 + r4); plus o-c (the `orbit_scan` line figure
> 135–163) and o-e (the counter-instance chamber's 3-read extension
> precision); round block §10). A repair round is NOT a pass, so the
> counter stays 0/2; W2-PE5 — a fresh hostile pass on THIS post-r4 text — is
> the next acceptance attempt. The runner `grt_w2_checks.py` (sha256
> 71f8fc90f7543fd3…, PE4-verified byte-identical across working tree, 5463f2a,
> and HEAD) and both artifacts remain BYTE-FROZEN; r4 touches only this note.**”

**CONDITIONALITY:** **`STALE-SELF-DESCRIPTION` on “counter 0/2 (ZERO clean passes)” and “W2-PE5 … is the next acceptance attempt”** — PE5 and PE6 both returned CLEAN and the note is **ACCEPTED at 2/2** (1336–1339, shard 2). Everything else in the block is a faithful record and is confirmed by the four round blocks (`.41`–`.43` and §10).
**Three properties of this arc make it unusual and worth preserving:**
(i) **Every pass ran a FRESH LEG on a route the previous passes had not used** — PE2's 16/16 at m = 1 plus hand T3B/T3F; PE3's own tower-field arithmetic at full roster scope (22/22 + the I4B r = 5 boundary from scratch); PE4's exhaustive selection-geography map (33,408 checks / 4,173 monic irreducibles × 7 fields). **That is four independent instruments across four passes.**
(ii) **One finding was ADJUDICATED AWAY**: PE4 found the r3 converse flag “SUFFICIENT — NO finding”, i.e. a hostile pass declining to raise something it had standing to raise.
(iii) **The arc contains a REVERT**: r1's F6 sign fix was reverted at r2 as unfaithful to the named source, with anti-re-flip records installed in both brackets (`.13`, `.26`).

*Arithmetic audit (rule 22).* Four passes, four rounds ✓. Finding counts: PE1 `0C + 2G + 5m` = 7; PE2 `0C + 2G + 1m` = 3; PE3 `0C + 1G` = 1; PE4 `0C + 1G + 1m` = 2 ✓ — **monotonically decreasing severity and count across the arc** (7 → 3 → 1 → 2), and **zero CRITICALs at every pass** ✓. The machine leg is `6,403/0` at every re-run ✓ four times ✓, consistent with (F2).

**DERIVATION:** Arc record.

**RESOLUTION TRACE:** statement 10–70 · round blocks 1052–1117 (`.41`), 1121–1193 (`.42`), 1197–1257 (`.43`), 1261–1330 (shard 2) · acceptance 1334–1353 (shard 2).

XREF: `GRTW2_passPE1_report.md` ✓ present · `GRTW2_passPE2_report.md` ✓ · `GRTW2_passPE3_report.md` ✓ · `GRTW2_passPE4_report.md` ✓ — 4/4.
PINS: `5463f2a` ✓ `083adff` ✓ `8d5e3fa` ✓ `79e796b` ✓ `ffa1e57` ✓ `9bd938f` ✓ `79d1d9c` ✓ `e92cb22` ✓ — 8/8 commits.
**UNPINNED (rule 23):** the runner sha256 `71f8fc90f7543fd3…` is **truncated** at every one of its five occurrences in the note. The file exists; the version is not verifiable from the note.

**TEETH:** four fresh legs across four passes, plus the frozen 6,403/0 runner re-run at each. **Disposition: executable regression on four decorrelated instruments.**

---

### EFF.GRTW2.s1of2.04  [theorem]  — the Object and the three clauses

**CANONICAL STATEMENT:** verbatim, lines 72–93.

**FORM:** bold-headed paragraph + a blockquoted three-clause display.

> “**Object:** the blueprint junction **W-2** (`docs/in-progress/
> GRT_WELD_BLUEPRINT_2026-08-08.md` §3.2), restated after the probe
> (`lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md`) falsified its
> byte-equality branch: for every realized principal-read OM type chain in the
> [ILN]† S0.1 class pin,
>
> > **(CLAUSE 1, admissible representative)** the harness canonical
> > ε-corrected lift Φ_{m+1} is a GMN Def-2.12 admissible key-polynomial
> > representative at every level — of the ξ-CONJUGATE residual class under
> > the pinned (P-ell) convention, of the type itself exactly when the
> > junction character is support-trivial;
> > **(CLAUSE 2, unit covariance)** the slot ratio between the harness lift
> > and the classifier's print-convention key is a pure z-monomial character
> > ξ^j in the slot index, with the per-level (ξ, w) an explicit function of
> > the read data (closed form in §3.4);
> > **(CLAUSE 3, ψ-transport)** conjugating each deeper residual ψ through
> > the recorded (ξ, w) BEFORE the next lift makes the full tower transport:
> > on the transported chain the harness lift is a STRICT Def-2.12
> > representative at every level, no junction ever degenerates to a
> > weight/support split, and every probed value-layer statement of the
> > corpus holds verbatim on the transported classifier lifts (the probe's
> > 96 F3 violations all turn GREEN).”

**CONDITIONALITY:** **All three clauses are qualified by the Grade cap (`.05`) and two are further superseded out of range.**
(a) **Clause 1's “at every level”** is chamber-qualified at `[r1, F2]` (`.24`) and its **scalar-orbit content is SUPERSEDED outside (C-coll)** by THEOREM W2-C1-CORR (1484–1531, shard 2). `SUPERSESSION KIND: replacement`.
(b) **Clause 2's “pure z-monomial character ξ^j”** holds unconditionally at m = 1 and on (C-coll); off (C-coll) only the exact recursion is claimed (`.18`(c), `.23`).
(c) **Clause 3's “at every level”** is re-scoped to proved-to-first-twist / measured-above (`.30`), and its **“MacLane-equivalent”/“same induced valuation data” wording is SUPERSEDED** by the ledger-equivalence re-display (1568–1594, shard 2). `SUPERSESSION KIND: replacement`.
(d) **The probe's falsification is the note's origin** — “restated after the probe … falsified its byte-equality branch”. So the note exists because a predecessor claim was refuted by machine.

**DERIVATION:** The three clauses are proved (at their graded scopes) at `.25`, `.18`/`.19`, `.29`.

**RESOLUTION TRACE:** statement 72–93 · grade cap 95–129 · out-of-range supersessions 1484–1531 (clause 1), 1568–1594 (clause 3).

ARTIFACT: `lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md` — **verified present**; `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` — **verified present**.

**TEETH:** the whole machine bracket (`.37`); clause 3's headline number is “the probe's 96 F3 violations all turn GREEN”, scored at TW-F3 684/684 (`.35`).

---

### EFF.GRTW2.s1of2.05  [scope-record]  — the Grade cap

**CANONICAL STATEMENT:** verbatim, lines 95–129 (the Grade cap, with FIVE nested bracket layers).

**FORM:** bold-headed paragraph with strike-through and four levels of nested round brackets.

> “**Grade cap (read first).** Clause 2 is PROVED at attempt grade at m = 1
> junctions and, at m ≥ 2, proved-given-the-displayed-collapse-perimeter with
> the exact recursion (HR-REC) unconditional on the shared-key scope; clause 1
> is PROVED at attempt grade on the same perimeter ~~(its two polygon legs
> unconditionally)~~ **[r1, F2] (its two polygon legs at every junction whose
> below-junction chain is byte-shared with the harness chain — the HARNESS-side
> line content is level-unconditional; the GMN v_r/polygon reading carries the
> chamber qualifier of LEMMA W2-C1a as repaired)**; ~~clause 3's chain-level
> statements are PROVED at attempt grade given clauses 1–2~~ **[r1, F1]
> clause 3's chain-level statements are PROVED at attempt grade given clauses
> 1–2 UP TO AND INCLUDING the first ξ ≠ 1 junction of each transported chamber
> (38 of the roster's 44 junction-levels) and MEASURED above it (the remaining
> 6 junction-levels: TW-ADM/TW-STRICT 44/44, TW-STRICT SAME-adjacent), riding
> the displayed open bridging lemma W2-OPEN-2 (§5.2)** **[r2, P1: the proved
> scope's boundary is keyed to the first RECORDED ξ ≠ 1 junction; ~~that this
> coincides with the first BYTE-divergence is PROVED at m = 1 (LEMMA W2-ID1,
> §5.2) and at m ≥ 2 is W2-OPEN-2's own premise sub-clause (OPEN-2a)~~
> **[r3, PE3-P1: one direction only — LEMMA W2-ID1 (§5.2) proves at m = 1
> that recorded ξ = 1 ⟹ byte-equal, i.e. NO byte-divergence strictly below
> the first recorded twist, and at m ≥ 2 that same forward direction is
> W2-OPEN-2's premise sub-clause (OPEN-2a); the CONVERSE (recorded ξ ≠ 1 ⟹
> byte-RED) is UNPROVED at every m — it rides the unpinned recorded-pair
> selection rule, with PE3's off-roster m = 1 counter-instance under the
> sealed scan's own selection recorded at §5.2]** — on the
> roster the identification is instance-exact (recorded ξ ≠ 1 ⟺ byte-RED at
> 22/22 walked junctions; every below-r₀ junction byte-GREEN — PE2's
> recomputation), so the 38/44 proved-scope census is fully §3-derived except
> where an m ≥ 2 recorded-trivial junction sits below (this roster: I4A/I4B
> at r = 5), where it stands as instance evidence riding (OPEN-2a)]**, and
> its value-layer
> statement (the corpus battery
> on transported lifts) is **machine-confirmed instance evidence, displayed as
> the open lemma W2-OPEN-1** — not a proven theorem. Nothing here fires the
> BLOCKED-ON-CARRIER-TIE gate, touches any accepted text, or advances W-1's
> operator dictionary beyond the level-1 value dictionary proved below.”

**CONDITIONALITY:** **This is the shard's deepest CHAIN and it now has FIVE members, two of them out of range.**

**CHAIN for clause 3's boundary (rule 25), in source order:**
1. **r0**: “clause 3's chain-level statements are PROVED … given clauses 1–2” — **struck**.
2. **`[r1, F1]`**: proved to each chamber's first ξ ≠ 1 junction (38/44), MEASURED above (6/44), riding W2-OPEN-2.
3. **`[r2, P1]`**: the boundary is keyed to the first RECORDED twist; the coincidence with byte-divergence is W2-ID1 at m = 1 and (OPEN-2a) at m ≥ 2 — **struck**.
4. **`[r3, PE3-P1]`**: **one direction only** — W2-ID1 gives forward (recorded ξ = 1 ⟹ byte-equal); the CONVERSE is UNPROVED at every m, with a counter-instance.
5. **Out of range — the Σ-LAW supplier upgrade (annexes 2026-08-08 and #3)**: **(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at attempt grade** through an ACCEPTED supplier. So the two instance-warranted census entries (I4A/I4B r = 5) now ride a theorem, not instance evidence.
6. **Out of range — the E5 certifier correction (finding 2)**: THEOREM W2-C1's universal reading is **SUPERSEDED**, and the census is **honestly re-displayed as 37/44 theorem-derived + 1/44 individually scalar-orbit-confirmed (I4B r = 5) + 6/44 above-twist** (1527).
**TERMINAL: member 6 — the E5 re-displayed census 37 + 1 + 6.**

**So the census in this Grade cap (38/44 = 36 + 2) is SUPERSEDED TWICE**: first upward by the Σ-LAW (the 2 become derived), then re-partitioned by E5 (37 theorem-derived + 1 individually confirmed). `SUPERSESSION KIND: license` then `counter re-reading`.

*Arithmetic audit (rule 22), all three censuses recomputed and reconciled.*
- **The r2 census.** 44 junction-levels total; 38 at-or-below a first twist, 6 above ✓ `38 + 6 = 44` ✓. Of the 38: “36 (all strictly-below junctions at m ≤ 1) fully §3-derived via TH-BASE + W2-ID1, and 2 (I4A r = 5, I4B r₀ = 5) instance evidence” ✓ `36 + 2 = 38` ✓.
- **PE3's independent recount** (1205–1207): “36 fully derived = 16 r = 2 + 16 r = 3 + 4 r = 4” ✓ `16 + 16 + 4 = 36` ✓ **exact**, and the 2 instance-warranted are I4A/I4B r = 5 ✓.
- **The E5 census.** “**37/44 theorem-derived, 1/44 individually scalar-orbit-confirmed (I4B r = 5), and 6/44 above-twist**” ✓ `37 + 1 + 6 = 44` ✓. **Reconciliation with the r2 census:** the Σ-LAW upgrade moves I4A r = 5 from instance-warranted to derived (`36 + 1 = 37` ✓), and I4B r = 5 stays individually confirmed because **its scalar orbit is a boundary instance off (C-coll)** (`.23`) — a *different* reason from the (OPEN-2a) one. **The two censuses reconcile exactly, and the note never displays the reconciliation.** Recorded as a compiler finding.
- **Roster totals.** 16 towers with 44 junction-levels; §3.3(b) gives “the roster has 28 r ≥ 3 junctions, of which 6 … are marked SKIP”, and TH-BASE covers 16 r = 2 junctions ✓ `28 + 16 = 44` ✓ **the two decompositions agree.**
**Every census reproduces and the three of them reconcile.**

**Two further clauses of the cap, both load-bearing:**
(e) **“Nothing here … advances W-1's operator dictionary beyond the level-1 value dictionary proved below.”** — the charge's named item; see `.39` and OPEN-CALL 3.
(f) **“Nothing here fires the BLOCKED-ON-CARRIER-TIE gate, touches any accepted text”** — the note's own no-append fence (header §B).

**DERIVATION:** Grade declaration; each clause's grade is at its own unit.

**RESOLUTION TRACE:** statement 95–129 · censuses recomputed at 1074, 1155–1158, 1205–1207 · out-of-range supersessions 1405–1440 (Σ-LAW), 1484–1531 (E5 finding 2).

XREF: `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` — grep-verified count **8** (the W-1-adjacent open dictionary; see `.34`, `.39`).

**TEETH:** TW-ADM/TW-STRICT 44/44 (`.37`), with TW-STRICT reclassified **SAME-adjacent given TW-ADM** — i.e. the two 44/44 legs are **not independent**, and the note says so.

---

### EFF.GRTW2.s1of2.06  [fence]  — Literature consumption (the faithfulness discipline)

**CANONICAL STATEMENT:** verbatim, lines 131–147.

**FORM:** bold-headed paragraph, a list of tex-anchored print objects.

> “**Literature consumption (faithfulness discipline).** The classifier side is
> consumed as LITERATURE from the GMN print `docs/references/HigherNewton.tex`
> ("Newton polygons of higher order in algebraic number theory"): Proposition
> `construct` (tex 1166–1258, hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})),
> Theorem `phir` (tex 1257–1283, with eq. `vrphir`), the representative
> Definition (tex 1285 — the project's "Thm 2.11/Def 2.12" cite per
> `docs/GMN_citations.md`), Definition `t(i)` (tex 1431), Definition
> `rescoeff` (tex 1447), Definition `defresidual` (tex 1497), Proposition
> `propertiesv` items 3/4 (tex 1028), and the Bézout convention ℓ_r h_r −
> ℓ′_r e_r = 1 with **no pinned representative** (tex ~1291). Every print
> formula used below is quoted with its tex anchor; the machine transcription
> of these formulas is the SEALED probe leg (`grt_weld_probe.GmnLeg`,
> commit 55f7416), imported verbatim by this unit's runner — this note adds
> NO new print transcription. Where the print's convention is genuinely
> underdetermined (the unpinned-ℓ orbit), this is said explicitly and
> parametrized (§4.3); the ℓ-orbit reading of Def 2.12 remains a convention
> analysis, review-owed (probe fence inherited).”

**CONDITIONALITY:** **A closed consumption list with tex anchors, and the closure is load-bearing three times:**
(i) **“this note adds NO new print transcription”** — the transcription risk sits entirely in the sealed probe leg at `55f7416` ✓ commit verified.
(ii) **The list is used as a FENCE in the derivability adjudication** (`.34` route 4): “no independence proposition is among this note's consumed anchors”, and W2-OPEN-2's alternative discharge route is explicitly “a NEW consumption under the faithfulness discipline, with its own transcription and audit”.
(iii) **The r1→r2 sign revert turned on reading two of these anchors at source** (`.13`, `.26`): tex 1431 (`Def-t(i)`) vs tex 1201 (`Prop-construct`'s child twist). **The faithfulness discipline is what let PE2 adjudicate the revert** — the anchors were specific enough to check.
**The `no pinned representative` clause (tex ~1291) is the origin of §4.3's review-owed fence** (`.26`).

**DERIVATION:** Declaration.

**RESOLUTION TRACE:** statement 131–147 · the anchors used at 223–231, 233–245, 254–284, 320–336, 507–526, 528–573 · the fence's use 849–877 (`.34`).

ARTIFACT: `docs/references/HigherNewton.tex` — **verified present**; `docs/GMN_citations.md` — **verified present**.
PIN: `55f7416` ✓ commit · `a6f7653` ✓ commit (the GmnLeg line, cited at `.40`).

**TEETH:** NONE (declaration). Its discipline is what makes `.13`/`.26`'s revert auditable.

---

### EFF.GRTW2.s1of2.07  [instrument-record]  — the machine bracket header

**CANONICAL STATEMENT:** verbatim, lines 149–156.

**FORM:** bold-headed paragraph.

> “**Machine bracket:** `verification/openmath/grt_w2_checks.py` (this unit;
> outputs `grt_w2_checks_output.txt`, `grt_w2_checks_results.json`; 6,403
> samples, 0 violations, 17 check families all GREEN, teeth caught) layered
> on the sealed probe artifacts (`grt_weld_probe*`; 1,391 samples). Roster:
> the probe's 16 towers (ℤ₂/ℤ₃/F₂[[t]]/F₃[[t]], 2–4 reads, wild p | e_j rows,
> d₀ = 2 rows, g ≥ 2 rows, flat rows, I4A/I4B/I4C verbatim) + the 5 concrete
> quartic/cubic shapes with fresh extraction; PARI `factorpadic`/
> `idealprimedec` external anchors.”

**CONDITIONALITY:** **The roster's `g ≥ 2 rows` clause is the coverage limit that makes PE3's counter-instance roster-invisible** — the Tower builder implements only `g ∈ {1,2}` (`.32`), and the counter-instance needs `g_m ≥ 3`. **So the roster's own construction is why the converse looked true on it.** That is a `signed vacuity disclosure` of the sharpest kind and the note makes it at `.32`.
**`F_p[[t]]` rows have no PARI leg** — a displayed deferral inherited from the probe (`.40`).

**DERIVATION:** Instrument description.

**RESOLUTION TRACE:** statement 149–156 · the family table 942–957 (`.37`) · the roster limit 766–772 (`.32`) · the PARI deferral 1024–1027 (`.40`).

ARTIFACT: `verification/openmath/grt_w2_checks.py` ✓ · `grt_w2_checks_output.txt` ✓ · `grt_w2_checks_results.json` ✓ — 3/3 present.

**TEETH:** the 17 families at `.37`.

---

### EFF.GRTW2.s1of2.08  [hypothesis]  — §1.1, the two legs

**CANONICAL STATEMENT:** verbatim, lines 164–181.

**FORM:** section body with an indented ASCII lift display.

> “Harness: the [ILN]† S0.1 class pin verbatim (`ITERLAWN_PROOF_2026-08-08.md`
> S0.1–S0.2): DVR O, uniformizer π, reads (e_j, h_j, g_j), j = 0..n, with
> e_j, h_j, g_j ≥ 1, gcd(e_j, h_j) = 1; normalized Bézout pairs ℓ_j h_j +
> ℓ_j′ e_j = 1 with 0 ≤ ℓ_j < e_j (so ℓ_j = 0 ⟺ e_j = 1); residue chain
> K_{j+1} = K_j[z_{j+1}]/(ψ_j), ψ_j monic irreducible with ψ_j(0) ≠ 0;
> weights γ₁ = h₀, γ_{j+1} = e_j·w_jΦ_j + h_j, w_jΦ_j = e_{j−1}g_{j−1}γ_j;
> the standard lift Φ₁ and the canonical ε-corrected lifts
>
>     Φ_{m+1} = Σ_{k ≤ g_m, ψ_{m,k} ≠ 0} C_k·Φ_m^{e_m k},   C_{g_m} = 1,
>     C_k := realize_m( ε_m(β_k)^{−1}·ψ_{m,k},  β_k ),   β_k := (g_m−k)γ_{m+1},
>
> with ε_m(β) := z_m^{ℓ′_{m−1}s − ℓ_{m−1}u}, (s,u) := eq12(β; e_{m−1},
> h_{m−1}), ε₀ := 1; harness reads R_m v and weights w_m per S0.2 (level-m
> read of f at weight λ: dev by Φ_{m−1}, grid s(λ) + je_{m−1}, packed
> C_j = ε_{m−1}(β_digit)·R_{m−1}v(A) into Σ_j C_j z_m^j).
>
> Classifier: the GMN print objects above, transcribed fresh in the sealed
> probe leg.”

**CONDITIONALITY:** Inherited hypothesis set, consumed **verbatim** from an accepted package ([ILN]† S0.1–S0.2). Unconditional as a hypothesis. **Two clauses are load-bearing everywhere below:** `ψ_j(0) ≠ 0` (used at `.24`'s initial-slot attainment and at `.31`'s j = 0 evaluation) and `ℓ_j = 0 ⟺ e_j = 1` (which makes `A_m = 0 ⟺ e_{m−1} = 1`, `.19`, and drives the T3E carry-inertness at `.36`).

**DERIVATION:** Hypothesis.

*Arithmetic audit (rule 22).* `ℓ_j h_j + ℓ_j′ e_j = 1` with `0 ≤ ℓ_j < e_j`: at `e_j = 1` the only choice is `ℓ_j = 0` ✓ and then `ℓ_j′ = 1` ✓ — **so `ℓ_j = 0 ⟺ e_j = 1`** ✓ (the ⟸ is immediate; the ⟹ holds because `ℓ_j = 0` forces `ℓ_j′e_j = 1` hence `e_j = 1` ✓). Consequently `A_m := ℓ_{m−1}g_{m−1}γ_m = 0 ⟺ e_{m−1} = 1` ✓ **matching `.19`'s display** ✓.

**RESOLUTION TRACE:** statement 164–181 · untouched by every round and append (verified).

ARTIFACT: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` — **verified present**.

**TEETH:** NONE (hypothesis).

---

### EFF.GRTW2.s1of2.09  [definition]  — §1.2, the P-index dictionary

**CANONICAL STATEMENT:** verbatim, lines 185–194.

**FORM:** section body, a run-on identification list.

> “GMN level i = harness read i−1 throughout: (e_i, h_i, f_i)^GMN =
> (e_{i−1}, h_{i−1}, g_{i−1})^har; ψ_i^GMN = ψ_{i−1}^har; F_i = K_{i−1};
> z_i^GMN = z_i^har (both the class of y in F_{i+1} = K_i); ℓ_i^GMN ≡
> ℓ_{i−1}^har (same normalized representative under (P-ell)); GMN keys
> φ_i = harness Φ_{i−1}; valuations v_i^GMN = harness w_{i−1} (same
> recursion, `propertiesv` item 3 vs the S0.2 weight recursion; in
> particular v_i(φ_i) = w_{i−1}Φ_{i−1} and v_{i+1}(φ_i) = γ_i^har);
> residual operators: GMN order-q residual R_q (dev by φ_q = Φ_{q−1})
> pairs with the harness level-q read R_q v. Pins (P-ell)/(P-lift)/
> (P-root)/(P-index) as sealed in the probe docstring.”

**CONDITIONALITY:** **The identification `φ_i^GMN = Φ_{i−1}^har` is the single most consequential line of §1**, and **getting it wrong twice caused two separate findings**: PE2's P3 (W2-OPEN-2's premise paired `φ_q^tw` with `Φ_q`; fixed to `Φ_{q−1}`, `.33`) and, four months of rounds later, **E5's finding 3** — “The prior P3 correction fixed the premise but **missed this later occurrence**” in the Equivalent sufficient form (1533–1560, shard 2). `SUPERSESSION KIND: replacement` at both sites. **Two independent misindexings of the same dictionary, one caught at r2 and one at the 2026-08-12 certification.**

**DERIVATION:** Definition (an index translation).

*Arithmetic audit (rule 22) of the degree argument E5 uses.* If one paired `φ_q` with `Φ_q`, then `deg Φ_q = e_{q−1}g_{q−1}·deg Φ_{q−1}` (from `.08`'s lift display: the top term is `Φ_m^{e_m g_m}`) ✓, while `deg φ_q = deg Φ_{q−1}` ✓ under the correct dictionary. So `deg Φ_q > deg φ_q` whenever `e_{q−1}g_{q−1} > 1` ✓, and `deg D_q < deg φ_q` would be impossible ✓ **exactly E5's argument** ✓ — and this compiler's recomputation confirms it. Under the correct pairing `Φ_{q−1} = φ_q + D_q`, both summands are monic of the same degree ✓ so `deg D_q < deg φ_q` is possible ✓.

**RESOLUTION TRACE:** statement 185–194 · the two misindexings 787 (fixed at r2, `.33`) and 841 (fixed at E5, shard 2).

**TEETH:** the P-index tie is exercised at every machine family; **CK-MM's 4,396 samples** are its sharpest test (`.13`).

---

### EFF.GRTW2.s1of2.10  [definition]  — §1.3, the junction notation and the shared-key perimeter

**CANONICAL STATEMENT:** verbatim, lines 198–215.

**FORM:** bold-headed section body with two indented ASCII displays.

> “**The junction at level m+1** (1 ≤ m ≤ n; GMN r := m+2) compares the
> harness lift Φ_{m+1} with the print key φ_r built by Prop-`construct` +
> Thm-`phir` on the same type data. Both are
>
>     (key)^{e_m g_m} + (slot coefficients)·(key)^{e_m·j},  j < g_m,
>
> key = Φ_m = φ_{r−1}, slot j carrying weight β_j = (g_m−j)γ_{m+1}
> (harness) = the T-side ordinate data u_j = g_m γ_{m+1} − j·h_m, V_j =
> u_j − j e_m·w_mΦ_m (print; V_j = β_j — same integers, §2.1). The slot
> coefficients live at harness level m, values in K_m. A junction is
> **shared-key** if Φ_q^har = φ_{q+1}^cls byte-for-byte for all q ≤ m (the
> first-divergence perimeter). The three read-data quantities of the note:
>
>     A_m := ℓ_{m−1}·g_{m−1}·γ_m ∈ ℤ_{≥0}      (A_m = 0 ⟺ e_{m−1} = 1),
>     c₁ = z_m^{−A_m}   [THE Thm-phir constant: the print's
>          c₁ = (z_{r−2})^{−ℓ_{r−2}v_{r−1}(φ_{r−1})/e_{r−2}}, tex 1270,
>          since v_{r−1}(φ_{r−1}) = w_mΦ_m = e_{m−1}g_{m−1}γ_m],
>     c  = c₁^{e_m g_m}  [Thm-phir's residual scalar: R_{r−1}(φ_r) = c·ψ_{r−1}].”

**CONDITIONALITY:** **“shared-key” is the note's central scope predicate** — §3 is entirely inside it (`.15`), clause 1 is proved on it (`.25`), and the whole W2-OPEN-2 box exists because transported chambers leave it above `r₀` (`.30`, `.33`). **Unconditional as a definition**, and untouched by every round and append.
**Note the shared-key definition's own indexing**: “Φ_q^har = φ_{q+1}^cls” — which is `.09`'s dictionary written the other way (`φ_{q+1} = Φ_q`) ✓ consistent ✓. **This occurrence is correct**; the two that were wrong are at `.33`.

**DERIVATION:** Definition; the `V_j = β_j` identity is proved at `.11` (W2-L0).

*Arithmetic audit (rule 22).* `c₁ = z_m^{−A_m}` from the print's `c₁ = z_{r−2}^{−ℓ_{r−2}v_{r−1}(φ_{r−1})/e_{r−2}}`: with `r − 2 = m`, `ℓ_{r−2} = ℓ_{m−1}` (by `.09`'s `ℓ_i^GMN ≡ ℓ_{i−1}^har`) — **careful**: the note writes `z_{r−2}` and identifies it with `z_m`, and `z_i^GMN = z_i^har` ✓ so `z_{r−2} = z_m` ✓. Exponent: `ℓ_{m−1}·v_{r−1}(φ_{r−1})/e_{m−1}` with `v_{r−1}(φ_{r−1}) = w_mΦ_m = e_{m−1}g_{m−1}γ_m` ✓ gives `ℓ_{m−1}·e_{m−1}g_{m−1}γ_m/e_{m−1} = ℓ_{m−1}g_{m−1}γ_m = A_m` ✓ **exactly** ✓. And `c = c₁^{e_mg_m} = z_m^{−A_m e_m g_m}` ✓ — **which is what `.18`(a) and `.22` consume** ✓.

**RESOLUTION TRACE:** statement 198–215 · `V_j = β_j` proved 223–231 (`.11`) · consumed at 361–392, 394–411, 430–442.

**TEETH:** **CK-SLOT / CK-BYTE** ride these definitions; the `shared-key` predicate is what marks 6 junctions SKIP (`.15`).

---

### EFF.GRTW2.s1of2.11  [lemma]  — LEMMA W2-L0 (grid/weight tie)

**CANONICAL STATEMENT:** verbatim, lines 221–231 (statement, proof and consequence — the note gives this lemma no blockquote).

**FORM:** `###`-headed section body (bold-headed lemma name in the heading, statement and proof in running prose).

> “The print's T-side initial abscissa (tex 1176: "the greatest side T
> contained in L whose end points have nonnegative integer coordinates";
> initial point (s,u)) equals the eq12 offset: s = ℓV mod e, u = (V − sh)/e.
> *Proof.* An abscissa x on L of slope −h/e and value V has integer ordinate
> iff xh ≡ V (mod e) iff x ≡ ℓV (mod e); the smallest nonnegative such x is
> ℓV mod e. ∎ Consequently the print's slot grid s + je and slot values V_j
> coincide with the harness grid and digit weights: V_j = u_j − (s+je_m)w_mΦ_m
> = (V − (s+je_m)γ_{m+1})/e_m = β-digit weight (expand γ_{m+1} = e_m w_mΦ_m +
> h_m). The two legs' polygons agree point-for-point at every junction slot.”

**CONDITIONALITY:** **Unconditional, and “used silently everywhere”** (the section title says so). Untouched by every round and append (verified). It is what licenses the `V_j = β_j` identification at `.10` and the “on-grid and on-line” hypothesis of HR-REC (`.16`).

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* `xh ≡ V (mod e)` ⟺ `x ≡ ℓV (mod e)` requires `ℓh ≡ 1 (mod e)` ✓ — which is the Bézout relation `ℓh + ℓ′e = 1` ✓ from `.08` ✓. The smallest nonnegative solution is `ℓV mod e` ✓ **by definition of the mod-reduction** ✓. Integrality of `u = (V − sh)/e`: `V − sh ≡ V − ℓVh ≡ V(1 − ℓh) ≡ V·ℓ′e ≡ 0 (mod e)` ✓ **exact** ✓. **The lemma is correct.**

**RESOLUTION TRACE:** statement 221–231 · consumed at 206–209 (`.10`), 326–327 (`.16`), 496–503 (`.24`).

**TEETH:** Indirect — every family rides the grid tie; **CK-MM** (4,396) is the sharpest since it tests the integer identity that makes the two grids coincide.

---

### EFF.GRTW2.s1of2.12  [lemma]  — LEMMA W2-L1 (the base builder) and COROLLARY TH-BASE

**CANONICAL STATEMENT:** verbatim, lines 235–252.

**FORM:** `###`-headed section body with an indented ASCII display, a proof, and a bold-headed corollary.

> “Let V ≥ e₁f₁v₂(φ₁) (GMN indexing; the print's own hypothesis) and
> φ(y) = Σ_{j<f₁} c_j y^j over F₁ = K₀. The print's order-2 construction
> (tex 1183–1190) P = Σ_j π^{u−jh₁}c_j(x)φ₁^{s+je₁} satisfies, in HARNESS
> semantics,
>
>     w₁(P) = V   and   R₁v(P) = φ(z₁) = Σ_j c_j z₁^j.
>
> *Proof.* The Φ₀-development of P is exactly the placed digits (deg c_j(x)
> < d₀). Digit at abscissa s+je₀ has level-0 weight u_j = u − jh₀, on the
> line by W2-L0. The level-1 read packs C_j = ε₀·R₀v(π^{u_j}c_j(x)) = c_j
> (ε₀ = 1; res at exact weight recovers the digit), so R₁v(P) = Σ c_j z₁^j. ∎
>
> **Corollary TH-BASE (r = 2 junctions byte-equal).** At the base junction
> both recipes place the same digits: harness C_k = realize₀(ψ_{0,k},
> (g₀−k)γ₁) = π^{(g₀−k)h₀}·lift(ψ_{0,k}); print slots π^{u_j}c_j(x)φ₁^{je₁}
> with c₁ = 1 (tex 1270, r = 2 case), u_j = (g₀−j)h₀, same digit lifts under
> (P-lift). Φ₁^har = φ₂^cls byte-for-byte. [Machine: probe F0 21/21; runner
> CK-SLOT r = 2 rows 16/16.]”

**CONDITIONALITY:** **TH-BASE is the base case of every ascending argument in the note** — it is why the 16 r = 2 junctions are byte-equal unconditionally, and it is one of the two ingredients (with W2-ID1) of the “36 fully derived” census entry (`.05`). Untouched by every round and append.
`ε₀ = 1` (from `.08`) is what makes the base collapse; **at r = 2 the whole covariance is trivial** (`c₁ = 1` at r = 2, tex 1270).

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* At `r = 2` the Thm-`phir` constant is `c₁ = z_0^{−ℓ_0 v_1(φ_1)/e_0}`… the note says “c₁ = 1 (tex 1270, r = 2 case)” ✓ — consistent with `.10`'s formula at `m = 0`: `A_0 = ℓ_{−1}g_{−1}γ_0` is not defined, and the base has no lower level, so `c₁ = 1` ✓ by convention matching `ε₀ := 1` ✓. Digit match: harness `C_k = π^{(g₀−k)h₀}·lift(ψ_{0,k})` vs print `π^{u_j}c_j(x)` with `u_j = (g₀−j)h₀` ✓ **same π-exponent** ✓ and same lift under (P-lift) ✓ ⟹ byte-equal ✓. Machine: 21/21 + 16/16 ✓, and **16 = the number of r = 2 junctions** (one per tower, 16 towers) ✓ **matching `.05`'s census decomposition `16 r = 2`** ✓.

**RESOLUTION TRACE:** statement 235–252 · consumed at 686–687, 725–726, 1155–1157, 1205–1207.

**TEETH:** **probe F0 21/21 + CK-SLOT r = 2 rows 16/16.** Disposition: executable regression, exhaustive on the base junctions, with a foreign (probe) leg agreeing.

---

### EFF.GRTW2.s1of2.13  [lemma]  — LEMMA W2-L2 (the Bézout bridge) with its `[r2, P2]` naming split

**CANONICAL STATEMENT:** verbatim, lines 256–284.

**FORM:** `###`-headed section body with a long struck-and-replaced naming parenthetical, an indented ASCII identity, a proof, and a reconciliation paragraph.

> “Fix a read (e, h) with normalized Bézout (ℓ, ℓ′), ℓh + ℓ′e = 1. Let V, u
> ∈ ℤ with u − V = kW for some k ∈ ℤ and W ∈ eℤ ∩ (the key weight, W = e·g·γ
> in every use). Put 𝔰 := ℓV mod e, u′ := (V − 𝔰h)/e, and T := (ℓu − 𝔰)/e
> ~~(the print's Def-`t(i)`/Prop-`construct` twist exponent at ordinate u)~~
> **[r2, P2] (the print's Prop-`construct` CHILD twist exponent at ordinate
> u — tex 1201, y^{(ℓ_{r−2}u_j − 𝔰_j)/e_{r−2}}, 𝔰_j the ideal on-line
> initial abscissa. NOT the print's Def-`t(i)`: tex 1431 arranges
> t_{r−1}(a)_i = (s_{r−1}(a) − ℓ_{r−1}·v_r(aφ_r^i))/e_{r−1} — the
> (s − ℓu)/e order, the near-negative of T. The r0 parenthetical conflated
> these two opposite-signed exponents under one name; PE1's F6 computed with
> the conflated alias and the r1 §4.3 sign flip implemented that finding —
> both reverted/split this round, see §4.3 [r2, P2]. The identity below and
> every use of it are about T itself and are machine-keyed (CK-MM 4,396);
> only this naming line was off.)**
> Then
>
>     T + (ℓ′𝔰 − ℓu′)  =  ℓ(u − V)/e  =  (ℓW/e)·k.
>
> *Proof.* ℓ′𝔰 − ℓu′ = ℓ′𝔰 − ℓ(V − 𝔰h)/e = 𝔰(eℓ′ + ℓh)/e − ℓV/e =
> (𝔰 − ℓV)/e. Add T = (ℓu − 𝔰)/e. ∎
>
> In the junction use W = w_mΦ_m, e = e_{m−1}, ℓ = ℓ_{m−1}: ℓW/e = A_m, so
> **ε_m(V)·z_m^{T} = z_m^{A_m·k}** as field elements — the print's total
> per-node twist and the harness ε-correction differ by the pure character
> z_m^{A_m·k} in the key exponent k. [Machine: CK-MM, 4,396 integer + element
> samples, 0 violations.] Reconciliation with the probe's T2A hand account:
> there the harness ε-exponent ℓu − ℓ′s = 4 and the print total twist
> ⌊ℓγ₂/e⌋ − ℓf₁h₁e₂ = 0 differ by A₁e₁g₁ = 4, ratio z₁^{−4} = z₁² — the
> k = e₁g₁ = top-slot instance of this identity.”

**CONDITIONALITY:** **The mathematics was never wrong; only a NAME was.** The `[r2, P2]` bracket says so explicitly: “The identity below and every use of it are about T itself and are machine-keyed (CK-MM 4,396); **only this naming line was off**.” **But the naming error propagated into a real sign flip** — PE1's F6 computed with the conflated alias, r1 implemented it, PE2 reverted it (`.26`). `SUPERSESSION KIND: replacement` (the naming parenthetical), with **anti-re-flip records installed in both brackets** so a future round cannot re-flip.
**This is the sweep's cleanest example of a citation defect causing a mathematical one**, and of the corpus catching and reverting it.

**DERIVATION:** Quoted inline; three lines of Bézout algebra.

*Arithmetic audit (rule 22), recomputed.*
- **The identity.** `ℓ′𝔰 − ℓu′ = ℓ′𝔰 − ℓ(V − 𝔰h)/e`. Common denominator `e`: `= (eℓ′𝔰 − ℓV + ℓ𝔰h)/e = (𝔰(eℓ′ + ℓh) − ℓV)/e = (𝔰 − ℓV)/e` ✓ using `ℓh + ℓ′e = 1` ✓ **exactly the displayed step.** Adding `T = (ℓu − 𝔰)/e`: `(ℓu − 𝔰 + 𝔰 − ℓV)/e = ℓ(u − V)/e` ✓ `= ℓkW/e` ✓ **exact.**
- **The junction specialization.** `ℓW/e = ℓ_{m−1}·w_mΦ_m/e_{m−1}` and `w_mΦ_m = e_{m−1}g_{m−1}γ_m` (from `.08`) ✓ gives `ℓ_{m−1}g_{m−1}γ_m = A_m` ✓ **exact** ✓.
- **The T2A reconciliation.** “harness ε-exponent ℓu − ℓ′s = 4 and the print total twist … = 0 differ by A₁e₁g₁ = 4, ratio z₁^{−4} = z₁²” — so `z₁` has order dividing… `z₁^{−4} = z₁²` ⟹ `z₁^6 = 1` ✓ consistent with a residue field of order dividing 7 or with `z₁` of order 6 or 3 or 2; the note gives no field, so no independent check. **Recorded as consistent-but-unverifiable.** The `k = e₁g₁` top-slot identification ✓ matches `.18`(a)'s `k_j = je₁` at `j = g₁` ✓.
**The identity and its specialization reproduce exactly.**

**RESOLUTION TRACE:** statement 256–284 · the naming split's twin 528–573 (`.26`) · consumed at 328–336, 368–372, 296–298.

XREF: `docs/references/HigherNewton.tex` — ✓ present (anchors tex 1201, tex 1431).

**TEETH:** **CK-MM — 4,396 integer + element samples, 0 violations**, the largest family in the bracket. **Disposition: executable regression, and it is what makes the “only the naming was off” claim checkable** — the identity was machine-verified throughout the sign confusion.

---

### EFF.GRTW2.s1of2.14  [lemma]  — LEMMA W2-L3 (VD-1, the level-1 packed dictionary)

**CANONICAL STATEMENT:** verbatim, lines 288–304.

**FORM:** `###`-headed section body with an indented ASCII identity, a proof, and a closing structural paragraph.

> “For nonzero A ∈ O[x], deg A < deg Φ₁, on-line at β := w₁(A), let s₁(A) be
> the initial attained abscissa of its level-1 polygon and τ₁(A) :=
> (s₁(A) − ℓ₀β)/e₀. Then
>
>     z₁^{τ₁(A)} · R₁(A)(z₁)  =  ε₁(β) · R₁v(A),
>
> R₁ the print's order-1 residual (order-one `rescoeff`, c_i = red(a_i/π^{u_i})).
> *Proof.* Write s₁(A) = s + νe₀ (ν the first attained grid slot). The print
> coefficients equal the harness digit reads (both are res at exact weight),
> so R₁v(A) = z₁^ν·R₁(A)(z₁). And τ₁(A) − ν = (s − ℓ₀β)/e₀ = ℓ′₀s − ℓ₀u =
> the ε₁-exponent (the 𝔰 = s, k = 0 case of W2-L2's computation). ∎
> [Machine: CK-VD1, 156 samples, 0 violations.]
>
> This is the structural reason the harness ε-kit exists: **the ε-correction
> is exactly the print's t(i)-twist rewritten in eq12-canonical coordinates.**
> At levels ≥ 2 the dictionary is NOT a scalar gauge — it is a conjugation
> (§3.2) — and that conjugation is the entire content of the W-2 covariance.”

**CONDITIONALITY:** **This is the one thing the note delivers to W-1 IN PROVED FORM** — §6.3 says so: “W2-L3 is the level-1 value dictionary IN PROVED FORM (ε = the print twist in canonical coordinates)” (`.39`). **And its closing sentence is the note's own statement of why W-1 is not advanced further**: “At levels ≥ 2 the dictionary is NOT a scalar gauge — it is a conjugation”. See `.39` and OPEN-CALL 3.
**Out of range, W2-L3 is generalized**: the Σ-LAW annex (1416–1418, shard 2) says “the attained-start τ-normalization is W2-L3's mechanism at every level”, and OPEN2ATTACK's surviving open step was “the Σ-LAW at proof grade — **the level-m generalization of LEMMA W2-L3**” (1390–1391) — **since PROVED** as THEOREM SL-1 with an accepted supplier. `SUPERSESSION KIND: license` (the level-m generalization exists and is accepted).

**DERIVATION:** Quoted inline; the key step is `τ₁(A) − ν = (s − ℓ₀β)/e₀`, the `𝔰 = s, k = 0` case of W2-L2.

*Arithmetic audit (rule 22).* `s₁(A) = s + νe₀` ⟹ `τ₁(A) = (s + νe₀ − ℓ₀β)/e₀ = ν + (s − ℓ₀β)/e₀` ✓ so `τ₁(A) − ν = (s − ℓ₀β)/e₀` ✓. W2-L2 at `k = 0` (so `u = V = β`) and `𝔰 = s`: the identity reads `T + (ℓ′𝔰 − ℓu′) = 0`, i.e. `(ℓ₀β − s)/e₀ = −(ℓ′₀s − ℓ₀u′)` ✓ so `(s − ℓ₀β)/e₀ = ℓ′₀s − ℓ₀u′` ✓ **matching the displayed `ℓ′₀s − ℓ₀u`** (with `u = u′` at `k = 0`) ✓ **which is the ε₁-exponent from `.08`'s `ε_m(β) := z_m^{ℓ′_{m−1}s − ℓ_{m−1}u}`** ✓ **exact.**

**RESOLUTION TRACE:** statement 288–304 · consumed at 987–989 (`.39`) · generalized out of range 1390–1391, 1405–1434 (shard 2).

**TEETH:** **CK-VD1, 156 samples, 0 violations.** Disposition: executable regression. **This family is also the base of the Σ-LAW's level-m generalization**, so the same mechanism is now verified at 2,828 samples in an accepted supplier note.

---

### EFF.GRTW2.s1of2.15  [scope-record]  — §3's shared-key scope

**CANONICAL STATEMENT:** verbatim, lines 310–316.

**FORM:** section preamble paragraph with an inline `[r1, F1]` bracket.

> “Throughout §3 the junction at level m+1 is **shared-key** (§1.3). This is
> the honest scope: above an interior byte-divergence the print chain
> multiplies by ITS OWN keys and the harness-read comparison is a different
> computation (the runner marks those junctions SKIP — exactly the probe's
> 6 above-twist rows; clause 3 removes them by transport **[r1, F1: at the
> re-scoped grade — the cure at the transported chamber's above-twist
> junctions is MEASURED, riding W2-OPEN-2; §5.2]**).”

**CONDITIONALITY:** **This preamble is where the 6 SKIP junctions enter, and they are the same 6 that remain OPEN at HEAD** (E5's “6/44 above-twist junctions riding W2-OPEN-2”, shard 2). The `[r1, F1]` bracket is the only correction; it downgrades “clause 3 removes them” to “MEASURED, riding W2-OPEN-2”. `SUPERSESSION KIND: scope-pin`.
**The scope is honest in a specific technical sense the note states**: above a byte-divergence the comparison is *a different computation*, not a failed one.

**DERIVATION:** Scope declaration.

*Arithmetic audit (rule 22).* 6 SKIP junctions ✓ = the “6 above-twist rows” ✓ = the “6/44 junction-levels above a first twist” at `.05` ✓ = “28 r ≥ 3 junctions, of which 6 … marked SKIP” at `.18`(b) ✓ **four independent occurrences of the same 6, all consistent** ✓.

**RESOLUTION TRACE:** statement 310–316 · the 6 at 383–385, 438–441, 680–682, 1074 · out-of-range 1527 (shard 2).

**TEETH:** the SKIP marking is itself a machine behaviour; **CK-BYTE records all 6 as samples with a byte verdict but no walk** (`.22`).

---

### EFF.GRTW2.s1of2.16  [lemma]  — §3.1 (HR-REC), the exact transfer recursion

**CANONICAL STATEMENT:** verbatim, lines 320–336.

**FORM:** `###`-headed section body with two indented ASCII displays.

> “Let P = construct(r, V, φ) be a print output at GMN order r ≥ 3 (output
> harness level Q := r−1), children P_j = construct(r−1, V_j, φ_j) at slots
> k_j = s + je_{Q−1}, with the print's child prescription (tex 1213–1218)
>
>     φ_j(y) ≡ y^{T_j}·c_j(y)  (mod ψ_{Q−2}),   T_j = (ℓ_{Q−2}u_j − 𝔰_j)/e_{Q−2}.
>
> Then, digits being on-grid and on-line (W2-L0), the harness read obeys
>
>     (HR-REC)   R_Q v(P) = Σ_j ε_{Q−1}(V_j) · R_{Q−1}v(P_j) · z_Q^j ,
>
> and by W2-L2 the ε-and-twist pair collapses per node:
> ε_{Q−1}(V_j)·z_{Q−1}^{T_j} = z_{Q−1}^{A_{Q−1}·k_j}. With the base
> R₁v(construct(2, V, φ)) = φ(z₁) (W2-L1), the recursion computes the
> harness read of EVERY print construction from read data alone, with no
> polynomial arithmetic. [Machine: CK-REC — the semantic simulator equals
> the actual harness read at every node of every shared-key roster junction,
> 55 nodes, 0 violations.]”

**CONDITIONALITY:** **HR-REC is the note's most durable export.** It is in the accepted enumeration (F3: “**HR-REC**” is listed by name at 1345), it is untouched by every round and every append, and it is **independently re-derived by PE6** (“the functional-equation re-derivation of HR-REC”, 1338–1339, shard 2). **What it does NOT give** is the scalar normal form — E5's finding 2 turns exactly on this: “**Section 3.3(c) computes the slot ratios but does not prove they form a geometric progression**” (1480, shard 2). So HR-REC is exact and complete, and *insufficient* for the scalar orbit off (C-coll). See `.18`, `.25`.

**DERIVATION:** The recursion follows from the print's child prescription (tex 1213–1218) with the digits on-grid/on-line by W2-L0, and the per-node collapse is W2-L2.

*Arithmetic audit (rule 22).* The per-node collapse `ε_{Q−1}(V_j)·z_{Q−1}^{T_j} = z_{Q−1}^{A_{Q−1}k_j}` is exactly W2-L2's junction specialization ✓ (`.13`), with `u − V = k_jW` ✓ matching the slot geometry `k_j = s + je_{Q−1}` ✓. Base: `R₁v(construct(2,V,φ)) = φ(z₁)` ✓ = W2-L1 ✓ (`.12`). **So HR-REC is W2-L1 + W2-L2 assembled by induction** ✓ and needs nothing else ✓.

**RESOLUTION TRACE:** statement 320–336 · consumed at 340–341, 388–392, 520–524, 837–843 · re-derived out of range 1338–1339 (PE6) · its insufficiency 1478–1531 (E5 finding 2).

**TEETH:** **CK-REC — 55 nodes, 0 violations**, a *semantic simulator* equalling the actual harness read at every node. **Disposition: executable regression against an independent implementation of the same recursion.**

---

### EFF.GRTW2.s1of2.17  [scope-record]  — §3.2, the conjugation and the collapse perimeter (C-coll)

**CANONICAL STATEMENT:** verbatim, lines 340–359.

**FORM:** `###`-headed section body with a display, two bulleted effects, and a bold-headed perimeter definition.

> “Unfolding one level: R_Q v(P) = Σ_j Θ_{Q−1}(V_j)·z_{Q−1}^{A_{Q−1}k_j}·c_j·z_Q^j,
> where Θ_{Q−1}(V_j) is the gauge accumulated in R_{Q−1}v(P_j) below. Two
> non-scalar effects appear for Q ≥ 3:
>
> * the **letter twist**: the j-dependent part of the character rides
>   z_{Q−1}^{A_{Q−1}e_{Q−1}·j}, i.e. the letter z_Q is effectively replaced
>   by ϑ_Q·z_Q with ϑ_Q := (junction character at level Q)^{−1} — the deeper
>   covariance re-appearing inside the dictionary;
> * the **mod-wrap**: the child prescription is the REDUCED representative
>   y^{T_j}c_j(y) mod ψ_{Q−2}, and reduction does not commute with y ↦ ϑy
>   unless ϑ acts trivially or the representative stays a monomial.
>
> **The collapse perimeter (C-coll):** every interior junction character is
> trivial as a field element — ξ_Q = 1 for 2 ≤ Q ≤ m (ξ_Q per §3.4's
> formula). On (C-coll) all wraps drop, every Θ is a z-monomial linear in
> its weight argument, and the whole dictionary is scalar per slot.
> Junctions with m = 1 have no interior levels: (C-coll) is vacuous there.
> Outside (C-coll) the law is still the exact recursion (HR-REC), which is
> closed in the read data; only the two-parameter SCALAR normal form below
> needs the perimeter. Boundary witness: §3.5.”

**CONDITIONALITY:** **(C-coll) is the perimeter every scalar claim in the note lives on**, and the two mechanisms that break it — the letter twist and the mod-wrap — are named precisely. **The mod-wrap is what the I4B r = 5 boundary witness exhibits** (`.23`) and what E5's finding 2 turns on (“HR-REC computes the three ρ_j but supplies no identity forcing this equation **when mod-wrap does not collapse**”, 1520, shard 2). Untouched by every round; **its scope is re-confirmed rather than corrected by E5**.
**“(C-coll) is vacuous at m = 1”** is what makes W2-C2(a) and W2-ID1 unconditional (`.18`, `.31`).
**One honesty item recorded at `.27`:** “whether (C-coll) survives into each transported chamber is NOT tracked” — so above `r₀` the recorded pair is the orbit scan's per-instance value, not the formula.

**DERIVATION:** One unfolding step of HR-REC.

**RESOLUTION TRACE:** statement 340–359 · the boundary witness 446–466 (`.23`) · the transport honesty item 697–700 (`.30`) · E5's use 1478–1531 (shard 2).

**TEETH:** **CK-SLOT's 22 non-SKIP samples include the non-perimeter ones**, “there the sim prediction is the recursion, not the scalar form” (`.18`(b)) — so the machine distinguishes the two regimes.

---

### EFF.GRTW2.s1of2.18  [theorem]  — THEOREM W2-C2 (the slot-ratio law), (a)/(b)/(c)

**CANONICAL STATEMENT:** verbatim, lines 363–392.

**FORM:** `###`-headed section with a definition paragraph and three bold-lettered clauses, each with a proof and a machine bracket; clause (b) carries an `[r1, F3]` count correction.

> “At a shared-key junction at level m+1 define the slot ratio ρ_j :=
> (level-m read of the print slot P_j) / (level-m read of the harness slot
> C_j), j < g_m with ψ_{m,j} ≠ 0 (the harness read of C_j is
> ε_m(β_j)^{−1}ψ_{m,j} by REALIZE R3).
>
> **(a) m = 1 (unconditional).** ρ_j = c · z₁^{A₁e₁·j}. *Proof.* By W2-L1
> the print slot reads to φ_j(z₁) = z₁^{T_j}·c·ψ_{1,j}; multiply by
> ε₁(V_j)ψ_{1,j}^{−1} and apply W2-L2 with u_j − V_j = k_j·w₁Φ₁, k_j = je₁
> (top junction has s = 0 since V = e₁g₁·... ≡ 0 mod e₁... V = e_m g_m
> γ_{m+1}·(e-divisible): s = 0). ∎ [Machine: CK-SLOT-M1, all 16 r = 3
> junctions exact.]
>
> **(b) general m on (C-coll).** ρ_j = c · Θ_m(V_j) · z_m^{A_m e_m·j} with
> Θ_m the collapsed gauge (linearized recursion of §3.4); the ratios are
> geometric in j and the (ξ, w) normal form of §3.4 holds. *Proof at attempt
> grade:* induction on the level through (HR-REC), all wraps dropping on
> (C-coll); the linearization step (replacing 𝔰(V) = ℓV mod e by ℓV) changes
> the value by a power of the trivial interior character. ∎ [Machine:
> CK-SLOT — sim-predicted ratios equal the actual slot ratios at ~~ALL 24~~
> **[r1, F3] all 22** shared-key junctions r ≥ 3 **(the roster has 28 r ≥ 3
> junctions, of which 6 — exactly the probe's above-twist rows — are marked
> SKIP and carry no shared-key comparison; CK-SLOT's 44 samples = 16 r = 2
> rows + 28 r ≥ 3 rows, the ratio law checked on the 22 non-SKIP)**,
> including the non-perimeter ones (there the
> sim prediction is the recursion, not the scalar form); 0 violations.]
>
> **(c) exact general law.** At every shared-key junction the slot ratios
> are computed by (HR-REC) + W2-L1/L2 — a finite explicit recursion in the
> read data. This is the general closed form; (a)/(b) are its scalar
> specializations. [Machine: CK-SLOT under (c) reading, 0 violations.]”

**CONDITIONALITY:**
(a) **is unconditional and is in the accepted enumeration** (F3 lists “W2-C2”).
(b) **holds on (C-coll) only** — and this is exactly the boundary E5's finding 2 sharpens: **(c) computes the ratios but does not prove them geometric**, so “the general scalar orbit asserted in W2-C1 does not follow from HR-REC” (1480, shard 2). `SUPERSESSION KIND: scope-pin` on how (c) may be consumed. **W2-C2 itself is NOT superseded** — E5 supersedes W2-C1's universal reading, and its consumer sweep says “W2-C2(a), W2-ID1, HR-REC, and the §3.4 scalar display on (C-coll) survive unchanged” (1526, shard 2) ✓.
(c) **The `[r1, F3]` count correction is one of three in the same finding** (`.22`, `.41`): `24 → 22` shared-key r ≥ 3.

*Arithmetic audit (rule 22), the count decomposition recomputed.* “CK-SLOT's 44 samples = 16 r = 2 rows + 28 r ≥ 3 rows” ✓ `16 + 28 = 44` ✓ **matching the family table's `CK-SLOT … 44`** ✓ (`.37`). “28 r ≥ 3 junctions, of which 6 … SKIP” ⟹ `28 − 6 = 22` non-SKIP ✓ **exactly the corrected figure** ✓. And `44` here is the same 44 as the junction-level census at `.05` ✓ — **the two 44s coincide**, which the note does not state. Recorded.
*The (a) proof's `s = 0` claim.* `V = e_m g_m γ_{m+1}` is divisible by `e_m`, and `s = ℓV mod e_m` ⟹ `s = 0` ✓ **exact** ✓ (the displayed parenthetical is garbled with an ellipsis but the arithmetic is right).

**DERIVATION:** Quoted inline for all three clauses.

**RESOLUTION TRACE:** statement 363–392 · the closed form 394–411 (`.19`) · E5's scope correction 1478–1531 (shard 2) · the count correction's twins 430–442, 1081–1086.

**TEETH:** **CK-SLOT 44 / CK-SLOT-M1 16, both GREEN.** Disposition: executable regression, with the (c)-reading checked separately at the non-perimeter junctions.

---

### EFF.GRTW2.s1of2.19  [definition]  — §3.4, THE (ξ, w) CLOSED FORM

**CANONICAL STATEMENT:** verbatim, lines 396–411 (the display and its validity line).

**FORM:** display (a boxed ASCII recursion with rule lines).

> “    A_m  := ℓ_{m−1}·g_{m−1}·γ_m                 (m ≥ 1;  A_m = 0 ⟺ e_{m−1} = 1)
>     χ_1  := 1 ;
>     χ_m  := χ_{m−1}^{ ℓ′_{m−1} − ℓ_{m−1}·w_{m−1}Φ_{m−1} } · z_{m−1}^{ A_{m−1}·ℓ_{m−1} }   (m ≥ 2)
>     ─────────────────────────────────────────────────────────────────────
>     ξ_{m+1} := χ_m^{ γ_{m+1} } · z_m^{ −e_m·A_m }
>     w_{m+1} := χ_m^{ −g_m·γ_{m+1} }
>     ─────────────────────────────────────────────────────────────────────
>     R_{r−1}( Φ_{m+1}^{har} )(y)  =  w_{m+1} · ψ_m( ξ_{m+1}·y )     [GMN r = m+2]
>
> with the print tie z_m^{−A_m} = c₁ (the Theorem-`phir` constant), so at
> m = 1 the pair is exactly
>
>     (any m = 1 junction)   ξ = c₁^{e₁} = z₁^{−e₁·ℓ₀·g₀·h₀},   w = 1.
>
> Validity: m = 1 unconditional (THM W2-C2(a) + §4.2); m ≥ 2 on (C-coll);
> outside (C-coll) the pair is read off the exact recursion (§3.3(c)).”

**CONDITIONALITY:** **“the (ξ,w) covariance closed form” is FIRST in the accepted enumeration** (F3, 1345). Its validity line is exactly the scope E5's finding 2 re-affirms: unconditional at m = 1, on (C-coll) at m ≥ 2, and off (C-coll) only the recursion. **Out of range, the Σ-LAW annex CORRECTS a downstream reading of these characters** (1409–1412, shard 2): the covariance map is “the **ξ-formula composite** (the §3.4 characters ξ_q = χ_{q−1}^{γ_q}z_{q−1}^{−e_{q−1}A_{q−1}}, χ-chain included — **NOT the bare interior twist** z_{q−1}^{A_{q−1}e_{q−1}})”. **So a later note had to correct itself for using the bare twist where the χ-chain was needed** — evidence that the χ-chain is load-bearing and easy to drop. Recorded.

**DERIVATION:** From W2-C2 (`.18`) plus §4.2's residual reading (`.25`).

*Arithmetic audit (rule 22), the m = 1 specialization recomputed.* At `m = 1`: `χ_1 = 1` ✓ so `ξ_2 = 1^{γ_2}·z_1^{−e_1A_1} = z_1^{−e_1A_1}` ✓ and `w_2 = 1^{−g_1γ_2} = 1` ✓ **matching “w = 1”** ✓. With `A_1 = ℓ_0g_0γ_1` and `γ_1 = h_0` (from `.08`) ✓: `ξ = z_1^{−e_1ℓ_0g_0h_0}` ✓ **exactly the displayed `z₁^{−e₁·ℓ₀·g₀·h₀}`** ✓. And `c₁ = z_1^{−A_1}` (from `.10`) ⟹ `c₁^{e_1} = z_1^{−e_1A_1} = ξ` ✓ **the displayed print tie** ✓. **All three forms agree.**
*Consistency with W2-C2(a).* `ρ_j = c·z₁^{A₁e₁j}` with `c = c₁^{e₁g₁} = ξ^{g₁}` ✓ and `z₁^{A₁e₁j} = ξ^{−j}` ✓ so `ρ_j = ξ^{g₁−j}` ✓ — **which is exactly what W2-ID1's proof uses at `.31`** ✓ **cross-check passes.**

**RESOLUTION TRACE:** statement 396–411 · remarks 412–442 (`.20`–`.22`) · the Σ-LAW correction 1409–1412 (shard 2).

**TEETH:** **CK-XI — 21 perimeter junctions + 1 recorded boundary = 22, GREEN** (`.37`), checking that the displayed pair satisfies the orbit equations.

---

### EFF.GRTW2.s1of2.20  [scope-record]  — §3.4 remark 1 (the covariance is generated by the print's own constant)

**CANONICAL STATEMENT:** verbatim, lines 414–421.

**FORM:** numbered remark inside §3.4.

> “1. **The whole covariance is generated by the print's own normalization
>    constant**: at m = 1, ξ = c₁^{e_m} and w = 1 — the covariance is
>    Thm-`phir`'s c₁ raised to the ramification of the read. The χ-chain is
>    the accumulated lower-level gauge; its composition exponent
>    ℓ′_{m−1} − ℓ_{m−1}w_{m−1}Φ_{m−1} is the SAME descent operator as the
>    [ILN]† shift recursion S_{j−1} = D_jγ_j + S_j(ℓ′_{j−1} −
>    ℓ_{j−1}w_{j−1}Φ_{j−1}) — the covariance gauge composes by the cocycle
>    shift chain.”

**CONDITIONALITY:** **A structural identification, not a claim needing proof** — and it is the load-bearing observation for the accepted LIFTCORNER's consumption (the acceptance record names “the accepted LIFTCORNER's shift-descent consumption”, 1351–1352, shard 2). **Out of range, the Σ-LAW's evaluator route REDERIVES this recursion from the other side**: “the gauge-ratio recursion Λ_q(w) = χ_q^{−w} **REDERIVES the §3.4 χ/ξ recursion from the evaluator side**” (1418–1419, shard 2) ✓ — **an independent derivation of the same chain.** `SUPERSESSION KIND: license` (corroboration, nothing moves).

**DERIVATION:** Identification of two recursions displayed side by side.

**RESOLUTION TRACE:** statement 414–421 · the independent re-derivation 1417–1419 (shard 2) · the consumer 1351–1352 (shard 2).

XREF: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` ✓ present (the shift recursion's source).

**TEETH:** Indirect — CK-XI tests the χ-chain's output; the shift-recursion identification is an observation.

---

### EFF.GRTW2.s1of2.21  [scope-record]  — §3.4 remark 2 (non-uniqueness; the support stabilizer)

**CANONICAL STATEMENT:** verbatim, lines 422–429.

**FORM:** numbered remark inside §3.4.

> “2. **Non-uniqueness (support stabilizer).** The orbit pair (ξ, w) with
>    R = w·ψ(ξy) is unique only modulo the stabilizer of supp(ψ_m): if
>    ψ_m is sparse (e.g. ψ = y² + c over F₃), distinct characters satisfy
>    the same equations. The closed form is stated as: THE DISPLAYED PAIR
>    SATISFIES the orbit equations. [Machine: CK-XI, 21 perimeter junctions,
>    0 violations; the I4B r = 4 junction is byte-equal yet carries the
>    nontrivial formula character ξ = −1 invisibly on supp(ψ₂) = {0, 2} —
>    the invisible-twist genre.]”

**CONDITIONALITY:** **This remark is the seed of the note's deepest finding.** Three later things depend on it:
(i) **The claim is deliberately weakened**: “The closed form is stated as: THE DISPLAYED PAIR **SATISFIES** the orbit equations” — not “is the pair”.
(ii) **PE3's counter-instance to the converse is exactly a support-stabilizer instance** (`.32`): at `supp(ψ₁) = {0,3}` over `F₄`, all three units of `F₄^×` satisfy the orbit equations, and the sealed scan records `ζ` rather than `1`.
(iii) **The invisible-twist genre named here (I4B r = 4) is the mechanism the r2 warrant worries about one layer down** (`.30`: “a read-invisible deeper-node divergence (the §3.5 invisible-twist genre one layer down)”).
**Untouched by every round and append** — the remark was right and the arc grew out of it.

**DERIVATION:** Observation with a worked instance.

*Arithmetic audit (rule 22).* `ψ = y² + c` over `F₃`: `supp = {0, 2}`, and a character `ξ` stabilizes the support-weighted equations iff `ξ^0 = ξ^2` in the relevant sense, i.e. `ξ² = 1` ⟹ `ξ ∈ {±1}` ✓ **a two-element stabilizer** ✓ — so `ξ = −1` is invisible ✓ **exactly the I4B r = 4 instance** ✓.

**RESOLUTION TRACE:** statement 422–429 · the boundary witness 446–466 (`.23`) · the counter-instance 741–779 (`.32`) · the r2 warrant 659–669 (`.30`).

**TEETH:** **CK-XI, 21 perimeter junctions, 0 violations** — and the I4B r = 4 invisible twist is *recorded* by the machine, not hidden.

---

### EFF.GRTW2.s1of2.22  [scope-record]  — §3.4 remark 3 (the byte-equality law) with its `[r1, F3]` count corrections

**CANONICAL STATEMENT:** verbatim, lines 430–442.

**FORM:** numbered remark with two struck-and-replaced count figures.

> “3. **Byte-equality law (the F1 verdict from read data).** A shared-key
>    junction is byte-equal iff every node value of the two builders' shared
>    recursion tree agrees; at m = 1 this is: c·z₁^{A₁e₁j} = 1 for every
>    j ∈ supp(ψ_m) ∩ [0, g_m). This reproduces the probe's full F1 verdict
>    pattern ~~(which 18 junctions RED, which 12 GREEN)~~ **[r1, F3] (on this
>    runner's own 28-junction r ≥ 3 roster: which 18 RED, which 10 GREEN —
>    the 12-GREEN figure was the probe note's, from its differently-counted
>    30-junction table, copied without reconciliation)**. [Machine: CK-BYTE —
>    walk verdict ≡ actual byte compare at ~~all 28 walked~~ **[r1, F3] all
>    22 walked** junctions **(+ the 6 above-twist SKIP junctions, recorded as
>    CK-BYTE samples with a byte verdict — all 6 byte-RED — but no walk:
>    28 samples total)**, 0
>    violations.]”

**CONDITIONALITY:** **The byte law itself is unconditional and is what W2-ID1 consumes** (`.31`). The two `[r1, F3]` corrections are **count corrections caused by copying a figure across notes without reconciling rosters** — the note says so: “the 12-GREEN figure was the probe note's, from its differently-counted 30-junction table, **copied without reconciliation**”. `SUPERSESSION KIND: counter re-reading`.
**The law's quantifier is the crux of the whole r2/r3 arc**: it “quantifies over EVERY node value of the recursion tree”, whereas the recorded pair “sees only the top-layer reads” (`.30`) — that gap is (OPEN-2a).

*Arithmetic audit (rule 22), all four figures reconciled.* Runner roster: 28 r ≥ 3 junctions ✓; 6 SKIP (all byte-RED) ✓; 22 walked ✓. Walked split: “18 RED / 10 GREEN” — but `18 + 10 = 28`, not 22. **Resolution:** §7's independent recount (1085–1086) says “independent recount: 28 = 22 + 6 SKIP; **walked split 10 GREEN/12 RED**; the 6 SKIPs all byte-RED → 18/10” ✓ — so `12 + 10 = 22` walked ✓ and `12 + 6 = 18` RED total ✓ **the 18/10 figure is over all 28, the 12/10 over the 22 walked** ✓. **Both are consistent and the note gives both, at different sites.** The probe's 12-GREEN came from a 30-junction table ✓ a different roster ✓ **the reconciliation is complete and this compiler's recount matches r1's** ✓.

**DERIVATION:** The m = 1 form is read off W2-C2(a): byte-equal ⟺ `ρ_j = 1` on the support ✓ (`.18`(a)).

**RESOLUTION TRACE:** statement 430–442 · the recount 1081–1086 (`.41`) · consumed at 711–719 (`.31`), 661–663 (`.30`).

**TEETH:** **CK-BYTE — 28 samples, 0 violations**, with the walk/no-walk split disclosed. Disposition: executable regression; **the SKIP junctions are recorded rather than dropped**, which is what lets the recount close.

---

### EFF.GRTW2.s1of2.23  [scope-record]  — §3.5, the I4B r = 5 boundary witness and W2-BOX-1

**CANONICAL STATEMENT:** verbatim, lines 446–466.

**FORM:** `###`-headed section body with two `[r1, F5]` renamings inline and a bold-headed box.

> “I4B (ℤ₃; reads (3,2,1),(2,1,1),(1,1,2),(2,1,1)) at r = 5: the interior
> formula character ~~ξ₄~~ **ξ₃ [r1, F5]** = χ₂^{γ₃}z₂^{−e₂A₂} = (−1)^{−13} = −1 is nontrivial
> (so (C-coll) fails) yet support-invisible at its own junction (ψ₂ = 1+y²,
> even support: r = 4 byte-equal). At r = 5 it re-emerges through the
> mod-wrap: the recorded orbit is (ξ, w) = (−1, −1) while the χ-formula
> gives (1, 1)·… — off by exactly a power of the interior ~~ϑ₄~~ **ϑ₃ [r1,
> F5]** = −1 entering
> through the monomial reduction y^{T+1} mod (y²+1) = ±y^{(T+1) mod 2}.
> **[r1, F5 — indexing: §3.2's ϑ_Q and §3.4's ξ_{m+1} are LEVEL-indexed, and
> the displayed formula is ξ_{m+1} at m = 2 — the level-3 junction, GMN
> r = 4 — so its level-indexed name is ξ₃ (with ϑ₃ = ξ₃^{−1}). The r0 text
> named it ξ₄/ϑ₄ (r-indexed), colliding with the level-indexed
> ξ₄ = χ₃^{γ₄}z₃^{−e₃A₃}, a DIFFERENT element (= 1 on I4B). Renamed;
> arithmetic unchanged (PE1 re-verified: ℓ₀ = 2, χ₂ = z₁⁴ = 1, A₂ = 13,
> z₂ = −1, recorded r = 5 orbit (−1,−1) per the JSON, formula pair (1,1)).]**
> **W2-BOX-1 (the exact residue of clause 2):** a two-parameter scalar
> formula on ALL junctions would need the monomial-collapse exponents (the
> ϑ-powers picked up by reduced representatives) tracked explicitly; the
> exact law is (HR-REC), the scalar form is proved only on (C-coll). On the
> roster every junction is either on (C-coll) or monomial-collapsing with
> scalar orbit anyway (CK-SLOT 0 violations; exactly 1 boundary junction).”

**CONDITIONALITY:**
(a) **The `[r1, F5]` renaming is an indexing collision fix**: the r0 text used an r-index where the surrounding sections use level-indices, and the r-indexed name `ξ₄` denotes a *different element* (= 1 on I4B). `SUPERSESSION KIND: replacement` (naming), with “arithmetic unchanged” and PE1's re-verification quoted.
(b) **W2-BOX-1 is one of the note's three fenced boxes** and its residue is exactly what E5's finding 2 formalizes as the geometricity test (`.25`).
(c) **“exactly 1 boundary junction”** on the roster — and E5's re-displayed census keeps it as its own category: “1/44 individually scalar-orbit-confirmed (I4B r = 5)” ✓ (1527, shard 2). **So this one junction survives every upgrade as its own census entry.**

**DERIVATION:** A worked instance; the mechanism is §3.2's mod-wrap.

*Arithmetic audit (rule 22), the re-verified data recomputed where possible.* Reads `(3,2,1),(2,1,1),(1,1,2),(2,1,1)` over ℤ₃. `ℓ₀`: solve `ℓ₀h₀ + ℓ₀′e₀ = 1` with `(e₀,h₀) = (3,2)` and `0 ≤ ℓ₀ < 3`: `2ℓ₀ ≡ 1 (mod 3)` ⟹ `ℓ₀ = 2` ✓ **matching the re-verification** ✓. `ψ₂ = 1 + y²` has `supp = {0,2}` ✓ **even support** ✓ so `ξ = −1` is invisible there ✓ (`.21`'s stabilizer computation) ✓. `(−1)^{−13} = −1` ✓ since `−13` is odd ✓. The monomial reduction `y^{T+1} mod (y²+1) = ±y^{(T+1) mod 2}` ✓ — reducing `y^k` modulo `y²+1` gives `(−1)^{⌊k/2⌋}y^{k mod 2}` ✓ **so a sign appears exactly as claimed** ✓. `χ₂ = z₁⁴`; with the residue chain's `K₁` and `z₁`… the note asserts `= 1`, which needs `ord(z₁) | 4`; no independent check available. **Recorded as consistent-but-partially-unverifiable**: `ℓ₀ = 2`, the support parity, the sign of `(−1)^{−13}`, and the reduction rule all reproduce; `χ₂ = 1` and `A₂ = 13` do not (no field data displayed).

**RESOLUTION TRACE:** statement 446–466 · the census entry 1527 (shard 2) · E5's formalization 1498–1520 (shard 2).

**TEETH:** **CK-XI records the boundary junction explicitly** (“21 perimeter junctions; 1 recorded boundary = I4B r=5”, `.37`) — the machine separates it rather than absorbing it. **Disposition: measurement, with the boundary case isolated.** **PE3 reproduced it from scratch** (“the I4B r = 5 boundary reproduced from scratch”, `.03`).

---

### EFF.GRTW2.s1of2.24  [lemma]  — LEMMA W2-C1a (the two polygon legs) with its `[r1, F2]` chamber qualifier

**CANONICAL STATEMENT:** verbatim, lines 474–503.

**FORM:** `###`-headed section with a bold-headed lemma carrying a struck-and-replaced hypothesis and a long bracketed honest split, then a proof.

> “**LEMMA W2-C1a.** ~~At every level m+1 (no shared-key hypothesis needed for
> the harness-side data):~~ **[r1, F2] At every junction level m+1, evaluated
> in a chamber whose keys BELOW the junction are byte-shared with the harness
> chain (the §1.3 perimeter restricted to q ≤ m; NO hypothesis on the junction
> itself, so every first-divergence junction is in scope):**
> v_r(Φ_{m+1}^har) = e_{r−1}f_{r−1}v_r(φ_{r−1}) and
> the order-(r−1) polygon of Φ_{m+1}^har is one-sided with support exactly
> {0, e_m g_m} ∪ (attained interior grid slots), initial abscissa 0, final
> abscissa e_m g_m. **[r1, F2 — the honest split the probe's own record
> forces: the HARNESS-SIDE content (slots at exact level-m weights, all on
> one line — the proof below) holds at every level of every tower with no
> chamber hypothesis. What the qualifier fences is the GMN READING: v_r and
> the order-(r−1) polygon are ambient-chamber quantities, identified with the
> harness line through the P-index tie, and the sealed probe's own F2 record
> has exactly 6 vok/onesided FAILURES of the unqualified statement — at
> raw-chain junctions above an interior twist (the WEIGHT/SUPPORT splits of
> §5.1's mechanism paragraph). In transported chambers the statement is
> TW-ADM's MEASURED content (44/44), riding W2-OPEN-2 above each chamber's
> first twist. Consumer note (PE1 §C.4 adjudication): the accepted [JB]'s
> §0M column (d) already consumes the REPAIRED pairing — "W2-C1a for the
> window object; W2-C3 for the transported chamber", with W-2 clause 1's own
> conditionality riding — so no accepted text is falsified by this
> qualifier.]** *Proof.* The slots C_k sit at abscissas e_m k with exact
> level-m weights β_k = (g_m−k)γ_{m+1} (REALIZE R2), so every attained point
> lies ON the line e_m·β + abscissa·h-value = e_m g_m γ_{m+1} = v_r-value =
> e_{r−1}f_{r−1}v_r(φ_{r−1}) (`vrphir`, tex 1259, through the P-index tie
> γ_{m+1} = v_r(φ_{r−1})). The initial slot k = 0 is attained because
> ψ_m(0) ≠ 0 (class pin); the final slot is the monic top. ∎ [Machine:
> probe F2 vok/onesided green at all 45 first-divergence/top junctions;
> runner TW-ADM 44/44 in the transported chambers.]”

**CONDITIONALITY:** **The `[r1, F2]` split is exemplary and should be preserved whole: the HARNESS-SIDE content is unconditional; the GMN READING carries the chamber qualifier.** The evidence for the qualifier is the probe's own record — “exactly **6** vok/onesided FAILURES of the unqualified statement” ✓ **the same 6 as everywhere else** (`.15`).
**The consumer note is a cross-note claim and should be read per rule 10:** it asserts that “the accepted [JB]'s §0M column (d) already consumes the REPAIRED pairing”, adjudicated by PE1 §C.4. **This compiler did not open GRTJB to verify the column's text** — recorded as OPEN-CALL 4. Note that a *later* orchestrator annex (out of range, 1363–1365) records GRTJB row 15's annotation as **EXECUTED at `5054d69`** ✓ commit verified — so the fold that this note left owed did land.
**E5's finding 2 leaves W2-C1a alone**: “Outside that scope the proved conclusion consists of **W2-C1a's polygon statement** plus the exact HR-REC residual” (1522, shard 2) ✓ — **W2-C1a survives every correction in the arc.**

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22).* Every slot `C_k` at abscissa `e_mk` with weight `β_k = (g_m−k)γ_{m+1}`: the line value is `e_m·β_k + (e_mk)·(h-value per abscissa)`. With the line through `(0, e_mg_mγ_{m+1})` and `(e_mg_m, 0)`, the value at abscissa `e_mk` is `e_mg_mγ_{m+1} − e_mk·γ_{m+1} = e_m(g_m−k)γ_{m+1} = e_mβ_k` ✓ **so every slot sits exactly ON the line** ✓. Endpoints: `k = 0` attained since `ψ_m(0) ≠ 0` ✓ (`.08`'s class pin); `k = g_m` is the monic top ✓. **Support `{0, e_mg_m} ∪ interior` ✓ one-sided ✓.** The `v_r` identification `e_{r−1}f_{r−1}v_r(φ_{r−1}) = e_mg_mγ_{m+1}` uses `.09`'s dictionary `(e_i,f_i)^GMN = (e_{i−1},g_{i−1})^har` ✓ so `e_{r−1}f_{r−1} = e_mg_m` ✓ and `v_r(φ_{r−1}) = γ_{m+1}`… **the note's own §1.2 says `v_{i+1}(φ_i) = γ_i^har`** ✓ giving `v_r(φ_{r−1}) = γ_{r−1}^har = γ_{m+1}` ✓ (with `r − 1 = m + 1`) ✓ **the identification closes exactly.**

**RESOLUTION TRACE:** statement 474–503 · the 6 failures 310–316 (`.15`), 606–615 (`.28`) · the fold's execution 1363–1365 (shard 2) · E5's exemption 1522 (shard 2).

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` — **verified present** (the consumer named).
PIN: `5054d69` ✓ commit.

**TEETH:** **probe F2 45/45 (foreign) + runner TW-ADM 44/44.** Disposition: executable regression on two instruments, one foreign; and **the probe's 6 FAILURES are the evidence for the qualifier**, i.e. a foreign instrument's red rows became this note's hypothesis.

---

### EFF.GRTW2.s1of2.25  [theorem]  — THEOREM W2-C1 (admissible representative, clause 1)

**CANONICAL STATEMENT:** verbatim, lines 507–526.

**FORM:** `###`-headed section with a bold-headed theorem, an indented ASCII display, and a proof.

> “**THEOREM W2-C1 (admissible representative, clause 1).** At a shared-key
> junction on the §3 perimeter, the print residual of the harness lift is
>
>     R_{r−1}(Φ_{m+1}^har)(y) = w_{m+1}·ψ_m(ξ_{m+1}·y)
>
> with (ξ, w) the §3.4 pair. Consequently, under the pinned (P-ell)
> convention Φ_{m+1}^har is a monic polynomial of type-degree m_r whose
> residual is a UNIT MULTIPLE OF THE ξ-CONJUGATE of ψ_m: it is a strict
> Def-2.12 representative of the ξ-conjugate type t^ξ (ψ_m replaced by
> ψ_m^{(ξ)}(y) := ξ^{−g_m}ψ_m(ξy), a monic irreducible with the same
> (e, h, g) data), and a representative of t ITSELF iff the character is
> support-trivial (ξ^j constant on supp ψ_m — e.g. always when ξ = 1;
> the I4B r = 4 even-support case shows support-triviality is weaker than
> ξ = 1). *Proof.* The slot-j residual coefficient of Φ^har is the slot-j
> coefficient of R(φ_r^cls) divided by ρ_j (the reads differ by ρ_j and the
> print evaluator is value-functorial on on-line digits — this is the same
> HR-REC mechanics read backwards); Thm-`phir` gives R(φ_r^cls) = c·ψ_m,
> and c/ρ_j = w·ξ^j by §3.3–3.4. Irreducibility and the (e,f) data of the
> conjugate: PARI leg. ∎ [Machine: probe F2-orbit 45/45 + F4 24/24 (both
> top lifts irreducible with (e,f) = (∏e_j, d₀∏g_j)); runner CK-XI.]”

**CONDITIONALITY:** **The universal reading of this theorem is SUPERSEDED by THEOREM W2-C1-CORR** (E5 finding 2, 1484–1531, shard 2). Quoted:

> “**[ANNEX 2026-08-12, certifier correction — W2-C1 SCALAR-ORBIT SCOPE.]** The universal reading of THEOREM W2-C1 outside the scalar-collapse perimeter is **SUPERSEDED** by the following proved display.”

with the replacement's three items: (1) `m = 1` unconditional; (2) `m ≥ 2` on (C-coll); (3) at a general shared-key junction outside (C-coll), **HR-REC computes `B_m` exactly, but no scalar orbit is asserted without a finite geometricity condition** `a_j = wξ^j` on `supp ψ_m`. And the consequent statement correction (1522): “CLAUSE 1 and the §6.2 W2-C1 row are proved universally only at `m = 1` and on (C-coll), and conditionally at other shared-key junctions when the displayed geometricity test is established.”

`SUPERSESSION KIND: replacement` at statement scope. **CHAIN: W2-C1 as displayed (all shared-key junctions) → E5 finding 2 → THEOREM W2-C1-CORR. TERMINAL: W2-C1-CORR, awaiting sol discharge (cert3).**

**The defect's exact location** is the proof's step “c/ρ_j = w·ξ^j by §3.3–3.4”: §3.3(c) computes the `ρ_j` but **does not prove they are geometric in j**, and off (C-coll) nothing forces it. E5's derivation makes this concrete: at `{0,1,2} ⊆ supp ψ_m` a scalar orbit forces `ρ₁² = ρ₀ρ₂`, “which HR-REC does not supply off (C-coll)”.

*Arithmetic audit (rule 22) of E5's geometricity criterion, recomputed.* `B_m = wψ_m(ξy)` means `[y^j]B_m = w·ψ_{m,j}·ξ^j` ✓, i.e. `a_j := [y^j]B_m/ψ_{m,j} = wξ^j` ✓ **exactly the displayed criterion** ✓. With `[y^j]B_m = (c/ρ_j)ψ_{m,j}` (from the proof) ✓, this is `c/ρ_j = wξ^j` ✓. Taking `j = 0,1,2`: `a_0 = w`, `a_1 = wξ`, `a_2 = wξ²` ⟹ `a_1² = a_0a_2` ✓ ⟹ `(c/ρ_1)² = (c/ρ_0)(c/ρ_2)` ⟹ **`ρ_1² = ρ_0ρ_2`** ✓ **exactly E5's display** ✓. **This compiler's independent recomputation confirms the certifier's derivation.**

**DERIVATION:** Quoted inline, with the superseded step named above.

**RESOLUTION TRACE:** statement 507–526 · the superseding display 1484–1531 (shard 2) · the surviving parts 1526–1529 (E5's consumer sweep: W2-C2(a), W2-ID1, HR-REC and the (C-coll) scalar display “survive unchanged”).

XREF: `docs/references/HigherNewton.tex` ✓ (tex 1285, Def-2.12).

**TEETH:** **probe F2-orbit 45/45 + F4 24/24 (foreign) + CK-XI 22 (own).** Disposition: executable regression on two instruments. **But note the gap E5 exposes: the machine checks that the displayed pair SATISFIES the orbit equations (CK-XI), which is exactly `.21`'s weakened claim — it does not check that a scalar orbit must exist.** So the instrument was measuring the right thing and the *theorem* over-read it.

---

### EFF.GRTW2.s1of2.26  [scope-record]  — §4.3, the unpinned-ℓ parametrization (review-owed) with the `[r2, P2]` revert

**CANONICAL STATEMENT:** verbatim, lines 530–573.

**FORM:** `###`-headed section body with a struck `[r1, F6]` bracket, a long `[r2, P2]` revert bracket, and an indented ASCII rescaling display.

> “The print fixes only ℓ_r h_r − ℓ′_r e_r = 1 (tex ~1291) — no
> representative is pinned. Shifting ℓ_{r−2} ↦ ℓ_{r−2} + k·e_{r−2}
> changes Def-`t(i)` by **t ↦ t − k·u_i** ~~[r1, F6] t ↦ t + k·u_i …~~
> **[r2, P2 — the r1 "fix" REVERTED as unfaithful to the named source;
> the r0 sign was CORRECT. Tex 1431's literal Def-`t(i)` is t_{r−1}(a)_i =
> (s_{r−1}(a) − ℓ_{r−1}·v_r(aφ_r^i))/e_{r−1} — the (s − ℓu)/e arrangement,
> with u_i = v_r(a_iφ_r^i) the polygon ordinate (tex 1373) and s_{r−1}(a)
> the attained initial abscissa, both ℓ-shift-INVARIANT — so
> ℓ_{r−2} ↦ ℓ_{r−2} + k·e_{r−2} gives t ↦ t − k·u_i directly …
> The r1 bracket's premise formula "(ℓu_i − s_i)/e" is a
> DIFFERENT print object — Prop-`construct`'s child twist exponent (tex
> 1201), near-negative of Def-`t(i)` — inherited from W2-L2's r0 naming
> parenthetical, which conflated the two opposite-signed exponents (split
> at §2.3 [r2, P2]); PE1's F6 computed with the conflated alias, r1
> implemented that finding, PE2 re-derived the sign at source. Recorded
> here so no future round re-flips it. The section's conclusions — orbit =
> characters ξ ∈ ⟨z_m^{h_m}⟩ with coupled w, reachability iff
> gcd(h_m, ord z_m) divides the ξ-exponent — quantify over all k ∈ ℤ and
> are sign-invariant under either convention, so nothing downstream moved
> in either round. The section stays inside its review-owed fence.]**,
> hence rescales the order-(r−1)
> residual coefficients on a side with initial point (s₀, u₀) by
> c_i ↦ z_{r−2}^{−k(u₀ − jh_{r−1})}·c_i:
>
>     R^{(ℓ+ke)}(X)(y) = z_{r−2}^{−k·u₀} · R^{(ℓ)}(X)( z_{r−2}^{k·h_{r−1}}·y ).
>
> So the ℓ-orbit acts on residuals exactly by the covariance characters
> with ξ ∈ ⟨z_m^{h_m}⟩ and coupled w = z_m^{−k·g_mγ_{m+1}}. The harness
> lift's character ξ = §3.4 is REACHABLE by an ℓ-shift iff
> z_m^{k·h_m} = ξ^{−1} is solvable in k, i.e. iff gcd(h_m, ord z_m) divides
> the ξ-exponent — true on many rows (e.g. T2A: h = 1, k = 2) but NOT a
> theorem of the class pin. Honest summary: **whether Def-2.12's "R ∼ ψ" is
> read strictly at a pinned ℓ or up to the ℓ-orbit is genuinely
> underdetermined by the print; under the strict pinned reading clause 1
> holds for the conjugate type t^ξ, under the orbit reading it holds for t
> itself exactly on the reachable rows.** This parametrization stands
> review-owed (probe fence inherited); nothing downstream consumes the
> orbit reading — clause 3 removes the ambiguity by transporting the type.”

**CONDITIONALITY:** **A REVIEW-OWED CONVENTION FENCE, and a REVERT.**
(a) **The revert:** r1 flipped a sign on PE1's F6; r2 reverted it at source with tex 1431 displayed, and **installed anti-re-flip records in two brackets** (`.13` and here). `SUPERSESSION KIND: replacement`. **CHAIN: r0 sign `t ↦ t − k·u_i` → `[r1, F6]` flip → `[r2, P2]` revert. TERMINAL: the r0 sign, restored.** **The note is explicit that nothing downstream moved in either round** — “the section's conclusions … quantify over all k ∈ ℤ and are sign-invariant under either convention”.
(b) **The fence:** “This parametrization stands review-owed (probe fence inherited)” — an **inherited** open item, and it is the fourth open surface listed at `.40` (“W2-OPEN-1 + W2-OPEN-2 + W2-BOX-1 + the §4.3 convention fence”).
(c) **E5's consumer sweep touches it once**: “Section 4.3's ℓ-orbit analysis applies **only after a scalar pair exists**” (1529, shard 2) — i.e. the fence now sits downstream of W2-C1-CORR's geometricity test. `SUPERSESSION KIND: scope-pin`.
(d) **“nothing downstream consumes the orbit reading”** is the containment claim, and it holds: clause 3 transports the type instead.

**DERIVATION:** Displayed inline; the rescaling identity follows from `Def-rescoeff` (tex 1447).

*Arithmetic audit (rule 22).* The shift's effect: `t = (s − ℓu_i)/e` with `s, u_i` both ℓ-shift-invariant ⟹ `ℓ ↦ ℓ + ke` gives `t ↦ (s − (ℓ+ke)u_i)/e = t − ku_i` ✓ **exactly the r0/r2 sign** ✓ **and this compiler's recomputation confirms the revert.** The near-negative object: `T = (ℓu − 𝔰)/e` (from `.13`) vs `t = (s − ℓu)/e` ✓ **opposite-signed** ✓ (equal up to the `s`-vs-`𝔰` distinction) ✓ **so the conflation was real.** Reachability: `z_m^{kh_m} = ξ^{−1}` solvable in `k` ⟺ `ξ^{−1} ∈ ⟨z_m^{h_m}⟩` ⟺ `ord(z_m)/gcd(h_m, ord z_m)` divides the order of `ξ`… the note's phrasing “gcd(h_m, ord z_m) divides the ξ-exponent” ✓ is the standard cyclic-group solvability criterion ✓.

**RESOLUTION TRACE:** statement 530–573 · the twin bracket 256–284 (`.13`) · the round record 1160–1175 (`.42`) · E5's scope-pin 1529 (shard 2).

XREF: `docs/references/HigherNewton.tex` ✓ (tex 1431, 1447, 1373, 1201, ~1291).

**TEETH:** NONE for the convention analysis — it is explicitly review-owed. **The revert itself was adjudicated at source by PE2**, which is a `transfer audit` disposition (rule 27): a hostile pass reading the cited print.

---

### EFF.GRTW2.s1of2.27  [definition]  — §5.1, the transported type

**CANONICAL STATEMENT:** verbatim, lines 581–604.

**FORM:** `###`-headed section body with a numbered two-step definition, an `[r1, F1]` honesty bracket inside step 1, and a closing sentence.

> “Fix a harness tower T in the class pin. Define the **transported type
> data** t^tw level by level, ascending. Start from T's own (e, h, ψ)
> ledger. At each junction level m+1 = 2, 3, …, working in the CURRENT
> (already partially transported) classifier chamber:
>
> 1. build the print chain on the current ledger and evaluate the Def-2.12
>    criterion on the harness lift Φ_{m+1}^har; record the junction pair
>    (ξ, w) with R(Φ^har)(y) = w·ψ^cur(ξy); **[r1, F1: above the chamber's
>    first ξ ≠ 1 junction the EXISTENCE of this pair is not §3-derived —
>    (C-coll) is NOT tracked through the transport, and §3.4's scalar warrant
>    stops at the first twist. The recording itself is a per-instance exact
>    computation (the finite orbit scan), well defined whenever the pair
>    exists; existence at every roster junction is the machine record TW-ADM
>    44/44, and existence in general is part of the open box W2-OPEN-2
>    (§5.2).]**
> 2. if ξ ≠ 1, replace the current level-m modulus by its ξ-conjugate
>    ψ^tw(y) := ξ^{−g_m}·ψ^cur(ξ·y) (monic, irreducible, ψ^tw(0) ≠ 0, same
>    (e, h, g) read data — the class the harness lift ACTUALLY represents),
>    and re-coordinate every higher-level residual datum through the letter
>    identification z_old = ξ·z_new (coordinate rescale (a_i) ↦ (a_i·ξ^i)
>    at the K_{m+1}-layer of every nested tuple).
>
> The w of the pair is recorded but not consumed by the transport (classes
> are scalar-free); it is the value-layer bookkeeping unit of §3.4.”

**CONDITIONALITY:**
(a) **Step 1's `[r1, F1]` bracket is the transport's own honesty item**: above the first twist the pair's EXISTENCE is not §3-derived, and existence in general is part of W2-OPEN-2. **So the transport is defined conditionally on the box it exists to motivate.**
(b) **Step 1 pins no selection rule** — “just says "record the junction pair"” (`.31`'s r3 bracket) — and that is exactly what PE3's counter-instance exploits (`.32`). **A selection rule was deliberately NOT added at r3**: “The alternative cure (pin the ξ = 1 preference into §5.1) is NOT taken: the sealed scan is byte-frozen and implements enumeration order, so a pinned preference would misdescribe the note's own machine bracket off-roster” (1242–1245, `.43`). **That is a refusal to make the text prettier than the instrument.**
(c) **E5's consumer sweep touches step 2**: “At a general non-collapse first twist, §5.1's ξ-transport is **conditional on the geometricity test**” (1528, shard 2). `SUPERSESSION KIND: scope-pin`.

**DERIVATION:** Definition; step 2's `ψ^tw` is monic irreducible with the same read data because conjugation by a unit preserves those.

*Arithmetic audit (rule 22).* `ψ^tw(y) := ξ^{−g_m}ψ^cur(ξy)`: if `ψ^cur = y^{g_m} + …`, then `ψ^cur(ξy) = ξ^{g_m}y^{g_m} + …` ✓ so `ξ^{−g_m}ψ^cur(ξy)` is monic ✓. `ψ^tw(0) = ξ^{−g_m}ψ^cur(0) ≠ 0` ✓. Irreducible ✓ (a linear substitution). Same `(e,h,g)` ✓ (degree preserved). **The re-coordination `(a_i) ↦ (a_iξ^i)` is the dual of `z_old = ξz_new`** ✓ (substituting `z_old = ξz_new` into `Σa_iz_old^i` gives `Σa_iξ^iz_new^i`) ✓ **exact.**

**RESOLUTION TRACE:** statement 581–604 · the mechanism 606–615 (`.28`) · the selection-rule refusal 1242–1245 (`.43`) · E5's scope-pin 1528 (shard 2).

**TEETH:** **TW-ADM 44/44** is the existence record; the transport's own correctness is measured by TW-RATIO/TW-STRICT (`.37`).

---

### EFF.GRTW2.s1of2.28  [scope-record]  — §5.1's Mechanism (why the transport is forced)

**CANONICAL STATEMENT:** verbatim, lines 606–615.

**FORM:** bold-headed paragraph.

> “**Mechanism (why this is forced — the probe's finding (4) restated as
> mathematics).** After a twisted junction the same ψ-bytes denote DIFFERENT
> residue classes in the two chains: the classifier's letter and the
> harness's letter differ by the character ξ. Without step 2 the classifier
> chain continued on raw ψ-bytes is a valid GMN type chain — of the
> CONJUGATE type — and above the twist the two keys differ at key weight
> (v(φ^cls − Φ^har) = v(key)): different induced valuations, WEIGHT/SUPPORT
> splits, and the value layer breaks (probe F2: 6, F3: 96).”

**CONDITIONALITY:** **This paragraph is the note's causal account and it is confirmed twice from outside.**
(i) **The probe's numbers are the evidence**: F2's 6 weight/support splits ✓ (the same 6 as `.15`, `.24`) and F3's 96 value-layer violations ✓ (the same 96 as `.04`, `.35`).
(ii) **The clause “different induced valuations” is SUPERSEDED in W2-C3's wording** (E5 finding 4, 1568–1594, shard 2) — but *not here*: E5 supersedes W2-C3's claim that the transported chains have the *same* induced valuation data; this paragraph's claim that the *untransported* chains have *different* ones is the same phenomenon and survives. **In fact E5's own derivation uses it**: “W2-OPEN-2's route-(3) obstruction now agrees with W2-C3” (1594). Recorded so a merge does not over-apply the supersession.
(iii) `v(φ^cls − Φ^har) = v(key)` is exactly the quantity route (3) of the derivability adjudication turns on (`.34`).

**DERIVATION:** Restatement of the probe's finding (4) as mathematics.

**RESOLUTION TRACE:** statement 606–615 · the probe numbers 890–892 (`.35`), 502–503 (`.24`) · route (3) 863–870 (`.34`) · E5's finding 4 1562–1594 (shard 2).

**TEETH:** **probe F2: 6 and F3: 96** — foreign-instrument evidence, and the 96 is the number the transport turns GREEN (`.35`).

---

### EFF.GRTW2.s1of2.29  [theorem]  — THEOREM W2-C3 (clause 3, chain level)

**CANONICAL STATEMENT:** verbatim, lines 617–649 (the `###` heading with its `[r1, F1]` re-scope tag, the three clauses, and the proof sketch with its machine bracket).

**FORM:** `###`-heading carrying a bracketed re-scope + three lettered clauses + a proof sketch.

> “### 5.2 THEOREM W2-C3 (chain level; attempt grade given §3–§4) **[r1, F1: RE-SCOPED — proved to each chamber's first twist, MEASURED above it; grade split and the open bridging box W2-OPEN-2 below]**
>
> On the transported ledger, at every level m+1:
>
>   (i) the junction is shared-perimeter-type: the two keys agree in
>       weights and support (one-sided, same polygon; no WEIGHT/SUPPORT
>       degeneration at any level of any tower);
>   (ii) Φ_{m+1}^har is a **STRICT** (pinned-ℓ) Def-2.12 representative of
>       the transported type t^tw at level m+1 — R(Φ^har) ∼ ψ^tw exactly,
>       no orbit needed;
>   (iii) the transported print key φ^tw and Φ^har represent THE SAME type
>       (both strict representatives of t^tw; equal (e,f) by the PARI leg)
>       — the probe's conjugate-type split is cured. This is the precise
>       cash-out of "the twisted chains are MacLane-equivalent level by
>       level": equivalence as type data (same residual classes, same
>       induced valuation data), NOT byte-equality of keys (junction unit
>       ratios persist and are the §3.4 characters of the transported
>       chamber).
>
> *Proof sketch at attempt grade.* (ii) is clause 1 applied in the
> transported chamber: R(Φ^har) = w·ψ^cur(ξy) = w·ξ^{g_m}·ψ^tw(y) — a scalar
> multiple of the new modulus, i.e. strict ∼. (i): with the classes matched,
> both builders place slots on the same one-sided polygon (W2-C1a for the
> harness side, Prop-`construct`/Thm-`phir` for the print side, on the same
> (e, h, g, γ) data — transport changes no weights). (iii) from (ii). The
> induction is over junctions ascending; the re-coordination step is an
> isomorphism of the residual ledger, so each chamber stays in the class
> pin. ∎ [Machine: TW-RATIO 44/44 junction comparisons with NO weight/
> support mismatch (the probe's 6 such rows all cure); TW-ADM 44/44;
> TW-STRICT 44/44 — strict unit at EVERY level of EVERY tower; TW-PARI
> 12/12 transported top lifts irreducible with (e,f) = (∏e_j, d₀∏g_j);
> TW-QO 7/7 on the extracted concrete shapes; MT-TW teeth: a garbled
> character (ξ·z₁) is caught on both designated rows.]”

**CONDITIONALITY:** **Two independent supersessions, one in range and one out.**
(a) **`[r1, F1]` re-scopes the grade**: proved to each chamber's first twist (38/44), MEASURED above (6/44). The full re-scope block is `.30`. `SUPERSESSION KIND: scope-pin`.
(b) **Clause (iii)'s equivalence wording is SUPERSEDED by E5 finding 4** (1568–1594, shard 2):

> “In W2-C3, the phrase “equivalence as type data (same residual classes, same induced valuation data)” and the subsequent description “MacLane-equivalent level by level” are **SUPERSEDED** by:
> > **ledger-equivalent at the displayed scope:** … No equality of the augmented valuation functions induced by the two different key representatives is claimed.”

with (iii) re-displayed as “a residual/type-ledger assertion, not an assertion that the two key augmentations define the same valuation on O[x]”. `SUPERSESSION KIND: replacement`. **CHAIN: (iii) as displayed → E5 finding 4's ledger-equivalence re-display. TERMINAL: the re-display, awaiting sol discharge (cert3).**
**The defect was self-inflicted and the note already contained the refutation**: route (3) of its own derivability adjudication (`.34`) proves that equal augmented valuations are unavailable — “the recorded data warrant only ≥ key weight … strictly BELOW γ, so the two chains' inductive valuations may genuinely differ”. **E5's finding is that (iii) claimed what §5.2's own route (3) denies.** The finding's own words: “The note itself proves that equality of augmented valuation functions is unavailable” (1564).
(c) **Clauses (i) and (ii) survive**: “W2-C3(i)'s polygon statement and W2-C3(ii)'s strict-residual statement do not use equality of valuation functions and survive at their separately corrected grades” (1594, shard 2) ✓.

**DERIVATION:** Quoted inline; (ii) is clause 1 in the transported chamber, and **that application is exactly what the `[r1, F1]` block fences** (`.30`).

*Arithmetic audit (rule 22) of (ii)'s one-line computation.* `R(Φ^har) = w·ψ^cur(ξy)`; substituting `ψ^tw(y) = ξ^{−g_m}ψ^cur(ξy)` ⟹ `ψ^cur(ξy) = ξ^{g_m}ψ^tw(y)` ✓ so `R(Φ^har) = w·ξ^{g_m}·ψ^tw(y)` ✓ **a scalar multiple** ✓ **exactly as displayed** ✓.
*E5's counter-derivation.* With `Φ = φ + D` and `μ(D) = μ(φ) < γ`: the `φ`-augmentation gives `μ_{φ,γ}(Φ) = min{γ, μ(D)} = μ(D) < γ` ✓, while the `Φ`-augmentation gives `μ_{Φ,γ}(Φ) = γ` ✓ **different** ✓ **so matching ledgers do not give equal valuations** ✓ **this compiler's recomputation confirms the certifier's derivation.**

**RESOLUTION TRACE:** statement 617–649 · the re-scope block 651–705 (`.30`) · route (3) 863–870 (`.34`) · E5's finding 4 1562–1594 (shard 2).

**TEETH:** **TW-RATIO 44/44 + TW-ADM 44/44 + TW-STRICT 44/44 + TW-PARI 12/12 + TW-QO 7/7 + MT-TW 2/2.** **Disposition: executable regression on five families plus a fired tooth.** **BUT the note itself reclassifies one**: “TW-STRICT is SAME-ADJACENT evidence given TW-ADM — once the orbit pair exists, the §5.1 conjugation makes strictness an identity — so the bracket above reads honestly as TW-ADM 44/44 plus a construction-forced strictness confirmation, **NOT two independent 44/44 legs**” (`.30`(b)). **That is a self-administered evidence-class downgrade** and it is the model of rule 20's disposition vocabulary.

---

### EFF.GRTW2.s1of2.30  [changes-record]  — the `[r1, F1]` HONEST RE-SCOPE block

**CANONICAL STATEMENT:** verbatim, lines 651–705 (the whole block, with its `[r2, P1]`, `[r3]` and `[r4, PE4 o-b]` nested brackets).

**FORM:** bold-headed bracketed block with strike-through, three nested round-brackets, a per-junction-level census, and two lettered honesty items.

> “**[r1, F1 — THE HONEST RE-SCOPE (PE1's major gap, cured by re-fencing; no
> statement above is changed, the GRADE is).** The sketch applies clause 1
> (THEOREM W2-C1) inside the transported chamber; clause 1 is proved AT A
> SHARED-KEY JUNCTION (§1.3: byte-equality of all keys below). In a
> transported chamber this warrant holds up to and including the chamber's
> FIRST ξ ≠ 1 junction r₀ — junctions below r₀ recorded ξ = 1, so no
> conjugation fired ~~and every key below r₀ is byte-equal to the harness key;
> the criterion AT r₀ is therefore evaluated over byte-shared lower keys and
> clauses 1–2 apply~~ **[r2, P1] — and the further step "recorded ξ = 1 ⟹
> byte-equal" (what makes the criterion at-or-below r₀ evaluate over
> byte-shared lower keys, so that clauses 1–2 apply) is NOT definitional: the
> recorded pair sees only the top-layer reads, while the byte law (§3.4 rk. 3)
> quantifies over EVERY node value of the recursion tree — a read-invisible
> deeper-node divergence (the §3.5 invisible-twist genre one layer down)
> would be byte-RED with recorded ξ = 1. That step is PROVED at m = 1
> (LEMMA W2-ID1 below) and at m ≥ 2 is exactly W2-OPEN-2's premise sub-clause
> (OPEN-2a); on the committed roster it is instance-exact — recorded ξ ≠ 1 ⟺
> byte-RED at 22/22 walked junctions, and every junction below every
> chamber's r₀ is byte-GREEN (PE2's recomputation from the committed JSON)**.
> ABOVE r₀ the transported print keys and the harness
> keys are byte-DIFFERENT **[r4, PE4 o-b: roster instance (all 6 above-r₀
> SKIP junctions byte-RED — PE2/PE4 recomputation); in general UNPROVED —
> the same converse+persistence content flagged inside W2-OPEN-2's premise
> [r3]; this block's conclusion consumes only the ABSENCE of the byte-share
> warrant, which holds either way]** (the persistent unit ratios of (iii)'s
> own wording), every higher junction sits OFF the §3 perimeter, and clauses
> 1–2 AS PROVED do not apply there. Honest grade, per junction-level of the
> roster's 44 (per-tower first-twist census recomputed this round from the
> committed ξ-ledger): **PROVED at attempt grade given §3–§4 at the 38
> junction-levels at-or-below each chamber's first twist; MEASURED at the 6
> junction-levels above a first twist** — T3A/T3C/T3D/T3E at r = 4 and I4C
> at r = 4, 5, exactly the interior-twist geography the transport exists to
> cure — where (i)–(iii) hold conditionally on the open bridging lemma
> W2-OPEN-2 displayed below. **[r2, P1 — the proved-scope sentence, scoped
> to what carries it: at the proved-scope junction-levels whose strictly-
> below junctions all sit at m ≤ 1 (GMN r ≤ 4; TH-BASE + LEMMA W2-ID1 cover
> the below-chain), the byte-share warrant is fully §3-derived; at the
> proved-scope junction-levels with an m ≥ 2 recorded-trivial junction below
> — on this roster exactly I4A r = 5 and I4B r₀ = 5 (read off the per-chamber
> first-twist census this round) — the warrant is INSTANCE EVIDENCE (every
> below-r₀ junction byte-GREEN, 22/22 walked equivalence — PE2's
> recomputation) riding (OPEN-2a). The 38/44 census stands as exactly that:
> 36 junction-levels fully warranted + 2 instance-warranted, not a uniform
> theorem-grade 38.]** (The final-chamber scans stand in for the
> mid-transport states: later junctions never touch the data a lower
> junction's residual depends on — PE1 §A.9 verified this index-by-index in
> `transport_leg`.) Two companion honesty items: (a) whether (C-coll)
> survives into each transported chamber is NOT tracked, so above r₀ the
> recorded (ξ, w) is the orbit scan's exact per-instance value, not the
> §3.4 scalar formula (§5.1 step 1's [r1] bracket); (b) evidence-class
> reclassification (PE1 §C.5): **TW-STRICT is SAME-ADJACENT evidence given
> TW-ADM** — once the orbit pair exists, the §5.1 conjugation makes
> strictness an identity — so the bracket above reads honestly as TW-ADM
> 44/44 plus a construction-forced strictness confirmation, NOT two
> independent 44/44 legs.]**”

**CONDITIONALITY:** **This block is the arc's centre of gravity and its state at HEAD differs from its displayed state in two ways.**
(a) **The `[r2, P1]` census “36 fully warranted + 2 instance-warranted, not a uniform theorem-grade 38” is UPGRADED out of range**: the Σ-LAW supplier proves (OPEN-2a)'s forward direction at every `m ≥ 2` (annexes 2026-08-08 and #3, shard 2), so the 2 instance-warranted entries gain a theorem. **Then E5 re-partitions to 37 + 1 + 6** (1527, shard 2) — I4A r = 5 becomes derived; **I4B r = 5 stays individually confirmed for a DIFFERENT reason** (its scalar orbit is a boundary instance off (C-coll), `.23`). `SUPERSESSION KIND: license` then `counter re-reading`. **TERMINAL: 37 + 1 + 6.**
(b) **The `[r4, PE4 o-b]` qualifier on “ABOVE r₀ … byte-DIFFERENT”** converts a universal into a roster instance plus an explicit UNPROVED, **and states why the block survives it**: “this block's conclusion consumes only the ABSENCE of the byte-share warrant, which holds either way”. `SUPERSESSION KIND: scope-pin`.
(c) **Honesty item (b) — the TW-STRICT reclassification — is a self-administered evidence downgrade** and is repeated in the §6.1 table (`.37`).
(d) **Honesty item (a)** is why the recorded pair above `r₀` is a scan value, not a formula value (`.27`).

*Arithmetic audit (rule 22).* The 6 measured junction-levels are enumerated: “T3A/T3C/T3D/T3E at r = 4 and I4C at r = 4, 5” ✓ `4 + 2 = 6` ✓ **exact enumeration matching the count everywhere else** ✓. The 2 instance-warranted: “I4A r = 5 and I4B r₀ = 5” ✓. `36 + 2 + 6 = 44` ✓. PE3's independent decomposition `36 = 16 + 16 + 4` ✓ (`.05`). **All four decompositions of 44 agree.**

**DERIVATION:** A grade re-fencing, not new mathematics — “no statement above is changed, the GRADE is”.

**RESOLUTION TRACE:** statement 651–705 · W2-ID1 707–739 (`.31`) · the box 781–847 (`.33`) · out-of-range upgrades 1376–1440, 1527 (shard 2).

**TEETH:** **TW-ADM 44/44 (with TW-STRICT reclassified SAME-adjacent), plus PE1 §A.9's index-by-index verification that final-chamber scans stand in for mid-transport states.** Disposition: executable regression + a hostile pass's structural check.

---

### EFF.GRTW2.s1of2.31  [lemma]  — LEMMA W2-ID1 (recorded-ξ triviality ⟹ byte-equality at m = 1)

**CANONICAL STATEMENT:** verbatim, lines 707–739.

**FORM:** bold-headed lemma with a proof and a struck-and-replaced “Consequently” sentence.

> “**LEMMA W2-ID1 (recorded-ξ triviality ⟹ byte-equality at m = 1). [r2, P1]**
> At an m = 1 junction (GMN r = 3, the first junction of any chamber — lower
> keys byte-shared unconditionally by TH-BASE, so no transport has fired
> below and ψ^cur = ψ₁), if the §5.1 step-1 recorded pair has ξ = 1, then the
> junction is byte-equal. *Proof (from W2-C2(a) + §3.4).* At m = 1 the §3.4
> display is unconditional: R₂(Φ₂^har)(y) = ψ₁(ξ_f·y) with the formula pair
> (ξ_f, w_f) = (z₁^{−e₁A₁}, 1). A recorded pair (1, w) means
> R₂(Φ₂^har) = w·ψ₁(y); equating the two at j = 0 (ψ₁(0) ≠ 0, class pin)
> forces w = 1, so ψ₁(ξ_f·y) = ψ₁(y), i.e. ξ_f^j = 1 for every
> j ∈ supp(ψ₁) — including the monic top j = g₁. Hence on supp(ψ₁) ∩ [0, g₁):
> c·z₁^{A₁e₁·j} = ξ_f^{g₁}·ξ_f^{−j} = ξ_f^{g₁−j} = 1 (using c = c₁^{e₁g₁} =
> ξ_f^{g₁} and z₁^{A₁e₁j} = ξ_f^{−j}) — exactly §3.4 rk. 3's m = 1
> byte-equality law, so the junction is byte-equal. ∎ ~~Consequently the
> identification "first recorded ξ ≠ 1 junction = first byte-divergence" is
> PROVED for every junction whose strictly-below junctions all sit at m ≤ 1
> (ascending: r = 2 by TH-BASE, r = 3 by this lemma); at m ≥ 2 it is OPEN —
> the premise sub-clause (OPEN-2a) of the box below.~~ **[r3, PE3-P1 —
> scoped to the proved direction:** consequently, at every junction whose
> strictly-below junctions all sit at m ≤ 1 …, NO byte-divergence occurs
> strictly below the first recorded ξ ≠ 1 junction — the HALF of the
> identification … that every consuming surface of this note uses …;
> at m ≥ 2 this same forward direction is the premise sub-clause (OPEN-2a) of
> the box below; the CONVERSE — recorded ξ ≠ 1 ⟹ byte-RED — is UNPROVED at
> every m including m = 1: it is a property of the recorded-pair SELECTION
> RULE, which this note never pins …, and it is FALSE under the sealed scan's
> actual selection — the counter-instance recorded below.**]** [Machine:
> instance-exact on the roster — recorded ξ ≠ 1 ⟺ byte-RED at all 22 walked
> junctions, of which the m = 1 slice is the 16 r = 3 rows (PE2 recomputation).]”

**CONDITIONALITY:** **The lemma is PROVED and is in the accepted enumeration** — F3 lists “LEMMA W2-ID1 (**forward direction**, with the converse's counter-instance displayed)” (1347–1348, shard 2). **Its “Consequently” sentence was two-sided and is SCOPED to the forward direction at r3.** `SUPERSESSION KIND: replacement`. **CHAIN: r2's two-sided consequence → `[r3, PE3-P1]`'s forward-only scoping. TERMINAL: forward only, at every m.**
**Out of range the forward direction is EXTENDED to `m ≥ 2`**: THEOREM OPEN-2a-Σ, on the accepted Σ-LAW supplier, gives “recorded ξ = 1 ⟹ byte-equal **under every selection rule**, at attempt grade” (1429–1432, shard 2). **So W2-ID1's `m = 1` restriction is now historical** — the same statement holds at every `m`. `SUPERSESSION KIND: license`. **The converse remains UNPROVED at every m** (E5 finding 1's correct-current-status paragraph, 1474, shard 2).

**DERIVATION:** Quoted inline.

*Arithmetic audit (rule 22), every step recomputed.*
- **The formula pair at m = 1.** `(ξ_f, w_f) = (z₁^{−e₁A₁}, 1)` ✓ from `.19` ✓.
- **`w = 1` from j = 0.** Equating `w·ψ₁(y)` with `ψ₁(ξ_f y)` at `y^0`: `w·ψ_{1,0} = ψ_{1,0}` ✓ and `ψ_{1,0} = ψ₁(0) ≠ 0` ✓ ⟹ `w = 1` ✓.
- **`ξ_f^j = 1` on supp.** `ψ₁(ξ_f y) = ψ₁(y)` coefficientwise gives `ψ_{1,j}ξ_f^j = ψ_{1,j}` ✓ ⟹ `ξ_f^j = 1` for `j ∈ supp` ✓ **including the monic top `j = g₁`** ✓.
- **The byte law.** `c = c₁^{e₁g₁}` (from `.10`) and `ξ_f = c₁^{e₁}` (from `.19`) ⟹ `c = ξ_f^{g₁}` ✓. And `z₁^{A₁e₁j} = (z₁^{−e₁A₁})^{−j} = ξ_f^{−j}` ✓. So `c·z₁^{A₁e₁j} = ξ_f^{g₁−j}` ✓, and `ξ_f^{g₁} = 1`, `ξ_f^{j} = 1` on supp ⟹ `ξ_f^{g₁−j} = 1` ✓ **exactly §3.4 rk. 3's m = 1 byte law** ✓ (`.22`).
**Every step reproduces. The lemma is correct as displayed.**

**RESOLUTION TRACE:** statement 707–739 · the counter-instance 741–779 (`.32`) · the box 781–847 (`.33`) · out-of-range extension 1376–1440 (shard 2).

**TEETH:** **Instance-exact on the roster: recorded ξ ≠ 1 ⟺ byte-RED at 22/22, the m = 1 slice being 16 r = 3 rows.** **And PE4's exhaustive leg**: “W2-ID1's forward direction **29,223 grid points / 0 violations** incl. g ∈ {3,4}” (`.03`) — **the forward direction is verified far off-roster, including at the g ≥ 3 geography where the converse fails.** Disposition: executable regression, exhaustive; the forward/converse asymmetry is measured, not asserted.

---

### EFF.GRTW2.s1of2.32  [run-record]  — the `[r3]` CONVERSE'S HONEST BOUNDARY (PE3's counter-instance)

**CANONICAL STATEMENT:** verbatim, lines 741–779.

**FORM:** bold-headed block quoting PE3's construction verbatim, with an `[r4, PE4 o-c]` line-figure correction and a roster-invisibility analysis.

> “**[r3] THE CONVERSE'S HONEST BOUNDARY — PE3's class-pin counter-instance
> at m = 1, recorded here next to the lemma (`GRTW2_passPE3_report.md` §P1;
> quoted, since it is the exact reason the converse direction is not
> claimed).** The sealed `orbit_scan` (grt_w2_checks.py lines ~~135–164~~
> **135–163 [r4, PE4 o-c: `return out` at 163; 164 is the trailing blank —
> re-verified at the sealed source this round]**)
> records the FIRST satisfying ξ in `F.elems()` enumeration order, and for
> extension residue fields that order yields the generator BEFORE 1
> (`Ext.elems` = `itertools.product(base.elems(), repeat=g)`,
> iterlawn_pe_reimpl.py line 220: for F₄, (0,1) = ζ precedes (1,0) = 1).
> PE3's construction, quoted: "Tower: ℤ₂ (or F₂[[t]]), d₀ = 1, Φ₀ = x; read
> 0 = (e₀,h₀,g₀) = (1,1,2) with ψ₀ = y²+y+1 (K₁ = F₄, ζ := z₁); read 1 =
> (2,1,3) with ψ₁ = y³ + ζ (monic, irreducible — x³ = 1 for all x ∈ F₄* so
> no root, and a cubic factorization needs a root — ψ₁(0) = ζ ≠ 0; in the
> [ILN]† S0.1 pin). At the m = 1 junction: e₀ = 1 ⟹ ℓ₀ = 0 ⟹ A₁ = 0 ⟹
> c = 1 and the §3.4 rk. 3 byte law holds trivially — the junction is
> byte-equal, formula pair (1,1). But supp(ψ₁) = {0,3} and ξ³ = 1 for EVERY
> ξ ∈ F₄*, so all three units satisfy the orbit equations, and the sealed
> scan's enumeration records (ζ, 1) — recorded ξ ≠ 1 at a byte-equal
> junction." For that chamber "first recorded ξ ≠ 1 junction = first
> byte-divergence" is FALSE (its ledger r₀ = 3 with no byte-divergence
> anywhere), and the transport fires a spurious conjugation — ψ^tw = ψ since
> ζ stabilizes the support, but the §5.1 step-2 re-coordination
> (a_i) ↦ (a_i·ζ^i) of higher data is nontrivial. Machine-probed by PE3 with
> the scan's ξ-loop semantics copied verbatim (`/tmp/w2_pe3_fresh.py`).
> ROSTER-INVISIBLE: the Tower builder implements only g ∈ {1,2} ("only g in
> {1,2} implemented", iterlawn_pe_reimpl.py line 311), and for g_m ≤ 2 no
> support-stabilizing unit with zero constant coefficient exists (g = 1:
> stabilizer trivial; g = 2 sparse: stabilizer {±1}, nonzero constant term),
> so on the committed roster enumeration order coincides with a ξ = 1
> preference everywhere — consistent with the 22/22 census; the failure
> needs g_m ≥ 3. Under a trivial-preferring selection rule the converse
> WOULD hold at every m (byte-equal ⟹ the trivial pair (1, c) satisfies the
> orbit equations by Thm-`phir` ⟹ recorded ξ = 1 under the preference); this
> note pins no such rule and the sealed runner is BYTE-FROZEN, so the
> converse stays UNCLAIMED — any future round pinning the ξ = 1 preference
> must also disclose that the sealed scan realizes it only where no
> nontrivial support-stabilizing unit precedes 1 in enumeration order (on
> this roster: everywhere; off-roster: not guaranteed, as above).”

**CONDITIONALITY:** **A counter-instance to the note's own converse, constructed by a hostile pass, recorded next to the lemma it bounds, with the roster-invisibility PROVED rather than assumed.** Four things make this the sweep's model disclosure:
(i) **The defect is in the INSTRUMENT's selection rule, not the mathematics** — `F.elems()` enumeration order.
(ii) **The roster-invisibility is derived**: `g ≤ 2` ⟹ no support-stabilizing unit with zero constant coefficient ⟹ enumeration order coincides with a ξ = 1 preference ✓, and “the failure needs `g_m ≥ 3`”.
(iii) **The alternative cure is named and refused**: pinning a ξ = 1 preference would “misdescribe the note's own machine bracket off-roster”, and the runner is frozen (`.43`).
(iv) **PE4 then mapped the failure exhaustively**: “spurious set exactly {(F₄, g = 3, supp {0,3}), (F₉, g = 4, supp {0,4})}, ZERO at g ≤ 2 (roster-invisibility exhaustive)” (`.03`) — **the disclosure condition confirmed as the EXACT characterization.**
**Out of range the boundary EXTENDS to `m ≥ 2` as predicted**: the OPEN2ATTACK annex records “16 constructed spurious-selection witnesses (F₉ y⁴+c recorded ord-4; F₆₄ y³+c recorded ord-3 …)” (1396–1400, shard 2) ✓ — **the genre generalizes exactly as the note said it would.**

**DERIVATION:** A construction, verified four ways (PE3's probe, PE4's from-scratch re-derivation, PE4's exhaustive map, and the OPEN2ATTACK extension).

*Arithmetic audit (rule 22), every claim in the construction recomputed.*
- **`ψ₀ = y²+y+1` over F₂** ⟹ irreducible ✓ (no root in F₂) ⟹ `K₁ = F₄` ✓, `ζ := z₁` a generator ✓.
- **`ψ₁ = y³ + ζ` over F₄ irreducible?** A cubic is irreducible iff it has no root. `x³ = 1` for all `x ∈ F₄^×` ✓ (the group has order 3) ✓, so `x³ + ζ = 1 + ζ ≠ 0` for `x ≠ 0` ✓, and `x = 0` gives `ζ ≠ 0` ✓ ⟹ **no root ⟹ irreducible** ✓ **exactly the displayed argument** ✓. `ψ₁(0) = ζ ≠ 0` ✓ (class pin satisfied).
- **`e₀ = 1 ⟹ ℓ₀ = 0`** ✓ (`.08`) ⟹ `A₁ = ℓ₀g₀γ₁ = 0` ✓ ⟹ `c = c₁^{e₁g₁} = z₁^{−A₁e₁g₁} = 1` ✓ ⟹ **the byte law `c·z₁^{A₁e₁j} = 1` holds trivially** ✓ **byte-equal** ✓, formula pair `(1,1)` ✓ (`ξ = c₁^{e₁} = 1` ✓).
- **The stabilizer.** `supp(ψ₁) = {0,3}` ✓ (`y³ + ζ`). The orbit equations need `ξ^j` constant on the support, i.e. `ξ^0 = ξ^3`, i.e. `ξ³ = 1` ✓ — **and `ξ³ = 1` for EVERY `ξ ∈ F₄^×`** ✓ (order 3) ✓ ⟹ **all three units satisfy them** ✓ **exact.**
- **Roster-invisibility.** `g = 1`: `supp ⊆ {0,1}`, stabilizer needs `ξ⁰ = ξ¹` ⟹ `ξ = 1` ✓ trivial. `g = 2` sparse (`supp = {0,2}`): `ξ² = 1` ⟹ `ξ ∈ {±1}` ✓, and the note's criterion is “no support-stabilizing unit **with zero constant coefficient**” — `supp` containing 0 means the constant term is nonzero ✓, so the sparse `g = 2` case has `ξ = −1` available but the *constant coefficient is nonzero*, which is what blocks the enumeration precedence… **the note's phrasing here is compressed and this compiler cannot fully reconstruct the “zero constant coefficient” criterion from the displayed text.** Recorded as source defect 3: **the roster-invisibility argument's `g = 2` half is stated too tersely to check.** PE4's exhaustive map (`ZERO at g ≤ 2`) supplies the fact independently ✓.
**Everything except the `g = 2` sub-argument reproduces exactly, and PE4's exhaustive leg covers that gap by measurement.**

**RESOLUTION TRACE:** statement 741–779 · the lemma 707–739 (`.31`) · PE4's exhaustive map 54–57 (`.03`) · the m ≥ 2 extension 1396–1400 (shard 2).

ARTIFACT: `verification/openmath/grt_w2_checks.py` ✓ (lines 135–163, the `orbit_scan`) · `iterlawn_pe_reimpl.py` — **verified present** at `verification/openmath/`.
**UNPINNED:** `/tmp/w2_pe3_fresh.py` — a temp-file path; **not present and not expected to be**. Recorded per rule 23 as an UNPINNED run.

**TEETH:** **A counter-instance that FIRED against the note's own converse, verified by four independent routes.** Disposition: `decorrelated-model audit` (rule 27) for the finding; executable regression (PE4's 33,408 checks) for the exact characterization.

---

### EFF.GRTW2.s1of2.33  [scope-record]  — W2-OPEN-2 and its premise sub-clause (OPEN-2a)

**CANONICAL STATEMENT:** verbatim, lines 781–847 (the box, its `[r2, P3]` index fix, its `[r3]`/`[r4]` converse flags, (OPEN-2a) with its `[r4, PE4-P1]` gloss scoping, the CLAIM (a)/(b), the equivalent sufficient form, and the alternative discharge route).

**FORM:** bold-headed box with four nested bracket layers, an indented CLAIM display, and two closing paragraphs.

> “**W2-OPEN-2 (the chain-level bridging lemma — this note's own open box at
> the chain level; OPEN, instance-confirmed).** In a transported chamber
> with first recorded ξ ≠ 1 junction r₀, consider any junction at GMN order
> r > r₀ (harness level m+1 = r−1). The chamber's keys φ_q^tw are byte-equal
> to the harness keys ~~Φ_q~~ **Φ_{q−1} [r2, P3 — the note's own §1.2
> dictionary (φ_i^GMN = Φ_{i−1}^har) pairs the order-q key with the harness
> Φ_{q−1}; as previously written the comparanda had different degrees]** for
> q < r₀ and byte-DIFFERENT for r₀ ≤ q < r **[r3, PE3-P1: this byte-DIFFERENT
> clause is the CONVERSE direction of the identification (recorded ξ ≠ 1 ⟹
> byte-RED) — unproved at every m and FALSE under the sealed scan's selection
> off-roster … **[r4, PE4 o-e: that chamber's top junction IS its r₀ — 2 reads,
> so this box's range r > r₀ is empty there; instantiating THIS clause's
> falsity strictly means appending any third read, immediate since appending
> a read leaves all lower junction data unchanged and the q = r₀ keys stay
> byte-equal as recorded]**; it stands
> here as part of this OPEN box's premise, alongside (OPEN-2a), not as a
> proved fact]** —
> same weights, same one-sided support, both strict Def-2.12 representatives
> of the same transported type, differing by persistent on-line unit ratios.
> **[r2, P1] (OPEN-2a) — the premise's own open sub-clause … **[r4, PE4-P1 —
> the opening gloss scoped to the proved direction …: (the junction
> identification's FORWARD direction at m ≥ 2): the byte-equality below r₀
> just asserted IS that identification's forward half (recorded ξ = 1 ⟹
> byte-equal …), which this note does NOT prove at m ≥ 2; the CONVERSE is
> UNPROVED at every m including m = 1, PE3's counter-instance recorded at
> LEMMA W2-ID1 above.]** Sub-clause statement: at a junction at level m+1
> with m ≥ 2, keys below byte-shared and recorded ξ = 1, the raw print key is
> byte-equal to the harness key. Status: PROVED at m = 1 (LEMMA W2-ID1
> above); OPEN at m ≥ 2 … instance-exact on the committed roster (22/22
> walked junctions; every below-r₀ junction byte-GREEN — PE2's
> recomputation). A class-pin chamber violating (OPEN-2a) would carry a byte
> divergence below its r₀ with the transport never firing there, putting this
> box's premise out of reach — which is why the sub-clause lives INSIDE the
> box as part of its premise rather than being imported silently.**
> CLAIM:
>
>     (a) v_r(Φ_{m+1}^har) = e_{r−1}f_{r−1}v_r(φ_{r−1}^tw), and the
>         order-(r−1) polygon of Φ_{m+1}^har IN THE TRANSPORTED CHAMBER is
>         one-sided with the harness support        [TW-ADM's vok/onesided];
>     (b) R_{r−1}(Φ_{m+1}^har) = (unit)·ψ_m^tw exactly — STRICT; in
>         particular the (ξ, w) recording of §5.1 step 1 exists at every
>         junction and the transport never aborts    [TW-ADM orbit +
>                                                     TW-STRICT].
>
> Equivalent sufficient form (the key-carry statement …): writing
> Φ_q^har = φ_q^tw + D_q with deg D_q < deg φ_q and D_q on-or-above the key
> line, the φ^tw-devs of the powers (φ^tw + D)^{e_m k} pick up only slot-
> character corrections … never produce a weight drop or a support split at
> any node of the (HR-REC) recursion tree.
> Alternative discharge route: a faithfully transcribed GMN
> representative-independence statement — NOT in this note's
> literature-consumption list; taking it would be a NEW consumption under
> the faithfulness discipline, with its own transcription and audit.”

**CONDITIONALITY:** **This box is the weld's one open lemma and it is ACCEPTED AS A BOX (F3). Its status at HEAD is the product of four out-of-range events, one of which is a WITHDRAWAL of an over-claim.**

**CHAIN for (OPEN-2a)'s forward direction (rule 25):**
1. `[r2, P1]`: folded into the box as its premise sub-clause; **OPEN at m ≥ 2**.
2. `[r3]`/`[r4]`: the gloss and the converse flag scoped to the forward half.
3. **OPEN2ATTACK annex (2026-08-08)**: (OPEN-2a)'s forward direction at `m ≥ 2` **NARROWED to a single displayed lemma** (the Σ-LAW), “Direction: box NARROWED …, NOT closed”.
4. **Σ-LAW annex + count corrections + supplier upgrade**: the Σ-LAW is PROVED and its note ACCEPTED 2/2, so “**(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at attempt grade**” and then rides an accepted supplier.
**TERMINAL for (OPEN-2a) forward: PROVED at attempt grade on an accepted supplier.**

**CHAIN for W2-OPEN-2(a)–(b) itself:**
1. Displayed OPEN, instance-confirmed 44/44.
2. **ANNEX #3 over-claims**: “W2-OPEN-2's residual open surface: the converse … only”.
3. **E5 finding 1 WITHDRAWS that sentence** (1465–1476, shard 2):

> “The final sentence of ANNEX #3, “W2-OPEN-2's residual open surface: the converse (recorded ξ ≠ 1 ⟹ byte-RED) only,” is **WITHDRAWN**. THEOREM OPEN-2a-Σ … proves only the shared-below forward implication … **It does not prove W2-OPEN-2(a)–(b) at any junction above the first recorded twist** \(r_0\). … **Correct current status:** … W2-OPEN-2(a)–(b), the chain-level transfer above \(r_0\), remains **OPEN and instance-confirmed on the six live roster junction-levels**.”

**TERMINAL for W2-OPEN-2(a)–(b): OPEN, instance-confirmed on the six live junction-levels — awaiting sol discharge (cert3).** `SUPERSESSION KIND: replacement` (a withdrawal).

**Two further in-range items:**
(c) **The `[r2, P3]` index fix** (`Φ_q ⇝ Φ_{q−1}`) is the first of two; **E5 finding 3 fixes the SECOND occurrence** in the Equivalent sufficient form (1539–1560, shard 2), which the P3 correction missed. `SUPERSESSION KIND: replacement`. **So the same dictionary was misapplied twice in one box, four months apart.**
(d) **The alternative discharge route is fenced by the faithfulness discipline** (`.06`): taking it “would be a NEW consumption … with its own transcription and audit”.

**DERIVATION:** The box states a claim, not a proof; the sufficient form and the four-route adjudication (`.34`) are its surrounding analysis.

**RESOLUTION TRACE:** statement 781–847 · the adjudication 849–879 (`.34`) · out-of-range: 1376–1403 (narrowed), 1405–1440 (Σ-LAW proved + upgrade), 1459–1476 (E5 finding 1's withdrawal), 1533–1560 (E5 finding 3's index fix).

XREF: `lean/notes/openmath/OPEN2ATTACK_2026-08-08.md` — **verified present**; `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` — **verified present**.
PINS: `bd82766` ✓ `8064ae3` ✓ `59c1ff2` ✓ `6b24942` ✓ `6e57e03` ✓ — 5/5 commits.

**TEETH:** **TW-ADM/TW-STRICT 44/44 across all 16 transported chambers, of which exactly 6 lie above a first twist (the lemma's live region); teeth MT-TW 2/2** (`.34`'s closing). **Disposition: instance-confirmation only — the box is OPEN.** Out of range, (OPEN-2a)'s instance base grows to 470 points (“468 fresh m ≥ 2 junction-levels … the I4A/I4B r = 5 geography swept 50 rows”, 1392–1395, shard 2).

---

### EFF.GRTW2.s1of2.34  [scope-record]  — the four-route derivability adjudication

**CANONICAL STATEMENT:** verbatim, lines 849–879.

**FORM:** bold-headed paragraph with four numbered routes and a Status line.

> “**Derivability adjudication (r1; four routes, each checked at source —
> none supplies the lemma, which is why it is boxed OPEN rather than cited):**
> (1) **[JC] (COORD-B)/JC-LOC:** machinery for ONE valuation — the harness w
> of a fixed tower, anchors built from harness data. Its
> normalized-coordinate invariance under line-wise rescaling (ρ_λ = 𝑅_λ/a_λ)
> is the right mechanism SHAPE but is proved chamber-internally only; and
> the corpus's sharpest two-operator dictionary, open lemma TR-3′-GEN, is
> OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only
> phrasing PERMANENTLY REFUTED on the order-3 stratum (ii) (the discrepancy
> is a slot-keyed character) — the accepted corpus itself prices the needed
> two-chain comparison as open. (2) **[JB]'s transport:** JB-DEV/JB-VTX/
> JB-TREE are single-chain harness dev/polygon/tree laws; the Σ(S) transport
> is a WEIGHT-FRAME reparameterization, never a key-representative change
> (JB row 15's 8 chamber walks are machine legs, not theorems). (3)
> **Classical MacLane key-equivalence invariance does not apply:** equal
> augmented valuations require v_{r−1}(Φ^har − φ^tw) ≥ γ (the ASSIGNED
> value); the recorded data warrant only ≥ key weight — with equality
> generic (proportional residuals differing by the unit w·ξ^{g_m}/c) —
> strictly BELOW γ, so the two chains' inductive valuations may genuinely
> differ as functions on O[x], and the lemma is irreducibly a statement
> about the CANONICAL lifts, not an instance of representative-invariance
> of the valuation. (4) **The GMN print:** develops the order-r theory over
> an arbitrary FIXED representative (tex 1288 "we fix a representative …
> without necessarily assuming that it has been constructed by the method
> of Proposition construct"; tex 1719) and itself flags
> representative-DEPENDENCE of derived objects (tex 2053); no independence
> proposition is among this note's consumed anchors, and even one would
> leave the two-recipe comparison (harness canonical lift vs print chamber)
> to prove. **Status: OPEN.** Machine: TW-ADM/TW-STRICT 44/44 junction-levels
> across all 16 transported chambers, of which exactly 6 lie above a first
> twist (the lemma's live region); teeth MT-TW 2/2.”

**CONDITIONALITY:** **A four-route non-derivability adjudication, each route checked at source, and it HELD under a deliberate fifth-route hunt at PE2** — “the four-route adjudication HELD at source under a deliberate fifth-route hunt (Lemma `extension`/Prop `extensionr` are unramified base-change with an exact multiplicative factor ρ_r — no supplier for the ADDITIVE two-recipe comparison; `admissible2` is the right genre but **its cross-term control IS W2-OPEN-2's open content**)” (1127–1131, `.42`). **So five routes were checked and none supplies the lemma.**
**Route (1) is the charge's named item.** It records the corpus's own pricing of the two-chain comparison as open, via **TR-3′-GEN**: “**OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only phrasing PERMANENTLY REFUTED on the order-3 stratum (ii)**”. `grep -cF 'TR-3′-GEN' GRTJC_PROOF_2026-08-08.md` = **8** ✓ verified. **`spec/HYPOTHESIS_LEDGER.md` HYP.139 quotes GRTJC on exactly this**: “Transport of the harness w and 𝑅 to the FGMN objects is still **W-1 (ATTEMPT)** — and the corpus's own march-level dictionary for that transport, **TR-3′-GEN, is OPEN at general order**.” See `.39` and OPEN-CALL 3.
**Route (3) is the one E5 finding 4 later uses against W2-C3(iii)** (`.29`) — the note's own adjudication contained the refutation of its own equivalence wording.
**Route (4) invokes the faithfulness discipline** (`.06`) to price the alternative as a NEW consumption.

**DERIVATION:** Four source checks; not a derivation.

**RESOLUTION TRACE:** statement 849–879 · the fifth-route hunt 1127–1131 (`.42`) · route (3)'s later use 1562–1594 (shard 2) · the ledger row `spec/HYPOTHESIS_LEDGER.md` HYP.139.

XREF: `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` — count **8**.
XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` ✓ present (route 2's subject).
XREF: `docs/references/HigherNewton.tex` ✓ (tex 1288, 1719, 2053).
ARTIFACT: `spec/HYPOTHESIS_LEDGER.md` ✓ present.

**TEETH:** **TW-ADM/TW-STRICT 44/44 + MT-TW 2/2 (a garbled character caught).** Disposition: instance confirmation; the adjudication itself is a `transfer audit` (rule 27) — five source reads, no instrument.

---

### EFF.GRTW2.s1of2.35  [scope-record]  — §5.3, W2-OPEN-1 (the value layer)

**CANONICAL STATEMENT:** verbatim, lines 883–902.

**FORM:** `###`-headed section with a bold-headed open lemma, a status line, and an honest-distance paragraph carrying an `[r1, F1]` bracket.

> “**W2-OPEN-1.** On every tower of the class pin, the committed value/
> cocycle battery — K5 = L6-(n) anchor values, K6 = W-MULT top, K7 = THE LAW
> c_{n+1} = z̄^δ·∏_j z_j^{D_j}, K12 = π-shift/ρ-monodromy, K1–K4/K13 riding —
> holds verbatim with the TRANSPORTED classifier lifts substituted for the
> harness lifts (the ClsTower reading: all valuations/reads/anchors/cocycles
> computed ON the transported keys against the harness ψ-byte ledger).
>
> Status: **instance-confirmed, not proved.** [Machine: TW-F3 = 0 violations
> on ALL 16 towers, 684 sample groups — in particular the probe's 96 RED
> (K6: 48, K7: 48 on T3A/T3C/T3D/I4C) all GREEN; TW-F3b control unchanged
> 0.] The honest distance to a proof: the battery's laws are corpus theorems
> about the HARNESS lifts; transporting them across the junction units needs
> the anchor-product carry analysis of §5.4 run level-generically (the
> transported key differs from the harness key by on-line unit ratios, and
> the battery consumes key bytes only through overflow carries — §5.4 —
> whose reads shift by exactly the recorded characters on both sides of the
> cocycle ratio). That analysis is the W-2 → W-5 seam (the correction-tree
> junction J-B) and is NOT claimed here. **[r1, F1: its CHAIN-LEVEL shadow —
> the same carry analysis run on the key objects instead of the anchors — is
> now displayed as the open box W2-OPEN-2 in §5.2.]**”

**CONDITIONALITY:** **OPEN and instance-confirmed, and it stays that way through every event.** E5's consumer sweeps say so three times: “W2-OPEN-1 remains open” (1476), “W2-OPEN-1 remains open and unchanged” (1529), “W2-OPEN-1 remains a comparison computed separately on the transported keys and remains OPEN” (1594) ✓ **three independent re-affirmations in one append.**
**The honest-distance paragraph names the missing analysis and its owner** (the W-2 → W-5 seam, junction J-B) and declines it. **The `[r1, F1]` bracket ties W2-OPEN-1 and W2-OPEN-2 as two shadows of one carry analysis** — anchors vs keys.

*Arithmetic audit (rule 22).* The probe's 96 RED decomposes as “K6: 48, K7: 48 on T3A/T3C/T3D/I4C” ✓ `48 + 48 = 96` ✓ **exact**, and four towers × 12 each × 2 families = 96 ✓ plausible. TW-F3's 684 sample groups over 16 towers ≈ 42.75 per tower — not an integer, so the groups are not uniform per tower; no cross-check available. **Recorded as consistent-but-unverifiable.** The control TW-F3b is “unchanged 0” ✓ — a control that stays at 0 is the right shape (it should not move).

**DERIVATION:** None — the box is open.

**RESOLUTION TRACE:** statement 883–902 · the carry mechanism 906–936 (`.36`) · the three re-affirmations 1476, 1529, 1594 (shard 2).

**TEETH:** **TW-F3 684/684 GREEN with the probe's 96 RED all turning GREEN, plus an unchanged control.** **Disposition: measurement; the strongest instance evidence in the note, and explicitly “instance-confirmed, not proved”.**

---

### EFF.GRTW2.s1of2.36  [lemma]  — §5.4, LEMMA W2-T3E (carry-inertness of a flat-shielded twist)

**CANONICAL STATEMENT:** verbatim, lines 906–936.

**FORM:** `###`-headed section with a bold-headed lemma, an instance analysis, and an `[r1, F7]` machine-key scope bracket.

> “**LEMMA W2-T3E (carry-inertness of a flat-shielded twist).** The battery
> consumes a diverged key Φ_j only through two channels: (a) exact powers
> in anchors and their products (byte-inert: the dev of a product of pure
> key powers by the key is exact, and the digit is the byte-shared lower
> part); (b) the division carry Φ_{j−1}^{e_{j−1}} ↦ Φ_j − Ĉ fired when an
> anchor product overflows, i.e. when s_j(γ) + s_j(γ′) ≥ e_{j−1} — ONLY
> then do the twisted correction bytes Ĉ enter a read. If e_{j−1} = 1
> directly below the (unique) diverged key, then s_j ≡ 0 identically and
> channel (b) never fires: the twist is CARRY-INERT and every battery
> quantity is byte-identical to the harness computation.
>
> On T3E the only battery-consumed diverged key is the top anchor key Φ₂
> with e₁ = 1 below it: s₂ ≡ 0 on the whole window. [Machine CK-T3E:
> s₂-census = {0}; 0 byte-differing battery digits across all pairs; 0
> violations.] On T3A (e₁ = 2) the overflow pairs exist and are exactly
> where the twisted bytes enter: every K6/K7-failing pair is an overflow
> pair whose top-dev digits differ in bytes (16 failing pairs ⊆ 24
> byte-diff pairs; the reverse containment fails honestly — a carry can be
> read-invisible or a common character can cancel in the cocycle ratio).
> [Machine CK-T3E: containment exact.] **[r1, F7 — machine-key scope: CK-T3E
> keys exactly the byte-diff containment (16 ⊆ 24) and the s₂-censuses ({0}
> on T3E, {0,1} on T3A); the identification of the 24 byte-diff pairs as
> s₂-OVERFLOW pairs is the mechanism's reading (channel (b) of LEMMA
> W2-T3E), asserted per-mechanism and not machine-keyed pair-by-pair.]** T3E is therefore NOT an anomaly: it
> is the e = 1 passthrough leg (the K13 genre) of the same mechanism that
> breaks the other rows — and after transport the question is moot
> (TW-F3 = 0 everywhere).”

**CONDITIONALITY:** **PROVED (mechanism) with a machine leg in both directions** (`.38`'s claims table). The `[r1, F7]` bracket is a **machine-key scope disclosure**: the machine keys the containment and the censuses, but **the identification of the 24 byte-diff pairs as overflow pairs is “asserted per-mechanism and not machine-keyed pair-by-pair”**. `SUPERSESSION KIND: scope-pin` on what the machine establishes. **That is a precise, self-administered downgrade of a machine claim.**
**The reverse containment failure is disclosed and explained**: “a carry can be read-invisible or a common character can cancel in the cocycle ratio” — so `16 ⊆ 24` strictly, honestly.
Untouched by every append.

**DERIVATION:** Quoted inline; channel (b) fires iff `s_j(γ) + s_j(γ′) ≥ e_{j−1}`, which is vacuous at `e_{j−1} = 1` because `s_j ≡ 0`.

*Arithmetic audit (rule 22).* At `e_{j−1} = 1`, the grid offset `s_j = ℓV mod e_{j−1} = ℓV mod 1 = 0` ✓ **identically** ✓ (`.11`'s W2-L0) ⟹ `s_j(γ) + s_j(γ′) = 0 < 1 = e_{j−1}` ✓ **never overflows** ✓ **exactly the displayed argument** ✓. T3E's reads `(2,1,2),(1,1,1),(2,3,1)` have `e₁ = 1` ✓ **the flat middle** ✓, and T3A has `e₁ = 2` ✓ so overflow is possible ✓ (`s₂-census = {0,1}` ✓). **The mechanism reproduces.**

**RESOLUTION TRACE:** statement 906–936 · the value layer it explains 883–902 (`.35`) · the round record 1096–1098 (`.41`).

**TEETH:** **CK-T3E, 2 samples, GREEN — “both directions”** (`.38`). Disposition: executable regression on the mechanism's two halves, **with the per-pair identification explicitly NOT machine-keyed** — a `signed vacuity disclosure` at pair granularity.

---

### EFF.GRTW2.s1of2.37  [table]  — §6.1, the machine bracket table and the `[r1, F4]` prereg disclosure

**CANONICAL STATEMENT:** verbatim, lines 942–966 (the Markdown table plus the prereg-disclosure bracket).

**FORM:** `###`-headed section with a Markdown table (12 rows) and a bold-headed disclosure bracket.

`[TABLE]` — transcribed verbatim (the source is Markdown; emitted once per rule 14's tables-are-units clause):

| family | claim keyed | samples | verdict |
|---|---|---|---|
| CK-MM | W2-L2 mismatch identity (integers + elements) | 4,396 | GREEN |
| CK-HR1 | W2-L1 base builder read | 156 | GREEN |
| CK-VD1 | W2-L3 level-1 packed dictionary | 156 | GREEN |
| CK-REC | (HR-REC) at every shared-key node | 55 | GREEN |
| CK-SLOT / CK-SLOT-M1 | W2-C2 slot-ratio law / m = 1 exact form | 44 / 16 | GREEN |
| CK-XI | §3.4 (ξ,w) satisfies the orbit equations (21 perimeter junctions; 1 recorded boundary = I4B r=5) | 22 | GREEN |
| CK-BYTE | byte law ⟺ node-value walk | 28 | GREEN |
| TW-RATIO / TW-ADM / TW-STRICT | W2-C3 (i)/(ii) *(with the `[r1, F1]` / `[r2, P1]` grade brackets — see `.30`)* | 44 each | GREEN |
| TW-F3 / TW-F3b | W2-OPEN-1 (96 → 0) / control | 684 / 684 | GREEN |
| TW-PARI / TW-QO | transported (e,f) ties / concrete shapes | 12 / 7 | GREEN |
| CK-T3E | W2-T3E mechanism (both directions) | 2 | GREEN |
| MT-TW | teeth (garbled character caught) | 2 | GREEN |

and the disclosure:

> “**[r1, F4 — prereg disclosure (the runner is byte-frozen, so the
> correction lives here):** the sealed runner's docstring preregisters
> "TW-PARI … PREDICT: 24/24", but the family as executed has **12** samples —
> ONE top lift per ℤ_p row (the transported classifier top); the 24 was the
> probe's both-legs count, copied into the seal. The substantive prediction
> (0 violations) HELD and the note's TW-PARI 12/12 figures are correct; the
> seal's sample-count miscount is disclosed here rather than silently
> absorbed.]**”

*Arithmetic audit (rule 22), the total recomputed from the table.* Summing the sample column: `4,396 + 156 + 156 + 55 + 44 + 16 + 22 + 28 + 44 + 44 + 44 + 684 + 684 + 12 + 7 + 2 + 2`. Step by step: `4,396 + 156 = 4,552`; `+156 = 4,708`; `+55 = 4,763`; `+44 = 4,807`; `+16 = 4,823`; `+22 = 4,845`; `+28 = 4,873`; `+44+44+44 = 5,005`; `+684 = 5,689`; `+684 = 6,373`; `+12 = 6,385`; `+7 = 6,392`; `+2 = 6,394`; `+2 = 6,396`. **Total 6,396 against the header's 6,403 — a shortfall of 7.** The table has **12 rows naming 17 families** (the header says “17 check families”): CK-MM, CK-HR1, CK-VD1, CK-REC, CK-SLOT, CK-SLOT-M1, CK-XI, CK-BYTE, TW-RATIO, TW-ADM, TW-STRICT, TW-F3, TW-F3b, TW-PARI, TW-QO, CK-T3E, MT-TW = **17** ✓ **the family count reproduces exactly.** The 7-sample gap is **not reconcilable from the displayed table** — most plausibly a family with an unlisted sample count (e.g. TW-QO's 7 counted once in the table and again in a per-shape breakdown), but **the note supplies no decomposition**. **Recorded as source defect 4: the sample column sums to 6,396, not the headline 6,403.** No claim is thereby wrong (every family is GREEN with 0 violations), but a merge that re-derives the total will not land on it.
*The prereg disclosure's arithmetic.* “TW-PARI … PREDICT: 24/24” vs 12 executed ✓, explained as “the probe's both-legs count” ✓ — `2 × 12 = 24` ✓ **consistent.** 12 = one top lift per ℤ_p row ✓ and the roster has 16 towers of which the ℤ_p ones number 12? The roster is “ℤ₂/ℤ₃/F₂[[t]]/F₃[[t]]” ✓ — if evenly split, 8 ℤ_p rows, not 12. **No decomposition is given; recorded as unverifiable.** The note is explicit that `F_p[[t]]` rows have no PARI leg (`.40`), which makes 12 ℤ_p top lifts out of 16 towers plausible only under an uneven split. Recorded.

**CONDITIONALITY:**
(a) **The `[r1, F4]` prereg disclosure is a signed miscount in a SEALED docstring**, disclosed because the runner is frozen: “the seal's sample-count miscount is disclosed here rather than silently absorbed”. `SUPERSESSION KIND: counter re-reading`. **The substantive prediction (0 violations) held** ✓.
(b) **The TW-RATIO/TW-ADM/TW-STRICT row carries the grade brackets** and the TW-STRICT SAME-adjacent reclassification (`.30`(b)) — **so the table itself refuses to count three independent 44/44 legs.**
(c) **CK-XI's row separates the boundary junction** (“21 perimeter junctions; 1 recorded boundary = I4B r=5”) ✓ consistent with `.23`.

**DERIVATION:** Machine record.

**RESOLUTION TRACE:** statement 942–966 · the grade brackets 651–705 (`.30`) · the round record 1087–1089 (`.41`).

ARTIFACT: `verification/openmath/grt_w2_checks.py` ✓ · `grt_w2_checks_output.txt` ✓ · `grt_w2_checks_results.json` ✓.
**UNPINNED:** the runner sha256 is truncated at all five occurrences (`.03`).

**TEETH:** this unit IS the teeth roster; the inverse table is §5.

---

### EFF.GRTW2.s1of2.38  [table]  — §6.2, the claims table (grades)

**CANONICAL STATEMENT:** verbatim, lines 970–983 (the Markdown table; the multi-layer brackets inside the W2-C3, W2-ID1 and W2-OPEN-2 rows are reproduced in the transcription below).

**FORM:** `###`-headed section with a Markdown table (13 rows), three of which carry nested round brackets.

`[TABLE]` — transcribed, with the nested brackets compressed to their TERMINAL readings and the full text pointed at its unit:

| claim | statement | grade as displayed | TERMINAL grade at HEAD |
|---|---|---|---|
| W2-L0/L1/L2/L3 | grid tie; base builder; mismatch identity; VD-1 | PROVED (attempt grade 0/2) | PROVED, and in the accepted enumeration (F3) |
| TH-BASE | r = 2 junctions byte-equal | PROVED | unchanged |
| W2-C1a | vok + one-sided polygon, `[r1, F2]` chamber-qualified | PROVED **as qualified** | unchanged; **explicitly exempted by E5 finding 2** |
| W2-C2(a) | slot law + (ξ,w) = (c₁^{e_m}, 1) at m = 1 | PROVED | unchanged; **E5: “survive unchanged”** |
| W2-C2(b) + §3.4 | scalar (ξ,w) closed form at m ≥ 2 | PROVED **on (C-coll)**; outside: exact recursion (c), boundary boxed W2-BOX-1 | unchanged |
| W2-C1 | clause 1 verdict (strict rep of t^ξ; of t iff support-trivial) | PROVED on the §3 perimeter | **SUPERSEDED outside (C-coll)** by W2-C1-CORR (`.25`) |
| §4.3 | unpinned-ℓ parametrization | CONVENTION ANALYSIS, review-owed | unchanged; **E5: applies only after a scalar pair exists** |
| W2-ID1 `[r2]` | recorded ξ = 1 ⟹ byte-equal at m = 1 `[r4, PE4 o-d: the FORWARD half; the converse unproved at every m]` | PROVED | **forward direction now PROVED at every m** via THEOREM OPEN-2a-Σ on an accepted supplier |
| W2-C3 (i)–(iii) | clause 3 chain level | `[r1, F1]` 38/44 proved + 6/44 measured; `[r2, P1]` 36 derived + 2 instance-warranted; `[r3]` forward direction only | **census re-displayed 37 + 1 + 6** (E5); **(iii)'s equivalence wording SUPERSEDED** to ledger-equivalence |
| W2-OPEN-2 `[r1]` | chain-level bridging lemma; carries (OPEN-2a) and the P3 pairing fix | **OPEN**, instance-confirmed 44/44; not derivable from the accepted corpus | **(OPEN-2a) forward PROVED at every m; W2-OPEN-2(a)–(b) OPEN on the six live junction-levels** (E5 finding 1's withdrawal) |
| W2-OPEN-1 | clause 3 value layer | **OPEN**, instance-confirmed 684 groups / 0 | unchanged — re-affirmed three times by E5 |
| W2-T3E | flat-shielded twists are carry-inert | PROVED (mechanism) + machine both directions | unchanged |

**CONDITIONALITY:** **The table's own grade column is the note's self-assessment and FIVE of its twelve rows have moved.** The TERMINAL column above is compiler-computed from the out-of-range appends and is **not in the source**; each entry cites its unit. `SUPERSESSION KIND` per row as listed at `.25`, `.29`, `.31`, `.33`.
**The `[r4, PE4 o-d]` scoping of the W2-ID1 row and the adjacent W2-OPEN-2 row label are two of the “sweep-completing sites”** found by r4's full-note grep (`.03`) — i.e. the r3 species sweep missed them and r4's grep found them. **That is the note's own lesson, stated at §10: “a species sweep must exhaust the species, not stop at the reviewer's site list”** (1292–1294, shard 2).

*Arithmetic audit (rule 22).* 12 claim rows ✓ covering: 4 base lemmas (as one row) + TH-BASE + W2-C1a + W2-C2(a) + W2-C2(b) + W2-C1 + §4.3 + W2-ID1 + W2-C3 + W2-OPEN-2 + W2-OPEN-1 + W2-T3E ✓. **Three are OPEN or fenced** (W2-OPEN-1, W2-OPEN-2, §4.3) plus W2-BOX-1 inside the W2-C2(b) row ✓ = **the four open surfaces `.40` lists** ✓ **exact match.**

**DERIVATION:** Self-assessment table.

**RESOLUTION TRACE:** statement 970–983 · the five moved rows 1484–1531, 1568–1594, 1459–1476 (shard 2), 1405–1440 (shard 2) · the r4 sweep 1283–1309 (shard 2).

**TEETH:** each row names its machine family; the inverse table is §5.

---

### EFF.GRTW2.s1of2.39  [scope-record]  — §6.3, the consequence display (what J-A / J-B can consume, with caps)

**CANONICAL STATEMENT:** verbatim, lines 985–1014.

**FORM:** `###`-headed section with three bullets, the second carrying four lettered carry-items with nested `[r1]`/`[r2]`/`[r4]` brackets.

> “* **For J-A (W-1, the operator dictionary):** W2-L3 is the level-1 value
>   dictionary IN PROVED FORM (ε = the print twist in canonical
>   coordinates), and (HR-REC) is the exact level-generic transfer shape;
>   but W-1 at orders ≥ 3 is NOT advanced — the level-≥2 dictionary is a
>   conjugation whose scalar collapse needs (C-coll).
> * **For W-2's consumers ([ILN]† applicability):** the corrected W-2 now
>   states — and this note proves at its displayed grades — that the
>   classifier's canonical keys are unit-covariant images of the harness
>   lifts with EXPLICIT characters, and that after ψ-transport the harness
>   value-layer corpus is instance-verified verbatim on classifier lifts.
>   Any consumer citing this must carry: (a) the (C-coll)/recursion split
>   of clause 2; (b) W2-OPEN-1's open status for the general value-layer
>   theorem; (c) the §4.3 convention fence; **(d) [r1, F1] W2-OPEN-2's open
>   status for clause 3's chain level ABOVE each transported chamber's first
>   ξ ≠ 1 junction (the grade split proved-to-first-twist / measured-above),
>   and the chamber qualifier on W2-C1a [r1, F2]** **[r2, P1: including
>   W2-OPEN-2's own premise sub-clause (OPEN-2a) — ~~the recorded-ξ/byte-
>   divergence identification at m ≥ 2, proved only at m = 1 (W2-ID1),~~
>   **[r4, PE4-P1: the FORWARD direction of the recorded-ξ/byte-divergence
>   identification at m ≥ 2 (recorded ξ = 1 ⟹ byte-equal — all the proved
>   scope needs), proved at m = 1 (W2-ID1); the CONVERSE (recorded ξ ≠ 1 ⟹
>   byte-RED) is UNPROVED at every m, PE3's counter-instance recorded at
>   §5.2]**,
>   instance-exact on the roster].**
> * **NOT unlocked:** W-5 (correction-tree transfer: the §5.4 carry
>   analysis is its opening move, not its proof), the J-C block W-6..W-9
>   (no gr claim anywhere here; BLOCKED-ON-CARRIER-TIE stands), J-D counts,
>   and every Phase-B Lean obligation. The P0 application gate stands.”

**CONDITIONALITY — THE W-1 TRANSPORT ATTEMPT ROW (the charge's named item), compiled exactly as the note and the corpus leave it:**

**(1) What this note gives W-1.** Bullet 1 is precise and modest: **W2-L3 in PROVED FORM at level 1**, and HR-REC as “the exact level-generic transfer shape”. **And it states its own limit in the same sentence: “but W-1 at orders ≥ 3 is NOT advanced — the level-≥2 dictionary is a conjugation whose scalar collapse needs (C-coll).”** The Grade cap says the same (`.05`(e)): “Nothing here … advances W-1's operator dictionary beyond the level-1 value dictionary proved below.”

**(2) What the corpus records about W-1, verified per rule 10.** `spec/HYPOTHESIS_LEDGER.md` **HYP.139**, whose WHERE is **`docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4 L48 and §5 L131** — the charge's “census I-4”:

> “STATEMENT: After the FGMN-WELD cite was PDF-verified and DISCHARGED (2026-08-12), the residue is not citational: “Residue is NOT the cite but the transport: **W-1 (harness w, 𝑅 → FGMN objects) stays ATTEMPT**, unchanged by this unit” (I-4); §5 — “the FGMN residue that remains is the W-1 transport (ATTEMPT), which is **a proof obligation, not a citation one**.””

with its consumer chain and class:

> “CONSUMED BY: I-4's own consumer chain — W-9 (proved GIVEN W-6..W-8) → GENHN-4's layer-1 carry bookkeeping at μ≥3 (GENHN-BOX-2) → count laws at μ≥3 … GRTJC L1990–1993 (re-verified at L1990): “Transport of the harness w and 𝑅 to the FGMN objects is still W-1 (ATTEMPT) — and the corpus's own march-level dictionary for that transport, TR-3′-GEN, is OPEN at general order.” This row is the **live residue that does NOT discharge with HYP.148 by a transcription fold** — it is class MATH where HYP.148 is class CARRY.”
> “CLASS: named-obligation … PROPOSED DISPOSITION: **MATH** — an in-cone ATTEMPT-grade proof obligation …”
> “**v6 ARC NOTE (2026-08-14).** … This row is **UNCHANGED, MATH at full strength** — a route that *passes* its hostile arc would retire this row per the v4 note above, but the arc has not yet passed.”

**(3) The compiled status.** **W-1's transport is at ATTEMPT grade, class MATH, at full strength as of 2026-08-14.** GRTW2 does not advance it beyond level 1 and says so twice. **GRTW2's own route (1) (`.34`) independently records the corpus's pricing of the same object**: TR-3′-GEN “is OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only phrasing **PERMANENTLY REFUTED** on the order-3 stratum (ii)” — `grep -cF 'TR-3′-GEN' GRTJC_PROOF_2026-08-08.md` = **8** ✓, and the ledger quotes GRTJC's own “OPEN at general order” ✓. **The two statements agree**: GRTW2 says the level-≥2 dictionary needs (C-coll); GRTJC/the ledger say the general-order dictionary is open and its units-only form is refuted. **Neither is a discharge, and no route in the corpus currently retires the row** (the candidate — HYP.149's WELD-ZERO fold — is at clean-pass 1 of 2, `.34`-adjacent, recorded at `spec/HYPOTHESIS_LEDGER.md`). See OPEN-CALL 3.

**Other conditionality:**
(a) **Carry item (d) is the note's consumer-facing conditionality and it was scoped THREE times** (`[r1, F1]` → `[r2, P1]` → `[r4, PE4-P1]`). **CHAIN TERMINAL: the `[r4]` forward-direction reading**, itself upgraded out of range (the forward direction is now proved at every m).
(b) **“NOT unlocked” is a four-item negative fence** and it is untouched by every append — including “the J-C block W-6..W-9 (no gr claim anywhere here; **BLOCKED-ON-CARRIER-TIE stands**)”, which is the same gate the Grade cap declines to fire (`.05`).

**DERIVATION:** Consequence declaration.

**RESOLUTION TRACE:** statement 985–1014 · the W-1 limit restated 128–129 (`.05`) · route (1) 851–859 (`.34`) · external: `spec/HYPOTHESIS_LEDGER.md` HYP.139, `docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4.

XREF: `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` — count **8**.
XREF: `spec/HYPOTHESIS_LEDGER.md:HYP.139` — grep-verified count **20**.
ARTIFACT: `docs/TIGHTNESS_CENSUS_2026-08-11.md` — **verified present**.

**TEETH:** NONE for the W-1 statement — it is a negative claim about what is *not* advanced. **W2-L3's proved level-1 content is toothed by CK-VD1 (156/0)** (`.14`).

---

### EFF.GRTW2.s1of2.40  [fence]  — §6.4, the dependency line

**CANONICAL STATEMENT:** verbatim, lines 1018–1048.

**FORM:** `###`-headed section body: a CONSUMES/CONSUMED-BY/Fences paragraph with a struck clause and four dated round brackets.

> “CONSUMES: [ILN]† S0.1/S0.2 (accepted package: class pin, canonical lifts,
> REALIZE/WELL-DEF, reads) · GMN print as literature (§ header list, tex
> anchors) · the sealed probe artifacts + its GmnLeg transcription (commit
> 55f7416/a6f7653 line) · GRB D-REAL only as context (no consumption) ·
> GRW2_TIE_DESIGN OB-1..6 only as the named downstream (no consumption).
> CONSUMED BY (intended): the W-1 dictionary unit, the W-5 tree unit, and
> the weld campaign's J-A ledger. Fences: instance evidence = 16 towers
> (reads ≤ 4 + top, residue fields ≤ F₉, wild rows included) + 5 shapes;
> F_p[[t]] rows have no PARI leg (displayed deferral, inherited); nothing
> here is a Lean artifact; ~~no acceptance arc opened — hostile passes owed
> before any consumption at proof grade~~ **[r1] the acceptance arc is OPEN
> (S-STATUS block, top): PE1 run (0C + 2G + 5m), r1 applied, counter 0/2 —
> 2-clean owed before any consumption at proof grade. The note's open boxes
> after r1: W2-OPEN-1 (value layer) + W2-OPEN-2 (chain level above a first
> twist) + W2-BOX-1 (scalar form off (C-coll)) + the §4.3 convention fence.**
> **[r2] PE2 run (0C + 2G + 1m, 79e796b), r2 applied, counter 0/2, PE3 next;
> open boxes unchanged in count — W2-OPEN-2 now carries its premise
> sub-clause (OPEN-2a) explicitly, and the new proved lemma W2-ID1 (§5.2)
> closes the m = 1 slice of that identification **[r4, PE4-P1: = of its
> FORWARD direction only …]**.** **[r3] PE3 run (0C + 1G
> minor, 9bd938f), r3 applied, counter 0/2, PE4 next; open boxes unchanged in
> count …** **[r4] PE4 run
> (0C + 1G minor + 1m, e92cb22), r4 applied, counter 0/2, PE5 next; open
> boxes unchanged in count …**”

**CONDITIONALITY:**
(a) **“CONSUMED BY (intended): the W-1 dictionary unit …”** — an *intended* consumer, i.e. the W-1 unit does not yet exist as a consumer of this note. Consistent with `.39` and HYP.139's ATTEMPT status.
(b) **`STALE-SELF-DESCRIPTION`** on all four “counter 0/2” entries and on “2-clean owed before any consumption at proof grade” — **the 2-clean landed** (PE5 + PE6) and the acceptance record's CONSEQUENCE reads “consumers riding W-2 at attempt grade … now ride an ACCEPTED supplier at its fenced scope” (1350–1353, shard 2).
(c) **“open boxes unchanged in count” is repeated at r2, r3 and r4** ✓ — **and it stays true through the whole in-range arc: four open surfaces throughout.** Out of range the count *does* change: (OPEN-2a) leaves the open set (proved), and W2-OPEN-2(a)–(b) narrows to six junction-levels. **Neither event is folded back into this line.** Recorded as source defect 5.
(d) **The `F_p[[t]]` PARI deferral is inherited from the probe** — a foreign fence carried forward.

**DERIVATION:** Dependency declaration.

**RESOLUTION TRACE:** statement 1018–1048 · the acceptance 1334–1353 (shard 2) · the box movements 1376–1440, 1459–1476 (shard 2).

PINS: `55f7416` ✓ `a6f7653` ✓ `79e796b` ✓ `9bd938f` ✓ `e92cb22` ✓ — 5/5.
ARTIFACT: `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` ✓ · `lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md` ✓.

**TEETH:** the fences are declarations; the instance-evidence figure (16 towers + 5 shapes) is the roster of `.07`.

---

### EFF.GRTW2.s1of2.41  [changes-record]  — §7, the r1 round record

**CANONICAL STATEMENT:** verbatim, lines 1052–1117 (the Against paragraph, the seven-finding repair map, the fold implications, and the Freeze paragraph).

**FORM:** `##`-headed round block: a bold-headed Against paragraph, seven bulleted findings, a bold-headed fold paragraph, and a bold-headed Freeze paragraph.

> “**Against:** W2-PE1 (`GRTW2_passPE1_report.md`, commit 083adff; target
> 5463f2a) — 0 CRITICAL, 2 JUSTIFICATION GAPS, 5 minor; core mathematics
> CONFIRMED by full re-derivation (PE1 §A), machine leg re-run bit-identical
> (PE1 §B). Repair map, finding → edit site: …
>
> **Fold implications recorded for the orchestrator (accepted texts are
> NEVER edited by this unit):** WELDMASTER's (M4) face quotes W2-C3
> ("ψ-transport: strict representative at every level of the transported
> chain, no weight/support splits") under its as-of pin [W2]@5463f2a (WM
> r3's O-1 pin group) — the pin makes that face drift-proof and PE1
> adjudicated that it carries the conditionality BY CITATION, so nothing is
> falsified; at the next ledger fold a dated annotation pointing (M4)'s
> W2-C3 cite at the re-scoped grade (proved-to-first-twist / measured-above
> / W2-OPEN-2) is owed, and likewise JB §0M row 15's subordinate
> "(representative reading; W2-C3 chamber off the byte perimeter)" cell.
> Both are orchestrator actions, not r1 edits.
>
> **Freeze:** r1 is note-only. `grt_w2_checks.py` (sha256 71f8fc90f7543fd3…,
> PE1-verified bit-identical to 5463f2a) and both artifacts untouched; a
> stray working-tree drift on `grt_w2_checks_results.json` (elapsed_s only,
> left by a prior pass's re-run) was restored to the committed bytes before
> this round's edits. **Counter 0/2 (ZERO clean passes); W2-PE2 — a fresh
> hostile pass on this post-r1 text — is the next acceptance attempt.**”

**CONDITIONALITY:**
(a) **The seven findings' repair sites are all located in this shard**: F1 → `.29`/`.30`/`.33`/`.34`; F2 → `.24`; F3 → `.18`/`.22`; F4 → `.37`; F5 → `.23`; F6 → `.26` (reverted at r2); F7 → `.36`. **All seven located and non-empty** ✓.
(b) **The fold implications are the note's no-append protocol in action** — two annotations recorded as owed to the orchestrator, **and both were EXECUTED out of range** (the 2026-08-08 fold-carry annex, 1359–1374, shard 2): GRTJB row 15 at `5054d69` ✓, WELDMASTER (M4) at the annex's own fold, “the half that had to wait for WELDMASTER's own acceptance (66b3498)” ✓ commit verified. **The annex's closing line: “Nothing else in the r1 record remains orchestrator-owed.”** `SUPERSESSION KIND: inventory completion`.
(c) **The Freeze paragraph records a drift RECOVERY** — an `elapsed_s`-only working-tree drift restored before editing. **That is the only instrument-integrity event in the arc and it was caught and reversed.**
(d) **PE1 confirmed the core mathematics by full independent re-derivation** — the strongest positive result of the arc's first pass.

*Arithmetic audit (rule 22).* “0 CRITICAL, 2 JUSTIFICATION GAPS, 5 minor” = 7 findings ✓ and the repair map has 7 bullets (F1–F7) ✓ **exact**. The F3 recount is audited at `.22` ✓.

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1052–1117 · the fold's execution 1359–1374 (shard 2) · the seven sites as listed.

PINS: `083adff` ✓ `5463f2a` ✓ `5054d69` ✓ `66b3498` ✓ — 4/4.

**TEETH:** PE1's full re-derivation (a hostile pass re-deriving the core) + the bit-identical machine re-run. **Disposition: `in-house hostile pass` (rule 27) + executable regression.**

---

### EFF.GRTW2.s1of2.42  [changes-record]  — §8, the r2 round record

**CANONICAL STATEMENT:** verbatim, lines 1121–1193.

**FORM:** `##`-headed round block: Against paragraph with PE2's confirmations, three bulleted findings, fold implications, Freeze.

> “**Against:** W2-PE2 (`GRTW2_passPE2_report.md`, commit 79e796b; target
> 8d5e3fa) — 0 CRITICAL, 2 JUSTIFICATION GAPS (P1 moderate, P2 minor),
> 1 minor (P3), NOT CLEAN. PE2 also CONFIRMED: the four-route derivability
> adjudication holds at source, with a deliberate fifth-route hunt finding
> no supplier (Lemma `extension`/Prop `extensionr` are unramified base-change
> with an exact multiplicative factor ρ_r — no supplier for the ADDITIVE
> two-recipe comparison; `admissible2` is the right genre but its cross-term
> control IS W2-OPEN-2's open content); machine leg re-run byte-identical
> (exit 0, 6,403/0, 17 GREEN, both artifacts byte-identical incl. elapsed);
> fresh leg — the §3.4 display evaluated against the committed ξ-ledger by
> from-scratch arithmetic, 16/16 at m = 1 (unique pairs, full support) plus
> hand re-derivations T3B/T3F r = 4 matching the ledger. …”

**CONDITIONALITY:**
(a) **The fifth-route hunt is the strongest confirmation W2-OPEN-2 gets**: two further print objects checked (`extension`/`extensionr`, `admissible2`) and neither supplies the lemma — with the sharp verdict that “`admissible2` is the right genre but **its cross-term control IS W2-OPEN-2's open content**”. **So the box is not for want of looking.**
(b) **P2's revert is adjudicated at source** (`.26`) — PE2 read tex 1431/1373/1447/1201 and found the r0 sign correct.
(c) **P3's index fix is the first of two** (`.09`, `.33`).
(d) **`STALE-SELF-DESCRIPTION`** on “counter 0/2 … W2-PE3 … next”.
(e) **The fold implications add one new item**: WM line 88's “its only commit” is STALE, with an `[r3, o1]` line-drift annotation. **A stale pointer in an accepted supplier, flagged and left to the orchestrator.**

*Arithmetic audit (rule 22).* “0C + 2G + 1m” = 3 findings ✓ and three bullets (P1, P2, P3) ✓. The fresh leg's `16/16 at m = 1` ✓ matches the 16 r = 3 junctions (one per tower) ✓ (`.22`, `.31`).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1121–1193 · P1 → `.30`/`.31`/`.33`; P2 → `.13`/`.26`; P3 → `.33` · the WM staleness 1184–1186.

PINS: `79e796b` ✓ `8d5e3fa` ✓ `f8c2c09` ✓ (WM r5, cited in the `[r3, o1]` annotation) — 3/3.

**TEETH:** PE2's from-scratch §3.4 evaluation (16/16) + hand re-derivations at T3B/T3F. **Disposition: executable regression on a decorrelated instrument + hand verification.**

---

### EFF.GRTW2.s1of2.43  [changes-record]  — §9, the r3 round record

**CANONICAL STATEMENT:** verbatim, lines 1197–1257.

**FORM:** `##`-headed round block: Against paragraph with PE3's five confirmations, one bulleted finding with a four-part cure, the two ungraded observations, and Freeze.

> “**Against:** W2-PE3 (`GRTW2_passPE3_report.md`, commit 9bd938f; target
> ffa1e57) — 0 CRITICAL, 1 JUSTIFICATION GAP (minor; P1, CONFIRMED by
> construction + probe), NOT CLEAN. PE3 also CONFIRMED: LEMMA W2-ID1's
> statement and proof SOUND (re-derived from the §3.4 display, valid for any
> recorded pair with ξ = 1); (OPEN-2a) exactly the m ≥ 2 inductive step the
> re-scope warrant needs — nothing weaker suffices, nothing stronger
> smuggled; the 36+2 census exact (recomputed from the committed JSON with an
> independent is-one test — 36 fully derived = 16 r = 2 + 16 r = 3 + 4 r = 4,
> the 2 instance-warranted = I4A/I4B r = 5); the P2 sign revert faithful at
> source (tex 1431/1373/1447/1201 line-exact, shift computation re-derived,
> no k ↦ −k gloss) and the anti-re-flip records adequate; the P3 pairing
> dictionary-correct; machine leg re-run exit 0, 6,403/0, 17 GREEN,
> bit-identical mod timing, both seals intact; FRESH LEG (route unused by
> PE1/PE2) — own tower-field arithmetic + own §3.4 evaluator vs the committed
> ledger modulo the support stabilizer at FULL roster scope, 22/22 (incl. the
> invisible-twist I4B r = 4 consistent and T3B/T3F r = 4 exact) + the I4B
> r = 5 boundary reproduced from scratch. …”

**CONDITIONALITY:**
(a) **PE3's confirmation list is the arc's densest**: five separate re-derivations, including “**(OPEN-2a) exactly the m ≥ 2 inductive step the re-scope warrant needs — nothing weaker suffices, nothing stronger smuggled**”. **That is a hostile pass certifying that a BOX is the right size** — neither over- nor under-claimed.
(b) **The 36 + 2 census is recomputed by an independent is-one test** ✓ audited at `.05`.
(c) **The four-part cure (a)–(d) is where the forward-direction scoping happens**, and part (d) is a *verbatim re-read* of every consuming surface — “each consume ONLY the proved direction — agreeing with PE3 §P1 "blast radius: contained"”.
(d) **The alternative cure is refused with a reason** (`.27`(b)) — pinning a ξ = 1 preference would misdescribe the frozen instrument. **This is the sweep's clearest instance of text being kept honest to a machine rather than the reverse.**
(e) **`STALE-SELF-DESCRIPTION`** on “counter 0/2 … W2-PE4 … next”.
(f) **The r3 sweep was INCOMPLETE and r4 says so**: “The r3 sweep stopped at PE3's four listed sites; three same-species surfaces still carried the two-sided … vocabulary” (1283–1285, shard 2), with the lesson “a species sweep must exhaust the species, not stop at the reviewer's site list”. `SUPERSESSION KIND: inventory completion`.

*Arithmetic audit (rule 22).* PE3's census decomposition `36 = 16 + 16 + 4` ✓ **exact** (`.05`); `36 + 2 = 38` ✓; `38 + 6 = 44` ✓. “0C + 1G” = 1 finding ✓ and one bullet ✓ (plus three ungraded observations o1/o2/o3, of which o3 “accrues to JA's ledger, not this note's; no edit” ✓).

**DERIVATION:** Round record.

**RESOLUTION TRACE:** statement 1197–1257 · the cure's four parts → `.31`, `.32`, `.33`, `.05` · the sweep's incompleteness 1283–1309 (shard 2).

PINS: `9bd938f` ✓ `ffa1e57` ✓ — 2/2.

**TEETH:** **PE3's FRESH LEG on a route unused by PE1/PE2** — own tower-field arithmetic + own §3.4 evaluator at full roster scope, 22/22, plus the I4B r = 5 boundary reproduced from scratch. **Disposition: executable regression on a third decorrelated instrument; and the counter-instance (`.32`) is a fired planted construction from the same pass.**

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

`[TABLE — compiler ledger]` Counts are `grep -cF '<designation>' <file>` at HEAD; artifacts and print files are existence-verified.

| # | Target : designation / file | Count / status | Role in this shard |
|---|---|---|---|
| 1 | `GRTJC_PROOF_2026-08-08.md:TR-3′-GEN` | **8** | The corpus's two-operator dictionary, OPEN at general order — route (1) of the adjudication and the W-1 perimeter (`.34`, `.39`) |
| 2 | `spec/HYPOTHESIS_LEDGER.md:HYP.139` | **20** | The ledger row for the W-1 transport (census I-4), class MATH, ATTEMPT (`.39`) |
| 3 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` | PRESENT | census row I-4 L48 and §5 L131 — the row's WHERE |
| 4 | `lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md` | PRESENT | [ILN]† S0.1/S0.2, consumed verbatim (`.08`, `.40`) |
| 5 | `lean/notes/openmath/GRTWELD_PROBE_2026-08-08.md` | PRESENT | the probe that falsified W-2's byte-equality branch (`.04`) |
| 6 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` | PRESENT | the blueprint junction §3.2 (`.04`) |
| 7 | `docs/references/HigherNewton.tex` | PRESENT | the GMN print; anchors tex 1028, 1166–1258, 1257–1283, 1285, ~1291, 1288, 1373, 1431, 1447, 1497, 1719, 2053 (`.06`) |
| 8 | `docs/GMN_citations.md` | PRESENT | the project's Def-2.12 cite mapping (`.06`) |
| 9 | `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` | PRESENT | [JB], route (2) of the adjudication; §0M row 15 the fold target (`.24`, `.34`, `.41`) |
| 10 | `lean/notes/openmath/OPEN2ATTACK_2026-08-08.md` | PRESENT | the unit that NARROWED (OPEN-2a) (`.33`) |
| 11 | `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` | PRESENT | the Σ-LAW supplier that PROVED (OPEN-2a) forward (`.33`) |
| 12 | `lean/notes/openmath/WELDMASTER_2026-08-08.md` | PRESENT | (M4)'s W2-C3 face, the fold target (`.41`) |
| 13 | `verification/openmath/grt_w2_checks.py` | PRESENT | the sealed runner (`.07`, `.32`, `.37`) |
| 14 | `verification/openmath/grt_w2_checks_output.txt` | PRESENT | artifact |
| 15 | `verification/openmath/grt_w2_checks_results.json` | PRESENT | artifact (the drift-recovery subject, `.41`) |
| 16 | `verification/openmath/iterlawn_pe_reimpl.py` | PRESENT | the enumeration-order source of the counter-instance (`.32`) |
| 17 | `GRTW2_passPE1_report.md` … `GRTW2_passPE4_report.md` | 4/4 PRESENT | the four hostile passes (`.03`, `.41`–`.43`) |

**Designations counted but NOT emitted as XREFs (2):**
- **`/tmp/w2_pe3_fresh.py`** — a temp path cited at `.32`; **not present and not expected to be**. Marked **UNPINNED** per rule 23.
- **§-anchor and line pointers** (`§0M row 15`, `WM line 88`/`line 111`, `iterlawn_pe_reimpl.py line 220`/`line 311`, `grt_w2_checks.py lines 135–163`) — location pins, not designations. **One of them was corrected in-arc** (`164 → 163`, `.32`) and **one annotated for drift** (`WM line 88 → 111`, `.42`), which is evidence the class is checked.

**Commit pins verified with `git cat-file -t` (all → `commit`): 22/22** — `874d26b`, `5463f2a`, `083adff`, `8d5e3fa`, `79e796b`, `ffa1e57`, `9bd938f`, `79d1d9c`, `e92cb22`, `ba2c47c`, `9d8aba0`, `adc6cf3`, `5054d69`, `66b3498`, `bd82766`, `8064ae3`, `59c1ff2`, `6b24942`, `6e57e03`, `55f7416`, `a6f7653`, `f8c2c09`.

**Hash pinning quality (rule 23).** The runner sha256 `71f8fc90f7543fd3…` is **truncated at all five occurrences** — **UNPINNED**, despite being the note's most-verified object (four passes checked it byte-identical). **This is the shard's one systematic pinning weakness**: the freeze is verified four times and recorded with an unverifiable hash prefix. Recorded as source defect 6.

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

`[TABLE — compiler ledger]`

| Consumer | Verified target | Shard-1 supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| WELDMASTER (accepted) | (M4)'s W2-C3 face, pinned `[W2]@5463f2a` | `.29` | The face quotes W2-C3's pre-re-scope wording; the as-of pin makes it drift-proof and PE1 adjudicated it carries the conditionality BY CITATION | **Not landed by GRTW2** — recorded as owed to the orchestrator (`.41`); **EXECUTED out of range** at the 2026-08-08 fold-carry annex (WELDMASTER annex O-1), after WM's own acceptance `66b3498` ✓ |
| GRTJB (accepted) | §0M row 15's subordinate cell; §0M column (d) | `.24`, `.29` | Column (d) already consumes the REPAIRED W2-C1a pairing (PE1 §C.4) | **Not landed by GRTW2**; **EXECUTED at `5054d69`** ✓ (GRTJB fold-annex erratum E-2) |
| The W-1 dictionary unit | — | `.14`, `.16`, `.39` | W2-L3 in PROVED FORM at level 1 + HR-REC as the transfer shape; **W-1 at orders ≥ 3 NOT advanced** | **Intended consumer; the unit does not exist as a consumer.** The corpus records the transport at **ATTEMPT, class MATH** (HYP.139 / census I-4) |
| The W-5 tree unit | — | `.36` | §5.4's carry analysis is “its opening move, not its proof” | Intended; NOT unlocked (`.39`) |
| OPEN2ATTACK / SIGMALAW | (OPEN-2a) | `.33` | Two later units narrowed then PROVED (OPEN-2a)'s forward direction at m ≥ 2 | **Inbound**, landed as orchestrator annexes on this note (shard 2) |
| LIFTCORNER (accepted) | the shift-descent | `.20` | The acceptance record names “the accepted LIFTCORNER's shift-descent consumption” | Not landed by GRTW2 |

**The last column is not an inference.** GRTW2 states the protocol twice verbatim — “**accepted texts are NEVER edited by this unit**” — and records fold implications rather than executing them. **Both owed folds were later executed by the orchestrator**, and the annex closing the pair says “Nothing else in the r1 record remains orchestrator-owed.” **Zero dated consumption appends are claimed landed by this note, and none is invented here.**

---

## 4. NON-IMPORTS

`[TABLE — compiler ledger]` The note's explicit negative fences homed in lines 1–1260.

| Fence | Explicit material NOT imported, NOT proved, or NOT claimed | Unit |
|---|---|---|
| New print transcription | “this note adds **NO new print transcription**” — the transcription risk is the sealed probe leg's | `.06` |
| An independence proposition | “**no independence proposition is among this note's consumed anchors**”; taking one “would be a NEW consumption … with its own transcription and audit” | `.06`, `.33`, `.34` |
| The ℓ-orbit reading | “nothing downstream consumes the orbit reading — clause 3 removes the ambiguity by transporting the type”; the section “stands review-owed” | `.26` |
| The scalar form off (C-coll) | W2-BOX-1: “the exact law is (HR-REC), **the scalar form is proved only on (C-coll)**” | `.23` |
| The chain level above r₀ | W2-OPEN-2: “**OPEN**, instance-confirmed”; “not derivable from the accepted corpus (four-route adjudication displayed)” | `.33`, `.34` |
| The value layer | W2-OPEN-1: “**instance-confirmed, not proved**”; the carry analysis “is NOT claimed here” | `.35` |
| Per-pair overflow identification | `[r1, F7]`: “asserted per-mechanism and **not machine-keyed pair-by-pair**” | `.36` |
| Independent TW-STRICT | “TW-STRICT is SAME-ADJACENT evidence given TW-ADM … **NOT two independent 44/44 legs**” | `.30`, `.37` |
| W-1 at orders ≥ 3 | “**W-1 at orders ≥ 3 is NOT advanced**”; “Nothing here … advances W-1's operator dictionary beyond the level-1 value dictionary” | `.05`, `.39` |
| W-5, W-6..W-9, J-D, Lean | “**NOT unlocked**: W-5 …, the J-C block W-6..W-9 (no gr claim anywhere here; BLOCKED-ON-CARRIER-TIE stands), J-D counts, and every Phase-B Lean obligation. The P0 application gate stands.” | `.39` |
| Accepted-text edits | “accepted texts are **NEVER** edited by this unit” (twice) | `.41`, `.42` |
| A pinned selection rule | the ξ = 1 preference is deliberately NOT pinned, because “a pinned preference would misdescribe the note's own machine bracket off-roster” | `.27`, `.32`, `.43` |
| The converse | “the converse stays UNCLAIMED”; UNPROVED at every m | `.31`, `.32`, `.33` |
| PARI on equal characteristic | “F_p[[t]] rows have no PARI leg (displayed deferral, inherited)” | `.40` |

---

## 5. Teeth inverse table

`[TABLE — compiler ledger]`

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **CK-MM** (4,396 integer + element samples) | `.13`, `.16`, `.09` | Executable regression — the largest family; **it is what makes “only the naming was off” checkable** |
| **CK-HR1** (156) | `.12` | Executable regression |
| **CK-VD1** (156) | `.14` | Executable regression — the level-1 dictionary, the note's one PROVED gift to W-1 |
| **CK-REC** (55 nodes) | `.16` | Executable regression against an independent semantic simulator |
| **CK-SLOT / CK-SLOT-M1** (44 / 16) | `.18`, `.17` | Executable regression; the non-perimeter rows are checked against the recursion, not the scalar form |
| **CK-XI** (22: 21 perimeter + 1 recorded boundary) | `.19`, `.21`, `.23`, `.25` | Executable regression — **checks that the displayed pair SATISFIES the orbit equations, which is exactly the weakened claim `.21` makes; it does NOT check that a scalar orbit must exist** (the gap E5 finding 2 exposes) |
| **CK-BYTE** (28: 22 walked + 6 SKIP recorded) | `.22`, `.31` | Executable regression, with the walk/no-walk split disclosed |
| **TW-RATIO / TW-ADM / TW-STRICT** (44 each) | `.29`, `.30`, `.33` | Executable regression — **but TW-STRICT is SAME-ADJACENT given TW-ADM, self-reclassified; not three independent legs** |
| **TW-F3 / TW-F3b** (684 / 684) | `.35`, `.28` | Measurement — the probe's 96 RED all GREEN, with an unchanged control |
| **TW-PARI / TW-QO** (12 / 7) | `.29` | Executable regression against PARI; **the seal's “PREDICT 24/24” is a disclosed miscount** (`.37`) |
| **CK-T3E** (2, both directions) | `.36` | Executable regression, **with the per-pair overflow identification explicitly not machine-keyed** |
| **MT-TW** (2) | `.29`, `.34` | Planted mutant — a garbled character (ξ·z₁) caught on both designated rows; **fired** |
| **probe F0 / F2 / F2-orbit / F4 / F3** (21, 45, 45, 24, 96 RED) | `.12`, `.24`, `.25`, `.28`, `.35` | **Foreign-note evidence** — and the probe's 6 F2 FAILURES are the evidence for W2-C1a's chamber qualifier, i.e. a foreign instrument's red rows became this note's hypothesis |
| **PE2's fresh leg** (16/16 at m = 1 + hand T3B/T3F) | `.19`, `.42` | Executable regression on a decorrelated instrument |
| **PE3's fresh leg** (own tower-field arithmetic + own §3.4 evaluator, 22/22 + I4B r = 5 from scratch) | `.23`, `.43` | Executable regression on a third decorrelated instrument |
| **PE3's counter-instance** (K₁ = F₄, ψ₁ = y³+ζ) | `.32`, `.31`, `.33` | **Planted counter-instance; FIRED against the note's own converse** |
| **PE4's selection-geography leg** (33,408 / 0 over 4,173 monic irreducibles × 7 fields; W2-ID1 forward 29,223 grid points / 0) | `.31`, `.32` | Executable regression, **exhaustive**; the r3 disclosure condition confirmed the EXACT characterization |

**PROOF-ONLY rows (rule 16), with the note's own coverage-hole sentence:**

| Unit | Coverage hole, in the note's words |
|---|---|
| `.26` (§4.3) | “This parametrization stands **review-owed** (probe fence inherited)” — no tooth, by design |
| `.33` (W2-OPEN-2(a)–(b)) | “**OPEN**, instance-confirmed 44/44 (live region = the 6 above-twist junction-levels)” |
| `.35` (W2-OPEN-1) | “**instance-confirmed, not proved**”; the carry analysis “is NOT claimed here” |
| `.23` (the scalar form off (C-coll)) | W2-BOX-1: “the scalar form is proved only on (C-coll)”; “exactly 1 boundary junction” on the roster |
| `.36` (the 24 overflow pairs) | `[r1, F7]`: “asserted per-mechanism and not machine-keyed pair-by-pair” |
| `.39` (W-1 at orders ≥ 3) | “W-1 at orders ≥ 3 is **NOT advanced**” — a negative claim, no tooth possible |

**AUDIT-disposition rows (rule 27):**

| Finding | Unit | Class |
|---|---|---|
| Clause 3's warrant applies clause 1 off its own perimeter (PE1 F1) | `.30` | in-house hostile pass — the arc's founding finding |
| W2-C1a's unqualified statement has 6 probe failures (PE1 F2) | `.24` | transfer audit — a foreign instrument's red rows |
| Three machine counts copied across notes without reconciling rosters (PE1 F3) | `.18`, `.22` | arithmetic recount |
| A sealed docstring preregisters a sample count the family does not have (PE1 F4) | `.37` | in-house instrument audit |
| An r-indexed name collides with a level-indexed element (PE1 F5) | `.23` | in-house hostile pass |
| A naming parenthetical conflated two opposite-signed print exponents (PE1 F6 → **reverted** at PE2 P2) | `.13`, `.26` | transfer audit at source — **and the reversal is itself a transfer audit** |
| “recorded ξ = 1 ⟹ byte-equal” is not definitional (PE2 P1) | `.30`, `.31` | in-house hostile pass |
| The premise pairs keys of different degrees (PE2 P3; **recurs and is caught again at E5 finding 3**) | `.09`, `.33` | in-house hostile pass, then decorrelated-model audit |
| The identification is two-sided in the text and one-sided in the proof (PE3 P1), **with a constructed counter-instance** | `.31`, `.32` | decorrelated construction |
| The r3 species sweep did not exhaust the species (PE4 P1) | `.38`, `.39` | in-house hostile pass |
| An annex falsely closed W2-OPEN-2 (E5 finding 1) | `.33` | decorrelated-model audit — **a CRITICAL against a ledger entry, not the proof** |
| HR-REC does not force geometricity (E5 finding 2) | `.25`, `.18` | decorrelated-model audit |
| “same induced valuation data” contradicts the note's own route (3) (E5 finding 4) | `.29`, `.34` | decorrelated-model audit |

**Both-direction audit.** Every row guards at least one unit; every toothed unit appears. Units with **`TEETH: NONE`** — `.01`, `.02`, `.06`, `.08`, `.26`, `.39`, `.40` — are headlines, declarations, hypotheses, fences or negative claims. Units flagged **Indirect** — `.11`, `.20` — ride the composite families. **Zero battery-row orphans; zero toothed-unit orphans; six signed PROOF-ONLY units; thirteen AUDIT-class findings across six passes.**

---

## 6. BOUNDARY SELF-AUDIT

GRTW2 is prose-with-blockquotes like GENHN and HE3, but its distinguishing feature is **bracket nesting depth**: four in-place rounds plus two out-of-range append layers, with up to five supersession layers on one sentence (`.05`). The boundary problem is therefore not “where does a statement end?” but **“which layer of a nested bracket is a unit, and which is a field?”**

### 6.0 The rule applied

> **A unit is the smallest span carrying one complete claim together with its proof obligations.**

Four tests as before, plus a fifth this note forced:

**(5) Does the span carry its OWN supersession CHAIN, distinct from its host's?** A `[rN]` bracket that merely re-scopes its host is a CONDITIONALITY field; a `[rN]` block that states a new claim, has its own targets, and is cited from elsewhere is a unit. `.30` (the honest re-scope) and `.32` (the converse's boundary) are units by this test; the dozens of one-clause `[r3]`/`[r4]` scopings are fields.

### 6.1 Boundaries drawn, with the arguable ones recorded both ways

**1. The Grade cap (`.05`) kept WHOLE, with its five-layer chain in CONDITIONALITY.** *Candidate A:* split by clause — clause 1's cap, clause 2's cap, clause 3's cap. *Candidate B (chosen):* one unit. **Reason:** the three caps share one census (44 junction-levels) and one governing sentence, and the `[r2, P1]` bracket that partitions 38 into 36 + 2 spans clause 3's cap and the roster claim jointly. Splitting would put one census in three CONDITIONALITY fields. *Cost:* the shard's longest CONDITIONALITY, with a five-member CHAIN.

**2. `.30` (the `[r1, F1]` honest re-scope) as a unit, not a field of `.29`.** **Test 5, decisively.** It states the grade split, carries its own census, has its own `[r2]`/`[r3]`/`[r4]` sub-layers, and is cited by designation from §6.1, §6.2, §6.3 and §7. *Candidate A:* fold into W2-C3's CONDITIONALITY. *Rejected* — four other units point at it.

**3. `.32` (the converse's honest boundary) as a unit.** Test 1 and 5: it is a `run-record` with a quoted construction, its own line-figure correction (`[r4, o-c]`), and its own roster-invisibility argument. *Candidate A:* part of W2-ID1's CONDITIONALITY. *Rejected* — it is cited from `.31`, `.33` and §9, and PE4 re-derived it independently.

**4. W2-OPEN-2 and (OPEN-2a) kept in ONE unit (`.33`), with the four-route adjudication split out (`.34`).** **The shard's most arguable call.** *Candidate A:* three units — the box, the sub-clause, the adjudication. *Candidate B (chosen):* two. **Reason:** (OPEN-2a) is explicitly *inside* the box's premise — the note says so: “which is why the sub-clause lives INSIDE the box as part of its premise rather than being imported silently”. Splitting them would undo a deliberate structural decision. **The adjudication IS split out** because it is cited independently (§7 F1, §8's fifth-route hunt) and because it contains route (3), which E5 later uses against a *different* unit (`.29`). *Cost:* `.33` carries two CHAINs.

**5. The three §3.4 remarks as three units (`.20`, `.21`, `.22`).** Test 4: three different predicates — a structural identification, a non-uniqueness caveat, a byte law. **Remark 2 (`.21`) turns out to be the seed of the whole r3 arc**, and remark 3 (`.22`) carries two count corrections. *Not arguable in hindsight.*

**6. The four round blocks as units (`.41`–`.43` + §10 in shard 2).** Test 1 and 3: each records a distinct pass with its own findings, confirmations and freeze verification, and each is cited by designation from S-STATUS. *Weakly arguable* — they are records. *Chosen* because **each contains confirmations found nowhere else** (PE2's fifth-route hunt, PE3's “nothing weaker suffices, nothing stronger smuggled”, PE1's full re-derivation).

**7. `.39` (the consequence display) as a unit, and the W-1 status compiled inside it.** Test 4: it is the consumer-facing face with four carry items. **The W-1 ATTEMPT status is compiled in its CONDITIONALITY rather than as a separate unit** — *arguable*: `.09`-style compiler-assembled status units exist in the HE3 shards. *Chosen inline* because §6.3's bullet 1 already states the note's own limit in the note's own words; the ledger row supplies the corpus status, and the two agree. **Honest cost: a reader who wants the ATTEMPT status must read `.39`'s CONDITIONALITY, not a headline unit.**

**8. The claims table (`.38`) emitted with a COMPILER-ADDED “TERMINAL grade at HEAD” column.** **The shard's one addition to a source table.** *Candidate A:* transcribe the two source columns only. *Candidate B (chosen):* add a third, clearly labelled as compiler-computed, because **five of twelve rows have moved out of range** and a chapter cut reading the source grades alone would carry five stale gradings. The added column is marked “compiler-computed … **not in the source**” and every entry cites its unit.

### 6.2 Merges deliberately NOT made, and three conflations blocked

- **`.13` and `.26` stay separate** (W2-L2's naming parenthetical and §4.3's sign): they are the two halves of one revert, at two sections, with two anti-re-flip records. The note deliberately split the conflation across both sites.
- **`.35` and `.36` stay separate**: W2-OPEN-1 is the open value-layer box; W2-T3E is a proved mechanism that *explains one row of it*.
- **BLOCKED CONFLATION 1 — “ACCEPTED 2/2” vs the open boxes.** The acceptance enumerates “W2-OPEN-2/OPEN-2a as the note's fenced OPEN box — … **accepted AS A BOX, not as a theorem**”. A chapter cut reporting 2/2 without (F3)'s enumeration would over-report.
- **BLOCKED CONFLATION 2 — (OPEN-2a) vs W2-OPEN-2(a)–(b).** These are different statements about different junctions, and **an annex conflated them; E5 finding 1 WITHDREW the conflation.** `.33` keeps them apart with two CHAINs.
- **BLOCKED CONFLATION 3 — the forward direction vs the identification.** “recorded ξ = 1 ⟹ byte-equal” (proved, now at every m) vs “first recorded ξ ≠ 1 junction = first byte-divergence” (two-sided, converse UNPROVED at every m). **The whole r3/r4 arc is the note un-conflating these**, at seven sites.

### 6.3 Format notes (v3 rules exercised, and two gaps)

Rules 11, 12, 14 (double-emission at `.37`, `.38` — both source tables Markdown, emitted once as `[TABLE]` per the tables-are-units clause, with `.38` carrying a labelled compiler column), 15 (no NEAR-MISS needed), 16 (PROOF-ONLY ×6), 17 (predicate C, six streams), 18 (**all eight kinds used**), 19 (`run-record` at `.32`, `instrument-record` at `.07`), 20 (all four disclosure labels), 21 (**three freeze predicates, the third — the acceptance-scope enumeration — new to this note**), 22 (**arithmetic audits on twenty-one displays; twenty reproduced, one found a discrepancy** — see below), 23 (22 commits verified, 17 files verified, **the runner sha256 UNPINNED at all five occurrences**), 25 (CHAIN with TERMINAL ×9, one of length five), 26 (STALE-SELF-DESCRIPTION ×6), 27 (AUDIT ×13 across six passes), 28 (SERIES GRTW2-GRADE-ARC, seven members, one in this shard's range plus five round-block members and the terminal in shard 2).

**Two gaps found in v3:**

1. **Rule 21 has no member for an ACCEPTANCE-SCOPE ENUMERATION.** (F3) — “WHAT IS ACCEPTED: … and W2-OPEN-2/OPEN-2a as the note's fenced OPEN box, **accepted AS A BOX, not as a theorem**” — is not a text-freeze and not an instrument-freeze; it is a statement about *which claims a grade covers*, and it is the only thing standing between “ACCEPTED 2/2” and an over-read. **Proposed fix: add `acceptance-scope enumeration` to rule 21's freeze-predicate list, with the requirement that any unit reporting a grade quote it.**

2. **Rule 22's arithmetic audit has no protocol for a total that does not reconcile.** `.37`'s sample column sums to **6,396** against a headline **6,403** (source defect 4). Nothing is thereby false — every family is GREEN — but the audit found a 7-sample gap it cannot close from the note. **Proposed fix: an explicit `AUDIT-GAP` disposition, distinct from “reproduced” and from “unverifiable”, for a computed total that contradicts a displayed one by a stated amount.**

---

## 7. SHARD NOTES

- **Corrections landing on this range from out of range (nine).**
  (1) **Fold-carry annex (2026-08-08)** → `.41`'s two owed folds, both EXECUTED.
  (2) **OPEN2ATTACK annex** → `.33` ((OPEN-2a) NARROWED to one lemma, “NOT closed”).
  (3) **Σ-LAW annex** → `.33`, `.31`, `.05` ((OPEN-2a) forward PROVED at m ≥ 2); also **corrects a downstream reading of `.19`'s characters** (the ξ-formula composite, not the bare interior twist).
  (4) **Annex #2 + its ERRATUM** → the Σ-LAW's machine figures, twice corrected (a transposition caught by a later pass).
  (5) **Annex #3** → the supplier upgrade; **and its final sentence over-claimed**.
  (6) **E5 finding 1** → `.33`: the ANNEX #3 sentence **WITHDRAWN**; W2-OPEN-2(a)–(b) confirmed OPEN on six junction-levels.
  (7) **E5 finding 2** → `.25`, `.18`, `.05`: THEOREM W2-C1's universal reading **SUPERSEDED** by W2-C1-CORR; census re-displayed **37 + 1 + 6**.
  (8) **E5 finding 3** → `.33`, `.09`: the key-carry index fix `Φ_q ⇝ Φ_{q−1}`, the second occurrence.
  (9) **E5 finding 4** → `.29`: W2-C3(iii)'s equivalence wording **SUPERSEDED** by ledger-equivalence.
  Items (2)–(3) are **licenses**; (6)–(9) are **replacements**; all four E5 items are “awaiting sol discharge (cert3)”.
- **Range-edge audit.** Line 1257 closes §9's Freeze; 1258 blank; 1259 `---`; 1260 blank; 1261 opens `## §10.` **No source unit is cut at the edge**; the manifest boundary falls on a section break.
- **Outside-HOME material used only as resolver:** §10 (r4), the ACCEPTANCE RECORD, the five-annex stack, and the 2026-08-12 C5/E5 adjudication with its four certifier corrections. Shard 2 owns them.
- **Protocol versus supply.** §§1–9's supply set is inventoried; **no consumption append is claimed landed on any note by GRTW2**, and none is invented. Six inbound streams are recorded at their targets.
- **Numbering.** Temporary IDs `EFF.GRTW2.s1of2.01`–`.43`. **Merge hazards to flag:**
  (a) **`.38`'s claims table carries a COMPILER-ADDED column**; a merge must keep it labelled as such.
  (b) **Five claims-table rows are stale at HEAD** (W2-C1, W2-C3(iii), W2-ID1's m = 1 restriction, W2-OPEN-2's residual surface, the 38/44 census).
  (c) **The four E5 corrections are “awaiting sol discharge (cert3)”**; do not present them as confirmed.
  (d) **(OPEN-2a) and W2-OPEN-2(a)–(b) must never be merged** — an annex did, and it took a CRITICAL to undo.
  (e) **The runner sha256 is UNPINNED**; four passes verified a hash the note truncates.
  (f) **`.37`'s sample total does not reconcile** (6,396 vs 6,403).
  (g) **SERIES GRTW2-GRADE-ARC** terminates in shard 2 at 2/2.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — “ACCEPTED 2/2” and three open boxes are simultaneously true, and the spec cannot decide how a chapter cut presents that

The note is **ACCEPTED at 2/2** (F1), and the acceptance **enumerates an OPEN box among what it accepts** (F3): “W2-OPEN-2/OPEN-2a as the note's fenced OPEN box — the weld's one open lemma, **accepted AS A BOX, not as a theorem**.” Three further surfaces are open or fenced at HEAD: **W2-OPEN-1** (value layer), **W2-BOX-1** (scalar form off (C-coll)), **§4.3** (review-owed convention). **Decision needed: whether a chapter cut may cite W-2 as accepted without reproducing (F3)'s enumeration.** This shard reproduces it in the header and at every grade-bearing unit.

### OPEN-CALL 2 — the four E5 certifier corrections are landed-but-undischarged

The 2026-08-12 append closes: “Ledger: row 23 → **all four repairs folded, awaiting sol discharge (cert3)**.” Two of the four **change a theorem's scope** (W2-C1 → W2-C1-CORR; W2-C3(iii) → ledger-equivalence), one **withdraws a status claim** (W2-OPEN-2), one **fixes an index** in a discharge route. **Decision needed: whether a chapter cut may consume landed-but-undischarged certifier corrections as current** — the same question `spec/EFF-GENHN-s2of2.md` OPEN-CALL 4 and `spec/EFF-HE3-s2of2.md` OPEN-CALL 2 raise. **All three should be answered together.**

### OPEN-CALL 3 — the W-1 transport ATTEMPT row: compiled status and what remains undecided

**Compiled status (verified, not inferred):** W-1's transport of the harness `w` and `𝑅` to the FGMN objects is at **ATTEMPT grade, class MATH, at full strength as of 2026-08-14** — `spec/HYPOTHESIS_LEDGER.md` **HYP.139** (count **20**), whose WHERE is **`docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4 L48 and §5 L131** ✓ file present. The ledger's own words: “**W-1 (harness w, 𝑅 → FGMN objects) stays ATTEMPT**”; “a **proof obligation, not a citation one**”; “This row is the **live residue that does NOT discharge with HYP.148 by a transcription fold**”; and the v6 arc note: “**UNCHANGED, MATH at full strength** — a route that *passes* its hostile arc would retire this row …, but the arc has not yet passed.”
**GRTW2's own position agrees and adds one proved increment:** W2-L3 is the level-1 value dictionary **in proved form**, HR-REC is the exact transfer shape, and “**W-1 at orders ≥ 3 is NOT advanced**” (`.39`), restated in the Grade cap (`.05`). Its route (1) independently records the corpus's pricing: **TR-3′-GEN** (count **8** in GRTJC) “is OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}, with its units-only phrasing **PERMANENTLY REFUTED** on the order-3 stratum (ii)”.
**What is undecided and needs a decision:** (i) whether the merged spec carries the ATTEMPT row as a unit of its own or inside `.39` (this shard chose the latter — see §6.1 item 7); (ii) whether GRTW2's level-1 increment should be recorded against HYP.139 as partial progress, given that the row's consumer chain runs through GENHN-BOX-2/HYP.148 rather than through W2-L3; (iii) whether the candidate retiring route (HYP.149's WELD-ZERO fold, at **clean-pass 1 of 2**) changes anything here — **it does not yet**, and this shard records it as not-yet.

### OPEN-CALL 4 — two cross-note consumer claims were not independently adjudicated

(a) **`.24`'s consumer note**: “the accepted [JB]'s §0M column (d) already consumes the REPAIRED pairing … so no accepted text is falsified by this qualifier”, adjudicated by PE1 §C.4. **This compiler verified GRTJB exists but did not open §0M column (d).**
(b) **`.41`'s fold implications**: both were recorded as EXECUTED out of range, at `5054d69` and at the fold-carry annex. **The commits verify; the executed text was not read.**
**Decision needed: whether the merge run performs these two reads, or records them as inherited assertions.**

### OPEN-CALL 5 — the note's open-box COUNT is stated as unchanged through four rounds, and it did change out of range

`.40` says “open boxes unchanged in count” at r2, r3 and r4 ✓ true in range (four surfaces throughout). **Out of range the set moves**: (OPEN-2a) leaves it (proved), and W2-OPEN-2(a)–(b) narrows to six junction-levels. **Neither is folded back into the dependency line.** **Decision needed: whether the merged spec re-states the open-surface count at HEAD** (this shard's reading: **three open surfaces plus one review-owed fence** — W2-OPEN-1, W2-OPEN-2(a)–(b), W2-BOX-1, §4.3 — with (OPEN-2a) retired).

### OPEN-CALL 6 — the machine bracket's headline total does not reconcile with its own table

`.37`'s sample column sums to **6,396**; the headline at `.07` and the four Freeze paragraphs all say **6,403**. The family count (17) reproduces exactly. **The 7-sample gap is not closable from the note.** **Decision needed: whether the merged spec reports 6,403 (the note's figure, four times re-verified by hostile passes against the frozen artifacts) or flags the table.** This shard reports both and flags the gap as source defect 4.

### Recorded source defects (flagged, not silently repaired)

1. **`.09`/`.33`:** the P-index dictionary was misapplied **twice in the same box** — caught at r2 (P3, the premise) and again at E5 finding 3 (the Equivalent sufficient form), four months apart.
2. **`.29`:** W2-C3(iii) claimed “same induced valuation data” while the note's **own route (3)** (`.34`) proves equal augmented valuations are unavailable. E5 finding 4's opening sentence: “The note itself proves that equality of augmented valuation functions is unavailable.”
3. **`.32`:** the roster-invisibility argument's `g = 2` half (“no support-stabilizing unit **with zero constant coefficient**”) is stated too tersely to check from the displayed text. PE4's exhaustive map supplies the fact by measurement instead.
4. **`.37`:** the machine-bracket table's sample column sums to **6,396**, not the headline **6,403** — a 7-sample gap with no decomposition in the note. (Family count 17 ✓ reproduces.)
5. **`.40`:** “open boxes unchanged in count” is true through the in-range arc and stale at HEAD (see OPEN-CALL 5).
6. **`.03`/`.37`/`.41`–`.43`:** the runner **sha256 is truncated at all five occurrences** — the note's most-verified object carries an unverifiable hash prefix.
7. **`.37`:** the sealed docstring preregisters “TW-PARI PREDICT: 24/24” against a 12-sample family — **disclosed** by the note as a seal miscount, not hidden.

### Fidelity audit

- Every CANONICAL STATEMENT is a verbatim source quotation; **no `[ASSEMBLED]` statements in this shard.** **No inverse, sign, quantifier, index, level, inequality direction, or implication direction was altered anywhere** — which matters unusually here, since the arc contains a sign flip and its revert, and both are quoted with their strike markers intact.
- **Strike-through and nested brackets are reproduced exactly.** Where a quotation compresses a deeply nested bracket, the elision is marked `…` and the elided layer is quoted at its own unit (`.05`, `.30`, `.33`, `.39`).
- Truncations inside quotations: used at `.30`, `.33`, `.39`, `.40`, `.42`, `.43`, all marked `…`; **no truncation removes a hypothesis, a quantifier, or a negation.**
- Terminal punctuation, ASCII display alignment and blockquote nesting are preserved.
- **Two source tables are emitted as `[TABLE]`** (`.37`, `.38`); `.38` carries one **clearly-labelled compiler-added column** (§6.1 item 8).
- **Twenty-one arithmetic audits were computed fresh** (rule 22) at `.05`, `.08`, `.09`, `.10`, `.11`, `.12`, `.13`, `.14`, `.15`, `.18`, `.19`, `.21`, `.22`, `.23`, `.24`, `.25`, `.26`, `.27`, `.29`, `.31`, `.32`, `.35`, `.36`, `.37`, `.41`, `.42`, `.43`. **Twenty reproduced the source exactly; one found a discrepancy** (`.37`'s 6,396 vs 6,403). Five produced findings the source does not state: the reconciliation of the r2 and E5 censuses (`.05`); the coincidence of the two “44”s (junction-levels and CK-SLOT samples, `.18`); the exact reproduction of E5's `ρ₁² = ρ₀ρ₂` criterion (`.25`); the exact reproduction of E5's degree argument for the index fix (`.09`); and the `16 r = 2 + 16 r = 3 + 4 r = 4 = 36` decomposition agreeing with PE3's independent recount (`.05`).
- **17 external targets verified** (2 by designation count, 15 by existence); **22 commit pins verified with `git cat-file -t` (22/22 → commit)**; **one temp path and one truncated sha256 marked UNPINNED**.
- Status and mathematical content are kept as distinct predicates, and this shard blocks three conflations explicitly (§6.2).
- Out-of-range material is used only to resolve in-range HOME units; shard 2 owns §10, the acceptance record, the annexes and the certifier corrections.
- **Honest limitation of this shard:** nine of the corrections that govern this range are physically in shard 2, and **four of them are “awaiting sol discharge (cert3)”** while **two change a theorem's scope**. Two cross-note consumer claims were not independently adjudicated (OPEN-CALL 4). Every affected unit quotes the governing text verbatim, so shard 1 is self-contained as a *reading*, but the merge must install the nine edges in §7 and answer OPEN-CALLs 1–3 before a chapter cut consumes W2-C1, W2-C3(iii) or the census.

EFF-GRTW2-s1of2 COMPILED: 43 statements / 17 xrefs verified / 6 open calls
