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

## 2. Statement inventory

62 units, contiguous, in effective-text order. FORM on every unit (tag-sparse genre).

### EFF.GENTOW1.01  [convention]

**CANONICAL STATEMENT:**

> “# GENTOW-1: composed entry budgets, inner refine transfer, composed window ledger
> ## ([GENHN-TOW-1] items (1), (2), (5) — proof attempt, BOX-CLOSURE campaign wave B1)”

**FORM:** title + subtitle.

**DERIVATION:** `[RECORD]` — the unit's identity and its charge target.

**CONDITIONALITY:** “proof attempt” is superseded by acceptance (`.59`); the item scope (1)/(2)/(5) is stable and is the note's supply set.

**RESOLUTION TRACE:** lines 1–2.

**TEETH:** XREF X01 — `GENHN-TOW-1` verified in `GENHN_PROOF_2026-08-08.md` at count **19**.

---

### EFF.GENTOW1.02  [repair-round record]  *(SERIES ARC, link 1)*

**CANONICAL STATEMENT:**

> “**2026-08-09 — COMPLETE at attempt grade 0/2 (hostile arc owed).
> Unit: GENTOW-1. Composed in per-section commits; machine leg
> sealed-then-verdict (S5).
> [ARC — passPE1 2026-08-09: NOT CLEAN, 1 GAP + 2 MINOR
> (GENTOW1_passPE1_report.md @ 606e85c); counter stays 0/2.
> GT1-r1 repair round 2026-08-09 (this commit): F-1 dated gauge
> annex — the corrected chat_t := lift(c_t·eta^{W(t)}) display
> pinned at the S0/S2/S3/S6 consumption sites (S7.1, per GENHN
> erratum 59c1966 + HETOW [r1]); m-1 P-1 SCORED GREEN 20/0
> (gentow1_r1_p1.py, S7.2); m-2 GENTOW-BOX-1 retirement
> back-pointer (S6). Sealed machine artifacts BYTE-UNTOUCHED;
> statements unchanged (manifest S7.4). Grade stays 0/2; PE2
> next.]**”

**FORM:** bold-headed status block with an embedded ARC bracket.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the counter is superseded twice (CHAIN-GRADE): → 1/2 (`.58`), → **2/2 ACCEPTED** (`.59`). “statements unchanged” is true of r1 and **false of the later appends** — four displayed statements are governed from outside (see §1's table). A consumer must not carry this sentence past 2026-08-09.

**RESOLUTION TRACE:** lines 4–16.

**TEETH:** `git cat-file -t 606e85c` = commit; `GENTOW1_passPE1_report.md` exists; `gentow1_r1_p1.py` exists and its output's last line reads `P-1 SCORED: 20 checks, 0 violations -- GREEN` ✓ — the “20/0” claim is exact.

---

### EFF.GENTOW1.03  [fence]

**CANONICAL STATEMENT:**

> “CHARGE (Asvin directive, ledger 2026-08-09: prove the boxes; a box
> survives only after genuine attempts fail): PROVE [GENHN-TOW-1] items
> (1) composed entry budgets (the GENHN-1 analogue at the composed key
> Phi_2, + the depth-3 node floor rider = item (6)(beta)), (2) the inner
> refine transfer (GENHN-4 one level up), (5) the composed window ledger
> (GENHN-3 at dv_2). Sources consumed (never edited — GENHN_PROOF's
> acceptance pass is live): GENHN_PROOF_2026-08-08.md S8 [r2] annex
> (LEMMA GENHN-T(b)': composed carrier (i), composed slot lemma
> GENHN-2' (ii), corrected leaf read (iii), stage shadow (iv)), S3.2
> LEMMA GENHN-1 + its [r2] corrected floor display (the r2-F2 form), S5
> LEMMA GENHN-3 + the f1>=3 band annex, S6.1 LEMMA GENHN-4, S9.1
> [GENHN-TOW-1]; machine recipes: genhnr2_supp.py (SUPP-A/B/C),
> genhn_pe3_fresh.py (FR1 e2=3 genre, FR2 q=3 f2=2 genre).”

**FORM:** bold-headed charge + import inventory.

**DERIVATION:** `[RECORD]` — the standing “prove the boxes” directive instantiated at three items.

**CONDITIONALITY:** “never edited — GENHN_PROOF's acceptance pass is live” is the standing supplier fence and is verified (N1: GENHN has zero GENTOW references). **The inventory is incomplete at HEAD**: the effective text additionally consumes GENHN's dated gauge erratum `59c1966` (added at r1, `.49`) and — for the S3 display — GENTOW5's `[GT5-r2]` corrected display (`.62`).

**RESOLUTION TRACE:** lines 18–30.

**TEETH:** all cited supplier objects exist; `genhnr2_supp.py` and `genhn_pe3_fresh.py` verified present in `verification/openmath/`.

---

### EFF.GENTOW1.04  [table]  `[TABLE]`

**CANONICAL STATEMENT:** the status table, source lines 34–40, transcribed:

| item | lemma | status |
|---|---|---|
| (1) budgets + node | LEMMA GENTOW-1 | PROVED (S2) |
| (1) rider: depth-3 floor (6)(beta) | COR GENTOW-1.1 | PROVED (S2.4) |
| (2) inner refine transfer | LEMMA GENTOW-2 | PROVED at mu2=2 pointwise; general mu2 layer-1 via graded frame (disclosed, GENHN-BOX-2 pattern) (S3) |
| (5) composed window ledger | LEMMA GENTOW-5 | PROVED (S4) |
| battery | gentow1_checks.py | GREEN 1,128 checks / 0 violations, 5/5 teeth (S5) |

**FORM:** table.

**DERIVATION:** `[RECORD]` of per-item status.

**CONDITIONALITY:** **the row-3 disclosure is the note's central honesty fence** and survives everything: GENTOW-2 is pointwise at μ₂ = 2 and graded-frame-conditional at general μ₂. The `.47` back-pointer routes that conditionality to GENTOW5 at ITS 0/2 grade — so the general-μ₂ leg is conditional on a 0/2 note even after this note reaches 2/2.

**RESOLUTION TRACE:** lines 32–40; the box at 547–561.

**TEETH:** the battery row is re-verified: the artifact's last lines read `=== VERDICT: GREEN -- 1128 checks, 0 violations (5.0s) ===` and five `tooth … fired` lines ✓.

---

### EFF.GENTOW1.05  [convention]

**CANONICAL STATEMENT:**

> “Outer genre (Q; e1, f1, mu1; h), key Phi' (deg D' = e1f1), dv = e1*v.
> Inner CS event on the level-1 stage read: side of dv-slope kappa2 =
> u2/e2 (gcd(u2,e2)=1, u2 > e2*D'h by the [r1] node floor), residual
> psi2^{mu2} over K = F_{Q^{f1}}, f2 = deg psi2, FULL side e2f2mu2 =
> mu1. Composed key Phi2 = Phi'^{e2f2} - Sum_{t<f2} chat_t
> n(u2(f2-t)) Phi'^{e2t}, monic, deg D2 = D'e2f2. … Composed ladder
> dv2 = e1e2*v. Composed basis {x^a Phi'^b : a<D', b<e2f2}; slot
> (a,b) at dv2-offset w(a,b) := a*e2h + b*u2; GENHN-2' (accepted
> annex): dv2(A(x0)) = min(e1e2*v(c_{a,b}) + w(a,b)) EXACTLY on the
> tower-node locus, one K2-digit per dv2-height, K2 = F_{Q^{f1f2}}.”

**FORM:** inline setting paragraph (§S0), with the GT1-r1 gauge pin elided here and emitted at `.06`.

**DERIVATION:** `[IMPORTED]` — “all from T(b)', restated for one-pass reading” (the section heading).

**CONDITIONALITY:** the FULL side `e2f2mu2 = mu1` is the standing scope; partial sides are item (4), untouched (`.46`). The node floor `u2 > e2D'h` is imported from GENHN-1's [r1] erratum and is consumed at four separate places (Step 0, Step 2, COR 1.1, S3's `a0 ≥ 0` claim).

**RESOLUTION TRACE:** lines 44–59.

**TEETH:** `GENHN-2'` is the accepted annex supplying the slot-min identity; the whole note's exactness claims ride it.

---

### EFF.GENTOW1.06  [definition]  *(CHAIN-GAUGE — TERMINAL, in-body site)*

**CANONICAL STATEMENT:**

> “[GT1-r1 GAUGE PIN
> (dated annex S7.1): chat_t := lift(c_t·eta^{W(t)}) with W(t) =
> floor((f2−t)·i(u2)/e1) — the CORRECTED display per GENHN's dated
> erratum 59c1966 (at f1 >= 2 per digit: the exact-height (LIFT)
> output L_{(f2−t)u2}(c_t·eta^{W(t)})), NOT the gauge-naive plain
> lift of c_t; at eta = 1 the two coincide. This pin governs chat_t
> at its uses below (S2 Steps 0/1/5, S3).]”

**FORM:** bracketed in-body pin at the key display.

**DERIVATION:** `[IMPORTED]` from GENHN's erratum, itself provoked by HETOW PE1 F-1.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of the S0 key display's coefficient. **The pin names its own consumption sites** (S2 Steps 0/1/5, S3) — an unusually disciplined supersession, and the full nine-site manifest is `.57`. The `f1 ≥ 2` clause routes to HETOW's (LIFT) no-overflow form, i.e. to `EFF.HETOW.18`.

**RESOLUTION TRACE:** statement lines 49–55; the dated annex at 598–629; the manifest at 678–692.

**TEETH:** `git cat-file -t 59c1966` = commit ✓. Cross-note: `EFF.HETOW.13`/`.14` compile the same correction from the finding side; the two entries agree on the formula `W(t) = ⌊(f₂−t)i(u₂)/e₁⌋` verbatim.

---

### EFF.GENTOW1.07  [definition]

**CANONICAL STATEMENT:**

> “THE ONE NEW CONSTANT: **E2 := e2f2u2** — the dv2-height of every
> side term of Phi2 (Phi'^{e2f2}(x0): e2f2*dv2(Phi'(x0)) = e2f2u2;
> lift term t: e2*u2(f2-t) + e2t*u2 = e2f2u2). E2 plays the role D'h
> played at level 1 (there the key's side height and dv(x^{D'})
> coincided at D'h; here they SPLIT: E2 > dv2(x^{D2}) = D2e2h =
> e2f2*(e2D'h), by u2 > e2D'h).”

**FORM:** bold-headed definition with an inline verification of the two term families.

**DERIVATION:** a two-case height computation, both cases displayed.

**CONDITIONALITY:** **the SPLIT is the note's structural novelty** — at level 1 the key's side height and `dv(x^{D'})` coincide; at level 2 they separate, and E2 (not `dv2(x^{D2})`) is the true floor. COR GENTOW-1.1 (`.25`) and the T-MUTFLOOR tooth both turn on this gap.

**RESOLUTION TRACE:** lines 61–66.

**TEETH:** **ARITHMETIC AUDIT, recomputed for all five families.** `E2 = e2f2u2` vs `dv2(x^{D2}) = D2·e2h = e1f1e2f2·e2h`: FAM-A5 `E2 = 2·1·5 = 10` vs `D2·e2h = 4·2 = 8` ✓; A7 `14` vs `8` ✓; B `1·2·3 = 6` vs `4·1 = 4` ✓; C `3·1·7 = 21` vs `6·3 = 18` ✓; D `6` vs `4` ✓. **All five match the note's own list “8/8/4/18/4 sits BELOW E2 = 10/14/6/21/6”** ✓ (`.11`(iv)) — computed here from the formulas, not read off the table.

---

### EFF.GENTOW1.08  [definition]

**CANONICAL STATEMENT:**

> “WEIGHT: for a monomial pi^v x^a Phi'^b Phi2^j define wt :=
> e1e2*v + a*e2h + b*u2 + j*E2. Note wt = dv2 of the evaluated
> monomial at any tower-node point where dv2(Phi') = u2 and
> dv2(Phi2) = E2 hold exactly; on the actual locus dv2(Phi2(x0)) > E2
> (S2.2), so wt is a LOWER bound with the j-graded part strict.”

**FORM:** bold-headed definition with a scope note.

**DERIVATION:** `[DEFINITIONAL]`, with the strictness of the j-graded part forward-referenced to GENTOW-1(d).

**CONDITIONALITY:** **wt is a LOWER bound, not an equality, on the actual locus** — the note is explicit, and the reason is exactly clause (d)'s strict field floor. Every “weight ≥ W” statement in S2 must be read as a lower-bound statement.

**RESOLUTION TRACE:** lines 68–72.

**TEETH:** the strictness is machine-checked as P-3: `GP-NODE` 171 row-checks of `e1e2·nfeltval(Phi2) > E2·pr.e` (STRICT) ✓.

---

### EFF.GENTOW1.09  [table]  `[TABLE]`

**CANONICAL STATEMENT:** the five constructed families, source lines 80–86, transcribed (source is a Markdown table):

| family | genre | q | Phi2 | u2 | E2 | dv2 | n |
|---|---|---|---|---|---|---|---|
| FAM-A5 | (2,1,4)->(2,1,2) | 2 | (x²−2)²−4x | 5 | 10 | 4v | 8 |
| FAM-A7 | (2,1,4)->(2,1,2) | 2 | (x²−2)²−8x | 7 | 14 | 4v | 8 |
| FAM-B | (2,1,4)->(1,2,2), K2=F4 | 2 | Phi'²−2xPhi'−8 | 3 | 6 | 2v | 8 |
| FAM-C | (2,1,6)->(3,1,2), e2=3 | 2 | (x²−2)³−8x | 7 | 21 | 6v | 12 |
| FAM-D | (2,1,4)->(1,2,2), K2=F9 | 3 | (x²−3)²+27 | 3 | 6 | 2v | 8 |

with the examples-first framing:

> “Five constructed tower families (per the standing examples-first
> discipline; recipes: genhnr2_supp SUPP-A/B + genhn_pe3 FR1/FR2 +
> fresh)”

**FORM:** table.

**DERIVATION:** `[DESIGN]` — constructed instances, per the standing examples-first directive.

**CONDITIONALITY:** **all five sit at η = 1** — disclosed at `.54` and added to GENTOW-BOX-2's coverage reading. The battery is therefore structurally blind to the gauge seam that the whole CHAIN-GAUGE is about.

**RESOLUTION TRACE:** lines 74–86; the blindness disclosure at 651–657.

**TEETH:** **ARITHMETIC AUDIT of every derived column, recomputed from the genre data:** `dv2 = e1e2·v` — A5/A7 `2·2 = 4v` ✓, B/D `2·1 = 2v` ✓, C `2·3 = 6v` ✓. `E2 = e2f2u2` — `2·1·5 = 10`, `2·1·7 = 14`, `1·2·3 = 6`, `3·1·7 = 21`, `1·2·3 = 6` ✓ all five. `n = mu2·D2 = mu2·D'e2f2` — A5 `2·2·2 = 8` ✓, B `2·2·1·2 = 8` ✓, C `2·2·3·1 = 12` ✓. Every column reproduces.

---

### EFF.GENTOW1.10  [run-record]  `[TABLE]`

**CANONICAL STATEMENT:** the budget tables. **Source display, verbatim** (fixed-width ASCII, v3 rule 14 double emission):

>     “FAM-A5 j=0: (0,0):6*  (1,0):5  (0,1):4  (1,1):4
>            j=1: (0,0):3   (1,0):3* (0,1):2  (1,1):1
>     FAM-A7 j=0: (0,0):8*  (1,0):7  (0,1):6  (1,1):5
>            j=1: (0,0):4   (1,0):4* (0,1):2  (1,1):2
>     FAM-B  j=0: (0,0):7*  (1,0):6  (0,1):5  (1,1):5*
>            j=1: (0,0):4*  (1,0):3  (0,1):2  (1,1):2*
>     FAM-C  j=0: (0,0):8*  (1,0):7  (0,1):6 (1,1):6 (0,2):5 (1,2):5
>            j=1: (0,0):4   (1,0):4* (0,1):3 (1,1):2 (0,2):2 (1,2):1
>     FAM-D  j=0: (0,0):7*  (1,0):6  (0,1):5  (1,1):5*
>            j=1: (0,0):4*  (1,0):3  (0,1):2  (1,1):2*”

with its header: “**THE BUDGET TABLES (machine output, gentow1_checks run of 2026-08-09; * = consumed pin).** v-floors per composed slot (a,b) at coordinate j”.

`[TABLE]` — transcription with the compiler's independent recomputation from GENTOW-1(a)'s displayed formula `floor(j,a,b) = ceil(((mu2−j)E2 − w(a,b))/(e1e2)) + [pin]`:

| family | j | (0,0) | (1,0) | (0,1) | (1,1) | recomputed | agrees |
|---|---:|---|---|---|---|---|:-:|
| FAM-A5 (e1e2=4, w = 2a+5b) | 0 | 6* | 5 | 4 | 4 | ⌈20/4⌉+1=6*, ⌈18/4⌉=5, ⌈15/4⌉=4, ⌈13/4⌉=4 | ✓ |
| FAM-A5 | 1 | 3 | 3* | 2 | 1 | ⌈10/4⌉=3, ⌈8/4⌉+1=3*, ⌈5/4⌉=2, ⌈3/4⌉=1 | ✓ |
| FAM-B (e1e2=2, w = a+3b) | 0 | 7* | 6 | 5 | 5* | ⌈12/2⌉+1=7*, ⌈11/2⌉=6, ⌈9/2⌉=5, ⌈8/2⌉+1=5* | ✓ |
| FAM-B | 1 | 4* | 3 | 2 | 2* | ⌈6/2⌉+1=4*, ⌈5/2⌉=3, ⌈3/2⌉=2, ⌈2/2⌉+1=2* | ✓ |

**FORM:** fixed-width ASCII display (source) → table (transcription).

**DERIVATION:** `[RUN]` — machine output, but every entry is *derivable* from `.15`(a)'s formula, which is what the audit above does.

**CONDITIONALITY:** the pin markers `*` are the `[pin] = 1` cases and their pattern is the content of `.11`(ii).

**RESOLUTION TRACE:** lines 88–101.

**TEETH:** **the four rows recomputed above match the source entry-for-entry, pin markers included — sixteen independent values, zero discrepancies.** The pin pattern also verifies the note's own reading: FAM-A5 has `f1f2 = 1` and exactly ONE pinned slot per coordinate ✓; FAM-B has `f2 = 2` and exactly TWO pinned slots per coordinate, at `(0,0)` and `(1,1)` ✓.

---

### EFF.GENTOW1.11  [derivation]

**CANONICAL STATEMENT:**

> “READ OFF THE TABLES (then proved in S2): (i) the floor at slot
> (j,a,b) is the SIDE HEIGHT (mu2−j)E2 minus the slot offset w(a,b),
> divided by e1e2 and ceiled, +1 at the lattice slots — e.g. FAM-C
> (0,(0,1)): ceil((42−7)/6) = 6, no pin (35 ≢ 0 mod 6); (ii) at
> f1f2 = 1 exactly ONE pinned slot per coordinate; at f2 = 2 (FAM-B,
> FAM-D) exactly TWO pinned slots per pinned height ((0,0) and (1,1)
> — the two flavor components of the one consumed K2-digit,
> two-step class separation made visible); (iii) node floors
> [21,11]/[29,15]/[13,7]/[43,22]/[13,7] = (mu2−j)E2 + 1, realized
> exactly by the NODE-EQ anchors (16Phi', 32xPhi', 64x, 64Phi',
> 729x — all tRAM with PARI sigma the composed-RAM dictionary
> value); (iv) the mutant base dv2(x^{D2}) = 8/8/4/18/4 sits BELOW
> E2 = 10/14/6/21/6 — the gap the wrong-floor tooth exploits.”

**FORM:** bold-headed four-item reading.

**DERIVATION:** the examples-first move — laws read off tables, then proved. This is the standing methodological directive applied literally.

**CONDITIONALITY:** these are READINGS, not proofs; S2 proves them.

**RESOLUTION TRACE:** lines 103–115.

**TEETH:** **ARITHMETIC AUDIT of all four items, recomputed independently.**
(i) FAM-C `(j=0, (a,b) = (0,1))`: `(mu2−0)E2 = 2·21 = 42`, `w(0,1) = 0·e2h + 1·u2 = 7` (e2h = 3·1), `⌈35/6⌉ = 6` ✓, and `35 mod 6 = 5 ≠ 0` so no pin ✓.
(ii) verified in `.10`'s table.
(iii) `(mu2−j)E2 + 1` for the five families at j = 0, 1: A5 `[21, 11]` ✓; A7 `[29, 15]` ✓; B `[13, 7]` ✓; C `[43, 22]` ✓; D `[13, 7]` ✓ — **all ten values reproduce.**
(iv) verified in `.07` — all five pairs ✓.

---

### EFF.GENTOW1.12  [run-record]  `[TABLE]`

**CANONICAL STATEMENT:** the refine table. **Source display, verbatim:**

>     “A5-R1 lam=13 s=1     : old (26,14,tEVEN) -> new (31,14,t2SIDED)
>     A5-R2 lam=21 s=1     : old (42,22,tEVEN) -> new (47,22,t2SIDED)
>       [n2hat(21) = 16Phi' — the r3 witness normalizer, exercised]
>     A7-R1 lam=15 s=1     : old (30,19,tEVEN) -> new (35,16,t2SIDED)
>     B-R1  lam=7  s=eta2  : old (14, 9,tEVEN) -> new (15, 8,tRAM)
>     B-R2  lam=8  s=1+eta2: old (16,10,tEVEN) -> new (19,11,tRAM)
>       [two-monomial K2-digit lift 16 + 4xPhi']
>     C-R1  lam=22 s=1     : old (44,24,tEVEN) -> new (47,25,tRAM)
>     D-R1  lam=9  s=1     : old (18, 9,tDBL ) -> new (19,10,tRAM)
>     D-R2  lam=10 s=eta2  : old (20,10,tDBL ) -> new (21,13,tRAM)
>       [q=3: BOTH event pins (lam AND 2lam) show and BOTH die]”

with its header: “**THE REFINE TABLE (old-key read -> refined-key read; all rows PARI-exact on the refined decided sigma; wrong-normalizer variant keeps the pin on every row = T-REFWRONG x8)**”.

`[TABLE]` — transcription with the compiler's check of the old-key pin law `p_0(old) = mu2·lam` (from `.31`(iv) at μ₂ = 2, j = 0):

| row | lam | s | old (p₀, p₁, type) | new | `2·lam` | p₀ = 2λ? |
|---|---:|---|---|---|---:|:-:|
| A5-R1 | 13 | 1 | (26, 14, tEVEN) | (31, 14, t2SIDED) | 26 | ✓ |
| A5-R2 | 21 | 1 | (42, 22, tEVEN) | (47, 22, t2SIDED) | 42 | ✓ |
| A7-R1 | 15 | 1 | (30, 19, tEVEN) | (35, 16, t2SIDED) | 30 | ✓ |
| B-R1 | 7 | eta2 | (14, 9, tEVEN) | (15, 8, tRAM) | 14 | ✓ |
| B-R2 | 8 | 1+eta2 | (16, 10, tEVEN) | (19, 11, tRAM) | 16 | ✓ |
| C-R1 | 22 | 1 | (44, 24, tEVEN) | (47, 25, tRAM) | 44 | ✓ |
| D-R1 | 9 | 1 | (18, 9, tDBL) | (19, 10, tRAM) | 18 | ✓ |
| D-R2 | 10 | eta2 | (20, 10, tDBL) | (21, 13, tRAM) | 20 | ✓ |

**FORM:** fixed-width ASCII display (source) → table (transcription).

**DERIVATION:** `[RUN]`, PARI-exact on the refined decided σ.

**CONDITIONALITY:** all eight rows are at **μ₂ = 2** — the pointwise regime. The general-μ₂ leg has no machine contact (`.04` row 3, `.47`).

**RESOLUTION TRACE:** lines 117–131.

**TEETH:** **ARITHMETIC AUDIT: all eight rows satisfy `p₀(old) = 2·lam` exactly** ✓, confirming `.31`(iv)'s minimal-height display at μ₂ = 2, j = 0. **The characteristic split also verifies**: the five q = 2 rows (A5, A7, B, C) show `p₁ = lam`-independent values with type `tEVEN` — i.e. the j = 1 pin has vanished (`2s = 0` in char 2) — while the two q = 3 rows (D-R1, D-R2) show `tDBL` with `p₁ = lam` exactly (9 and 10) ✓, i.e. **both pins present** at q = 3, exactly as `.31`(iv) predicts. This is a clean machine confirmation of a characteristic-sensitive display.

---
### EFF.GENTOW1.13  [derivation]

**CANONICAL STATEMENT:**

> “Read off: the old key sees the alpha-event at exactly (2lam, lam)
> heights with the (T−s)²-residues (q=2: the lam-pin vanishes, 2s=0;
> q=3: tDBL with both pins — the binomial char-sensitivity);
> the refine kills the pins into the lam-floored node; heights
> transport on the dv2-ladder; eta2-flavored and two-monomial lifts
> behave identically to monomial ones. (Then proved in S3.)”

**FORM:** inline reading paragraph.

**DERIVATION:** examples-first reading of `.12`; proved at `.31`(iv).

**CONDITIONALITY:** a reading, not a proof; μ₂ = 2 only.

**RESOLUTION TRACE:** lines 133–138.

**TEETH:** verified against `.12`'s recomputed table — the q = 2/q = 3 split reproduces on all eight rows.

---

### EFF.GENTOW1.14  [definition]

**CANONICAL STATEMENT:**

> “**Definition (the tower-entry locus 𝒯).** Fix the tower genre data
> (Q; e1,f1,mu1; h; Phi'; u2, e2, psi2, mu2), full inner side
> e2f2mu2 = mu1, and the composed key Phi2. 𝒯 := the monic f of
> degree n = mu2*D2 on the genre-G opening locus whose level-1 stage
> read exhibits the full inner side: the (J, dv(A_J))-polygon is ONE
> side of slope kappa2 = u2/e2 from (0, mu1*kappa2) to (mu1, 0) with
> twist-coherent residual psi2^{mu2} (S4 normalizers).”

**FORM:** bold-headed definition.

**DERIVATION:** `[DEFINITIONAL]`

**CONDITIONALITY:** **FULL side only** — the note repeats this fence at `.46`: “item (4) partial inner sides (e2f2mu2 < mu1 — 𝒯's definition here is FULL-side; every S2–S4 statement is scoped to it)”.

**RESOLUTION TRACE:** lines 142–148.

**TEETH:** the level-1 entry gate is machine-checked on 12 random in-budget members per family (P-4, REAL 180).

---

### EFF.GENTOW1.15  [lemma]

**CANONICAL STATEMENT:**

> “**LEMMA GENTOW-1.**
> (a) [WEIGHT CHARACTERIZATION] monic f of degree n lies on 𝒯 iff
> every composed slot of g := f − Phi2^{mu2} has weight >= mu2*E2+1;
> equivalently, in f = Phi2^{mu2} + Sum_{j<mu2} C_j Phi2^j,
> C_j = Sum c_{j,a,b} x^a Phi'^b (a < D', b < e2f2):
>
>     v(c_{j,a,b}) >= ceil( ((mu2−j)E2 − w(a,b)) / (e1e2) ) + [pin],
>     [pin] = 1  iff  e1e2 | (mu2−j)E2 − w(a,b) >= 0,
>
> the composed side height at the slot, ceiled to the digit grid,
> plus one consumed digit at each lattice slot — the r2-F2 level-1
> display verbatim with (D'h, ih, e1) ↦ (E2, w(a,b), e1e2).”

**FORM:** bold-headed lemma clause with an ASCII display.

**DERIVATION:** Steps 0/1/2/3 (`.19`–`.22`).

**CONDITIONALITY:** the transport-of-display claim “the r2-F2 level-1 display verbatim with (D'h, ih, e1) ↦ (E2, w(a,b), e1e2)” is the note's structural thesis for item (1): the composed floors are the level-1 floors under one substitution.

**RESOLUTION TRACE:** statement lines 150–161; proof 174–244.

**TEETH:** **the display was used to recompute sixteen budget-table entries at `.10`, all matching.** Machine: NEC 350 (both directions), T-MUTFLOOR ×5 (the `dv2(x^{D2})`-based mutant floors are machine-dead).

---

### EFF.GENTOW1.16  [lemma]

**CANONICAL STATEMENT (frozen):**

> “(b) [FIBRATION] f ↦ (c_{j,a,b}) is a triangular-unimodular digit
> bijection from 𝒯 onto the budget box (digits free above floors);
> one K2-digit per dv2-height per coordinate (GENHN-2'); per window
> N the free-O-digit count is Sum_{j,a,b} (N − floor(j,a,b)).”

**CANONICAL STATEMENT (EFFECTIVE):** the free-count display is REPLACED by **R2a** (`.65`):

>     “free-O-digit count per window N = Σ_{j,a,b} max(0, N − floor(j,a,b)).”

**FORM:** bold-headed lemma clause.

**DERIVATION:** Step 3's triangularity (`.22`); the clip is re-derived from (b)'s own fibration at `.65`.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement**. “the sealed form is false whenever N < floor at some slot”. **TARGETS:** this unit and, by R2a's own consumer re-scope, `.39` (GENTOW-5(e)'s “exact per window” sentence, which now reads at the clipped display).

**RESOLUTION TRACE:** statement lines 162–165; correction 860–884.

**TEETH:** ROUNDTRIP 150 digit round-trips; the clip's counter-instance and its inactivity on the committed rows are machine-scored (`.65`).

---

### EFF.GENTOW1.17  [lemma]

**CANONICAL STATEMENT:**

> “(c) [NODE] on 𝒯: p_j := dv2(C_j(x0)) >= (mu2−j)E2 + 1 for j < mu2
> at every root x0, equality realizable at every j (two-step class
> separation supplies a slot in every residue class mod e1e2).”

**FORM:** bold-headed lemma clause.

**DERIVATION:** Step 4 (`.23`), whose realizability half is a two-stage CRT solve.

**CONDITIONALITY:** none beyond 𝒯.

**RESOLUTION TRACE:** statement lines 166–168; proof 246–257.

**TEETH:** **P-5, the sharpness test**: “the five NODE-EQ anchors hit p0 = mu2·E2 + 1 exactly, tRAM, PARI both routes (the node floor is SHARP)”. The five anchor values were recomputed at `.11`(iii) and all ten match. T-BELOWNODE fires: “a digit AT weight mu2·E2 breaks the entry endpoint: dv(A0) = 12 ≠ 10”.

---

### EFF.GENTOW1.18  [lemma]

**CANONICAL STATEMENT:**

> “(d) [NODE AT THE FIELD] every root x0 of every f in 𝒯 has
> dv2(Phi2(x0)) > E2 — the psi-cancellation (HE6-0) argument one
> level up. (dv2(Phi2(x0)) need not be an integer on 𝒯 — RAM leaves
> have e(L) = 2e1e2; the strict inequality is the statement.)”

**FORM:** bold-headed lemma clause with a parenthetical scope note.

**DERIVATION:** Step 5 (`.24`) — a residue computation ending in `psi2(eta2(x0)) = 0`.

**CONDITIONALITY:** **this clause is the one the gauge seam kills at η ≠ 1** — Step 5's `[GT1-r1]` bracket says so and gives the machine evidence (`.24`). The non-integrality parenthetical is a genuine scope guard: the statement is an inequality, not a value.

**RESOLUTION TRACE:** statement lines 169–172; proof 259–271.

**TEETH:** **P-3: 171 `GP-NODE` row-checks of `e1e2·nfeltval(Phi2) > E2·pr.e` (STRICT), with `e1·val(x) = h·pr.e` and `e1e2·val(Phi') = u2·pr.e` exact.** Re-read from the artifact tally: `'GP-NODE': 171` ✓.

---

### EFF.GENTOW1.19  [derivation]

**CANONICAL STATEMENT:** Step 0, the weight-monotonicity hinge, `[ASSEMBLED]` from lines 176–202. Its two moves, verbatim:

> “* x-carry (a' >= D'): x^{D'} = Phi' + (Phi'-tail); tail monomials
>   x^c pi^g have g >= (D'−c)h/e1 (the key's one side), so
>   e1e2*g + c*e2h >= D'e2h = wt(x^{D'}) — tail weight preserved or
>   raised; the Phi'-part has weight u2 > e2D'h ([r1] node floor) —
>   strictly raised.
> * Phi'-carry (b' >= e2f2): Phi'^{e2f2} = Phi2 + Sum_t chat_t
>   n(u2(f2−t)) Phi'^{e2t}; each lift term has weight
>   e2*u2(f2−t) + e2t*u2 = E2 = wt(Phi'^{e2f2}) … — preserved; the Phi2-part at
>   weight E2 exactly.”

and its conclusion, verbatim:

> “**"all slots of P at weight >= W" is the same condition on both grids.**”

**FORM:** bold-headed step with a two-bullet display.

**DERIVATION:** two carry computations, each priced by one side.

**CONDITIONALITY:** the `[GT1-r1]` pin here is explicitly **VALUE-BLIND**: “this display is VALUE-BLIND — it prices heights only, and lift(c_t·eta^{W(t)}) and lift(c_t) sit at the same height, so Step 0 is unchanged under the gauge correction.” **This is wrap-immunity leg 1** and is corroborated independently by PE1's own re-derivation (`.53`).

**RESOLUTION TRACE:** lines 176–202.

**TEETH:** ARITHMETIC AUDIT: the lift term's weight `e2·u2(f2−t) + e2t·u2 = e2u2f2 = E2` ✓ for every t — the cancellation is exact and t-independent, which is precisely why Step 0 is value-blind.

---

### EFF.GENTOW1.20  [derivation]

**CANONICAL STATEMENT:** Step 1, verbatim (abridged at the r1 bracket, quoted next):

> “**Step 1 (Phi2^{mu2}'s own level-1 data — from T(b)'(i), consumed).**
> Phi2's level-1 development is one-sided of slope kappa2 with
> residual psi2: slots at weight >= E2, the weight-E2 graded layer =
> psi2's coefficients at the side lattice … Multiplicativity
> of side residuals (graded layer of a product = product of graded
> layers, as in (i)'s proof): Phi2^{mu2} has slots at weight
> >= mu2*E2 with weight-mu2*E2 layer psi2^{mu2}, and every
> off-lattice slot strictly above.”

**FORM:** bold-headed step.

**DERIVATION:** `[IMPORTED]` from T(b)′(i) plus multiplicativity of graded layers.

**CONDITIONALITY:** **the r1 pin makes this step GAUGE-LIVE and says exactly how it fails otherwise**:

> “[GT1-r1: read AT
> THE CORRECTED KEY (S0 pin, S7.1) — the erratum's scope clause:
> T(b)'(i)'s carrier/slot/residual mechanism holds at the corrected
> key; at the gauge-naive key the weight-E2 layer is c_t·eta^{−W(t)},
> NOT psi2's coefficients, and this step fails at eta != 1.]”

**RESOLUTION TRACE:** lines 204–217.

**TEETH:** the failure mode is machine-scored at the fresh route's F1 frame: `ef(Phi2^N) = {(4,1)} != {(2,2)}` with a degenerate twisted residual `(T−1)^2` (`.53`).

---

### EFF.GENTOW1.21  [derivation]

**CANONICAL STATEMENT:** Step 2 (⟸ realizability), verbatim:

> “**Step 2 (⟸ realizability).** Digits >= floors give every slot of
> g weight >= mu2*E2 + 1 (Step 0 arithmetic); by Step 0 all level-1
> slots of g sit strictly above the inner side … Adding Phi2^{mu2} (Step 1): f's level-1 pins are
> the full inner side with residual psi2^{mu2} exactly. Outer
> grammar: a weight-wt grid monomial has x-height wt − B(u2 − e2D'h),
> B := b + j*e2f2 <= mu1 − 1, so x-height >= mu2*E2 + 1 −
> (mu1−1)(u2 − e2D'h) = u2 + (mu1−1)e2D'h + 1 > mu1*e2D'h = n*e2h:
> strictly above the outer side … So f ∈ 𝒯.”

**FORM:** bold-headed step.

**DERIVATION:** Step 0 arithmetic + Step 1 + an outer-grammar degree count.

**CONDITIONALITY:** consumes the node floor `u2 > e2D'h` twice (in Step 0 and in the outer-grammar chain).

**RESOLUTION TRACE:** lines 219–229.

**TEETH:** **ARITHMETIC AUDIT of the outer-grammar chain, recomputed:** with `mu2·E2 = mu1·u2` (since `E2 = e2f2u2` and `mu1 = e2f2mu2`), the bound reads `mu1u2 + 1 − (mu1−1)(u2 − e2D'h) = u2 + (mu1−1)e2D'h + 1` ✓ — the displayed simplification is exact. And `u2 + (mu1−1)e2D'h + 1 > mu1·e2D'h` reduces to `u2 + 1 > e2D'h`, true by the node floor ✓.

---

### EFF.GENTOW1.22  [derivation]

**CANONICAL STATEMENT:** Step 3 (⟹ necessity + fibration), verbatim:

> “**Step 3 (⟹ necessity + fibration).** f ∈ 𝒯: its level-1 side
> digits at the lattice equal psi2^{mu2}'s coefficients — the same
> K-digit data Phi2^{mu2} carries (Step 1, same coherent-normalizer
> convention as the residual's definition). In g = f − Phi2^{mu2}
> the lattice digits cancel to one digit higher … Step 0 converts to the composed floors. Triangularity: the
> coordinate map is a composition of monic divisions (by Phi2, then
> Phi'), unipotent in the x-degree filtration: c_{j,a,b} = the
> coefficient of f at degree jD2 + bD' + a plus an Ô-combination of
> strictly higher-degree coefficients — a digit bijection; Steps 2+3
> identify image and budget box. Free-count display immediate. ∎(a,b)”

**FORM:** bold-headed step closing (a) and (b).

**DERIVATION:** cancellation of the shared lattice digits, then Step 0 conversion, then a unipotence argument on the x-degree filtration.

**CONDITIONALITY:** **“Free-count display immediate” is the sentence R2a corrects** — the display it produces is unclipped and false at small N (`.65`). The triangularity claim itself is untouched and is re-used verbatim by GENTOW-5(e) (`.39`).

**RESOLUTION TRACE:** lines 231–244; correction 860–884.

**TEETH:** ROUNDTRIP 150; the unipotence is the ground of `.39`'s mod-π^N bijection.

---

### EFF.GENTOW1.23  [derivation]

**CANONICAL STATEMENT:** Step 4, verbatim:

> “**Step 4 (node (c)).** All roots x0 of f ∈ 𝒯 are tower-node points:
> the full inner side forces v(Phi'(x0)) = u2/(e1e2) exactly with
> eta2(x0) a psi2-root (the level-1 Newton polygon of the inner read
> has the one side of slope kappa2, residual psi2^{mu2} zero-free at
> the corners — T(b)'(iii)'s (T1')/(T2') transport, consumed). So
> GENHN-2' reads p_j exactly as the slot-min; by (a)'s floors each
> slot has e1e2*v + w >= (mu2−j)E2 + 1. Equality: pick the residue
> class: solve b*u2 ≡ target (mod e2) (gcd(u2,e2) = 1), then
> a*h ≡ (target − b*u2)/e2 (mod e1) (gcd(h,e1) = 1) — a slot with
> w(a,b) ≡ (mu2−j)E2 + 1 (mod e1e2) inside a < e1 <= D',
> b < e2 <= e2f2; set its digit at the floor, rest empty: on 𝒯 by
> (b), pin at exactly (mu2−j)E2 + 1. ∎(c)”

**FORM:** bold-headed step with a two-stage CRT solve.

**DERIVATION:** the all-roots transport (imported), then GENHN-2′'s slot-min, then a constructive CRT realization.

**CONDITIONALITY:** **this sentence is the one HETOW's F-2 annex quotes as its all-roots-transport cite** — `EFF.HETOW.54` cites exactly this Step 4, and that citation is a NEAR-MISS (transliterated and elided). **The cross-entry consequence:** the quotation HETOW relies on is THIS unit's first sentence, and the clause HETOW elided is this unit's parenthetical justification. Compiled from both sides, the referent is unambiguous.

**RESOLUTION TRACE:** lines 246–257; the downstream cite at `HETOW_RECON_2026-08-09.md:811–819`.

**TEETH:** the CRT solve's two-step class separation is re-used by `.36`(b) (“class surjectivity is GENTOW-1 Step 4's CRT display”) and by `.10`'s pin pattern (two pinned slots at f₂ = 2) ✓.

---

### EFF.GENTOW1.24  [derivation]

**CANONICAL STATEMENT:** Step 5, verbatim:

> “**Step 5 (field floor (d)).** Phi2(x0) = Phi'(x0)^{e2f2} − Sum_t
> chat_t(x0) n(u2(f2−t))(x0) Phi'(x0)^{e2t}: every term at dv2 = E2
> exactly ((T1),(T12)); the height-E2 residue under the coherent
> height-E2 normalizer is (unit)·psi2(eta2(x0)) — the S4 cocycle
> enters every term identically, exactly (i)'s side-residual
> computation — and psi2(eta2(x0)) = 0 (T22). Ultrametric:
> dv2(Phi2(x0)) > E2. ∎”

**FORM:** bold-headed step.

**DERIVATION:** an exact-height term census, then a residue computation, then the ultrametric.

**CONDITIONALITY:** **this is the VALUE-LIVE gauge site, and the r1 bracket states the failure with machine evidence:**

> “[GT1-r1: "the residue is
> (unit)·psi2(eta2(x0))" holds at the CORRECTED chat_t (S0 pin,
> S7.1); at the gauge-naive lifts the term-t residue carries the
> extra factor eta^{−W(t)}-bar and the sum is NOT psi2(eta2(x0)) —
> (d) then FAILS at eta != 1: machine-confirmed, nfeltval(Phi2^N) =
> 3·pr.e EXACTLY at 20/20 scored prime rows of the fresh frame F1
> (S7.1).]”

**RESOLUTION TRACE:** lines 259–271.

**TEETH:** **the failure is machine-scored 20/20** and re-verified here: `gentow1_pe1_fresh_output.txt`'s teeth line reads `teeth: {'GAUGE-NODE': 20, 'GAUGE-SIGMA': 2, 'REFWRONG': 2}` ✓ — the 20 GAUGE-NODE rows are exactly the “20/20 scored prime rows”. Disposition `AUDIT / decorrelated frame` (the F1 frame is η ≠ 1, outside the sealed battery's blind spot).

---

### EFF.GENTOW1.25  [corollary]

**CANONICAL STATEMENT:**

> “**COROLLARY GENTOW-1.1 (the depth->=3 node floor — [GENHN-TOW-1]
> item (6)(beta)'s missing provenance).** Every side of the composed
> polygon (j, p_j) of an f ∈ 𝒯 has dv2-slope
>
>     kappa3 > E2 = e2f2u2 > dv2(x^{D2}) = D2*e2h.
>
> *Proof.* Pins p_j >= (mu2−j)E2 + 1 (GENTOW-1(c)) with right
> endpoint (mu2, 0): the rightmost (minimal) side slope is
> >= min_j p_j/(mu2−j) >= E2 + 1/mu2 > E2; convexity gives every
> side slope > E2; and E2 = e2f2*u2 > e2f2*(e2D'h) = D2*e2h by the
> [r1] node floor u2 > e2D'h. ∎”

with the discharge sentence:

> “Item (6)(beta) is
> hereby discharged INTO item (1); item (6)(alpha) (the iterated
> carry-cancellation bookkeeping) is untouched and keeps the box.”

**FORM:** bold-headed corollary with an inline display and proof.

**DERIVATION:** the pin bound + convexity + the node floor.

**CONDITIONALITY:** **item (6)(β) is discharged with a SHARPER constant than the box asked for** — the note is explicit: “at level 2 they split and the SHARPER constant E2 is the true floor”. (6)(α) keeps its box.

**RESOLUTION TRACE:** lines 273–289.

**TEETH:** **ARITHMETIC AUDIT of the witness, recomputed:** the note's witness is “kappa3 = 21/2 > E2 = 10 > dv2(x^{D2}) = 8” — at FAM-A5, `min_j p_j/(mu2−j) ≥ (mu2E2+1)/mu2 = 21/2 = 10.5 > 10 = E2` ✓ and `E2 = 10 > 8 = D2·e2h = 4·2` ✓. The general bound `E2 + 1/mu2` at μ₂ = 2, E2 = 10 gives 10.5 ✓ — the witness is the general bound instantiated.

---

### EFF.GENTOW1.26  [fence]

**CANONICAL STATEMENT:**

> “**Remark (count-law unlock, honest scope).** With (b), tower count
> laws take the W-12.A cell-law form on the composed keying with
> entry exponent Sum(N − floor) — the battery's budget tables are
> the first measured contact (S5); the per-genre tower count LEDGERS
> (the GENH5-DENS-style displays) are a counting unit NOT executed
> here.”

**FORM:** bold-headed remark.

**DERIVATION:** `[RECORD]` of a downstream unlock with its scope fence.

**CONDITIONALITY:** **the exponent displayed here is the UNCLIPPED one** and inherits R2a's correction (`.65`): a consumer building count laws must use `Σ max(0, N − floor)`. The note does not re-point this remark at R2a — recorded as a completeness item (OPEN-CALL 2).

**RESOLUTION TRACE:** lines 291–296; the governing clip at 860–884.

**TEETH:** none; a declared non-executed unit.

---

### EFF.GENTOW1.27  [definition]

**CANONICAL STATEMENT (frozen):** §S3's setting, `[ASSEMBLED]` from lines 300–317. The event and the ladder normalizers, verbatim:

> “f ∈ 𝒯 whose composed polygon (j, p_j) is one side of integer
> dv2-slope lam > E2 with residual (T − s)^{mu2} over K2, s ∈ K2^×
> (the composed frame's stage-alpha event; by GENTOW-1(c) any
> composed side has slope > E2, so lam >= E2 + 1 automatically — the
> composed floor plays S6.1's "kappa > S′"). LADDER NORMALIZERS
> (the r3 mechanism's n̂₂, now with provenance): n2hat(m) :=
> pi^{a0} x^i Phi'^b, i < e1, b < e2, e1e2*a0 + i*e2h + b*u2 = m —
> the (i,b)-pair is unique per residue class mod e1e2 (two-step
> separation) and a0 >= 0 whenever m > E2 (since u2 > e2D'h forces
> E2 >= (e1−1)e2h + (e2−1)u2 + 1).”

and the K2-DIGIT LIFT display, verbatim (the object later corrected):

> “K2-DIGIT LIFT: for s =
> Sum_{t<f2} s_t eta2^t (s_t ∈ K), lift(s; m) := Sum over the f1f2
> within-class monomials x^{i+e1r} Phi'^{b+e2t} at height m with
> O-digit coefficients realizing the components in the coherent
> normalization (the same S4-cocycle convention as the entry lifts
> chat_t [GT1-r1: = the CORRECTED convention — the S0 pin's
> eta^{W}-corrected lifts, S7.1]); deg lift < D2 always
> (x-exponents < e1f1 = D', Phi'-exponents < e2f2).”

**CANONICAL STATEMENT (EFFECTIVE):** the lift display is REPLACED by the 2026-08-10 S3 correction (`.62`):

>     “lift(s; m) := Sum_{r,t} d_{r,t} · M_{r,t}(m),
>     M_{r,t}(m)  := n2hat(m − Delta(r,t)) · x^{e1·r} · Phi'^{e2·t},
>     Delta(r,t)  := e1e2h·r + e2u2·t,”

**FORM:** bold-headed setting with two displays.

**DERIVATION:** the normalizer uniqueness is two-step class separation; the `a0 ≥ 0` claim is an inequality consumed from the node floor.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of the lift display only. **The frozen sentence “deg lift < D2 always” STANDS as written** — the correction verifies it survives (`.62`). The fixed-base display is FALSE at seam-live heights, with a machine counter-instance.

**RESOLUTION TRACE:** statement lines 300–317; correction 769–845.

**TEETH:** **ARITHMETIC AUDIT of the `a0 ≥ 0` inequality, recomputed:** the claim is `E2 ≥ (e1−1)e2h + (e2−1)u2 + 1`, i.e. `e2f2u2 ≥ (e1−1)e2h + (e2−1)u2 + 1`. At `f2 ≥ 1` and `u2 > e2D'h = e2e1f1h ≥ e1h`: `e2f2u2 − (e2−1)u2 ≥ u2 > e1h·e2 ≥ (e1−1)e2h`, so the inequality holds with room ✓. The displayed derivation is sound.

---
