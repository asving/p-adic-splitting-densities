# EFF-GENTOW3 — CANONICAL EFFECTIVE SPECIFICATION v2 (full compilation)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Header

**Source note:** `lean/notes/openmath/GENTOW3_PROOF_2026-08-09.md` (1,041 lines / 57,484 bytes).

**HEAD blob hash:** `f6160c3763c89cca9ef1ccfe09faac5fce6874ac` (fresh `git hash-object`; last touched by commit `3ee83992`).

**Compilation context:** Stage 0a; governing template `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). IDs `EFF.GENTOW3.<nn>`, contiguous, in effective-text order.

**GENRE: TAG-SPARSE ASCII PROSE PROOF + SEALED BATTERY + SIX-ROUND ARC + THREE POST-ACCEPTANCE APPENDS.** `grep -c '\tag{'` = **0**. Three unit populations (v3 rule 19): **preregistrations** (P-1…P-7 + 3 teeth, sealed at `5ac0d80`), **run-records** (S5 plus four fresh routes), **proof units** (S2–S4).

**What makes this note distinctive in the queue:** it is the only entry whose arc contains a documented **OVER-CORRECTION** — r2 repaired a certificate-free claim by inserting an “exactly” that r3 then had to withdraw as an unproved only-if, refuted by a measured member. The compilation carries that three-layer chain explicitly (CHAIN-GEOG).

### FREEZE PREDICATES (v3 rule 21 — three text freezes + one eleven-artifact instrument freeze; **all verified**)

`[TABLE — compiler ledger]`

| # | Predicate | Stated | Compile-time verification |
|---:|---|---|---|
| F-1 | S7.5: “Body state before this round: md5 8664269e723c7779538f25329490c06d = the PE1 target (verdict commit d90db6d)” | md5 + commit | **`git cat-file -p d90db6d:<file> \| md5sum` = `8664269e723c7779538f25329490c06d`** ✓ (whole-body pin, correctly not a HEAD prefix — r1 inserted brackets in-body) |
| F-2 | post-PE5: “pre-append body md5 1e753d199950bc591a95962686f25ed3 (815 lines) = the rider state @ d6b409ce” | md5 + line count | **lines 1–815 → `1e753d199950bc591a95962686f25ed3`** ✓ (both md5 and the 815-line count) |
| F-3 | S8.3: “post-acceptance body md5 203f7c04 (203f7c04fa8499853509e33524bab77f; 878 lines, 48,738 bytes)” | md5 + lines + bytes | **lines 1–878 → `203f7c04fa8499853509e33524bab77f`, 48,738 bytes** ✓ (all three) |
| F-4 | S7.5/S7.6/S7.7: “the eleven pinned md5s … re-computed and matching at HEAD” | 11 artifact md5s | **ALL ELEVEN MATCH** (plus two PE5 artifacts and the RUN B log — thirteen in total; see §3.2). `towerrat2_runB_gentow3_output.txt` also matches its stated **6,297 B** exactly |

**Eight stated text quantities and thirteen artifact hashes, all reproduced, zero discrepancies.**

### Effective-text rule (DERIVED)

**(i) Rounds r1–r3 were applied as bracketed IN-BODY insertions**, each with its own numbered manifest (S7.5, S7.6's Manifest, S7.7). r1's manifest states the edit shape: “[GT3-r1]-bracketed INSERTIONS plus this S7 — checkable as `git diff d90db6d..HEAD` on this file”.

**(ii) The statement displays were held outside r1 and r3.** S7.5: “the statement displays of THEOREM GENTOW-3 (i)–(iv), COR GENTOW-3.C, and the S0/S1/S3/S4 texts sit outside the inserted brackets”. S7.7: “The THEOREM GENTOW-3 (i)–(iv) and COR GENTOW-3.C statement displays appear in no deleted or inserted line of that diff.” **r2 is the exception and says so**: its edit site (3) is “S2 THEOREM (iv) statement pin ("touched" = the certificate sense — a definition pin inside the statement, per the r2 charge; it is the reading the (iv) proof supports, no weakening)”.

**(iii) After PE5 the note is frozen.** “**THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.**”

**(iv) Post-freeze corrections land BY SUPERSESSION with the superseded sentence quoted and left byte-intact.** S8's preamble: “the note is frozen, so both land as dated corrections BY SUPERSESSION (the superseded sentences stay byte-intact above and read as corrected here)”.

**EFFECTIVE TEXT = the note as written (r1–r3 brackets landed), READ AS SUPERSEDED by S8.1, S8.2 and S8.4 in that order.** Two (iv)-adjacent sentences are superseded post-freeze, and one of those supersessions is itself superseded (CHAIN-NONFUNC).

### Supersession CHAINS (v3 rule 25 — TERMINALs marked)

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-GEOG (the S0 geography clause)** | composed: attainment asserted **certificate-free** at “overflow genres” (a term defined nowhere) → **r2**: rewritten to “fails AT Θ_j **exactly** at the coordinates carrying (iv)'s certificate” → **r3**: that “exactly” is an **only-if S2 never proves**, refuted by the measured W member; dropped for the proved if-direction + an existential measured member-failure clause | **r3** (`.10`) |
| **CHAIN-XFREE** | S2's x-free definition with its displayed “equivalently i(u2(f2−t)) = 0” → **[GT3-r1]**: the equivalence holds at **f1 = 1 ONLY**; the PRIMARY clause (read at the corrected `chat_t`) is operative at every f1 | **[GT3-r1] S7.1** (`.17`, `.45`) |
| **CHAIN-GAUGE** | GENHN-T(b)′'s gauge-naive `chat_t` → HETOW PE1 F-1 → GENHN erratum `59c1966` → **[GT3-r1]** pins the corrected display at nine sites | **[GT3-r1]** (`.15`, `.44`) |
| **CHAIN-PERSIST (iv)'s deep-perturbation clause** | composed: “both reads shift by the SAME g-digits (linearity), so the divergence persists” → **S8.1**: that inference is **WITHDRAWN** (linearity gives `(Sh−C)(f0+g) = (Sh−C)(f0) + (Sh−C)(g)`, not `Sh(g) = C(g)`); persistence RE-DERIVED from the margin ledger at the GENTOW-1(a) box hypothesis | **S8.1** (`.58`) |
| **CHAIN-NONFUNC (iv)'s closing sentence)** | composed: “The shadow read at heights ≥ THETA_j is NOT a function of the honest data” → **S8.2**: literally FALSE; scoped to the honest read's **OUTPUT** (pins, deciding residues, σ, labels) → **S8.4**: that scope is **WITHDRAWN** too (the committed search cannot support it); final claim = “not a function of the honest read's **σ**” | **S8.4** (`.62`) |
| **CHAIN-CENSUS** | S5's “110 members” → **[GT3-r1] m-2**: the true count is **137** member_check calls = 274/2; “110” undercounted | **[GT3-r1] S7.3** (`.49`) |
| **CHAIN-GRADE** | 0/2 → PE1 NOT CLEAN → PE2 NOT CLEAN → PE3 NOT CLEAN → **PE4 CLEAN, 0/2 → 1/2** → **PE5 CLEAN (ZERO findings), 1/2 → 2/2 ACCEPTED** → S8: “acceptance 2/2 stands ANNOTATED” | S8 (`.57`) |

### SERIES declared (v3 rule 28)

**SERIES ARC** — one unit per dated round record: `.02` (PE1/r1) → `.03` (PE2/r2) → `.04` (PE3/r3) → `.05` (PE4 CLEAN + rider fold) → `.54` (PE5 CLEAN, ACCEPTED 2/2) → `.57` (r4, RUN B) → `.61`/`.62` (r5, 2026-08-12). **Seven dated entries; four repair rounds; two post-acceptance correction batches.**

**SERIES REPAIR-SECTIONS** — the numbered repair sections in source order: `.43`–`.51` (S7/S7.1–S7.5, r1) → `.52` (S7.6, r2) → `.53` (S7.7, r3) → `.58`–`.60` (S8.1–S8.3, r4) → `.62` (S8.4, r5).

**SERIES CERTIFICATE-CONFIG** — the three MEASURED certificate configurations, which the note itself assembles as a series for GENTOW3-BOX-1: **attained** (FAM-A5 j = 0, and FR5X μ₂ = 2 j = 0) → **slack / digit cancels** (FR-M3 j = 0; FR5X μ₂ = 3 j = 0) → **identically zero** (FR5X μ₂ = 3 j = 2; the S1 table's “—” entries). Compiled at `.55` with its own unit, because the note explicitly reads them as “three measured cases to decide among”.

### Scope split — THREE predicates (rule 7 + v3 rule 17)

**A. Mathematical absorption / supply SET.** The CHARGE:

> “CHARGE: characterize EXACTLY when the stage-shadow read (T(b)'(iv):
> the coefficientwise mod-Phi' projection G-hat_j(theta, Y)) agrees
> with the composed read (the Phi2-development of f itself) — the
> per-height criterion, T(a)'s event-band survival as a theorem, and
> the leaf-depth failure quantified at the PE1 anchors.”

Delivered: **one theorem (GENTOW-3, four clauses), one corollary (GENTOW-3.C), and one quantified failure analysis (S4, three regimes)** — the STATUS TABLE's three deliverables plus the battery.

**B. Append / consumption PROTOCOL scope — what this note has LANDED elsewhere.** Declared zero:

> “**Consumption path (not executed here):** the item-(3) discharge
> into GENHN_PROOF's [GENHN-TOW-1] box text — and the (iv)
> sentence's upgrade from "machine-verified" to "theorem
> (GENTOW-3.C)" — is the orchestrator's dated consumption update
> after this note's own hostile arc; GENHN_PROOF and the GENTOW-1/2
> notes are byte-untouched by this unit.”

Verified: `grep -cF 'GENTOW-3' GENHN_PROOF_2026-08-08.md` = **0** (N1), and `grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` = **0** — the discharge is unlanded, and so is the (iv)-sentence upgrade. **The note also performs its own CONSUMER WALK** at r2 (`.52`) and finds no consumer edit owed — a discipline no other entry in this queue exhibits.

**C. Inbound corrections RECEIVED — four sources:** (1) GENHN's gauge erratum via HETOW PE1 (→ r1); (2) this note's own PE1–PE5; (3) the decorrelated **CODEX TOWERRAT2 RUN B** (→ r4); (4) the **sol E13 certification run** with an orchestrator activation note (→ r5).

### Resolution rules applied

1. `[GT3-r1/r2/r3]` brackets are already-landed in-body text.
2. Post-freeze supersessions (S8.1, S8.2, S8.4) quote their target and leave it byte-intact; the unit carries the frozen sentence as CANONICAL STATEMENT and the superseding reading in CONDITIONALITY with its KIND.
3. **Where a supersession is itself superseded (CHAIN-NONFUNC), all three layers are emitted and the TERMINAL is marked** — a consumer citing S8.2 alone would carry a withdrawn scope.
4. Numbers recomputed from the committed artifacts and from the note's own formulas.
5. Cross-note claims (the consumer walk's three targets) are grep-verified.

### Quotation and table discipline

Verbatim or `[ASSEMBLED]`; `…` marks truncation. ASCII notation preserved (the note writes `Phi'`, `mu2`, `THETA_j`, `delta`; the S1 table uses Unicode `Θ`, `δ` — both quoted as they stand). Four source tables are `[TABLE]`-flagged; the two fixed-width ASCII blocks (divergence table, verdict block) are double-emitted per v3 rule 14.

---

## 2. Statement inventory

62 units, contiguous, in effective-text order. FORM on every unit.

### EFF.GENTOW3.01  [convention]

**CANONICAL STATEMENT:**

> “# GENTOW-3: THE FAITHFULNESS GEOGRAPHY ([GENHN-TOW-1] item (3))
> ## When the stage-shadow read agrees with the composed read”

with the status line:

> “**2026-08-09 — COMPLETE at attempt grade 0/2 (hostile arc owed).
> Unit: GENTOW-3, BOX-CLOSURE campaign wave B1. Machine leg
> sealed-then-verdict (S5): GREEN 582/0, 3/3 teeth.”

**FORM:** title + subtitle + bold status line.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the grade is superseded to **ACCEPTED 2/2** (`.54`) and then ANNOTATED (`.57`). SUPERSESSION KIND: **counter re-reading**.

**RESOLUTION TRACE:** lines 1–6; corrections 819–826, 880–892.

**TEETH:** the battery figure is re-read from the artifact: `=== VERDICT: GREEN -- 582 checks, 0 violations (0.1s) ===` ✓, `tooth T-SHADOW-REG fired x1` ✓.

---

### EFF.GENTOW3.02  [repair-round record]  *(SERIES ARC, link 1)*

**CANONICAL STATEMENT:**

> “[ARC — passPE1 2026-08-10: NOT CLEAN, 1 GAP + 3 MINOR
> (GENTOW3_passPE1_report.md @ 3101cf5); counter stays 0/2.
> GT3-r1 repair round 2026-08-10 (this commit): F-1 dated gauge
> annex — chat_t := lift(c_t·eta^{W(t)}) pinned per GENHN erratum
> 59c1966, the x-free "equivalently" clause re-scoped (f1 = 1 only),
> GENTOW3-BOX-2 honest status, FR-GL adopted as the eta != 1 machine
> row (S7.1); m-1 digit-value attribution (S7.2); m-2 P-1 census
> 110 -> 137 (S7.3); m-3 T-SHADOW-REG sigma-leg disclosure (S7.4).
> Sealed machine artifacts BYTE-UNTOUCHED (md5s, S7.5). Grade stays
> 0/2; PE2 next.]”

**FORM:** bracketed dated ARC record.

**DERIVATION:** `[RECORD]`; the four dispositions are compiled at `.44`–`.50`.

**CONDITIONALITY:** counter superseded (`.54`).

**RESOLUTION TRACE:** lines 7–16.

**TEETH:** `git cat-file -t 3101cf5` = commit; `git cat-file -t 59c1966` = commit ✓.

---

### EFF.GENTOW3.03  [repair-round record]  *(SERIES ARC, link 2)*

**CANONICAL STATEMENT:**

> “[ARC — passPE2 2026-08-10: NOT CLEAN, 1 GAP
> (GENTOW3_passPE2_report.md @ c048154); counter stays 0/2.
> GT3-r2 repair round 2026-08-10 (this commit): F-1 certificate
> scoping — the S0 geography clause, the S4 delta = 1 bullet, and
> the S4 count-law rewritten to carry (iv)'s per-coordinate
> certificate hypothesis; "touched coordinate(s)" pinned to the
> certificate reading in the (iv) statement (S7.6). Sealed machine
> artifacts BYTE-UNTOUCHED (md5s re-verified, S7.6). Grade stays
> 0/2; PE3 next.]”

**FORM:** bracketed dated ARC record.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **r2 is the only round that edits inside a THEOREM statement** (the “touched” pin), and it declares that explicitly. Its S0 rewrite is then over-corrected and partly withdrawn at r3 (CHAIN-GEOG).

**RESOLUTION TRACE:** lines 17–25; the round at 680–761.

**TEETH:** `git cat-file -t c048154` = commit ✓.

---

### EFF.GENTOW3.04  [repair-round record]  *(SERIES ARC, link 3; CHAIN-GEOG — TERMINAL)*

**CANONICAL STATEMENT:**

> “[ARC — passPE3 2026-08-10: NOT CLEAN, 1 GAP + 1 MINOR
> (GENTOW3_passPE3_report.md @ a1c181d); counter stays 0/2.
> GT3-r3 repair round 2026-08-10 (this commit): F-1 one-siding —
> the S0 geography clause's r2 "exactly" (an only-if S2 never
> proves, refuted by the measured W witness member at FR-M3
> j = 0) dropped for the proved direction: certificate ->
> failure AT THETA_j, attained by the key power's own shadow;
> where the digit cancels only the KEY POWER's first divergence
> provably sits strictly above THETA_j. m-A: S7.6 FR-M3 record
> Phi'/Phi2 label fix (constants unaffected). Sealed machine
> artifacts BYTE-UNTOUCHED (all nine md5s re-verified). Grade
> stays 0/2; PE4 next.]”

**FORM:** bracketed dated ARC record.

**DERIVATION:** `[RECORD]` of an OVER-CORRECTION repair — r3 fixes r2, not the composition.

**CONDITIONALITY:** **this is the arc's methodological centre.** The corrected geography is now one-sided: certificate ⟹ failure at Θ_j (proved); digit cancels ⟹ only the KEY POWER's first divergence is provably above Θ_j (other members may still fail at Θ_j, and one measured member does).

**RESOLUTION TRACE:** lines 26–37; the round's manifest at 763–815.

**TEETH:** `git cat-file -t a1c181d` = commit ✓. The refuting W member is machine-pinned at `.53`.

---

### EFF.GENTOW3.05  [acceptance-box]  *(SERIES ARC, link 4)*

**CANONICAL STATEMENT:**

> “[ARC — passPE4 2026-08-10: CLEAN, 0 GAP + 1 MINOR
> (GENTOW3_passPE4_report.md @ b6a43963); counter 0/2 -> 1/2 — the
> arc's first clean pass. Rider fold (post-PE4, this commit; minors
> only, no repair round owed): m-1 traceability — the S0
> W-measurement cite gains the PE3-fresh artifact md5 pins (runner
> bde31247, output 3ce4128a; re-computed against the committed
> artifacts at this fold) and the [GT3-r3] round gains its numbered
> manifest + adoption record (S7.7), matching the r1/S7.5 and
> r2/S7.6 format. Sealed artifacts BYTE-FROZEN (the eleven pinned
> md5s re-verified this fold). Counter 1/2; PE5 next.]**”

**FORM:** bracketed dated ARC record closing the header block.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the “minors only, no repair round owed” rule** is the same non-double-counting discipline HETOW and GENTOW1 apply: a CLEAN pass with minors scores, and its cures are a rider fold rather than a round.

**RESOLUTION TRACE:** lines 38–47.

**TEETH:** `git cat-file -t b6a43963` = commit ✓; **both cited md5s verified**: `gentow3_pe3_fresh.py` = `bde31247…`, `gentow3_pe3_fresh_output.txt` = `3ce4128a…` ✓.

---

### EFF.GENTOW3.06  [fence]

**CANONICAL STATEMENT:** the CHARGE, quoted in §1 A.

**FORM:** bold-headed charge paragraph.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the word “EXACTLY” in the charge is what r2/r3 spend two rounds calibrating — the delivered characterization is **one-sided**, not an iff (`.10`).

**RESOLUTION TRACE:** lines 49–53.

**TEETH:** XREF X01 — `GENHN-TOW-1` verified in GENHN at count 19.

---

### EFF.GENTOW3.07  [fence]

**CANONICAL STATEMENT:**

> “SOURCES CONSUMED (never edited): GENHN_PROOF_2026-08-08.md S8 [r2]
> annex — LEMMA GENHN-T(b)' clauses (i)-(iv), especially (iv) [THE
> STAGE SHADOW + FAITHFULNESS THRESHOLD] and its proof (functoriality
> of monic division; discrepancy Phi'(x0)H_j at dv2 >= u2 +
> dv2(H_j-class)); GENHN_passPE1_report.md (the three refuted n = 8
> instances, the 16Phi'-at-21 mechanism); GENTOW1_PROOF_2026-08-09.md
> (LEMMA GENTOW-1 budgets + Step 0 carry monotonicity, LEMMA GENTOW-5
> ledger, the constant E2 = e2f2u2); machine: gentow1_checks.py
> (families imported additively).”

**FORM:** bold-headed import inventory.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the import of GENTOW-1 carries GENTOW-1's grade**, and the conditionality stack says so: “LEMMA GENTOW-1 … and LEMMA GENTOW-5 at GENTOW-1's 0/2 grade” (`.41`). At HEAD GENTOW1 is ACCEPTED 2/2 (`spec/EFF-GENTOW1.md` `.59`), so this clause is **stale in the favorable direction** — recorded, not repaired (OPEN-CALL 4).

**RESOLUTION TRACE:** lines 55–63.

**TEETH:** all four sources exist; `gentow1_checks.py` md5 `6df4b213…` matches the pin recorded in both notes ✓ — a cross-note artifact identity, independently confirmed.

---

### EFF.GENTOW3.08  [table]  `[TABLE]`

**CANONICAL STATEMENT:** the status table, source lines 67–72:

| deliverable | statement | status |
|---|---|---|
| (a) per-height criterion | THEOREM GENTOW-3 (S2) | PROVED |
| (b) T(a) event-band survival | COR GENTOW-3.C (S3) | PROVED |
| (c) leaf failure quantified | S4 (PE1 anchors = first violation) | DONE |
| battery | gentow3_checks.py (S5) | GREEN 582/0, 3/3 teeth |

**FORM:** table.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** “PROVED” for (a) is scoped by GENTOW3-BOX-1: clauses (i)–(iii) are general, (iv)'s ATTAINMENT rests on a per-genre certificate (`.39`).

**RESOLUTION TRACE:** lines 65–72.

**TEETH:** the battery row re-verified (`.01`).

---

### EFF.GENTOW3.09  [definition]

**CANONICAL STATEMENT:**

>     “delta := u2 − e2·D'h   (>= 1: the [r1] node floor, integers)
>     THETA_j := (mu2 − j)·E2 + delta     (per composed coordinate j)”

**FORM:** indented ASCII display opening §S0 (“THE ONE CONSTANT AND THE THRESHOLD (announced up front)”).

**DERIVATION:** `[DEFINITIONAL]`; `delta ≥ 1` is the node floor imported from GENHN-1's erratum.

**CONDITIONALITY:** everything in the note is indexed by `delta`; the three S4 regimes are `delta = 1`, `delta ≥ 2`, x-free.

**RESOLUTION TRACE:** lines 76–77.

**TEETH:** **ARITHMETIC AUDIT across the five families, recomputed from `delta = u2 − e2D'h` with `D' = e1f1 = 2, h = 1`:** FAM-A5 `5 − 2·2 = 1` ✓; FAM-A7 `7 − 2·2 = 3` ✓; FAM-B `3 − 1·2 = 1` ✓; FAM-C `7 − 3·2 = 1` ✓; FAM-D `3 − 1·2 = 1` ✓ — **all five δ values in the S1 table reproduce**. And `Θ_j = (mu2−j)E2 + delta` at μ₂ = 2: A5 `2·10+1 = 21`, `1·10+1 = 11` ✓; A7 `2·14+3 = 31`, `1·14+3 = 17` ✓; B `2·6+1 = 13`, `7` ✓; C `2·21+1 = 43`, `22` ✓; D `13`, `7` ✓ — **all ten Θ values reproduce.**

---

### EFF.GENTOW3.10  [scope record]  *(CHAIN-GEOG — TERMINAL)*

**CANONICAL STATEMENT:** the geography clause at its r3 reading, verbatim:

> “THE GEOGRAPHY (proved in S2): the stage-shadow read is
> digit-faithful at every consulted dv2-height < THETA_j; at a
> non-x-free genre it can first fail no earlier than THETA_j, and
> at the coordinates carrying (iv)'s certificate (the key power's
> assembled height-THETA_j K2-digit does not cancel —
> GENTOW3-BOX-1) it DOES fail at THETA_j: there the floor is
> attained by the key power's own shadow. Where the digit cancels,
> what is proved is only that the KEY POWER's own first divergence
> sits strictly above THETA_j (measured FR-M3 (mu2 = 3):
> self-shadow pins [12, 7, 4] vs THETA [10, 7, 4], slack at j = 0,
> attained at j = 1, 2 — S7.6); other members can still fail at
> exactly THETA_j there, through scope remark (2)'s
> entry-digit-driven overflows — priced by the same Step-2 ledger
> at the same floor, and measured: the member
> f = Phi2³ + 2x·Phi2² + 8·Phi2 + 64 at FR-M3 j = 0 has first
> disagreeing height exactly 10 = THETA_0, the shadow undercutting
> the honest deciding vertex (0,12) -> (0,10)
> (gentow3_pe3_fresh.py, runner md5 bde31247, output md5 3ce4128a …)”

with the two dated brackets it carries, verbatim:

> “[GT3-r2: certificate-scoped — the composed clause asserted
> attainment certificate-free at "overflow genres", a term defined
> nowhere; S7.6. GT3-r3: one-sided — the r2 form's "fails AT
> THETA_j exactly at the coordinates carrying (iv)'s certificate"
> claimed an only-if that S2's attainment analysis (key-power-
> scoped) never proves and the measured W member refutes]”

and the closing x-free clause:

> “at x-free genres (every lift coefficient of the composed key an
> x-free monomial) it is faithful at EVERY height.”

**FORM:** inline paragraph carrying two nested dated brackets.

**DERIVATION:** the if-direction from S2(iv); the “only the key power” restriction from the scope of S2's attainment analysis; the existential counter-clause from a measured member.

**CONDITIONALITY:** **THREE LAYERS, and the effective reading is the third.** Composed (certificate-free, undefined term) → r2 (certificate-scoped but with a false “exactly”) → r3 (one-sided, with an existential measured witness). SUPERSESSION KINDs: **replacement** then **replacement**. A consumer must not read the geography as a biconditional in any form.

**RESOLUTION TRACE:** statement lines 79–105; the r2 round at 680–761; the r3 manifest at 763–815.

**TEETH:** **the two md5 pins in the cite are verified** (`bde31247…`, `3ce4128a…`) ✓, and the FR-M3 constants are re-derived at `.53`. **ARITHMETIC AUDIT of the FR-M3 slack claim:** at FR-M3 (`μ₂ = 3, E2 = 3, δ = 1`), `Θ = [(3−0)·3+1, (3−1)·3+1, (3−2)·3+1] = [10, 7, 4]` ✓ exactly as displayed; the measured self-shadow pins `[12, 7, 4]` then give slack `12 > 10` at j = 0 and equality at j = 1, 2 ✓ — the “slack at j = 0, attained at j = 1, 2” reading is exactly right.

---

### EFF.GENTOW3.11  [scope record]

**CANONICAL STATEMENT:**

> “The entry band (heights <= (mu2−j)E2) sits below THETA_j with
> margin delta at every genre — T(a)'s survival. At delta = 1 the
> first leaf height IS the threshold (the PE1 geography, 21 = 20+1);
> at delta >= 2 a faithful leaf band of width delta − 1 exists
> (FAM-A7: pins 29, 30 faithful; first violation 31).”

**FORM:** inline paragraph closing §S0.

**DERIVATION:** immediate from `Θ_j = (mu2−j)E2 + δ` — the entry band top is exactly δ below the threshold.

**CONDITIONALITY:** this is the seed of COR GENTOW-3.C (`.29`) and of S4's three regimes.

**RESOLUTION TRACE:** lines 106–110.

**TEETH:** **ARITHMETIC AUDIT:** at FAM-A5, entry top `mu2·E2 = 20` and `Θ_0 = 21 = 20 + 1` ✓ (the note's “21 = 20+1”). At FAM-A7 (`δ = 3`), the faithful leaf band is `[mu2E2+1, Θ_0−1] = [29, 30]`, width `δ − 1 = 2` ✓ — **exactly the two measured faithful rows A7-BAND29 and A7-BAND30**, and the first violation at `Θ_0 = 31` ✓. The band formula and the machine rows agree entry-for-entry.

---

### EFF.GENTOW3.12  [table]  `[TABLE]`

**CANONICAL STATEMENT:** the five-family constants table, source lines 119–125:

| family | genre | E2 | δ | Θ_0 | Θ_1 | entry top | Φ2² self-shadow pins |
|---|---|---|---|---|---|---|---|
| FAM-A5 | (2,1,4)→(2,1,2)/Q2 | 10 | 1 | 21 | 11 | 20 | (21, —) |
| FAM-A7 | (2,1,4)→(2,1,2)/Q2 | 14 | 3 | 31 | 17 | 28 | (31, —) |
| FAM-B | (2,1,4)→(1,2,2)/Q2 | 6 | 1 | 13 | 7 | 12 | (13, 7) |
| FAM-C | (2,1,6)→(3,1,2)/Q2 | 21 | 1 | 43 | 22 | 42 | (43, —) |
| FAM-D | (2,1,4)→(1,2,2)/Q3 | 6 | 1 | 13 | 7 | 12 | x-free: (—, —) |

**FORM:** table.

**DERIVATION:** constants derived from the imported GENTOW-1 genres; self-shadow pins are machine output.

**CONDITIONALITY:** the families are **imported additively from `gentow1_checks.py`** — so this note's battery and GENTOW1's share a genre roster, and GENTOW3-BOX-2 is “GENTOW-BOX-2's geography verbatim” (`.40`). The shared roster means the two notes' coverage gaps are the SAME gaps.

**RESOLUTION TRACE:** lines 115–125.

**TEETH:** **every derived column recomputed at `.09` and `.11`: all five δ, all ten Θ, all five entry tops (`mu2·E2` = 20/28/12/42/12 ✓).** The self-shadow pin column matches the SHARP want-lists quoted at `.48` (`[21, None] / [31, None] / [13, 7] / [43, None]`) ✓ and the S1 “—” entries are the identically-zero configuration `.55` later names.

---

### EFF.GENTOW3.13  [derivation]

**CANONICAL STATEMENT:**

> “READ OFF (then proved): (i) the key power Phi2^{mu2} — honest read
> DRAIN — casts a nonzero shadow whose pin lands at Θ_j EXACTLY at
> every non-x-free family (the shadow's fake content = the key's own
> Phi'-branch, invisible to the quotient); (ii) FAM-B touches BOTH
> coordinates (its lift −2x·Phi' is x-ful at the Y^{e2t}-step);
> (iii) FAM-D's lift −27 is x-free and its shadow is EXACT on a
> 12-member sweep — the geography has identically-faithful genres;
> (iv) the entry band top mu2·E2 sits δ below Θ_0 at every family.”

**FORM:** bold-headed four-item reading.

**DERIVATION:** examples-first: read off, then proved in S2.

**CONDITIONALITY:** item (i)'s “at every non-x-free family” is a statement about **these five families**, not a genre-general law — GENTOW3-BOX-1 (`.39`) is exactly the gap, and `.55` later measures a family where it fails (FR5X at μ₂ = 3, j = 0).

**RESOLUTION TRACE:** lines 127–134.

**TEETH:** (iv) recomputed for all five ✓ (`.12`); (iii)'s 12-member sweep is P-3 (`.36`).

---

### EFF.GENTOW3.14  [run-record]  `[TABLE]`

**CANONICAL STATEMENT:** the divergence table. **Source display, verbatim** (v3 rule 14 double emission):

>     “PE1-0 G=Y⁴+16Y+96      honest tRAM(25,14) shadow tRAM(21,14)
>           first divergence 21 = Θ_0; σ both {(8,1)} = parity luck
>     PE1-1 G=Y⁴+16Y³+32Y²+96 honest tRAM(21,14) shadow tINERT(28,14)
>           first divergence 21; shadow prices {(4,2)}, PARI {(8,1)}
>     PE1-2 G=..+224          honest tRAM(21,14) shadow t2SIDED(30,14)
>           first divergence 21; shadow prices {(4,1)²}, PARI {(8,1)}
>     A5-DEEP Phi2²+2⁵⁰xPhi'  honest tRAM(207) shadow tRAM(21)
>           divergence 21; σ both {(8,1)} — the parity-luck genre
>     A7-BAND29 Phi2²+32xPhi' p_0 = 29 < Θ_0 = 31: shadow = honest
>           tRAM(29), PARI {(8,1)} — a FAITHFUL LEAF (leaf depth is
>           not automatically unfaithful; the criterion is the height)
>     A7-BAND30 Phi2²+128x+4Phi'Phi2  pins (30,15), both < Θ: shadow
>           = honest tINERT, PARI {(4,2)} — faithful at Θ_0 − 1”

`[TABLE]` — transcription with the compiler's threshold check:

| row | honest | shadow | first divergence | Θ_0 | at/below Θ? | σ verdict |
|---|---|---|---:|---:|---|---|
| PE1-0 | tRAM(25,14) | tRAM(21,14) | 21 | 21 | AT | σ both {(8,1)} — pin corrupted, σ intact |
| PE1-1 | tRAM(21,14) | tINERT(28,14) | 21 | 21 | AT | shadow {(4,2)} vs PARI {(8,1)} — **σ corrupted** |
| PE1-2 | tRAM(21,14) | t2SIDED(30,14) | 21 | 21 | AT | shadow {(4,1)²} vs PARI {(8,1)} — **σ corrupted** |
| A5-DEEP | tRAM(207) | tRAM(21) | 21 | 21 | AT | σ both {(8,1)} |
| A7-BAND29 | tRAM(29) | = honest | none | 31 | BELOW | PARI {(8,1)}, faithful |
| A7-BAND30 | tINERT(30,15) | = honest | none | 31 | BELOW | PARI {(4,2)}, faithful |

**FORM:** fixed-width ASCII display (source) → table (transcription).

**DERIVATION:** `[RUN]`, PARI both-route adjudicated.

**CONDITIONALITY:** **the table proves the criterion is a HEIGHT criterion, not a depth criterion** — A7-BAND29's `p_0 = 29` is a decided LEAF read that is faithful because `29 < 31`. The note draws exactly that conclusion inline.

**RESOLUTION TRACE:** lines 136–151.

**TEETH:** **ARITHMETIC AUDIT: every row's classification reproduces from `.09`'s formula.** A5 rows: `Θ_0 = 21`, and all four A5-family rows diverge at exactly 21 ✓. A7 rows: `Θ_0 = 31`, and pins 29, 30 are both `< 31` ✓ with 30 = `Θ_0 − 1` ✓ exactly as labelled. **The two σ-corrupted rows (PE1-1, PE1-2) are the note's non-vacuity evidence** and are re-used at `.33` and `.62`.

---
### EFF.GENTOW3.15  [convention]  *(CHAIN-GAUGE — TERMINAL, in-body site)*

**CANONICAL STATEMENT:** the §S2 Setting, with its gauge pin, verbatim:

> “**Setting (T(b)' + GENTOW-1 S0, restated for one pass).** Tower
> locus 𝒯 (full inner side e2f2mu2 = mu1): outer genre
> (Q; e1, f1, mu1; h), key Phi' (deg D' = e1f1), inner slope
> kappa2 = u2/e2, composed key Phi2 (deg D2) [GT3-r1 GAUGE PIN
> (dated annex S7.1): Phi2's lift coefficients read chat_t :=
> lift(c_t·eta^{W(t)}), W(t) = floor((f2−t)·i(u2)/e1), per GENHN
> erratum 59c1966 — NOT the gauge-naive plain lift of c_t; at
> eta = 1 (all five S1 families) the two coincide], dv2 = e1e2·v, slot
> offsets w(a,b) = a·e2h + b·u2, E2 = e2f2u2.”

**FORM:** bold-headed setting with an in-line dated pin.

**DERIVATION:** `[IMPORTED]` from T(b)′ and GENTOW-1 S0.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of the key's coefficient display. The parenthetical “at eta = 1 (all five S1 families) the two coincide” is the coverage fact BOX-2 later calls a structural blindness (`.40`).

**RESOLUTION TRACE:** lines 155–163; annex 504–533.

**TEETH:** the formula `W(t) = ⌊(f₂−t)i(u₂)/e₁⌋` is identical in three notes of this queue (`EFF.HETOW.13`, `EFF.GENTOW1.06`, here) — a three-way cross-entry agreement on a corrected display.

---

### EFF.GENTOW3.16  [definition]

**CANONICAL STATEMENT:**

> “THE TWO READS at
> member f ∈ 𝒯, per composed coordinate j < mu2:
> * COMPOSED (honest): C_j from f = Phi2^{mu2} + Σ C_j Phi2^j in
>   Ô[x]; pins/residues by GENHN-2' slot-mins (accepted annex).
> * STAGE SHADOW (the refuted T(b) object): the two-variable division
>   F(x,Y) = Y^{mu1} + Σ A_J(x) Y^J = Σ_j Ĝ_j(x,Y)·K2(x,Y)^j carried
>   out over R = Ô[x]/(Phi') — every coefficient reduced mod Phi';
>   K2(x,Y) is the Y-form of the key (Phi2 = K2(x,Phi')). Shadow
>   coordinate ShC_j := Σ_b ḡ_{j,b}(x)Phi'^b (deg ḡ < D'), read on
>   the same slot grid. (Functoriality of monic division identifies
>   this with T(b)'(iv)'s Ĝ_j(θ,Y) — the (iv) proof, consumed.)”

**FORM:** bold-headed two-bullet definition.

**DERIVATION:** `[DEFINITIONAL]` + the functoriality identification imported from T(b)′(iv)'s proof.

**CONDITIONALITY:** **the shadow is “the refuted T(b) object”** — this note characterizes exactly when a KNOWN-WRONG read is nonetheless right. That framing is why the deliverable is a geography and not a correctness theorem.

**RESOLUTION TRACE:** lines 163–173.

**TEETH:** the identification with T(b)′(iv)'s object is consumed, not re-proved — an import recorded in the conditionality stack (`.41`).

---

### EFF.GENTOW3.17  [definition]  *(CHAIN-XFREE — TERMINAL, in-body site)*

**CANONICAL STATEMENT:**

> “X-FREE GENRES: call the genre x-free iff every lift coefficient
> ĉ_t·n̂(u2(f2−t)) of Phi2 (t < f2, ĉ_t ≠ 0) is an x-free monomial
> π^a — equivalently i(u2(f2−t)) = 0, i.e. e1 | u2(f2−t)·h⁻¹-class
> [GT3-r1: the "equivalently" reduction holds at f1 = 1 ONLY (there
> chat_t is a constant); at f1 >= 2 it is FALSE in general — the
> exact scope is re-derived in S7.1 (i-test AND c_t·eta^{W(t)} ∈
> F_Q). The PRIMARY clause — every lift coefficient an x-free
> monomial, read at the corrected chat_t — is the operative
> definition at every f1 and is what (iii)'s proof consumes];
> witness FAM-D: Phi2 = (x²−3)² + 27, lift = −27 = π³-flavor.”

**FORM:** bold-headed definition with an in-line dated scope bracket.

**DERIVATION:** `[DEFINITIONAL]`, with the equivalence re-derived at `.45`.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin**. **The PRIMARY clause is the operative definition; the displayed i-test is an f1 = 1 evaluation of it.** A consumer classifying genres at f1 ≥ 2 must use the primary clause, and the note is explicit that (iii) “so read needs no f1 restriction”.

**RESOLUTION TRACE:** statement lines 175–184; re-derivation 535–565.

**TEETH:** FAM-D is the witness and is machine-swept (P-3, 12 members, zero discrepancies, self-shadow DRAIN).

---

### EFF.GENTOW3.18  [theorem]

**CANONICAL STATEMENT:**

> “**THEOREM GENTOW-3 (the faithfulness geography).** Set
> delta := u2 − e2D'h (≥ 1, the [r1] node floor) and
> THETA_j := (mu2 − j)·E2 + delta. On 𝒯:
> (i) [FLOOR] every dv2-height at which ShC_j and C_j carry
> different slot digits is ≥ THETA_j; equivalently the first
> disagreeing height pin(ShC_j − C_j) ≥ THETA_j.”

**FORM:** bold-headed theorem, clause (i).

**DERIVATION:** Steps 0–2 (`.22`–`.24`).

**CONDITIONALITY:** **UNCONDITIONAL and gauge-immune** — S7.1's honest-status paragraph certifies it: “Step 0 and Steps 1–2 of the S2 proof are weight-level and value-blind … so clauses (i)/(ii) and their proofs are gauge-immune and uniform in f1 as claimed”. This is the note's strongest statement.

**RESOLUTION TRACE:** statement lines 186–191; proof 218–269.

**TEETH:** P-1 FLOOR 274 checks — every discrepancy height on 137 member_check calls clears Θ_j ✓ (census corrected at `.49`).

---

### EFF.GENTOW3.19  [theorem]

**CANONICAL STATEMENT:**

> “(ii) [FAITHFUL BAND] at every height m < THETA_j the two reads'
> digits agree — values, classes, and K2-residues. Consequently any
> read whose consulted heights at coordinate j are all < THETA_j
> (pins, deciding residues, event data) returns identical output on
> both reads; in particular if the composed pin p_j < THETA_j then
> the shadow pin equals it with the same residue.”

**FORM:** theorem clause.

**DERIVATION:** “(ii) is (i) restated” (`.25`).

**CONDITIONALITY:** unconditional and gauge-immune, as (i). **This is the clause every downstream protection rides**, and S4's count-law is explicitly “(ii)'s one-sided law” (`.33`).

**RESOLUTION TRACE:** statement lines 192–197; proof 270–272.

**TEETH:** P-6 LABEL 6 rows (members with pins below Θ have identical labels + σ) and the two A7-BAND rows ✓.

---

### EFF.GENTOW3.20  [theorem]

**CANONICAL STATEMENT:**

> “(iii) [X-FREE EXACTNESS] at an x-free genre the discrepancy is
> ZERO at every height: ShC_j = C_j identically on 𝒯 — the shadow
> IS the composed read.”

**FORM:** theorem clause.

**DERIVATION:** `.26` — no x-overflow ever occurs, so reduction mod Φ′ is the identity.

**CONDITIONALITY:** reads at the PRIMARY x-free definition (`.17`), under which S7.1 certifies “(iii)'s proof is correct at every f1”.

**RESOLUTION TRACE:** statement lines 198–200; proof 273–278.

**TEETH:** P-3 XFREE 3 checks + a 12-member FAM-D sweep with zero discrepancies and a DRAIN self-shadow ✓.

---

### EFF.GENTOW3.21  [theorem]

**CANONICAL STATEMENT:**

> “(iv) [ATTAINMENT — the leaf-depth failure] at a non-x-free genre
> whose key power's self-overflow is non-cancelling (certificate
> below; machine-checked at FAM-A5/A7/B/C), the floor is ATTAINED:
> f = Phi2^{mu2} has composed read DRAIN (C_j = 0) while its shadow
> read carries a nonzero digit at exactly THETA_j at the touched
> coordinate(s) [GT3-r2 PIN: "touched" is the CERTIFICATE sense —
> coordinate j is touched iff the key power's assembled
> height-THETA_j K2-digit (the proof's single-Phi'-extraction sum)
> does not cancel, i.e. GENTOW3-BOX-1's certificate holds at
> (genre, j); NOT the weaker "ShC_j ≠ 0" — a measured frame
> separates the two readings (FR-M3 j = 0: ShC_0 = 64 ≠ 0 with pin
> 12 while the height-THETA_0 = 10 digit cancels), and (iv) is true
> under the certificate reading only — S7.6] — and deep
> perturbations (disc ≠ 0) keep the
> divergence. The shadow read at heights ≥ THETA_j is NOT a function
> of the honest data.”

**FORM:** theorem clause with an in-statement dated definition pin.

**DERIVATION:** `.27`.

**CONDITIONALITY — THREE separate supersessions land on this one clause:**
1. **The “touched” pin ([GT3-r2])** is IN the statement — the only statement-internal edit of the arc (`.03`). SUPERSESSION KIND: **scope-pin**, and the note argues it is “the reading the (iv) proof supports, no weakening”.
2. **“deep perturbations … keep the divergence”** — its INFERENCE is withdrawn by **S8.1** and the conclusion re-derived under the GENTOW-1(a) box hypothesis (`.58`). KIND: **replacement of a justification**.
3. **The closing sentence** is superseded twice — by **S8.2** and then **S8.4** (CHAIN-NONFUNC, TERMINAL `.62`). KIND: **replacement**, then **replacement**.
**A consumer reading (iv) as displayed would carry a withdrawn inference and a doubly-withdrawn scope.**

**RESOLUTION TRACE:** statement lines 201–216; proof 279–302; corrections 894–939 (S8.1), 941–961 (S8.2), 998–1035 (S8.4).

**TEETH:** the certificate is machine-checked at four families (SHARP 11 rows); the FR-M3 separation is machine-pinned at `.52`.

---

### EFF.GENTOW3.22  [derivation]

**CANONICAL STATEMENT:**

> “**Step 0 (weights, from GENTOW-1 Step 0 — consumed).** For a
> two-variable monomial π^v x^{a'} Y^{b'} (a', b' unrestricted) set
> wt := e1e2·v + a'·e2h + b'·u2. The x-carry x^{D'} = Phi' + tail
> splits weight-monotonically: tail branches at weight ≥ parent
> (equality on the key's side), the Phi'-branch at parent + delta
> EXACTLY (x^{D'}-part carries D'e2h, the Phi'-part u2). The
> Phi'-carry Phi'^{e2f2} = Phi2 + lifts is weight-preserving with
> the Phi2-part at E2 (GENTOW-1 Step 0 verbatim).”

**FORM:** bold-headed step.

**DERIVATION:** `[IMPORTED]` from GENTOW-1 Step 0, with the δ-quantification made explicit.

**CONDITIONALITY:** **the “+ delta EXACTLY” is the whole engine of the note** — every discrepancy branch pays δ per Φ′-extraction, which is why the floor is `(mu2−j)E2 + δ`.

**RESOLUTION TRACE:** lines 220–227.

**TEETH:** **ARITHMETIC AUDIT:** the Φ′-branch weight is `u2` against the `x^{D'}` weight `D'e2h`, a gain of `u2 − e2D'h = δ` ✓ — exactly the definition at `.09`. Cross-entry: this is the same Step 0 compiled at `EFF.GENTOW1.19`, and both entries record it as VALUE-BLIND.

---

### EFF.GENTOW3.23  [derivation]

**CANONICAL STATEMENT:**

> “**Step 1 (the division ledger: Ĝ_j sits at weight ≥ (mu2−j)E2).**
> On 𝒯 the entry pins lie weakly above the inner side:
> e2·dv(A_J) ≥ (mu1 − J)u2, so every term of A_J·Y^J has
> wt ≥ (mu1−J)u2 + J·u2 = mu1·u2 = mu2·E2; Y^{mu1} likewise. Every
> term of K2 has wt = E2 exactly (side terms of the key — T(b)'(i)).
> Monic division in Y is weight-monotone against such a key … Iterating the K2-division mu2 times from
> F (wt ≥ mu2E2): every term of Ĝ_j(x,Y) has wt ≥ (mu2−j)E2 — in
> the UNREDUCED weight (x-degrees kept literal; the division is
> LINEAR in F, so Ĝ_j-terms are A_J·(products of K2-coefficients),
> x-degree ≤ (D'−1) + Σ i_t-parts).”

**FORM:** bold-headed step.

**DERIVATION:** a weight-monotone induction down the Y-degree.

**CONDITIONALITY:** **the LINEARITY noted here is what S8.1 later exploits** to re-derive persistence — and also what S8.1 shows was mis-used in the composed (iv) proof.

**RESOLUTION TRACE:** lines 229–243.

**TEETH:** **ARITHMETIC AUDIT:** `(mu1−J)u2 + J·u2 = mu1·u2`, and `mu1·u2 = (e2f2mu2)·u2 = mu2·(e2f2u2) = mu2·E2` ✓ — the identity uses the full-side hypothesis exactly once, as it must.

---

### EFF.GENTOW3.24  [derivation]

**CANONICAL STATEMENT:** Step 2, the proof of (i), `[ASSEMBLED]` from lines 245–269. The three branch classes, verbatim:

> “* an x-overflow monomial of Ĝ_j (a' ≥ D', wt ≥ (mu2−j)E2 by
>   Step 1) reduces along x^{D'} = Phi' + tail: the shadow keeps
>   only the iterated tail route (weight ≥ parent); every branch
>   retaining k ≥ 1 Phi'-factors sits at wt ≥ parent + k·delta ≥
>   (mu2−j)E2 + delta = THETA_j (Step 0);
> * branches whose Phi'-exponent reaches e2f2 recarry through
>   Phi2 = Phi'^{e2f2} − lifts INTO coordinate j+1: arriving content
>   came from Ĝ_{j'} (j' ≤ j) overflow branches with k ≥ e2f2 − b' ≥
>   1 extractions per Phi2-step, each Phi2-absorption spending E2 of
>   weight: slot weight at the receiving coordinate j ≥
>   (mu2−j')E2 + k·delta − (j−j')E2 ≥ (mu2−j)E2 + delta = THETA_j.
>   Recarry moves content only UPWARD in j (division uniqueness —
>   T(b)'(iv)'s recarry remark, consumed);
> * the reduction discrepancy at each division step feeds forward
>   into later steps only through coefficients already ≥ THETA-
>   floored …”

and the conversion to heights, verbatim:

> “By GENHN-2' each slot digit's dv2-value is the slot-min exactly and
> heights separate classes (one K2-digit per height), so
> "difference supported at weights ≥ THETA_j" reads off as: every
> disagreeing HEIGHT is ≥ THETA_j. ∎(i)”

**FORM:** three-bullet proof step.

**DERIVATION:** a branch census with per-branch pricing, closed by GENHN-2′'s weight-to-height conversion.

**CONDITIONALITY:** the conversion consumes GENHN-2′ (accepted annex).

**RESOLUTION TRACE:** lines 245–269.

**TEETH:** **ARITHMETIC AUDIT of the recarry bound, recomputed:** `(mu2−j')E2 + k·δ − (j−j')E2 = (mu2−j)E2 + k·δ ≥ (mu2−j)E2 + δ` for `k ≥ 1` ✓ — the displayed chain is exact, and the `(j−j')E2` subtraction is exactly the E2-per-Φ₂-absorption spend. **This is the step S8.1 re-runs on g** to get the strict `+1`.

---

### EFF.GENTOW3.25  [derivation]

**CANONICAL STATEMENT:**

> “(ii) is (i) restated: below THETA_j the digit strings coincide, and
> every displayed read-output (pin values, residues, labels, σ,
> event data) is a function of the consulted digits. ∎(ii)”

**FORM:** one-line proof clause.

**DERIVATION:** immediate from (i) plus the observation that read outputs are functions of consulted digits.

**CONDITIONALITY:** none. **The parenthetical list (pins, residues, labels, σ, event data) is the same tuple S8.2 later tries to use as a non-functionality scope and S8.4 withdraws** — the tuple is well-defined as a *dependency* list here but not as a *committed object* there (`.61`).

**RESOLUTION TRACE:** lines 270–272.

**TEETH:** guarded by P-6 LABEL.

---

### EFF.GENTOW3.26  [derivation]

**CANONICAL STATEMENT:**

> “(iii): at an x-free genre every K2-coefficient is x-free, the
> division's coefficient arithmetic never raises x-degree above
> deg A_J ≤ D'−1 < D': no x-overflow ever occurs, reduction mod Phi'
> is the identity on every coefficient, and Σ_b g_{j,b}Phi'^b (all
> x-degrees < D2, Phi'-exponents < e2f2) is the unique composed
> development: ShC_j = C_j. ∎(iii)”

**FORM:** proof clause.

**DERIVATION:** a degree argument: no overflow ⟹ the mod-Φ′ reduction is the identity ⟹ the two developments coincide by uniqueness.

**CONDITIONALITY:** reads at the PRIMARY x-free definition; S7.1 certifies it needs no f1 restriction there.

**RESOLUTION TRACE:** lines 273–278.

**TEETH:** P-3 (FAM-D, 12-member sweep, zero discrepancies) ✓.

---

### EFF.GENTOW3.27  [derivation]

**CANONICAL STATEMENT:** the proof of (iv), `[ASSEMBLED]` from lines 279–302. The mechanism and the certificate, verbatim:

> “(iv): for f = Phi2^{mu2} the composed division is exact: C_j = 0,
> all j < mu2 — the honest read is DRAIN. The shadow object is the
> self-shadow of the key power: K2(x,Phi')^{mu2} = Phi2^{mu2}, but
> the shadow division sees F = the level-1 development of Phi2^{mu2},
> whose x-overflow content (the products of x-ful lift monomials
> crossing D') re-enters as genuine level-1 data that the reduced
> K2-powers can no longer cancel. All terms of K2^{mu2} sit at
> wt = mu2E2 exactly; the minimal surviving branch is a single
> Phi'-extraction: height THETA_j at the touched coordinate,
> NONZERO whenever the assembled K2-digit does not cancel — the
> per-genre CERTIFICATE, decided by one finite computation
> (machine-checked: A5/A7/C touch j = 0 with digits 16Phi'/64Phi'/
> 64Phi' at 21/31/43; B touches BOTH: ShC_1 = 4Phi' + 8x at 7,
> ShC_0 = 64Phi' + 64x at 13) [GT3-r1 attribution: "machine-checked"
> = the PINS (the sealed SHARP want-lists), which are the
> certificate; the digit VALUES were hand-derived at composition and
> gained machine legs at PE1 — S7.2].”

and the deep-perturbation close, verbatim (the sentence S8.1 withdraws):

> “Deep perturbation f = Phi2^{mu2} + g
> (g in-budget with slots at heights > THETA_j, disc ≠ 0): both
> reads shift by the SAME g-digits (linearity of both divisions in
> f), so the divergence at THETA_j persists while the honest read
> becomes a decided leaf … ∎(iv)”

**FORM:** proof clause with an in-line dated attribution pin.

**DERIVATION:** a minimal-branch identification (single Φ′-extraction at height Θ_j) plus a per-genre non-cancellation certificate.

**CONDITIONALITY:** **the last sentence's INFERENCE is WITHDRAWN by S8.1** (`.58`) — “linearity gives (Sh - C)(f0 + g) = (Sh - C)(f0) + (Sh - C)(g), not Sh(g) = C(g)”. The CONCLUSION survives, re-derived under the box hypothesis. Also: the parenthetical hypothesis “(slots at heights > THETA_j)” is explicitly **NOT consumed** by the corrected derivation; the GENTOW-1(a) box hypothesis is.

**RESOLUTION TRACE:** lines 279–302; correction 894–939.

**TEETH:** the digit values gained two independent legs at PE1 (`.48`): the verifier's hand walks and the fresh instrument's FR-P5 exact polynomial replications.

---

### EFF.GENTOW3.28  [fence]

**CANONICAL STATEMENT:**

> “**Scope remarks (honest).** (1) The certificate in (iv) is a
> non-cancellation of one explicitly displayed K2-digit; it is
> decided per genre by finite arithmetic, machine-checked at the
> five battery families, NOT proved as a genre-general
> non-vanishing (GENTOW3-BOX-1, S6) — the floor (i)/(ii)/(iii) is
> general. (2) Attainment via entry-digit-driven overflows (genres
> where the key self-power stays below D' in x but products with
> full-degree entry digits overflow) is covered by the same Step-2
> ledger but no witness battery row is shipped; named in
> GENTOW3-BOX-1. (3) Everything is per-coordinate and in-window;
> the window interaction is GENTOW-5(a)'s cap (consulted heights
> also < e1e2·N) — orthogonal, composes by min.”

**FORM:** bold-headed three-item scope remark.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **remark (2) is what r3's existential clause later instantiates** — the “other members can still fail at exactly THETA_j … through scope remark (2)'s entry-digit-driven overflows” of `.10`. So the composed text already contained the mechanism that refuted r2's “exactly”; r3 connected them.

**RESOLUTION TRACE:** lines 304–315.

**TEETH:** remark (3)'s composition-by-min is the interface to `EFF.GENTOW1.35`'s cap clause — and that clause was itself restated three-band by GENTOW1's R2c, which does not disturb the min composition (heights only).

---

### EFF.GENTOW3.29  [corollary]

**CANONICAL STATEMENT:**

> “**COROLLARY GENTOW-3.C.** On 𝒯, the inner CS event's data — the
> level-1 side (J, dv(A_J)) with residual psi2^{mu2}, i.e. the datum
> T(a) detects and T(b)' consumes — is read identically by the stage
> shadow and the composed frame, at EVERY genre, with margin δ:
> (1) the level-1 coefficients A_J have degree < D', so the mod-Phi'
> projection is the identity on them: the entry read is
> discrepancy-free outright; (2) recast at the composed frame
> (GENTOW-1(a)'s entry gate), the event data occupies dv2-heights
> ≤ (mu2−j)E2 per coordinate — the inner side's height range — and
> (mu2−j)E2 = Θ_j − δ < Θ_j: THEOREM GENTOW-3(ii) gives digit
> agreement on the whole band, for every genre (δ ≥ 1 is the [r1]
> node floor, unconditional on 𝒯). Hence the sentence in
> GENHN-T(b)'(iv) — "this inequality HOLDS at the entry/event band"
> — previously machine-verified at the PE1 instances and the P8
> witness only, is now a THEOREM: [GENHN-TOW-1] item (3)'s
> parenthetical ("T(a)'s event-band survival as a theorem") is
> discharged. Machine face: the ENTRY tally (274 checks …). ∎”

**FORM:** bold-headed corollary with a two-leg proof.

**DERIVATION:** two independent legs — (1) is degree-level and needs no threshold at all; (2) rides (ii) with the δ margin.

**CONDITIONALITY:** **UNCONDITIONAL at every genre** — this is the note's cleanest result, and it is the one that upgrades a supplier's machine-verified sentence to a theorem. **The upgrade is NOT landed on GENHN** (`.42`, N1).

**RESOLUTION TRACE:** lines 320–338.

**TEETH:** ENTRY 274 checks. **Honest caveat recorded by the note itself** at `.50`: “the ENTRY tally 274 is entailed by FLOOR 274 given delta >= 1 — honest as COR 3.C's machine face, not independent evidence.” Disposition `disclosed non-independence` — a rare and valuable self-assessment.

---

### EFF.GENTOW3.30  [scope record]

**CANONICAL STATEMENT:** the δ = 1 regime, verbatim:

> “* **δ = 1 (u2 = e2D'h + 1 — the PE1 geography).** Θ_j = the node
>   floor: (ii)'s faithful leaf band is EMPTY (width δ − 1 = 0), no
>   leaf height is criterion-protected, and at a coordinate carrying
>   (iv)'s certificate the key power's own shadow diverges at the
>   FIRST leaf height itself [GT3-r2: certificate-scoped; the
>   composed "the FIRST leaf height is already unfaithful" is
>   REFUTED as a per-member δ = 1 claim — S7.6]. FAM-A5 (certificate
>   machine-checked at j = 0): Θ_0 = 21; the PE1 instances' first
>   divergence is 21 on each of the three rows … "Fails generically at leaf
>   depth" is sharp here in the BAND sense only: a Θ-reaching
>   decided leaf can still read faithfully when the discrepancy
>   digits it would consult vanish or sit off its hull (measured:
>   FR-M3, δ = 1, certificate cancelled at j = 0 — f = Phi2³ + 32
>   decides at pin 10 = Θ_0 with hulls and vertex digits identical
>   on both reads, PARI σ {(6,1)} on both routes — S7.6).”

**FORM:** bulleted regime with an in-line dated correction.

**DERIVATION:** `Θ_j = (mu2−j)E2 + 1` coincides with GENTOW-1(c)'s node floor `(mu2−j)E2 + 1`.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** — the composed per-member claim is REFUTED, and the surviving claim is band-level. **The refuting member is measured and committed.**

**RESOLUTION TRACE:** lines 347–363; the r2 round 680–761.

**TEETH:** **ARITHMETIC AUDIT: at δ = 1, `Θ_j = (mu2−j)E2 + 1` is exactly GENTOW-1(c)'s node floor** (`EFF.GENTOW1.17`) ✓ — the two notes' constants coincide precisely at δ = 1, which is why the faithful band is empty. The refuting member's pin `10 = Θ_0` at FR-M3 is verified at `.10`'s audit ✓.

---

### EFF.GENTOW3.31  [scope record]

**CANONICAL STATEMENT:**

> “* **δ ≥ 2.** A faithful leaf band of width δ − 1 exists:
>   [(mu2−j)E2 + 1, Θ_j − 1]. FAM-A7 (δ = 3): pins 29 and 30 are
>   decided LEAF reads on which shadow = honest with PARI-confirmed
>   σ (A7-BAND rows) — leaf depth alone does not break the shadow;
>   the first violation is Θ_0 = 31, where the supp sweep's
>   stage-INERT(36)-vs-true-RAM(31) row (GENHN_PROOF S8 [r2] annex)
>   sits exactly.”

**FORM:** bulleted regime.

**DERIVATION:** the band is `[node floor, Θ_j − 1]`, of width `δ − 1`.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 364–370.

**TEETH:** **ARITHMETIC AUDIT: at FAM-A7, `[mu2E2+1, Θ_0−1] = [29, 30]`, width 2 = δ − 1 ✓**, and both members of the band are measured faithful (`.14`) — the band is not merely non-empty but exhaustively exercised at this family.

---

### EFF.GENTOW3.32  [scope record]

**CANONICAL STATEMENT:**

> “* **x-free genres.** No violation at any height (FAM-D sweep) —
>   T(b)'s stage algebra is retroactively EXACT there; its
>   refutation was a statement about the x-ful genres.”

**FORM:** bulleted regime.

**DERIVATION:** (iii).

**CONDITIONALITY:** **this is a positive scope result about a REFUTED object** — the refutation of T(b)'s stage algebra is localized to x-ful genres.

**RESOLUTION TRACE:** lines 371–373.

**TEETH:** P-3 ✓.

---

### EFF.GENTOW3.33  [scope record]

**CANONICAL STATEMENT:** the count-law meaning at its r2 reading, verbatim:

> “The count-law meaning [GT3-r2 rewrite: the composed biconditional
> ("mislabeled exactly on … the entire leaf population") is REFUTED
> by measurement in both directions — S7.6]: strata priced through
> shadow pins can be corrupted ONLY on members with a consulted
> height ≥ Θ_j — (ii)'s one-sided law. At δ = 1 the node floor
> itself sits at Θ_j, so this protection excludes no leaf stratum;
> at δ ≥ 2 it protects the width-(δ−1) leaf band; at x-free genres
> the discrepancy is zero and nothing is corrupted. Reaching Θ_j is
> NECESSARY, not sufficient: actual mislabeling further needs the
> divergent digit PRESENT on the member and CONSULTED at the
> pricing granularity. Measured instances: the PE1-1/PE1-2 σ-strata
> corrections … Measured non-instances: FR-M3's
> f = Phi2³ + 32 (decided AT Θ_0 = 10; hulls and vertex digits
> identical on both reads — faithful) and the S1 table's own PE1-0
> row (first divergence 21 = Θ_0, σ both {(8,1)} = parity luck —
> pin-corrupted, σ-stratum intact).”

**FORM:** paragraph with an in-line dated rewrite bracket.

**DERIVATION:** (ii)'s one-sided law, plus a necessity-not-sufficiency analysis with measured instances AND non-instances on both sides.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of a biconditional by a one-sided law. **The note supplies measured witnesses in BOTH directions** — corrupted (PE1-1/2) and uncorrupted-at-Θ (FR-M3, PE1-0) — which is what makes the one-sidedness demonstrated rather than merely conceded.

**RESOLUTION TRACE:** lines 375–391.

**TEETH:** all four cited rows are in `.14`'s recomputed table or `.52`'s FR-M3 record ✓.

---
