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
