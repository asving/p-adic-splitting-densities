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
### EFF.GENTOW3.34  [instrument-record]

**CANONICAL STATEMENT:**

> “INSTRUMENT: `verification/openmath/gentow3_checks.py`, sealed at
> commit 5ac0d80 (predictions P-1..P-7 + 3 teeth in the docstring
> BEFORE the first full run; design smoke disclosed there: the A5
> self-shadow row and PE1 row-2 shadow pin, both matching the hand
> derivation; two pre-seal instrument fixes made before sealing —
> the A5-DEEP construction had double-added Phi2^{mu2}, and the PE1
> shadow-label wants were tightened to tINERT/t2SIDED from the hand
> computation). Runner md5 at the verdict run:
> 7cf3a7b8a580d6b9893d8e62f94464e2 — BIT-IDENTICAL to seal; no
> post-seal edit of any kind.”

**FORM:** bold-headed instrument record.

**DERIVATION:** `[RECORD]` — a two-commit seal with pre-seal fixes disclosed.

**CONDITIONALITY:** **“BIT-IDENTICAL to seal; no post-seal edit of any kind”** — note the contrast with GENTOW1, whose sealed runner needed a disclosed post-seal repair (`EFF.GENTOW1.42`). This instrument's seal is clean.

**RESOLUTION TRACE:** lines 395–404.

**TEETH:** **`md5sum gentow3_checks.py` = `7cf3a7b8a580d6b9893d8e62f94464e2`** — matches exactly ✓. `git cat-file -t 5ac0d80` = commit ✓.

---

### EFF.GENTOW3.35  [run-record]  `[TABLE]`

**CANONICAL STATEMENT:** the verdict. **Source display, verbatim:**

>     “GREEN — 582 checks, 0 violations, 3/3 teeth.
>     Tally: FLOOR 274, ENTRY 274, SHARP 11, LABEL 6, XFREE 3,
>     BAND 2, PE1 3, GP-SIG 6, TEETH 3.”

with its header: “VERDICT RUN (this repo, 2026-08-09, output `gentow3_checks_output.txt` md5 926cd05f)”.

`[TABLE]` — transcription:

| FLOOR | ENTRY | SHARP | LABEL | XFREE | BAND | PE1 | GP-SIG | TEETH |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 274 | 274 | 11 | 6 | 3 | 2 | 3 | 6 | 3 |

**MANDATORY ARITHMETIC AUDIT (v3 rule 22):** 274 + 274 + 11 + 6 + 3 + 2 + 3 + 6 + 3 = **582** ✓ — the nine-category tally sums exactly to the headline. **Cross-verified against the committed artifact**, whose last two lines read `=== VERDICT: GREEN -- 582 checks, 0 violations (0.1s) ===` and `tally: {'FLOOR': 274, 'ENTRY': 274, 'SHARP': 11, 'LABEL': 6, 'XFREE': 3, 'BAND': 2, 'PE1': 3, 'GP-SIG': 6, 'TEETH': 3}` — **all nine categories match** ✓.

**FORM:** indented ASCII verdict block (source) → table.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** ENTRY 274 is **entailed by** FLOOR 274 given δ ≥ 1 and is disclosed as non-independent (`.50`) — so the effective independent check count is lower than 582.

**TEETH:** `md5sum gentow3_checks_output.txt` = `926cd05f…` ✓.

---

### EFF.GENTOW3.36  [run-record]

**CANONICAL STATEMENT:** the per-prediction scoring, `[ASSEMBLED]` from lines 413–429. P-1 with its census correction, verbatim:

> “P-1 (FLOOR, 274): every discrepancy height on 110
> members (nec + real + anchors, five families) clears Θ_j [GT3-r1
> census correction: the true count is 137 member_check calls =
> 274/2 — 5 × (14 nec + 12 real + 1 anchor) + 2 A7-BAND rows; "110"
> undercounted (omitted the 20 perturbation variants, 5 anchors, 2
> band rows) — S7.3].”

P-2 through P-7 in brief, verbatim where sharpest:

> “P-2
> (SHARP): self-shadow pins landed at the preregistered Θ values
> (A5/A7/C: 21/31/43 at j = 0 only; B: 13 AND 7 — both
> coordinates); A5-DEEP honest tRAM(207) vs shadow tRAM(21), PARI
> {(8,1)}. P-3 (XFREE): FAM-D lift coefficients x-free, 12-member
> sweep zero discrepancies, self-shadow DRAIN. P-4 (ENTRY, 274):
> zero discrepancy inside the entry band on every member. P-5
> (BAND): A7 rows at 29 (tRAM) and (30,15) (tINERT) shadow = honest,
> PARI {(8,1)}/{(4,2)}. P-6 (LABEL, 6): members with pins below Θ
> have identical labels+σ. P-7 (PE1): honest (25,14)/(21,14)/(21,14)
> tRAM vs shadow (21,14) tRAM/(28,14) tINERT/(30,14) t2SIDED, first
> divergence 21 = Θ_0 on each, PARI {(8,1)} ×3.”

**FORM:** bulleted per-prediction list with an in-line census correction.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** SUPERSESSION KIND on the census: **counter re-reading**, in the CONSERVATIVE direction (“more was checked than the sentence claimed”, `.49`).

**RESOLUTION TRACE:** lines 413–429.

**TEETH:** **ARITHMETIC AUDIT of the corrected census, recomputed:** `5 × (14 + 12 + 1) + 2 = 5 × 27 + 2 = 137` ✓, and `137 × 2 coordinates = 274` = the FLOOR tally ✓. **The sealed tally and the corrected census reconcile exactly**, which is what proves “110” was the error and 274 was always right.

---

### EFF.GENTOW3.37  [run-record]

**CANONICAL STATEMENT:** the three teeth, verbatim:

> “TEETH: T-THRESH-UP
> x4 (the Θ+1 mutant is killed by each self-shadow row —
> disagreement AT Θ); T-BAND-EDGE x1 (the Θ−1 mutant calls height
> 30 unfaithful; agreement + PARI refute it); T-SHADOW-REG x1 (the
> shadow reproduces the refuted stage pins and its priced σ differs
> from PARI on rows 1–2) [GT3-r1 disclosure: the σ-comparison branch
> in the sealed runner is DEAD CODE (gentow3_checks.py L398–399, a
> literal `pass`); the tooth fires on pins + labels matching the
> preregistered wants alone; the σ-difference is ENTAILED by the
> machine-checked labels through the accepted (iii) dictionary, not
> compared in-code — S7.4].”

**FORM:** teeth list with an in-line dated disclosure.

**DERIVATION:** `[RUN]` — two threshold mutants (Θ+1 and Θ−1) and one regression tooth.

**CONDITIONALITY:** **T-SHADOW-REG's σ-leg is DEAD CODE and the note says so** — the tooth fires on pins + labels only; the σ-difference is *entailed*, not *compared*. SUPERSESSION KIND: **disclosed non-repair**.

**RESOLUTION TRACE:** lines 429–439; the disclosure section 640–654.

**TEETH:** **THE DEAD-CODE CLAIM IS VERIFIED VERBATIM AT COMPILE TIME.** `verification/openmath/gentow3_checks.py` lines **398–399** read exactly:

```
        if i > 0 and rs[3] is not None and rs[3] != [(8, 1)]:
            pass  # shadow-priced sigma wrong vs PARI: tooth part
```

— a literal `pass`, at the stated line numbers ✓. **The two threshold mutants are the note's anti-vacuity pair**: T-THRESH-UP kills “the floor is higher than Θ” and T-BAND-EDGE kills “the floor is lower than Θ”, so Θ is pinned from both sides by machine.

---

### EFF.GENTOW3.38  [fence]

**CANONICAL STATEMENT:**

> “**What stays open in [GENHN-TOW-1] (untouched here):** items (4)
> (partial inner sides — 𝒯 here is FULL-side; every S2–S4 statement
> is scoped to it) and (6)(alpha) at its GENTOW-2 grade; item (3)'s
> box text asked for the faithfulness geography — delivered above —
> with the two named residues below.”

**FORM:** bold-headed residue fence.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **item (4) is the third independent fencing of the partial-side gap in this queue** (`EFF.HETOW.28`, `EFF.GENTOW1.46`, here) — at HEAD it is GENTOW-4's territory.

**RESOLUTION TRACE:** lines 443–447.

**TEETH:** N1 (the box is live and undischarged).

---

### EFF.GENTOW3.39  [fence]

**CANONICAL STATEMENT:**

> “**GENTOW3-BOX-1 (attainment certificate).** THEOREM GENTOW-3(iv)'s
> sharpness rests on a per-genre non-cancellation certificate (the
> key power's height-Θ K2-digit ≠ 0), decided by finite arithmetic
> and machine-checked at the five families; a genre-general
> non-vanishing proof, and battery witnesses for entry-digit-driven
> overflows at genres where the key self-power stays below D' in x,
> are NOT delivered. The floor/faithful-band/x-free clauses
> (i)–(iii) — the criterion itself — are general.”

**FORM:** bold-headed box.

**DERIVATION:** `[RECORD]` of the note's one mathematical residue.

**CONDITIONALITY:** **OPEN at HEAD**, and the note's last word on it is `.55`'s three-configuration data point: “BOX-1 stays OPEN.” **The box's separation of general (i)–(iii) from certificate-conditional (iv) is the note's central honesty structure** and is what every downstream consumer must carry.

**RESOLUTION TRACE:** lines 449–456; the data point at 845–867.

**TEETH:** disposition `signed non-delivery`, with three measured configurations now on record (`.55`).

---

### EFF.GENTOW3.40  [fence]

**CANONICAL STATEMENT:**

> “**GENTOW3-BOX-2 (machine coverage).** Rows exercise mu2 = 2, f1 =
> 1 outer keys, q ∈ {2,3}, e2 ∈ {1,2,3}, f2 ∈ {1,2}, depth 2, d = 1
> ambients — GENTOW-BOX-2's geography verbatim (the same imported
> families). The S2 proof is uniform in (e1, f1, e2, f2, mu2, q, h);
> the gap is machine-side. [GT3-r1 HONEST STATUS (S7.1): the
> uniformity claim holds for the S2 PROOF under the PRIMARY x-free
> definition read at the corrected key; the displayed i-test
> reduction is f1 = 1-scoped, so as composed the gap was NOT
> machine-side only. The machine gap is two-axis: the five committed
> families sit at f1 = 1 AND eta = 1 …, so the sealed battery is
> structurally blind to the gauge seam; the eta != 1 coverage is the
> adopted FR-GL row (S7.1); f1 >= 2 classification rows exist
> nowhere yet.]”

**FORM:** bold-headed box with an in-line dated honest-status rider.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** of a false self-assessment. **“the gap is machine-side” was WRONG as composed** — the displayed classification test was f1 = 1-scoped, i.e. a PROOF-side gap. The rider is the note's own refutation of its own coverage claim, and it is unusually blunt.

**RESOLUTION TRACE:** lines 458–471; the derivation 566–584.

**TEETH:** `signed coverage disclosure`, two-axis. The η ≠ 1 coverage is the single adopted FR-GL row (`.47`); f1 ≥ 2 has **zero** rows in any leg.

---

### EFF.GENTOW3.41  [acceptance-box]

**CANONICAL STATEMENT:**

> “**GRADE: 0/2 (attempt; composed this session, no hostile arc).**
> Conditionality stack: consumes LEMMA GENHN-T(b)' (i)–(iv) — (iii)
> enters through the σ-dictionary the battery's labels price —
> (GENHN accepted 2/2 at PE4) [GT3-r1: AT THE CORRECTED KEY …], LEMMA GENTOW-1 (Step 0 carry
> monotonicity, budgets, node floors) and LEMMA GENTOW-5 at
> GENTOW-1's 0/2 grade, the [r1] node floor u2 > e2D'h, and S4's
> coherent normalizers. Machine leg = S5 (this unit's sealed
> battery; PARI cross-checks on 6 σ rows).”

**FORM:** bold-headed grade + conditionality stack.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the grade → **ACCEPTED 2/2** (`.54`). **The stack's “at GENTOW-1's 0/2 grade” is stale in the FAVORABLE direction**: GENTOW1 is ACCEPTED 2/2 at HEAD (verified in this queue). Recorded as OPEN-CALL 4, not repaired.

**RESOLUTION TRACE:** lines 473–482.

**TEETH:** the GENTOW1 grade is independently established at `spec/EFF-GENTOW1.md` `.59`.

---

### EFF.GENTOW3.42  [fence]

**CANONICAL STATEMENT:** the consumption path, quoted in §1 B.

**FORM:** bold-headed protocol fence.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **precondition met (2/2), discharge NOT done.** Two obligations are named: the item-(3) discharge AND the (iv)-sentence upgrade from “machine-verified” to “theorem (GENTOW-3.C)”.

**RESOLUTION TRACE:** lines 484–489.

**TEETH:** N1 — `grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` = **0** ✓.

---

### EFF.GENTOW3.43  [changes-record]

**CANONICAL STATEMENT:**

> “PE1 verdict (GENTOW3_passPE1_report.md @ 3101cf5): NOT CLEAN —
> 1 GAP (F-1, the gauge seam at the x-free definition) + 3 MINOR
> (m-1 digit-value attribution, m-2 P-1 census, m-3 T-SHADOW-REG's
> dead σ-leg); counter stays 0/2. This section is the r1 repair
> round; this round's edits are marked [GT3-r1] ([r1] bare in the
> body refers, as before, to GENHN-1's node-floor erratum). Sealed
> machine artifacts (gentow3_checks.py + output; the PE1 fresh
> instrument gentow3_pe1_fresh.py + both outputs; the import base
> gentow1_checks.py) are BYTE-UNTOUCHED by this round (md5s S7.5).”

**FORM:** section preamble.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the same `[r1]` / `[GT3-r1]` tag-disambiguation as GENTOW1** — bare `[r1]` is GENHN-1's node-floor erratum. Respected throughout this compilation.

**RESOLUTION TRACE:** lines 494–502.

**TEETH:** all five named artifacts exist with matching md5s (§3.2) ✓.

---

### EFF.GENTOW3.44  [changes-record]  *(CHAIN-GAUGE — the annex)*

**CANONICAL STATEMENT:** §S7.1's seam and corrected display, verbatim:

> “**The seam.** This note's verdict commit (d90db6d, 08-09 15:53)
> predates the GENHN dated gauge erratum (59c1966, 08-09 20:13):
> LEMMA GENHN-T(b)''s original display of the composed key's lift
> coefficients … is GAUGE-NAIVE … The note as composed consumed the pre-erratum display and
> carried no gauge pin; its one VALUE-LIVE chat_t site is the S2
> x-free genre definition, whose displayed "equivalently" clause is
> moreover false at f1 >= 2 on its own terms (below).”

> “**THE PINNED CORRECTED DISPLAY (per erratum 59c1966; = GENTOW1's
> S7.1 pin):**
>
>     chat_t := lift(c_t·eta^{W(t)}),
>     W(t)   := floor((f2−t)·i(u2)/e1)”

with the site inventory:

> “This pin governs chat_t at its S2 uses: the Setting's Phi2/K2
> displays, Step 0's Phi'-carry lifts (value-blind — heights
> unchanged), the (iii)/(iv) coefficient values, and the x-free
> classification.”

**FORM:** bold-headed annex with a display.

**DERIVATION:** `[IMPORTED]` from GENHN's erratum.

**CONDITIONALITY:** **this note's VALUE-LIVE site is DIFFERENT from GENTOW1's.** GENTOW1's value-live site was Step 5's residue computation (`EFF.GENTOW1.24`); here it is the **x-free classification**. Two sibling notes consumed the same defective display and it bit in two different places — a cross-entry fact worth carrying.

**RESOLUTION TRACE:** lines 504–533.

**TEETH:** `git cat-file -t d90db6d` = commit; `git cat-file -t 59c1966` = commit ✓. The timestamp gap (15:53 vs 20:13, same day) is the same provenance form GENTOW1 uses (15:16 vs 20:13) — **both notes' verdict commits predate the erratum by hours**, which is exactly why both consumed it naively.

---

### EFF.GENTOW3.45  [derivation]  *(CHAIN-XFREE — TERMINAL)*

**CANONICAL STATEMENT:** the re-derived equivalence, verbatim:

> “**The x-free equivalence RE-DERIVED (the correct scope).** Write
> m_t := u2(f2−t) and nhat(m) = π^{(m−i(m)h)/e1}·x^{i(m)}. Since
> {1, eta, ..., eta^{f1−1}} is an F_Q-basis of K and eta's lift is
> (x^{e1}/π^h)-shaped, the height-m_t lift of c = Σ_{r<f1}
> lambda_r·eta^r ∈ K is L_{m_t}(c) = nhat(m_t)·Σ_r
> lift(lambda_r)·(x^{e1}/π^h)^r: its x-support is
> {i(m_t) + e1·r : lambda_r ≠ 0} — pairwise-distinct exponents, all
> < D' = e1f1 (no overflow, no cancellation). Hence, per t with
> c_t ≠ 0, at the corrected key:
>
>     chat_t·nhat(m_t) is an x-free monomial π^a
>         <=>  i(m_t) = 0  AND  c_t·eta^{W(t)} ∈ F_Q.”

with the scope, verbatim:

> “SCOPE. At f1 = 1 (K = F_Q) the second clause is automatic and the
> displayed "equivalently i(u2(f2−t)) = 0" is CORRECT … At f1 >= 2 the display is FALSE in general: the i-test is
> necessary, not sufficient … eta = 1 does NOT
> restore the equivalence at f1 >= 2 (the second clause then reads
> c_t ∈ F_Q, i.e. psi2 ∈ F_Q[Z] — not automatic when K ⊋ F_Q); what
> eta = 1 buys is only corrected = naive. THE PRIMARY CLAUSE …
> is the operative definition at
> every f1 … and (iii) so read needs no f1 restriction. The
> displayed i-test survives as the f1 = 1 evaluation of the primary
> clause, nothing more.”

**FORM:** bold-headed re-derivation with a displayed biconditional.

**DERIVATION:** an explicit computation of the height-m_t lift's x-support, giving a two-clause criterion.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin**. **The η = 1 caveat is the sharpest observation here**: η = 1 buys corrected = naive but does NOT restore the equivalence at f1 ≥ 2 — so the battery's blindness is genuinely two-axis, not one.

**RESOLUTION TRACE:** lines 535–565.

**TEETH:** **ARITHMETIC AUDIT of the x-support claim, recomputed:** the exponents `i(m_t) + e1·r` for `0 ≤ r < f1` are pairwise distinct (they differ by multiples of `e1` with `0 ≤ i(m_t) < e1`) ✓ and bounded by `(e1−1) + e1(f1−1) = e1f1 − 1 = D' − 1` ✓ — **the same degree chain GENTOW1's `.18` verifies for its (LIFT) form**, reached independently here.

---

### EFF.GENTOW3.46  [changes-record]

**CANONICAL STATEMENT:**

> “**BOX-2's f1-uniformity claim walked under the primary definition
> (the honest status).** Step 0 and Steps 1–2 of the S2 proof are
> weight-level and value-blind — corrected and naive lifts sit at
> the same heights ((f2−t)u2 per digit) — so clauses (i)/(ii) and
> their proofs are gauge-immune and uniform in f1 as claimed;
> (iii)'s proof is correct at every f1 under the primary definition
> (above); (iv)'s certificate framework is general with certificates
> machine-checked at the five f1 = 1 families only (GENTOW3-BOX-1,
> unchanged). What sat FALSE inside the claimed uniform scope was
> the classification TEST … HONEST STATUS: BOX-2's sentence "the gap is
> machine-side" was wrong as composed …”

**FORM:** bold-headed clause-by-clause walk.

**DERIVATION:** a per-clause audit of the note's own uniformity claim.

**CONDITIONALITY:** **the walk's verdict is clause-differentiated and should be carried as such**: (i)/(ii) gauge-immune and f1-uniform; (iii) correct at every f1 under the primary definition; (iv) general framework, certificates at f1 = 1 only; the TEST was f1 = 1-scoped.

**RESOLUTION TRACE:** lines 566–584.

**TEETH:** `AUDIT / in-house hostile pass` (PE1 found F-1); the walk itself is the note's response and is unusually granular.

---

### EFF.GENTOW3.47  [run-record]

**CANONICAL STATEMENT:** the FR-GL row, `[ASSEMBLED]` from lines 586–608. The frame and the attainment, verbatim:

> “**THE MACHINE ROW (adopted from the PE1 fresh route): FR-GL — this
> note's first eta != 1 contact, at the corrected key, attainment at
> BOTH coordinates.** Source: gentow3_pe1_fresh.py + outputs @
> 3101cf5 (run 2 GREEN 485/0, runner md5 35ad32aa, output md5
> 94160b22; run 1 RED 485/1 KEPT, md5 485946fc — the one miss a
> disclosed instrument literal, no prediction changed). Frame …:
> p = 3, Phi' = x²−6 (e1 = 2, f1 = 1, h = 1, eta = 2),
> (e2, f2) = (1, 2), u2 = 3, K2 = F9, CORRECTED key Phi2 =
> Phi'² + 3x·Phi' + 108 (the HETOW frame-X key; note W(0) = 1 with
> i(6) = 0 — a lift coefficient whose normalizer is x-free and whose
> VALUE is gauge-live: naive 54 vs corrected 108), delta = 1,
> E2 = 6, THETA = (13, 7). Rows: self-shadow ShC_0 = −486·Phi' +
> 2916x (both slots at dv2 = 2·5+3 = 2·6+1 = 13 = THETA_0), ShC_1 =
> 9·Phi' − 27x (both slots at 2·2+3 = 2·3+1 = 7 = THETA_1) — the
> floor ATTAINED at both coordinates …
> At the gauge-NAIVE key this frame is not even a carrier (σ
> {(4,1)}, erratum 59c1966) — the row is meaningful only at the
> corrected key.”

**FORM:** bold-headed adopted-row record.

**DERIVATION:** `[RUN]` — a decorrelated fresh route, with run 1 RED **kept** and its single miss disclosed.

**CONDITIONALITY:** **this frame IS HETOW's frame X** — the note says so (“the HETOW frame-X key”), and the key `Φ′² + 3xΦ′ + 108` is byte-identical to `EFF.HETOW.14`'s corrected key. **Three notes in this queue exercise the same frame** (HETOW, GENTOW1 as F1, GENTOW3 as FR-GL), each from a different instrument.

**RESOLUTION TRACE:** lines 586–608.

**TEETH:** **all three md5s verified**: `gentow3_pe1_fresh.py` = `35ad32aa…`, output = `94160b22…`, run-1 RED = `485946fc…` ✓. **ARITHMETIC AUDIT of the frame constants, recomputed:** `D' = e1f1 = 2`, `E2 = e2f2u2 = 1·2·3 = 6` ✓, `δ = u2 − e2D'h = 3 − 1·2·1 = 1` ✓, `Θ = (2·6+1, 1·6+1) = (13, 7)` ✓. **The slot heights recompute both ways as displayed**: `2·5+3 = 13` and `2·6+1 = 13` ✓; `2·2+3 = 7` and `2·3+1 = 7` ✓ — the two-flavor slots land at the same height, which is the f2 = 2 two-flavor structure. **The gauge factor**: naive 54 vs corrected 108 = `54·η^{W(0)} = 54·2` ✓ — identical to HETOW's frame-X pair (`EFF.HETOW.14`), independently confirmed from a second note.

---

### EFF.GENTOW3.48  [changes-record]

**CANONICAL STATEMENT:**

> “The sealed instrument machine-checks the PINS — the SHARP
> want-lists [21, None] / [31, None] / [13, 7] / [43, None] at
> A5/A7/B/C, i.e. self-shadow nonzeroness AT THETA, which IS the
> (iv) certificate. The digit VALUES displayed in S2's (iv)
> parenthetical … were HAND-DERIVED at
> composition — they appear in no sealed machine output. At PE1 the
> values gained two legs: (leg 1) the verifier's independent
> division walks (report m-1: each value confirmed by hand); (leg 2)
> the fresh instrument's FR-P5 battery-digit replication rows, exact
> polynomial equality (output: A5 [−32, 0, 16] = 16Phi'; A7 and C
> [−128, 0, 64] = 64Phi'; B [−128, 64, 64] = 64Phi' + 64x and
> [−8, 8, 4] = 4Phi' + 8x; D DRAIN). Attribution now: pins = the
> sealed leg; digit values = the PE1 walk + the FR-P5 replication.”

**FORM:** section body (§S7.2).

**DERIVATION:** an attribution audit separating what the SEAL checked (pins) from what was hand-derived (values).

**CONDITIONALITY:** SUPERSESSION KIND: **provenance-rider**. **The pins ARE the certificate** — so the certificate has a sealed leg even though the displayed digit values did not.

**RESOLUTION TRACE:** lines 610–626.

**TEETH:** **ARITHMETIC AUDIT of the replication rows, recomputed:** with `Φ′ = x²−2` at the A5/A7/C families, `16Φ′ = 16x² − 32` → coefficient list low→high `[−32, 0, 16]` ✓; `64Φ′ = 64x² − 128` → `[−128, 0, 64]` ✓; `64Φ′ + 64x` → `[−128, 64, 64]` ✓; `4Φ′ + 8x = 4x² + 8x − 8` → `[−8, 8, 4]` ✓. **All four displayed polynomial identities reproduce exactly.**

---

### EFF.GENTOW3.49  [changes-record]  *(CHAIN-CENSUS — TERMINAL)*

**CANONICAL STATEMENT:**

> “Re-counted from the FLOOR battery's code paths at this round:
> member_check calls = 5 families × (14 nec [10 bases + 4
> deep-perturbation variants at i ≡ 0 mod 3, per nec_members] + 12
> real + 1 anchor) + 2 A7-BAND rows = 137; × 2 coordinates = 274
> FLOOR checks = the sealed tally. "110" counted nec-bases + real
> only (50 + 60), omitting the 20 perturbation variants, the 5
> anchors, and the 2 band rows despite naming anchors. Conservative
> direction — more was checked than the sentence claimed. The S5
> sentence carries the in-place [GT3-r1] correction.”

**FORM:** section body (§S7.3).

**DERIVATION:** a re-count from code paths, reconciled against the sealed tally.

**CONDITIONALITY:** SUPERSESSION KIND: **counter re-reading**, conservative direction.

**RESOLUTION TRACE:** lines 628–638.

**TEETH:** **ARITHMETIC AUDIT, both the wrong figure and the right one:** `5×27 + 2 = 137` ✓, `137×2 = 274` = the sealed FLOOR tally ✓; and the erroneous decomposition `50 + 60 = 110` ✓ (5×10 bases + 5×12 real). **Both arithmetics reproduce, which pins the error precisely: 137 − 110 = 27 = 20 perturbation variants + 5 anchors + 2 band rows** ✓ — exactly the note's three omitted classes.

---

### EFF.GENTOW3.50  [changes-record]

**CANONICAL STATEMENT:**

> “In the sealed runner the σ-comparison branch is a literal `pass`
> (gentow3_checks.py L398–399: `if i > 0 and rs[3] is not None and
> rs[3] != [(8, 1)]: pass`); the tooth fires on honest/shadow labels
> + pins matching the preregistered wants alone. The σ-difference in
> the S5 tooth description is ENTAILED by machine-checked facts —
> the shadow labels tINERT/t2SIDED force priced σ {(4,2)}/{(4,1)²}
> through the accepted (iii) dictionary, against PARI-checked
> {(8,1)} on PE1 rows 1–2 — but the comparison itself is not
> executed in-code. The sealed runner stays byte-frozen; the
> disclosure lives at the S5 tooth row and here. (Related report
> observation, no finding: the ENTRY tally 274 is entailed by FLOOR
> 274 given delta >= 1 — honest as COR 3.C's machine face, not
> independent evidence.)”

**FORM:** section body (§S7.4).

**DERIVATION:** a source reading of the sealed runner.

**CONDITIONALITY:** **TWO disclosures of non-independence in one paragraph** — the dead σ-leg and the entailed ENTRY tally. Both reduce the note's effective evidence and both are volunteered.

**RESOLUTION TRACE:** lines 640–654.

**TEETH:** **the dead code is verified verbatim at L398–399** (`.37`) ✓. The ENTRY-entailment is verified by inspection: FLOOR ≥ Θ_j and the entry band ends at `Θ_j − δ ≤ Θ_j − 1`, so zero entry discrepancy follows from the floor whenever `δ ≥ 1` ✓ — the entailment is real, and the disclosure is correct.

---
### EFF.GENTOW3.51  [instrument-record]

**CANONICAL STATEMENT:** the r1 edit manifest and md5 ledger, verbatim:

> “Body state before this round: md5 8664269e723c7779538f25329490c06d
> = the PE1 target (verdict commit d90db6d). [GT3-r1] edit sites:
> (1) header ARC line; (2) S2 Setting gauge pin at the Phi2 display;
> (3) S2 x-free-definition scope pin; (4) S2 (iv) attribution pin;
> (5) S5 P-1 census correction; (6) S5 T-SHADOW-REG disclosure;
> (7) S6 GENTOW3-BOX-2 honest-status rider; (8) S6
> conditionality-stack corrected-key pin; (9) this S7. Edit shape:
> [GT3-r1]-bracketed INSERTIONS plus this S7 … the statement displays of
> THEOREM GENTOW-3 (i)–(iv), COR GENTOW-3.C, and the S0/S1/S3/S4
> texts sit outside the inserted brackets … Sealed
> machine artifacts BYTE-FROZEN, md5s verified before and after this
> round: gentow3_checks.py 7cf3a7b8a580d6b9893d8e62f94464e2,
> gentow3_checks_output.txt 926cd05f4be21a24e66b84c325ce679e,
> gentow3_pe1_fresh.py 35ad32aab60f5c4fbb09cd6b69ae6c18,
> gentow3_pe1_fresh_output.txt 94160b22ca919276d61a2ed4f5d374d5,
> gentow3_pe1_fresh_output_run1_RED.txt
> 485946fc773f7d57289f3731d2e51de2, import base gentow1_checks.py
> 6df4b213ed0aab6afa37ac7b418540aa. Grade stays 0/2; PE2 next.”

**FORM:** section body (§S7.5) — a nine-site manifest with a six-md5 ledger.

**DERIVATION:** `[RECORD]` — written for the next pass's diff.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 656–678.

**TEETH:** **ALL SIX md5s RE-COMPUTED AND MATCHED at compile time** ✓ — including `gentow1_checks.py 6df4b213…`, which is the SAME hash GENTOW1's own S5 pins (`EFF.GENTOW1.42`). **A cross-note artifact identity, verified from both sides.** F-1's whole-body pin also verified (`git cat-file -p d90db6d:<file> | md5sum` = `8664269e…`) ✓.

---

### EFF.GENTOW3.52  [changes-record]  *(SERIES REPAIR-SECTIONS, r2)*

**CANONICAL STATEMENT:** §S7.6, `[ASSEMBLED]` from lines 683–761. The verdict and the re-derivation, verbatim:

> “PE2 verdict (GENTOW3_passPE2_report.md @ c048154): NOT CLEAN — 1
> GAP (F-1: three record sentences — the S0 geography clause, the
> S4 δ = 1 bullet, the S4 count-law — asserted per-coordinate
> attainment/mislabeling CERTIFICATE-FREE, plus "touched
> coordinate(s)" undefined in the (iv) statement); counter stays
> 0/2.”

> “**The re-derivation (from this note's own S2 (iv) proof and
> GENTOW3-BOX-1, per the repair rule — not from the report's
> wording).** Step 2 proves the FLOOR unconditionally. The (iv)
> proof then exhibits the MINIMAL candidate branch … and proves its digit "NONZERO
> whenever the assembled K2-digit does not cancel": BOX-1's
> per-genre, per-coordinate non-cancellation certificate. So what
> the theorem PROVES is attainment AT THETA_j at exactly the
> certificate-carrying coordinates; where the assembled digit
> cancels, (i) still floors the discrepancy but its first height
> sits strictly ABOVE THETA_j.”

The two refuting instances, verbatim in brief: **FR-M3** (`p = 2, Phi' = x²−2, Phi2 = Phi'−2x` per the r3 m-A label fix, `e2 = f2 = 1, u2 = 3, mu2 = 3, delta = 1, E2 = 3, THETA = [10,7,4]`): self-shadow `ShC = [[64], [0, 40], [12]]`, pins `[12, 7, 4]` — the height-10 digit at j = 0 CANCELS; and **the count-law counter-member** `f = Phi2³ + 32` at FR-M3, honest pins `[10, ∞, ∞]` decided, shadow pins `[10, 7, 4]` with fake pins strictly above the deciding edge, “hulls IDENTICAL, vertex digit IDENTICAL, PARI σ {(6,1)} on both routes”.

The non-vacuity check and the consumer walk, verbatim in brief: FAM-A5 still attains at 21 (“Nothing became vacuous”); and

> “**Consumer walk (the three sentences).** GENTOW6_PROOF S3 — the
> one downstream consumer of (iv)-adjacent content — consumes
> THEOREM GENTOW-3(i) and BOX-1's certificate FRAMING …: already
> certificate-conditional; none of the three sentences is cited.
> docs/PROJECT_STATE.md append #12 records this unit through
> floor/band/x-free + "the PE1 refutations = the criterion's first
> violations exactly" — no overclaim carried … No consumer edit owed.”

**FORM:** numbered repair section with re-derivation, verification, non-vacuity check, consumer walk and manifest.

**DERIVATION:** re-derived from the note's own (iv) proof, explicitly “not from the report's wording” — the standing repair rule.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin** on three record sentences + **scope-pin inside the (iv) statement** (the “touched” definition pin). **The r2 S0 rewrite is itself over-corrected at r3** (CHAIN-GEOG).

**RESOLUTION TRACE:** lines 680–761; the over-correction at 763–789.

**TEETH:** **the FOUR-PART repair structure — re-derivation, refuting instances, non-vacuity check, consumer walk — is the most complete repair protocol in this queue.** The non-vacuity check in particular (“Nothing became vacuous”) is a discipline no other entry performs. **ARITHMETIC AUDIT of FR-M3's constants:** `E2 = e2f2u2 = 1·1·3 = 3` ✓, `δ = u2 − e2D'h = 3 − 1·2·1 = 1` ✓, `Θ = [3·3+1, 2·3+1, 1·3+1] = [10, 7, 4]` ✓ — all three reproduce. `git cat-file -t c048154` = commit ✓; the three adopted PE2-fresh artifacts all exist with matching md5s (`55208baf…`, `06b4bddf…`, and the run-1 RED) ✓.

---

### EFF.GENTOW3.53  [changes-record]  *(SERIES REPAIR-SECTIONS, r3)*

**CANONICAL STATEMENT:** §S7.7, `[ASSEMBLED]` from lines 767–815. The verdict and the fold's scope, verbatim:

> “PE3 verdict (GENTOW3_passPE3_report.md @ a1c181d): NOT CLEAN — 1
> GAP (F-1: the r2 S0 clause's "fails AT THETA_j exactly at the
> coordinates carrying (iv)'s certificate" claimed an only-if S2's
> key-power-scoped attainment analysis never proves, refuted by the
> measured W witness member) + 1 MINOR (m-A: the S7.6 FR-M3 record
> handed Phi2's polynomial to Phi'); counter stays 0/2. The r3
> round (landed at 8165208) shipped its record in the header ARC
> paragraph plus two inline brackets but no numbered section and no
> in-note artifact pins for the adopted W measurement; passPE4
> (CLEAN, 0 GAP + 1 MINOR, counter 0/2 -> 1/2; report @ b6a43963)
> flagged the traceability hole as its m-1. This S7.7 is that fold
> — record-discipline only; no S0/S2/S4/S7.6 claim re-adjudicated.”

The adopted W measurement, verbatim:

> “**THE ADOPTED W MEASUREMENT (artifact pins).** Instrument:
> gentow3_pe3_fresh.py, md5 bde312470601ede13338691573cfb96f;
> output gentow3_pe3_fresh_output.txt, md5
> 3ce4128ad44b360ecc8cea762b12af69 (sealed pre-run @ 16a729bd,
> verdict @ a1c181d; output verdict line: GREEN — 451 checks, 0
> violations, teeth 3/3). Both md5s re-computed against the
> committed files at this fold. Re-derived from the pinned runner
> itself (not from any report sentence): at FR-M3 … the runner
> builds gW = 2x·Phi2² + 8·Phi2 and checks W-A = Phi2³ + gW and
> W-B = W-A + 64 (runner L410–417, fkM = Phi2³ at L378); the
> machine-checked want-lists (L418–431, GREEN in the pinned
> output): W-B honest pins [12,6,3], shadow pins [10,6,3], ShC_0 =
> 96 vs C_0 = 64, mindiff [10,9,4] — first disagreeing height at
> j = 0 EXACTLY 10 = THETA_0 … W-A likewise
> mindiff_0 = 10 …; witness census 32 gated members with mindiff_0 = 10 …”

**FORM:** numbered repair section (a post-hoc record fold).

**DERIVATION:** the W measurement is **re-derived from the pinned runner itself**, explicitly “not from any report sentence” — the strongest provenance discipline available.

**CONDITIONALITY:** **this fold is record-discipline only**: “no S0/S2/S4/S7.6 claim re-adjudicated”. The mathematical content (the one-siding) landed at r3; this section supplies its traceability.

**RESOLUTION TRACE:** lines 763–815.

**TEETH:** **both md5s verified** (`bde31247…`, `3ce4128a…`) ✓; the output's verdict line re-read: `=== VERDICT: GREEN -- 451 checks, 0 violations, teeth 3/3 ===` ✓ with teeth `{'T3-UP': 8, 'T3-DOWN': 5, 'T3-BICOND': 2}`. **Note the third tooth's name — `T3-BICOND`** — the fresh route carried a tooth specifically against the biconditional reading, which is what refuted r2's “exactly”. `git cat-file -t 16a729bd` = commit ✓. **The r3 diff figures are also stated and checkable**: “3 hunks, 39 insertions / 12 deletions” between `a1c181d..8165208`, both commits resolving ✓.

---

### EFF.GENTOW3.54  [acceptance-box]  *(SERIES ARC, link 5; CHAIN-GRADE)*

**CANONICAL STATEMENT:**

> “**GENTOW3 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP +
> 1 MINOR, GENTOW3_passPE4_report.md @ b6a43963; counter 0/2 -> 1/2)
> followed by passPE5 CLEAN (0 CRITICAL + 0 GAP + 0 MINOR — ZERO
> findings, GENTOW3_passPE5_report.md @ 0633c6a3; counter 1/2 ->
> 2/2): two consecutive clean hostile passes, the standing
> acceptance bar. **THE NOTE IS FROZEN AT THIS RECORD: dated appends
> and dated brackets only; statement displays and sealed artifacts
> stay byte-untouched.**”

with the arc, verbatim:

> “The arc in one breath: seal (2026-08-09; S5 machine leg GREEN
> 582/0) -> PE1 NOT CLEAN 1G+3m @ 3101cf5 (the GAUGE …) -> r1 @ e1a8dfe … -> PE2 NOT CLEAN 1G @
> c048154 (the CERTIFICATE SEAM …) -> r2 @ 0d09d65 … -> PE3 NOT CLEAN 1G+1m @
> a1c181d (r2's OVER-CORRECTION: the inserted "exactly" only-if,
> refuted by the measured W member at FR-M3) -> r3 @ 8165208 (the
> ONE-SIDING …) -> PE4 CLEAN 0G+1m @
> b6a43963, the arc's first clean pass -> rider @ d6b409ce … -> PE5 CLEAN 0 GAP +
> 0 MINOR @ 0633c6a3.”

**FORM:** bold-headed acceptance record with a one-breath arc.

**DERIVATION:** `[RECORD]` of two consecutive CLEAN passes, the second with ZERO findings.

**CONDITIONALITY:** superseded only in status by S8's “ACCEPTED 2/2 stands ANNOTATED” (`.57`).

**RESOLUTION TRACE:** lines 817–843.

**TEETH:** **all eight commits in the arc resolve**: `3101cf5`, `e1a8dfe`, `c048154`, `0d09d65`, `a1c181d`, `8165208`, `b6a43963`, `d6b409ce`, `0633c6a3` ✓ (nine, counting the rider). **The arc names its own over-correction** — “r2's OVER-CORRECTION” — which is the honesty marker that makes this note's history reusable as a methodology datum.

---

### EFF.GENTOW3.55  [run-record]  *(SERIES CERTIFICATE-CONFIG)*

**CANONICAL STATEMENT:**

> “**PE5 obs-1 recorded as data (the THIRD certificate
> configuration; named for the GENTOW3-BOX-1 residue).** At PE5's
> fresh frame FR5X (p = 2, Phi' = x²−2, e2 = 2, f2 = 1, delta = 9 —
> the largest delta in any leg of this arc — run at mu2 = 2 AND
> mu2 = 3; instrument gentow3_pe5_fresh.py md5 9acab757, output
> fc4f8d55, GREEN 287/0, verdict @ 2c8bb507), the key power's
> self-shadow rows read off the committed output (lines 2 and 4):
> mu2 = 2: G = [4096·Y, 0], pins [61, None] — ATTAINED at
> 61 = THETA_0, j = 1 IDENTICALLY ZERO; mu2 = 3: G = [2^19·xY,
> 12288·Y, 0], pins [91, 61, None] vs THETA [87, 61, 35] — SLACK at
> j = 0 (the height-87 digit cancels, the first divergence sits
> strictly above THETA_0), ATTAINED at j = 1, IDENTICALLY ZERO at
> j = 2. The identically-zero shadow coordinate is a stronger
> failure form than FR-M3's cancelled-digit-with-slack …: the coordinate is untouched vacuously, which is
> exactly how the (iv) certificate pin classifies it … Data point
> for GENTOW3-BOX-1: this arc has now MEASURED three certificate
> configurations — attained, slack, identically zero — and a
> genre-general certificate law (BOX-1's open ask) has these three
> measured cases to decide among … BOX-1 stays OPEN.”

**FORM:** bold-headed observation record.

**DERIVATION:** `[RUN]` at a new fresh frame, read off the committed output by line number.

**CONDITIONALITY:** **this is DATA for an open box, not a repair** — the note is explicit that BOX-1 stays open. Its value is that it enumerates the three configurations a general law must cover.

**RESOLUTION TRACE:** lines 845–867.

**TEETH:** **both md5s verified** (`9acab757…`, `fc4f8d55…`) ✓; output verdict re-read: `=== VERDICT: GREEN -- 287 checks, 0 violations ===` ✓ with tally `[('BAND', 4), ('DIV', 3), ('ENTRY', 120), ('FLOOR', 120), ('GP', 6), ('REP', 11), ('SELF', 11), ('SWEEP', 2), ('TEETH', 3), ('WIT', 7)]`. **ARITHMETIC AUDIT: 4+3+120+120+6+11+11+2+3+7 = 287** ✓ — the ten-category tally sums exactly to the headline. **The FR5X constants recompute:** `D' = e1f1 = 2`, `E2 = e2f2u2` with `e2 = 2, f2 = 1` and `δ = u2 − e2D'h = 9` gives `u2 = 9 + 2·2·1 = 13`, so `E2 = 2·1·13 = 26`; then `Θ` at μ₂ = 3 is `[3·26+9, 2·26+9, 1·26+9] = [87, 61, 35]` ✓ **exactly as displayed**, and at μ₂ = 2 `Θ_0 = 2·26+9 = 61` ✓ **exactly the attained pin**. Every constant in the observation reproduces from δ = 9 alone. `git cat-file -t 2c8bb507` = commit ✓.

---

### EFF.GENTOW3.56  [instrument-record]

**CANONICAL STATEMENT:**

> “BYTE-FREEZE LEDGER (this round): pre-append body md5
> 1e753d199950bc591a95962686f25ed3 (815 lines) = the rider state @
> d6b409ce; this record is a PURE APPEND on that body, verified by
> prefix md5 after the append. Sealed artifacts byte-frozen: the
> eleven S7.5/S7.6/S7.7 pinned md5s re-verified at PE5 (report S
> machine leg, four isolated re-runs bit-identical + the known gp
> stderr line); no runner edited, no re-run this round.”

**FORM:** bold-headed freeze ledger.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 869–875.

**TEETH:** **VERIFIED: lines 1–815 hash to `1e753d199950bc591a95962686f25ed3`** ✓ — both the md5 and the stated 815-line count reproduce. All eleven pinned artifact md5s re-verified (§3.2) ✓.

---

### EFF.GENTOW3.57  [record]  *(SERIES ARC, link 6)*

**CANONICAL STATEMENT:**

> “Provenance: decorrelated-model adversarial RUN B (record
> CODEX_TOWERRAT2_2026-08-10.md S3; raw log
> verification/openmath/towerrat2_runB_gentow3_output.txt, md5
> 32751d5d, 6,297 B; outcome CHALLENGE — 2 JUSTIFICATION GAPs, 16
> CHECKED-CLEAN lines), adjudicated 2/2 REAL at their stated severity.
> Both corrections are RE-DERIVED from this note's own Steps 0-2 and
> the committed FR-M3 artifacts, not transcribed from the verifier;
> the note is frozen, so both land as dated corrections BY SUPERSESSION
> (the superseded sentences stay byte-intact above and read as
> corrected here).”

with the section heading's grade clause: “**acceptance 2/2 stands ANNOTATED, per the batch charter**”.

**FORM:** provenance paragraph under the §S8 heading.

**DERIVATION:** `[RECORD]` of a decorrelated post-acceptance ratification.

**CONDITIONALITY:** **“16 CHECKED-CLEAN lines” is a positive result worth carrying**: the same run checked and passed the floor/band/x-free core, the certificate scoping and the count-law (`.60` says so explicitly). The two GAPs are both on (iv)-adjacent sentences, not on the criterion.

**RESOLUTION TRACE:** lines 883–892.

**TEETH:** **the raw log is verified present with md5 `32751d5d…` AND its stated byte count: `wc -c` = 6,297 B exactly** ✓ — a size pin, rare in the corpus and here exact. `CODEX_TOWERRAT2_2026-08-10.md` exists ✓.

---

### EFF.GENTOW3.58  [changes-record]  *(CHAIN-PERSIST — TERMINAL)*

**CANONICAL STATEMENT:** §S8.1, `[ASSEMBLED]` from lines 898–939. The withdrawal, verbatim:

> “**Superseded inference (quoted).** "both reads shift by the SAME
> g-digits (linearity of both divisions in f), so the divergence at
> THETA_j persists" — WITHDRAWN as an inference: linearity gives
> (Sh - C)(f0 + g) = (Sh - C)(f0) + (Sh - C)(g), not Sh(g) = C(g),
> and honest depth of g does not make the two shifts identical (the
> committed FR-M3 W member: honest C_0 = 0 while ShC_0 = 32 with first
> discrepancy exactly THETA_0 = 10 …).”

The corrected three-step derivation, verbatim:

> “(1) the level-1 development of g carries the same floor …;
> (2) Step 1's ledger is LINEAR in F and weight-monotone (its own
>     sentences): from g-terms at wt >= mu2*E2 + 1, every term of
>     Ghat_j(g) sits at wt >= (mu2 - j)E2 + 1;
> (3) Step 2's branch pricing adds k*delta with k >= 1 on every
>     discrepancy branch …: the difference Sh(g) - C(g) at
>     coordinate j is supported at wt >= (mu2 - j)E2 + 1 + delta =
>     THETA_j + 1; … every disagreeing height of g's two reads is >= THETA_j + 1,
>     STRICTLY above the floor.”

and the boundary confirmation, verbatim:

> “Boundary confirmation from the committed instruments: the
> FR-M3 W member's g_W = 2x*Phi2^2 + 8*Phi2 has slot weights 9, 9 <
> 10 = mu2*E2 + 1 — OUTSIDE the box — and its discrepancy lands at
> exactly THETA_0 = 10; the corrected law puts in-budget
> g-discrepancies at >= 11 at j = 0, so the measured row sits exactly
> on the repaired hypothesis boundary, refuting nothing. The
> parenthetical hypothesis "(slots at heights > THETA_j)" is NOT
> consumed by the corrected derivation; the box hypothesis is the
> operative one.”

**FORM:** numbered correction section with a quoted withdrawal and a three-step re-derivation.

**DERIVATION:** the note's own Steps 0–2 re-run on `g` under the GENTOW-1(a) box hypothesis, giving a STRICT `+1` above the floor; linearity then isolates the key power's certificate digit at `Θ_j`.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement of a justification** — the conclusion (persistence) survives; the inference is replaced and the operative hypothesis CHANGES from “slots at heights > Θ_j” to the GENTOW-1(a) box.

**RESOLUTION TRACE:** lines 894–939; the superseded sentence at 295–298.

**TEETH:** **ARITHMETIC AUDIT of the three-step chain, recomputed:** step (2) `wt ≥ mu2E2 + 1` ⟹ `Ĝ_j(g)` at `wt ≥ (mu2−j)E2 + 1` (Step 1's ledger shifts by `(mu2−j)E2` relative to `mu2E2`) ✓; step (3) adds `k·δ ≥ δ` giving `(mu2−j)E2 + 1 + δ = Θ_j + 1` ✓ — **strictly above the floor, exactly as claimed.** **The boundary confirmation also recomputes:** `mu2E2 + 1 = 3·3 + 1 = 10` at FR-M3, and `g_W`'s slot weights are stated as 9, 9 `< 10` ✓ — so the measured member is genuinely outside the box and refutes nothing. **This is the sharpest repair in the entry: a withdrawn inference, a stronger conclusion (`≥ Θ_j + 1`), and a measured boundary case that sits exactly on the new hypothesis edge.**

---

### EFF.GENTOW3.59  [changes-record]  *(CHAIN-NONFUNC, link 2 — SUPERSEDED)*

**CANONICAL STATEMENT:** §S8.2, verbatim:

> “**Superseded sentence (quoted).** "The shadow read at heights >=
> THETA_j is NOT a function of the honest data." Literally read, this
> is FALSE: the full honest composed data — the key together with the
> digit strings C_j of f = Phi2^{mu2} + Sum_j C_j Phi2^j (the Phi2-adic
> development is unique) — determine f, and the stage-shadow division
> is a deterministic function of f; so the shadow IS a function of the
> FULL honest data.”

> “**Corrected sentence (the scope the note's instances prove).** The
> shadow read's content at heights >= THETA_j is not a function of the
> honest read's OUTPUT — the verdict-level data (pins, deciding
> residues, sigma, labels) that the sub-THETA faithful band (ii)
> determines: the committed PE1 triple varies the shadow read at fixed
> honest sigma, and conversely the S8.1 pair construction gives
> members with identical shadow data and different honest reads …
> No committed pair witnesses a stronger truncation scope …, and none is claimed.”

**FORM:** numbered correction section.

**DERIVATION:** a determinacy observation (the Φ₂-adic development is unique) refuting the literal reading, then a re-scoping to the verdict-level output.

**CONDITIONALITY:** **THIS CORRECTION IS ITSELF SUPERSEDED by S8.4** (`.62`), which withdraws the verdict-level tuple scope entirely. SUPERSESSION KIND: **replacement**, then **replacement**. **A consumer citing S8.2's corrected sentence is citing a withdrawn claim** — the TERMINAL is S8.4's σ-only statement.

**RESOLUTION TRACE:** lines 941–961; the superseded original at 215–216; the withdrawal at 1012–1019.

**TEETH:** the two directions it claims are the PE1 triple (`.14`, verified) and the S8.1 pair construction (`.58`) — both committed; but the *scope* they support is exactly what S8.4 re-measures and reduces.

---

### EFF.GENTOW3.60  [instrument-record]

**CANONICAL STATEMENT:**

> “Pre-append state: post-acceptance body md5 203f7c04
> (203f7c04fa8499853509e33524bab77f; 878 lines, 48,738 bytes); this
> section is a PURE APPEND on it … Sealed machine artifacts
> BYTE-FROZEN and untouched this round (the eleven pinned md5s of
> S7.5/S7.6/S7.7 stand; the S8.1 boundary confirmation re-reads the
> committed gentow3_pe3_fresh artifacts, no re-run). Statement
> displays above stay byte-intact; both corrections are dated
> supersessions of two (iv)-adjacent sentences. Grade: ACCEPTED 2/2
> stands, ANNOTATED by RUN B; S8.1/S8.2 discharge the adjudication's
> repair charges in full — the floor/band/x-free core, the
> certificate scoping, and the count-law were CHECKED CLEAN by the
> same run (16 lines) and are untouched.”

**FORM:** bold-headed freeze + append ledger (§S8.3).

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** lines 963–977.

**TEETH:** **VERIFIED, all three quantities: lines 1–878 hash to `203f7c04fa8499853509e33524bab77f` and measure exactly 48,738 bytes** ✓. The “16 CHECKED-CLEAN lines” positive result is recorded here and at `.57`.

---

### EFF.GENTOW3.61  [record]

**CANONICAL STATEMENT:**

> “**Activation note (orchestrator, 2026-08-12).** The E13 search spec
> was implemented twice against the committed readers (tracing, then
> direct call-surface extraction: gentow3_shadow_search.py / _v2.py;
> outputs runs/cert2/E13_search_output.txt +
> runs/cert4/X1_search_output.txt). Both runs returned INCOMPLETE with
> the same diagnosis: NO committed call surface computes the
> verdict-level tuple (pins, deciding residues, σ, labels) or the
> canonical high-shadow slot map — the stronger claim's own terms are
> not committed objects, so the full-output-matched search is not
> implementable against committed semantics (a stronger ground for
> scope reduction than an EMPTY sweep). Under the owner's 2026-08-12
> delegated authority (end-to-end-proof criterion: S8.2 is a side
> observation, not load-bearing for the uniformity theorem), the
> fallback below is activated with "returns EMPTY" read as "is not
> supported by the committed evidence". The correction text is sol's
> E13 delivery, transcribed unaltered:”

**FORM:** bold-headed orchestrator activation note.

**DERIVATION:** `[RECORD]` of a **conditional activation whose trigger condition was not met literally** — the search returned INCOMPLETE, not EMPTY, and the orchestrator reads INCOMPLETE as a *stronger* ground and activates anyway, under a named delegated authority.

**CONDITIONALITY:** **this is the most delicate protocol move in the entry and it is fully disclosed.** S8.4's own heading says it is “activated only after the committed full-output collision search returns EMPTY on its complete roster”; the note then records that the search never returned EMPTY, explains why INCOMPLETE is stronger (the claim's own terms are not committed objects), and cites the authority and the criterion (S8.2 is a side observation, not load-bearing). **A consumer must read S8.4 with this note attached** — the heading alone misstates the activation basis. OPEN-CALL 2.

**RESOLUTION TRACE:** lines 981–996.

**TEETH:** **both search outputs verified present**: `runs/cert2/E13_search_output.txt` ✓ and `runs/cert4/X1_search_output.txt` ✓, as is `runs/cert2/E13_gentow3_output.log` ✓. The two search instruments named (`gentow3_shadow_search.py` / `_v2.py`) are cited without a directory; recorded as a soft pin (OPEN-CALL 3).

---

### EFF.GENTOW3.62  [changes-record]  *(CHAIN-NONFUNC — TERMINAL)*

**CANONICAL STATEMENT:** §S8.4, verbatim:

> “The residual search compared members only within an identical
> committed reader frame and required equality of the ENTIRE
> verdict-level honest output: pins, deciding residues, sigma, and
> labels. It found no pair on the committed roster having that full
> honest-output tuple identical and shadow content different at
> heights >= THETA_j. An EMPTY finite-roster search does not prove
> that no such pair exists on the full tower locus; it shows that
> the committed evidence does not establish the stronger
> full-verdict-output scope.”

> “**S8.2 supersession.** The S8.2 corrected sentence beginning
> "The shadow read's content at heights >= THETA_j is not a
> function of the honest read's OUTPUT" is WITHDRAWN. Its reference
> to the full verdict-level tuple "(pins, deciding residues, sigma,
> labels)" is likewise WITHDRAWN.”

> “**Final corrected claim.** The shadow read's content at heights
> >= THETA_j is not a function of the honest read's sigma.”

> “**Proof from the committed instances.** PE1-0 and PE1-1 have the
> same honest sigma, namely {(8,1)}, while their shadow reads differ:
> PE1-0 has shadow pins (21,14) and label tRAM, whereas PE1-1 has
> shadow pins (28,14) and label tINERT. In particular their shadow
> content differs at coordinate 0 at heights >= THETA_0 = 21.
> Hence equal honest sigma can have different shadow content, so no
> function of honest sigma alone determines that content …”

with the scope fence:

> “This correction changes only S8.2's non-functionality scope.
> S8.1's repaired margin proof, THEOREM GENTOW-3(i)-(iii), the
> certificate-scoped persistence statement, and the accepted
> machine records are untouched.”

**FORM:** numbered correction section (transcribed sol delivery).

**DERIVATION:** a two-instance witness proof from the committed PE1 rows.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (a scope reduction). **TERMINAL of CHAIN-NONFUNC.** The final claim is the weakest of the three and the only one with a committed two-instance proof.

**RESOLUTION TRACE:** lines 998–1035; the closing provenance parenthetical at 1037–1041.

**TEETH:** **THE WITNESS PAIR IS VERIFIED AGAINST `.14`'s RECOMPUTED TABLE.** PE1-0: honest tRAM(25,14), shadow tRAM(21,14), σ {(8,1)}. PE1-1: honest tRAM(21,14), shadow tINERT(28,14), σ (PARI) {(8,1)}. **Same honest σ = {(8,1)} ✓; different shadow pins (21,14) vs (28,14) ✓; different shadow labels tRAM vs tINERT ✓; and both shadow divergences at coordinate 0 sit at heights ≥ Θ_0 = 21 ✓** (21 and 28 respectively). The proof reproduces exactly from the note's own S1 divergence table. The provenance parenthetical records the same re-check: “the PE1-0/PE1-1 witness pair re-checked against the committed records” — and “Ledger: row 9 → folded, awaiting discharge-confirm (cert5)”, an outstanding item (OPEN-CALL 5).

---

## 3. XREF verification ledger

### 3.1 Designation XREFs

`[TABLE — compiler ledger]`

| ID | Target | Check | count | Role |
|---|---|---|---:|---|
| X01 | `GENHN_PROOF_2026-08-08.md` | `GENHN-TOW-1` | **19** | the box; item (3) is this note's charge |
| X02 | `GENTOW6_PROOF_2026-08-09.md` | exists; named by the r2 consumer walk as “the one downstream consumer of (iv)-adjacent content” | — | consumer-walk target (`.52`) |
| X03 | `docs/PROJECT_STATE.md` | append #12 / #13, named by the consumer walk | — | consumer-walk target |
| X04 | `CODEX_TOWERRAT2_2026-08-10.md` | exists | — | RUN B's record (`.57`) |
| X05 | `GENTOW1_PROOF_2026-08-09.md` | exists; supplies LEMMA GENTOW-1/5 and the imported families | — | the note's principal proof-side import |

### 3.2 Commit and artifact pins (v3 rule 23) — **thirteen artifact md5s, all matched**

`[TABLE — compiler ledger]`

| ID | Pin | Verified |
|---|---|---|
| P-01 | commits `3101cf5`, `c048154`, `a1c181d`, `b6a43963`, `0633c6a3`, `d90db6d`, `5ac0d80`, `e1a8dfe`, `0d09d65`, `8165208`, `d6b409ce`, `16a729bd`, `2c8bb507`, `59c1966` | **ALL FOURTEEN resolve** |
| P-02 | `gentow3_checks.py` `7cf3a7b8…` | MATCHES |
| P-03 | `gentow3_checks_output.txt` `926cd05f…` | MATCHES; `GREEN -- 582 checks, 0 violations` |
| P-04 | `gentow3_pe1_fresh.py` `35ad32aa…` | MATCHES |
| P-05 | `gentow3_pe1_fresh_output.txt` `94160b22…` | MATCHES |
| P-06 | `gentow3_pe1_fresh_output_run1_RED.txt` `485946fc…` | MATCHES (the RED run is KEPT, not deleted) |
| P-07 | `gentow1_checks.py` `6df4b213…` | MATCHES — **and is the same hash GENTOW1's own S5 pins** |
| P-08 | `gentow3_pe2_fresh.py` `55208baf…`, output `06b4bddf…`, run-1 RED `3ca64bd4…` | ALL THREE MATCH |
| P-09 | `gentow3_pe3_fresh.py` `bde31247…`, output `3ce4128a…` | BOTH MATCH; `GREEN -- 451 checks, 0 violations, teeth 3/3` |
| P-10 | `gentow3_pe5_fresh.py` `9acab757…`, output `fc4f8d55…` | BOTH MATCH; `GREEN -- 287 checks, 0 violations` |
| P-11 | `towerrat2_runB_gentow3_output.txt` `32751d5d…`, **6,297 B** | MATCHES md5 **and byte count** |
| P-12 | the three text freezes | **ALL VERIFIED** (§1) |
| P-13 | `gentow3_checks.py` L398–399 dead code | **VERBATIM MATCH at the stated lines** |
| P-14 | `runs/cert2/E13_search_output.txt`, `runs/cert4/X1_search_output.txt`, `runs/cert2/E13_gentow3_output.log` | ALL THREE EXIST |
| P-15 | `gentow3_shadow_search.py` / `_v2.py` | cited without a directory; **not located** — soft pin, OPEN-CALL 3 |

### 3.3 Verified NEGATIVE edges

| ID | Check | count | Meaning |
|---|---|---:|---|
| N1 | `grep -cF 'GENTOW' GENHN_PROOF_2026-08-08.md` | **0** | the item-(3) discharge AND the (iv)-sentence upgrade are both UNLANDED (`.42`) |

---

## 4. Effective supply / consumption ledger

| Obligation | Effective supply | Surviving fence | Protocol status |
|---|---|---|---|
| [GENHN-TOW-1] item (3): the faithfulness geography | `.18`–`.21` (THEOREM, four clauses) | (i)–(iii) general; **(iv) certificate-conditional** (`.39`); geography one-sided (`.10`) | **DELIVERED, ACCEPTED 2/2, ANNOTATED**; discharge UNLANDED (N1) |
| item (3)'s parenthetical: T(a) event-band survival as a theorem | `.29` (COR GENTOW-3.C) | unconditional at every genre | **DISCHARGED**; the supplier-sentence upgrade UNLANDED (N1) |
| the leaf-depth failure quantified | `.30`–`.33` (three regimes) | δ = 1 band empty; count-law one-sided | **DONE**, with measured instances AND non-instances |
| the corrected `chat_t` | `.15`, `.44` | value-live only at the x-free classification here | **IMPORTED** from GENHN's erratum |
| items (4), (6)(α) | not supplied | `.38` | **OPEN**; item (4) = GENTOW-4's territory |

---

## 5. NON-IMPORTS

**NI-1 — no supplier file is edited.** `.07`, `.42`; verified (N1).
**NI-2 — the certificate is NOT proved genre-generally.** `.39`: “a genre-general non-vanishing proof … [is] NOT delivered”.
**NI-3 — no witness battery for entry-digit-driven overflows.** `.28`(2), `.39`.
**NI-4 — the geography is ONE-SIDED.** `.10`: no only-if is claimed; “other members can still fail at exactly THETA_j”.
**NI-5 — reaching Θ_j is NECESSARY, not sufficient.** `.33`.
**NI-6 — the σ-comparison is NOT executed in code.** `.37`, `.50`: dead code; the difference is entailed, not compared.
**NI-7 — the ENTRY tally is NOT independent evidence.** `.50`.
**NI-8 — the deep-perturbation parenthetical is NOT the operative hypothesis.** `.58`: “The parenthetical hypothesis "(slots at heights > THETA_j)" is NOT consumed by the corrected derivation”.
**NI-9 — no stronger non-functionality scope is claimed.** `.59`, `.62`: the final claim is σ-only; “No non-functionality claim for the larger tuple … is retained.”

Accordingly **no edge is created** from this note to a genre-general certificate law, to a biconditional mislabeling law, to an in-code σ comparison, or to any non-functionality claim beyond honest σ.

---

## 6. TEETH inverse inventory

### 6.1 Obligation → guarded units

| # | Row | Guarded units | Disposition |
|---:|---|---|---|
| 1 | P-1 FLOOR 274 (137 member_checks) | `.18` | executable regression; census corrected conservatively (`.49`) |
| 2 | P-2 SHARP 11 (self-shadow pins at Θ) | `.21`, `.27`, `.12` | executable regression — **the (iv) certificate's sealed leg** |
| 3 | P-3 XFREE 3 + 12-member sweep | `.20`, `.17` | executable regression |
| 4 | P-4 ENTRY 274 | `.29` | **disclosed non-independent** (entailed by FLOOR given δ ≥ 1) |
| 5 | P-5 BAND 2 | `.19`, `.31` | executable regression — the faithful-leaf-band witnesses |
| 6 | P-6 LABEL 6 | `.19` | executable regression |
| 7 | P-7 PE1 3 + GP-SIG 6 | `.14`, `.33`, `.62` | executable regression — **and the witness pair for the terminal σ-claim** |
| 8 | T-THRESH-UP ×4 | `.18`, `.21` | **anti-vacuity: pins Θ from above** |
| 9 | T-BAND-EDGE ×1 | `.19`, `.31` | **anti-vacuity: pins Θ from below** |
| 10 | T-SHADOW-REG ×1 | `.37`, `.50` | **disclosed non-repair** — σ-leg is dead code |
| 11 | the PE1 fresh route (FR-GL, 485/0, η ≠ 1) | `.47` | **AUDIT / decorrelated frame** — the note's only η ≠ 1 contact |
| 12 | the PE2 fresh route (149/0, the count-law counter-member) | `.52` | **AUDIT / decorrelated frame** — refutes a composed biconditional |
| 13 | the PE3 fresh route (451/0, teeth incl. `T3-BICOND`) | `.53`, `.10` | **AUDIT / decorrelated frame** — refutes r2's over-correction |
| 14 | the PE5 fresh route (287/0, FR5X at δ = 9) | `.55` | **AUDIT / decorrelated frame** — the third certificate configuration |
| 15 | RUN B (2 GAPs, 16 CHECKED-CLEAN) | `.57`–`.60` | **AUDIT / decorrelated-model audit** |
| 16 | the E13 search (twice implemented, INCOMPLETE) | `.61`, `.62` | **instrument-record: NOT IMPLEMENTABLE against committed semantics** |
| 17 | GENTOW3-BOX-1 | `.39`, `.55` | **PROOF-ONLY, OPEN** — three configurations measured |
| 18 | GENTOW3-BOX-2 | `.40` | **signed coverage disclosure**, two-axis |

**Zero-orphan check: 18 obligations, all mapped, 0 orphans.**

### 6.2 Arithmetic audit summary (v3 rule 22)

- **582** = 274+274+11+6+3+2+3+6+3 ✓, all nine categories matching the artifact ✓
- **287** = 4+3+120+120+6+11+11+2+3+7 ✓ (FR5X)
- **all five δ** and **all ten Θ** of the S1 table, recomputed from `.09`'s formulas ✓
- **all five entry tops** `mu2·E2` ✓; the faithful-band width `δ−1` at FAM-A7 = [29,30] ✓
- **the census**: `5×27+2 = 137`, `×2 = 274` ✓; the erroneous `50+60 = 110` ✓; the gap `27` = 20+5+2 ✓
- **FR-M3**: `E2 = 3`, `δ = 1`, `Θ = [10,7,4]` ✓
- **FR-GL**: `E2 = 6`, `δ = 1`, `Θ = (13,7)`, both slot-height routes ✓, the gauge factor 54→108 ✓
- **FR5X**: from `δ = 9` alone, `u2 = 13`, `E2 = 26`, `Θ(μ₂=3) = [87,61,35]`, `Θ_0(μ₂=2) = 61` ✓
- **the four digit replications** `[−32,0,16]`, `[−128,0,64]`, `[−128,64,64]`, `[−8,8,4]` ✓
- **Step 2's recarry bound** and **Step 1's `mu1u2 = mu2E2`** ✓
- **S8.1's `Θ_j + 1`** and the `g_W` boundary `9 < 10` ✓
- **S8.4's witness pair** (same honest σ, different shadow pins/labels, both ≥ Θ_0) ✓
- **three text freezes**: 815 lines; 878 lines/48,738 bytes; the `d90db6d` blob md5 ✓
- **thirteen artifact md5s** + one byte count (6,297 B) ✓

**Zero arithmetic discrepancies found.**

---

## 7. BOUNDARY SELF-AUDIT

### 7.1 The rule applied

Zero `\tag{`; smallest cuttable span. Theorem CLAUSES are units (clause (iv) alone carries three separate supersessions); numbered repair SECTIONS are units; the three S4 regimes are units (each is cited separately downstream).

### 7.2 Boundaries drawn, arguable ones both ways

1. **THEOREM GENTOW-3 → four clause units + six proof units.** *Chosen* because (i)/(ii) are unconditional and gauge-immune, (iii) is definition-scoped, and (iv) carries three supersessions. No single unit could state that.
2. **The four ARC records → four units (`.02`–`.05`).** *Chosen* because the arc's value is its shape — GAP → over-correction → one-siding → clean — and per-entry emission is the only way a merge run sees it.
3. **S8.2 emitted despite being superseded (`.59`).** *Arguable*: one could emit only S8.4. *Chosen* because S8.4 supersedes S8.2 by NAME and quotes it; without `.59` the terminal correction has no antecedent, and a reader could not tell that the verdict-level tuple was ever in play.
4. **`.61` (the activation note) split from `.62` (S8.4).** *Chosen* because the activation note is the ORCHESTRATOR's and S8.4 is sol's transcribed delivery — different authors, and the activation's disclosure that the trigger condition was not literally met is the load-bearing part.
5. **The three certificate configurations → one unit (`.55`) with a declared SERIES.** *Arguable*: three units. *Chosen* because the note assembles them as one data point for one open box, and their value is comparative.
6. **`.47` (FR-GL) kept separate from `.44`/`.45`.** *Chosen* because it is a run-record adopted from another instrument, not part of the annex's derivation.
7. **`.50` kept separate from `.37`** though both concern the dead σ-leg: `.37` is the tooth's own row (a run-record), `.50` is the numbered disclosure section (a changes-record) and carries the second, unrelated non-independence disclosure.

### 7.3 Merges deliberately NOT made

- `.30`/`.31`/`.32` (the three regimes) kept apart: each is cited separately, and only `.30` carries a dated correction.
- `.10` (geography) not merged into `.09` (the constants): the geography carries a two-layer supersession the constants do not.
- `.58`/`.59` kept apart: two different GAPs from one run, with different fates.

### 7.4 Rules that fought this genre

- **Rule 25 (CHAIN) is indispensable here and CHAIN-NONFUNC is the queue's only THREE-layer chain where the middle layer is itself a correction.** A flat “superseded by” field would leave a consumer citing a withdrawn scope.
- **Rule 22 paid heavily**: every constant in five families and four fresh frames recomputes from two formulas, which independently validates the S1 tables and all four fresh-route records.
- **Rule 23**: thirteen artifact md5s, one byte count, three text freezes, fourteen commits — the densest pin set in the queue after GENTOW1, and complete.
- **Rule 19's split** mattered at `.61`: an *instrument* that is **not implementable** is neither a preregistration nor a run-record, and only the three-way split makes that statable.

---

## 8. Deferred reconciliation obligations

1. **The item-(3) discharge and the (iv)-sentence upgrade are both unlanded on GENHN — FOR-0c.** Precondition (2/2) met; N1 verified. Two distinct obligations in one sentence.
2. **The conditionality stack cites GENTOW-1 at 0/2 — FOR-0b.** Stale in the favorable direction; GENTOW1 is ACCEPTED 2/2 at HEAD.
3. **Ledger row 9 awaits discharge-confirm (cert5) — FOR-0c.** S8.4's closing parenthetical: “Ledger: row 9 → folded, awaiting discharge-confirm (cert5).”
4. **The two E13 search instruments are cited without a path — FOR-0b.** `gentow3_shadow_search.py` / `_v2.py` were not located; their outputs exist.

---

## 9. Self-audit and OPEN-CALLS

### 9.1 Resolved compilation calls

- The effective-text rule distinguishes r1–r3's in-body insertions from the three post-freeze supersessions, and identifies the ONE statement-internal edit (r2's “touched” pin) that the note itself flags.
- **Seven CHAINs reconstructed with TERMINALs**, including the queue's only documented over-correction (CHAIN-GEOG) and its only doubly-superseded sentence (CHAIN-NONFUNC).
- **All thirteen artifact md5s, one byte count, three text freezes and fourteen commits verified; the dead-code lines verified verbatim at their stated line numbers.**
- **Every constant in five families and four fresh frames recomputed from the note's own two formulas; zero discrepancies.**
- The note's own disclosures of non-independence (ENTRY entailed by FLOOR; the dead σ-leg) are carried as dispositions rather than absorbed into the evidence count.
- The r2 repair's four-part structure (re-derivation / refuting instances / non-vacuity check / consumer walk) is recorded as the queue's most complete repair protocol.

### 9.2 OPEN-CALLS

**OPEN-CALL 1 — the S0 geography is one-sided; is that the charge's “EXACTLY”? FOR-0b.**
The CHARGE asks to “characterize EXACTLY when the stage-shadow read … agrees”. What is delivered after r3 is a one-sided law: below Θ_j faithful (proved, general); at Θ_j, failure at certificate-carrying coordinates (proved) and possible failure elsewhere (measured, not characterized). **Whether item (3)'s box counts as discharged by a one-sided law is a note-owner/ledger judgment** — the note claims delivery, and the r2 consumer walk found no consumer relying on more, but the charge's own word is “EXACTLY”.

**OPEN-CALL 2 — S8.4's activation condition was not literally met. FOR-0c/0d — NEEDS ASVIN.**
The section heading reads “activated only after the committed full-output collision search returns EMPTY on its complete roster”. The search returned **INCOMPLETE**, twice, because the claim's own terms are not committed objects. The orchestrator's activation note (`.61`) discloses this fully, argues INCOMPLETE is a *stronger* ground, and cites delegated authority plus the end-to-end-proof criterion. **The disclosure is exemplary; the protocol question — may a conditional append be activated on a stronger-but-different condition, with the heading left stating the original one? — is not a compiler decision.** A one-line heading amendment would remove the mismatch.

**OPEN-CALL 3 — two search instruments are unlocated. FOR-0b.**
`gentow3_shadow_search.py` and `_v2.py` are named without a directory and were not found. Their outputs exist and are pinned. Committing the instruments (or citing their path) would close it.

**OPEN-CALL 4 — the conditionality stack's GENTOW-1 grade is stale. FOR-0b.** See §8 item 2. Favorable direction; no consumer is wrong.

**OPEN-CALL 5 — ledger row 9 awaits discharge-confirm. FOR-0c.** S8.4 is folded but its discharge-confirm (cert5) is outstanding per the note's own closing line.

### 9.3 Fidelity audit

- Every CANONICAL STATEMENT is verbatim, or `[ASSEMBLED]` (eight units: `.24`, `.27`, `.36`, `.47`, `.52`, `.53`, `.58`, and the S8 provenance), with `…` at every truncation.
- ASCII/Unicode mixing preserved as the source has it (`THETA_j` in S0/S2, `Θ_j` in the S1 table and S8) — both quoted as written.
- Four source tables emitted as tables; the two fixed-width ASCII blocks (divergence table, verdict block) double-emitted per v3 rule 14.
- No quantifier, threshold, pin, label or σ tuple altered. Compiler-computed values appear only in TEETH fields, marked recomputed.
- 5 designation XREFs, 15 pin classes, 1 negative edge verified; **no designation invented**.

EFF-GENTOW3 COMPILED: 62 statements / 5 xrefs verified / 5 open calls
