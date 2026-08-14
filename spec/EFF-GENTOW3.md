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
