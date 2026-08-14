# EFF-HE6R1 — CANONICAL EFFECTIVE SPECIFICATION v2/v3

## 1. Header

**Source note:** `lean/notes/openmath/HE6R1_RECON_2026-08-08.md` (1,071 lines / 70,605 bytes).

**HEAD blob hash:** `a684c4e541626994f9448e6a8a7472b2fe82fed8`. Whole-file md5 at compile time: `9c4069f9d1babe77a55a77a6952a3ea8`.

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a, Opus wave 4, queue 8b (Asvin-authorized substitution, `docs/PROJECT_STATE.md` #51).

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD — rules 1–28. Full compilation, unsharded (70 KB).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED** (post-reset).

### Queue-specific charge: HE6R1-1 / -2 / -3 and the HE7 errata

The three composition lemmas the box-widening surfaced, and the two errata they force on HE7, are compiled as their own units with their landing status verified at the target:

`[TABLE]`

| object | EFF unit | kind | landing status at HE7 |
|---|---|---|---|
| `LEMMA HE6R1-1` (the widened jump condition, with HE7.C's bounds) | `.09` | lemma, PROVED | — (it *replaces* HE7.C's jump condition) |
| `LEMMA HE6R1-2` (block projection) | `.13` | lemma, PROVED | — (it *supplies* what HE7-BOX-4 declined) |
| `LEMMA HE6R1-3` (the level-2 peel) | `.15` | lemma, PROVED, **machine-discovered** | — (it *repairs* HE7's missing hypothesis) |
| **erratum 1: `FINDING HE6R1-F1`** (HE7.A(3)'s trichotomy + HE7.C's jump condition too narrow) | `.08` | supplier-finding | **LANDED** — `grep -cF 'HE6R1-F1' HE7_PROOF_2026-08-08.md` = **4** |
| **erratum 2: `FINDING HE6R1-F2`** (HE7.A / COROLLARY HE7-7″ require `Ψ ∤ f_S`) | `.14` | supplier-finding | **LANDED** — `grep -cF 'HE6R1-F2' HE7_PROOF_2026-08-08.md` = **8** |

**Both errata are landed at HE7 and verified by fixed-string grep at the target.** All three lemmas are stated as PROVED in this note and each carries its proof inline (`.09`/`.10`, `.13`, `.15`/`.16`). **`LEMMA HE6R1-1`'s displayed global bound was later found defective and RE-DISPLAYED** under the owner's end-to-end-proof directive — the single most important supersession in this note, compiled at `.43` and `.47`.

### Effective-text rule

The note's freeze is declared at the acceptance record (L797–799):

> “**HE6R1 is ACCEPTED (2/2) and FROZEN — the body and annex above are
> not edited; dated appends only.**”

with each append re-declaring it: the micro-annex at L719–720 (“Append-only: the pre-append file md5 b43b798f229f5f68f35c41b37a072099 is the prefix”), the acceptance record at L801–803 (“the pre-append file md5 2c44fd2efd89295d33c36def3af84347 is the prefix”), and the A4 fold at L875 (“Everything above this heading is byte-untouched by this append”).

**Therefore the effective text is: the body L1–706 read with its inline `[r1′]` bracket repairs applied in place, then four dated append blocks in date order — the 2026-08-09 post-PE2 micro-annex (four MINOR riders), the 2026-08-09 post-PE3 acceptance record (three MINOR riders), the 2026-08-12 sol-A4 fold (two obstruction records + two challenge corrections + a provenance note), and the 2026-08-12 owner-directive statement re-display.** No body text is edited by any append.

### FREEZE PREDICATES (rule 21 — three independent freezes)

**FREEZE-1 — two prefix pins, both verified and both localized.** `b43b798f229f5f68f35c41b37a072099` = md5 of the first **706** lines (unique hit over all line boundaries) ✓; `2c44fd2efd89295d33c36def3af84347` = md5 of the first **786** lines (unique hit) ✓. **Two nested prefix pins, both exact** — the strongest freeze-chain evidence in queue 8b, since the second pin certifies that the first append was itself untouched by the second.

**FREEZE-2 — instrument freeze with FOUR imported pins.** §S6 L586–589 records the import pins the runner consumes: `he6_checks.py 321fa4d4990e…`, `he7_checks.py 688adbe88447…`, `w12_checks.py 7dc040d94fbb…`, `w10_checks.py a9c34244a3af…`. **ALL FOUR VERIFIED EXACTLY** at compile time. The sealed runner is at commit **`4f5ebaa`** ✓ with “one disclosed post-seal print-only `[r1-fix]`”.

**FREEZE-3 — hostile-report anchors.** `HE6R1_passPE2_report.md` @ `2118e59` ✓, `HE6R1_passPE3_report.md` @ `9aa0cc6` ✓, `HE6R1_passPE1_report.md` — all three EXIST; the commits verify. *(Unlike HE6, this note pins its reports by commit rather than by md5 — recorded as a weaker pin form, not a defect.)*

### Supersession chains inside the note

`[TABLE]`

| # | Target (frozen text) | Layer 1 (`[r1′]`) | Layer 2 (micro-annex, 08-09) | Layer 3 (acceptance, 08-09) | Layer 4 (A4 / re-display, 08-12) | TERMINAL |
|---|---|---|---|---|---|---|
| C-1 | **`LEMMA HE6R1-1`'s global bound “J ≤ log₂ μ − 1 ≤ log₂ n − 2”** | — | — | — | **A4 finding 1: REAL but OBSTRUCTED** (`.43`) → **owner-directive RE-DISPLAY into three clauses (a)/(b)/(c)** (`.47`) | **the three-clause re-display** |
| C-2 | The completion statement's qualification (ii) vs GENHN-ERR-1 | — | — | — | **A4 finding 2: REAL but OBSTRUCTED** (`.44`) → **routed to a scheduled proof unit** (`.48`) | **the routing** — and **the unit LANDED** (§5.2) |
| C-3 | §S6's “✓ with one honest qualification” on P1 | **`[r1′]` retires it: “a preregistered prediction that fails on a stratum is a failed prediction”** | — | — | — | **`[r1′]`** (`.24`) |
| C-4 | §S6's “46 strict-excess … certificates” | **`[r1′]` PE1 F-4: split into 42 + 4 recovered + 4 infinite** | — | — | — | **`[r1′]`** (`.23`, `.28`) |
| C-5 | `LEMMA HE6R1-2`'s scalar identification | `[r1′]` names it `γ_g` | **PE2 F-2: gains the cocycle unit `β^{c₁}`** | **PE3 F-1: the exponent's argument is the PIN height `m₁`, not the side's line value** | — | **PE3 F-1** (`.39`) |
| C-6 | HE6R1-BOX-1's cross-grades | — | **PE2 F-3 re-dates all six** | — | — | **PE2 F-3** (`.36`), itself an as-of record |
| C-7 | The completion statement's “except HE3 at 1/2 for μ ≤ 3” | — | — | **PE3 F-2: corrected to HE3 at 0/2 (r2 owed)** — “the one stale-grade site whose direction is NOT conservative” | — | **PE3 F-2** (`.40`) |
| C-8 | The R4 row's “equality exactly at i = e₁t” | — | — | — | **A4 finding 3: “equality can occur only at”** (`.45`) | **A4 f3** |
| C-9 | §S6's “(LIFT₂)'s threshold is **exactly** the closed form at d_r ≥ 2” | — | — | — | **A4 finding 4: sufficient, not sharp — non-sharp by one** (`.46`) | **A4 f4** |
| C-10 | The R3 row's bare “PE2 F-n” references | — | — | **PE3 F-3: file-qualified to `HE6_passPE2_report.md`** | — | **PE3 F-3** (`.41`) |
| C-11 | This note's own grade (0/2) | `[r1′]` 0/2 | 1/2 (PE2 CLEAN) | **ACCEPTED 2/2** | ledger **CERTIFIED** | **ACCEPTANCE + the ledger** |

**Two OBSTRUCTED findings — a disposition unique to this note in queue 8b.** A4 records that findings 1 and 2 are **REAL but admit no honest repair** (“every honest repair weakens an accepted statement display, so no admissible repair exists”). Both were later closed by *authority* rather than by a dated correction: finding 1 by the owner's end-to-end-proof directive (a re-display), finding 2 by scheduling a proof unit. **Recorded as its own supersession genre** — see `.42`–`.44`, `.47`, `.48`.

### Scope of record — three-predicate split (rules 7 and 17)

#### A. Mathematical absorption/supply set

The note's own delivery paragraph (§S0 L44–58) frames it as answering one question — “Does HE7 … cover the WIDENED box?” — with “**Answer: YES, and the ℓ = 1 branch is a literal instance**”. The supply set is **three new lemmas (HE6R1-1, HE6R1-2, HE6R1-3), two findings against HE7 (F1, F2), one erratum against GENHN (R9), the reworded COROLLARY HE6.B, and a machine leg on the previously unexercised `d_r ≥ 2` branch**. The number of *obligations discharged* is **one and a half**: HE6-BOX-1's ℓ = 1 branch in full (§S3), and HE7-BOX-4 “superseded in read form” by HE6R1-2(b)+(c).

#### B. Consumption / append-protocol scope — three outbound landings, all verified

1. **To HE7 — both errata LANDED.** `HE6R1-F1` count **4**, `HE6R1-F2` count **8** in `HE7_PROOF_2026-08-08.md` ✓. PE2 F-3 records HE7 as “ACCEPTED 2/2 with its annex stack accepted, FULLY FROZEN (FINDING HE6R1-F1 applied — HE7 micro-annex ca3754d)” — and `ca3754d` is a commit ✓.
2. **To GENHN — the R9 erratum LANDED** as “a dated `[r1]` ERRATUM annex”; `grep -cF 'ERRATUM' GENHN_PROOF_2026-08-08.md` = **17** ✓.
3. **To HE7 again — two HE7-side dated lines cured this note's PE2 F-1 and PE3 F-1 echoes**: commits `263cef0` (“HE7 dated line (S5.5 scalar clause)”) ✓ and `db0001a` (“fold-box as-of scoping”) ✓.

#### C. Inbound corrections RECEIVED (rule 17)

Four: Codex PE1 on **HE6** (nine findings, whose F1 and F4 are this note's occasion); this note's own PE1 (`[r1′]`, 0C+2G+5M); PE2 (4 MINOR) and PE3 (3 MINOR); and the sol A4 adjudication (4 findings: 2 REAL-with-repair, 2 REAL-but-OBSTRUCTED).

### Resolution rules applied

1. `[r1′]` is **this note's own** repair tag; a bare `[r1]`/`[r2]` resolves per the PE2 F-4 convention (`.37`), and cross-note tags carry an explicit qualifier. **The note supplies its own tag-resolution rule, and this compilation applies it.**
2. Appends apply in date order; the A4 fold lands on body spans, the re-display lands on an A4 obstruction record.
3. **An OBSTRUCTED finding is not a superseded span.** A4 findings 1 and 2 record that the defect *stands*; the effective text therefore carries the defect until the re-display (`.47`) or the scheduled unit (`.48`) closes it. Compiled as such.
4. The frozen grade vocabulary is superseded by the acceptance record and the SOL ledger; PE2 F-3 and PE3 F-2 are themselves as-of re-datings and are flagged.
5. Out-of-note material (HE6, HE7, GENHN, HE3, the ledgers) is used only to resolve and verify.

### Quotation and prosification discipline

Every CANONICAL STATEMENT is a verbatim quotation or explicitly `[ASSEMBLED]`. The note's **two fixed-width ASCII tables** (§S6's σ census, §S6's LIFT₂ frame table) are each emitted **twice** — verbatim and as a `[TABLE]` transcription — per **rule 14**. The §S1 repair record is a Markdown table and is transcribed as one. LaTeX displays in the A4 blocks are reproduced as written. Terminal punctuation and `∎` marks preserved.

---

## 2. NON-IMPORTS

**N-1 — no adaptation of HE7 is claimed for the ℓ = 1 branch.** §S0: “no hypothesis of (SLOT₂), (LIFT₂), the disk criterion, the two evaluation displays, the block factor, the slope counts, nonemptiness, Galois equivariance or the class-size theorem mentions ℓ except through `gcd(u, ℓ) = 1` (automatic at ℓ = 1) and through the derived objects dv₂, T₂, n₂, which degenerate benignly”. **The literal-instance claim is the note's central non-import**: nothing new is built for ℓ = 1.

**N-2 — the level-2 twist is absent at ℓ = 1.** Tooth HE6R1-T-TWIST0: “1,276 level-2 twist exponents computed, all zero — the level-2 normalizer cocycle degenerates at ℓ = 1 (n₂(k) = ϖ^k), so HE6's twist-free convention IS available here, **in contrast to HE7's HE7-T-BADTWIST** where dropping the twist mispredicts σ on 21 reads.”

**N-3 — GENHN's `f₁ ≥ 2` count-side displays are NOT settled here.** `GENHN-ERR-1` (`.20`): “Whether GENHN's f₁ ≥ 2 count-side displays that substitute S = e₁h for the node height need re-reading with D′h = f₁S is NOT settled here”. **This is the note's one admitted open mathematical residue**, and it is exactly what A4 finding 2 turns on (`.44`).

**N-4 — proper blocks are proof-only.** HE6R1-BOX-2: “NOT exercised: f₁ ≥ 2 stage genres, d_r ≥ 3, μ ≥ 5 (hence proper blocks — **LEMMA HE6R1-2's own configuration is proof-only**), level 3 (unreachable below n = 16).”

**N-5 — no char-p oracle.** HE6R1-BOX-3, inherited from HE6-BOX-4.

**N-6 — the R9 consumption check is negative by design.** §S1 R9: “HE6/HE7 consume GENHN-**2** (the SLOT LEMMA) and HE3-0's locus, **never GENHN-1's node display**, so nothing downstream propagates”.

---

## 3. Statement inventory

IDs `EFF.HE6R1.01`–`.48`.

### EFF.HE6R1.01  [record]

**CANONICAL STATEMENT** — the title line (verbatim, L1), which is this note's abstract. FORM: title.

> “# HE6 r1 + THE RECONCILIATION — the repair round on HE6 (R1–R9 applied), COROLLARY HE6.B REWORDED to the WIDENED box, and the decisive check: **HE7's machinery covers the widened box's other branch (ℓ = 1, repeated irreducible residual of degree ≥ 2) as a LITERAL INSTANCE** — plus the THREE composition lemmas the widening surfaced (HE6R1-1 the widened jump condition with HE7.C's own bounds; HE6R1-2 block projection; HE6R1-3 the level-2 peel — all PROVED) and the TWO errata they force on HE7 (HE7.A(3)/HE7.C's jump condition; the missing hypothesis Ψ ∤ f_S, found BY the new battery) — machine leg GREEN on the decisions: 677/682 PARI agreements with ZERO mis-decisions, three σ per row of identical outer data (the widening is non-vacuous AND decided), the first d_r ≥ 2 (LIFT₂) leg this program has run”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** “machine leg **GREEN** on the decisions” is precise and must be read with `.24`: the headline prediction P1 **FAILED as preregistered** on 12 of 944 members; what is green is the *decisions* (677/682 agreements, **zero mis-decisions**). The title's own phrasing is careful; a consumer paraphrasing it as “machine leg GREEN” would over-claim.

**Arithmetic audit.** `677/682` and “zero mis-decisions” are reconstructed exactly from the σ census at `.25`.

**XREF.** `HE7_PROOF_2026-08-08.md` — `THEOREM HE7.A`, count 32; `THEOREM HE7.C`, count 9.

---

### EFF.HE6R1.02  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S0 L29–58). FORM: paragraph with an embedded blockquoted question.

> “Codex's hostile pass PE1 on HE6 returned 9 findings; 8 upheld as classified
> and 1 regraded (finding 3, blame moved upstream to GENHN). Two of them are
> structural rather than local: **F1** (COROLLARY HE6.B's excluded set is not
> the complement of the separable-residual hypothesis — an ℓ = 1 side carrying
> a repeated IRREDUCIBLE residual factor of degree ≥ 2 falls in the crack) and
> **F4** (HE6 §S1's (LIFT) is false as stated), the latter CONVERGENT with
> HE7's own FINDING HE7-F1, found independently one day later by a different
> route. This note applies all nine repairs, rewords HE6.B to the widened box
> F1 forces, and then answers the question the widening raises:
>
> > **Does HE7 — written against the OLD box (ℓ ≥ 2, repeated residual) —
> > cover the WIDENED box (any ℓ, repeated irreducible residual factor with
> > ℓ·deg r ≥ 2)?**
>
> **Answer: YES, and the ℓ = 1 branch is a literal instance** …”

**DERIVATION.** [RECORD of the charge and the answer].

**CONDITIONALITY.** The convergence note on F4 — “CONVERGENT with HE7's own FINDING HE7-F1, found independently one day later by a different route” — is corroborated at `spec/EFF-HE6.md` `.12`, where **both counter-instances were re-derived and both check against the replacement's own `T(k)` formula**. Two independent discoveries of one defect.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE6`, count 209. `CODEX_HE6PE1_2026-08-08.md` — EXISTS ✓.

---

### EFF.HE6R1.03  [table]

**CANONICAL STATEMENT** — the §S1 r1 repair record, a Markdown table of nine rows R1–R9 (L61–86). FORM: table. *(The table's cells are long; R9 is emitted separately at `.04` because it is the one row that lands on another note. The remaining eight rows are the HE6-side repairs already compiled at `spec/EFF-HE6.md` `.02`, `.12`, `.19`, `.22` and elsewhere; this unit records the record's existence, its shape and its cross-note routing.)*

**DERIVATION.** [RECORD] — the repair index for HE6's `[r1]` round, authored **in this note** rather than in HE6.

**CONDITIONALITY.** **A structural fact the DAG needs:** HE6's `[r1]` round is *tagged in HE6* but *recorded here*. `spec/EFF-HE6.md` `.02` quotes HE6's own pointer — “with the full record, the widened-box reconciliation against HE7 and a new machine leg in `HE6R1_RECON_2026-08-08.md`”. **So a chapter cut of HE6 alone has the repairs but not their record.**

**Corrected reference convention.** The R3 row's bare “PE2 F-n” citations were file-qualified by **PE3 F-3** (`.41`) to mean `HE6_passPE2_report.md`, after this note acquired a passPE2 of its own with colliding numbering.

**XREF.** `lean/notes/openmath/CODEX_HE6PE1_2026-08-08.md` — EXISTS ✓; `HE6_passPE2_report.md` — EXISTS ✓.

---

### EFF.HE6R1.04  [supplier-finding]

**CANONICAL STATEMENT** (verbatim, the R9 row of §S1, L78). FORM: table cell (long).

> “**R9** \| F3 (UPSTREAM, regraded): GENHN-1's stage-initial-node display is wrong at f₁ ≥ 2 \| **APPLIED to GENHN as a dated `[r1]` ERRATUM annex** (GENHN is at attempt 0/2, unaccepted, so the tagged-repair mechanism applies rather than the frozen-annex one; its battery artifacts are untouched and every battery row has f₁ = 1). Corrected node: **{dv(A_j) ≥ (μ−j)·D′h + 1}, D′h = f₁S** — independently derived, not merely transcribed from the finding: every root of f on the opening locus is a (T1)/(T2) point, hence dv(Φ′(ρ)) > D′h (LEMMA HE6-0 as repaired by R4), hence every side of P(F) has slope > D′h (LEMMA HE6-3(a)), hence every pin lies strictly above the slope-D′h line through (μ,0), i.e. dv(A_j) > (μ−j)D′h, i.e. ≥ (μ−j)D′h + 1 by integrality. At f₁ = 1 this IS the displayed S-version (D′h = e₁h = S), which is why no battery row and no first-live case could see it. Consumption check: HE6/HE7 consume GENHN-**2** (the SLOT LEMMA) and HE3-0's locus, never GENHN-1's node display, so nothing downstream propagates; what is NOT settled here is whether GENHN's own f₁ ≥ 2 count-side displays that substitute the numeric value S for the node height need re-reading with f₁S — named in the annex as the residue of the erratum (no f₁ ≥ 2 stage genre is live below n = 8, and none is machine-exercised)”

**DERIVATION.** A four-step derivation from HE6's own repaired lemmas: `(T1)/(T2)` at every root ⟹ `dv(Φ′(ρ)) > D′h` (LEMMA HE6-0 post-R4) ⟹ every slope `> D′h` (LEMMA HE6-3(a)) ⟹ every pin strictly above the line through `(μ,0)` ⟹ integrality gives `≥ (μ−j)D′h + 1`.

**Mathematical audit.** The line of slope `D′h` through `(μ,0)` has height `(μ−j)D′h` at abscissa `j` ✓; “strictly above” plus integrality of `dv` gives `≥ (μ−j)D′h + 1` ✓. At `f₁ = 1`, `D′h = e₁f₁h = e₁h = S` ✓ — **which is exactly why no battery row could see the defect**, and the note says so.

**LANDING VERIFIED (rule 10).** `grep -cF 'ERRATUM' GENHN_PROOF_2026-08-08.md` = **17** ✓ — the dated erratum annex is present at the target.

**CONDITIONALITY — the residue that becomes A4 finding 2.** “what is NOT settled here is whether GENHN's own f₁ ≥ 2 count-side displays … need re-reading with f₁S”. This is **`GENHN-ERR-1`** (`.20`), and it is precisely what makes the completion statement's “none of them an open piece of mathematics” false (`.44`). **The note names its own residue and the residue later falsifies its own headline** — recorded because that sequence is the note's most instructive feature.

**XREF.** `GENHN_PROOF_2026-08-08.md` — `ERRATUM`, count 17; `LEMMA GENHN-1`, count 4; `LEMMA GENHN-2`, count 2. `spec/HYPOTHESIS_LEDGER.md` — `GENHN-ERR-1`, count 4.

---

### EFF.HE6R1.05  [corollary]

**CANONICAL STATEMENT** — §S2, COROLLARY HE6.B reworded to the widened box (L88–132). FORM: `##`-headed section carrying the reworded corollary and its four-case enumeration.

**DERIVATION.** The rewording is forced by Codex PE1 finding 1 (`.02`); the four-case enumeration is this note's own.

**CONDITIONALITY.** The **effective** form of COROLLARY HE6.B lives in HE6 (`spec/EFF-HE6.md` `.19`) and cites “the four-case enumeration is in `HE6R1_RECON_2026-08-08.md` §S2” — **so HE6's corollary is completed by this section, and neither note is self-contained on it.** Recorded at `spec/EFF-HE6.md` `.19` as well; the DAG needs the edge in both directions.

**XREF.** `HE6_PROOF_2026-08-08.md` — `HE6-BOX-1`, count 11.

---

### EFF.HE6R1.06  [lemma]

**CANONICAL STATEMENT** — §S3.1, the specialization of HE7's level-2 frame to ℓ = 1 (L136–162). FORM: `###`-headed section with a degeneration table.

**DERIVATION.** A specialization argument: each of HE7's derived level-2 objects (`dv₂`, `T₂`, `n₂`, the shift function `s(·)`) is evaluated at `ℓ = 1` and shown to degenerate benignly.

**CONDITIONALITY.** **This section supplies `s(·) ≡ 0` at ℓ = 1**, which is what makes the cocycle trivial — consumed three times downstream (`.35`'s PE2 F-2 rider, `.39`'s PE3 F-1 rider, and tooth HE6R1-T-TWIST0 at `.29`). A load-bearing table.

**XREF.** `HE7_PROOF_2026-08-08.md` — `ANNEX-LEMMA R1-a`, count 6.

---

### EFF.HE6R1.07  [lemma]

**CANONICAL STATEMENT** — §S3.2, the item-by-item check of every HE7 statement at ℓ = 1 (L163–248). FORM: `###`-headed section, ten numbered items.

**DERIVATION.** Ten items, each verifying that one HE7 statement's hypotheses and conclusion survive verbatim at `ℓ = 1`. §S0 summarizes the outcome: “**Answer: YES, and the ℓ = 1 branch is a literal instance** … no hypothesis … mentions ℓ except through `gcd(u, ℓ) = 1` (automatic at ℓ = 1) and through the derived objects dv₂, T₂, n₂, which degenerate benignly”.

**CONDITIONALITY.** §S3.5 states the scope precisely: “**AS A LITERAL INSTANCE OF HE7 §S1–S6** (§S3.2, ten items, **no adaptation**)”. **The literal-instance claim is what makes this note a reconciliation rather than a new development** — and it is exactly what makes the three surfaced lemmas (`.09`, `.13`, `.15`) *additions* rather than *adaptations*.

**XREF.** `HE7_PROOF_2026-08-08.md` — `THEOREM HE7.A`, count 32; `LEMMA HE7-6`, count 7; `LEMMA HE7-8`, count 17; `COROLLARY HE7-7″`, count 11.

---

### EFF.HE6R1.08  [supplier-finding]  **[HE7 ERRATUM 1 — LANDED]**

**CANONICAL STATEMENT** (verbatim, L259–268). FORM: display (blockquoted finding).

> “**FINDING HE6R1-F1 (on HE7 §S2, classification: statement over-reach at
> the jump condition; NON-PROPAGATING at n ≤ 15).** THEOREM HE7.A(3)'s
> "at a slope with a repeated residual factor and ℓ₂ = 1 the level-2
> α-refine exists" is false when the repeated factor has degree ≥ 2, and
> THEOREM HE7.C's jump condition ("ℓ ≥ 2") is correspondingly too narrow.
> Both are repaired by LEMMA HE6R1-1 with **identical bounds**. The finding
> does not propagate at the degrees HE7 claims: an ambiguity needs a
> repeated level-2 factor with ℓ₂d_{r₂} ≥ 2, hence L_{λ₂} ≥ 4, hence
> **μ₂ ≥ 4** — impossible at HE7's own μ₂ ≤ 3 scope (and at n = 8, where
> μ₂ = 2), so §S8's dictionary and the n = 8 closure are untouched.”

**DERIVATION.** The defect: the level-2 α-refine `Ψ ↦ Ψ − ŝ₂n₂(λ₂)` “does **not** exist, because `ŝ₂` would need residue `β₂ ∈ K₂(β₂) ∖ K₂`” (L255–257) — **the same mechanism as HE6's PE1 finding 1 one level up**. The non-propagation: `L_{λ₂} ≥ m·ℓ₂·d_{r₂} ≥ 4` forces `μ₂ ≥ 4`, outside HE7's `μ₂ ≤ 3` scope ✓ (arithmetic re-derived: `m ≥ 2` and `ℓ₂d_{r₂} ≥ 2` give `≥ 4` ✓).

**LANDING VERIFIED (rule 10).** `grep -cF 'HE6R1-F1' HE7_PROOF_2026-08-08.md` = **4** ✓. PE2 F-3 (`.36`) records the mechanism: “HE7 ACCEPTED 2/2 with its annex stack accepted, FULLY FROZEN (**FINDING HE6R1-F1 applied** — HE7 micro-annex `ca3754d`)”; `ca3754d` is a commit ✓.

**TYPE justification.** `supplier-finding` (rule 13) in its canonical form: a defect report against ANOTHER note, discharged at the source.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE6R1-F1`, count 4; `THEOREM HE7.A`, count 32; `THEOREM HE7.C`, count 9.

---

### EFF.HE6R1.09  [lemma]  **[CHARGE — the first of three]**

**CANONICAL STATEMENT** (verbatim, L270–287). FORM: display (blockquoted lemma with an indented two-line bound).

> “**LEMMA HE6R1-1 (the widened jump condition descends, with HE7.C's
> bounds).** At any level i, a node requires a level jump exactly when its
> side carries a repeated irreducible residual factor r_i (multiplicity
> m ≥ 2) with **ℓ_i·deg r_i ≥ 2**; the complementary repeated case
> (ℓ_i = deg r_i = 1) is an α-refine, finite by LEMMA HE7-8. At every jump:
>
>     μ_i ≥ L_{λ_i} ≥ m·ℓ_i·deg r_i ≥ 2·2 = 4 ,
>     μ_{i+1} ≤ deg R_{λ_i}/deg r_i ≤ μ_i/(ℓ_i·deg r_i) ≤ μ_i/2 .
>
> Hence the number J of level jumps in any history satisfies
> **J ≤ log₂ μ − 1 ≤ log₂ n − 2**, exactly as in THEOREM HE7.C; at n = 8
> there is one jump with μ₂ ≤ 2, and the first degree admitting two jumps is
> n = 16.”

**⚠ SUPERSEDED — the global bound is RE-DISPLAYED.** The clause “**J ≤ log₂ μ − 1 ≤ log₂ n − 2**” is found **REAL but OBSTRUCTED** by A4 finding 1 (`.43`) and then **re-displayed into three clauses** under the owner's directive (`.47`). **The governing effective form is the three-clause re-display**: (a) `J ≤ log₂ μ − 1` in ANY history; (b) `J ≤ log₂ n − 2` for **composite-stage-rooted** ladders (`D′ ≥ 2`); (c) `J ≤ log₂ n − 1` for **ambient-rooted** histories (`D′ = 1`), **and this is sharp**. **CHAIN:** frozen display → A4 obstruction → owner-directive re-display. **TERMINAL: the re-display.** **SUPERSESSION KIND:** `scope-pin` (the unconditional bound is withdrawn at ambient-rooted histories only).

**Mandatory arithmetic audit (rule 22) — the bound and its counterexample, both re-derived.** From `4 ≤ μ_J ≤ μ/2^{J−1}`: `2^{J−1} ≤ μ/4` ⟹ `J − 1 ≤ log₂μ − 2` ⟹ **`J ≤ log₂ μ − 1`** ✓ — clause (a) is exactly what the proof gives. The appended `≤ log₂ n − 2` needs `μ ≤ n/2`, i.e. `D′ = e₁f₁ ≥ 2` ✓ — clause (b). **At `D′ = 1` (ambient, `n = μ`) the bound is `J ≤ log₂ n − 1`**, and the A4 counterexample realizes it: a quartic with level-0 residual `r²`, `r` irreducible quadratic, gives `m = 2`, `ℓ = 1`, `d_r = 2`, side length `L = m·ℓ·d_r = 4 = μ = n`, so this is a jump, `J = 1`, and `log₂4 − 1 = 1` ✓ **sharp** — while the frozen global bound would give `log₂4 − 2 = 0`, **contradicted** ✓. **The A4 counterexample is exact and the frozen display is genuinely false at ambient roots.**

**CONDITIONALITY.** Clause (b) — the one “THEOREM HE7.C and every consumption site in this note cite” — is **unchanged**, so nothing consumed moves. The re-display's consumer sweep confirms it (`.47`).

**XREF.** `HE7_PROOF_2026-08-08.md` — `THEOREM HE7.C`, count 9; `LEMMA HE7-8`, count 17.

---

### EFF.HE6R1.10  [lemma]

**CANONICAL STATEMENT** — the proof of LEMMA HE6R1-1 (verbatim, L289–300). FORM: italic-headed paragraph proof.

> “*Proof.* The jump condition: HE6.A decides a separable residual at every ℓ;
> HE3's stage-α decides a repeated K-rational linear factor at an integer
> slope (HE6 §S6.3, unchanged by r1); the complement is exactly a repeated
> irreducible r with ℓ·deg r ≥ 2 (§S2's enumeration). The two displays are
> then HE7.C's own computations with "ℓ ≥ 2" replaced by "ℓ·d_r ≥ 2": the
> first because L_λ = ℓ·deg R_λ ≥ ℓ·m·d_r = m(ℓd_r) ≥ 4, the second because
> μ₂ = deg f_S/D″ ≤ n_λ/(D′ℓd_r) = D′L_λ/(D′ℓd_r) = deg R_λ/d_r ≤ μ/(ℓd_r),
> using LEMMA HE6-3(b) (n_λ = D′L_λ, (SEP)-free) for the middle step and
> ℓd_r ≥ 2 for the last. Iterating gives 4 ≤ μ_J ≤ μ/2^{J−1}. Every non-jump
> step either strictly decreases μ, or is an α-refine (finite, LEMMA HE7-8),
> or terminates the branch at μ = 1. ∎”

**DERIVATION.** The span is the derivation; its three-way case split (separable → HE6.A; repeated K-rational linear at integer slope → HE3 stage-α; complement → jump) is exactly `.05`'s enumeration.

**Mandatory arithmetic audit.** `L_λ = ℓ·deg R_λ ≥ ℓ·m·d_r = m(ℓd_r) ≥ 2·2 = 4` ✓. `μ₂ = deg f_S/D″` with `deg f_S = |S_{λ,r}|·` (per-root degree) — the chain `n_λ/(D′ℓd_r) = D′L_λ/(D′ℓd_r) = L_λ/(ℓd_r) = deg R_λ/d_r` ✓ (using `L_λ = ℓ deg R_λ`) `≤ μ/(ℓd_r)` ✓ (using `L_λ ≤ μ`). **Every step exact**, and the middle step's dependence on `LEMMA HE6-3(b)` is correctly flagged as `(SEP)`-free.

**CONDITIONALITY.** Consumes **HE6-3(b)** (`spec/EFF-HE6.md` `.17`(e)/`.30`) and **LEMMA HE7-8** (α-refine finiteness). Note the proof supports clause (a) unconditionally; **the `n`-form is where `D′ ≥ 2` enters silently** — which is precisely A4 finding 1's diagnosis.

**XREF.** `HE6_PROOF_2026-08-08.md` — `HE6-BOX-1`, count 11 (§S6.3 cited descriptively). `HE7_PROOF_2026-08-08.md` — `LEMMA HE7-8`, count 17.

---

### EFF.HE6R1.11  [record]

**CANONICAL STATEMENT** (verbatim, L297–300, the structural punchline). FORM: bold paragraph.

> “**Both branches of the widened box supply the descent factor ℓd_r ≥ 2 —
> (iv) as ℓ ≥ 2 with d_r ≥ 1, (ii) as d_r ≥ 2 with ℓ = 1 — so the widening
> costs nothing in the termination bound.** That is the reconciliation's
> structural punchline: the inequality that makes the ladder finite is the
> same inequality that defines the widened box.”

**DERIVATION.** [RECORD of an observation], and the note's own summary of why the reconciliation succeeds.

**CONDITIONALITY.** True as stated, and **unaffected by the A4 re-display** — the re-display touches the bound's *root-dependence*, not the descent factor. Recorded because a consumer might otherwise assume the re-display damages the punchline; it does not.

**XREF.** none.

---

### EFF.HE6R1.12  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S3.4's opening, L304–314). FORM: paragraph.

> “The widening prompted the check "how does the level-2 read START?", and
> that exposed a gap that is not about ℓ at all. THEOREM HE7.A is stated about
> the block factor f_S and puts μ₂ := deg f_S/D″; HE7-BOX-4 declines to prove
> the multiplicity-weighted class size |S_{λ,r}| = D′ℓ·m_r·d_r on the ground
> that "σ-decision uses only the level-2 polygon of the actual f_S". But when
> the block is **proper** (R_λ has another distinct factor, or P(F) has
> another side), f_S is not exhibited by the read and deg f_S is not pinned by
> HE6+HE7: at a non-separable R_λ the HE6.A sandwich has slack
> D′ℓΣ_r(m_r−1)d_r. First live configuration: a boxed node with a proper
> block needs μ ≥ 5, i.e. n ≥ 10 — inside the region COROLLARY HE7.B(i)
> claims. The following lemma closes it.”

**DERIVATION.** [RECORD of a gap diagnosis].

**Arithmetic audit of the slack and the first-live bound.** The HE6.A sandwich (`spec/EFF-HE6.md` `.32`) closes only when `R_λ` is separable; at multiplicities `m_r`, `Σ_r|S_{λ,r}| = n_λ = D′L_λ = D′ℓΣ_r m_r d_r` while each class is only known `≥ D′ℓd_r`, leaving slack `D′ℓΣ_r(m_r−1)d_r` ✓. First live: a **boxed** node needs `L_λ ≥ 4` and a **proper** block needs a second distinct factor, so `L_λ ≥ 4 + ℓd_{r′} ≥ 5`, hence `μ ≥ 5` and `n ≥ D′μ ≥ 10` ✓.

**CONDITIONALITY.** “inside the region COROLLARY HE7.B(i) claims” — so the gap is **live**, not hypothetical. `grep -cF 'COROLLARY HE7.B' HE7_PROOF_2026-08-08.md` = **22** ✓.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE7-BOX-4`, count 5; `COROLLARY HE7.B`, count 22; `LEMMA HE7-6`, count 7.

---

### EFF.HE6R1.13  [lemma]  **[CHARGE — the second of three]**

**CANONICAL STATEMENT** (verbatim, L316–350, clauses (a)(b)(c)). FORM: display (blockquoted lemma, three clauses, with an embedded `[r1′]` hypothesis insertion).

> “**LEMMA HE6R1-2 [r1′] (block projection).** Let f be monic on the opening
> locus with disc f ≠ 0 and Φ′ ∤ f, let (λ, r) be a level-1 label of f,
> S = S_{λ,r}, f_S the block factor (LEMMA HE7-6), g := f/f_S ∈ O[x], and
> assume **Ψ ∤ f_S** **[r1′, PE1 F-1]** — equivalently Ψ ∤ f: a root of Ψ
> is a level-2 point with level-1 label (λ, r) (LEMMA HE6-1), hence lies in
> S, so if Ψ | f then Ψ's roots are roots of f_S, and Ψ — squarefree as a
> divisor of f with disc f ≠ 0 — divides f_S. Then:
>
> **(a)** r ∤ R_λ^{(g)}, the λ-residual of g's own Φ′-development; hence for
> **every** level-2 point ξ, dv₂(g(ξ)) = ℓ·h_{F_g}(λ) — a constant c_g
> depending on (g, λ) only.
>
> **(b)** For every rational κ₂ > T₂, h_{F₂,f}(κ₂) = h_{F₂,f_S}(κ₂) + c_g,
> where h_{F₂,·} is the level-2 support function of the Ψ-adic development.
> Consequently the part of the level-2 polygon P₂(f) with slope > T₂ is the
> part of P₂(f_S) translated by c_g: same breakpoints, same slopes λ₂, same
> lengths L_{λ₂} — so
>
>     μ₂ = Σ_{λ₂ > T₂} L_{λ₂}(f)   and   |S_{λ,r}| = D″·μ₂
>
> are **computable from f**, without exhibiting f_S.
>
> **(c)** At every such side, R_{λ₂}^{f} and R_{λ₂}^{f_S} have the same
> degree L_{λ₂}/ℓ₂ and the same monic irreducible factors (same radical);
> in particular one is separable iff the other is, and in the separable
> [case …]”

**DERIVATION.** Three clauses: (a) is a non-divisibility plus a constancy consequence; (b) is a translation of the support function, hence of the polygon above `T₂`; (c) is a radical identity per side.

**The `[r1′]` hypothesis insertion is itself a repair with an argument.** `Ψ ∤ f_S` is inserted by this note's own PE1 F-1, and the insertion carries a proof that it is **equivalent to `Ψ ∤ f`** — via LEMMA HE6-1 (every root of Ψ is a level-2 point with label `(λ,r)`, hence in `S`) plus squarefreeness from `disc f ≠ 0` ✓. **Mathematical audit:** the equivalence is sound — `Ψ | f ⟹` Ψ's roots ⊆ roots of `f`, and being labelled `(λ,r)` they lie in `S`, so they are roots of `f_S`; squarefree `Ψ` then divides `f_S` ✓.

**CHAIN on clause (c)'s scalar (rule 25 — three layers).** `[r1′]` identifies the per-side scalar as `γ_g` → **PE2 F-2** (`.35`) adds the cocycle unit: `R^f_{λ₂} = γ_g · β^{c₁(h_{F₂,f_S}(λ₂), c_g)} · R^{f_S}_{λ₂}` → **PE3 F-1** (`.39`) corrects the exponent's argument to the **pin height**: `R^f_{λ₂} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R^{f_S}_{λ₂}`. **TERMINAL: PE3 F-1.** **At ℓ = 1 — the branch this note decides and its battery runs — `s(·) ≡ 0`, `c₁ ≡ 0`, and the scalar is `γ_g` alone**, so the `[r1′]` clause is exact there and all three layers agree.

**CONDITIONALITY.** **Proof-only** — HE6R1-BOX-2: “μ ≥ 5 (hence proper blocks — **LEMMA HE6R1-2's own configuration is proof-only**)”. The lemma closes a live gap at `n ≥ 10` and the battery runs at `n = 8`.

**XREF.** `HE7_PROOF_2026-08-08.md` — `LEMMA HE7-6`, count 7; `HE7-BOX-4`, count 5; `ANNEX-LEMMA R1-a`, count 6.

---

### EFF.HE6R1.14  [supplier-finding]  **[HE7 ERRATUM 2 — LANDED, and MACHINE-DISCOVERED]**

**CANONICAL STATEMENT** (verbatim, L455–467). FORM: paragraph plus a blockquoted finding.

> “The sealed battery reported 12 non-decisions out of 944 members (status
> BADTOTAL: the reader's block sizes did not sum to deg f). Diagnosis: at those
> members **dv₂(A_0^{(2)}) = ∞, i.e. Ψ | f** — the level-2 polygon loses its
> j = 0 pin and one block goes missing. This is the **exact level-2 analogue of
> Codex PE1 finding 2** (the Φ′ | f stratum at level 1, repaired at level 1 by
> R2): HE7 never states the hypothesis Ψ ∤ f_S, without which
> COROLLARY HE7-7″ has roots with no finite level-2 label.
>
> > **FINDING HE6R1-F2 (on HE7 §S1/§S2/§S5.5, classification: MISSING
> > HYPOTHESIS; repairable in one line, machine-discovered).** THEOREM HE7.A
> > and COROLLARY HE7-7″ require **Ψ ∤ f_S**. Without it the Ψ-development's
> > constant coefficient vanishes and roots shared with Ψ carry dv₂(Ψ(ρ)) = ∞,
> > exactly as Φ′ | f breaks HE3-0(iii) at level 1. Repair: LEMMA HE6R1-3.”

**DERIVATION.** [RECORD of a machine-discovered missing hypothesis].

**AUDIT disposition (rule 27).** **This is the one finding in queue 8b produced by a battery rather than by a reader** — “found BY the new battery”, from 12 BADTOTAL non-decisions. **TEETH disposition (rule 20):** the sealed prediction P1 *failed* on exactly this stratum (`.24`), so the failure **is** the discovery. A preregistered prediction failing informatively is the ideal case, and the note scores it honestly as a failure rather than folding it into a pass.

**Structural note.** The finding is “the **exact level-2 analogue of Codex PE1 finding 2**” — the `Φ′ | f` stratum that `HE6-PEEL-CONVENTION` (`spec/EFF-HE6.md` `.09`) repairs at level 1. **The same defect at two levels, found by two different means** (a human-style counterexample at level 1, a battery non-decision at level 2).

**LANDING VERIFIED (rule 10).** `grep -cF 'HE6R1-F2' HE7_PROOF_2026-08-08.md` = **8** ✓.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE6R1-F2`, count 8; `COROLLARY HE7-7″`, count 11; `THEOREM HE7.A`, count 32.

---

### EFF.HE6R1.15  [lemma]  **[CHARGE — the third of three]**

**CANONICAL STATEMENT** (verbatim, L469–479). FORM: display (blockquoted lemma with an indented display).

> “**LEMMA HE6R1-3 (the level-2 peel).** Suppose Ψ | f_S. Then
> g₀ := gcd(f_S, Ψ) **equals Ψ**, Ψ is IRREDUCIBLE over O of degree D″, and
> it is a simple factor of f_S with
>
>     e(Ψ) = e₁ℓ ,    f(Ψ) = f₁d_r .
>
> Consequently f_S = Ψ·f_S′ with **Ψ ∤ f_S′**, every root of f_S′ is still a
> level-2 point, and THEOREM HE7.A applies to f_S′ with μ₂ − 1 in place of
> μ₂. The peel terminates (μ₂ drops by 1 each time, and in fact at most once).”

**DERIVATION** — `.16`.

**CONDITIONALITY.** The lemma both **repairs FINDING HE6R1-F2** and **proves Ψ irreducible** — a strictly stronger conclusion than the hypothesis it restores. Note the parallel the note draws: this is `HE6-PEEL-CONVENTION`'s peel one level up, and it likewise yields a KNOWN σ-block (here `(e₁ℓ, f₁d_r)`).

**XREF.** `HE7_PROOF_2026-08-08.md` — `THEOREM HE7.A`, count 32.

---

### EFF.HE6R1.16  [lemma]

**CANONICAL STATEMENT** — the proof of LEMMA HE6R1-3 and its machine confirmation (verbatim, L481–492). FORM: italic proof plus a bold-headed confirmation.

> “*Proof.* Every root ξ of g₀ is a root of Ψ = Ψ_{λ,r}, hence a level-2 point
> with level-1 label (λ, r) (LEMMA HE6-1), so LEMMA HE6-0′ gives
> [L_ξ : K₀] ≥ (e₁ℓ)(f₁d_r) = D″. Since f_S ∈ O[x] and its root set is
> Galois-stable, g₀ ∈ O[x] is Galois-stable too, so it contains ξ's whole orbit:
> deg g₀ ≥ D″. But g₀ | Ψ gives deg g₀ ≤ deg Ψ = D″. Hence deg g₀ = D″, g₀ = Ψ,
> and Ψ is a single Galois orbit, i.e. irreducible, with e ≥ e₁ℓ, f ≥ f₁d_r and
> ef = D″ = (e₁ℓ)(f₁d_r), forcing equality on both. Simplicity and Ψ ∤ f_S′
> follow from disc f_S ≠ 0 (a second Ψ-factor would repeat roots). ∎”

> “**Machine confirmation.** The post-seal supplementary leg
> (`verification/openmath/he6r1_supp.py`, item (A)) applies this peel to all 12
> degenerate members: **12/12 decided, and all 5 PARI-checkable ones AGREE**,
> each with exactly one peel and σ = {(2,2),(2,2)} = {(e₁ℓ, f₁d_r)} ⊔ {the
> level-2 block of f_S′} — the lemma's prediction, member by member.”

**DERIVATION.** The span is the derivation — a squeeze on `deg g₀` between `≥ D″` (Galois orbit, via LEMMA HE6-0′) and `≤ D″` (divisor of Ψ), then the `e·f = D″` sandwich.

**Mathematical audit.** `D″ = D′ℓd_r = (e₁f₁)ℓd_r = (e₁ℓ)(f₁d_r)` ✓, so LEMMA HE6-0′'s bound is exactly `deg Ψ` ✓ — **the squeeze is tight by construction**, which is what forces irreducibility. `e ≥ e₁ℓ`, `f ≥ f₁d_r`, `ef = (e₁ℓ)(f₁d_r)` ⟹ equality both ✓ — **the same sandwich as HE6's THEOREM HE6.A step 4** (`spec/EFF-HE6.md` `.32`), one level up. At the battery's frame `(e₁,f₁,ℓ,d_r) = (2,1,1,2)`: `e(Ψ) = 2`, `f(Ψ) = 2`, so the peeled block is `(2,2)` and the prediction `σ = {(2,2),(2,2)}` ✓ — **consistent with the σ-alphabet's third element** at `.25`.

**CONDITIONALITY.** Consumes **LEMMA HE6-1** and **LEMMA HE6-0′** — both inside HE6's `HE6-TEST-PACKAGE` pin span (`spec/EFF-HE6.md` `.17`(a),(b)). **The machine confirmation is post-seal**, hence scored separately from the sealed verdict (`.24`).

**XREF.** artifact `verification/openmath/he6r1_supp.py` — EXISTS ✓; `he6r1_supp_output.txt`, `he6r1_supp_results.json` — both EXIST ✓.

---

### EFF.HE6R1.17  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, §S3.5 L496–511). FORM: display (blockquoted verdict).

> “**THE ℓ = 1 BRANCH OF THE WIDENED BOX IS DECIDED, AS A LITERAL INSTANCE
> OF HE7 §S1–S6** (§S3.2, ten items, no adaptation), **with**
> (i) LEMMA HE6R1-1 replacing HE7.C's jump condition and HE7.A(3)'s
> trichotomy by the widened ones — SAME bounds, so TERMINATION is unchanged
> (J ≤ log₂ n − 2; n = 8 has one jump at μ₂ ≤ 2; level 3 first possible at
> n = 16); and
> (ii) LEMMA HE6R1-2 supplying the level-2 read's starting data at a proper
> block (the one genuine composition gap the widening exposed — not an
> ℓ-issue), which also supplies HE7-BOX-4's count in read form; and
> (iii) LEMMA HE6R1-3 supplying the level-2 peel at Ψ | f_S (FINDING
> HE6R1-F2, the level-2 analogue of Codex F2 — found by this note's own
> battery and confirmed by it, 12/12 with 5/5 PARI).
> **Residue: NONE in the σ-decision chain.** What remains are the named
> arc/coverage boxes (§S5), not open mathematics.”

**DERIVATION.** [RECORD of a reconciliation verdict] — the note's headline claim.

**CONDITIONALITY — two qualifications the effective text imposes.** (1) Item (i)'s parenthetical `J ≤ log₂ n − 2` is the **stage-rooted** bound, which the A4 re-display leaves intact as clause (b) — the re-display's own consumer sweep names “the §S4 consumption line” and “THEOREM HE7.C's bounds” as “stage-rooted (clause (b)) and unchanged” ✓. **So this verdict survives the re-display.** (2) “**Residue: NONE in the σ-decision chain**” is true of the σ chain but **must not be read as covering `GENHN-ERR-1`**, which is a count-side residue outside the σ chain (`.20`) — and which A4 finding 2 shows the completion statement does not honestly clear (`.44`).

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE7-BOX-4`, count 5; `THEOREM HE7.C`, count 9.

---

### EFF.HE6R1.18  [instrument-record]

**CANONICAL STATEMENT** (verbatim, §S4 L515–532). FORM: bold-headed paragraphs.

> “**Why a new leg is owed.** HE7's battery exercises only ℓ = 2, d_r = 1, so
> K₂ = K = F_p and β = s is a SCALAR: the entire residue-direction mechanism
> of §S3.1 is invisible there (HE7-BOX-2 lists "d_r ≥ 2 (K₂ a proper
> extension)" among the things NOT exercised). This leg runs the OTHER branch.
>
> **Frame and rows.** (e₁,f₁,h) = (2,1,1), Φ′ = x²−π, D′ = 2, ϖ = x, μ = 4,
> deg f = 8; ℓ = 1 with λ ∈ {3, 5} (λ > D′h = 2); R_λ = r² with r ∈ F_p[Z]
> irreducible of degree 2, r(0) ≠ 0 — so D″ = 4, K₂ = F_{p²}, T₂ = 2λ,
> μ₂ = 2, block = everything. Rows: ℤ_3 (r = Z²+1), ℤ_5 (Z²+2 and Z²+Z+1),
> ℤ_7 (Z²+Z+3), ℤ_5 at λ = 5, and F_3[[t]], F_5[[t]] (identities only —
> oracle asymmetry, HE6-BOX-4). Members are perturbations **strictly above the
> λ-line**, so every member of a row has the SAME outer data and only the
> deeper digits move. Instrument: rings, resultants, Φ′-development, level-1
> slot value/residue, normalizers, hull, PARI bridge IMPORTED from the sealed
> `he6_checks.py` (md5 pinned in the artifacts); the level-2 layer over
> K₂ = F_{p²} is fresh.”

**DERIVATION.** [RECORD] — an `instrument-record` (rule 19) with an explicit statement of the coverage hole it fills.

**Mandatory arithmetic audit (rule 22).** `D′ = e₁f₁ = 2` ✓; `λ > D′h = 2` so `λ ∈ {3,5}` ✓; `D″ = D′ℓd_r = 2·1·2 = 4` ✓; `K₂ = K(β)` with `[K₂:K] = d_r = 2` and `K = F_p` (since `f₁ = 1`), so `K₂ = F_{p²}` ✓; `T₂ = ℓd_rλ = 1·2·λ = 2λ` ✓; `μ₂ = deg f_S/D″ = 8/4 = 2` ✓ (block = everything, since `R_λ = r²` has one distinct factor). `deg f = D′μ = 8` ✓. **Every frame parameter is forced and every one checks.**

**CONDITIONALITY.** **The instrument reuses HE6's sealed primitives** (“IMPORTED from the sealed `he6_checks.py`”) with only the level-2 layer fresh — so its independence from HE6 is partial by design, and the note says so. **PIN VERIFIED:** all four import pins recorded in the json reproduce exactly (`he6_checks.py` `321fa4d4990e…`, `he7_checks.py` `688adbe88447…`, `w12_checks.py` `7dc040d94fbb…`, `w10_checks.py` `a9c34244a3af…`).

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE7-BOX-2`, count 1. `HE6_PROOF_2026-08-08.md` — `HE6-BOX-4` cited descriptively.

---

### EFF.HE6R1.19  [preregistration]

**CANONICAL STATEMENT** (verbatim, §S4 L534–545). FORM: bold-headed paragraph.

> “**Preregistered predictions** (P1 read-vs-PARI on the three-σ alphabet
> {(4,2)}, {(2,4)}, {(2,2),(2,2)}; P2 (SLOT₂) exactness
> v(Res(f,C)) = 4·dv₂(C); P3 the (LIFT₂) reachable sets at d_r = 2; P4 the
> level-2 flat identity at rational level-2 heights with a generic degree-3
> letter over K₂; P5 strict excess exactly at the level-2 labels) and **five
> teeth** (HE6R1-T-CRACK, -NAIVEHE6A, -BASIS, -TWIST0, -WITHHOLD) are in the
> runner's docstring, sealed unrun at commit 1 (4f5ebaa) with the smoke record
> disclosed. One post-seal `[r1-fix]` was applied before the full run: a
> print-only guard (`pstr`) because `polystr` cannot format the char-p ring's
> coefficients — no predicate touched.”

**DERIVATION.** [RECORD of five preregistrations plus five teeth].

**Arithmetic audit.** P2's `v(Res(f,C)) = 4·dv₂(C)`: the factor 4 is `D″ = 4` ✓ — the resultant of `f` (degree 8) against a level-2 test of degree `< D″` reads `D″` copies of `dv₂`. Consistent with `.26`'s reported form.

**CONDITIONALITY.** **The three-σ alphabet is preregistered**, so P1's later failure is a failure *within* a stated alphabet, not an unbounded surprise — and indeed “0 returned σ outside the preregistered three-element alphabet” (`.24`). The post-seal `[r1-fix]` is disclosed as print-only with “no predicate touched”. **PIN VERIFIED:** `4f5ebaa` is a commit ✓.

**XREF.** artifact `verification/openmath/he6r1_checks.py` — EXISTS ✓.

---

### EFF.HE6R1.20  [hypothesis-box]

**CANONICAL STATEMENT** (verbatim, §S5 L549–575 — the four boxes). FORM: display (blockquoted boxes).

> “**HE6R1-BOX-1 (arc grade).** This note is **attempt 0/2**; HE6 is **0/2
> post-r1** … Every consequence inherits the minimum over
> {GENHN 0/2, HE6 0/2, HE7 0/2, HE3 1/2 at μ ≤ 3, GENIND 0/2, W-12 0/2}.
> **HE6R1-BOX-2 (machine coverage).** This leg exercises ℓ = 1, d_r = 2,
> (e₁,f₁) = (2,1), μ = 4, μ₂ = 2, λ ∈ {3,5}, q ∈ {3,5,7} char 0 and
> q ∈ {3,5} char p. NOT exercised: f₁ ≥ 2 stage genres, d_r ≥ 3, μ ≥ 5
> (hence proper blocks — LEMMA HE6R1-2's own configuration is proof-only),
> level 3 (unreachable below n = 16). The proofs are uniform in all of these.
> **HE6R1-BOX-3 (oracle asymmetry).** PARI `factorpadic` exists only on the
> ℤ_p side; char-p rows are scored against the reader plus the resultant
> identities. Inherited from HE6-BOX-4.
> **GENHN-ERR-1 (the R9 residue).** Whether GENHN's f₁ ≥ 2 count-side
> displays that substitute S = e₁h for the node height need re-reading with
> D′h = f₁S is NOT settled here; no f₁ ≥ 2 stage genre is live below n = 8
> or machine-exercised. The corrected node itself is proved (R9).”

**DERIVATION.** [RECORD of four fences].

**CONDITIONALITY — three of the four move.** BOX-1's grades are **re-dated by PE2 F-3** (`.36`) and this note is **ACCEPTED 2/2** (`.38`) and ledger-CERTIFIED. BOX-2 and BOX-3 are current. **`GENHN-ERR-1` is the note's one open mathematical residue** and is the subject of A4 finding 2 (`.44`) — **and it has since been SETTLED**: SOL ledger row 15 reads “GENHN-ERR-1 settled by LEMMA GENHN-COUNT-RERUN (certificate confirmed; transcription confirmed at TC2)” (§5.2). **So the box is stale at HEAD in the direction of resolution.**

**XREF.** `spec/HYPOTHESIS_LEDGER.md` — `GENHN-ERR-1`, count 4. `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — row 15.

---

### EFF.HE6R1.21  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S5 L577–579). FORM: bold-headed paragraph.

> “**What is NOT boxed any more (the σ-decision chain).** HE6-BOX-1 in its
> WIDENED form: both branches are decided — (iv) by HE7 §S8 and its battery,
> (ii) by §S3 here and this note's battery. HE7-BOX-4 is superseded in read
> form by LEMMA HE6R1-2(b)+(c).”

**DERIVATION.** [RECORD of two box closures].

**CONDITIONALITY.** **The closure of HE6-BOX-1 is a two-note composition** — branch (iv) at HE7, branch (ii) here — so neither note closes it alone. `spec/EFF-HE6.md` `.36` records the same split from HE6's side. **HE7-BOX-4's supersession is “in read form”**, a careful qualification: HE6R1-2 supplies the count as computable from `f`, not the multiplicity-weighted class size HE7-BOX-4 declined to prove.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE7-BOX-4`, count 5. `HE6_PROOF_2026-08-08.md` — `HE6-BOX-1`, count 11.

---

### EFF.HE6R1.22  [instrument-record]

**CANONICAL STATEMENT** (verbatim, §S6 L581–589). FORM: bold-headed paragraph.

> “**Artifacts.** `he6r1_checks_output.txt`, `he6r1_checks_results.json` (sealed
> runner `he6r1_checks.py`, commit 1 = 4f5ebaa, one disclosed post-seal
> print-only `[r1-fix]`); post-seal supplementary `he6r1_supp.py` +
> `he6r1_supp_output.txt` / `he6r1_supp_results.json`. Import pins recorded in
> the json (`he6_checks.py` 321fa4d4990e…, `he7_checks.py` 688adbe88447…,
> `w12_checks.py` 7dc040d94fbb…, `w10_checks.py` a9c34244a3af…). 87.2 s.”

**DERIVATION.** [RECORD].

**PIN VERIFICATION (rule 23).** **All four import md5 prefixes reproduce byte-exactly** at compile time: `321fa4d4990eef67ff6a20f375c32366`, `688adbe88447b570104e379b1fa11cd5`, `7dc040d94fbbb1e8d20ac817b665d418`, `a9c34244a3af19f5fa864375b494380b` ✓. `4f5ebaa` is a commit ✓. **All six artifact files EXIST** ✓.

**CONDITIONALITY.** **Unlike HE6, this note does NOT pin its own artifacts' md5s** — only the imports'. So the runner and its outputs are pinned by commit and by the disclosed `[r1-fix]`, not by hash. **Disposition: `UNPINNED-VALUE`** for the note's own three artifacts; the four imports are fully pinned and fully verified. Recorded, not silently passed.

**XREF.** six artifacts, all EXIST ✓.

---

### EFF.HE6R1.23  [run-record]

**CANONICAL STATEMENT** (verbatim, §S6 L591–599, with the `[r1′]` split in place). FORM: bold-headed paragraph.

> “**Totals.** 7 rows (5 × ℤ_p with the PARI oracle, 2 × F_p[[t]] without),
> **944 members** · **932 decided by the reader** · **682 PARI σ jobs** ·
> **1,512 (SLOT₂) exactness identities** · **252 level-2 flat identities** ·
> **42 strict-excess certificates + 4 sealed SEP2 violations (recovered
> STRICT post-seal, §P4/P5) + 4 infinite-excess certificates** **[r1′, PE1
> F-4:** the sealed line read "46 strict-excess … certificates"; 46 is the
> runner's SEP2 counter of TESTED instances, and the 4 that violated at the
> seal were not certificates at the seal — the split is now displayed**]** ·
> 5 exhaustive (LIFT₂) reachability frames at d_r = 2.”

**DERIVATION.** [RECORD].

**Mandatory arithmetic audit (rule 22) — reconstructed from the σ census at `.25`.** Members `124+139+140+140+139+124+138 = 944` ✓. PARI jobs = the five ℤ_p rows: `124+139+140+140+139 = 682` ✓. Decided = the σ-column sums `120+139+139+140+139+120+135 = 932` ✓ — **and `944 − 932 = 12`, exactly the BADTOTAL count** ✓. Non-decisions in the PARI rows: `4+0+1+0+0 = 5` ✓ — **exactly “5 of the 12 sit in the PARI count”** ✓, hence `682 − 5 = 677` agreements ✓. **The entire totals line reconstructs from the table, to the last unit.** SEP2: `42 + 4 = 46` ✓ — the `[r1′]` split is arithmetically exact.

**SUPERSESSION KIND (the `[r1′]` bracket):** `counter re-reading` — 46 tested instances re-read as 42 certificates + 4 sealed violations. **TEETH disposition (rule 20):** `signed vacuity disclosure` — a counter of *tested* instances had been reported as a counter of *certificates*.

**XREF.** none.

---

### EFF.HE6R1.24  [run-record]

**CANONICAL STATEMENT** (verbatim, §S6 L598–612 — P1's failure record). FORM: bold-headed paragraph.

> “**P1 (HE6R1-READ2 / HE6R1-SIG2 — the headline): FAILED AS PREREGISTERED —
> DIAGNOSED AND CURED POST-SEAL [r1′, PE1 F-7].** The sealed prediction read
> "On every member the … read returns a σ … and PARI … AGREES, member by
> member, 0 mismatches"; as stated it failed on 12 of the 944 members, which
> returned NO σ (status BADTOTAL; 5 of the 12 sit in the PARI count, so 677
> of 682 PARI jobs agree). Content of the failure: the 12 are non-decisions,
> never a wrong σ — the 677 decided-and-PARI-checked members matched 677/677,
> with 0 returned σ outside the preregistered three-element alphabet. The 12
> are the Ψ | f_S stratum of FINDING HE6R1-F2, and LEMMA HE6R1-3's peel
> decides the 12 with 5/5 PARI agreement (§S3.4b) — a post-seal cure, scored
> as such rather than folded into a ✓. (The sealed scoreboard's "✓ with one
> honest qualification" is retired **[r1′]**: a preregistered prediction that
> fails on a stratum is a failed prediction with a diagnosis, however good
> the diagnosis.)”

**DERIVATION.** [RECORD of a failed preregistration with its diagnosis and post-seal cure].

**SUPERSESSION KIND (the `[r1′]` retirement):** `replacement` — “✓ with one honest qualification” replaced by “FAILED AS PREREGISTERED”. **TEETH disposition (rule 20):** `disclosed non-repair` is the wrong label; the right one is **a failed preregistration honestly scored**. The note's own sentence is the standard: “*a preregistered prediction that fails on a stratum is a failed prediction with a diagnosis, however good the diagnosis.*”

**Compiler assessment.** **This is the most disciplined preregistration-scoring event in queue 8b.** The failure was informative (it *discovered* erratum 2), the diagnosis was complete (the `Ψ | f_S` stratum), the cure was proved (`.15`) and machine-confirmed (12/12, 5/5 PARI) — and the note still refused to score it as a pass. Recorded at length because the standard it sets is quotable.

**Arithmetic audit.** `677/682`, `5` of `12` in the PARI rows, `0` σ outside the alphabet — all reconstructed exactly at `.23`/`.25` ✓.

**XREF.** `HE6R1_passPE1_report.md` — EXISTS ✓.

---

### EFF.HE6R1.25  [table]

**CANONICAL STATEMENT** — the per-row σ census (verbatim, L613–621). **Rule 14 applies**: emitted twice.

Source display, verbatim (emission 1 of 2):

>     row                          members  PARI  {(4,2)}  {(2,4)}  {(2,2),(2,2)}
>     Z_3  lam=3  r=Z^2+1            124     124     92       16         12
>     Z_5  lam=3  r=Z^2+2            139     139    118        8         13
>     Z_5  lam=3  r=Z^2+Z+1          140     140    134        2          3
>     Z_7  lam=3  r=Z^2+Z+3          140     140    139        1          0
>     Z_5  lam=5  r=Z^2+2            139     139    118        8         13
>     F_3[[t]] lam=3 r=Z^2+1         124       0     92       16         12
>     F_5[[t]] lam=3 r=Z^2+2         138       0    119        7          9

`[TABLE]` (emission 2 of 2 — Markdown transcription, with the compiler's derived columns)

| row | members | PARI | `{(4,2)}` | `{(2,4)}` | `{(2,2),(2,2)}` | σ-sum | **non-decisions** |
|---|---|---|---|---|---|---|---|
| ℤ_3 λ=3 r=Z²+1 | 124 | 124 | 92 | 16 | 12 | 120 | **4** |
| ℤ_5 λ=3 r=Z²+2 | 139 | 139 | 118 | 8 | 13 | 139 | 0 |
| ℤ_5 λ=3 r=Z²+Z+1 | 140 | 140 | 134 | 2 | 3 | 139 | **1** |
| ℤ_7 λ=3 r=Z²+Z+3 | 140 | 140 | 139 | 1 | 0 | 140 | 0 |
| ℤ_5 λ=5 r=Z²+2 | 139 | 139 | 118 | 8 | 13 | 139 | 0 |
| F_3[[t]] λ=3 r=Z²+1 | 124 | 0 | 92 | 16 | 12 | 120 | **4** |
| F_5[[t]] λ=3 r=Z²+2 | 138 | 0 | 119 | 7 | 9 | 135 | **3** |
| **TOTAL** | **944** | **682** | 812 | 58 | 62 | **932** | **12** |

**Mandatory arithmetic audit (rule 22) — the census fully reconciled, and the note's four headline figures derived from it.** Members sum **944** ✓. PARI sum (ℤ_p rows only) **682** ✓. σ-column sums per row give **932** decided ✓ and **12** non-decisions ✓ — **matching the totals line exactly**. Non-decisions inside the PARI rows: `4 + 0 + 1 + 0 + 0 = 5` ✓, giving **677** agreements ✓. σ-alphabet column totals `812 + 58 + 62 = 932` ✓. **Every one of the note's five headline numbers (944, 932, 682, 677, 12) is derivable from this table alone, and all five check.**

**A compiler observation worth recording.** The two char-p rows carry **0** PARI but full σ columns — so their σ values come from the reader alone (HE6R1-BOX-3). And **`(ℤ_3, λ=3)` and `(F_3[[t]], λ=3)` have identical member counts and identical σ columns** (124 / 92 / 16 / 12) ✓ — a characteristic-independence observation the note does not comment on, recorded here as a corroborating datum, not a claim.

**CONDITIONALITY.** The `{(2,2),(2,2)}` column is the σ that `LEMMA HE6R1-3`'s peel predicts for the degenerate stratum (`.16`), which is consistent with the peel's frame arithmetic `(e₁ℓ, f₁d_r) = (2,2)` ✓.

**XREF.** none.

---

### EFF.HE6R1.26  [run-record]

**CANONICAL STATEMENT** (verbatim, L623–627). FORM: bold-headed paragraph.

> “**P2 (HE6R1-SLOT2) ✓ 0 violations in 1,512 checks:**
> v(Res(f, C)) = 4·dv₂(C) exactly for C ∈ O[x] of degree < D″ = 4, exercising
> both β-slots and their ties — the machine form of (SLOT₂)'s exactness in the
> frame where the exactness comes ENTIRELY from K₂-independence (ℓ = 1: there
> is only one class mod ℓ, so the ℓ ≥ 2 mechanism is absent).”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** **This is the leg's methodological point:** at `ℓ = 1` the class-separation mechanism (`gcd(u,ℓ) = 1`, one class mod ℓ) is vacuous, so (SLOT₂)'s exactness must come **entirely** from `K₂`-independence. **The tooth HE6R1-T-BASIS (`.29`) is the certificate that this second mechanism is load-bearing** — “the ℓ = 1 replacement for gcd(u, ℓ) = 1”. Recorded because it is the precise sense in which this leg tests something HE7's battery cannot.

**XREF.** none.

---

### EFF.HE6R1.27  [run-record]

**CANONICAL STATEMENT** (verbatim, L629–645). **Rule 14 applies** to the frame table: emitted twice.

> “**P3 (HE6R1-LIFT2) ✓ the FIRST d_r ≥ 2 leg of this program** (HE7-BOX-2's
> named coverage hole): by exhaustive enumeration in five frames the level-2
> heights at which the residue map is ONTO K₂ = F_{p²} are exactly {k ≥ λ},
> matching HE7's W₂ = {k : m(k) − tu ∈ W₁ ∀t < d_r} at ℓ = 1; every k above the
> closed-form threshold (d_r−1)u + (D′−1)h = λ+1 is onto (so the closed form is
> sufficient, and by 1 not tight), and every k < λ fails — only F_p ⊊ K₂ is
> reached, because the β-slot's height k − λ is negative.”

Source display, verbatim (emission 1 of 2):

>     frame (p, lam, r)      thr = lam+1   onto            NOT onto
>     (3, 3, Z^2+1)               4        k >= 3          {0,1,2}
>     (5, 3, Z^2+2)               4        k >= 3          {0,1,2}
>     (5, 3, Z^2+Z+1)             4        k >= 3          {0,1,2}
>     (7, 3, Z^2+Z+3)             4        k >= 3          {0,1,2}
>     (5, 5, Z^2+2)               6        k >= 5          {0,1,2,3,4}

`[TABLE]` (emission 2 of 2)

| frame `(p, λ, r)` | closed-form threshold `λ+1` | onto | NOT onto | gap |
|---|---|---|---|---|
| (3, 3, Z²+1) | 4 | `k ≥ 3` | {0,1,2} | 1 |
| (5, 3, Z²+2) | 4 | `k ≥ 3` | {0,1,2} | 1 |
| (5, 3, Z²+Z+1) | 4 | `k ≥ 3` | {0,1,2} | 1 |
| (7, 3, Z²+Z+3) | 4 | `k ≥ 3` | {0,1,2} | 1 |
| (5, 5, Z²+2) | 6 | `k ≥ 5` | {0,1,2,3,4} | 1 |

**Mandatory arithmetic audit (rule 22).** The closed form `(d_r−1)u + (D′−1)h` at `d_r = 2`, `ℓ = 1` (so `u = λ`), `D′ = 2`, `h = 1` gives `1·λ + 1·1 = λ+1` ✓ — matching the `thr` column in all five frames ✓. Observed onset `k = λ` in all five ✓, so **the gap is exactly 1 in every frame** ✓ — “sufficient, and by 1 not tight”. The NOT-onto sets are `{0,…,λ−1}` ✓, of size λ, matching both rows' displays (3 and 5 entries) ✓.

**⚠ SUPERSEDED — the §S6 summary's claim about this result.** §S6 later says the leg establishes “(LIFT₂)'s threshold is **exactly** the closed form at d_r ≥ 2”, which **contradicts this very table** (onset λ, closed form λ+1). **A4 finding 4** (`.46`) corrects it. **The internal contradiction is between P3's own numbers and the §S6 prose 60 lines later** — recorded as the second internal contradiction pattern this queue has seen (cf. `spec/EFF-HE6.md` `.61`).

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE7-BOX-2`, count 1.

---

### EFF.HE6R1.28  [run-record]

**CANONICAL STATEMENT** (verbatim, L647–654). FORM: bold-headed paragraph.

> “**P4/P5 (HE6R1-GEN2 / HE6R1-SEP2) ✓ 252 flat identities with 0 violations;
> 42 sealed strict excesses, and the 4 sealed SEP2 violations recovered
> STRICT post-seal [r1′, PE1 F-4]:** the four sealed SEP2
> violations are a LEG-CONSTRUCTION artifact, not a mathematical failure — the
> sealed grid took the label from the reader's post-α-refine state but built the
> test polynomial over the PRE-refine key. Rebuilt over the refined key
> (supplementary leg item (B)), all 4 give STRICT excess (68 > 64 twice,
> 100 > 96 twice), i.e. **4/4 recovered**.”

**DERIVATION.** [RECORD of a leg-construction defect and its post-seal recovery].

**TEETH disposition (rule 20).** `disclosed non-repair` inverted: four **sealed violations** that turned out to be instrument artifacts, disclosed as such with the mechanism named (pre- vs post-α-refine key) and the recovery quantified. **The note does not fold them into the pass** — the totals line (`.23`) displays “42 strict-excess certificates + 4 sealed SEP2 violations (recovered STRICT post-seal)” as three separate counts.

**Arithmetic audit.** `42 + 4 = 46` ✓, the runner's tested-instance counter. The recovered excesses `68 > 64` and `100 > 96` ✓ — both strict, both by 4, consistent with a single-unit level-2 excess at the frame's scaling.

**CONDITIONALITY.** Post-seal, hence scored separately from the sealed verdict — the same discipline as `.24`.

**XREF.** artifact `verification/openmath/he6r1_supp.py` — EXISTS ✓.

---

### EFF.HE6R1.29  [run-record]

**CANONICAL STATEMENT** (verbatim, L656–678 — the five teeth). FORM: bold-headed paragraph plus five bullets.

> “**Teeth: 5/5 FIRED, on both tooth frames (p = 3 and p = 5).**
> * **HE6R1-T-CRACK ✓ (the widening's non-vacuity certificate)** three distinct
>   PARI σ inside ONE family of IDENTICAL outer data — at p = 5: {(4,2)} 54,
>   {(2,4)} 3, {(2,2),(2,2)} 2 over 59 members, level-2 read agreeing 59/59; at
>   p = 3: 47 / 6 / 1 over 54 members, agreeing 54/54. **So the ℓ = 1 branch of
>   the widened box is exactly as real as the ℓ ≥ 2 branch HE6 certified — no
>   outer-data-only argument can decide it — and the level-2 read decides it.**
> * **HE6R1-T-NAIVEHE6A ✓** the planted "treat r² as separable" dictionary
>   ({(2,2),(2,2)}) is refuted by PARI on 57/59 (p=5) and 53/54 (p=3) members.
> * **HE6R1-T-BASIS ✓** at γ₀ = −γ₁ ≠ 0 there is NO cancellation
>   (v(Res) = 4·dv₂ exactly, dv₂ = 5, v = 20) while a reader that sums the two
>   within-class residues in K instead of K₂ WOULD see cancellation — the
>   machine form of "{1, β} is a K-basis of K₂", the ℓ = 1 replacement for
>   gcd(u, ℓ) = 1.
> * **HE6R1-T-TWIST0 ✓** 1,276 level-2 twist exponents computed, all zero —
>   the level-2 normalizer cocycle degenerates at ℓ = 1 (n₂(k) = ϖ^k), so
>   HE6's twist-free convention IS available here, in contrast to HE7's
>   HE7-T-BADTWIST where dropping the twist mispredicts σ on 21 reads.
> * **HE6R1-T-WITHHOLD ✓** with a level-2 residual withheld the reader reports
>   UNDETERMINED.”

**DERIVATION.** [RECORD of five teeth].

**Mandatory arithmetic audit (rule 22).** T-CRACK at p=5: `54 + 3 + 2 = 59` ✓; at p=3: `47 + 6 + 1 = 54` ✓ — **both breakdowns sum to their member counts**, and both exhibit **three** distinct σ. T-NAIVEHE6A: `57/59` and `53/54` refutations — the complements are `2` and `1`, exactly the `{(2,2),(2,2)}` counts of T-CRACK ✓ (the planted dictionary is right only where the true σ happens to be `{(2,2),(2,2)}`) — **an internal consistency the note does not point out, verified here**. T-BASIS: `v(Res) = 4·dv₂ = 4·5 = 20` ✓.

**CONDITIONALITY.** **T-CRACK is the widening's non-vacuity certificate** — the exact analogue of HE6-T-CASEB (`spec/EFF-HE6.md` `.37`) for the other branch, and the note says so. **T-TWIST0 is a contrastive tooth**: it certifies that a mechanism which is load-bearing at HE7's `ℓ ≥ 2` (HE7-T-BADTWIST mispredicts σ on 21 reads) is *absent* at `ℓ = 1`. Recorded because a contrastive tooth is a rarer instrument than a confirming one.

**XREF.** none.

---

### EFF.HE6R1.30  [scope-record]

**CANONICAL STATEMENT** (verbatim, L680–691). FORM: bold-headed paragraph.

> “**What the machine leg establishes** (instrument grade, not acceptance): that
> the ℓ = 1 / d_r = 2 branch of the widened box is genuinely undecided by the
> outer data (three σ per row of identical outer data) and that HE7's level-2
> read — specialized exactly as §S3.1 says — decides it against an independent
> oracle on 677 of 682 octics with **zero mis-decisions**, the remaining 5
> being the Ψ | f_S stratum that FINDING HE6R1-F2 names and LEMMA HE6R1-3
> closes (12/12, 5/5 PARI); that (SLOT₂)'s exactness holds on 1,512 instances
> in the frame where only the residue-direction mechanism is available; that
> (LIFT₂)'s threshold is exactly the closed form at **d_r ≥ 2**, the coverage
> HE7-BOX-2 declared unexercised; and that the K₂-basis hypothesis is
> load-bearing rather than decorative.”

**DERIVATION.** [RECORD of the leg's itemized reach].

**⚠ SUPERSEDED (one clause).** “(LIFT₂)'s threshold is **exactly** the closed form at d_r ≥ 2” is **SUPERSEDED by A4 finding 4** (`.46`): the leg verifies the closed form as **sufficient, not sharp**, and the exercised frames show it **non-sharp by one**. **SUPERSESSION KIND:** `scope-pin`. **The other four items in the list are current** and each is independently reconstructed above.

**CONDITIONALITY.** “instrument grade, not acceptance” — the same refusal HE6's §S9 makes.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE7-BOX-2`, count 1.

---

### EFF.HE6R1.31  [record]

**CANONICAL STATEMENT** (verbatim, L685–692 — THE COMPLETION STATEMENT). FORM: `###`-headed section with a blockquoted display.

> “All four charges landed and (3) is PROVED, so the statement is displayed —
> with its two attached qualifications, which are part of it:
>
> > **THE MATHEMATICS OF THE UNIFORMITY PROGRAM IS COMPOSED-COMPLETE — every
> > named box in the theorem chain W-12.D ∘ GENIND.B ∘ GENHN.B ∘ HE6.A(r1) ∘
> > HE7.A is closed at composition grade; the remaining bar is hostile-arc
> > verification + the named hardening/coverage boxes + the Codex ratification
> > sweep.**”

**DERIVATION.** [RECORD of a program-level status claim] — **the most consequential single sentence in this note, and the one A4 finding 2 attacks.**

**CONDITIONALITY.** The note itself insists the two qualifications “are part of it” (`.32`). **A4 finding 2 (`.44`) shows qualification (ii) is not honest as written**: it names `GENHN-ERR-1` and simultaneously asserts the consumed boxes are “none of them an open piece of mathematics”, while `GENHN-ERR-1` is precisely an unsettled mathematical check. **REAL but OBSTRUCTED** — no admissible repair, since qualifying the statement would weaken an accepted display. **Closed at HEAD by a scheduled proof unit that has since LANDED** (`.48`, §5.2): SOL ledger row 15 — “GENHN-ERR-1 settled by LEMMA GENHN-COUNT-RERUN”.

**Compiler note.** A chapter cut quoting the completion statement **must** carry `.32`'s two qualifications, `.44`'s obstruction record, and `.48`'s routing — and may now also carry the ledger's settlement. Quoting the display alone would be the exact over-read the note's own qualifications exist to prevent.

**XREF.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — row 15.

---

### EFF.HE6R1.32  [scope-record]

**CANONICAL STATEMENT** (verbatim, L694–706). FORM: bold-headed paragraph, two numbered qualifications.

> “**The two qualifications, stated so the sentence is not read larger than it
> is.** (i) "Closed at composition grade" means: no step of the σ-decision
> chain is an open mathematical problem, and every step is proved in a note at
> attempt grade 0/2 (HE6 post-r1, HE7 with FINDINGS HE6R1-F1/F2 applied, GENHN
> post-r1 erratum, this note) except HE3 at 1/2 for μ ≤ 3; acceptance requires
> the hostile arcs, and this round ADDED three new statements (LEMMA HE6R1-1,
> HE6R1-2, HE6R1-3) and two errata that have never been attacked. (ii) The
> composition consumes, beyond HE6/HE7, the named boxes carried by W-12.D,
> GENIND.B and GENHN.B at their own grades (including GENHN-ERR-1 from R9), and
> the machine coverage boxes of §S5 — none of them an open piece of
> mathematics, all of them unverified-by-a-hostile-pass.”

**DERIVATION.** [RECORD of two scope qualifications].

**CONDITIONALITY — both qualifications move.** (i)'s “except HE3 at 1/2 for μ ≤ 3” is **corrected by PE3 F-2** (`.40`) to “HE3 at 0/2 (r2 owed)” — and PE3 F-2 flags it as **“the one stale-grade site whose direction is NOT conservative”**, i.e. the only place the note *overstates* a dependency. (ii)'s “none of them an open piece of mathematics” is the clause **A4 finding 2 falsifies** (`.44`). **Both qualifications, written to prevent over-reading, themselves needed correction** — recorded because it is the note's own most instructive irony and a chapter cut must carry the corrected forms.

**A durable observation.** Qualification (i)'s closing clause — “this round ADDED three new statements … and two errata **that have never been attacked**” — was true when written and is **no longer true**: PE2, PE3 and the sol A4 read have all attacked them, and A4 found `LEMMA HE6R1-1`'s display defective (`.43`). `STALE-SELF-DESCRIPTION`.

**XREF.** `HE3_PROOF_2026-08-08.md` — EXISTS ✓; `HE3_passPE2_report.md` @ `6d0ff09` ✓ (commit verified).

---

### EFF.HE6R1.33  [changes-record]

**CANONICAL STATEMENT** (verbatim, L710–720 — the micro-annex frame). FORM: `##`-headed dated append with an italic provenance paragraph.

> “## DATED MICRO-ANNEX (2026-08-09, post-PE2) — the four owed one-liners
>
> *Provenance.* This note's passPE2 (`HE6R1_passPE2_report.md` @
> 2118e59: CLEAN — 0 CRITICAL, 0 GAP, 4 MINOR; machine leg
> bit-identical in isolation; fresh non-prime-q route 487/487) started
> the 2-clean count: 0/2 → 1/2. The four owed MINOR one-liners land
> here as dated riders. Per the minors-only precedent (HE7's
> post-acceptance micro-annex ca3754d: owed MINOR cures land as riders
> without a grade event), **the count HOLDS at 1/2**; pass 2-of-2 (PE3)
> remains. Append-only: the pre-append file md5
> b43b798f229f5f68f35c41b37a072099 is the prefix.”

**DERIVATION.** [RECORD]. **SERIES membership:** ARC SERIES member 3 (after `.01` composition-era and `.20` BOX-1).

**PIN VERIFICATION.** `2118e59` and `ca3754d` are commits ✓; the prefix md5 **localizes uniquely to line 706** ✓. “machine leg bit-identical in isolation” and “fresh non-prime-q route 487/487” are decorrelation legs of the pass, reported not re-verified here.

**XREF.** `HE6R1_passPE2_report.md` — EXISTS ✓.

---

### EFF.HE6R1.34  [supplier-finding]

**CANONICAL STATEMENT** (verbatim, PE2 F-1, L722–729). FORM: bulleted dated rider.

> “- **PE2 F-1 (the HE7-side echo — cured at the owner's frozen copy).**
>   Frozen HE7's §S5.5 [r1] addition (b) parenthesis ("equal outright
>   when separable", HE7 L731) carries the clause PE1 F-3 falsified.
>   Cured this wave by HE7's dated line (commit 263cef0, "HE7 dated
>   line (S5.5 scalar clause)"), which states the corrected per-side
>   K₂^×-scalar reading with the scale-invariant-consumer check. No
>   text of this note moves for F-1.”

**DERIVATION.** [RECORD of an outbound cure]. **TYPE:** `supplier-finding` — a defect in HE7 discharged at HE7.

**LANDING VERIFIED.** `263cef0` is a commit ✓. **“No text of this note moves for F-1”** — so this rider is purely a DAG edge, which is exactly why it must be inventoried.

**XREF.** `HE7_PROOF_2026-08-08.md` — EXISTS ✓ (L731 cited by the note; the cure is at HE7's own dated line).

---

### EFF.HE6R1.35  [changes-record]

**CANONICAL STATEMENT** (verbatim, PE2 F-2, L731–751). FORM: bulleted dated rider with a derivation and a display.

> “- **PE2 F-2 (the ℓ ≥ 2 scalar identification gains the cocycle
>   unit).** LEMMA HE6R1-2(c)'s [r1′] clause identifies the scalar as
>   γ_g, g's level-2 residue. Re-derived at general ℓ: at a side λ₂ the
>   residues multiply along f = f_S·g after division by the height
>   normalizers, and n₂ composes only up to the cocycle —
>   n₂(h_{F₂,f_S}(λ₂))·n₂(c_g) = τ₂(h_{F₂,f_S}(λ₂), c_g)·n₂(h_{F₂,f}(λ₂)),
>   with h_{F₂,f}(λ₂) = h_{F₂,f_S}(λ₂) + c_g by (b) and the heights in
>   ℤ (dv₂ ℤ-valued). By HE7's ANNEX-LEMMA R1-a(iv),
>   τ₂(a,b) = Λ₁^{c₁(a,b)} with c₁(a,b) = (s(a)+s(b)−s(a+b))/ℓ ∈ {0,1},
>   and by R1-a(iii) its residue at a level-2 point is the transport of
>   the FIXED unit β^{c₁} ∈ K₂^×. Pointwise at the (c)-proof's test
>   points, converted to a polynomial identity by the same
>   generic-letter degree argument, the corrected identification per
>   side λ₂ is
>
>       R^f_{λ₂} = γ_g · β^{c₁(h_{F₂,f_S}(λ₂), c_g)} · R^{f_S}_{λ₂} ,
>
>   a fixed nonzero element of K₂^× per side, with the exponent c₁ free
>   to differ side by side. At ℓ = 1 — the branch this note decides and
>   its battery runs — s(·) ≡ 0 (§S3.1 table), the cocycle is trivial,
>   and the scalar is γ_g alone: the [r1′] clause is exact there. The
>   clause's consumed content — a fixed K₂^× scalar per side, nonzero,
>   consumers scale-invariant — survives the correction unchanged.”

**DERIVATION.** The span is the derivation: a cocycle composition using HE7's ANNEX-LEMMA R1-a(iii)/(iv), converted from pointwise to polynomial by a generic-letter degree argument.

**SUPERSESSION KIND:** `wording-rider` at ℓ = 1 (where nothing changes) and `replacement` at general ℓ (where the scalar gains a factor). **Layer 2 of C-5.**

**CONDITIONALITY.** **The correction is vacuous exactly on the branch the note decides** (`ℓ = 1`, `s(·) ≡ 0`, `c₁ ≡ 0`), and bites only at general `ℓ` — i.e. on `LEMMA HE6R1-2`'s statement as written for all `ℓ`, which is `.13`'s proof-only configuration. **Consumed content unchanged** (a fixed nonzero `K₂^×` scalar per side; consumers scale-invariant).

**XREF.** `HE7_PROOF_2026-08-08.md` — `ANNEX-LEMMA R1-a`, count 6.

---

### EFF.HE6R1.36  [changes-record]

**CANONICAL STATEMENT** (verbatim, PE2 F-3, L753–773). FORM: bulleted dated rider re-dating six supplier grades.

> “- **PE2 F-3 (the stale cross-grades in HE6R1-BOX-1 — re-dated).** The
>   box's sentences "HE7 is 0/2 and now carries FINDING HE6R1-F1" and
>   the minimum list "{GENHN 0/2, HE6 0/2, HE7 0/2, HE3 1/2 at μ ≤ 3,
>   GENIND 0/2, W-12 0/2}" read as-of the seal era. Re-dated at this
>   append: HE7 ACCEPTED 2/2 with its annex stack accepted, FULLY
>   FROZEN (FINDING HE6R1-F1 applied — HE7 micro-annex ca3754d); HE6
>   ACCEPTED 2/2 (PE4 CLEAN, 7ca97c9); GENHN ACCEPTED 2/2 (PE4 CLEAN,
>   6053c3d); GENIND ACCEPTED 2/2 (PE8), carrying its post-acceptance
>   Codex-CHALLENGE ANNEX R at the annex's own unpassed grade; W-12
>   ACCEPTED 2/2 (d76b785, dated re-anchor 2fcbd0c); HE3 0/2 (its [r1]
>   corrected the old 1/2 down; PE2 6d0ff09 left 2 GAP, r2 owed); this
>   note 1/2. Direction as PE2 noted: the stale sentences UNDERSTATE
>   the named grades (conservative), and the box's inherited minimum
>   keeps the value 0/2 — now keyed to HE3's 0/2 rather than to the
>   accepted notes (legs routed through this note price at its 1/2).
>   Same-genus re-date one row up: the R3 row's parenthesis "(an
>   HE7-side residue, noted here)" about HE7's fold-box "verbatim"
>   sentence predates HE7's dated line db0001a ("fold-box as-of
>   scoping"), which scoped that sentence as-of the r1 landing — the
>   residue is addressed at the owner.”

**DERIVATION.** [RECORD of a six-way grade re-dating] with a **direction analysis** — the key move.

**SUPERSESSION KIND:** `as-of scoping`. **TARGETS:** `.20` (HE6R1-BOX-1).

**PIN VERIFICATION — all six re-dated grades' commits.** `ca3754d` (HE7 micro-annex) ✓, `7ca97c9` (HE6 PE4) ✓ — **and cross-confirmed**: `spec/EFF-HE6.md` `.54` independently verifies `7ca97c9` as HE6's passPE4 commit and HE6's acceptance at 2/2 ✓. `6053c3d` (GENHN PE4) ✓, `d76b785` and `2fcbd0c` (W-12) ✓, `6d0ff09` (HE3 PE2) ✓. **Six of six.**

**CONDITIONALITY — the direction analysis is the load-bearing part.** “the stale sentences UNDERSTATE the named grades (conservative), and the box's inherited minimum keeps the value 0/2 — **now keyed to HE3's 0/2 rather than to the accepted notes**”. So the *value* of the minimum is unchanged but its *binding constraint* moves from a diffuse set to a single note. **A consumer needs the new key, not just the value** — recorded because the two are easy to conflate.

**XREF.** all six commits verified; `HE3_PROOF_2026-08-08.md`, `GENHN_PROOF_2026-08-08.md`, `GENIND_PROOF_2026-08-08.md`, `W12_PROOF_2026-08-08.md`, `HE7_PROOF_2026-08-08.md`, `HE6_PROOF_2026-08-08.md` — all EXIST ✓.

---

### EFF.HE6R1.37  [convention]

**CANONICAL STATEMENT** (verbatim, PE2 F-4, L775–786). FORM: bulleted dated rider.

> “- **PE2 F-4 (the tag convention made precise).** The [r1′] header's
>   convention sentence describes the unqualified uses; the precise
>   form: a plain **[r1]** or **[r2]** with no attached file qualifier
>   names, respectively, the HE6-side repairs of §S1 and the
>   HE6-PE2-era row updates of this note; a tag carried by an explicit
>   cross-note qualifier resolves to the named note's round. Cross-note
>   occurrences found by grep at this append, enumerated: L78 ("APPLIED
>   to GENHN as a dated [r1] ERRATUM annex" — GENHN's r1); L237 ("HE7's
>   later [r2] round") and L241 ("frozen HE7 §S5.8 [r2]") — HE7's r2;
>   L432 ("§S1 CONVENTION [r1]" under "HE7's frozen HEAD" — HE7's r1).
>   The primed tag [r1′] is this round's own; no colliding use was
>   found by grep.”

**DERIVATION.** [RECORD of a resolution convention] with an **exhaustive grep-enumerated site list** — four cross-note occurrences at named lines.

**CONDITIONALITY.** **This unit is a resolution rule for the whole note** and is applied by this compilation (§1 resolution rule 1). Its enumeration is what makes the rule checkable rather than a promise: four sites, each with a line number and a resolution.

**Compiler note.** A tag-resolution convention with an exhaustive site enumeration is the right shape for a note that carries repair tags from **four** different sources (its own `[r1′]`, HE6's `[r1]`/`[r2]`, HE7's `[r1]`/`[r2]`, GENHN's `[r1]`). Recorded as reusable practice.

**XREF.** none (all four sites are note-internal line addresses).

---

### EFF.HE6R1.38  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L790–803). FORM: `###`-headed dated append with an italic acceptance line.

> “*Acceptance line.* This note's passPE2 (`HE6R1_passPE2_report.md` @
> 2118e59: CLEAN — 0 CRITICAL, 0 GAP, 4 MINOR) and passPE3
> (`HE6R1_passPE3_report.md` @ 9aa0cc6: CLEAN — 0 CRITICAL, 0 GAP,
> 3 MINOR; machine leg bit-identical in isolation; fresh ℓ₂ = 3 /
> two-sided-polygon route 246/246 on both PARI oracles, first wild
> corner p = 3, e = 6) complete the 2-clean count 1/2 → 2/2.
> **HE6R1 is ACCEPTED (2/2) and FROZEN — the body and annex above are
> not edited; dated appends only.** The three PE3 MINOR one-liners land
> here as dated riders (minors-only precedent, HE7 ca3754d: riders
> without a grade event). Append-only: the pre-append file md5
> 2c44fd2efd89295d33c36def3af84347 is the prefix.”

**DERIVATION.** [RECORD of an acceptance]. **SERIES membership:** ARC SERIES member 4 — **TERMINAL for the counter**.

**SUPERSESSION KIND:** `replacement` of every prior grade statement. **TARGETS:** `.20` (HE6R1-BOX-1), `.32` (qualification (i)).

**PIN VERIFICATION.** `2118e59`, `9aa0cc6`, `ca3754d` all commits ✓; **the prefix md5 localizes uniquely to line 786** ✓ — and since 786 > 706, **the second pin certifies that the micro-annex was itself untouched by this append** ✓, a nested-freeze property worth naming.

**CONDITIONALITY — PE3's decorrelation leg is the strongest in the note.** “fresh **ℓ₂ = 3 / two-sided-polygon** route 246/246 on **both** PARI oracles, **first wild corner p = 3, e = 6**”. **This reaches configurations the sealed battery cannot** (the battery runs `ℓ₂` implicit at a single-sided level-2 polygon, `μ₂ = 2`); PE3's route runs a two-sided polygon at `ℓ₂ = 3` and a wild corner. Recorded because it partially offsets HE6R1-BOX-2's coverage holes — though not the `μ ≥ 5` proper-block hole, which stays proof-only.

**XREF.** `HE6R1_passPE3_report.md` — EXISTS ✓.

---

### EFF.HE6R1.39  [changes-record]

**CANONICAL STATEMENT** (verbatim, PE3 F-1, L805–834). FORM: bulleted dated rider with a corrected display.

> “- **PE3 F-1 (the cocycle exponent's argument is the PIN height m₁,
>   not the side's line value).** The PE2 F-2 rider above — and its
>   same-wave HE7-side copy (HE7 dated line 263cef0) — writes the
>   corrected per-side scalar with exponent
>   c₁(h_{F₂,f_S}(λ₂), c_g), the side's LINE VALUE. Off the first side
>   of a multi-side level-2 polygon at ℓ₂ ≥ 2 that value need not lie
>   in ℤ: h(λ₂) = m₁ + j₁λ₂ ∈ ℤ requires ℓ₂ | j₁ (e.g. pins (3,0),
>   (1,13), (0,21) — PE3's own fresh-route TS geometry — give the
>   13/2-side h = 39/2 ∉ ℤ), while s(·) and hence c₁ are defined on ℤ
>   (ANNEX-LEMMA R1-a: a, b, k ∈ ℤ) — the display is ill-formed there.
>   Corrected derivation, per the PE3 report's mechanism: normalize
>   each side by n₂(m₁)·Ψ(ξ)^{j₁} — the normalization HE7-7′(b)'s own
>   proof uses — where m₁ := dv₂(A^{(2)}_{j₁}) is the PIN height at the
>   side's starting index j₁, an integer; the Ψ(ξ)^{j₁} factor is
>   COMMON to f and f_S (same sides by (b)) and CANCELS in the ratio;
>   the vertex pins shift by c_g (m₁^f = m₁^{f_S} + c_g); the cocycle
>   composition then runs entirely over ℤ, and the corrected per-side
>   identification is
>
>       R^f_{λ₂} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R^{f_S}_{λ₂} ,
>
>   with the exponent the **pin height** c₁(m₁^{f_S}, c_g). Scope of
>   the line-value form: it agrees with the pin-height form exactly
>   when j₁ = 0 (a single-side level-2 polygon, or the first side), and
>   at ℓ = 1 — the branch this note decides and its battery runs —
>   s(·) ≡ 0 makes c₁ ≡ 0 and the scalar is γ_g alone, so the rider's
>   ℓ = 1 statements stand as written. The consumed content (a FIXED
>   nonzero K₂^× scalar per side; consumers scale-invariant) is
>   unchanged by the correction; PE3's blast-radius check found no
>   consumer of the exponent at HEAD. The HE7-side copy carries the
>   same wrinkle; its cure is HE7's same-wave dated line ("cocycle
>   argument"), landed with this record.”

**DERIVATION.** A well-formedness argument (`c₁` is defined on ℤ; the line value need not be an integer off the first side) plus a corrected normalization.

**Mathematical audit — the ill-formedness witness re-derived.** `h(λ₂) = m₁ + j₁λ₂`; with the pins `(3,0), (1,13), (0,21)` the side from `(3,0)` to `(1,13)` has slope `13/2`, so `ℓ₂ = 2`; at `j₁ = 1`, `h = 13 + 1·(13/2)`… taking the note's own reading `h = 39/2` ✓ requires `m₁ + j₁λ₂` with `m₁ = 13`, `j₁ = 1`, `λ₂ = 13/2` → `13 + 13/2 = 39/2` ✓ **exactly**, and `39/2 ∉ ℤ` ✓. The integrality condition `ℓ₂ | j₁` ✓ (`2 ∤ 1`). **The witness is exact and the defect is real.**

**SUPERSESSION KIND:** `replacement` (the exponent's argument). **Layer 3 of C-5 — TERMINAL.** **TARGETS:** `.35` and, cross-note, HE7's own dated line `263cef0` — whose cure “landed with this record”.

**CONDITIONALITY.** **Vacuous at ℓ = 1** (the branch decided here), agrees with the superseded form when `j₁ = 0`, and “PE3's blast-radius check found no consumer of the exponent at HEAD”. **A three-layer chain on a clause with no consumers** — recorded because that is precisely why it survived two rounds.

**XREF.** `HE7_PROOF_2026-08-08.md` — `ANNEX-LEMMA R1-a`, count 6; commit `263cef0` ✓.

---

### EFF.HE6R1.40  [changes-record]

**CANONICAL STATEMENT** (verbatim, PE3 F-2, L836–848). FORM: bulleted dated rider.

> “- **PE3 F-2 (the §S6 completion statement's "except HE3 at 1/2 for
>   μ ≤ 3" — corrected to HE3 at 0/2).** The completion statement's
>   qualification (i) reads "… except HE3 at 1/2 for μ ≤ 3", the
>   seal-era grade. At HEAD HE3 is 0/2: its [r1] corrected the old 1/2
>   down, and `HE3_passPE2_report.md` @ 6d0ff09 left 2 GAP with r2
>   owed. This is the one stale-grade site whose direction is NOT
>   conservative — it overstates a dependency's grade. Corrected
>   reading of qualification (i): "… except HE3 at 0/2 for μ ≤ 3
>   (r2 owed)". The authoritative grade box (HE6R1-BOX-1 with the PE2
>   F-3 rider above) already carries the corrected minimum keyed to
>   HE3's 0/2; this rider re-dates the §S6 prose to match it.”

**DERIVATION.** [RECORD of a grade correction] — **with a direction judgement that makes it substantive**: “the one stale-grade site whose direction is NOT conservative — it **overstates** a dependency's grade.”

**SUPERSESSION KIND:** `replacement`. **TARGETS:** `.32` qualification (i).

**CONDITIONALITY.** **This is the discriminating rule for stale grades**, and it is worth carrying corpus-wide: a stale grade that *understates* a supplier is conservative and harmless; one that *overstates* is a defect. **Of the many stale-grade sites this queue has compiled, this is the only one flagged as non-conservative** — and the note flags it itself. **PIN VERIFIED:** `6d0ff09` is a commit ✓.

**XREF.** `HE3_PROOF_2026-08-08.md` — EXISTS ✓.

---

### EFF.HE6R1.41  [changes-record]

**CANONICAL STATEMENT** (verbatim, PE3 F-3, L850–862). FORM: bulleted dated rider.

> “- **PE3 F-3 (the cross-report finding numbers — file-qualified).**
>   The R3 row's [r2] block cites "(PE2 F-4: …)" and "(PE2 F-1)"
>   meaning `HE6_passPE2_report.md`'s findings (F-4 = the five cosmetic
>   byte-diffs; F-1 = the η_θ^{−q(k)} coset omission) — written before
>   this note had a passPE2 of its own, whose report also numbers an
>   F-1 and an F-4, so the bare references acquired a second candidate
>   referent after the fact. Disambiguation, extending the PE2 F-4
>   rider's convention to pass-report references: a bare "PE2 F-n" in
>   the R3 row resolves to `HE6_passPE2_report.md`; a reference to this
>   note's own pass reports carries an explicit qualifier ("this note's
>   PE2/PE3", as in this record). PE3 names the R3 row as the colliding
>   site; this rider file-qualifies it.”

**DERIVATION.** [RECORD of a reference disambiguation].

**CONDITIONALITY.** **A reference collision created by the passage of time** — the R3 row's citations were unambiguous when written and acquired a second referent when this note gained its own PE2. **The cure extends `.37`'s tag convention to pass-report references**, so the note now carries one resolution rule covering both tags and finding numbers. **Cross-check:** the identified referents are correct — `HE6_passPE2_report.md`'s F-1 *is* the `η_θ^{−q(k)}` coset omission, independently compiled at `spec/EFF-HE6.md` `.03` and `.13` ✓.

**XREF.** `HE6_passPE2_report.md` — EXISTS ✓; `HE6R1_passPE2_report.md` — EXISTS ✓.

---

### EFF.HE6R1.42  [changes-record]

**CANONICAL STATEMENT** (verbatim, L864–875 — the A4 frame). FORM: `###`-headed dated append.

> “### Dated adjudication + corrections (2026-08-12 — sol certification A4: the R7 chain challenge adjudicated at HEAD)
>
> The sol-5.6 chain read of this note (gpt-5.6-sol high,
> runs/residues/R7_he6r1_output.log, 2026-08-12) returned CHALLENGE
> with four findings. The A4 certification run (gpt-5.6-sol high,
> runs/cert/A4_he6r1_output.log) re-adjudicated all four against HEAD
> including every dated append: findings 3 and 4 are REAL with derived
> repairs — the two dated corrections below; **findings 1 and 2 are REAL
> but OBSTRUCTED — every honest repair weakens an accepted statement
> display, so no admissible repair exists**; the two dated obstruction
> records below transcribe the A4 adjudications verbatim. Everything
> above this heading is byte-untouched by this append.”

**DERIVATION.** [RECORD of an adjudication with a **novel disposition**].

**AUDIT disposition (rule 27).** `decorrelated-model audit`. **All four findings REAL — and two of them ADMIT NO REPAIR.** This is the only OBSTRUCTED disposition in queue 8b, and it is a genuine third category: not “no defect”, not “defect repaired”, but “**defect real, every repair inadmissible**”. The inadmissibility criterion is stated: “every honest repair weakens an accepted statement display”.

**Compiler note on why the category is needed.** Under the repo's honesty invariant, a note that is ACCEPTED cannot have its displayed statements weakened by a dated append. So a defect discovered *after* acceptance that can only be cured by weakening a display has no in-note remedy. **The corpus's answer — visible at `.47`/`.48` — is to route such findings to an authority (an owner directive) or to new mathematics (a scheduled proof unit), never to a silent qualification.** Recorded as the governing precedent.

**PIN VERIFICATION.** `runs/residues/R7_he6r1_output.log` EXISTS ✓; `runs/cert/A4_he6r1_output.log` EXISTS ✓.

**XREF.** artifacts as above.

---

### EFF.HE6R1.43  [changes-record]

**CANONICAL STATEMENT** (verbatim, L877–880 — the first obstruction record's operative line, plus the A4 diagnosis quoted from the provenance note). FORM: `###`-headed dated record.

> “### Dated obstruction record (2026-08-12, R7 finding 1 — LEMMA HE6R1-1's global jump bound; the A4 adjudication transcribed verbatim)
>
> The defect stands. No dated append cures it.”

with the A4 diagnosis (verbatim, from the provenance paragraph L1000–1010):

> “finding 1: HE6R1-1's proof re-read: it derives
> J ≤ log₂μ − 1 (4 ≤ μ/2^{J−1}), and the appended "≤ log₂n − 2"
> requires μ ≤ n/2, i.e. a stage start D′ ≥ 2; the lemma's own
> quantifier ("At ANY level i, a node requires a level jump exactly
> when its side carries a repeated irreducible residual factor with
> ℓ_i·deg r_i ≥ 2") admits ambient-level nodes (D′ = 1), where a
> quartic with residual r², r irreducible quadratic (m = 2, ℓ = 1,
> d_r = 2, side length 4) is a jump at n = μ = 4 — so the display's
> global bound J ≤ log₂4 − 2 = 0 is contradicted by J = 1.”

**DERIVATION.** [RECORD of an obstructed finding] with an explicit counterexample.

**Mathematical audit — the counterexample is exact.** At `D′ = 1` (ambient), `n = μ = 4`; residual `r²` with `r` irreducible quadratic gives `m = 2`, `ℓ = 1`, `d_r = 2`, so `ℓd_r = 2 ≥ 2` — **a jump by the lemma's own criterion** ✓ — and side length `L = m·ℓ·d_r = 4 = μ` ✓. So `J ≥ 1`, while the frozen global bound gives `J ≤ log₂4 − 2 = 0` ✓ **contradiction**. And the lemma's quantifier really does admit ambient nodes: “**At ANY level i**” ✓. **The finding is right, the diagnosis is right, and the counterexample is minimal.**

**CONDITIONALITY.** “The defect stands. No dated append cures it.” — **and this compilation confirms the obstruction's reasoning**: any in-note fix either restricts the lemma's quantifier (weakening an accepted display) or weakens the bound (likewise). **Closed only at `.47`, by owner authority.**

**XREF.** `runs/cert/A4_he6r1_output.log` — EXISTS ✓.

---

### EFF.HE6R1.44  [changes-record]

**CANONICAL STATEMENT** (verbatim, L910–926 — the second obstruction record). FORM: `###`-headed dated record with a quoted box and LaTeX.

> “### Dated obstruction record (2026-08-12, R7 finding 2 — the completion statement vs GENHN-ERR-1; the A4 adjudication transcribed verbatim)
>
> The defect stands and is expressly admitted at HEAD by:
>
> > **GENHN-ERR-1 (the R9 residue).** Whether GENHN’s \(f_1\ge2\) count-side displays … need re-reading with \(D'h=f_1S\) is NOT settled here.
>
> Neither the “DATED MICRO-ANNEX (2026-08-09, post-PE2)” nor the “Dated acceptance record + corrections (2026-08-09, post-PE3)” resolves that mathematical residue. PE2 F-3 merely re-dates GENHN’s grade.
>
> R9 proves that the correct node is
>
> \[
> dv(A_j)\ge(\mu-j)D'h+1.
> \]
>
> For \(f_1=2\) and \(\mu-j=1\), this is \(dv(A_j)\ge2S+1\), genuinely different from \(dv(A_j)\ge S+1\). Nothing in this note proves that GENHN’s count remains valid after that change.
>
> Repairing the completion statement without weakening it requires a new lemma re-running GENHN’s \(f_1\ge2\) count argument on the corrected region. The requisite count-side displays and argument are absent from this note; indeed, the note explicitly records that check as unsettled. Alternatively, qualifying the composition-complete theorem by GENHN-ERR-1 would weaken an accepted displayed theorem, which is forbidden. Therefore no honest repair can be derived from the supplied note alone.”

**DERIVATION.** [RECORD of an obstructed finding] with a quantified gap.

**Mathematical audit.** At `f₁ = 2` and `μ − j = 1`: the corrected node gives `dv(A_j) ≥ D′h = f₁S = 2S`, plus 1, i.e. `≥ 2S+1`; the old displayed form gives `≥ S+1` ✓ — **genuinely different, by `S`** ✓. And the note's own `GENHN-ERR-1` (`.20`) admits the count-side check is unsettled ✓. **The obstruction's premise is verified on both sides.**

**CONDITIONALITY.** The two named exits are (i) a new lemma re-running GENHN's `f₁ ≥ 2` count on the corrected region, or (ii) qualifying the completion statement — **forbidden**, as it weakens an accepted display. **Exit (i) was taken** (`.48`) **and has LANDED**: SOL ledger row 15 — “GENHN-ERR-1 settled by **LEMMA GENHN-COUNT-RERUN** (certificate confirmed; transcription confirmed at TC2)” ✓ (§5.2).

**XREF.** `spec/HYPOTHESIS_LEDGER.md` — `GENHN-ERR-1`, count 4. `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — row 15.

---

### EFF.HE6R1.45  [changes-record]

**CANONICAL STATEMENT** (verbatim, L928–968 — A4 finding 3). FORM: `###`-headed dated correction with LaTeX displays.

> “### Dated challenge correction (2026-08-12) — the Φ′ line may have zero coefficients
>
> The R4 description’s sentence
>
> > “Φ′’s own slots have \(e_1v(a_i)+ih\ge D'h\) with equality exactly at
> > \(i=e_1t\)”
>
> is corrected as follows: every slot satisfies
> \[
> e_1v(a_i)+ih\ge D'h,
> \]
> and equality can occur only at an index \(i=e_1t\), \(0\le t\le f_1\);
> it need not occur at every such index. … For \(i=e_1t\), the slot inequality gives
> \[
> v(a_{e_1t})\ge(f_1-t)h.
> \]
> Hence
> \[
> \bar a_t:=
> \operatorname{res}\!\left(
> a_{e_1t}\pi^{-(f_1-t)h}
> \right)
> \]
> is defined and is zero whenever \(a_{e_1t}=0\) or the inequality is
> strict. By the definition of the residual polynomial,
> \[
> \psi(Z)=\sum_{t=0}^{f_1}\bar a_t Z^t.
> \]
> Therefore the attaining-term residue sum at a (T2) point is still
> \[
> \sum_{t=0}^{f_1}\bar a_t\eta_\xi^t
> =\psi(\eta_\xi)=0.
> \]
> Thus the ψ-cancellation proof and its conclusions are unchanged; only the
> false assertion that every index \(e_1t\) attains equality is withdrawn.”

**DERIVATION.** The span is the derivation: a divisibility scoping plus a normalized-coefficient display that self-corrects for above-the-line slots.

**⚠ CROSS-NOTE IDENTITY — this is the SAME correction as HE6's A3 F-3.** `spec/EFF-HE6.md` `.60` compiles HE6's own A3 F-3, which corrects the identical sentence in HE6 §S3.1 (“with equality exactly at the slots i = e₁t” → “with equality possible only at”). **The A4 provenance note says so**: “identical mathematics to HE6's own F-3 correction folded at A3, **mutually consistent**”. **Two notes, one sentence, two independently derived corrections landing the same day** — and this compilation independently verified both (`spec/EFF-HE6.md` `.60` and here). **A strong decorrelation datum.**

**Mathematical audit.** `e₁v(a_i) + ih = D′h ⟹ e₁ | (D′−i)h ⟹ e₁ | i` ✓ (as at `spec/EFF-HE6.md` `.22`). The normalized coefficient `ā_t = res(a_{e₁t}π^{−(f₁−t)h})` is defined because `v(a_{e₁t}) ≥ (f₁−t)h` ✓, and is zero when the pin is strictly above the line ✓ — so `ψ(Z) = Σ ā_t Z^t` is correct with the zero terms included ✓.

**SUPERSESSION KIND:** `wording-rider`. **TARGETS:** the R4 row of `.03`.

**XREF.** `runs/cert/A4_he6r1_output.log` — EXISTS ✓.

---

### EFF.HE6R1.46  [changes-record]

**CANONICAL STATEMENT** (verbatim, L972–996 — A4 finding 4). FORM: `###`-headed dated correction with a blockquoted replacement.

> “### Dated challenge correction (2026-08-12) — scope of the LIFT₂ machine result
>
> The §S6 sentence saying that the machine leg establishes that
> “(LIFT₂)’s threshold is exactly the closed form at \(d_r\ge2\)” is
> corrected to the following:
>
> > The machine leg verifies the closed-form (LIFT₂) bound as a sufficient
> > bound in the exercised \(d_r=2\) frames, but does not establish it as
> > sharp. In every displayed frame the exhaustive onset of surjectivity is
> > \(k=\lambda\), whereas the closed-form sufficient bound is
> > \[
> > (d_r-1)u+(D'-1)h=\lambda+1.
> > \]
> > Thus \(k=\lambda\) is an explicit attained height below the closed-form
> > bound, proving that the bound is non-sharp by one in these frames. No
> > claim of an exact or generally sharp threshold for arbitrary
> > \(d_r\ge2\) is made.
>
> This is precisely the distinction already recorded in P3: the theorem’s
> closed form is sufficient, while the experimentally exact onset in the
> tested frames is one lower.”

**DERIVATION.** A comparison of the §S6 prose against P3's own table.

**Mathematical audit.** Independently re-derived at `.27`: closed form `= λ+1` in all five frames ✓, observed onset `= λ` in all five ✓, **gap exactly 1 everywhere** ✓. **The correction restates P3's numbers exactly**, as the provenance note claims.

**SUPERSESSION KIND:** `scope-pin` — “exactly the closed form” → “sufficient, not sharp”. **TARGETS:** `.30`.

**CONDITIONALITY.** **The corrected claim is weaker and true; the frozen one was stronger and contradicted by the note's own table 60 lines earlier.** This is the note's **second internal contradiction** (after `.32`'s two qualifications needing correction), and like HE6's `.61` it survived every in-house pass and was caught by the decorrelated read. Recorded as a pattern now seen in three notes of this queue.

**XREF.** `runs/cert/A4_he6r1_output.log` — EXISTS ✓.

---

### EFF.HE6R1.47  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1031–1071 — the owner-directive re-display). FORM: `###`-headed dated section with a three-clause display.

> “### Dated statement re-display (2026-08-12 — R7 finding 1 closed under the owner's directive; finding 2 routed to a proof unit)
>
> Asvin (2026-08-12) delegated proof-related statement decisions under
> the end-to-end-proof criterion (the right display is the one the
> complete proof of the pinned main theorem consumes, stated simply).
> Under that authority, R7 finding 1 is closed by the re-display below
> (orchestrator-composed from the A4 obstruction record's own option
> text; consumer sites verified stage-rooted at HEAD; subject to sol
> discharge-confirmation in the cert2 pass). …
>
> **Dated statement re-display (2026-08-12, R7 finding 1 — LEMMA
> HE6R1-1's global bound).** The display "J ≤ log₂ μ − 1 ≤ log₂ n − 2"
> is re-displayed as the three clauses its proof supports:
>
> (a) in ANY history, J ≤ log₂ μ − 1, where μ is the multiplicity at
> the ladder's root — the proof's 4 ≤ μ_J ≤ μ/2^{J−1}, unchanged;
>
> (b) for ladders rooted at a COMPOSITE-STAGE opening (key degree
> D′ = e₁f₁ ≥ 2, hence μ ≤ n/D′ ≤ n/2): J ≤ log₂ n − 2 — the bound
> THEOREM HE7.C and every consumption site in this note cite; n = 8
> admits one jump (μ₂ ≤ 2) and n = 16 is the first degree admitting
> two, exactly as consumed;
>
> (c) for histories rooted at an AMBIENT node (D′ = 1, n = μ):
> J ≤ log₂ n − 1, and this is sharp — a quartic with level-0 residual
> r², r irreducible quadratic (m = 2, ℓ = 1, d_r = 2, side length 4)
> realizes J = 1 = log₂ 4 − 1 (the R7/A4 counterexample).
>
> The former unconditional "≤ log₂ n − 2" is withdrawn at
> ambient-rooted histories only. Consumer sweep at this fold: the §S4
> consumption line ("J ≤ log₂ n − 2; n = 8 has one jump at μ₂ ≤ 2;
> level 3 first possible at n = 16") and THEOREM HE7.C's bounds are
> stage-rooted (clause (b)) and unchanged; the descent/termination
> consumers (HE3.B's strict descent) do not read this display.”

**DERIVATION.** A three-way split of the frozen bound by the root's key degree, each clause carrying exactly what the proof supports.

**Mandatory arithmetic audit (rule 22) — all three clauses.** (a) `4 ≤ μ/2^{J−1} ⟹ J ≤ log₂μ − 1` ✓ (re-derived at `.09`). (b) `D′ ≥ 2 ⟹ μ ≤ n/2 ⟹ log₂μ − 1 ≤ log₂n − 2` ✓; `n = 8, D′ = 2 ⟹ μ ≤ 4 ⟹ J ≤ 1` ✓; two jumps need `log₂n − 2 ≥ 2`, i.e. `n ≥ 16` ✓. (c) `D′ = 1 ⟹ n = μ ⟹ J ≤ log₂n − 1` ✓, **and sharp**: the quartic realizes `J = 1 = log₂4 − 1` ✓. **All three clauses exact, and clause (c)'s sharpness witnessed.**

**SUPERSESSION KIND:** `scope-pin` — “The former unconditional ‘≤ log₂ n − 2’ is **withdrawn at ambient-rooted histories only**.” **CHAIN:** frozen display → A4 obstruction (`.43`) → this re-display. **TERMINAL.** **TARGETS:** `.09`, and by the consumer sweep `.17`(i) and `.18`'s consumption line.

**CONDITIONALITY — the authority is named and its criterion quoted.** “Asvin (2026-08-12) delegated proof-related statement decisions under the end-to-end-proof criterion (**the right display is the one the complete proof of the pinned main theorem consumes, stated simply**).” **This is the only statement change in queue 8b made under a named delegated authority rather than by a supplier finding or a run result.** It is also “subject to sol discharge-confirmation in the cert2 pass” — **and the confirmation landed**: SOL ledger row 15, “repairs + re-display discharged (D2d 3/3)” ✓ (§5.2).

**The consumer sweep is verified.** Every consumption site named — `.18`'s line and THEOREM HE7.C's bounds — is stage-rooted, hence clause (b), hence unchanged ✓; and `.17`(i)'s parenthetical likewise ✓.

**XREF.** `HE7_PROOF_2026-08-08.md` — `THEOREM HE7.C`, count 9. `HE3_PROOF_2026-08-08.md` — `COROLLARY HE3.B` cited descriptively.

---

### EFF.HE6R1.48  [scope-record]

**CANONICAL STATEMENT** (verbatim, L1039–1046 — the routing of R7 finding 2). FORM: paragraph inside the re-display section.

> “R7 finding 2 is NOT closed
> by re-display: under the same criterion "qualify the completion
> statement" loses to "prove the missing lemma" — the GENHN f₁ ≥ 2
> count re-run on the corrected node floor {dv(A_j) ≥ (μ−j)D′h + 1} is
> hereby a scheduled proof unit (numerical certification first, then
> the proof; it simultaneously settles GENHN-ERR-1 and restores the
> completion statement's "none of them an open piece of mathematics"
> clause with no wording change).”

**DERIVATION.** [RECORD of a routing decision] under the same delegated criterion as `.47`.

**CONDITIONALITY — and the unit has LANDED.** The scheduled unit is named by its content (“the GENHN f₁ ≥ 2 count re-run on the corrected node floor”) and its method (“numerical certification first, then the proof”). **At HEAD it exists and has discharged**: `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 15 reads

> “\| 15 \| HE6R1 \| CHALLENGE (fresh, R7) \| **CERTIFIED 2026-08-12** — repairs + re-display discharged (D2d 3/3); **GENHN-ERR-1 settled by LEMMA GENHN-COUNT-RERUN** (certificate confirmed; transcription confirmed at TC2) \|”

`grep -cF 'HE6R1' docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` = **1** ✓. **So the obstruction of `.44` is closed at HEAD by new mathematics, exactly as this routing specified**, and the completion statement's clause is restored “with no wording change”.

**Compiler note — the decisive precedent.** Two REAL-but-OBSTRUCTED findings, two different exits: **finding 1 by a re-display under delegated authority** (the display was wrong; the mathematics was not), **finding 2 by proving the missing lemma** (the mathematics was genuinely absent). **Neither was closed by qualifying a displayed theorem.** That is the pattern a chapter cut should carry forward.

**XREF.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — `HE6R1`, count 1 (row 15). `spec/HYPOTHESIS_LEDGER.md` — `GENHN-ERR-1`, count 4.

---

## 4. XREF verification ledger

### 4.1 HE7 designations (the errata's target)

`[TABLE]`

| # | designation | count in `HE7_PROOF_2026-08-08.md` | consumed at |
|---|---|---|---|
| X1 | `THEOREM HE7.A` | 32 | `.07`, `.08`, `.14`, `.15` |
| X2 | `THEOREM HE7.C` | 9 | `.08`, `.09`, `.17`, `.47` |
| X3 | `COROLLARY HE7.B` | 22 | `.12` |
| X4 | `LEMMA HE7-6` | 7 | `.12`, `.13` |
| X5 | `LEMMA HE7-8` | 17 | `.09`, `.10` |
| X6 | `HE7-BOX-2` | 1 | `.18`, `.27`, `.30` |
| X7 | `HE7-BOX-4` | 5 | `.12`, `.13`, `.21` |
| X8 | `COROLLARY HE7-7″` | 11 | `.07`, `.14` |
| X9 | `ANNEX-LEMMA R1-a` | 6 | `.06`, `.35`, `.39` |
| X10 | **`HE6R1-F1`** | **4** | `.08` — **erratum 1 LANDED** |
| X11 | **`HE6R1-F2`** | **8** | `.14` — **erratum 2 LANDED** |
| X12 | `HE6` | 209 | `.02` |

### 4.2 Other suppliers, consumers and ledgers

`[TABLE]`

| # | file | designation | count | consumed at |
|---|---|---|---|---|
| X13 | `GENHN_PROOF_2026-08-08.md` | `ERRATUM` | 17 | `.04` — **the R9 erratum LANDED** |
| X14 | `GENHN_PROOF_2026-08-08.md` | `LEMMA GENHN-1` | 4 | `.04` |
| X15 | `GENHN_PROOF_2026-08-08.md` | `LEMMA GENHN-2` | 2 | `.04` |
| X16 | `HE6_PROOF_2026-08-08.md` | `HE6-BOX-1` | 11 | `.05`, `.21` |
| X17 | `spec/HYPOTHESIS_LEDGER.md` | `GENHN-ERR-1` | 4 | `.04`, `.20`, `.44`, `.48` |
| X18 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | `HE6R1` | 1 (row 15) | `.20`, `.31`, `.44`, `.48` |

**No OPEN-CALL arises from any designation; zero NEAR-MISS.** Every cited name is grep-verified at count ≥ 1.

### 4.3 PIN VERIFICATION ledger (rule 23)

**Commit hashes — 11 cited, 11 verified** via `git cat-file -t` → `commit`: `4f5ebaa`, `2118e59`, `9aa0cc6`, `ca3754d`, `263cef0`, `db0001a`, `6053c3d`, `d76b785`, `2fcbd0c`, `6d0ff09`, `7ca97c9`. **Zero failures.**

**md5 pins — 6 cited, 6 verified.** Four **import** pins, all byte-exact: `he6_checks.py` `321fa4d4990eef67ff6a20f375c32366` ✓, `he7_checks.py` `688adbe88447b570104e379b1fa11cd5` ✓, `w12_checks.py` `7dc040d94fbbb1e8d20ac817b665d418` ✓, `w10_checks.py` `a9c34244a3af19f5fa864375b494380b` ✓. Two **nested prefix** pins, both localized to a unique line boundary: `b43b798f229f5f68f35c41b37a072099` → **line 706** ✓; `2c44fd2efd89295d33c36def3af84347` → **line 786** ✓.

**`UNPINNED-VALUE` — three.** The note's own artifacts (`he6r1_checks.py`, `…_output.txt`, `…_results.json`) are pinned by commit `4f5ebaa` and the disclosed `[r1-fix]`, not by md5. The three supplementary artifacts likewise. Recorded (`.22`), not silently passed.

**Artifacts — 12 cited, 12 exist:** `verification/openmath/{he6r1_checks.py, he6r1_checks_output.txt, he6r1_checks_results.json, he6r1_supp.py, he6r1_supp_output.txt, he6r1_supp_results.json, he7_checks.py}`, `lean/notes/openmath/{HE6R1_passPE1_report.md, HE6R1_passPE2_report.md, HE6R1_passPE3_report.md}`, `runs/residues/R7_he6r1_output.log`, `runs/cert/A4_he6r1_output.log`. **Zero missing.**

---

## 5. Consumption table and consumer edges

### 5.1 What HE6R1 consumes (forward edges)

`[TABLE]`

| supplier | object | consuming units | load-bearing? |
|---|---|---|---|
| HE7 | §S1–S6 in full, as a literal instance at ℓ = 1 | `.06`, `.07`, `.17` | YES — the reconciliation's whole content |
| HE7 | `LEMMA HE7-6` (the block factor), `LEMMA HE7-8` (α-refine finiteness) | `.10`, `.13` | YES |
| HE7 | `ANNEX-LEMMA R1-a`(iii)(iv) (the cocycle) | `.35`, `.39` | YES, at general ℓ |
| HE6 | `LEMMA HE6-1`, `LEMMA HE6-0′` | `.13`, `.16` | YES |
| HE6 | `LEMMA HE6-3(b)` ((SEP)-free slope counts) | `.10` | YES — the middle step of the descent |
| HE6 | `THEOREM HE6.A`, §S6.3 (HE3 stage-α) | `.10` | YES — the jump condition's complement |
| GENHN | GENHN-1's node display | `.04` | **NO — it is what R9 corrects** |
| HE6's sealed battery | rings, resultants, PARI bridge | `.18` | YES for the instrument |

### 5.2 Reverse-XREF rows — who consumes HE6R1 (rule 8)

`[TABLE]`

| # | consumer | designation | count | what is consumed | status |
|---|---|---|---|---|---|
| RX-1 | `HE7_PROOF_2026-08-08.md` | `HE6R1-F1` **4**, `HE6R1-F2` **8** | both errata | **LANDED** (micro-annex `ca3754d`; the HE7-side dated lines `263cef0`, `db0001a`) |
| RX-2 | `GENHN_PROOF_2026-08-08.md` | `ERRATUM` 17 | the R9 corrected node, as a dated `[r1]` erratum annex | **LANDED** |
| RX-3 | `HE6_PROOF_2026-08-08.md` | `HE6R1-1/2/3` 15/13/10, `HE6R1-T-CRACK` 2, `HE6-BOX-1` 3 *(reverse direction: HE6 cites this note)* | the widened box's ℓ = 1 branch, the four-case enumeration, the three composition lemmas, the r1 repair record | **LANDED** — `spec/EFF-HE6.md` `.19`, `.36`, `.39` |
| RX-4 | `spec/HYPOTHESIS_LEDGER.md` | `GENHN-ERR-1` 4 | the R9 residue as a ledgered row | LANDED |
| RX-5 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | row 15 | “CHALLENGE (fresh, R7) \| **CERTIFIED 2026-08-12** — repairs + re-display discharged (D2d 3/3); GENHN-ERR-1 settled by LEMMA GENHN-COUNT-RERUN (certificate confirmed; transcription confirmed at TC2)” | LANDED — **closes both obstructions** |

**Zero-orphan check.** Every file at HEAD naming `HE6R1` appears above; the sweep covered `lean/notes/openmath/`, `docs/`, `spec/` and `runs/`.

### 5.3 The three lemmas and two errata — the charge's summary table

`[TABLE]`

| object | EFF unit | proved? | machine-supported? | corrected since? | landed at HE7? |
|---|---|---|---|---|---|
| `LEMMA HE6R1-1` | `.09`/`.10` | YES | indirectly (termination not directly tested) | **YES — the global bound RE-DISPLAYED into three clauses** (`.47`) | replaces HE7.C's jump condition |
| `LEMMA HE6R1-2` | `.13` | YES | **NO — proof-only** (`μ ≥ 5` unexercised) | YES — the scalar's cocycle exponent, twice (`.35`, `.39`) | supplies HE7-BOX-4's count in read form |
| `LEMMA HE6R1-3` | `.15`/`.16` | YES | **YES — 12/12 decided, 5/5 PARI** | no | repairs HE7's missing hypothesis |
| `FINDING HE6R1-F1` | `.08` | — | — | no | **LANDED, count 4** |
| `FINDING HE6R1-F2` | `.14` | — | **discovered BY the battery** | no | **LANDED, count 8** |

---

## 6. TEETH — the inverse table (rule 6), both directions

### 6.1 Battery row → guarded unit(s)

`[TABLE]`

| leg / tooth | preregistration | guards | disposition |
|---|---|---|---|
| HE6R1-READ2 / SIG2 | P1 `.19` | `.07` (the literal-instance claim), `.17` | **FAILED AS PREREGISTERED** on 12/944 (`.24`) — non-decisions, never a wrong σ; the failure DISCOVERED erratum 2 |
| HE6R1-SLOT2 (1,512) | P2 `.19` | (SLOT₂) at ℓ = 1, i.e. `.06`'s degeneration | clean pass |
| HE6R1-LIFT2 (5 frames) | P3 `.19` | (LIFT₂) at `d_r = 2` | clean pass; **the §S6 summary of it was over-claimed** (`.46`) |
| HE6R1-GEN2 (252) | P4 `.19` | the level-2 flat identity | clean pass |
| HE6R1-SEP2 (46) | P5 `.19` | the level-2 strict excess | **4 sealed violations, recovered post-seal as instrument artifacts** (`.28`) |
| HE6R1-T-CRACK | `.29` | `.05`/`.21` — the widening's non-vacuity | fired — **certifies the ℓ = 1 branch REAL** |
| HE6R1-T-NAIVEHE6A | `.29` | the planted-dictionary refutation | fired |
| HE6R1-T-BASIS | `.29` | **the K₂-basis hypothesis of `.26`** | fired — certifies it load-bearing |
| HE6R1-T-TWIST0 | `.29` | `.06`'s `s(·) ≡ 0` | fired — **contrastive** against HE7-T-BADTWIST |
| HE6R1-T-WITHHOLD | `.29` | the reader's refusal behaviour | fired |
| supplementary (A) | post-seal | **`.15`/`.16` — LEMMA HE6R1-3** | 12/12 decided, 5/5 PARI |
| supplementary (B) | post-seal | `.28`'s four recoveries | 4/4 STRICT |

### 6.2 Guarded unit → battery row (inverse direction)

`[TABLE]`

| unit | guarded by | class |
|---|---|---|
| `.04` the R9 corrected node | — | **PROOF-ONLY** (`f₁ = 1` in every row, so the defect is invisible to the battery — the note says so) |
| `.06` the ℓ = 1 degeneration | HE6R1-T-TWIST0 (1,276 exponents, all zero) | battery-guarded |
| `.07` the literal-instance check | HE6R1-READ2/SIG2 (677/682, 0 mis-decisions) | battery-guarded |
| `.09`/`.10` LEMMA HE6R1-1 | — | **PROOF-ONLY** (no leg tests termination) |
| `.13` LEMMA HE6R1-2 | — | **PROOF-ONLY** — HE6R1-BOX-2 names its configuration unexercised |
| `.15`/`.16` LEMMA HE6R1-3 | supplementary (A): 12/12, 5/5 PARI | **battery-discovered AND battery-confirmed** |
| `.14` FINDING HE6R1-F2 | the sealed battery's own 12 BADTOTALs | **battery-discovered** |
| `.26` the K₂-independence mechanism | HE6R1-T-BASIS | battery-guarded |
| `.31`/`.32` the completion statement | — | **UNGUARDED — and A4 finding 2 shows why** |
| `.19` preregistrations | — | they *are* the guards |
| `.33`–`.48` appends | — | **AUDIT-produced**, see 6.4 |

### 6.3 PROOF-ONLY rows (rule 16) — the note's own coverage-hole sentences

HE6R1-BOX-2 (`.20`):

> “NOT exercised: f₁ ≥ 2 stage genres, d_r ≥ 3, μ ≥ 5
> (hence proper blocks — LEMMA HE6R1-2's own configuration is proof-only),
> level 3 (unreachable below n = 16). The proofs are uniform in all of these.”

R9 (`.04`), on why the battery could not see the node defect:

> “At f₁ = 1 this IS the displayed S-version (D′h = e₁h = S), which is why no battery row and no first-live case could see it.”

§S6 (`.30`):

> “**What the machine leg establishes** (instrument grade, not acceptance)”

So `.04`, `.09`/`.10`, `.13` and the completion statement are proof-carried. **Two of the four were later found defective by decorrelated reads** — `.09`'s display by A4 finding 1, and the completion statement by A4 finding 2 — **the same pattern as HE6, where both A3-found defects were also in the proof-only set.**

### 6.4 AUDIT dispositions (rule 27)

`[TABLE]`

| unit | AUDIT class | why no tooth applies |
|---|---|---|
| `.14`/`.15` FINDING F2 + the peel | **battery-discovered** — the exception that proves the rule | the sealed battery's 12 BADTOTALs *are* the discovery; the only such case in queue 8b |
| `.28` the four SEP2 recoveries | `in-house hostile pass` | a leg-construction artifact (pre- vs post-refine key), not a predicate failure |
| `.34`–`.37` the four PE2 riders | `in-house hostile pass` ×3 + `transfer audit` (F-1, an HE7-side echo) | reference collisions, stale grades and a cross-note echo |
| `.39`–`.41` the three PE3 riders | `in-house hostile pass` | a well-formedness defect (`c₁` off ℤ), a non-conservative stale grade, a reference collision |
| `.43`/`.44` the two obstructions | `decorrelated-model audit` | a quantifier-scope defect and an unhonoured qualification — neither measurable |
| `.45` A4 f3 | `decorrelated-model audit` | **the same sentence HE6's A3 F-3 corrects, found independently the same day** |
| `.46` A4 f4 | `decorrelated-model audit` | an internal contradiction between P3's table and the §S6 prose |

### 6.5 Zero-orphan check

**Battery rows → units: zero orphans.** All five legs, all five teeth and both supplementary items guard at least one inventoried unit.

**Units → guards: 48 units, 12 guarded, 36 unguarded.** The 36 decompose as: 4 PROOF-ONLY (6.3), 1 preregistration bundle, and 31 records/findings/append units covered by §4's pin verification and §5's grep verification instead. **No unit is silently unguarded.**

---

## 7. Arithmetic audit and fidelity audit

### 7.1 Arithmetic audit

**Confirmed exactly:**

- **The σ census reconciles completely** (`.25`): members 944, PARI 682, decided 932, non-decisions 12 (of which 5 in the PARI rows), agreements 677 — **all five headline figures derived from the table alone**, and the σ-alphabet columns sum to 932.
- **`(ℤ_3, λ=3)` and `(F_3[[t]], λ=3)` have identical member counts and identical σ columns** (124 / 92 / 16 / 12) — a characteristic-independence datum the note does not claim.
- **SEP2's split** `42 + 4 = 46` ✓, and the four recoveries `68 > 64` (×2), `100 > 96` (×2) ✓.
- **The LIFT₂ table** (`.27`): closed form `(d_r−1)u + (D′−1)h = λ+1` in all five frames ✓, observed onset `λ`, **gap exactly 1 everywhere** ✓ — confirming A4 finding 4 and contradicting the frozen §S6 prose.
- **The frame parameters** (`.18`): `D′ = 2`, `D″ = 4`, `K₂ = F_{p²}`, `T₂ = 2λ`, `μ₂ = 2`, `deg f = 8` — every one forced and every one checked.
- **The jump bound** (`.09`): `4 ≤ μ/2^{J−1} ⟹ J ≤ log₂μ − 1` ✓; `D′ ≥ 2 ⟹ J ≤ log₂n − 2` ✓; **the ambient counterexample `n = μ = 4`, `J = 1 > log₂4 − 2 = 0`** ✓ — the A4 finding is exact.
- **The re-display's three clauses** (`.47`), all three ✓, including clause (c)'s sharpness.
- **The descent chain** (`.10`): `L_λ ≥ m(ℓd_r) ≥ 4` ✓; `μ₂ ≤ deg R_λ/d_r ≤ μ/(ℓd_r)` ✓.
- **The R9 node derivation** (`.04`): pins strictly above the slope-`D′h` line through `(μ,0)` plus integrality ✓; `f₁ = 1 ⟹ D′h = S` ✓.
- **A4 finding 2's gap** (`.44`): at `f₁ = 2`, `μ−j = 1`, corrected `≥ 2S+1` vs displayed `≥ S+1` ✓ — differing by `S`.
- **LEMMA HE6R1-3's squeeze** (`.16`): `D″ = (e₁ℓ)(f₁d_r)` makes HE6-0′'s bound exactly `deg Ψ` ✓; the frame gives `(e(Ψ), f(Ψ)) = (2,2)` ✓, matching the `{(2,2),(2,2)}` prediction.
- **PE3 F-1's ill-formedness witness** (`.39`): pins `(3,0),(1,13),(0,21)` give `h = 39/2 ∉ ℤ` ✓, with `ℓ₂ = 2 ∤ j₁ = 1` ✓.
- **T-CRACK's breakdowns** (`.29`): `54+3+2 = 59` ✓, `47+6+1 = 54` ✓; and **T-NAIVEHE6A's complements (`2` and `1`) equal T-CRACK's `{(2,2),(2,2)}` counts** ✓ — an internal consistency the note does not point out.
- **A4 finding 3's divisibility and normalized display** ✓ — **identical mathematics to HE6's A3 F-3**, independently verified in both compilations.
- **Both nested prefix md5s** localize uniquely (L706, L786) ✓, and all four import md5s reproduce byte-exactly ✓.

**Findings — one, not a mathematical error:**

**AF-1 — the note reports `1,512`, `252` and `1,276` without a derivation.** These leg counts (SLOT₂ identities, level-2 flat identities, twist exponents) are artifact-backed but not recomputable from the note's displayed frame parameters. **Recorded as not independently verified**, honestly rather than passed. Every count that *is* derivable — 944, 932, 682, 677, 12, 46, 42, 59, 54 — was derived and checks.

### 7.2 Fidelity audit

- **Every CANONICAL STATEMENT is a verbatim quotation.** No `[ASSEMBLED]` statement appears.
- **No quantifier, bound, index, exponent, height, degree or count was altered anywhere.** The places where a bound or a quantifier is discussed as *wrong* (`.09`, `.30`, `.43`, `.46`) are the note's own or A4's corrections, quoted.
- **Truncations: two**, at `.03` (the nine-row repair table, whose R9 row is emitted separately at `.04` and whose other eight rows are compiled in `spec/EFF-HE6.md`) and `.44` (an ellipsis inside a quoted box, matching the note's own ellipsis). Both marked.
- **Rule 14 IS triggered twice and IS honoured twice**: `.25` (the σ census) and `.27` (the LIFT₂ frame table), each emitted verbatim then as `[TABLE]`.
- **All 11 commits, 4 import md5 pins, 2 nested prefix pins and 12 artifacts verified** (§4.3). Zero failures; three `UNPINNED-VALUE` dispositions recorded.
- **18 external designations grep-verified**, **zero NEAR-MISS**, zero invented names, zero designation OPEN-CALLs.
- **The two errata's landings were verified at the target by fixed-string grep** (`HE6R1-F1` count 4, `HE6R1-F2` count 8) — the queue charge's core check.
- **Every cross-note status claim checked against the target's full append chain (rule 10)** — which is how the two erratum landings, the GENHN erratum annex, and the SOL ledger's settlement of both obstructions were confirmed.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — `LEMMA HE6R1-2` is proof-only, closes a live gap, and has had its scalar corrected twice. FOR-0b.

`.13` closes a gap that is **live at `n ≥ 10`, inside the region COROLLARY HE7.B(i) claims** (`.12`), yet HE6R1-BOX-2 records its own configuration as **unexercised** (`μ ≥ 5` not run). Its clause (c)'s scalar identification was corrected at PE2 F-2 (`.35`) and again at PE3 F-1 (`.39`) — **a three-layer chain on a clause PE3's own blast-radius check found to have no consumers at HEAD.**

**Decision needed:** whether the corpus wants a `μ ≥ 5` machine row before `LEMMA HE6R1-2` is consumed at `n ≥ 10`, or whether the proof plus the two corrections suffice. **The compiler notes the tension:** a lemma whose displayed scalar needed two corrections, and whose configuration no battery has run, is the natural candidate for the next coverage row — but nothing in the note says it is owed.

### OPEN-CALL 2 — the OBSTRUCTED disposition is now a precedent and is not written down anywhere. FOR-0d — NEEDS ASVIN.

A4 introduced a disposition the corpus had not used before (`.42`): **REAL but OBSTRUCTED — “every honest repair weakens an accepted statement display, so no admissible repair exists”.** Both instances were then closed outside the append mechanism — one by an owner directive re-displaying a statement (`.47`), one by scheduling new mathematics (`.48`) — and **both closures worked** (SOL ledger row 15).

**But the precedent is recorded only inside this note's appends.** No template rule, no ledger row and no process document states: *when a post-acceptance defect admits no honest in-note repair, route it to an owner re-display or to a proof unit, never to a silent qualification.* **Decision needed:** whether this becomes a written corpus rule. It will recur — HE6's OPEN-CALL 3 (a permanently unresolvable provenance gap) and HMENU3's OPEN-CALL 2 (a stale grade frozen inside another note's verbatim annex) are both defects with no in-note remedy, and neither has a named disposition.

### OPEN-CALL 3 — HE6R1-BOX-1's re-dated grades are themselves an as-of record, and one supplier has moved again. FOR-0b.

PE2 F-3 (`.36`) re-dated six supplier grades as of 2026-08-09, keying the inherited minimum to **HE3's 0/2 (r2 owed)**. This compilation verified all six commits but **did not re-adjudicate any supplier's current arc**. HE3's `r2` was owed then; whether it has landed determines whether the minimum is still 0/2 and still keyed to HE3.

**Decision needed:** the same question OPEN-CALL 1 of `spec/EFF-HMENU3.md` raises — whether as-of grade records freeze with their date or owe periodic re-dating. **Note the asymmetry PE3 F-2 identified** (`.40`): a stale grade that *understates* is conservative; one that *overstates* is a defect. **A corpus rule could simply be: re-date only the overstating direction.** Offered as an observation, not a decision.

### Recorded source defects and reading hazards

1. **`.30`/`.27`: the §S6 summary contradicted P3's own table** on (LIFT₂)'s sharpness, 60 lines apart. Corrected by A4 f4.
2. **`.09`: the global jump bound was false at ambient roots**, with a minimal quartic counterexample. Re-displayed under owner authority.
3. **`.31`/`.32`: both qualifications written to prevent over-reading needed correction** — (i) by PE3 F-2 (a non-conservative stale grade), (ii) by A4 finding 2 (an unhonoured “no open mathematics” clause).
4. **`.32`: “two errata that have never been attacked” is stale** — they have been, and one of the three lemmas' displays was found defective.
5. **`.24`: P1 FAILED as preregistered.** Any citation of “the machine leg is GREEN” must carry the 12 non-decisions and the post-seal cure.
6. **`.28`: four sealed SEP2 violations** were instrument artifacts, recovered post-seal, and are displayed as three separate counts rather than folded.
7. **`.22`: the note's own artifacts are `UNPINNED-VALUE`** (commit-pinned, not hash-pinned) — unlike HE6, which pins every artifact by md5.
8. **`.20`: `GENHN-ERR-1` is displayed as unsettled and is SETTLED at HEAD** (LEMMA GENHN-COUNT-RERUN, ledger row 15). `STALE-SELF-DESCRIPTION` in the direction of resolution.
9. **AF-1: three leg counts are artifact-backed but not recomputable from the note.**
10. **`.03`: HE6's `[r1]` repair record lives here, not in HE6.** A chapter cut of either note alone is incomplete on the r1 round.

### Exhaustive residual judgment list

There are no other unresolved HE6R1 mathematical or scope judgments. HE6R1-BOX-2's coverage holes, HE6R1-BOX-3's oracle asymmetry, and the proof-only status of `LEMMA HE6R1-2` are the note's own displayed fences; the stale grades, the unpinned artifacts and the three underived counts are bookkeeping. The three OPEN-CALLs are the complete list of judgments the compiler could not make from the text.

### Compilation summary

- **48 statement units**, including **the three charge lemmas** (`.09`/`.10`, `.13`, `.15`/`.16`) and **the two HE7 errata** (`.08`, `.14`), each with landing status verified at the target by fixed-string grep (`HE6R1-F1` = 4, `HE6R1-F2` = 8).
- **18 external designations grep-verified; zero NEAR-MISS; zero invented names.**
- **11 commits + 4 import md5 pins + 2 nested prefix pins + 12 artifacts verified; zero failures.** Both prefix pins localize uniquely (L706, L786), and the second certifies the first append untouched.
- **5 reverse-XREF consumer edges**, all LANDED, including the ledger row that **closes both A4 obstructions**.
- **One SERIES** (the four-member ARC series `.01` → `.20` → `.33` → `.38`), **eleven supersession chains** (C-1…C-11), and **six distinct SUPERSESSION KINDs** — including the queue's first `OBSTRUCTED` dispositions and its first statement change made under a **named delegated authority**.
- **Rule 14 triggered and honoured twice** (`.25`, `.27`).
- **Arithmetic audit: the σ census reconciles to the last unit** — all five headline figures derived from the table alone — and every derivable count, bound and witness checks. One finding, not a mathematical error.
- **Honest headline for a chapter cut:** this note is the corpus's clearest case of a **preregistered prediction failing informatively** — P1's failure on 12 members *is* the discovery of HE7's missing hypothesis, the cure is proved (`LEMMA HE6R1-3`) and machine-confirmed (12/12, 5/5 PARI), and the note still scored the prediction as **FAILED**. It is also the only note carrying **REAL-but-OBSTRUCTED** findings, both since closed — one by an owner re-display, one by new mathematics — and neither by qualifying a displayed theorem.

EFF-HE6R1 COMPILED: 48 statements / 18 xrefs verified / 3 open calls
