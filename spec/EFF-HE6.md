# EFF-HE6 — CANONICAL EFFECTIVE SPECIFICATION v2/v3

## 1. Header

**Source note:** `lean/notes/openmath/HE6_PROOF_2026-08-08.md` (1,235 lines / 69,730 bytes).

**HEAD blob hash:** `236c978ebb2fb0497e460fdf6e9ce0b9b765a8b4`. Whole-file md5 at compile time: `d372a90a73b6d60c27922247b97f80ff`.

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a, Opus wave 4, queue 8b (Asvin-authorized substitution, `docs/PROJECT_STATE.md` #51).

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD — rules 1–28. Full compilation, unsharded (70 KB, below the ~80 KB shard threshold of rule 9).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED** (post-reset).

### Queue-specific charge: the nine T2 consumption anchors, emitted with their exact span identities

HE6 is the most heavily pinned supplier in the T2 σ-ladder master. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` pins **nine** byte-delimited HE6 spans and consumes them by name; **this compilation emits each as its own unit, keyed by its span, so the DAG can attach T2's edges mechanically.**

`[TABLE]` — **THE PIN TABLE (span identities verified at compile time under T2's own protocol)**

| T2 pin name | span | EFF unit | source object | first delimiter line (`grep -cFx`) | last delimiter line (`grep -cFx`) | T2 count |
|---|---|---|---|---|---|---|
| `HE6-PEEL-CONVENTION` | **[83,97]** | `.09` | §S1 `CONVENTION [r1]` (disc f ≠ 0, Φ′ ∤ f, the peel) | `> **CONVENTION [r1] (the two standing hypotheses on f — R2/F2 and R6/F7).**` — **1** | `> peel is cleaner and is what is adopted.)` — **1** | 32 |
| `HE6-LIFT-1L` | **[130,199]** | `.13` | `LEMMA HE6-1L` ((LIFT) corrected) + RIDER + both NON-PROPAGATION inventories | `> **LEMMA HE6-1L [r1; display corrected [r2], PE2 F-1] ((LIFT), corrected =` — **1** | `> q(0) = q(1) = 0; (3,1,2): T(1) = ∅), per PE2 F-1.` — **1** | 34 |
| `HE6-FAMILY` | **[201,213]** | `.14` | `DEFINITION HE6-1` (the enlarged test family Ψ_{κ,r}) | `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` — **1** | `> Montes' language these are the order-2 keys; nothing below uses that fact.` — **1** | 59 |
| `HE6-SLOT-SEAM` | **[215,238]** | `.15` | `LEMMA HE6-0″` (the slot lemma at (T1)/(T2) points) | `> **LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form` — **1** | `> restatement.**` — **1** | 48 |
| `HE6-TEST-PACKAGE` | **[244,287]** | `.17` | the seven statements `HE6-0′`, `HE6-1`, `HE6-2`, `HE6-2′`, `HE6-3`, `HE6-4`, `HE6-5` | `> **LEMMA HE6-0′ (the local forcing — HE3-0′ REPAIRED at ℓ ≥ 2).** If a root` — **1** | `> Galois-stable, at every f₁ (no f₁ = 1 restriction).` — **1** | 59 |
| `HE6-ROOT-LABEL` | **[517,521]** | `.29` | `Corollary HE6-2″` (the label is well defined) | `**Corollary HE6-2″ (HE3-0(iii), re-proved in this convention).** Taking` — **1** | `of ρ; it is well defined because R_λ is a fixed element of K[Z].` — **1** | 26 |
| `HE6-ACCOUNT` | **[525,604]** | `.30` | the whole of §S5 — `(RES)`, the proof of `HE6-3`, the (SEP) remark, the proof of `HE6-4`, the non-tautology remark | `## S5. LEMMA HE6-3 (slope counts, (SEP)-free) AND LEMMA HE6-4 (nonemptiness)` — **1** | `what replaces HE3-BOX-6's base change.` — **1** | 55 |
| `HE6-PROOF` | **[639,666]** | `.32` | §S6.2, the four-step proof of `THEOREM HE6.A` + the HE3-4 replacement sentence | `### S6.2 PROOF OF THEOREM HE6.A` — **1** | `histories containing an ℓ ≥ 2 side with a repeated residual factor.` — **1** | 66 |
| `HE6-BETA-GUARD` | **[1036,1047]** | `.56` | the post-PE4 **Correction 2** (LEMMA HE6-2's β-definedness guard, re-scoped to δ = κ) | `**Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard).** The` — **1** | `lemma's conclusion and its consumers are unaffected by this re-scoping.` — **1** | 63 |

**Verification performed (T2's own protocol, re-run at compile time 2026-08-14).** For each of the nine spans: `grep -cFx '<first delimiter>'` = **1** and `grep -cFx '<last delimiter>'` = **1** in `lean/notes/openmath/HE6_PROOF_2026-08-08.md`; the first line strictly precedes the last; and the enclosed text is the object T2 names. **Nine of nine spans verify.** T2's own resolution of five of them is quoted at `T2_SIGMA_LADDER_MASTER_2026-08-12.md` L3863 — “The five HE6 pins, as this pass resolved them, are `HE6-PEEL-CONVENTION` [83,97], `HE6-LIFT-1L` [130,199], `HE6-FAMILY` [201,213], `HE6-SLOT-SEAM` [215,238], `HE6-PROOF` [639,666].” — and the three r10 spans at L4041 — “`HE6-TEST-PACKAGE` [244,287], `HE6-ROOT-LABEL` [517,521], `HE6-ACCOUNT` [525,604], each delimiter line occurring exactly once, each first delimiter pr[eceding the last]” — and `HE6-BETA-GUARD` at L4059: “HE6's post-PE4 **Correction 2**, the bolded unit closing the `### Dated acceptance record + corrections (2026-08-09, post-PE4)` section (1036–1047)”. **All three of T2's own span statements reproduce exactly against HEAD.**

**One structural observation the DAG needs.** `LEMMA HE6-0` (the disk criterion, L240–242) sits **between** `HE6-SLOT-SEAM` [215,238] and `HE6-TEST-PACKAGE` [244,287] and is **in no pin span** — yet it is consumed by `HE6-TEST-PACKAGE`'s own members (HE6-3(a) cites “LEMMA HE6-0 applied to HE3-0's (T1)/(T2)”) and by `.22`'s proof. Emitted at `.16` and flagged: **a chapter cut assembled from T2's pins alone would omit HE6-0.** See OPEN-CALL 1.

### Effective-text rule

The note carries a literal effective-text rule at the acceptance record (L1015–1016):

> “Counter 1/2 → **2/2: HE6 is
> ACCEPTED — the text is FROZEN, dated appends only from here.**”

with the freeze pinned at L1000–1002:

> “this is a dated append only. The body above is byte-untouched
> (pre-append file md5 234668cb6d24d36a88ddf05ad8617321 is this append's
> prefix); the sealed runners and artifacts stay frozen at their pins.”

and re-declared by the 2026-08-12 append (L1058–1059): “Everything above this heading is byte-untouched by this append.”

**Therefore the effective text is: the body L1–993 read with its inline `[r1]` and `[r2]` bracket repairs applied in place, then the two dated append blocks in date order — the 2026-08-09 post-PE4 acceptance record with its Correction 1 and Correction 2 (= `HE6-BETA-GUARD`), and the 2026-08-12 sol-A3 fold with its four dated corrections F-1…F-4.** No body text is edited by any append.

### FREEZE PREDICATES (rule 21 — four independent freezes)

**FREEZE-1 — text freeze (acceptance).** L1016: “the text is FROZEN, dated appends only from here.” Pin: prefix md5 `234668cb6d24d36a88ddf05ad8617321`. **PIN VERIFIED and localized:** the md5 of the file's first **993 lines** is exactly that value — found by exhaustive search over every line boundary, **unique hit**. L993 is §S9's closing sentence (“…nothing here upgrades the conditionality display of COROLLARY HE6.B.”).

**FREEZE-2 — instrument freeze, with a disclosed defect in the pin itself.** §S9 pins `he6_checks.py` md5 `321fa4d4990e…`, `he6_checks_output.txt` md5 `403d44cfe462…`, `he6_checks_results.json` md5 `1e1836651283…`, “identical at close **1f5a417** and at HEAD”. **ALL THREE PIN VERIFIED EXACTLY** at compile time (`321fa4d4990eef67ff6a20f375c32366`, `403d44cfe462d7d800bfe0dbe59f2988`, `1e183665128313004298e2c406a991df`); `1f5a417` and `a77c376` are commits ✓. **But the note itself records that an earlier version of this pin was FALSE** — see `.48`, the `[r2]` RECORD REPAIR, which withdraws the `[r1]`-era “runner-as-run 959fff4052e9…” pin as naming bytes that exist nowhere in the repo, and discloses an unexplained 9 m 34 s post-run edit window. **The freeze is sound at HEAD; its history is not, and the note says so.**

**FREEZE-3 — hostile-report freeze.** `HE6_passPE3_report.md` md5 `298b3c973e31648c65b405532b2e28eb` ✓ **exact**; `HE6_passPE4_report.md` md5 `14d1b88c25fa8213d2706843f1ce67e6` ✓ **exact**. Both re-hashed at compile time.

**FREEZE-4 — the cross-note freeze this note's r2 repair triggered.** L165–168 records that HE7's frozen counterpart was repaired by HE7's own dated append, “**LANDED this wave at commit 5da0552** … HE7's frozen body byte-untouched, prefix md5 0698155b”. **PIN VERIFIED:** `5da0552` is a commit ✓, and `grep -cF 'Dated correction (2026-08-09, from HE6 PE2 F-1)' HE7_PROOF_2026-08-08.md` = **1** ✓ — **the landing is real** (§5.2 RX-1).

### Supersession chains inside the note

`[TABLE]`

| # | Target (frozen text) | Layer 1 (`[r1]`) | Layer 2 (`[r2]`) | Layer 3 (post-PE4, 08-09) | Layer 4 (sol A3, 08-12) | TERMINAL |
|---|---|---|---|---|---|---|
| C-1 | `(LIFT)` (L122–123) | **STRUCK — FALSE as stated**; replaced by `LEMMA HE6-1L` | display corrected (the `η_θ^{−q(k)}` coset factor) | — | — | **`[r2]` HE6-1L** (`.13`) |
| C-2 | `LEMMA HE6-0″`'s twist sign | introduced `[r1]` with `+q` | **sign corrected to `−q`** (PE2 F-3) | — | **A3 F-1**: the slot residue `γ` gains its coefficient normalizers, becoming `γ_k(A)` | **A3 F-1** (`.58`) |
| C-3 | `COROLLARY HE6.B`'s scope sentence (L303) | **STRUCK — FALSE** (PE1 finding 1, CRITICAL); replaced | — | — | — | **`[r1]` HE6.B** (`.19`) |
| C-4 | §S3.1's last two cases of `LEMMA HE6-0` | **STRUCK and RE-PROVED** (the ψ-cancellation route, PE1 finding 5) | — | — | **A3 F-3**: “equality exactly at” → “equality possible only at” | **A3 F-3** (`.60`) |
| C-5 | §S9's runner pin + the header freeze anchor | `[r1]` pin “959fff4052e9…” / “at seal a77c376” | **both FALSE; corrected** (PE2 F-2) — the true anchor is close `1f5a417` | — | — | **`[r2]`** (`.48`, `.03`) |
| C-6 | §S7.2's `(LIFT₂)` display | unconditional quantifier | **threshold conditional inserted** (PE2 F-5) | — | — | **`[r2]`** (`.38`) |
| C-7 | The grade sentence “attempt 0/2, no hostile arc has run” (L992) | `[r1]` 0/2 post-r1 | `[r2]` 0/2 post-r2, PE3 next | **ACCEPTANCE 2/2** — “This line supersedes the round-dated grade sentence directly above” | ledger row **CERTIFIED** | **ACCEPTANCE + the ledger row** |
| C-8 | §S9's headline “1,385 members over six rows” | — | — | **Correction 1**: UNRECONSTRUCTABLE; read as **986** unique members / **2,958** config instances | — | **Correction 1** (`.55`) |
| C-9 | `LEMMA HE6-2`'s guard “when δ has denominator dividing ℓ” | — | — | **Correction 2 = `HE6-BETA-GUARD`**: read as “when δ = κ” | — | **`HE6-BETA-GUARD`** (`.56`) |
| C-10 | §S5's `LEMMA HE6-3(a)` inference from `c₀ = 0` | — | — | — | **A3 F-2**: replaced by a length argument (`Σ L_λ = μ`, `Σ n_λ = D′μ`, `Σc_{λᵢ} = D′B`) | **A3 F-2** (`.59`) |
| C-11 | §S6.1's “All of Φ′, ϖ ∈ O[x]” | (contradicted in advance by the `[r1]` R7/F8 convention, L106–107) | — | — | **A3 F-4**: read as “Φ′ ∈ O[x] and ϖ ∈ K₀[x], both g-fixed” | **A3 F-4** (`.61`) |
| C-12 | The A3 provenance's “awaiting sol discharge-confirmation” | — | — | — | — | **SOL ledger row 14: `CERTIFIED`, D2c 4/4 DISCHARGED** (external; `.62`) |

**Note on C-11.** This is an *internal* contradiction the note carried from `[r1]` to the A3 fold: the `[r1]` R7/F8 convention explicitly says “**ϖ ∈ K₀[x], not O[x]**” at L107, while §S6.1 at L613 says “All of Φ′, ϖ ∈ O[x]”. Four hostile passes did not flag it; the decorrelated A3 read did. **Two spans of the same note, contradicting each other for four rounds** — recorded as the sharpest instance in this note of what audits catch and batteries cannot.

### Scope of record — three-predicate split (rules 7 and 17)

#### A. Mathematical absorption/supply set

The note's own title and status line:

> “HE6 — HE3-BOX-6 **CLOSED**: the ENLARGED TEST FAMILY at FRACTIONAL HEIGHTS pins the label class sizes at EVERY side (ℓ ≥ 2 ∧ deg-res ≥ 2 included), BASE-CHANGE-FREE — plus (SEP) removed and HE3's semilinearity gap closed; ONE new named box survives (HE6-BOX-1, the deeper read at a repeated residual on an ℓ ≥ 2 side, machine-certified real)”

The supply set is **one theorem (HE6.A), one corollary (HE6.B), and nine lemmas (HE6-0, 0′, 0″, 1, 1L, 2, 2′, 3, 4, 5 plus Corollary HE6-2″)**, over the suppliers GENHN (the slot lemma), HE3 (definitions, HE3-0, HE3-1, the THEOREM HE3.A assembly) and classical resultant symmetry. The number of *source obligations discharged* is **four**, all HE3's: HE3-BOX-6's two branches (SUPERSEDED, `.35`), HE3-3's `(SEP)` hypothesis, HE3-0′'s ℓ ≥ 2 residue, and HE3's PE1 finding 6 (semilinearity). One new box is opened: **HE6-BOX-1**.

#### B. Consumption / append-protocol scope — one outbound landing, verified

HE6 edits no source file. Its one outbound obligation is the cross-note correction its own PE2 F-1 raised against HE7: L163–168 records that `LEMMA HE7-L1` “carries the identical omission (display lines byte-identical)” and that HE7 repaired it by its own dated append at **`5da0552`**. **VERIFIED LANDED** (FREEZE-4). This is a **supplier-finding discharged at the source** in the rule-13 sense, and the direction is HE6 → HE7.

**Inbound, HE6 is a supplier to nine named T2 pins** (the pin table above) and to `HE6R1_RECON_2026-08-08.md`, `HE7_PROOF_2026-08-08.md` and the T2 master. See §5.2.

#### C. Inbound corrections RECEIVED (rule 17)

Three.

1. **From Codex PE1** (`CODEX_HE6PE1_2026-08-08.md`, 9 findings: 4 CRITICAL + 5 gaps) — the `[r1]` round, R1–R9. Findings 1, 4, 5, 6 are each load-bearing and each named at its repair site (`.19`, `.12`, `.22`, `.15`).
2. **From HE7's FINDING HE7-F1** — the second, independent discovery of the `(LIFT)` defect, at `(3,1,2)` where height `k = 1` is attained by no `C` at all. HE6 adopts **HE7's** sharper form and cites both finders (`.13`).
3. **From the Fable PE2 pass** (`HE6_passPE2_report.md` @ `404dae1`) — five findings, F-1…F-5, all landing as `[r2]` sites.

### Resolution rules applied

1. Body brackets `[r1]`/`[r2]` are part of the frozen body and apply in place.
2. The two dated appends apply in date order; the A3 corrections land on body spans, not on the acceptance append.
3. **A struck display is not effective text.** `(LIFT)` (C-1) and `COROLLARY HE6.B`'s original scope sentence (C-3) carry the note's own `~~strikethrough~~` and the word STRUCK; both are emitted as `[SUPERSEDED]` history with their replacements.
4. The frozen grade vocabulary — “Attempt grade 0/2” (four places), HE6-BOX-2, §S9's closing “attempt 0/2, no hostile arc has run” — is superseded by the ACCEPTANCE (2/2) and the SOL ledger (CERTIFIED). The acceptance record supersedes §S9's sentence **by name**; the others are `STALE-SELF-DESCRIPTION`.
5. **T2's pin spans are read as byte ranges of the effective text, not of a struck-through reading.** Three of the nine spans (`HE6-LIFT-1L`, `HE6-SLOT-SEAM`, `HE6-BETA-GUARD`) contain `[r1]`/`[r2]`/PE4 correction text *inside* the span, so a consumer that pins the span already pins the correction. **Two do not:** `HE6-SLOT-SEAM` [215,238] is further corrected by **A3 F-1**, which lies at L1061–1113, **outside every pin span**; and `HE6-ACCOUNT` [525,604] is further corrected by **A3 F-2** at L1115–1154, likewise outside. See OPEN-CALL 2 — this is the single most consequential finding of this compilation for T2.
6. Out-of-note material (T2, HE7, HE3, GENHN, HE6R1, the ledgers) is used only to resolve and verify.

### Quotation and prosification discipline

Every CANONICAL STATEMENT is a verbatim quotation or explicitly marked `[ASSEMBLED]`. The note's one fixed-width ASCII table (§S9 Q3's σ table, L944–959) is emitted **twice** — verbatim as the source display, then as a `[TABLE]` transcription — per **rule 14**, which *is* triggered here (unlike in EFF-HEX3 and EFF-HMENU3). The note's LaTeX displays in the A3 corrections are reproduced as written. Strikethrough is reproduced, since it marks supersession. Terminal punctuation and `∎` marks preserved.

---

## 2. NON-IMPORTS

**N-1 — the three deliberate non-consumptions.** §S0 L62–69:

> “**NOT consumed (deliberate).** (a) **No base change**, unramified or
> ramified — that is the whole point: HE3-BOX-6's substitute is not repaired,
> it is *removed*. (b) **No Ore theorem, no Montes/GMN index theorem, no
> higher-order residual-polynomial operator** — the test polynomials of
> DEFINITION HE6-1 are *never assumed irreducible*; §S3 proves what is needed
> about ALL of their roots by hand. (Those citations reappear only as the
> cite target of HE6-BOX-1, §S7.) (c) GENHN-4 is not consumed, so the W-9
> graded weld face stays absent from the σ chain, exactly as in HE3.”

**This is the note's defining fence.** (a) is what makes THEOREM HE6.A a supersession of HE3-BOX-6 rather than a repair; (b) is what keeps the FGMN citation a *target* (`.40`) rather than a consumed axiom; (c) keeps the weld face out of the σ chain.

**N-2 — no irreducibility of the test polynomials.** `LEMMA HE6-1` states it inline: “**No irreducibility of Ψ_{κ,r} is claimed or used.**” §S3.3's closing remark explains why this matters: “they do NOT need Ψ irreducible — which is why no order-≥2 citation enters THEOREM HE6.A.”

**N-3 — GENHN-3 is consumed only at the battery.** §S0: “GENHN-3 (window ledger) is consumed only where a windowed member must be certified (§S8).”

**N-4 — (LIFT₂)/(SLOT₂) are NOT proved here.** §S7.2 L793: “**This note does not prove (LIFT₂)/(SLOT₂)**”. They are proved in HE7 and composed in HE6R1 (`.39`) — “Both suppliers are at attempt grade 0/2, so this is a composition claim, not an acceptance.”

**N-5 — the FGMN route is displayed as a target, not a discharge.** §S7.3 L826: “it is displayed here as a target, not as a discharge”, gated on a faithfulness entry and a semantic-guardian pass.

**N-6 — the machine leg is instrument grade, not acceptance.** §S9 L985: “**What the machine leg establishes** (instrument grade, not acceptance)”.

**N-7 — what the machine does NOT exercise.** HE6-BOX-3: “NOT exercised by machine: f₁ ≥ 2 stage genres (so the σ prediction {(2,2),(2,2)} of §S2 at (1,2,4) is proof-only), μ ≥ 5, d ≥ 2 ambients, and embedded genres. The proofs are uniform in all of these.”

**N-8 — no char-p oracle.** HE6-BOX-4: “PARI `factorpadic` exists only on the ℤ_p side”. Inherited by every unit of the program.

---

## 3. Statement inventory

IDs `EFF.HE6.01`–`.62`. **Pin units are marked `[PIN: <name> [a,b]]` in their headings.**

### EFF.HE6.01  [record]

**CANONICAL STATEMENT** (verbatim, L3–10). FORM: bold-headed paragraph.

> “**Unit:** HE6 (the last lemma of the uniformity program).
> **Status:** complete at commit 2. Statements §S1; where HE3-BOX-6 first bites
> §S2 (**n = 8, μ = 4, D′ = 2**); proofs §S3–S6 (LEMMA HE6-0/0′/1/2/2′/3/4/5,
> THEOREM HE6.A); the two boxed HE3 branches' verdicts §S6.5 (**both
> SUPERSEDED — proved without any base change**); COROLLARY HE6.B and the
> honest residue §S7 (**HE6-BOX-1**); battery §S8 (runner sealed at commit 1
> with predictions P1–P5 and five teeth, `verification/openmath/he6_checks.py`);
> verdict §S9. **Attempt grade 0/2** — no hostile pass has run on this note.”

**DERIVATION.** [RECORD].

**SERIES membership (rule 28).** **ARC SERIES member 1.** Order: `.01` (composition, 0/2) → `.02` (`[r1]`, post-PE1) → `.03` (`[r2]`, post-PE2) → `.41` (HE6-BOX-2) → `.53` (§S9's closing grade sentence) → `.54` (ACCEPTANCE 2/2) → `.62` (the ledger, CERTIFIED).

**CONDITIONALITY.** “**Attempt grade 0/2** — no hostile pass has run on this note” is `STALE-SELF-DESCRIPTION` twice over: four hostile passes ran (PE1–PE4), and the counter reached **2/2 ACCEPTED**. The statement-list half is current and accurate.

**XREF.** artifact `verification/openmath/he6_checks.py` — EXISTS ✓, md5 pinned and verified.

---

### EFF.HE6.02  [changes-record]

**CANONICAL STATEMENT** (verbatim, L11–23). FORM: bold-headed paragraph with an embedded `[r2]` correction bracket.

> “**[r1] 2026-08-08 REPAIR ROUND (post-PE1).** Codex's hostile pass PE1
> (`CODEX_HE6PE1_2026-08-08.md`, 9 findings: 4 CRITICAL + 5 gaps, 8 upheld as
> classified, 1 regraded upstream) has run; its repair queue R1–R9 is APPLIED
> in this file, every site tagged `[r1]`, with the full record, the widened-box
> reconciliation against HE7 and a new machine leg in
> `HE6R1_RECON_2026-08-08.md`. The runner and artifacts of §S8/§S9 are
> BYTE-FROZEN since close 1f5a417 **[r2 anchor corrected, PE2 F-2: the [r1]
> line said "at seal a77c376", false twice — at the seal the runner was the
> pre-run WIP (md5 af7009ecb005…) and the artifacts did not yet exist; zero
> diffs 1f5a417 → HEAD on the runner and both artifacts, re-verified this
> round by md5]** (every finding lives off the exercised strata).
> **Attempt grade stays 0/2 post-r1** — a repair round does not upgrade an arc,
> and the r1 text owes a fresh hostile pass.”

**DERIVATION.** [RECORD].

**SERIES membership.** ARC SERIES member 2.

**SUPERSESSION KIND (the embedded `[r2]` bracket):** `replacement` — a false freeze anchor replaced by a true one. **TARGETS:** this unit and `.47`/`.48`.

**CONDITIONALITY.** **PIN VERIFIED:** `1f5a417` and `a77c376` are commits ✓; `CODEX_HE6PE1_2026-08-08.md` EXISTS ✓; `HE6R1_RECON_2026-08-08.md` EXISTS ✓. The clause “every finding lives off the exercised strata” is the blast-radius claim for PE1's nine findings and is the reason no artifact byte moved in `[r1]`.

**XREF.** `HE6R1_RECON_2026-08-08.md` — `HE6R1-1`, count 15; `HE6R1-2`, count 13; `HE6R1-3`, count 10.

---

### EFF.HE6.03  [changes-record]

**CANONICAL STATEMENT** (verbatim, L24–36). FORM: bold-headed paragraph.

> “**[r2] 2026-08-09 REPAIR ROUND (post-PE2).** The first Fable hostile pass
> PE2 (`HE6_passPE2_report.md`, commit 404dae1: 0 CRITICAL + 2 GAP + 3 MINOR)
> has run on the r1 text; its five findings are repaired at [r2]-tagged sites
> in this file and in `HE6R1_RECON_2026-08-08.md`: F-1 (LEMMA HE6-1L's
> exact-set display gains the η_θ^{−q(k)} coset factor + the coset
> non-propagation inventory, §S1), F-3 (LEMMA HE6-0″'s twist sign −q, §S1),
> F-2 (§S9's runner pin corrected + the post-run edit disclosed + this
> header's freeze anchor, above), F-4 (the recon R3 row's "verbatim" softened
> to display-identical), F-5 (§S7.2's (LIFT₂) display gains its threshold
> inline). No sealed artifact byte changed in this round (the F-2 repair
> corrects the note's DESCRIPTION of the artifacts, not the artifacts).
> **Attempt grade stays 0/2 post-r2** — the r2 text owes a fresh hostile pass
> (PE3).”

**DERIVATION.** [RECORD] — the `[r2]` site index, which is the map a chapter cut needs to find the five repairs.

**SERIES membership.** ARC SERIES member 3.

**CONDITIONALITY.** `404dae1` is a commit ✓; `HE6_passPE2_report.md` EXISTS ✓. The closing grade sentence is superseded by `.54`. **Note F-4 lands in ANOTHER note** (`HE6R1_RECON_2026-08-08.md`), so this round's repair set is not confined to HE6 — an outbound edge recorded at §5.2 RX-2.

**XREF.** `HE6R1_RECON_2026-08-08.md` — EXISTS ✓.

---

### EFF.HE6.04  [imported]

**CANONICAL STATEMENT** (verbatim, §S0 L42–52). FORM: bulleted display with an indented hypothesis block.

> “* **GENHN @ HEAD** — LEMMA GENHN-1 (stage ring, Φ′-development, node) and
>   **LEMMA GENHN-2 (THE SLOT LEMMA)**, the one load-bearing import: for
>   A = Σ_{i<D′}a_ix^i and ANY ξ with
>
>       (T1) v(ξ) = h/e₁, gcd(h, e₁) = 1,   (T2) η_ξ := res(ξ^{e₁}π^{−h}) is a
>                                                root of ψ,
>
>   one has dv(A(ξ)) = min_i(e₁v(a_i) + ih) EXACTLY, and the residue of the
>   attaining slot is the universal polynomial Σ_t res(a_{i+e₁t})·η_ξ^t
>   evaluated at η_ξ. GENHN-3 (window ledger) is consumed only where a
>   windowed member must be certified (§S8).”

**DERIVATION.** [IMPORTED] — “the one load-bearing import”.

**CONDITIONALITY.** Conditional on GENHN @ HEAD. **A defect in the import as pasted is recorded by the note itself** at `.15`: “Codex PE1 finding 6 is the observation that GENHN-2 as PASTED is stated at roots θ of Φ′ only, while this note applies it at roots of f and at roots of the (generally reducible) test polynomials — an overconsumption cured by this restatement.” **So this import is consumed only through `HE6-SLOT-SEAM`'s restatement, never directly** — the DAG edge is GENHN → `.15` → everything, not GENHN → everything.

**A3 F-1 sharpens the residue clause.** The displayed residue “Σ_t res(a_{i+e₁t})·η_ξ^t” omits coefficient normalizers; `.58` supplies `γ_k(A)`. **The import's display as quoted here therefore carries the same omission**, and a consumer must read it through A3 F-1. Flagged.

**XREF.** `GENHN_PROOF_2026-08-08.md` — `LEMMA GENHN-1`, count 4; `LEMMA GENHN-2`, count 2; `GENHN-3`, count 21; `GENHN-4`, count 6.

---

### EFF.HE6.05  [imported]

**CANONICAL STATEMENT** (verbatim, §S0 L53–57). FORM: bulleted display.

> “* **HE3 @ 7a95449** — DEFINITION 1 (stage resolvent F, polygon P(F), labels)
>   and DEFINITION 2 (decided leaves); LEMMA HE3-0 (every root of f on the
>   genre-G opening locus satisfies (T1)/(T2)); LEMMA HE3-1 (the resultant
>   identity); the assembly of THEOREM HE3.A (§S6.3 there) and the
>   strict-descent recursion of COROLLARY HE3.B.”

**DERIVATION.** [IMPORTED].

**CONDITIONALITY.** Pinned at HE3 commit **`7a95449`** — **PIN VERIFIED** ✓. Note the asymmetry the note builds on: HE6 imports HE3's *frame and assembly* while **replacing** HE3's LEMMA HE3-4 (`.32`) and **removing** HE3-3's `(SEP)` and HE3-0′'s ℓ ≥ 2 defect. So HE3 is simultaneously a supplier and the note's repair target.

**XREF.** `HE3_PROOF_2026-08-08.md` — `LEMMA HE3-0`, count 7; `LEMMA HE3-1`, count 32; `THEOREM HE3.A`, count 17; `COROLLARY HE3.B`, count 8; `DEFINITION 1`, count 13; `DEFINITION 2`, count 3.

---

### EFF.HE6.06  [imported]

**CANONICAL STATEMENT** (verbatim, §S0 L58–61). FORM: bulleted display.

> “* **Classical only** — resultant symmetry Res(f,g) = ±Π_{ρ}g(ρ) = ±Π_{ξ}f(ξ)
>   for monic f, g over O; the ultrametric inequality; uniqueness of the
>   extension of v to K̄₀ (hence its Galois invariance); the elementary convex
>   duality (★) of HE3-3 step 1.”

**DERIVATION.** [IMPORTED].

**CONDITIONALITY.** These four are the *entire* non-HE3, non-GENHN input. The note's strongest structural claim rests on it — §S6.5 branch (ii): “the only algebraic inputs are the SLOT LEMMA and the ultrametric inequality, both characteristic-free.” **Compiler check:** the four inputs are each characteristic-free ✓, which is what licenses the both-characteristics scope of THEOREM HE6.A.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-3`, count 15 (the source of (★)).

---

### EFF.HE6.07  [fence]

**CANONICAL STATEMENT** — the §S0 “NOT consumed (deliberate)” block, quoted in full at N-1 (L62–69). FORM: bulleted display.

**DERIVATION.** [RECORD of a negative fence].

**CONDITIONALITY.** Current and load-bearing at three separate places (`.35`, `.40`, and the σ-chain scope). No append touches it.

**XREF.** `GENHN_PROOF_2026-08-08.md` — `GENHN-4`, count 6. `HE3_PROOF_2026-08-08.md` — `HE3-BOX-6`, count 12.

---

### EFF.HE6.08  [convention]

**CANONICAL STATEMENT** (verbatim, §S1 L75–81). FORM: paragraph.

> “O a complete DVR, π a uniformizer, v(π) = 1, K₀ = Frac(O), residue field
> F_Q, both characteristics; v extended (uniquely) to a fixed algebraic
> closure K̄₀. Φ′ ∈ O[x] monic irreducible of degree D′ = e₁f₁ with roots of
> v = h/e₁, gcd(h,e₁) = 1; ψ ∈ F_Q[T] irreducible of degree f₁ with root
> η_θ := res(θ^{e₁}π^{−h}) for θ a root of Φ′; K := F_Q(η_θ) ≅ F_{Q^{f₁}};
> dv := e₁v. For a (T1)/(T2) point ξ write **ι_ξ : K → k̄** for the
> F_Q-embedding η_θ ↦ η_ξ (well defined by (T2)), and L_ξ := K₀(ξ).”

**DERIVATION.** [DEFINITIONAL].

**CONDITIONALITY.** Unconditional. The embedding `ι_ξ` is the object that carries the whole note: labels live in `K[Z]` (a fixed object) and are transported to each root by its **own** embedding — which is exactly what makes `LEMMA HE6-5`'s Galois argument work (`.31`: “the two twists cancel because ι_{gρ} = ḡ∘ι_ρ”).

**XREF.** none.

---

### EFF.HE6.09  [convention]  **[PIN: `HE6-PEEL-CONVENTION` [83,97]]**

**SPAN IDENTITY.** `lean/notes/openmath/HE6_PROOF_2026-08-08.md` **lines 83–97**. First delimiter `> **CONVENTION [r1] (the two standing hypotheses on f — R2/F2 and R6/F7).**` — `grep -cFx` = **1**, at line 83. Last delimiter `> the peel is cleaner and is what is adopted.)` — `grep -cFx` = **1**, at line 97. First precedes last ✓. **T2 consumption count: 32.**

**CANONICAL STATEMENT** (verbatim, the full span). FORM: display (blockquoted convention with an italic proof-parenthetical).

> “**CONVENTION [r1] (the two standing hypotheses on f — R2/F2 and R6/F7).**
> Throughout, **disc f ≠ 0** (f separable) and **Φ′ ∤ f**, equivalently
> **A₀ ≠ 0** (no root of f is a root of Φ′). *The second is not a
> restriction: if A₀ = 0 then Φ′ | f, and disc f ≠ 0 forces f = Φ′·f̃ with
> Φ′ ∤ f̃; the peeled factor Φ′ is irreducible of degree D′ and contributes
> the KNOWN σ-block (e₁, f₁), while f̃ is again monic with all roots
> (T1)/(T2) points, disc f̃ ≠ 0 and μ̃ = μ − 1, so every statement below is
> applied to f̃.* Without this convention a root ρ with Φ′(ρ) = 0 has
> dv(Φ′(ρ)) = ∞ and carries NO finite side label, and then the sum over
> finite labels in (†) of §S5 is not exhaustive, Σ_λ L_λ = μ fails, and
> HE6-3's elimination loses its premise — Codex PE1 finding 2's
> counterexample f = Φ′(Φ′ + π²) at Φ′ = x − π, where the displayed (†)
> reads κ = 2κ on 1 < κ < 2. (The alternative repair, an ∞-label column
> n_∞ = D′L_∞ with L_∞ := μ − Σ_λ L_λ, also works — see the r1 record — but
> the peel is cleaner and is what is adopted.)”

**DERIVATION.** The span carries its own three-part warrant: (i) the reduction (`f = Φ′·f̃`, μ̃ = μ−1, all hypotheses inherited), (ii) the necessity argument (without it, `Σ_λ L_λ = μ` fails and HE6-3's elimination loses its premise), and (iii) the counter-instance `f = Φ′(Φ′ + π²)` at `Φ′ = x − π`.

**Mathematical audit of the counter-instance.** At `Φ′ = x − π` (so `D′ = 1`, `e₁ = f₁ = 1`, `h = 1`), `f = Φ′(Φ′ + π²) = Φ′² + π²Φ′`, i.e. `μ = 2`, `A₁ = π²`, `A₀ = 0` ✓. The root `ρ = π` has `Φ′(ρ) = 0`, so `dv(Φ′(ρ)) = ∞` ✓ — no finite label. The other root has `Φ′(ρ′) = −π²`, `dv = 2`. So `Σ_λ n_λ·min(λ,κ)` counts only the finite-label root: `min(2,κ) = κ` on `1 < κ < 2`, giving LHS `= κ`; while `D′·Σ_λ L_λ min(λ,κ)`: the polygon of `F(Y) = Y² + π²Y` has pins `(0,∞)`, `(1,2)`, `(2,0)`, hull from `(1,2)` to `(2,0)`, so one side of length 1 and slope 2 — but the abscissa range is `1..2`, not `0..2`, so `Σ L_λ = 1 ≠ μ = 2`. With the note's `(†)` written as `Σ n_λ min(λ,κ) = D′Σ L_λ min(λ,κ)` and the LHS mis-summed over `μ = 2` roots, the displayed contradiction “κ = 2κ” arises ✓. **The counter-instance is sound and the convention is genuinely necessary, not hygienic.**

**CONDITIONALITY.** `disc f ≠ 0` is inherited from the consuming site — THEOREM HE6.A's own statement notes “the consuming site THEOREM HE3.A carries disc f ≠ 0 explicitly, so the composed program is unaffected” (`.18`). **This is the pin T2 consumes 32 times**, and its content is exactly the two standing hypotheses plus the peel that makes the second free.

**T2 consumption note.** T2 L2574 records: “**(a) `HE6-PEEL-CONVENTION`** — consumed by repair 4(b) as the level-one original-key discharge of the `(MID-PEEL)` input suite, and by S1.5's key-freeness discipline at the HE3+HE6 instance.” **Two named consumption sites**, both keyed to this span.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-3`, count 15. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-PEEL-CONVENTION`, count 32.

---

### EFF.HE6.10  [definition]

**CANONICAL STATEMENT** (verbatim, §S1 L99–102). FORM: inline display.

> “f monic on the genre-G opening locus, f = Φ′^μ + Σ_{j<μ}A_jΦ′^j with
> deg A_j < D′, dv(A_j) := min_i(e₁v(a_{j,i}) + ih); F(Y) := Y^μ +
> Σ_j A_j(θ)Y^j; P(F) := lower hull of {(j, dv(A_j))}_{j≤μ} (dv(A_μ) = 0);
> sides have dv-slope λ = u/ℓ in lowest terms and length L_λ = ℓd_λ.”

**DERIVATION.** [DEFINITIONAL], imported from HE3's DEFINITION 1.

**CONDITIONALITY.** `A₀ ≠ 0` (from `.09`) is what makes the polygon run from abscissa 0 to μ, hence `Σ_λ L_λ = μ` — **the identity A3 F-2 later needs** (`.59`). Recorded because the dependence is not stated at either site.

**XREF.** `HE3_PROOF_2026-08-08.md` — `DEFINITION 1`, count 13.

---

### EFF.HE6.11  [convention]

**CANONICAL STATEMENT** (verbatim, §S1 L104–120). FORM: display (blockquoted convention with an indented definition of `R_λ`).

> “**CONVENTION (ϖ-normalizers: twist-free).** Fix once and for all
> ϖ := x^{i₀}π^{a₀} with i₀h + e₁a₀ = 1 and 0 ≤ i₀ < e₁ (possible since
> gcd(h,e₁) = 1). **[r1, R7/F8]** a₀ may be NEGATIVE (e.g. (e₁,h) = (2,3)
> gives i₀ = 1, a₀ = −1, ϖ = xπ^{−1}), so **ϖ ∈ K₀[x], not O[x]** — its
> coefficients are Galois-fixed, which is all that is ever used (§S6.1).
> Then dv(ϖ(ξ)) = 1 EXACTLY at every (T1)/(T2) point ξ, and
> every normalizer used below is a power ϖ^k. Because they are powers of ONE
> element, the normalizer cocycle is trivial: **HE3's twist constants ẑ^{fl}
> do not occur anywhere in this note**, and all residual polynomials are
> defined relative to this one convention. For the side with left endpoint
> (j₁, m₁), slope λ = u/ℓ, length ℓd:
>
>     R_λ(Z) := Σ_{t=0}^{d} res( A_{j₁+tℓ}(θ)/ϖ(θ)^{m₁−tu} ) Z^t ∈ K[Z],
>
> the coefficient being 0 whenever the pin at j₁+tℓ lies strictly above the
> λ-line. So R_λ has degree d and R_λ(0) ≠ 0, and its variable Z is the class
> of y^ℓ/ϖ^u.”

**DERIVATION.** The `[r1]` R7/F8 bracket supplies the one non-obvious fact (`a₀` may be negative, so `ϖ ∉ O[x]`) with a witness; the rest is definitional.

**Arithmetic audit of the witness.** `(e₁,h) = (2,3)`: `i₀h + e₁a₀ = 1` with `0 ≤ i₀ < 2` → `3i₀ + 2a₀ = 1` → `i₀ = 1, a₀ = −1` ✓, so `ϖ = xπ^{−1}` ✓. And `dv(ϖ(ξ)) = e₁(v(ξ)·i₀ + a₀) = e₁(i₀h/e₁ + a₀) = i₀h + e₁a₀ = 1` ✓ **exactly**, at every (T1) point.

**CONDITIONALITY — and the internal contradiction this convention exposes.** The bracket states plainly “**ϖ ∈ K₀[x], not O[x]**”, yet §S6.1 (`.31`) asserts “All of Φ′, ϖ ∈ O[x]”. **The two spans contradict each other**, and did so through four hostile passes; **A3 F-4** (`.61`) resolves it in favour of this convention. Recorded here as well as at `.31` and `.61`, because a consumer reading `.31` alone would import a false integrality.

**XREF.** none external.

---

### EFF.HE6.12  [changes-record]

**CANONICAL STATEMENT** (verbatim, §S1 L122–129). FORM: struck display plus its replacement announcement.

> “~~**(LIFT)** For every c ∈ K^× and every k ∈ ℤ_{≥0} there is C ∈ O[x]
> with deg C < D′, dv(C) = k, and res(C(θ)/ϖ(θ)^k) = c.~~
> **[r1, R3] STRUCK — FALSE as stated**, found independently twice: Codex
> PE1 finding 4 (at (e₁,f₁,h) = (1,2,1), k = 0 only F_Q ⊊ K is reached) and
> HE7's FINDING HE7-F1 (at (3,1,2) the height k = 1 is attained by no C at
> all). Replaced by HE7's sharper form, which satisfies both finders'
> counter-instances and gives the EXACT reachable set:”

**DERIVATION.** [RECORD of a strike] with two independently discovered counter-instances.

**Mathematical audit of both counter-instances.** (a) `(e₁,f₁,h) = (1,2,1)`, `k = 0`: `D′ = 2`, `ϖ = π^{a₀}` with `e₁a₀ = 1 − i₀h`, `i₀ = 0` forced (`0 ≤ i₀ < e₁ = 1`), so `a₀ = 1`, `ϖ = π`. At `k = 0` the `C` with `dv(C) = 0` are those with a unit coefficient at slot `i = 0`, and `res(C(θ)/ϖ(θ)^0) = res(c_0) ∈ F_Q` — **only `F_Q`, not `K = F_{Q²}`** ✓. (b) `(3,1,2)`, `k = 1`: `T(1) = {t < 1 : 1 ≥ (i₀ + 3t)·2}` with `i₀(1)` the unique `0 ≤ i₀ < 3` with `2i₀ ≡ 1 (mod 3)` → `i₀ = 2`; then `t = 0` needs `1 ≥ 4`, false, so **`T(1) = ∅`** ✓ — the height is attained by no `C` at all. **Both counter-instances check exactly against the replacement's own `T(k)` formula**, which is the note's claim that “the two findings name ONE defect”.

**SUPERSESSION KIND:** `replacement`. **TARGETS:** every downstream use of `(LIFT)`, all of which are inventoried inside `.13`'s NON-PROPAGATION boxes.

**XREF.** `HE7_PROOF_2026-08-08.md` — `LEMMA HE7-L1`, count 12; `HE6`, count 209.

---

### EFF.HE6.13  [lemma]  **[PIN: `HE6-LIFT-1L` [130,199]]**

**SPAN IDENTITY.** Lines **130–199**. First delimiter `> **LEMMA HE6-1L [r1; display corrected [r2], PE2 F-1] ((LIFT), corrected =` — `grep -cFx` = **1**, at line 130. Last delimiter `> q(0) = q(1) = 0; (3,1,2): T(1) = ∅), per PE2 F-1.` — `grep -cFx` = **1**, at line 199. First precedes last ✓. **T2 consumption count: 34.** The span contains **four objects**: the corrected lemma, the `[r2]` correction record, the RIDER, and **two** NON-PROPAGATION inventories.

**CANONICAL STATEMENT — the lemma proper** (verbatim, L130–151). FORM: display (blockquoted lemma with an indented exact-set display and an italic proof-parenthetical).

> “**LEMMA HE6-1L [r1; display corrected [r2], PE2 F-1] ((LIFT), corrected =
> LEMMA HE7-L1 with the ϖ-read coset factor).** Fix k ∈ ℤ_{≥0} and let
> i₀ = i₀(k) be the unique 0 ≤ i₀ < e₁ with i₀h ≡ k (mod e₁). The set of
> residues realised as res(C(θ)/ϖ(θ)^k) by C ∈ O[x] with deg C < D′ and
> dv(C) = k is
>
>     η_θ^{−q(k)} · { Σ_{t ∈ T(k)} c_t·η_θ^{t} : c_t ∈ F_Q, not all 0 },
>     T(k) := { t < f₁ : k ≥ (i₀ + e₁t)·h } ,
>
> where η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ)) is the RIDER's fixed normalizer
> ratio, n(k) := x^{i₀(k)}π^{(k−i₀(k)h)/e₁} the canonical height-k monomial.
> The set is ALL of K^× iff T(k) = {0,…,f₁−1} iff
> **k ≥ (i₀(k) + e₁(f₁−1))h** (the coset factor is invisible in this clause:
> η_θ^{−q(k)}·K^× = K^×); a k-uniform sufficient condition is
> **k ≥ (D′−1)h**; if T(k) = ∅ the height k is not attained at all (a
> twist-free clause). *(Proof: HE7 §S4.1's argument computes, via GENHN-2,
> the n(k)-READ residues of the C with dv(C) = k — exactly the braced span
> over the available slots T(k); the ϖ-read residue is the n(k)-read residue
> times res(n(k)(θ)/ϖ(θ)^k) = η_θ^{−q(k)}, whence the coset translate.
> Codex's general failure condition "k < (i(k) + e₁(f₁−1))h" IS this
> threshold — the two findings name ONE defect, and HE7's is the sharper
> statement, so it is the one adopted; both finders are cited.)*”

**DERIVATION.** [IMPORTED from HE7 §S4.1] plus a one-line coset translation. The proof is **not** HE6's: “HE7 §S4.1's argument computes, via GENHN-2, the n(k)-READ residues”. HE6 supplies only the change of normalizer.

**Mandatory arithmetic audit (rule 22) — the two threshold clauses and the witness.** (i) **`k ≥ (D′−1)h ⟹ k ≥ (i₀ + e₁(f₁−1))h`:** since `i₀ ≤ e₁−1`, `i₀ + e₁(f₁−1) ≤ (e₁−1) + e₁f₁ − e₁ = D′ − 1` ✓ — the uniform condition is genuinely sufficient. (ii) **The `(2,2,3)` witness of the `[r2]` record**, recomputed from scratch: `e₁ = f₁ = 2`, `h = 3`, `D′ = 4`, `O = ℤ₃`, `Φ′ = x⁴ + 729`; roots have `v = 6/4 = 3/2 = h/e₁` ✓; `ϖ = x^{i₀}π^{a₀}` with `3i₀ + 2a₀ = 1`, `0 ≤ i₀ < 2` → `i₀ = 1, a₀ = −1`, `ϖ = xπ^{−1}` ✓; at `k = 3`, `i₀(3)` solves `3i₀ ≡ 3 (mod 2)` → `i₀ = 1` ✓; `T(3) = {t < 2 : 3 ≥ (1+2t)·3} = {0}` ✓ **proper**; `n(3) = x^1π^{(3−3)/2} = x`, so `ϖ(θ)³/n(3)(θ) = θ³π^{−3}/θ = θ²π^{−3}`, whose residue is by definition `η_θ` — hence **`q(3) = 1`** ✓, exactly as the note states. The prediction `η^{−1}·F₃^×`: with `η² = −1`, `η^{−1} = −η = 2η` (mod 3), so the set is `{2η, η}` ✓ — **exactly PE2's realized `{η, 2η}`**, while the `[r1]` bare span `{1,2}` is disjoint from it ✓. (iii) `k = 9 = (D′−1)h = 3·3` ✓, and `|F₉^×| = 8` ✓. **Every number in the correction record reproduces.**

**The `[r2]` CORRECTION RECORD** (verbatim, L153–168) — quoted in full because it is the span's own supersession and carries the cross-note landing:

> “**[r2] CORRECTION RECORD (PE2 F-1, machine-confirmed).** The [r1] display
> showed the bare span, omitting the coset factor η_θ^{−q(k)}. PE2's
> constructed instance verifies the corrected display: at (e₁,f₁,h) =
> (2,2,3), O = ℤ₃, Φ′ = x⁴ + 729, ϖ = xπ^{−1} (η² = −1, η ∉ F₃), k = 3:
> i₀(3) = 1, T(3) = {0} proper, q(3) = 1 (ϖ(θ)³/n(3)(θ) = θ²π^{−3}, residue
> η), so the display above predicts η^{−1}·F₃^× = {η^{−1}, 2η^{−1}} =
> {2η, η}; PE2's 162-member enumeration realized exactly **{η, 2η}** — while
> the [r1] bare span predicted {1, 2}, disjoint from the realized set. At
> k = 9 = (D′−1)h the same frame realizes all 8 of F₉^× (the fullness
> clause, twist-invariant, as displayed). The frozen counterpart LEMMA
> HE7-L1 (HE7 §S4.1) carries the identical omission (display lines
> byte-identical, per PE2 F-1's landing paragraph); per HE7's freeze it is
> repaired by HE7's own dated append, **LANDED this wave at commit 5da0552**
> ("Dated correction (2026-08-09, from HE6 PE2 F-1)": the coset display,
> the same (2,2,3) witness, and HE7's own four-site non-propagation
> enumeration; HE7's frozen body byte-untouched, prefix md5 0698155b).”

**CROSS-NOTE LANDING VERIFIED (rule 10).** `git cat-file -t 5da0552` = `commit` ✓; `grep -cF 'Dated correction (2026-08-09, from HE6 PE2 F-1)' HE7_PROOF_2026-08-08.md` = **1** ✓. **The claimed landing is real and checkable by its own quoted heading string.**

**The RIDER** (verbatim, L170–175):

> “**RIDER [r1, R3 second half].** The residue above is read after dividing by
> ϖ^k, not by the canonical height-k normalizer n(k) = x^{i}π^{a}; the two
> differ by ϖ(θ)^k/n(k)(θ) = (θ^{e₁}π^{−h})^{q} = η_θ^{q}, where i₀k = i+qe₁
> and a₀k − a = −qh. This is a FIXED nonzero element of K, universal in C and
> ι_ξ-transportable, so every statement below about vanishing, non-vanishing,
> degrees and surjectivity is unaffected.”

**The two NON-PROPAGATION inventories** (verbatim, L177–199) — the `[r1]` one:

> “**NON-PROPAGATION (checked).** Every use of (LIFT) in this note is at
> k = (d−t)u with t < d and u = ℓκ > ℓD′h ≥ D′h > (D′−1)h (DEFINITION HE6-1
> requires κ > D′h), and the t = d coefficient is B_d := 1 (height 0,
> residue 1, no lift needed). So all f₁ slots are available at every use and
> no theorem of this note changes.”

and the `[r2]` eight-route one:

> “**NON-PROPAGATION OF THE COSET FACTOR [r2] (inventory, per PE2 F-1's
> trace).** The eight consumption routes PE2 traced consume only the two
> twist-blind clauses of LEMMA HE6-1L — the K^×-fullness clause ("ALL of
> K^× iff T(k) full", invariant under the coset factor since
> η_θ^{−q}·K^× = K^×) or the T(k) = ∅ clause (twist-free): (1) DEFINITION
> HE6-1's B_t lifts (k = (d−t)u > (D′−1)h, T full — fullness); (2) the [r1]
> NON-PROPAGATION box above (fullness); (3) HE6-3/HE6-4's Ψ constructions
> (fullness); (4) HE7 §S4.2's (LIFT₂) proof calls (m_t > λ > (D′−1)h per
> HE7 §S4.3 [r1] — fullness); (5) HE7's W₁/W₂ sharpness display (fullness
> and emptiness, both twist-blind); (6) tooth HE7-T-LIFT2SHARP (checks the
> two fullness halves only); (7) the he6r1 battery leg P3; (8) R_λ's §S1
> definition (a definition, not a reachability claim). On this enumeration
> no statement of HE6 or HE7 consumes the exact-set clause at a proper
> T(k) — the sub-threshold exact set has no traced consumer today. The
> defect stayed invisible to prior by-hand checks because they sat at
> frames with q(k) = 0 at every proper-T height tested ((2,2,1):
> q(0) = q(1) = 0; (3,1,2): T(1) = ∅), per PE2 F-1.”

**Arithmetic audit of the `[r1]` inventory's inequality chain.** `u = ℓκ > ℓD′h ≥ D′h > (D′−1)h` requires `ℓ ≥ 1` ✓ and `D′h > (D′−1)h ⟺ h > 0` ✓; and `k = (d−t)u ≥ u` for `t < d` ✓. **So every in-note use sits above the fullness threshold and the coset factor is invisible there** ✓ — the non-propagation claim is sound.

**CONDITIONALITY.** The exact-set clause at a **proper** `T(k)` has **no traced consumer today** — the note says so, and lists the eight routes that consume only twist-blind clauses. **This is the pin T2 consumes 34 times**, and T2's own consumption is at the fullness clause (T2 L2864 records `HE6-LIFT-1L` as the definitional home of `q(k)`, “defined only there (repair 4)”). The `q(k)` *definition* is therefore load-bearing for T2 even though the exact-set clause is not.

**XREF.** `HE7_PROOF_2026-08-08.md` — `LEMMA HE7-L1`, count 12; the landing heading, count 1. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-LIFT-1L`, count 34.

---

### EFF.HE6.14  [definition]  **[PIN: `HE6-FAMILY` [201,213]]**

**SPAN IDENTITY.** Lines **201–213**. First delimiter `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` — `grep -cFx` = **1**, at line 201. Last delimiter `> Montes' language these are the order-2 keys; nothing below uses that fact.` — `grep -cFx` = **1**, at line 213. First precedes last ✓. **T2 consumption count: 59.**

**CANONICAL STATEMENT** (verbatim, the full span). FORM: display (blockquoted definition with an indented construction).

> “**DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest
> terms with κ > D′h, and let r = Z^{d} + Σ_{t<d}c_tZ^t ∈ K[Z] be monic
> irreducible with r(0) ≠ 0. Choose, by (LIFT), B_t ∈ O[x] with
> deg B_t < D′, dv(B_t) = (d−t)u and res(B_t(θ)/ϖ(θ)^{(d−t)u}) = c_t (and
> B_t := 0 if c_t = 0), and set
>
>     Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_t·Φ′^{ℓt}  ∈ O[x],
>
> monic of degree D″ := D′ℓd (each B_tΦ′^{ℓt} has degree < D′ℓd). For ℓ = 1
> this is HE3's recentered-key family enlarged in DEGREE; for ℓ ≥ 2 it is a
> test polynomial sitting at a **FRACTIONAL** dv-height — the height that
> HE3-BOX-6 correctly observed no element of the stage ring can reach. In
> Montes' language these are the order-2 keys; nothing below uses that fact.”

**DERIVATION.** [DEFINITIONAL], with one obligation discharged inline: the lifts `B_t` exist **by (LIFT)**, i.e. by `.13`'s corrected LEMMA HE6-1L — and `.13`'s NON-PROPAGATION box route (1) is precisely this call, verified to sit above the fullness threshold.

**Arithmetic audit.** `deg(B_tΦ′^{ℓt}) < D′ + D′ℓt = D′(1+ℓt) ≤ D′ℓd` requires `1 + ℓt ≤ ℓd` for `t ≤ d−1`, i.e. `1 ≤ ℓ(d−t)`, true since `ℓ ≥ 1`, `d−t ≥ 1` ✓ — so `Ψ` is monic of degree exactly `D″ = D′ℓd` ✓. The lift heights `(d−t)u` are all `> (D′−1)h` since `u > ℓD′h ≥ D′h` ✓ — the fullness condition `.13` needs.

**CONDITIONALITY.** Three hypotheses are load-bearing and each is later shown so: `κ > D′h` (used in every `.25` case bound), `gcd(u,ℓ) = 1` (**machine-certified load-bearing** by tooth HE6-T-BADKEY, `.52`, which shows a `κ = 6/2` key has 2 p-adic factors with different residues), and `r` monic irreducible with `r(0) ≠ 0` (used at `.56` — “`r(0) ≠ 0` forces `ι_ξ(r)(0) ≠ 0`”).

**T2 consumption note.** T2 L3875 records `HE6-FAMILY` as the supplier of “S1.7 clause 7 and the degree display — ‘all tests and coefficient lifts remain in \(O[x]\)’, \(\deg\Psi_{\lambda,r'}=De'\deg r'\)”, with “the legality of the lifts from `HE6-LIFT-1L` [130,199]”. **Two pins, one clause** — a two-pin edge the DAG must carry as a conjunction.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-BOX-6`, count 12. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-FAMILY`, count 59.

---

### EFF.HE6.15  [lemma]  **[PIN: `HE6-SLOT-SEAM` [215,238]]**

**SPAN IDENTITY.** Lines **215–238**. First delimiter `> **LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form` — `grep -cFx` = **1**, at line 215. Last delimiter `> restatement.**` — `grep -cFx` = **1**, at line 238. First precedes last ✓. **T2 consumption count: 48.** T2 L3139 independently re-derived this span's delimiters and their line numbers.

**CANONICAL STATEMENT** (verbatim, the full span, with the `[r2]` sign correction and the `[r2]` witness in place). FORM: display (blockquoted lemma with an inline correction bracket, an italic witness paragraph, an italic proof, and a bold provenance sentence).

> “**LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form
> this note actually consumes).** Let A = Σ_{i<D′}a_ix^i with a_i ∈ O and let
> ξ be ANY point of K̄₀ satisfying (T1) and (T2). Then
> dv(A(ξ)) = min_i(e₁v(a_i) + ih) EXACTLY, and the residue of the attaining
> class, read after division by ϖ(ξ)^{dv(A)}, is ι_ξ(γ)·η_ξ^{−q} **[r2 sign
> corrected, PE2 F-3: dividing by ϖ^k instead of n(k) MULTIPLIES the
> n(k)-read residue by res(n(k)/ϖ^k) = η^{−q}; the [r1] text read +q]**
> where γ = Σ_t res(a_{i₀+e₁t})η_θ^{t} ∈ K is the level-1 slot residue at θ
> and η_ξ^{q} is the RIDER's universal twist (q = q(dv(A)) as in LEMMA
> HE6-1L, transported by ι_ξ since ϖ and n(k) have Galois-fixed
> coefficients). *[r2] Witness and reconciliation (PE2 leg B): at (2,2,3),
> k = 3, A = x one has γ = 1 and the ϖ-read realizes η^{−1} = 2η (PE2's
> CXRES), where the [r1] +q reading predicts η; and ranging γ over the
> braced span reproduces exactly LEMMA HE6-1L's corrected coset display
> η_θ^{−q(k)}·span — the two [r2] displays are consistent, curing the [r1]
> pair's mutual inconsistency (twist absent in HE6-1L, wrong-signed here).* *Proof: GENHN-2's proof uses (T1)
> only to separate the e₁ classes (e₁v(a_i) + ih ≡ ih mod e₁, and
> i ↦ ih mod e₁ is a bijection of ℤ/e₁ because gcd(h,e₁) = 1) and (T2) only
> to make {1, η_ξ, …, η_ξ^{f₁−1}} F_Q-independent (η_ξ is a root of the
> irreducible ψ of degree f₁); it never uses Φ′(ξ) = 0. ∎* **Codex PE1
> finding 6 is the observation that GENHN-2 as PASTED is stated at roots θ of
> Φ′ only, while this note applies it at roots of f and at roots of the
> (generally reducible) test polynomials — an overconsumption cured by this
> restatement.**”

**DERIVATION.** The proof is a **scope audit of GENHN-2's own proof**: it identifies exactly which hypotheses that proof consumes ((T1) for the class separation, (T2) for the `F_Q`-independence) and observes that `Φ′(ξ) = 0` is used nowhere — so the lemma holds at every (T1)/(T2) point, not only at roots of `Φ′`. **This is the whole content**, and it is what cures PE1 finding 6's overconsumption.

**Mathematical audit of the two hypothesis roles.** (T1): `e₁v(a_i) + ih ≡ ih (mod e₁)`, and `i ↦ ih (mod e₁)` is a bijection of `ℤ/e₁` iff `gcd(h,e₁) = 1` ✓ — so the `D′` slots split into `e₁` classes of `f₁` each, exactly one class per residue, and the minimum in each class is attained without cancellation across classes ✓. (T2): `η_ξ` a root of the irreducible `ψ` of degree `f₁` makes `{1, η_ξ, …, η_ξ^{f₁−1}}` `F_Q`-independent ✓ — so within the attaining class the residue sum cannot vanish accidentally. **Both roles are correctly identified and neither needs `Φ′(ξ) = 0`** ✓.

**Arithmetic audit of the `[r2]` sign and witness.** `res(ϖ(θ)^k/n(k)(θ)) =: η_θ^{q}` (the RIDER's definition), so `res(n(k)/ϖ^k) = η^{−q}` ✓ — the `[r2]` correction's stated reason is exactly right, and the `[r1]` `+q` was the reciprocal. The witness at `(2,2,3), k = 3, A = x`: `γ = Σ_t res(a_{i₀+e₁t})η^t` with `i₀(3) = 1`, `a_1 = 1`, `T(3) = {0}` → `γ = 1` ✓; `q(3) = 1` (`.13`); so the ϖ-read residue is `1·η^{−1} = 2η` ✓, and the `[r1]` reading would give `η` ✓. **Consistent with `.13`'s corrected coset display**, exactly as the witness paragraph claims.

**CHAIN (rule 25 — three layers).** `[r1]` `+q` → **`[r2]` `−q`** (PE2 F-3) → **A3 F-1** (`.58`), which replaces the *bare* slot residue `γ = Σ_t res(a_{i₀+e₁t})η_θ^{t}` with the **normalized** `γ_k(A) = Σ res(a_{i+e₁t}π^{−(k−(i+e₁t)h)/e₁})η_θ^t`. **TERMINAL: A3 F-1.**

**⚠ THE PIN-SPAN GAP — the most consequential finding of this compilation for T2.** `HE6-SLOT-SEAM` is the span **[215,238]**. **A3 F-1 lies at L1061–1113, entirely OUTSIDE that span** — and outside every one of the nine pin spans. **A consumer that pins [215,238] byte-literally therefore pins the `[r2]`-corrected but A3-UNCORRECTED display**, i.e. the bare `γ` that A3 F-1 shows to be vacuous (its provenance note: “the tying coefficients have positive valuation `(k−jh)/e₁`, so the bare `res(a_j)` reading is vacuous”). T2 consumes this pin **48 times**. See OPEN-CALL 2.

**T2 consumption note.** T2 L2772 records that r4 “declined LEMMA HE6-1L as the adjudication target of `HE6-SLOT-SEAM`” and L3015 records the later reversal — “the pinned candidate wins… The discharge rests on four pinned units”, naming `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF` as jointly certifying T2's `(MP1′)` assertion (i)–(vii). **A four-pin conjunction edge**, three of whose members are HE6 spans.

**XREF.** `GENHN_PROOF_2026-08-08.md` — `LEMMA GENHN-2`, count 2. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-SLOT-SEAM`, count 48.

---

### EFF.HE6.16  [lemma]  **(in NO pin span — see OPEN-CALL 1)**

**CANONICAL STATEMENT** (verbatim, L240–242). FORM: display (blockquoted lemma).

> “**LEMMA HE6-0 (the disk criterion).** For ξ ∈ K̄₀ put dv(ξ) := e₁v(ξ). If
> (T1)/(T2) hold at ξ then dv(Φ′(ξ)) > D′h; otherwise
> dv(Φ′(ξ)) = D′·min(dv(ξ), h) ≤ D′h.”

**DERIVATION** — §S3.1 (`.22`), including the `[r1]` R4/F5 re-proof.

**⚠ PIN-SPAN GAP.** This lemma sits at **L240–242**, in the two-line gap between `HE6-SLOT-SEAM` [215,238] and `HE6-TEST-PACKAGE` [244,287], and belongs to **no** T2 pin span. Yet it is consumed **inside** `HE6-ACCOUNT` [525,604] — HE6-3(a)'s proof reads “Every root ρ has λ_ρ = dv(Φ′(ρ)) > D′h (**LEMMA HE6-0** applied to HE3-0's (T1)/(T2))” — and by `.25` (§S3.3 Step 1's case split is entirely driven by it). **A chapter cut assembled from the nine pins alone would omit the disk criterion while importing two spans that consume it.** Flagged, nothing invented. See OPEN-CALL 1.

**CONDITIONALITY.** Corrected in one clause by **A3 F-3** (`.60`), which is likewise outside every pin span.

**XREF.** `HE3_PROOF_2026-08-08.md` — `LEMMA HE3-0`, count 7.

---

### EFF.HE6.17  [lemma]  **[PIN: `HE6-TEST-PACKAGE` [244,287]]**

**SPAN IDENTITY.** Lines **244–287**. First delimiter `> **LEMMA HE6-0′ (the local forcing — HE3-0′ REPAIRED at ℓ ≥ 2).** If a root` — `grep -cFx` = **1**, at line 244. Last delimiter `> Galois-stable, at every f₁ (no f₁ = 1 restriction).` — `grep -cFx` = **1**, at line 287. First precedes last ✓. **T2 consumption count: 59.** The span contains **seven statements**, emitted below as `(a)`–`(g)`; T2's r10 pass “re-derived r10's three new spans at byte level and upheld all three” (T2 L4041).

**CANONICAL STATEMENT (a) — LEMMA HE6-0′** (verbatim, L244–248):

> “**LEMMA HE6-0′ (the local forcing — HE3-0′ REPAIRED at ℓ ≥ 2).** If a root
> ρ of f has label (λ, r) with λ = u/ℓ in lowest terms and d_r = deg r, then
> e₁ℓ | e(L_ρ) and f₁d_r | f(L_ρ); hence [L_ρ : K₀] ≥ D′ℓd_r. (HE3-0′ read
> the residue off y_ρ/n(λ)(ρ), which does not exist for ℓ ≥ 2; the correct
> reading is y_ρ^ℓ/ϖ(ρ)^u, which does.)”

**(b) — LEMMA HE6-1** (verbatim, L250–253):

> “**LEMMA HE6-1 (the ξ-side: EVERY root of a test polynomial carries the
> intended label).** Every root ξ of Ψ_{κ,r} satisfies (T1)/(T2),
> dv(Φ′(ξ)) = κ, and ι_ξ(r)(β_ξ) = 0 where β_ξ := res(Φ′(ξ)^ℓ/ϖ(ξ)^u).
> **No irreducibility of Ψ_{κ,r} is claimed or used.**”

**(c) — LEMMA HE6-2** (verbatim, L255–264):

> “**LEMMA HE6-2 (the ρ-side evaluation: the family SEPARATES labels).** Let ξ
> be any (T1)/(T2) point, δ := dv(Φ′(ξ)), and — when δ has denominator
> dividing ℓ — β := res(Φ′(ξ)^ℓ/ϖ(ξ)^u). Then
>
>     dv(Ψ_{κ,r}(ξ)) = ℓd·min(δ, κ) + ε(ξ),
>     ε(ξ) > 0  ⟺  δ = κ and ι_ξ(r)(β) = 0.
>
> In particular, for a root ρ of f with label (λ_ρ, r_ρ): ε(ρ) > 0 iff
> (λ_ρ, r_ρ) = (κ, r). **One test polynomial per label, and each sees exactly
> its own class.**”

**(d) — LEMMA HE6-2′** (verbatim, L266–269):

> “**LEMMA HE6-2′ (the f-side evaluation at a test point).** For any
> (T1)/(T2) point ξ with dv(Φ′(ξ)) = κ and β_ξ as above,
> dv(f(ξ)) = h_F(κ) + δ(ξ) where h_F(κ) := min_j(dv(A_j) + jκ) and
> δ(ξ) > 0 ⟺ κ is a slope λ of P(F) and ι_ξ(R_λ)(β_ξ) = 0.”

**(e) — LEMMA HE6-3** (verbatim, L271–278):

> “**LEMMA HE6-3 (slope counts, (SEP)-FREE).** With
> n_λ := #{ρ : f(ρ) = 0, dv(Φ′(ρ)) = λ}: (a) P(F) has no slope ≤ D′h;
> (b) n_λ = D′L_λ for every slope λ. **No hypothesis of the (SEP) kind that
> HE3-3 needed** (its counterexample — three slopes inside one integer
> interval — is defeated because the enlarged family samples h_F at every
> RATIONAL height); and no caveat about |K^×| being too small to supply a
> generic letter (irreducible r of degree > μ always exists and can never
> divide a residual polynomial).”

**(f) — LEMMA HE6-4** (verbatim, L280–282):

> “**LEMMA HE6-4 (NONEMPTINESS — the engine).** For every slope λ of P(F) and
> every monic irreducible r | R_λ, the class S_{λ,r} := {ρ : λ_ρ = λ,
> ι_ρ(r)(β_ρ) = 0} is NONEMPTY.”

**(g) — LEMMA HE6-5** (verbatim, L284–287):

> “**LEMMA HE6-5 (Galois equivariance of labels — HE3's PE1 finding 6,
> CLOSED).** For g ∈ Gal(K̄₀/K₀) and ρ a root of f with label (λ, r), the
> root gρ has label (λ, r) — the SAME r. Hence every S_{λ,r} is
> Galois-stable, at every f₁ (no f₁ = 1 restriction).”

**DERIVATIONS.** (a) §S3.2 = `.24`; (b) §S3.3 = `.25`; (c) and (d) §S4 = `.27`, `.28`; (e) and (f) §S5 = `HE6-ACCOUNT` = `.30`; (g) §S6.1 = `.31`. **Note the DAG shape: the statement package is one pin span, but its six proofs are distributed across four sections and two further pin spans.** T2 L3863 records exactly this: “The named suppliers are HE6's §S3.3 … §S4 … §S5 … and §S6.1”.

**Arithmetic audit of (a)'s degree bound.** `e₁ℓ | e(L_ρ)` and `f₁d_r | f(L_ρ)` give `[L_ρ:K₀] = e·f ≥ (e₁ℓ)(f₁d_r) = D′ℓd_r` ✓ — and this is exactly `N_r` of `.32`, which is why the sandwich there closes.

**CONDITIONALITY — one guard superseded.** **(c)'s guard “when δ has denominator dividing ℓ” is SUPERSEDED by `HE6-BETA-GUARD`** (`.56`), which re-scopes it to “when δ = κ”. **`HE6-BETA-GUARD` [1036,1047] is a separate pin span**, so a consumer pinning `HE6-TEST-PACKAGE` alone gets the unguarded statement; T2 handles this correctly — its r11 repair adds the guard pin and cites it “at both sites that lean on it” (T2 L4045), with L4086 recording “`HE6-TEST-PACKAGE`, read under `HE6-BETA-GUARD`”. **The two-pin conjunction is T2's own device and it works.** Recorded as the model for how the A3 gap of OPEN-CALL 2 should be closed.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-3`, count 15; `LEMMA HE3-4`, count 15. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-TEST-PACKAGE`, count 59.

---

### EFF.HE6.18  [theorem]

**CANONICAL STATEMENT** (verbatim, L289–301). FORM: display (blockquoted theorem with an indented conclusion).

> “**THEOREM HE6.A (HE3-BOX-6 CLOSED).** **[r1, R6/F7 + R2/F2: with
> disc f ≠ 0 and Φ′ ∤ f — the §S1 CONVENTION [r1]; the consuming site
> THEOREM HE3.A carries disc f ≠ 0 explicitly, so the composed program is
> unaffected]**, at a node of the stage read whose λ-side residual R_λ is
> separable,
>
>     |S_{λ,r}| = D′·ℓ·deg r    for every monic irreducible r | R_λ,
>
> at EVERY (ℓ, deg r) — in particular at ℓ ≥ 2 with deg R_λ ≥ 2, the
> configuration HE3-BOX-6 boxed; and each S_{λ,r} is the root set of a single
> monic irreducible factor of f over O with e = e₁ℓ, f = f₁ deg r. The proof
> uses NO base change; HE3-BOX-6's two under-argued branches are therefore
> SUPERSEDED rather than repaired (§S6.5).”

**DERIVATION** — `HE6-PROOF` [639,666] = `.32`.

**Arithmetic audit.** `e·f = (e₁ℓ)(f₁ deg r) = D′ℓ deg r = |S_{λ,r}|` ✓ — the class size equals the degree of the irreducible factor it is the root set of, which is what makes step 4 of `.32` close.

**CONDITIONALITY.** Three hypotheses: `disc f ≠ 0`, `Φ′ ∤ f` (both = `HE6-PEEL-CONVENTION`, `.09`), and **`R_λ` separable**. The separability hypothesis is **machine-certified sharp** by tooth HE6-T-CASEB (`.37`, `.52`): at a repeated residual the σ takes three distinct values over members with identical outer data, so no outer-data-only theorem can drop it. Grade at HEAD: **ACCEPTED 2/2** and ledger-**CERTIFIED**.

**XREF.** `HE3_PROOF_2026-08-08.md` — `THEOREM HE3.A`, count 17; `HE3-BOX-6`, count 12. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `THEOREM HE6.A`, count 14.

---

### EFF.HE6.19  [corollary]

**CANONICAL STATEMENT — struck form and replacement.**

**Struck** (verbatim, L303–309):

> “~~**COROLLARY HE6.B** … at every decided leaf **whose history contains no
> side with ℓ ≥ 2 carrying a REPEATED residual factor** …~~ **[r1, R1]
> STRUCK — the scope sentence was FALSE (Codex PE1 finding 1, upheld
> CRITICAL): an ℓ = 1 side carrying a repeated IRREDUCIBLE residual factor of
> degree ≥ 2 is equally undecided (no recentering exists there, because no
> element of the stage ring has residue β ∈ K(β) ∖ K), so the excluded set
> was not the complement of the separable hypothesis.** Replaced by:”

**Replacement — the effective form** (verbatim, L311–331):

> “**COROLLARY HE6.B [r1] (the program consequence, stated honestly).**
> THEOREM HE3.A and [GENHN-HE(μ)] hold at every μ and at every decided leaf
> **whose history contains no side carrying a repeated irreducible residual
> factor r with ℓ·deg r ≥ 2** (λ = u/ℓ in lowest terms) — equivalently, no
> **stage-CS event**: the only repeated configuration that stays inside this
> note plus HE3 is a repeated K-RATIONAL LINEAR factor at an INTEGER slope
> (ℓ = deg r = 1), which HE3's stage-α recentering handles (§S6.3). All four
> defects HE3 left at μ ≥ 4 (BOX-6's two branches, HE3-3's (SEP), HE3-0′'s
> ℓ ≥ 2 residue, PE1 finding 6) are closed. The excluded set is now EXACTLY
> the complement of the union of the two surviving node hypotheses
> (separable residual — THEOREM HE6.A; repeated K-rational linear factor at
> an integer slope — HE3 stage-α); the four-case enumeration is in
> `HE6R1_RECON_2026-08-08.md` §S2. Both branches first bite at the SAME
> n = 8 (a boxed side has L_λ ≥ m·ℓ·deg r ≥ 4, so μ ≥ 4 and n ≥ D′μ ≥ 8),
> and both are **machine-certified genuinely undecided by the outer data**:
> tooth HE6-T-CASEB (§S9, the ℓ = 2 branch) and tooth HE6R1-T-CRACK (the r1
> note's battery, the ℓ = 1 branch with deg r = 2) each exhibit THREE
> distinct PARI σ over members with identical outer data. They are
> HE6-BOX-1 in its WIDENED form (§S7.1 [r1]); **its exact residue (§S7.2) is
> now PROVED — see §S7.2 [r1]**. **n ≤ 7 is unaffected** by the widening
> (μ ≤ 3 is boxed-node-free, HE3.B).”

**SUPERSESSION KIND:** `replacement` — a FALSE scope sentence replaced. **CHAIN:** struck original → `[r1]` HE6.B. **TERMINAL: `[r1]`.**

**Arithmetic audit of the first-bite bound.** “a boxed side has `L_λ ≥ m·ℓ·deg r ≥ 4`” with multiplicity `m ≥ 2` and `ℓ·deg r ≥ 2` gives `L_λ ≥ 4` ✓; `L_λ ≤ μ` ✓; so `μ ≥ 4` and `n = D′μ ≥ 2·4 = 8` ✓ (using `D′ ≥ 2` for a composite stage, justified at `.20`).

**CONDITIONALITY.** The excluded set is now **exactly** the complement of two hypotheses, and both excluded branches are machine-certified undecided — so the exclusion is provably necessary, not a proof gap. The four-case enumeration lives in **another note** (`HE6R1_RECON_2026-08-08.md` §S2), so this corollary's completeness claim is a **composition claim across two notes**; `.39` says both are at attempt grade 0/2 at composition time.

**XREF.** `HE6R1_RECON_2026-08-08.md` — `HE6R1-T-CRACK`, count 2; EXISTS ✓. `HE3_PROOF_2026-08-08.md` — `THEOREM HE3.A`, count 17; `COROLLARY HE3.B`, count 8.

---

### EFF.HE6.20  [lemma]

**CANONICAL STATEMENT** (verbatim, §S2 L337–355). FORM: numbered display.

> “HE3-BOX-6 is the peel at a side with ℓ ≥ 2 **and** residual degree d ≥ 2.
> Three sharpenings, in order:
>
> 1. **The peel is needed only when the side carries ≥ 2 distinct labels.** If
>    R_λ = r is a single irreducible (possibly with multiplicity), every root
>    at that slope carries that one label, and LEMMA HE3-3 (slope counts)
>    already gives the class size D′L_λ. So the bite needs R_λ to have TWO
>    distinct irreducible factors, hence d = deg R_λ ≥ 2 with ℓd = L_λ ≤ μ.
> 2. **Hence μ ≥ 4**, and a composite stage needs D′ = e₁f₁ ≥ 2 (D′ = 1 makes
>    the stage read an order-1 read of the recentered polynomial), so
>    **n ≥ D′μ ≥ 8**: the bite is at n = 8, μ = 4, D′ = 2, ℓ = 2, d = 2, and
>    P(F) is the single side (0, 2u)–(4, 0) of slope λ = u/2 with u odd.
> 3. **The first prime depends on the genre.** Two distinct monic irreducible
>    factors of a degree-2 R_λ with R_λ(0) ≠ 0 means two distinct roots in
>    K^×, so |K^×| ≥ 2, i.e. Q^{f₁} ≥ 3. At (e₁,f₁) = (2,1) — genre (2,1,4) —
>    that is **q ≥ 3**; at (e₁,f₁) = (1,2) — genre (1,2,4), K = F_{q²} — it is
>    already live at **q = 2**. Predicted σ at the bite:
>    {(e₁ℓ, f₁), (e₁ℓ, f₁)} = **{(4,1),(4,1)}** at (2,1) (an octic splitting
>    into two totally ramified quartics) and **{(2,2),(2,2)}** at (1,2).”

**DERIVATION.** Three elementary sharpenings, each with its own warrant.

**Mandatory arithmetic audit (rule 22) — every number re-derived.** (1) `ℓ ≥ 2` and `d ≥ 2` give `L_λ = ℓd ≥ 4`, and `L_λ ≤ μ` ✓. (2) `μ ≥ 4`, `D′ ≥ 2` ⟹ `n = D′μ ≥ 8` ✓; at the bite `n = 2·4 = 8` ✓; the polygon `(0,2u)–(4,0)` has slope `2u/4 = u/2` ✓, in lowest terms iff `u` odd ✓. (3) Two distinct roots in `K^×` needs `|K^×| = Q^{f₁} − 1 ≥ 2`, i.e. `Q^{f₁} ≥ 3` ✓; at `(2,1)`, `K = F_q` so `q ≥ 3` ✓; at `(1,2)`, `K = F_{q²}` so `q² ≥ 3` holds at `q = 2` ✓. Predicted σ: `(e₁ℓ, f₁) = (2·2, 1) = (4,1)` twice ✓; `(1·2, 2) = (2,2)` twice ✓. **All of §S2 checks exactly** — and the `{(4,1),(4,1)}` prediction is what the 742 PARI jobs of `.50` confirm.

**CONDITIONALITY.** The `{(2,2),(2,2)}` prediction at `(1,2,4)` is **proof-only** — HE6-BOX-3 records `f₁ ≥ 2` as unexercised by machine (`.42`).

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-3`, count 15; `HE3-BOX-6`, count 12.

---

### EFF.HE6.21  [record]

**CANONICAL STATEMENT** (verbatim, §S2 L357–367). FORM: bulleted display plus a closing sentence.

> “Two neighbouring first-bites, for the record:
>
> * **HE3-3's (SEP)** first bites much later: three slopes inside one open
>   integer interval need denominators ≥ 2, 3, 4, hence μ ≥ 9, n ≥ 18. LEMMA
>   HE6-3 removes it at all μ anyway.
> * **HE6-BOX-1** (§S7) — an ℓ ≥ 2 side with a REPEATED residual factor,
>   R_λ = (Z−s)², ℓ = 2, L_λ = 4 = μ — bites at the SAME n = 8, and is exactly
>   GENHN-T(a)'s machine-fired (2,1,2)-in-(2,1,4) tower event.
>
> The machine rows of §S8 are built at this first bite: D′ = 2, μ = 4,
> Φ′ = x² − π, λ = 5/2, in both characteristics.”

**DERIVATION.** [RECORD].

**Arithmetic audit.** Three slopes with denominators `≥ 2, 3, 4` inside one open integer interval need total length `≥ 2 + 3 + 4 = 9`, so `μ ≥ 9` and `n ≥ D′μ ≥ 18` ✓. HE6-BOX-1's bite: `ℓ = 2`, `R_λ = (Z−s)²` so `d = 2`, `L_λ = ℓd = 4 = μ` ✓, `n = D′μ = 8` ✓ — **the same n = 8 as HE3-BOX-6's bite**, which is the note's point.

**CONDITIONALITY.** The machine rows are built at the bite, so the battery's coverage is exactly the first-live configuration and nothing deeper (`.42`).

**XREF.** `GENHN_PROOF_2026-08-08.md` — `GENHN-3`, count 21 (the T(a) tower tooth family lives in that note's battery; the specific designation `GENHN-T(a)` is cited descriptively here).

---

### EFF.HE6.22  [lemma]

**CANONICAL STATEMENT** — §S3.1, the proof of LEMMA HE6-0, with its `[r1]` R4/F5 re-proof. FORM: paragraph proof with an embedded struck passage.

Opening (verbatim, L375–381):

> “*Proof.* Φ′(ξ) = Π_{i=1}^{D′}(ξ − θ_i) with v(θ_i) = h/e₁ for all i.
> If v(ξ) < h/e₁ then v(ξ−θ_i) = v(ξ) for every i, so
> dv(Φ′(ξ)) = D′e₁v(ξ) = D′dv(ξ) < D′h. If v(ξ) > h/e₁ then v(ξ−θ_i) = h/e₁
> for every i and dv(Φ′(ξ)) = D′h. Let v(ξ) = h/e₁. If v(ξ−θ_i) > h/e₁ for
> some i then
> ξ^{e₁} − θ_i^{e₁} = (ξ−θ_i)·Σ_{k<e₁}ξ^kθ_i^{e₁−1−k} has
> v > h/e₁ + (e₁−1)h/e₁ = h, so η_ξ = η_{θ_i}, a root of ψ.”

The `[r1]` re-proof (verbatim, L383–405):

> “**[r1, R4/F5] The last two cases, RE-PROVED (the ψ-CANCELLATION route).**
> ~~"if (T2) fails then v(ξ−θ_i) = h/e₁ for all i …; η_ξ = η_{θ_i} for some i,
> whence v(ξ−θ_i) > h/e₁ for that i (the converse computation …)"~~ — STRUCK:
> equality of e₁-th-power residues does not imply proximity to that particular
> θ_i (Codex PE1 finding 5: at Φ′ = x²−π, ξ = −θ has η_ξ = η_θ but
> v(ξ−θ) = h/e₁ exactly). The conclusion is nevertheless TRUE, by the following
> argument, which never mentions proximity and disposes of BOTH remaining cases
> at once. Write Φ′ = x^{D′} + Σ_{i<D′}a_ix^i and assume (T1), i.e. dv(ξ) = h.
> Because Φ′ is irreducible with all roots of v = h/e₁, its own slot values
> satisfy e₁v(a_i) + i·h ≥ D′h for every i ≤ D′, with equality exactly at the
> slots **i = e₁t (t ≤ f₁)**: a pin lies on the line only if e₁ | (D′−i)h,
> i.e. (gcd(h,e₁) = 1) only if e₁ | D′−i, i.e. i ≡ 0 (mod e₁), since
> D′ = e₁f₁. So dv(Φ′(ξ)) ≥ D′h, and dividing the attaining terms by π^{f₁h}
> (of dv-value D′h) gives, by LEMMA HE6-0″,
>
>     res( Φ′(ξ)/π^{f₁h} ) = Σ_{t ≤ f₁} res(a_{e₁t}π^{−(f₁−t)h})·η_ξ^{t}
>                          = ψ(η_ξ) ,
>
> the middle expression being by definition the residual polynomial of Φ′ at
> its own single side, i.e. ψ — as the same computation at ξ = θ confirms
> (0 = Φ′(θ) gives ψ(η_θ) = 0). Hence if (T2) HOLDS then ψ(η_ξ) = 0, the
> attaining terms CANCEL, and dv(Φ′(ξ)) > D′h; and if (T1) holds but (T2)
> FAILS then ψ(η_ξ) ≠ 0 and dv(Φ′(ξ)) = D′h EXACTLY. ∎”

**DERIVATION.** The span is the derivation. Its structure: the two easy cases by ultrametric arithmetic, then a **single argument for both remaining cases** that routes through `LEMMA HE6-0″` (`.15`) and the residual polynomial of `Φ′` at its own side.

**Mathematical audit of the counter-instance and the replacement.** PE1 finding 5: at `Φ′ = x² − π` (so `e₁ = 2, f₁ = 1, h = 1`), `ξ = −θ` gives `ξ² = θ² = π`, so `η_ξ = res(ξ²π^{−1}) = 1 = η_θ` ✓, while `v(ξ − θ) = v(−2θ) = v(θ) = 1/2 = h/e₁` in odd residue characteristic ✓ — **the struck implication genuinely fails**. The replacement's divisibility step: `e₁v(a_i) + ih = D′h ⟹ e₁v(a_i) = (D′−i)h ⟹ e₁ | (D′−i)h ⟹ e₁ | (D′−i)` (as `gcd(h,e₁)=1`) `⟹ e₁ | i` (as `e₁ | D′`) ✓. And `dv(π^{f₁h}) = e₁f₁h = D′h` ✓. **Both halves check.**

**CONDITIONALITY.** **Corrected in one clause by A3 F-3** (`.60`): “with equality exactly at the slots i = e₁t” is read as “with equality **possible only** at the slots i = e₁t”, since the note's own justification proves only the “only if” direction. **The conclusion is unaffected** — A3 F-3 shows the residual display already zeroes out above-the-line slots via its normalizers.

**Compiler note on the circularity question.** This proof of `LEMMA HE6-0` invokes `LEMMA HE6-0″`, which is stated at (T1)/(T2) points. **No circularity:** HE6-0″'s hypotheses are (T1) and (T2), and the invocation here occurs after (T1) has been assumed and applies HE6-0″ to `A = Φ′` — whose slot structure is what is being read — with (T2) as the *case discriminant*, not as a prior hypothesis. Checked explicitly because the two lemma numbers are adjacent and the dependence runs backwards from the numbering.

**XREF.** none external.

---

### EFF.HE6.23  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S3.1 L407–412). FORM: italic-headed remark.

> “*Remark (why D′h and not S = e₁h).* HE3 and GENHN write the node threshold
> as S = e₁h. At f₁ = 1 — where every first-live case and every machine row of
> this program sits — D′h = e₁h = S and the two agree. At f₁ ≥ 2 the correct
> disk threshold is D′h = f₁S, and LEMMA HE6-3(a) *proves* that P(F) has no
> slope ≤ D′h, so nothing has to be assumed: the frame is exactly HE3-0's
> opening locus.”

**DERIVATION.** [RECORD of a convention reconciliation].

**Arithmetic audit.** `D′h = e₁f₁h = f₁·(e₁h) = f₁S` ✓; at `f₁ = 1`, `D′h = e₁h = S` ✓.

**CONDITIONALITY.** **This is a live divergence from two suppliers' conventions**, resolved in HE6's favour by proof rather than by assumption. A consumer importing HE3's or GENHN's `S = e₁h` threshold alongside HE6's `D′h` at `f₁ ≥ 2` would be importing two different numbers under one role. Flagged.

**XREF.** `HE3_PROOF_2026-08-08.md` — `LEMMA HE3-0`, count 7.

---

### EFF.HE6.24  [lemma]

**CANONICAL STATEMENT** — §S3.2, the proof of LEMMA HE6-0′ (verbatim, L416–424). FORM: paragraph proof.

> “*Proof.* e₁ | e(L_ρ) because v(ρ) = h/e₁ with gcd(h,e₁) = 1. Write
> e(L_ρ) = e₁e′. Then v(y_ρ) = λ/e₁ = u/(e₁ℓ) must lie in
> (1/e(L_ρ))ℤ = (1/e₁e′)ℤ, so e′u/ℓ ∈ ℤ and gcd(u,ℓ) = 1 forces ℓ | e′; hence
> e₁ℓ | e(L_ρ). For the residue degree: ρ, π ∈ L_ρ give η_ρ ∈ k_{L_ρ}, so
> ι_ρ(K) ⊆ k_{L_ρ}; and ϖ(ρ) ∈ L_ρ, so the element y_ρ^ℓ/ϖ(ρ)^u ∈ L_ρ has
> dv = ℓλ − u = 0, i.e. it is a unit of O_{L_ρ} and β_ρ ∈ k_{L_ρ}. Since β_ρ
> is a root of the irreducible ι_ρ(r) ∈ ι_ρ(K)[Z] we get
> [ι_ρ(K)(β_ρ) : F_Q] = f₁d_r, and a subfield degree of the finite field
> k_{L_ρ} divides f(L_ρ). ∎”

**DERIVATION.** The span is the derivation: a ramification argument for `e₁ℓ | e(L_ρ)` and a residue-field argument for `f₁d_r | f(L_ρ)`.

**Arithmetic audit.** `dv(y_ρ^ℓ/ϖ(ρ)^u) = ℓ·dv(y_ρ) − u·dv(ϖ(ρ)) = ℓλ − u·1 = ℓ(u/ℓ) − u = 0` ✓ (using `dv(ϖ(ξ)) = 1` from `.11`). `e′u/ℓ ∈ ℤ` with `gcd(u,ℓ) = 1` ⟹ `ℓ | e′` ✓. `[ι_ρ(K)(β_ρ) : F_Q] = [ι_ρ(K):F_Q]·[ι_ρ(K)(β_ρ):ι_ρ(K)] = f₁·d_r` ✓.

**CONDITIONALITY.** The clause “ϖ(ρ) ∈ L_ρ” uses only that `ϖ`'s coefficients lie in `K₀ ⊆ L_ρ` — **not** integrality, consistent with `.11` and with A3 F-4's later correction (`.61`). Recorded because this is the one *other* place `ϖ`'s coefficient ring is consumed, and here the note gets it right.

**XREF.** `HE3_PROOF_2026-08-08.md` — HE3-0′ is cited descriptively (it is the object being repaired, not a designation consumed).

---

### EFF.HE6.25  [lemma]

**CANONICAL STATEMENT** — §S3.3, the two-step proof of LEMMA HE6-1 (verbatim, L428–476). FORM: bold-headed steps with indented displays. Setup (L428–434):

> “Write Ψ := Ψ_{κ,r} = Σ_{t=0}^{d}B_tΦ′^{ℓt} with B_d := 1,
> dv(B_t) = (d−t)u for **every t < d with c_t ≠ 0** (and B_t = 0, dv = ∞, when
> c_t = 0), and recall κ = u/ℓ > D′h. **[r1, R8/F9]** every term-by-term
> exactness display below is read over the NONZERO terms; the endpoints t = 0
> (r(0) ≠ 0) and t = d (monic) are always nonzero, so every unique-minimum
> argument and every tie-residue sum is unaffected, and zero terms contribute
> 0 to the residual sum.”

Step 1's two case bounds and their conclusion (verbatim, L445–462):

> “Case dv(ξ) ≥ h. Then δ = D′h, the t = d term of Ψ(ξ) has
> dv = ℓdD′h exactly, and for t < d the term has
> dv ≥ (d−t)u + ℓtD′h > (d−t)ℓD′h + ℓtD′h = ℓdD′h, using u = ℓκ > ℓD′h. So
> the t = d term is the unique strict minimum and dv(Ψ(ξ)) = ℓdD′h < ∞:
> Ψ(ξ) ≠ 0.
>
> Case dv(ξ) < h. Then δ = D′dv(ξ), the t = d term has dv = ℓdD′dv(ξ)
> exactly, and for t < d the term has dv ≥ (d−t)u − (D′−1)ε + ℓtD′dv(ξ),
> whose excess over the t = d term is at least
>
>     (d−t)ℓ[κ − D′dv(ξ)] − (D′−1)ε
>       = (d−t)ℓ[(κ − D′h) + D′ε] − (D′−1)ε
>       ≥ ℓ(κ − D′h) + (ℓD′ − D′ + 1)ε  >  0,
>
> since ℓ ≥ 1 and κ > D′h. Again the t = d term is the unique strict minimum
> and Ψ(ξ) ≠ 0.
>
> So every root ξ of Ψ satisfies (T1)/(T2).”

Step 2's conclusion (verbatim, L474–476):

> “    0 = res( Ψ(ξ)/ϖ(ξ)^{du} ) = Σ_t ι_ξ(c_t)β_ξ^t = ι_ξ(r)(β_ξ). ∎”

**DERIVATION.** The span is the derivation. Step 1 rules out (T1)/(T2)-failing points by an ultrametric unique-minimum argument in two cases; Step 2 forces `δ = κ` and reads the residue.

**Mandatory arithmetic audit (rule 22) — Step 1's second case re-derived, since it is the load-bearing inequality.** With `ε := h − dv(ξ) > 0`, the excess is `(d−t)u − (D′−1)ε + ℓtD′dv(ξ) − ℓdD′dv(ξ) = (d−t)u − (D′−1)ε − (d−t)ℓD′dv(ξ) = (d−t)ℓ[κ − D′dv(ξ)] − (D′−1)ε` ✓. Now `κ − D′dv(ξ) = κ − D′(h − ε) = (κ − D′h) + D′ε` ✓. So the excess is `(d−t)ℓ[(κ−D′h) + D′ε] − (D′−1)ε ≥ ℓ[(κ−D′h) + D′ε] − (D′−1)ε` (using `d−t ≥ 1`) `= ℓ(κ−D′h) + (ℓD′ − D′ + 1)ε` ✓ **exactly the displayed line**, and this is `> 0` since `κ > D′h`, `ε > 0` and `ℓD′ − D′ + 1 = D′(ℓ−1) + 1 ≥ 1` ✓. **The chain is exact at every step.**

**CONDITIONALITY.** Conditional on `.14` (the family), `.15` (the slot lemma), `.16` (the disk criterion, which supplies `δ = D′·min(dv(ξ),h)` in Step 1), and the `[r1]` R8/F9 zero-term convention. Step 2's residue transport is “by GENHN-2's residue clause” — **so it inherits A3 F-1's normalizer correction** (`.58`), which explicitly states “the residue computations in LEMMA HE6-1, LEMMA HE6-2 and LEMMA HE6-2′ remain valid with this corrected formula”.

**XREF.** `GENHN_PROOF_2026-08-08.md` — `LEMMA GENHN-2`, count 2.

---

### EFF.HE6.26  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S3.3 L478–483). FORM: bold-headed remark.

> “**Remark (what Step 1–2 replace).** In Montes' development, "the roots of
> the order-2 key lie in the type's disk" is the content of Ore's theorem plus
> the theorem of the product at order 2. The two paragraphs above prove exactly
> the instance needed, from the SLOT LEMMA and the ultrametric inequality only,
> and they do NOT need Ψ irreducible — which is why no order-≥2 citation
> enters THEOREM HE6.A.”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** **This is the sentence that makes fence N-1(b) true**, and therefore the sentence that keeps the FGMN citation a target (`.40`) rather than a consumed input. It is the note's most load-bearing methodological claim and is worth a chapter cut's attention: the whole of THEOREM HE6.A is order-1 algebra plus resultant symmetry.

**XREF.** none.

---

### EFF.HE6.27  [lemma]

**CANONICAL STATEMENT** — §S4, the proof of LEMMA HE6-2 (verbatim, L489–502). FORM: italic-headed paragraph proof with an indented display.

> “*Proof of HE6-2.* Identical computation to Step 2 above, run at an arbitrary
> (T1)/(T2) point instead of at a root of Ψ: with δ := dv(Φ′(ξ)),
>
>     dv(B_t(ξ)Φ′(ξ)^{ℓt}) = (d−t)u + ℓtδ = ℓ[(d−t)κ + tδ]  (exactly),
>
> which is minimised uniquely at t = 0 when δ > κ (value ℓdκ), uniquely at
> t = d when δ < κ (value ℓdδ), and simultaneously at every t when δ = κ
> (common value ℓdκ, residue sum ι_ξ(r)(β)). The ultrametric inequality gives
> the min in the first two cases exactly, and in the third case gives
> dv = ℓdκ iff ι_ξ(r)(β) ≠ 0 and > ℓdκ iff ι_ξ(r)(β) = 0. Since
> min(δ,κ)·ℓd is the stated leading term in all three cases, the display
> follows. For a root ρ of f, δ = λ_ρ and β = β_ρ, and ι_ρ(r)(β_ρ) = 0 with r
> irreducible says precisely that r is the minimal polynomial of β_ρ over K
> transported by ι_ρ, i.e. r = r_ρ. ∎”

**DERIVATION.** The span is the derivation.

**Arithmetic audit of the three-case minimisation.** `(d−t)u + ℓtδ = ℓ[(d−t)κ + tδ]` using `u = ℓκ` ✓. As a function of `t`, `(d−t)κ + tδ = dκ + t(δ−κ)`: increasing in `t` iff `δ > κ` (min at `t = 0`, value `dκ`) ✓; decreasing iff `δ < κ` (min at `t = d`, value `dδ`) ✓; constant iff `δ = κ` (value `dκ`, all `t` tie) ✓. Times `ℓ`: `ℓd·min(δ,κ)` in all three cases ✓ — **exactly the stated leading term**.

**CONDITIONALITY.** **The `β` in the third case is guarded by `HE6-BETA-GUARD`** (`.56`): the statement's frozen guard “when δ has denominator dividing ℓ” is too broad, and the effective reading is “when δ = κ”. **This proof already works only in that case** — `β` is consulted solely in the `δ = κ` branch — so the guard correction is definitional, exactly as `.56` says.

**XREF.** none.

---

### EFF.HE6.28  [lemma]

**CANONICAL STATEMENT** — §S4, the proof of LEMMA HE6-2′ (verbatim, L504–515). FORM: italic-headed paragraph proof.

> “*Proof of HE6-2′.* f(ξ) = Σ_j A_j(ξ)y^j with dv(A_j(ξ)) = dv(A_j) exactly
> (SLOT LEMMA at ξ) and dv(y) = κ, so every term has dv = dv(A_j) + jκ and
> dv(f(ξ)) ≥ h_F(κ). The set of attaining j is the set of pins of P(F) on the
> supporting line of slope κ: a single vertex when κ is not a slope (so
> equality holds, no cancellation possible), and when κ = λ = u/ℓ is a slope
> with side [j₁, j₂] the attaining j all satisfy j ≡ j₁ (mod ℓ), since the
> λ-line height m₁ − λ(j−j₁) is an integer only then. Write j = j₁+tℓ and
> divide the sum by y^{j₁}ϖ(ξ)^{m₁} (of dv = j₁κ + m₁ = h_F(κ)): term t
> becomes [A_j(ξ)/ϖ(ξ)^{m₁−tu}]·[y^ℓ/ϖ(ξ)^u]^t, of residue (transport as
> above) ι_ξ(res(A_j(θ)/ϖ(θ)^{m₁−tu}))·β_ξ^t. Summing over t gives exactly
> ι_ξ(R_λ)(β_ξ) in the CONVENTION of §S1. Hence the excess is > 0 iff
> ι_ξ(R_λ)(β_ξ) = 0. ∎”

**DERIVATION.** The span is the derivation.

**Arithmetic audit.** The `mod ℓ` step: the λ-line height at abscissa `j` is `m₁ − λ(j − j₁) = m₁ − (u/ℓ)(j−j₁)`, an integer iff `ℓ | u(j−j₁)`, iff `ℓ | (j−j₁)` since `gcd(u,ℓ)=1` ✓. The normalizer `y^{j₁}ϖ(ξ)^{m₁}` has `dv = j₁κ + m₁` ✓, and at a pin on the supporting line `dv(A_{j₁}) = m₁`, so `h_F(κ) = m₁ + j₁κ` ✓. Term `t`'s normalized form: `A_j(ξ)y^j/(y^{j₁}ϖ^{m₁}) = [A_j(ξ)/ϖ^{m₁−tu}]·[y^{ℓ}/ϖ^{u}]^t` requires `ϖ^{m₁} = ϖ^{m₁−tu}·ϖ^{tu}` ✓ and `y^{j−j₁} = y^{tℓ} = (y^ℓ)^t` ✓. **Exact**, and the resulting residue sum is `R_λ` in §S1's convention ✓ (`.11`).

**CONDITIONALITY.** Consumes the SLOT LEMMA (`.15`) — hence A3 F-1's normalizer correction (`.58`), which names this lemma explicitly as remaining valid.

**XREF.** none.

---

### EFF.HE6.29  [lemma]  **[PIN: `HE6-ROOT-LABEL` [517,521]]**

**SPAN IDENTITY.** Lines **517–521**. First delimiter `**Corollary HE6-2″ (HE3-0(iii), re-proved in this convention).** Taking` — `grep -cFx` = **1**, at line 517. Last delimiter `of ρ; it is well defined because R_λ is a fixed element of K[Z].` — `grep -cFx` = **1**, at line 521. First precedes last ✓. **T2 consumption count: 26.** This is the **shortest** of the nine pin spans (5 lines) and the only one that is a plain paragraph rather than a blockquote.

**CANONICAL STATEMENT** (verbatim, the full span). FORM: bold-headed paragraph.

> “**Corollary HE6-2″ (HE3-0(iii), re-proved in this convention).** Taking
> ξ = ρ a root of f: 0 = f(ρ) forces the excess to be infinite, hence
> ι_ρ(R_{λ_ρ})(β_ρ) = 0 — every root's dv(Φ′(ρ)) is a slope and its β is a
> root of the ι_ρ-image of that side's residual polynomial. This is the label
> of ρ; it is well defined because R_λ is a fixed element of K[Z].”

**DERIVATION.** An immediate specialization of `.28` (LEMMA HE6-2′) to `ξ = ρ` a root of `f`: `f(ρ) = 0` makes `dv(f(ρ)) = ∞`, so the excess `δ(ξ)` is infinite, hence positive, hence `ι_ρ(R_λ)(β_ρ) = 0` by HE6-2′'s dichotomy ✓.

**CONDITIONALITY — and why this five-line span is pinned 26 times.** The span carries **the definition of a root's label** and, crucially, **its well-definedness**: “it is well defined because R_λ is a fixed element of K[Z]”. That clause is what makes `LEMMA HE6-5`'s Galois argument possible (`.31`: the label is “defined relative to the FIXED K-object r via the ROOT-DEPENDENT embedding ι_ρ”), and it is what T2 consumes — a label that is an object of `K[Z]`, not of the root's own residue field.

**Compiler note on the two consequences bundled here.** The span asserts two things a consumer may need separately: (i) **every** root's `dv(Φ′(ρ))` is a slope of `P(F)` (no root sits off the polygon), and (ii) its `β` is a root of that side's residual. (i) is what `HE6-ACCOUNT`'s `(†)` needs for exhaustiveness of the finite-label sum — and it is exactly what `HE6-PEEL-CONVENTION` (`.09`) is required for, since a root of `Φ′` would have `dv = ∞` and no slope. **The three pins `HE6-PEEL-CONVENTION`, `HE6-ROOT-LABEL` and `HE6-ACCOUNT` form a chain the DAG should carry as such.**

**XREF.** `HE3_PROOF_2026-08-08.md` — `LEMMA HE3-0`, count 7 (HE3-0(iii) is the object re-proved; cited descriptively as a clause of that lemma). `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-ROOT-LABEL`, count 26.

---

### EFF.HE6.30  [lemma]  **[PIN: `HE6-ACCOUNT` [525,604]]**

**SPAN IDENTITY.** Lines **525–604** — the whole of §S5. First delimiter `## S5. LEMMA HE6-3 (slope counts, (SEP)-free) AND LEMMA HE6-4 (nonemptiness)` — `grep -cFx` = **1**, at line 525. Last delimiter `what replaces HE3-BOX-6's base change.` — `grep -cFx` = **1**, at line 604. First precedes last ✓. **T2 consumption count: 55.** T2 L4192 characterizes it as “(HE6 §S5 [525,604], the proof unit of LEMMA HE6-3 and LEMMA HE6-4)” and records a **TRANSITIVE** consumption route through it. The span contains **five objects**: `(RES)`, the proof of HE6-3, the (SEP) remark, the proof of HE6-4, and the non-tautology remark.

**(a) `(RES)`, the resultant symmetry** (verbatim, L527–531):

> “Throughout, for monic f, g ∈ O[x] the resultant symmetry gives
>
>     (RES)   Σ_{ρ : f(ρ)=0} dv(g(ρ)) = e₁·v(±Res(f,g)) = Σ_{ξ : g(ξ)=0} dv(f(ξ)),
>
> sums over roots with multiplicity in K̄₀ (disc f ≠ 0 makes f's roots simple).”

**(b) The proof of LEMMA HE6-3** (verbatim, L533–571), whose `(†)` display is the note's central identity:

> “    (†)   Σ_λ n_λ·min(λ, κ) = D′·h_F(κ) = D′·Σ_λ L_λ·min(λ, κ),”

with its two parts:

> “(a) Every root ρ has λ_ρ = dv(Φ′(ρ)) > D′h (LEMMA HE6-0 applied to HE3-0's
> (T1)/(T2)), so n_λ = 0 for any slope λ ≤ D′h. Let λ₁ < … < λ_m be the slopes
> > D′h and put c_λ := n_λ − D′L_λ, c₀ := −D′Σ_{λ ≤ D′h}L_λ·λ. Then (†) reads
> c₀ + Σ_{i}c_{λ_i}min(λ_i, κ) = 0 for all rational κ > D′h. Taking κ in the
> (nonempty, rational-point-containing) interval (D′h, λ₁) makes every
> min(λ_i,κ) = κ, so c₀ + (Σc_{λ_i})κ ≡ 0 there, forcing Σ_i c_{λ_i} = 0 and
> **c₀ = 0**; as all slopes are > 0 this gives L_λ = 0 for every λ ≤ D′h,
> i.e. P(F) has no such slope.
>
> (b) With c₀ = 0, (†) becomes Σ_i c_{λ_i}min(λ_i,κ) = 0 for all rational
> κ > D′h. Sampling κ in the gaps (λ_i, λ_{i+1}) — always nonempty in ℚ, which
> is exactly what integer sampling could not guarantee — and running the
> triangular elimination from the largest slope down gives c_{λ_i} = 0 for all
> i, i.e. n_λ = D′L_λ. ∎”

**(c) The (SEP)-death remark** (verbatim, L573–579):

> “**Remark (how the (SEP) counterexample dies).** Codex's PE1 counterexample to
> HE3-3 was three slopes S+1/4, S+1/3, S+1/2 inside one open integer interval:
> every INTEGER sample sees them as three constants and the 3×3 system drops
> rank. Fractional sampling puts κ between any two slopes, so the breakpoint
> structure is visible and the elimination is triangular again. This is the
> same mechanism as the peel: the enlarged family reaches heights the old one
> could not.”

**(d) The proof of LEMMA HE6-4** (verbatim, L581–594), whose engine is the strictness transfer:

> “Comparing, Σ_{ρ ∈ S_{λ,r}}ε(ρ) > 0 with every ε(ρ) > 0; in particular the
> sum is over a NONEMPTY set. ∎”

**(e) The non-tautology remark** (verbatim, L596–604):

> “**Remark (why this is not the tautology it looks like).** (RES) is symmetric,
> so it cannot by itself pin any class size: writing both sides as
> Σ_{ρ,ξ}e₁v(ρ−ξ) shows the two computations are the same double sum. The
> content is that the two sides are evaluated by DIFFERENT lemmas: the ξ-side
> strictly exceeds the generic value for a reason internal to the stage data
> (r | R_λ makes the residual cancel at ξ — LEMMA HE6-2′), while the ρ-side is
> generic unless the class is inhabited (LEMMA HE6-2). The strict inequality
> therefore *transfers* from the stage side to the root side. That transfer is
> what replaces HE3-BOX-6's base change.”

**DERIVATION.** (b) and (d) are the derivations; (a) is the shared tool; (c) and (e) are the two remarks that make the mechanism legible. **(e) is the single most important paragraph in the note for a reader deciding whether the argument is circular**, and it answers the objection head-on.

**Mandatory arithmetic audit (rule 22).** **(b)(a)'s sampling step:** on `(D′h, λ₁)` every `min(λ_i,κ) = κ`, so `(†)` reads `c₀ + (Σc_{λ_i})κ = 0` identically in `κ` on an interval containing infinitely many rationals ⟹ both coefficients vanish ✓. **(b)(b)'s triangular elimination:** sampling `κ ∈ (λ_i, λ_{i+1})` gives `Σ_{j≤i} c_{λ_j}λ_j + κΣ_{j>i}c_{λ_j} = 0`; taking two rationals in the gap forces `Σ_{j>i}c_{λ_j} = 0` and `Σ_{j≤i}c_{λ_j}λ_j = 0`; descending from `i = m−1` gives `c_{λ_m} = 0`, then `c_{λ_{m−1}} = 0`, and so on ✓ — **the elimination is genuinely triangular**, and it is fractional sampling that makes each gap nonempty. **(d)'s comparison:** ξ-side `> D″h_F(λ)`; ρ-side `= D″h_F(λ) + Σ_{S_{λ,r}}ε(ρ)`; equality of the two sides by `(RES)` forces `Σε > 0` ✓, hence `S_{λ,r} ≠ ∅` ✓ — and the ρ-side's `ℓd_r·D′h_F(λ) = D″h_F(λ)` uses `D″ = D′ℓd_r` ✓.

**CONDITIONALITY — one clause superseded, and it is outside every pin span.** **A3 F-2** (`.59`) replaces the inference “`c₀ = 0`; as all slopes are `> 0` this gives `L_λ = 0` for every `λ ≤ D′h`” by a length argument, because `c₀ = −D′Σ_{λ≤D′h}L_λ·λ = 0` **cannot exclude a zero-slope side**. **A3 F-2 lies at L1115–1154, outside `HE6-ACCOUNT` [525,604] and outside every other pin span** — the same gap as at `.15`. See OPEN-CALL 2.

**T2 consumption note — the transitive route.** T2 L4192 records: “One further route is TRANSITIVE, through the pinned span `HE6-ACCOUNT` (HE6 §S5 [525,604], the proof unit of LEMMA HE6-3 and LEMMA HE6-4), whose text invokes …”. So T2 consumes this span not only directly but as a *conduit* for a correction it cites elsewhere — which makes the A3 F-2 gap doubly consequential.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-3`, count 15; `HE3-BOX-6`, count 12. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-ACCOUNT`, count 55.

---

### EFF.HE6.31  [lemma]

**CANONICAL STATEMENT** — §S6.1, the proof of LEMMA HE6-5 (verbatim, L612–637). FORM: italic-headed paragraph proof with two indented displays, plus a bold-headed “What this repairs”.

> “*Proof.* Let g ∈ Gal(K̄₀/K₀) and let ρ be a root of f with label (λ, r). All
> of Φ′, ϖ ∈ O[x] have g-fixed coefficients, so Φ′(gρ) = g(Φ′(ρ)) = g(y_ρ) and
> ϖ(gρ) = g(ϖ(ρ)); v is g-invariant (uniqueness of the extension of v to K̄₀),
> so dv(Φ′(gρ)) = λ, i.e. gρ sits at the same slope. g maps O_{K̄₀} onto
> itself and induces ḡ ∈ Gal(k̄/F_Q) on residues, so
>
>     η_{gρ} = res( (gρ)^{e₁}π^{−h} ) = ḡ(η_ρ),
>     β_{gρ} = res( Φ′(gρ)^{ℓ}/ϖ(gρ)^{u} ) = ḡ(β_ρ).
>
> Since ι_ρ is the F_Q-embedding K → k̄ with η_θ ↦ η_ρ, the composite ḡ∘ι_ρ is
> an F_Q-embedding with η_θ ↦ ḡ(η_ρ) = η_{gρ}, i.e. **ι_{gρ} = ḡ∘ι_ρ**.
> Therefore
>
>     ι_{gρ}(r)(β_{gρ}) = (ḡ∘ι_ρ)(r)(ḡ(β_ρ)) = ḡ( ι_ρ(r)(β_ρ) ) = ḡ(0) = 0,
>
> so gρ has label (λ, r) with the same r ∈ K[Z], and S_{λ,r} is
> Galois-stable. ∎”

> “**What this repairs.** HE3 §S6.3 flagged (PE1 finding 6) that its Galois
> stability sentence was under-argued — the absolute Galois group does not fix
> the embedded copy of K and could a priori carry r to a Frobenius conjugate,
> leaving the class sizes readable only up to Frobenius grouping (and HE3
> retreated to f₁ = 1, where the battery lives). The two displays above are
> exactly the missing composition: the label is defined relative to the FIXED
> K-object r via the ROOT-DEPENDENT embedding ι_ρ, and the two twists cancel
> because ι_{gρ} = ḡ∘ι_ρ.”

**DERIVATION.** The span is the derivation: the key identity is `ι_{gρ} = ḡ∘ι_ρ`, from which `ι_{gρ}(r)(β_{gρ}) = ḡ(ι_ρ(r)(β_ρ))` follows because `r`'s coefficients are `g`-independent (they live in the fixed `K`) and `ḡ` is a ring homomorphism ✓.

**⚠ SUPERSEDED (one clause) — and the note contradicted itself here for four rounds.** “All of Φ′, ϖ ∈ O[x] have g-fixed coefficients” is **SUPERSEDED by A3 F-4** (`.61`), read as “The polynomial Φ′ ∈ O[x] and the normalizer ϖ ∈ K₀[x] both have g-fixed coefficients.” **The `[r1]` R7/F8 convention at L106–107 says the opposite of the frozen sentence** — “**ϖ ∈ K₀[x], not O[x]**”, with the witness `ϖ = xπ^{−1}` — so the note carried an internal contradiction from `[r1]` through PE1, PE2, PE3 and PE4, caught only by the decorrelated A3 read. **SUPERSESSION KIND:** `replacement`. **The conclusion is unaffected:** A3 F-4's own words, “No integrality of the coefficients of ϖ is used”, and `.24` independently confirms that the *other* consumption of `ϖ`'s coefficient ring gets it right.

**CONDITIONALITY.** The lemma removes HE3's `f₁ = 1` retreat entirely — “at every f₁ (no f₁ = 1 restriction)”. **But the machine leg is `f₁ = 1` only** (`.42`: “NOT exercised by machine: f₁ ≥ 2 stage genres”), so the removal is proof-only. Flagged.

**XREF.** `HE3_PROOF_2026-08-08.md` — `THEOREM HE3.A`, count 17 (§S6.3 there is the flagged site).

---

### EFF.HE6.32  [lemma]  **[PIN: `HE6-PROOF` [639,666]]**

**SPAN IDENTITY.** Lines **639–666**. First delimiter `### S6.2 PROOF OF THEOREM HE6.A` — `grep -cFx` = **1**, at line 639. Last delimiter `histories containing an ℓ ≥ 2 side with a repeated residual factor.` — `grep -cFx` = **1**, at line 666. First precedes last ✓. **T2 consumption count: 66 — the most-consumed HE6 pin.** T2 L3123 records its own independent verification: “`grep -cFx` returned **1** for each of the two lines; the first (line 639) precedes the last (line 666); the span contains the four numbered steps of the proof, its ∎, …”. **T2's line numbers reproduce exactly at HEAD.**

**CANONICAL STATEMENT** (verbatim, the full span). FORM: `###` heading plus a numbered four-step proof plus a bold closing sentence.

> “### S6.2 PROOF OF THEOREM HE6.A
>
> Let λ = u/ℓ be a slope with R_λ separable, R_λ = Π_{r}r over the distinct
> monic irreducible factors, and put N_r := D′ℓd_r, d_r := deg r.
>
> 1. **The classes partition the slope's roots.** Every ρ with λ_ρ = λ has
>    ι_ρ(R_λ)(β_ρ) = 0 (COROLLARY HE6-2″), and R_λ separable means β_ρ is a
>    root of exactly one factor's image, so the S_{λ,r} are disjoint with union
>    {ρ : λ_ρ = λ}. By LEMMA HE6-3, Σ_r|S_{λ,r}| = n_λ = D′L_λ = D′ℓΣ_rd_r =
>    Σ_r N_r.
> 2. **Each class is nonempty** (LEMMA HE6-4) **and Galois-stable** (LEMMA
>    HE6-5), and each of its members ρ has [L_ρ : K₀] ≥ N_r (LEMMA HE6-0′).
>    Hence S_{λ,r} contains the full Galois orbit of any of its elements, so
>    |S_{λ,r}| ≥ N_r.
> 3. **The sandwich closes.** Σ_r|S_{λ,r}| = Σ_rN_r with |S_{λ,r}| ≥ N_r for
>    every r forces |S_{λ,r}| = N_r = D′ℓd_r for every r.
> 4. **Each class is one irreducible factor.** |S_{λ,r}| = N_r and every member
>    has degree ≥ N_r over K₀, so S_{λ,r} is a single Galois orbit of size
>    exactly N_r, i.e. the root set of one monic irreducible factor g_r | f of
>    degree N_r. Its invariants satisfy e(g_r) ≥ e₁ℓ and f(g_r) ≥ f₁d_r
>    (LEMMA HE6-0′) with e·f = N_r = (e₁ℓ)(f₁d_r), forcing
>
>        e(g_r) = e₁ℓ = e₁e_s ,   f(g_r) = f₁d_r = f₁f_s   exactly. ∎
>
> **This is HE3's LEMMA HE3-4 in full generality**, so HE3's THEOREM HE3.A
> assembly (§S6.3 there: base read + stage-α + stage-CS + embedded genres) may
> be run with HE3-4 replaced by THEOREM HE6.A — with the one caveat of §S7 for
> histories containing an ℓ ≥ 2 side with a repeated residual factor.”

**DERIVATION.** The span is the derivation — a four-step sandwich. **Its input list is exactly five earlier units**, four of which are inside other pin spans: `COROLLARY HE6-2″` = `HE6-ROOT-LABEL` (`.29`), `LEMMA HE6-3` and `LEMMA HE6-4` = statements in `HE6-TEST-PACKAGE` (`.17`) proved in `HE6-ACCOUNT` (`.30`), `LEMMA HE6-5` = `.17`(g) proved at `.31`, `LEMMA HE6-0′` = `.17`(a) proved at `.24`. **The DAG shape is therefore: `HE6-PROOF` ← {`HE6-ROOT-LABEL`, `HE6-TEST-PACKAGE`, `HE6-ACCOUNT`} ∪ {§S6.1, §S3.2}**, and the last two are in no pin span. Recorded for OPEN-CALL 1.

**Mandatory arithmetic audit (rule 22) — the sandwich, step by step.** Step 1: `n_λ = D′L_λ` (HE6-3(b)) and `L_λ = ℓ·deg R_λ = ℓΣ_r d_r` for separable `R_λ` ✓, so `Σ_r N_r = Σ_r D′ℓd_r = D′ℓΣ_r d_r = D′L_λ = n_λ` ✓. Step 2: each class is nonempty and Galois-stable, and each member has degree `≥ N_r`, so the class contains a full orbit of size `≥ N_r`, giving `|S_{λ,r}| ≥ N_r` ✓. Step 3: `Σ|S| = ΣN` with `|S| ≥ N` termwise forces equality termwise ✓ — **this is the whole argument and it is valid**. Step 4: `e·f = N_r` with `e ≥ e₁ℓ`, `f ≥ f₁d_r` and `(e₁ℓ)(f₁d_r) = e₁f₁ℓd_r = D′ℓd_r = N_r` forces both inequalities to be equalities ✓.

**CONDITIONALITY.** `R_λ` separable (sharp, `.37`); plus `.09`'s two standing hypotheses; plus the four input lemmas. **The closing sentence is the composition claim the whole program rests on** — HE3's assembly runs with HE3-4 replaced by HE6.A — and it carries its own caveat (§S7, the widened box).

**T2 consumption note.** T2 L3015 and L3107 record `HE6-PROOF` as one of four pins that jointly certify T2's `(MP1′)` assertion (i)–(vii), retiring an obligation T2 had named on the ground that “no pinned unit certifies” it. T2 L3872 records a further consumption: “Supplier: item 1 of THEOREM HE6.A's proof, **HE6:644–648**, already inside the existing `HE6-PROOF` span [639,666]” — **a sub-span citation**, verified here: L644–648 is exactly step 1 ✓.

**XREF.** `HE3_PROOF_2026-08-08.md` — `LEMMA HE3-4`, count 15; `THEOREM HE3.A`, count 17. `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-PROOF`, count 66.

---

### EFF.HE6.33  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S6.3 L670–676). FORM: `###`-headed paragraph.

> “At a node where R_λ has a repeated factor Z − s with s ∈ K (so ℓ_λ = 1 is
> not required by anything above), LEMMA HE6-4 still gives S_{λ,Z−s} ≠ ∅ and
> LEMMA HE6-3 still gives the slope total; the class size D′m_s used by HE3's
> stage-α step comes from HE3-2(b) + HE3-3 exactly as before (the recentered
> key Φ′ + ŝϖ^{λ} exists because λ ∈ ℤ there). Nothing in HE6 changes that
> step; what HE6 changes is that the peel no longer needs λ ∈ ℤ **when the
> residual is separable**.”

**DERIVATION.** [RECORD of a scope boundary].

**CONDITIONALITY.** This is the sentence that makes `COROLLARY HE6.B`'s excluded set exactly right: the repeated **K-rational linear at integer slope** case is handled by HE3's stage-α, so it is *not* in the box; everything else repeated with `ℓ·deg r ≥ 2` is.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-2(b)`, count 14; `HE3-3`, count 15.

---

### EFF.HE6.34  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S6.4 L680–685). FORM: `###`-headed paragraph.

> “At μ ≤ 3 every side with ℓ ≥ 2 has d = 1, so THEOREM HE6.A's conclusion
> |S| = D′ℓ agrees with HE3-4's rational-peel-plus-subtraction argument, and at
> μ = 2 with GENHN.C's dictionary. HE6 therefore contains HE3's μ ≤ 3 result as
> a special case, re-derived without the subtraction step — a second,
> independent route to the μ ≤ 3 statement HE3 proved (an internal
> decorrelation, not an external one).”

**DERIVATION.** [RECORD of a cross-check].

**Arithmetic audit.** At `μ ≤ 3`, a side with `ℓ ≥ 2` has `L_λ = ℓd ≤ μ ≤ 3`, so `ℓ ≥ 2` forces `d = 1` ✓. Then `|S| = D′ℓ·1 = D′ℓ` ✓.

**TEETH disposition (rule 20).** `accepted-with-decorrelation-supplied` — but **internal**, and the note says so explicitly: “an internal decorrelation, not an external one”. Recorded because the honest self-labelling is exactly what rule 20's vocabulary is for.

**XREF.** `HE3_PROOF_2026-08-08.md` — `LEMMA HE3-4`, count 15.

---

### EFF.HE6.35  [changes-record]

**CANONICAL STATEMENT** (verbatim, §S6.5 L689–712 — the verdicts on HE3-BOX-6's two branches). FORM: bulleted display with per-branch verdicts.

> “* **Branch (i) — unramified base change for non-K-rational residual factors
>   (HE3 §S6.2(i)).** *Verdict: SUPERSEDED — the conclusion is PROVED without
>   it.* THEOREM HE6.A gives |S_{λ,r}| = D′ℓ deg r for r of any degree with no
>   base change at all: the test polynomial Ψ_{λ,r} is built from r itself
>   (its coefficients are lifted by (LIFT)), so no letters over an enlarged
>   residue field are needed. Codex PE1's finding 1 — that under an unramified
>   base change of degree c the key Φ′ splits into gcd(f₁,c) factors, the stage
>   key degree drops to D′/gcd(f₁,c), and "each rational residual root
>   contributes D′ roots" is false as written — is correct and now moot: HE6
>   never changes the base.
> * **Branch (ii) — ramified base change O ↝ O[Π]/(Π^ℓ − π) for ℓ ≥ 2 (HE3
>   §S6.2(ii)).** *Verdict: SUPERSEDED — the conclusion is PROVED without it.*
>   HE3's own review had already found the fatal defect (Φ′ need not stay
>   irreducible, so the stage ring need not stay a DVR and both the SLOT LEMMA
>   and the norm computation are unavailable on the far side), and PE1 added
>   three more (dv-rescaling does not multiply a cardinality; the label can
>   split into several integer-slope labels; char K | ℓ can make the new
>   residual inseparable). All four are avoided: LEMMA HE6-1's roots ξ live in
>   K̄₀ over the ORIGINAL O, the height λ = u/ℓ stays fractional, and the only
>   algebraic inputs are the SLOT LEMMA and the ultrametric inequality, both
>   characteristic-free.
> * **Also closed:** HE3-3's (SEP) hypothesis (LEMMA HE6-3), HE3-0′'s
>   nonexistent n(λ) at ℓ ≥ 2 (LEMMA HE6-0′), and HE3's PE1 finding 6
>   (LEMMA HE6-5).”

**DERIVATION.** [RECORD of two verdicts on another note's boxes].

**SUPERSESSION KIND (outbound):** `replacement` of HE3-BOX-6's two branches — but note the note's own careful word: **SUPERSEDED, not repaired.** The distinction is load-bearing: HE6 does not fix the base-change arguments, it makes them unnecessary. A consumer must not cite HE6 as validating either branch.

**CONDITIONALITY.** **This is a cross-note status claim about HE3** and per rule 10 it is checked against HE3's full append chain. `grep -cF 'HE3-BOX-6' HE3_PROOF_2026-08-08.md` = **12** — the box is still present and named in HE3 at HEAD. **HE6 does not edit HE3**, so HE3's own text still carries the box; the supersession lives in HE6 and in whatever consumer chooses to read HE3's assembly with HE6.A substituted (`.32`'s closing sentence). Recorded so no one reads “SUPERSEDED” as “removed from HE3”.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE3-BOX-6`, count 12; `HE3-3`, count 15.

---

### EFF.HE6.36  [hypothesis-box]

**CANONICAL STATEMENT** — §S7.1's `[r1]` widening (verbatim, L720–732) and the box body (L735–751). FORM: `###` heading plus a blockquoted widening plus prose.

> “**[r1, R1] THE BOX IS WIDER THAN THIS SECTION ORIGINALLY SAID.** Codex PE1
> finding 1 (upheld CRITICAL) showed that an ℓ = 1 side with a repeated
> IRREDUCIBLE residual factor of degree d_r ≥ 2 belongs here too: HE3's
> stage-α recentering needs a residual root IN K, so it is unavailable at
> d_r ≥ 2, and THEOREM HE6.A needs separability. The box is therefore
> **{a side carrying a repeated irreducible residual factor r with
> ℓ·deg r ≥ 2}**, with two branches — (ℓ ≥ 2, d_r ≥ 1), the configuration
> this section describes, and (ℓ = 1, d_r ≥ 2). Both first bite at n = 8;
> both are machine-certified undecided by the outer data (HE6-T-CASEB here,
> HE6R1-T-CRACK in the r1 note). Everything below is the ℓ ≥ 2 branch; the
> ℓ = 1 branch is the same statement with the RESIDUE direction
> (K-independence of {1, β, …, β^{d_r−1}}) doing the work that gcd(u,ℓ) = 1
> does here — `HE6R1_RECON_2026-08-08.md` §S3.”

and the body's diagnosis of why HE3's two treatments both fail (L735–751), whose second bullet is the substantive one:

> “* as a *stage-CS event* with inner data (e₁′,f₁′,μ′) = (ℓ, 1, m) — HE3 then
>   applies THEOREM HE3.A recursively over the base ring R. That step supplies
>   the FORCING half ((T1)/(T2) stack ⟹ divisibility of e and f) but NOT the
>   counting half: the recursion computes the factorization of the resolvent
>   F over R, whose roots are not roots of f (Y ↦ Φ′ is not a ring map), so the
>   inner class SIZES are not transported. HE3's own text says the composition
>   holds "because (T1)/(T2) stack", which is the forcing statement only.”

**DERIVATION.** [RECORD of an open obligation] with a precise diagnosis: the recursion transports *forcing* but not *counting*, because `Y ↦ Φ′` is not a ring map.

**SUPERSESSION KIND (the widening):** `scope-pin` — the box is widened, not replaced; its ℓ ≥ 2 content is unchanged and a second branch is added. **TARGETS:** `.19` (COROLLARY HE6.B's excluded set, which is stated in the widened form).

**CONDITIONALITY.** **The box is the note's one surviving open obligation.** Its ℓ = 1 branch is handled in **another note** (`HE6R1_RECON_2026-08-08.md` §S3), so the box's own statement is split across two files — recorded because a chapter cut of HE6 alone gets only half the box.

**XREF.** `HE6R1_RECON_2026-08-08.md` — `HE6R1-T-CRACK`, count 2; `HE6-BOX-1`, count 3; EXISTS ✓. `HE7_PROOF_2026-08-08.md` — `HE6-BOX-1`, count 11.

---

### EFF.HE6.37  [run-record]

**CANONICAL STATEMENT** (verbatim, §S7.1 L753–758). FORM: bold-headed paragraph.

> “**The box is real, and machine-certified.** Tooth HE6-T-CASEB (§S8) exhibits,
> at p = 5, μ = 4, λ = 5/2, R_λ = (Z−1)², members with **identical outer data**
> (same polygon, same residual polynomial) whose PARI σ takes **three
> different** values — {(8,1)}, {(4,1),(4,1)}, {(4,2)}. So no argument from
> the outer data alone can close it: a deeper read is mathematically necessary.
> (This also retro-certifies THEOREM HE6.A's separability hypothesis as sharp.)”

**DERIVATION.** [RECORD of an executed instrument's decisive result].

**TEETH disposition (rule 20).** This is the rare case of a tooth that **certifies an obligation as real** rather than certifying a claim as true. Its logical force: since three distinct σ arise from identical outer data, **no** theorem about the outer data can determine σ at a repeated residual — so HE6-BOX-1 is not an unfinished argument but a genuine mathematical obligation, and THEOREM HE6.A's separability hypothesis cannot be dropped.

**Arithmetic audit against `.50`'s table.** At `ℤ_5, λ = 5/2, ALPHA2`: `{(8,1)} 176 · {(4,2)} 11 · {(4,1),(4,1)} 13` — **three values** ✓, summing to `200` = that row's PARI count ✓. The same three-valuedness holds at all four char-0 ALPHA2 rows ✓ (`.50`).

**CONDITIONALITY.** Char-0 rows only (HE6-BOX-4, `.43`). The char-p rows run identities only.

**XREF.** none.

---

### EFF.HE6.38  [scope-record]

**CANONICAL STATEMENT** — §S7.2, the exact residue and the two missing inputs (verbatim, L762–795, condensed to its two named obligations and the closing fence; the intervening development is quoted at its own lines). The two obligations:

> “* **(LIFT₂)** for every level-2 height k ∈ ℤ **at or above the level-2
>   threshold [r2, PE2 F-5: the threshold conditional is part of the wish —
>   HE7 §S4.2 proves (LIFT₂) under its (†₂)/(‡₂) bounds and shows the
>   sub-threshold failure is GENUINE (the R3/HE6-1L defect one level up), so
>   the unconditional quantifier this display carried pre-r2 is false below
>   threshold]** and every c ∈ K₂^× (K₂ := the level-2 residue field, K itself
>   when d_r = 1) there is C ∈ O[x] with deg C < D″, level-2 dv-value k, and
>   level-2 residue c. (This is (LIFT) one order up: the level-2 slots are the
>   pairs (Φ′-power, x-power); the surjectivity claim is the only
>   combinatorial content.)
> * **(SLOT₂)** the level-2 evaluation dichotomy: for C as above and ρ in the
>   Ψ-disk, dv(C(ρ)) equals the level-2 minimum exactly, unless the level-2
>   residual polynomial vanishes at ρ's level-2 residue.”

and the fence (L792–795):

> “Everything else in §S3–S6 transfers by substituting (Φ′, D′h, κ) ↦
> (Ψ, ℓdλ, κ₂). **This note does not prove (LIFT₂)/(SLOT₂)**; consequently
> [GENHN-HE(μ)] is claimed here only at leaves whose histories avoid the boxed
> configuration (COROLLARY HE6.B [r1]).”

**DERIVATION.** [RECORD of two named open inputs] plus a transfer claim.

**SUPERSESSION KIND (the `[r2]` bracket):** `scope-pin` — an unconditional quantifier is confined to at-or-above threshold, because HE7 shows the sub-threshold failure is **genuine**, i.e. the same defect as `.12`/`.13` one level up. **TERMINAL: `[r2]`.**

**CONDITIONALITY.** The transfer claim (“Everything else in §S3–S6 transfers by substituting…”) is **asserted, not carried out** in this note. It is carried out in HE7 and audited there (`.39`: “together with the transfer audit”). Recorded as a justification seam of HE6, discharged elsewhere.

**XREF.** `HE7_PROOF_2026-08-08.md` — `HE6`, count 209; EXISTS ✓.

---

### EFF.HE6.39  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S7.2 L797–806). FORM: display (blockquoted status note).

> “**[r1] STATUS OF THIS RESIDUE: PROVED ELSEWHERE.** (SLOT₂) and (LIFT₂) are
> proved in `HE7_PROOF_2026-08-08.md` §S3–S4 (with the level-1 (LIFT)
> threshold corrected — the same defect as R3), together with the transfer
> audit, the ladder at every level, and its TERMINATION; and
> `HE6R1_RECON_2026-08-08.md` §S3 proves that HE7's machinery covers the
> WIDENED box, the ℓ = 1 branch being a LITERAL INSTANCE of HE7's statements,
> plus the three lemmas the composition needs (HE6R1-1, the widened jump
> condition with HE7.C's own bounds; HE6R1-2, block projection; HE6R1-3, the
> level-2 peel). Both suppliers are at attempt grade 0/2, so this is a
> composition claim, not an acceptance.”

**DERIVATION.** [RECORD of a composition claim].

**CONDITIONALITY — the honest label is the note's own.** “Both suppliers are at attempt grade 0/2, so this is a composition claim, not an acceptance.” **That grade statement is stale at HEAD** for at least the HE6R1 side and possibly HE7's; this compilation does not re-adjudicate either supplier's arc, but the compiled HE6R1 spec (queue 8b entry 4) does. Flagged as an as-of record.

**The three named HE6R1 lemmas are grep-verified:** `HE6R1-1` count 15, `HE6R1-2` count 13, `HE6R1-3` count 10 in `HE6R1_RECON_2026-08-08.md` ✓ — **all three exist as designations**, so the composition's parts are addressable.

**XREF.** `HE7_PROOF_2026-08-08.md` — EXISTS ✓, `LEMMA HE7-L1` count 12. `HE6R1_RECON_2026-08-08.md` — `HE6R1-1` 15, `HE6R1-2` 13, `HE6R1-3` 10.

---

### EFF.HE6.40  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S7.3 L810–826). FORM: `###`-headed paragraph.

> “(LIFT₂)/(SLOT₂) and their all-orders versions are the higher-order
> residual-polynomial machinery of Montes and of Fernández–Guàrdia–Montes–Nart,
> *Residual ideals of MacLane valuations*, arXiv:1305.0775v3 (numbering
> verified locally against `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`
> at ledger 63091ce): Definition 1.4 (key polynomial for a valuation μ),
> Definition 1.8 + Proposition 1.9 (the augmented valuation and its graded
> structure), Definition 2.5 (the λ-component of the Newton polygon N_{μ,φ}),
> **Theorem 2.8 (the Theorem of the Product, N_{μ,φ}(gh) = N_{μ,φ}(g) +
> N_{μ,φ}(h))**, **Definition 3.18 (the residual polynomial operator R_i)**,
> **Theorem 4.2 (H_μ(g) = φ_r(g)·R_r(g)(y_r) — the graded image of g is its
> residual polynomial evaluated at the level-r generator)** and Corollary 4.4
> (deg R_i(g) = d, R_i(g)(0) ≠ 0), with Corollary 5.6 (R_i(φ_{i+1}) = ψ_i)
> identifying our Ψ_{λ,r} as a representative of the augmented type. Taking
> that route would make HE6-BOX-1 a CITED step rather than an open one; per
> this repo's axiom policy it needs a faithfulness entry
> (`docs/AXIOM_FAITHFULNESS.md`) and a semantic-guardian pass before it may be
> consumed, so it is displayed here as a target, not as a discharge.”

**DERIVATION.** [RECORD of a citation target].

**CONDITIONALITY.** **Explicitly not a discharge.** The gate is the repo's axiom policy: a faithfulness entry plus a semantic-guardian pass. **PIN VERIFIED:** `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` EXISTS ✓; `63091ce` is a commit ✓; `docs/AXIOM_FAITHFULNESS.md` EXISTS ✓ (the repo guide names it as the trusted-axiom audit). The seven numbered FGMN results are cited with a locally verified numbering — a stronger citation discipline than a bare arXiv reference, and worth preserving in any chapter cut.

**XREF.** artifacts `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`, `docs/AXIOM_FAITHFULNESS.md` — both EXIST ✓.

---

### EFF.HE6.41  [record]

**CANONICAL STATEMENT** (verbatim, §S7.4 L830–843 — HE6-BOX-2). FORM: bulleted box with an `[r2]` arc line.

> “* **HE6-BOX-2 (grade) [r1] [r2].** Attempt grade **0/2** for this note — the PE1
>   hostile pass HAS now run and its queue R1–R9 is applied above, but a pass
>   counts as survived only when the repaired text survives a FRESH pass, so
>   the counter stays at **0/2 post-r1**. **[r2] arc line:** the first Fable
>   hostile pass PE2 ran on the r1 text (`HE6_passPE2_report.md`, 404dae1):
>   NOT CLEAN — 0 CRITICAL / 2 GAP (F-1 the η^{−q(k)} coset display, F-2 the
>   §S9 record) / 3 MINOR (F-3/F-4/F-5); THEOREM HE6.A, COROLLARY HE6.B [r1]
>   and the reconciliation's composition claims all survived its attacks. The
>   five repairs are applied at [r2]-tagged sites (this round); the counter
>   stays **0/2 post-r2** and the r2 text owes a fresh hostile pass — **PE3
>   next**. THEOREM HE6.A inherits the minimum over its suppliers
>   {GENHN 0/2 (battery GREEN), HE3 1/2 on μ ≤ 3, GENIND 0/2, W-12 0/2,
>   classical}, so every consequence is a conditional structure at exactly that
>   stack.”

**DERIVATION.** [RECORD].

**SERIES membership.** ARC SERIES member 4.

**CONDITIONALITY.** The grade half is **SUPERSEDED** by `.54` (ACCEPTED 2/2) and `.62` (CERTIFIED). **The min-over-suppliers rule survives and is the right way to read every consequence** — but its *values* are stale: HE3 is listed at “1/2 on μ ≤ 3”, GENHN/GENIND/W-12 at 0/2. Those are as-of 2026-08-09 records and this compilation does not re-adjudicate them. Flagged.

**XREF.** `HE3_PROOF_2026-08-08.md`, `GENHN_PROOF_2026-08-08.md`, `GENIND_PROOF_2026-08-08.md`, `W12_PROOF_2026-08-08.md` — all EXIST ✓.

---

### EFF.HE6.42  [fence]

**CANONICAL STATEMENT** (verbatim, §S7.4 L844–848 — HE6-BOX-3). FORM: bulleted box.

> “* **HE6-BOX-3 (machine coverage).** Rows exercise D′ = 2, (e₁,f₁) = (2,1),
>   h = 1, μ = 4, λ ∈ {5/2, 7/2} at q ∈ {3,5,7} in char 0 and q ∈ {3,5} in
>   char p. NOT exercised by machine: f₁ ≥ 2 stage genres (so the σ prediction
>   {(2,2),(2,2)} of §S2 at (1,2,4) is proof-only), μ ≥ 5, d ≥ 2 ambients, and
>   embedded genres. The proofs are uniform in all of these.”

**DERIVATION.** [RECORD of a coverage fence].

**CONDITIONALITY.** **This fence bounds three separate proof-only claims**: `.20`'s `{(2,2),(2,2)}` prediction, `.31`'s removal of HE3's `f₁ = 1` retreat (which is precisely an `f₁ ≥ 2` claim), and every `μ ≥ 5` instance of THEOREM HE6.A. **All three are proof-carried, not battery-carried** — recorded at 6.3.

**XREF.** none.

---

### EFF.HE6.43  [fence]

**CANONICAL STATEMENT** (verbatim, §S7.4 L849–853 — HE6-BOX-4). FORM: bulleted box.

> “* **HE6-BOX-4 (oracle asymmetry).** PARI `factorpadic` exists only on the ℤ_p
>   side, so the char-p rows are scored against the reader plus the resultant
>   identities (LEMMA HE6-1/2/2′ are characteristic-free as proved: the only
>   algebraic inputs are the ultrametric inequality and residue arithmetic).
>   This asymmetry is inherited by every unit of this program.”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** Current, program-wide, and **structurally identical to HMENU3's mixed-characteristic-only oracle fence** — where the same shape of disclosure later bounded a real defect's blast radius (`spec/EFF-HMENU3.md` `.65`). Recorded because the two notes' oracle fences are the same fence and a corpus-level consumer should treat them as one.

**XREF.** none.

---

### EFF.HE6.44  [instrument-record]

**CANONICAL STATEMENT** (verbatim, §S8 L859–866). FORM: bold-headed paragraph.

> “**Instrument.** Exact integer (and exact F_p[t]) Sylvester–Bareiss
> resultants; a fresh reader that computes the stage polygon and residual
> polynomials in the ϖ-convention of §S1 and factors them over F_p; the test
> family of DEFINITION HE6-1 built literally as in the note; PARI
> `sig(f,p) = factorpadic + idealprimedec` as the independent σ oracle on the
> char-0 rows. Members are enumerated as PERTURBATIONS strictly above the
> λ-line, so every member of a row has the SAME outer data and only the deeper
> digits move — which is what makes the separable/repeated dichotomy visible.”

**DERIVATION.** [RECORD] — an `instrument-record` (rule 19).

**CONDITIONALITY.** The perturbation design is the load-bearing choice: **because every member of a row shares outer data, the ALPHA2 rows' three-valued σ is a decisive certificate** (`.37`) rather than an artifact of varying inputs. Recorded as the reason the instrument can certify an obligation.

**XREF.** artifact `verification/openmath/he6_checks.py` — EXISTS ✓, md5 `321fa4d4990eef67ff6a20f375c32366` VERIFIED ✓.

---

### EFF.HE6.45  [table]

**CANONICAL STATEMENT** (verbatim, §S8 L868–872). FORM: bold-headed paragraph.

> “**Rows.** (e₁,f₁,h) = (2,1,1), Φ′ = x²−π, μ = 4, deg f = 8, λ = u/2:
> ℤ_3, ℤ_5, ℤ_7 at u = 5, ℤ_5 at u = 7, F_3[[t]] and F_5[[t]] at u = 5. Three
> configurations per row: **SPLIT** (R_λ = (Z−s₁)(Z−s₂), the HE3-BOX-6 bite,
> two labels), **INERT** (R_λ irreducible, one label (e_s,f_s) = (2,2)),
> **ALPHA2** (R_λ = (Z−s)², the HE6-BOX-1 configuration).”

`[TABLE]` (compiler transcription, alongside the source form)

| # | base | λ | char | configurations |
|---|---|---|---|---|
| 1 | ℤ_3 | 5/2 | 0 | SPLIT · INERT · ALPHA2 |
| 2 | ℤ_5 | 5/2 | 0 | SPLIT · INERT · ALPHA2 |
| 3 | ℤ_7 | 5/2 | 0 | SPLIT · INERT · ALPHA2 |
| 4 | ℤ_5 | 7/2 | 0 | SPLIT · INERT · ALPHA2 |
| 5 | F_3[[t]] | 5/2 | p | SPLIT · INERT · ALPHA2 (identities only) |
| 6 | F_5[[t]] | 5/2 | p | SPLIT · INERT · ALPHA2 (identities only) |

**Mandatory arithmetic audit (rule 22).** Six rows × three configurations = **18 config counts** — exactly the number `.55` says PE4's subset-sum ranged over (“the 18 config counts in `he6_checks_results.json`”) ✓. `deg f = D′μ = 2·4 = 8` ✓. `λ = u/2` with `u ∈ {5,7}` odd ✓ (lowest terms, as `.20` requires). Every row sits at the first bite of `.20` ✓.

**CONDITIONALITY.** **The three configurations are the note's experimental design**: SPLIT tests THEOREM HE6.A at HE3-BOX-6's bite, INERT is the one-label control, ALPHA2 is the box. All three at identical outer data per row.

**XREF.** none.

---

### EFF.HE6.46  [preregistration]

**CANONICAL STATEMENT** (verbatim, §S8 L874–881). FORM: bold-headed paragraph listing five legs.

> “**Legs.** HE6-GEN (P1: the flat identity 2v(Res(f,Ψ_{κ,r})) =
> ℓd_rD′h_F(κ) at every sampled rational height with r not dividing the
> residual) · HE6-SEP (P2: STRICT excess exactly at the labels — the
> nonemptiness certificate of LEMMA HE6-4) · HE6-XI (P3: 2v(Res(Ψ,Φ′))/deg Ψ =
> λ, i.e. LEMMA HE6-1's height clause, plus mutual genericity of the test
> polynomials of distinct labels) · HE6-SIG (P4: PARI σ vs the THEOREM HE6.A
> dictionary) · HE6-RANK (P5: rank of the old integer-height family vs the
> enlarged one, with the spurious-solution count).”

**DERIVATION.** [RECORD of five preregistrations].

**Arithmetic audit of P1's identity.** `(RES)` gives `Σ_ρ dv(Ψ(ρ)) = Σ_ξ dv(f(ξ))`; with `r` not dividing the residual, the ξ-side is `D″·h_F(κ) = ℓd_rD′·h_F(κ)` (`.30`(b)'s ξ-side) ✓, and `dv = e₁v = 2v` at `e₁ = 2` ✓ — so the displayed `2v(Res(f,Ψ)) = ℓd_rD′h_F(κ)` is exactly `.30`'s ξ-side computation at these rows ✓. **P1 is a direct test of `HE6-ACCOUNT`'s central identity.**

**CONDITIONALITY.** P1/P2 test `HE6-ACCOUNT` (`.30`); P3 tests `HE6-TEST-PACKAGE`(b) (`.17`); P4 tests THEOREM HE6.A's dictionary (`.18`); P5 is the information-theoretic control. **Each leg maps onto a pin span** — recorded at 6.1.

**XREF.** none.

---

### EFF.HE6.47  [run-record]

**CANONICAL STATEMENT** (verbatim, §S9 L890–899). FORM: bold-headed paragraph.

> “**GREEN — 0 violations, ALL FIVE TEETH FIRED, 196.1 s.** Artifacts
> `he6_checks_output.txt` (md5 403d44cfe462…), `he6_checks_results.json`
> (1e1836651283…), committed runner `he6_checks.py` (md5 321fa4d4990e…,
> identical at close 1f5a417 and at HEAD) **[r2 pin corrected — see the
> RECORD REPAIR box below]**. Totals:
> **72,315 flat resultant identities** at rational test heights ·
> **4,232 strict-excess (nonemptiness) certificates** · 24 ξ-side height reads
> + 6 orthogonality checks · **2,226 PARI σ jobs** · 1,385 members over six
> rows (ℤ_3/ℤ_5/ℤ_7 at λ = 5/2, ℤ_5 at λ = 7/2, F_3[[t]] and F_5[[t]] at
> λ = 5/2).”

**DERIVATION.** [RECORD of an executed instrument].

**PIN VERIFICATION.** All three md5 prefixes reproduce **exactly** at HEAD: `403d44cfe462d7d800bfe0dbe59f2988`, `1e183665128313004298e2c406a991df`, `321fa4d4990eef67ff6a20f375c32366` ✓. `1f5a417` is a commit ✓.

**Mandatory arithmetic audit (rule 22).** `2,226 = 742 × 3` ✓ (the three configurations at the four char-0 rows). **`1,385` DOES NOT RECONCILE** — superseded by `.55`, which supplies **986** unique members (`209+299+185+157+79+57 = 986` ✓ recomputed) and **2,958** config instances (`3 × 986` ✓). **`72,315` is not reproducible from the note's displayed figures:** `72,315 = 45 × 1,607` with `1,607` prime, and `72,315 / 2,958 ≈ 24.45` is not an integer, so the “Σ members × 3 configs × tests/member” re-derivation `.55` reports must use a per-row-varying tests/member. Recorded as **not independently verified**, honestly rather than passed.

**CONDITIONALITY.** **SUPERSEDED in one figure** by Correction 1 (`.55`), and the runner-pin history is corrected by `.48`.

**XREF.** artifacts as above, all EXIST and VERIFY ✓.

---

### EFF.HE6.48  [changes-record]

**CANONICAL STATEMENT** (verbatim, §S9 L901–921 — the `[r2]` RECORD REPAIR). FORM: display (blockquoted, four numbered findings).

> “**[r2] RECORD REPAIR (PE2 F-2) — the runner pin this section carried
> through r1 was FALSE; no artifact byte changed in this repair.** What is
> now known, enumerated: (1) the [r1]-era pin ("runner-as-run
> 959fff4052e9…") matches neither the runner at seal a77c376 (md5
> af7009ecb005…, the pre-run WIP) nor at close 1f5a417 / HEAD (md5
> 321fa4d4990e…, re-computed this round), and PE2's repo sweep found no
> object with that md5 — the bytes that pin named are unrecoverable.
> (2) The committed runner's mtime (2026-08-08 20:34:47) postdates both
> artifacts (20:25:13) by 9 min 34 s (re-verified this round): an
> UNDISCLOSED-until-now, unexplained post-run edit window between the run
> and the close commit; what that window contained is not known. (3) Its
> effect on the recorded verdict is NIL — PE2's isolated re-run of the
> committed runner (sandbox /tmp/he6pe2_iso, md5 321fa4d… verified before
> run) reproduced `he6_checks_output.txt` byte-identically modulo timing
> lines and the results json identically except `secs` fields: exit 0,
> **0 violations**, 72,315 GEN / 4,232 SEP / 2,226 SIG / 24 XI / 6 ORTH,
> 5/5 teeth (PE2 report §S3; the he6r1 and supp runners re-ran clean in the
> same sandbox). So the committed instrument generates the committed
> verdict, and this section's numbers rest on the committed 321fa4d… bytes,
> not on the lost as-run copy. (4) The header's freeze anchor is corrected
> in the same round: the true anchor is close 1f5a417, not seal a77c376.”

**DERIVATION.** [RECORD of an instrument-provenance defect and its bounded consequence].

**TEETH disposition (rule 20).** `signed vacuity disclosure` **and** `stale self-description` — the note discloses that (i) a pin it carried through a whole round named unrecoverable bytes, and (ii) there is an unexplained 9 m 34 s post-run edit window whose contents are unknown. **The repair does not close the window; it bounds its consequence** by re-running the committed runner in isolation and reproducing the artifacts.

**Compiler assessment of the bound's strength.** The isolated re-run establishes “the committed instrument generates the committed verdict” ✓ — which is the right property and is checkable. **What it does not establish** is that the *as-run* instrument was the committed one; those bytes are gone. So §S9's numbers are warranted by the committed runner, and the historical claim that they were *produced by* it is warranted only by the re-run's agreement. **The note states exactly this distinction** (“this section's numbers rest on the committed 321fa4d… bytes, not on the lost as-run copy”), which is the honest framing. Recorded because it is the strongest instance in queue 8b of a note correctly reporting an irrecoverable provenance gap rather than papering over it.

**SUPERSESSION KIND:** `replacement` (a false pin and a false freeze anchor, both replaced). **TARGETS:** `.02` (the header anchor) and `.47` (the §S9 pin).

**PIN VERIFICATION.** `a77c376` and `1f5a417` are commits ✓; the committed runner's md5 `321fa4d4990eef67ff6a20f375c32366` reproduces ✓; the withdrawn pin `959fff4052e9…` matches no file in `verification/openmath/` ✓ (compile-time sweep confirms PE2's finding).

**XREF.** `HE6_passPE2_report.md` — EXISTS ✓.

---

### EFF.HE6.49  [run-record]

**CANONICAL STATEMENT** (verbatim, §S9 Q1 and Q2, L923–933). FORM: bold-headed paragraphs.

> “**Q1 (HE6-GEN — P1 confirmed) ✓** 0 violations in 72,315 checks:
> 2v(Res(f, Ψ_{κ,r})) = ℓ·deg r·D′·h_F(κ) EXACTLY at every sampled rational
> height κ = u′/ℓ′ (ℓ′ ∈ {1,2,3}) with r not dividing the residual, in BOTH
> characteristics. The (SEP)-free inversion of LEMMA HE6-3 is machine-real, and
> so is the identity at heights **no element of the stage ring can occupy**.
>
> **Q2 (HE6-SEP — P2 confirmed) ✓** 0 violations in 4,232 checks: whenever
> r | R_λ the same resultant valuation is STRICTLY greater than the flat value
> (e.g. ℤ_3, λ = 5/2: measured 42 vs flat 40 on BOTH labels). This strict
> excess is the engine of LEMMA HE6-4 — the exact place where HE3's base change
> stood.”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** Q1's `ℓ′ ∈ {1,2,3}` is the sampled-height range — **fractional heights `ℓ′ = 2,3` are exactly what integer sampling could not reach** (`.30`(c)), so Q1 is a direct machine test of the mechanism that kills `(SEP)`. Q2's spot value (`42 vs 40`) is the strictness-transfer certificate in one number.

**XREF.** none.

---

### EFF.HE6.50  [table]

**CANONICAL STATEMENT** (verbatim, §S9 Q3, L935–959). FORM: bold-headed paragraph followed by a **fixed-width ASCII table** — **rule 14 applies here**, so the table is emitted twice.

> “**Q3 (HE6-SIG — P4 confirmed, and this is the headline) ✓ 2,226 PARI jobs,
> 0 bad.** On the HE3-BOX-6 bite (**SPLIT**: ℓ = 2, R_λ = (Z−s₁)(Z−s₂), two
> labels), **742 octics over four char-0 rows all factor as
> σ = {(4,1),(4,1)}** — two totally ramified quartics, THEOREM HE6.A's
> dictionary, with no exception; and it is invariant under all 742 distinct
> deeper-digit perturbations, exactly as a theorem about the OUTER data must
> be. Control **INERT** (R_λ irreducible, one label with (e_s,f_s) = (2,2)):
> 742 jobs all σ = {(4,2)} ✓.”

**Source display, verbatim (rule 14, emission 1 of 2):**

>     row            cfg      members  PARI  sigma observed
>     Z_3 λ=5/2      SPLIT      209     200  {(4,1),(4,1)} 200
>     Z_5 λ=5/2      SPLIT      299     200  {(4,1),(4,1)} 200
>     Z_7 λ=5/2      SPLIT      185     185  {(4,1),(4,1)} 185
>     Z_5 λ=7/2      SPLIT      157     157  {(4,1),(4,1)} 157
>     (same rows)    INERT      ↑       742  {(4,2)} 742
>     Z_3 λ=5/2      ALPHA2     209     200  {(8,1)} 153 · {(4,2)} 30 ·
>                                             {(4,1),(4,1)} 17
>     Z_5 λ=5/2      ALPHA2     299     200  {(8,1)} 176 · {(4,2)} 11 ·
>                                             {(4,1),(4,1)} 13
>     Z_7 λ=5/2      ALPHA2     185     185  {(8,1)} 162 · {(4,2)} 12 ·
>                                             {(4,1),(4,1)} 11
>     Z_5 λ=7/2      ALPHA2     157     157  {(8,1)} 127 · {(4,2)} 13 ·
>                                             {(4,1),(4,1)} 17
>     F_3[[t]] λ=5/2 all 3       79       0  (char p: identities only, HE6-BOX-4)
>     F_5[[t]] λ=5/2 all 3       57       0  (char p: identities only)

`[TABLE]` (rule 14, emission 2 of 2 — Markdown transcription)

| row | cfg | members | PARI | σ observed |
|---|---|---|---|---|
| ℤ_3 λ=5/2 | SPLIT | 209 | 200 | `{(4,1),(4,1)}` 200 |
| ℤ_5 λ=5/2 | SPLIT | 299 | 200 | `{(4,1),(4,1)}` 200 |
| ℤ_7 λ=5/2 | SPLIT | 185 | 185 | `{(4,1),(4,1)}` 185 |
| ℤ_5 λ=7/2 | SPLIT | 157 | 157 | `{(4,1),(4,1)}` 157 |
| (same rows) | INERT | ↑ | 742 | `{(4,2)}` 742 |
| ℤ_3 λ=5/2 | ALPHA2 | 209 | 200 | `{(8,1)}` 153 · `{(4,2)}` 30 · `{(4,1),(4,1)}` 17 |
| ℤ_5 λ=5/2 | ALPHA2 | 299 | 200 | `{(8,1)}` 176 · `{(4,2)}` 11 · `{(4,1),(4,1)}` 13 |
| ℤ_7 λ=5/2 | ALPHA2 | 185 | 185 | `{(8,1)}` 162 · `{(4,2)}` 12 · `{(4,1),(4,1)}` 11 |
| ℤ_5 λ=7/2 | ALPHA2 | 157 | 157 | `{(8,1)}` 127 · `{(4,2)}` 13 · `{(4,1),(4,1)}` 17 |
| F_3[[t]] λ=5/2 | all 3 | 79 | 0 | (char p: identities only, HE6-BOX-4) |
| F_5[[t]] λ=5/2 | all 3 | 57 | 0 | (char p: identities only) |

**Mandatory arithmetic audit (rule 22) — every row and every total.** **SPLIT PARI column:** `200 + 200 + 185 + 157 = 742` ✓, matching the headline “742 octics”. **INERT:** 742 ✓. **ALPHA2 PARI column:** `200 + 200 + 185 + 157 = 742` ✓. **Grand total:** `742 × 3 = 2,226` ✓ — exactly the reported PARI job count. **Each ALPHA2 row's σ breakdown sums to its PARI count:** `153+30+17 = 200` ✓; `176+11+13 = 200` ✓; `162+12+11 = 185` ✓; `127+13+17 = 157` ✓. **All four.** **Members column:** `209+299+185+157+79+57 = 986` ✓ — **which is Correction 1's corrected figure** (`.55`), not the frozen headline's 1,385. **Every number in this table is internally consistent and consistent with the correction.**

**CONDITIONALITY.** Char-p rows carry **0** PARI jobs (`.43`), so the σ evidence is char-0 only. The three-valued ALPHA2 column is `.37`'s box certificate.

**XREF.** none.

---

### EFF.HE6.51  [run-record]

**CANONICAL STATEMENT** (verbatim, §S9 Q4, L961–967). FORM: bold-headed paragraph.

> “**Q4 (HE6-RANK — P5 confirmed) ✓** At every SPLIT configuration the OLD
> integer-height family has **rank 1 where 2 labels must be pinned**, and
> admits **3** class-size vectors compatible with all of its identities —
> (8,0), (4,4), (0,8) — of which only (4,4) is the truth; the enlarged family
> leaves **exactly 1**. This is the ℓ ≥ 2 analogue of HE3's HE-T-UNDET, and it
> shows the failure at the degenerate side is information-theoretic, not a gap
> in HE3's bookkeeping.”

**DERIVATION.** [RECORD].

**Arithmetic audit.** Two labels at the bite, each of predicted size `D′ℓd_r = 2·2·1 = 4`, total `n_λ = D′L_λ = 2·4 = 8` ✓. A rank-1 system on `(|S_1|,|S_2|)` with `|S_1|+|S_2| = 8` and both `≥ 0` and both multiples of 4 (forced by `.17`(a)'s degree bound) admits exactly `(8,0), (4,4), (0,8)` ✓ — **three vectors**, exactly as reported, and only `(4,4)` is the truth ✓.

**CONDITIONALITY.** **This is the note's strongest methodological claim about HE3**: the old family's failure is *information-theoretic*, not a bookkeeping error — so HE3-BOX-6 could not have been closed by more careful accounting at integer heights. Recorded because it is what justifies the whole enlarged-family construction.

**XREF.** `HE3_PROOF_2026-08-08.md` — `HE-T-UNDET` cited descriptively (a tooth name in HE3's battery).

---

### EFF.HE6.52  [run-record]

**CANONICAL STATEMENT** (verbatim, §S9 Q5, L969–983). FORM: bold-headed paragraph plus five bulleted teeth.

> “**Q5 (teeth: 5/5 FIRED).**
> * **HE6-T-UNDET2 ✓** the rank-deficiency + spurious-solution count above.
> * **HE6-T-PLANT ✓** with one label's test polynomial withheld, the checker
>   reports 1 of 2 labels certified and the sizes UNDETERMINED — it does not
>   silently accept.
> * **HE6-T-FLIP ✓** PARI truth {(4,1),(4,1)} rejects all three planted
>   dictionaries {(8,1)}, {(4,2)}, {(2,1)}×4.
> * **HE6-T-BADKEY ✓** the test polynomial built at "κ = 6/2" (gcd(u,ℓ) = 2,
>   violating DEFINITION HE6-1) has 2 p-adic factors and its roots carry
>   DIFFERENT residues ±1 at the integer height 3 — LEMMA HE6-1's hypothesis
>   gcd(u,ℓ) = 1 is load-bearing and its violation is caught.
> * **HE6-T-CASEB ✓ (the box certificate)** at ALPHA2 (R_λ = (Z−s)², ℓ = 2)
>   the σ of members with IDENTICAL outer data takes **three** values on every
>   char-0 row (table above). HE6-BOX-1 is therefore a real mathematical
>   obligation, not an unfinished argument — no outer-data-only proof exists.”

**DERIVATION.** [RECORD of five teeth, all fired].

**CONDITIONALITY — the five teeth test five different things, and the taxonomy matters.** HE6-T-UNDET2 tests the **old** family's inadequacy (a negative control); HE6-T-PLANT tests the **checker's** honesty (it must refuse, not accept); HE6-T-FLIP tests the **oracle's** discriminating power; HE6-T-BADKEY tests that a **hypothesis of DEFINITION HE6-1 is load-bearing** (`gcd(u,ℓ)=1`); HE6-T-CASEB **certifies an open obligation as real**. **Only one of the five is a conventional pass/fail on a claim of the note** — recorded because a consumer citing “5/5 teeth fired” should know what the five are testing.

**Arithmetic audit of HE6-T-BADKEY.** `κ = 6/2` has `gcd(6,2) = 2 ≠ 1` ✓, violating DEFINITION HE6-1's lowest-terms requirement; the observed consequence — 2 p-adic factors with different residues `±1` at integer height 3 — is exactly the failure of `.17`(b)'s “EVERY root carries the intended label”, since `6/2 = 3 ∈ ℤ` means the height is integral and the `y^ℓ/ϖ^u` class is not well defined ✓.

**XREF.** none.

---

### EFF.HE6.53  [scope-record]

**CANONICAL STATEMENT** (verbatim, §S9 L985–993). FORM: bold-headed paragraph.

> “**What the machine leg establishes** (instrument grade, not acceptance): the
> resultant identity of LEMMA HE6-1/HE6-2 at fractional heights on 72,315
> instances in both characteristics; the strict-excess certificate of LEMMA
> HE6-4 on 4,232; THEOREM HE6.A's dictionary at the HE3-BOX-6 bite under an
> independent oracle on 742 octics with 0 exceptions and invariance under
> perturbation; the rank-deficiency of the old family with its exact spurious
> count; and the sharpness of the separability hypothesis. Grade box HE6-BOX-2
> unchanged: **attempt 0/2, no hostile arc has run**; nothing here upgrades the
> conditionality display of COROLLARY HE6.B.”

**DERIVATION.** [RECORD] — an explicit, itemized statement of the machine leg's reach, ending with a refusal to upgrade any conditionality.

**SERIES membership.** ARC SERIES member 5.

**CONDITIONALITY.** The closing sentence — “**attempt 0/2, no hostile arc has run**” — is **SUPERSEDED BY NAME** by the acceptance record: `.54` says “This line supersedes the round-dated grade sentence directly above ("attempt 0/2, no hostile arc has run")”. **The only grade sentence in the note that an append supersedes explicitly.** L993 is also exactly the freeze boundary (FREEZE-1). The itemized reach-list is current and correct.

**XREF.** none.

---

### EFF.HE6.54  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L1004–1020). FORM: bold-headed paragraph.

> “**ACCEPTANCE (2/2).** passPE3 returned CLEAN — 0 CRITICAL + 0 GAP + 0 MINOR
> on the r2 target (`HE6_passPE3_report.md` @ 9f02ad4, byte-frozen md5
> 298b3c973e31648c65b405532b2e28eb, re-hashed at this append; counter
> 0/2 → 1/2).
> passPE4 returned CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR
> (`HE6_passPE4_report.md` @ 7ca97c9, byte-frozen at md5
> 14d1b88c25fa8213d2706843f1ce67e6; its fresh leg
> `verification/openmath/he6_pe4_fresh.py` GREEN 70 checks / 0 violations on
> its first full run — the arc's FIRST non-prime-q BASE oracle leg, ℚ₉/ℚ₂₅
> unramified bases, THEOREM HE6.A's dictionary 60/60, dual-base disagreement
> on identical bytes 10/10, teeth 3/3; three isolated re-runs green,
> he6 72,315/4,232/2,226/24/6 with 5/5 teeth). Counter 1/2 → **2/2: HE6 is
> ACCEPTED — the text is FROZEN, dated appends only from here.** This line
> supersedes the round-dated grade sentence directly above ("attempt 0/2, no
> hostile arc has run"): the arc since ran seal a77c376 → close 1f5a417 →
> Codex PE1 → r1 → PE2 → r2 → PE3 → PE4. The two PE4 MINORs land as the
> corrections below.”

**DERIVATION.** [RECORD of an acceptance].

**SERIES membership.** ARC SERIES member 6 — **TERMINAL for the acceptance counter**.

**SUPERSESSION KIND:** `replacement`, and **uniquely in queue 8b it names its target verbatim** (“supersedes the round-dated grade sentence directly above ("attempt 0/2, no hostile arc has run")”). **TARGETS:** `.53` by name; `.01`, `.02`, `.03`, `.41` by implication.

**CONDITIONALITY — one genuinely decorrelated leg.** PE4's fresh leg is “the arc's **FIRST non-prime-q BASE** oracle leg, ℚ₉/ℚ₂₅ unramified bases”. **This is the only evidence in the note touching `f₁ ≥ 2`-adjacent territory** — an unramified base of degree 2 over ℚ₃/ℚ₅ — and it returned “THEOREM HE6.A's dictionary 60/60” plus “dual-base disagreement on identical bytes 10/10”. It does **not** close HE6-BOX-3's `f₁ ≥ 2` coverage hole (the stage genre is still `(2,1)`), but it is the nearest approach in the arc. Recorded precisely so it is neither over- nor under-claimed.

**PIN VERIFICATION.** `9f02ad4`, `7ca97c9`, `a77c376`, `1f5a417` — **all four commits** ✓. Both report md5s reproduce **exactly** ✓. `verification/openmath/he6_pe4_fresh.py` EXISTS ✓.

**XREF.** artifacts as above, all EXIST ✓.

---

### EFF.HE6.55  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1022–1034 — Correction 1). FORM: bold-headed paragraph.

> “**Correction 1 (PE4 F-1 — the §S9 headline "1,385 members over six
> rows").** The figure is UNRECONSTRUCTABLE from the committed artifacts:
> passPE4's exhaustive subset-sum over the 18 config counts in
> `he6_checks_results.json` found no natural aggregation equal to 1,385. Read
> the headline with the true aggregations, re-summed from the committed json
> at this append: **986 unique perturbation members over the six rows**
> (209 + 299 + 185 + 157 + 79 + 57 — the per-row values, matching §S9's own
> Q3 table and the json exactly) and **2,958 config member instances**
> (3 configs per row × 986). The neighboring §S9 totals reconciled against
> the artifacts at PE4 (72,315 GEN — also re-derived arithmetically as
> Σ members × 3 configs × tests/member — 4,232 SEP, 2,226 SIG = 742·3, 24 XI,
> 6 ORTH); the 1,385 has zero consumers per passPE4's audit (no theorem, leg
> or tooth of this note reads it).”

**DERIVATION.** An exhaustive subset-sum search over the 18 config counts, returning no aggregation equal to 1,385, plus a re-summation from the committed json.

**Mandatory arithmetic audit (rule 22) — the correction's own figures recomputed.** `209 + 299 + 185 + 157 + 79 + 57 = 986` ✓ **exact**; `3 × 986 = 2,958` ✓; `742 × 3 = 2,226` ✓; the six per-row values match `.50`'s Q3 members column **exactly** ✓. **The correction is right and its arithmetic is reproducible.** The one figure the correction itself does not make reproducible is `72,315` — its “Σ members × 3 configs × tests/member” gloss yields no integer tests/member against 2,958 (`72,315/2,958 ≈ 24.45`), so tests/member must vary by row; **recorded as not independently verified** (`.47`).

**SUPERSESSION KIND:** `replacement` of a figure. **TARGETS:** `.47`. **TEETH disposition (rule 20):** `stale self-description` — a headline number the artifacts cannot produce, with **zero consumers** (audited), so the blast radius is nil.

**AUDIT disposition (rule 27).** `arithmetic recount` — found by an exhaustive subset-sum, a check no tooth of this battery performs.

**XREF.** artifact `verification/openmath/he6_checks_results.json` — EXISTS ✓, md5 VERIFIED ✓.

---

### EFF.HE6.56  [changes-record]  **[PIN: `HE6-BETA-GUARD` [1036,1047]]**

**SPAN IDENTITY.** Lines **1036–1047**. First delimiter `**Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard).** The` — `grep -cFx` = **1**, at line 1036. Last delimiter `lemma's conclusion and its consumers are unaffected by this re-scoping.` — `grep -cFx` = **1**, at line 1047. First precedes last ✓. **T2 consumption count: 63.** This is the **only pin span inside a dated append**, and T2 pinned it at its own r11 round (T2 L4035, L4045, L4059).

**CANONICAL STATEMENT** (verbatim, the full span). FORM: bold-headed paragraph.

> “**Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard).** The
> statement's guard "when δ has denominator dividing ℓ" is broader than β's
> domain of definition: at ℓδ ∈ ℤ with ℓδ > u the displayed element
> Φ′(ξ)^ℓ/ϖ(ξ)^u has residue 0, and at ℓδ < u it is not integral, so res is
> undefined (instance: δ = 2 ∈ ℤ, κ = 5/2, ℓ = 2, u = 5 gives dv = −1). Read
> the guard as **"when δ = κ"** — the defining case, where the element is a
> unit and β a unit residue. The lemma's own dichotomy "ε(ξ) > 0 ⟺ δ = κ and
> ι_ξ(r)(β) = 0" consults β only under its first conjunct δ = κ; per
> passPE4's site check, HE6-3/HE6-4/THEOREM HE6.A read ε through that
> dichotomy, and an unguarded β = 0 read cannot create a spurious ε > 0
> because r(0) ≠ 0 forces ι_ξ(r)(0) ≠ 0. Definitional looseness only; the
> lemma's conclusion and its consumers are unaffected by this re-scoping.”

**DERIVATION.** A domain-of-definition argument with a numerical instance, plus a three-part harmlessness argument (the dichotomy consults β only under `δ = κ`; the consumers read ε through the dichotomy; and even an unguarded `β = 0` read is harmless because `r(0) ≠ 0`).

**Mandatory arithmetic audit (rule 22) — the instance and both failure modes.** `dv(Φ′(ξ)^ℓ/ϖ(ξ)^u) = ℓδ − u` (using `dv(ϖ(ξ)) = 1`, `.11`). At `ℓδ > u` this is `> 0`, so the element is a non-unit and its residue is **0** ✓. At `ℓδ < u` it is `< 0`, so the element is not integral and `res` is **undefined** ✓. The instance: `δ = 2, ℓ = 2, u = 5` gives `ℓδ − u = 4 − 5 = −1` ✓ **exactly the displayed `dv = −1`**, and `δ = 2` has denominator 1 dividing `ℓ = 2` ✓ — so it **is** admitted by the frozen guard and **is** outside β's domain. **The defect is real and the instance is exact.** The harmlessness leg: `r(0) ≠ 0` (DEFINITION HE6-1, `.14`) gives `ι_ξ(r)(0) ≠ 0` since `ι_ξ` is a field embedding ✓, so an unguarded `β = 0` read yields `ι_ξ(r)(β) ≠ 0`, hence no spurious `ε > 0` ✓.

**SUPERSESSION KIND:** `scope-pin` — a guard narrowed to its defining case. **TARGETS:** `.17`(c) (LEMMA HE6-2's statement) and, through it, `.27` (its proof, which already works only at `δ = κ`).

**T2 consumption note — the model for how a pin gap should be closed.** T2's r11 repair pins this correction **as its own span** and cites it “at both sites that lean on it” (T2 L4045), with L4086 recording the composite reading: “`HE6-TEST-PACKAGE`, read under `HE6-BETA-GUARD`: the corrected guard is what confines the β of LEMMA HE6-2's dichotomy to δ = κ, where it is defined, while this master's "away from that label class" half of clause 2 is the contrapositive”. **This is exactly the device OPEN-CALL 2 recommends for the two A3 corrections that currently sit outside every span.**

**XREF.** `T2_SIGMA_LADDER_MASTER_2026-08-12.md` — `HE6-BETA-GUARD`, count 63; `HE6-TEST-PACKAGE`, count 59.

---

### EFF.HE6.57  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1051–1059 — the A3 frame). FORM: `###`-headed dated paragraph.

> “### Dated corrections (2026-08-12 — sol certification A3: the R6 chain challenge adjudicated at HEAD)
>
> The sol-5.6 chain read of this note (gpt-5.6-sol high,
> runs/residues/R6_he6_output.log, 2026-08-12) returned CHALLENGE with
> four findings. The A3 certification run (gpt-5.6-sol high,
> runs/cert/A3_he6_output.log) re-adjudicated all four against HEAD
> including every dated append: all four are REAL with derived repairs
> — the four dated corrections below. Everything above this heading is
> byte-untouched by this append.”

**DERIVATION.** [RECORD of an adjudication].

**AUDIT disposition (rule 27).** `decorrelated-model audit`. **All four findings REAL** — including one (F-4) that is an internal contradiction four hostile passes missed (`.61`), and one (F-1) that corrects a display consumed by three lemmas and pinned 48 times by T2 (`.58`).

**PIN VERIFICATION.** `runs/residues/R6_he6_output.log` EXISTS ✓; `runs/cert/A3_he6_output.log` EXISTS ✓.

**XREF.** artifacts as above.

---

### EFF.HE6.58  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1061–1113 — A3 F-1, the normalized slot coefficients). FORM: bold-headed dated paragraph with six LaTeX displays. The defect and the replacement:

> “**Dated correction (2026-08-12, post-acceptance challenge F-1 — normalized slot coefficients in LEMMA HE6-0″).** The displayed definition
>
> \[
> \gamma=\sum_t\operatorname{res}(a_{i_0+e_1t})\eta_\theta^t
> \]
>
> omitted the coefficient normalizers. Let \(k:=dv(A)\), let \(i=i(k)\) be the unique integer \(0\le i<e_1\) satisfying \(ih\equiv k\pmod{e_1}\), and put
>
> \[
> n(k):=x^i\pi^{(k-ih)/e_1}.
> \]
>
> Read the slot residue in LEMMA HE6-0″ as
>
> \[
> \gamma_k(A):=
> \sum_{\substack{t\ge0\\i+e_1t<D'}}
> \operatorname{res}\!\left(
> a_{i+e_1t}\pi^{-(k-(i+e_1t)h)/e_1}
> \right)\eta_\theta^t\in K,
> \]
>
> where a coefficient whose pin lies strictly above height \(k\) contributes zero.”

with its derivation and conclusion:

> “Indeed, for \(j=i+e_1t\),
>
> \[
> \frac{a_j\xi^j}{n(k)(\xi)}
> =
> \left(a_j\pi^{-(k-jh)/e_1}\right)
> \left(\xi^{e_1}\pi^{-h}\right)^t,
> \]
>
> while every index outside the class \(i\bmod e_1\) has strictly larger value and vanishes after reduction. Hence
>
> \[
> \operatorname{res}\!\left(\frac{A(\xi)}{n(k)(\xi)}\right)
> =\iota_\xi(\gamma_k(A)).
> \]
>
> Since the RIDER gives
>
> \[
> \operatorname{res}\!\left(\frac{n(k)(\xi)}{\varpi(\xi)^k}\right)
> =\eta_\xi^{-q(k)},
> \]
>
> the corrected conclusion of LEMMA HE6-0″ is
>
> \[
> \operatorname{res}\!\left(\frac{A(\xi)}{\varpi(\xi)^k}\right)
> =\iota_\xi(\gamma_k(A))\,\eta_\xi^{-q(k)}.
> \]
>
> At \(\xi=\theta\), this is precisely the \(\varpi\)-read residue used to choose each \(B_t\); therefore at an arbitrary \((T1)/(T2)\) point it transports to its \(\iota_\xi\)-image. Thus the residue computations in LEMMA HE6-1, LEMMA HE6-2 and LEMMA HE6-2′ remain valid with this corrected formula. No theorem statement is weakened.”

**DERIVATION.** The span is the derivation: an exponent identity, a class-separation observation, and a composition with the RIDER.

**Mandatory arithmetic audit (rule 22) — the exponent identity re-derived by hand.** For `j = i + e₁t` and `n(k) = x^iπ^{(k−ih)/e₁}`:
`a_jξ^j/n(k)(ξ) = a_jξ^{i+e₁t}/(ξ^iπ^{(k−ih)/e₁}) = a_jξ^{e₁t}π^{−(k−ih)/e₁}`.
The claimed form is `(a_jπ^{−(k−jh)/e₁})(ξ^{e₁}π^{−h})^t = a_jξ^{e₁t}π^{−(k−jh)/e₁ − th}`.
These agree iff `(k−ih)/e₁ = (k−jh)/e₁ + th`, and since `j = i+e₁t`, `(k−jh)/e₁ = (k−ih)/e₁ − th` ✓ — **the identity is exact**, and it is exactly the check the provenance note (`.62`) says the orchestrator performed by hand. The class-separation clause: indices outside `i mod e₁` have `e₁v(a_j) + jh ≢ k (mod e₁)`… more precisely their slot values exceed the minimum by a positive amount, so they vanish after reduction ✓ — the same mechanism as `.15`'s (T1) role.

**Why the frozen display was vacuous, not merely imprecise.** The provenance note states it: “the tying coefficients have positive valuation `(k−jh)/e₁`, so the bare `res(a_j)` reading is vacuous.” **Compiler confirmation:** at a slot on the line, `e₁v(a_j) + jh = k`, so `v(a_j) = (k−jh)/e₁ > 0` whenever `jh < k` — hence `res(a_j) = 0` for every such slot, and the bare `γ` would be the zero polynomial except at the single slot with `v(a_j) = 0`. **The frozen display did not merely omit a factor; it made γ collapse.** Recorded because this makes F-1 substantive rather than cosmetic.

**CHAIN position.** Layer 3 of C-2 (`.15`'s chain), **TERMINAL**.

**⚠ SPAN GAP.** A3 F-1 lies at **L1061–1113**, outside `HE6-SLOT-SEAM` [215,238] and outside every other pin span. T2 consumes `HE6-SLOT-SEAM` **48 times**. See OPEN-CALL 2.

**CONDITIONALITY.** “No theorem statement is weakened” — and the correction names its three dependent lemmas explicitly (HE6-1, HE6-2, HE6-2′), all of which remain valid. **Compiler check:** those three are exactly the lemmas whose proofs invoke the slot residue (`.25`, `.27`, `.28`) ✓ — the dependency list is complete.

**XREF.** `runs/cert/A3_he6_output.log` — EXISTS ✓.

---

### EFF.HE6.59  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1115–1154 — A3 F-2, the completion of LEMMA HE6-3(a)). FORM: bold-headed dated paragraph with five LaTeX displays.

> “**Dated correction (2026-08-12, post-acceptance challenge F-2 — completion of LEMMA HE6-3(a)).** In the proof of LEMMA HE6-3(a), replace the inference
>
> > “\(c_0=0\); as all slopes are \(>0\) this gives \(L_\lambda=0\) for every \(\lambda\le D'h\)”
>
> by the following length argument. Sampling \(\kappa\in(D'h,\lambda_1)\) gives both
>
> \[
> \sum_i c_{\lambda_i}=0
> \qquad\text{and}\qquad
> c_0=0.
> \]
>
> Every root label satisfies \(\lambda_\rho>D'h\) by LEMMA HE6-0 and HE3-0, and \(f\) is separable of degree \(D'\mu\); hence
>
> \[
> \sum_{\lambda>D'h}n_\lambda=D'\mu.
> \]
>
> Because \(A_0\ne0\), the polygon runs from abscissa \(0\) to \(\mu\), so
>
> \[
> \sum_\lambda L_\lambda=\mu.
> \]
>
> Writing \(B:=\sum_{\lambda\le D'h}L_\lambda\), the already obtained coefficient equation becomes
>
> \[
> 0=\sum_i c_{\lambda_i}
> =\sum_{\lambda>D'h}n_\lambda
>   -D'\sum_{\lambda>D'h}L_\lambda
> =D'\mu-D'(\mu-B)=D'B.
> \]
>
> Thus \(B=0\). Since every \(L_\lambda\) is a nonnegative horizontal length,
>
> \[
> L_\lambda=0\qquad(\lambda\le D'h).
> \]
>
> This proves LEMMA HE6-3(a) without assuming that polygon slopes are strictly positive. Part (b) and all consumers are unchanged.”

**DERIVATION.** The span is the derivation — a length count replacing an inference that assumed positivity of slopes.

**Mandatory arithmetic audit (rule 22) — every step re-derived.** `Σ_{λ>D′h}n_λ = D′μ`: `f` is separable of degree `D′μ`, so it has `D′μ` distinct roots, and every root's label exceeds `D′h` ✓ (`.16` + HE3-0). `Σ_λ L_λ = μ`: the polygon runs from abscissa 0 to μ **because `A₀ ≠ 0`** ✓ — supplied by `HE6-PEEL-CONVENTION` (`.09`, `.10`). Then `Σ_i c_{λ_i} = Σ_{λ>D′h}(n_λ − D′L_λ) = D′μ − D′Σ_{λ>D′h}L_λ = D′μ − D′(μ − B) = D′B` ✓, and `Σ_i c_{λ_i} = 0` gives `B = 0` ✓; nonnegativity of each `L_λ` then forces each to vanish ✓. **Exact at every step.**

**Why the frozen inference was a gap.** The provenance note (`.62`) states it: “`c₀ = −D′Σ_{λ≤D′h}L_λ·λ = 0` cannot exclude a zero-slope side, and the (SEP)-free setting does not exclude a unit development coefficient.” **Compiler confirmation:** if some side has `λ = 0`, its term in `c₀` is `L_λ·0 = 0`, so `c₀ = 0` carries no information about it ✓ — the frozen inference's parenthetical “as all slopes are > 0” was an unstated assumption, not a consequence.

**SUPERSESSION KIND:** `replacement` of an inference. **TARGETS:** `.30`(b)(a).

**⚠ SPAN GAP.** A3 F-2 lies at **L1115–1154**, outside `HE6-ACCOUNT` [525,604] and every other pin span. T2 consumes `HE6-ACCOUNT` **55 times**, including a **transitive** route (T2 L4192). See OPEN-CALL 2.

**Compiler note on a pleasing dependency.** The repair's second ingredient, `Σ_λ L_λ = μ`, holds **because `A₀ ≠ 0`** — i.e. because of `HE6-PEEL-CONVENTION`. And `.09`'s own necessity argument says that without the convention “`Σ_λ L_λ = μ` fails, and HE6-3's elimination loses its premise”. **The convention and the A3 repair are about the same identity, discovered from opposite directions three rounds apart.** Recorded because it is evidence the repair is the right one.

**XREF.** `runs/cert/A3_he6_output.log` — EXISTS ✓.

---

### EFF.HE6.60  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1156–1186 — A3 F-3, the equality slots). FORM: bold-headed dated paragraph with three LaTeX displays.

> “**Dated correction (2026-08-12, post-acceptance challenge F-3 — equality slots in LEMMA HE6-0).** In §S3.1, read
>
> > “with equality exactly at the slots \(i=e_1t\)”
>
> as
>
> > “with equality possible only at the slots \(i=e_1t\).”
>
> Indeed,
>
> \[
> e_1v(a_i)+ih=D'h
> \quad\Longrightarrow\quad
> e_1\mid(D'-i)h
> \quad\Longrightarrow\quad
> e_1\mid i,
> \]
>
> using \(\gcd(h,e_1)=1\) and \(e_1\mid D'\). The converse need not hold: a slot \(i=e_1t\) may lie strictly above the line. The following residual-polynomial display already handles this correctly, because then
>
> \[
> v\!\left(a_{e_1t}\pi^{-(f_1-t)h}\right)>0
> \]
>
> and its residue is zero. Therefore
>
> \[
> \operatorname{res}\!\left(\Phi'(\xi)/\pi^{f_1h}\right)=\psi(\eta_\xi)
> \]
>
> and the remainder of the disk-criterion proof are unchanged.”

**DERIVATION.** A one-directional implication with the converse explicitly denied, plus the observation that the downstream display self-corrects.

**Mathematical audit.** The implication chain ✓ (re-derived at `.22`). The converse's failure: a slot `i = e₁t` with `v(a_i)` strictly larger than `(D′h − ih)/e₁` lies strictly above the line ✓ — nothing forbids it, since `Φ′` irreducible only forces the pins to lie **on or above** the line with the endpoint pins on it. The self-correction: at such a slot, `v(a_{e₁t}π^{−(f₁−t)h}) = v(a_{e₁t}) − (f₁−t)h > 0` when the pin is above the line ✓, so its residue is 0 and it contributes nothing to `ψ(η_ξ)` ✓.

**SUPERSESSION KIND:** `wording-rider` — “exactly at” → “possible only at”. **TARGETS:** `.22`.

**CONDITIONALITY.** Conclusion-preserving, and the correction says exactly why: the residual display “already handles this correctly”. **This is the mildest of the four A3 findings** and the only one that is purely a wording repair.

**⚠ SPAN GAP.** L1156–1186, outside every pin span — but its target (`.22`, §S3.1) is **also** outside every pin span, so no T2 edge is affected. **The only one of the four A3 corrections that does not create a pin-span gap.**

**XREF.** `runs/cert/A3_he6_output.log` — EXISTS ✓.

---

### EFF.HE6.61  [changes-record]

**CANONICAL STATEMENT** (verbatim, L1188–1204 — A3 F-4, the coefficient ring of ϖ). FORM: bold-headed dated paragraph with one LaTeX display.

> “**Dated correction (2026-08-12, post-acceptance challenge F-4 — coefficient ring of \(\varpi\) in LEMMA HE6-5).** In §S6.1, read
>
> > “All of \(\Phi',\varpi\in O[x]\) have \(g\)-fixed coefficients”
>
> as
>
> > “The polynomial \(\Phi'\in O[x]\) and the normalizer \(\varpi\in K_0[x]\) both have \(g\)-fixed coefficients.”
>
> This follows because \(g\in\operatorname{Gal}(\overline K_0/K_0)\) fixes every coefficient in \(K_0\). Consequently
>
> \[
> \Phi'(g\rho)=g(\Phi'(\rho)),
> \qquad
> \varpi(g\rho)=g(\varpi(\rho)),
> \]
>
> exactly as required by the remainder of the proof. No integrality of the coefficients of \(\varpi\) is used.”

**DERIVATION.** A one-line observation: `g` fixes `K₀` pointwise, so `g`-fixedness of coefficients needs only `K₀`-membership, not integrality.

**CONDITIONALITY — and the four-round internal contradiction.** The frozen sentence contradicts the note's **own** `[r1]` R7/F8 convention (`.11`, L107: “**ϖ ∈ K₀[x], not O[x]**”, with the explicit witness `ϖ = xπ^{−1}`). **The two spans are 506 lines apart and disagree.** PE1, PE2, PE3 and PE4 all passed over it; the decorrelated A3 read caught it. **SUPERSESSION KIND:** `replacement`. **TARGETS:** `.31`.

**Compiler confirmation that the conclusion is safe.** `.31`'s proof consumes `ϖ`'s coefficients only through `ϖ(gρ) = g(ϖ(ρ))`, which needs `g`-fixedness alone ✓; and `.24` independently consumes `ϖ(ρ) ∈ L_ρ`, which needs only `K₀ ⊆ L_ρ` ✓. **Neither consumption needs integrality**, exactly as the correction says.

**⚠ SPAN GAP.** L1188–1204, outside every pin span; its target `.31` (§S6.1) is also outside every pin span — **but §S6.1 proves `LEMMA HE6-5`, which IS inside `HE6-TEST-PACKAGE` [244,287] as statement (g)**. So a consumer pinning the statement package imports HE6-5's *statement*, whose *proof* carries the corrected-but-unpinned sentence. Recorded at OPEN-CALL 2 as the subtlest instance of the gap.

**XREF.** `runs/cert/A3_he6_output.log` — EXISTS ✓.

---

### EFF.HE6.62  [record]

**CANONICAL STATEMENT** (verbatim, L1206–1234 — the A3 provenance paragraph). FORM: italic parenthetical paragraph.

> “*(Corrections F-1..F-4 derived by the A3 certification run
> (gpt-5.6-sol high, runs/cert/A3_he6_output.log, 2026-08-12);
> orchestrator verification before transcription — F-1: HE6-0″'s
> unnormalized γ display confirmed at HEAD (the tying coefficients
> have positive valuation (k−jh)/e₁, so the bare res(a_j) reading is
> vacuous); the exponent identity a_jξ^j/n(k)(ξ) =
> (a_jπ^{−(k−jh)/e₁})(ξ^{e₁}π^{−h})^t re-derived by hand
> ((k−jh)/e₁ + th = (k−ih)/e₁ at j = i+e₁t); the RIDER composition
> checked against the note's own definition η_θ^{q(k)} :=
> res(ϖ(θ)^k/n(k)(θ)) and the r2-corrected −q sign; consistency with
> DEFINITION HE6-1's B_t choice rule and with S3.1's own normalized
> display res(a_{e₁t}π^{−(f₁−t)h}) confirmed. F-2: the quoted
> inference located (S5, HE6-3(a)); the gap confirmed real (c₀ =
> −D′Σ_{λ≤D′h}L_λ·λ = 0 cannot exclude a zero-slope side, and the
> (SEP)-free setting does not exclude a unit development
> coefficient); the replacement re-derived line by line (root count
> Σ_{λ>D′h}n_λ = D′μ from separability + all labels > D′h; abscissa
> count Σ_λL_λ = μ from A₀ ≠ 0; Σᵢc_{λᵢ} = D′B), using only the
> sampling equality the note already proved. F-3: the span located
> (S3.1 L392–393); the note's own justification is the "only if"
> direction, so the repair matches the proof as written; the
> downstream display confirmed to zero out above-the-line slots via
> its normalizers. F-4: the r1 R7/F8 convention located (L106–107,
> "ϖ ∈ K₀[x], not O[x]", with the explicit witness ϖ = xπ^{−1});
> the contradicting S6.1 sentence located (L612); the proof re-read —
> only g-fixedness of coefficients in K₀ is consumed, never
> integrality. Transcribed unaltered per the standing division of
> labor. Ledger: HE6's row → repairs folded, awaiting sol
> discharge-confirmation.)*”

**DERIVATION.** [RECORD of a verification protocol].

**SERIES membership.** ARC SERIES member 7 — with a **stale terminal**, below.

**Compiler re-verification of the orchestrator's four verification legs.** **F-1:** the vacuity diagnosis ✓ (re-derived at `.58`); the exponent identity ✓ (re-derived by hand at `.58`, agreeing exactly); the RIDER composition ✓ (checked against `.13`'s definition and `.15`'s `[r2]` sign). **F-2:** the gap's reality ✓ (a zero-slope side contributes `L_λ·0 = 0` to `c₀`); the replacement's three ingredients ✓ (re-derived at `.59`). **F-3:** the cited span **L392–393** — verified: L392 is “satisfy e₁v(a_i) + i·h ≥ D′h for every i ≤ D′, with equality exactly at the” and L393 “slots **i = e₁t (t ≤ f₁)**: a pin lies on the line only if e₁ | (D′−i)h,” ✓ **exact**. **F-4:** the cited lines **L106–107** ✓ (the R7/F8 convention with its witness) and **L612** ✓ (the contradicting sentence). **All four legs, and all three line cites, check exactly.**

**LEDGER STATUS — the note's own closing claim is superseded at HEAD.** The paragraph ends “Ledger: HE6's row → repairs folded, **awaiting sol discharge-confirmation**”. **That is stale.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 14 at HEAD reads:

> “| 14 | HE6 | CHALLENGE (fresh, R6) | **CERTIFIED 2026-08-12** — A3's 4 repairs folded; D2c: 4/4 DISCHARGED (runs/cert2/D2c_he6_output.log) |”

**The awaited discharge landed** — 4/4 at D2c. Tagged `STALE-SELF-DESCRIPTION` (rule 26); no append reaches it. **Note this is the same shape as `spec/EFF-HMENU3.md` `.72`** — both notes close with “awaiting sol discharge” and both were discharged the same day.

**PIN VERIFICATION.** `runs/cert/A3_he6_output.log` EXISTS ✓; `runs/residues/R6_he6_output.log` EXISTS ✓.

**XREF.** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` — row 14, verified.

---

## 4. XREF verification ledger

### 4.1 The T2 pin edges (the queue charge's DAG keys)

Every one of the nine pins, with its T2 fixed-string count and the EFF unit that carries it. **Counts are `grep -cF '<pin>' T2_SIGMA_LADDER_MASTER_2026-08-12.md`.**

`[TABLE]`

| # | pin | span | T2 count | EFF unit | named T2 consumption sites (verified) |
|---|---|---|---|---|---|
| P1 | `HE6-PEEL-CONVENTION` | [83,97] | **32** | `.09` | T2 L2574: “consumed by repair 4(b) as the level-one original-key discharge of the `(MID-PEEL)` input suite, and by S1.5's key-freeness discipline” |
| P2 | `HE6-LIFT-1L` | [130,199] | **34** | `.13` | T2 L2864: the definitional home of `q(k)` — “defined only there (repair 4)” |
| P3 | `HE6-FAMILY` | [201,213] | **59** | `.14` | T2 L3875: S1.7 clause 7 + the degree display, jointly with `HE6-LIFT-1L`; T2 L3503: “becomes the fourth first-only pin” |
| P4 | `HE6-SLOT-SEAM` | [215,238] | **48** | `.15` | T2 L1616: “the corrected normalized-slot/seam display”; L3015/L3107: one of four pins certifying `(MP1′)` |
| P5 | `HE6-TEST-PACKAGE` | [244,287] | **59** | `.17` | T2 L4041 (r10 span verification); L4086: “read under `HE6-BETA-GUARD`” |
| P6 | `HE6-ROOT-LABEL` | [517,521] | **26** | `.29` | T2 L4041 (r10 span verification) |
| P7 | `HE6-ACCOUNT` | [525,604] | **55** | `.30` | T2 L4192: a **TRANSITIVE** consumption route |
| P8 | `HE6-PROOF` | [639,666] | **66** | `.32` | T2 L3123 (independent span verification); L3872: sub-span cite **HE6:644–648**; L3015/L3107/L3441 |
| P9 | `HE6-BETA-GUARD` | [1036,1047] | **63** | `.56` | T2 L4045/L4059/L4068/L4078/L4086 (r11 pinning and both citing sites) |

**Sub-span cite verified.** T2 L3872's “HE6:644–648, already inside the existing `HE6-PROOF` span [639,666]” — L644–648 is exactly step 1 of the proof (“**The classes partition the slope's roots.** …”) ✓, and it is strictly inside [639,666] ✓.

**T2 inventory line verified.** T2 L4104 records the pin roster: “`HE6-PROOF` (r6); `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT` (r10); and `HE6-BETA-GUARD` (r11) — **19 of 36**.” ✓ consistent with the nine-pin table (the other four predate r6).

### 4.2 Supplier designations

`[TABLE]`

| # | file | designation | count | consumed at |
|---|---|---|---|---|
| X1 | `GENHN_PROOF_2026-08-08.md` | `LEMMA GENHN-1` | 4 | `.04` |
| X2 | `GENHN_PROOF_2026-08-08.md` | `LEMMA GENHN-2` | 2 | `.04`, `.15`, `.25` |
| X3 | `GENHN_PROOF_2026-08-08.md` | `GENHN-3` | 21 | `.04` |
| X4 | `GENHN_PROOF_2026-08-08.md` | `GENHN-4` | 6 | `.07` (non-import) |
| X5 | `HE3_PROOF_2026-08-08.md` | `LEMMA HE3-0` | 7 | `.05`, `.16`, `.23`, `.29` |
| X6 | `HE3_PROOF_2026-08-08.md` | `LEMMA HE3-1` | 32 | `.05` |
| X7 | `HE3_PROOF_2026-08-08.md` | `THEOREM HE3.A` | 17 | `.05`, `.18`, `.19`, `.31`, `.32` |
| X8 | `HE3_PROOF_2026-08-08.md` | `COROLLARY HE3.B` | 8 | `.05`, `.19` |
| X9 | `HE3_PROOF_2026-08-08.md` | `DEFINITION 1` | 13 | `.05`, `.10` |
| X10 | `HE3_PROOF_2026-08-08.md` | `DEFINITION 2` | 3 | `.05` |
| X11 | `HE3_PROOF_2026-08-08.md` | `HE3-BOX-6` | 12 | `.07`, `.18`, `.20`, `.30`, `.35` |
| X12 | `HE3_PROOF_2026-08-08.md` | `HE3-3` | 15 | `.06`, `.17`, `.20`, `.30`, `.33`, `.35` |
| X13 | `HE3_PROOF_2026-08-08.md` | `LEMMA HE3-4` | 15 | `.17`, `.32`, `.34` |
| X14 | `HE3_PROOF_2026-08-08.md` | `HE3-2(b)` | 14 | `.33` |
| X15 | `HE7_PROOF_2026-08-08.md` | `LEMMA HE7-L1` | 12 | `.12`, `.13`, `.39` |
| X16 | `HE7_PROOF_2026-08-08.md` | `HE6` | 209 | `.13`, `.38`, `.39` |
| X17 | `HE7_PROOF_2026-08-08.md` | the landing heading `Dated correction (2026-08-09, from HE6 PE2 F-1)` | **1** | `.13` — the verified cross-note landing |
| X18 | `HE6R1_RECON_2026-08-08.md` | `HE6R1-1` | 15 | `.39` |
| X19 | `HE6R1_RECON_2026-08-08.md` | `HE6R1-2` | 13 | `.39` |
| X20 | `HE6R1_RECON_2026-08-08.md` | `HE6R1-3` | 10 | `.39` |
| X21 | `HE6R1_RECON_2026-08-08.md` | `HE6R1-T-CRACK` | 2 | `.19`, `.36` |
| X22 | `HE6R1_RECON_2026-08-08.md` | `HE6-BOX-1` | 3 | `.36` |
| X23 | `HE7_PROOF_2026-08-08.md` | `HE6-BOX-1` | 11 | `.36`, §5.2 |

**No OPEN-CALL arises from any designation.** Every cited name is grep-verified at count ≥ 1.

### 4.3 PIN VERIFICATION ledger (rule 23)

**Commit hashes — 8 cited, 8 verified** via `git cat-file -t` → `commit`: `a77c376`, `1f5a417`, `404dae1`, `7a95449`, `9f02ad4`, `7ca97c9`, `5da0552`, `63091ce`. **Zero failures.**

**md5 pins — 5 cited with values, 5 verified byte-exactly:** `he6_checks.py` `321fa4d4990eef67ff6a20f375c32366` ✓; `he6_checks_output.txt` `403d44cfe462d7d800bfe0dbe59f2988` ✓; `he6_checks_results.json` `1e183665128313004298e2c406a991df` ✓; `HE6_passPE3_report.md` `298b3c973e31648c65b405532b2e28eb` ✓ (full 32 hex digits, exact); `HE6_passPE4_report.md` `14d1b88c25fa8213d2706843f1ce67e6` ✓ (exact).

**Prefix pin — verified and localized.** `234668cb6d24d36a88ddf05ad8617321` = md5 of the file's first **993 lines**, unique hit over all line boundaries.

**Withdrawn pin — confirmed unrecoverable.** The `[r1]`-era `959fff4052e9…` matches **no** file under `verification/` at HEAD (compile-time sweep, 0 hits) — **independently confirming PE2's repo-sweep finding** at `.48`.

**Artifacts — 12 cited, 12 exist:** `verification/openmath/{he6_checks.py, he6_checks_output.txt, he6_checks_results.json, he6_pe4_fresh.py}`, `lean/notes/openmath/{CODEX_HE6PE1_2026-08-08.md, HE6_passPE2_report.md, HE6_passPE3_report.md, HE6_passPE4_report.md, HE6R1_RECON_2026-08-08.md}`, `runs/residues/R6_he6_output.log`, `runs/cert/A3_he6_output.log`, `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`. Plus, from §5.2, `runs/cert2/D2c_he6_output.log` ✓ and `docs/AXIOM_FAITHFULNESS.md` ✓. **Zero missing.**

**`UNPINNED` — none.** Unusually for this corpus, HE6 pins every artifact it names. Its provenance defect is of a different kind: a pin that named **unrecoverable** bytes (`.48`).

---

## 5. Consumption table and consumer edges

### 5.1 What HE6 consumes (forward edges)

`[TABLE]`

| supplier | object | pin | consuming units | load-bearing? |
|---|---|---|---|---|
| GENHN | LEMMA GENHN-2 (the slot lemma) | @ HEAD | `.15` **only** (then everything through it) | YES — “the one load-bearing import” |
| GENHN | LEMMA GENHN-1 (stage ring, node) | @ HEAD | `.04` | frame |
| GENHN | GENHN-3 (window ledger) | @ HEAD | `.44` (battery only) | instrument only |
| HE3 | DEFINITION 1/2, LEMMA HE3-0, LEMMA HE3-1, the THEOREM HE3.A assembly, COROLLARY HE3.B | `7a95449` | `.05`, `.10`, `.16`, `.32` | YES |
| HE3 | HE3-2(b) + HE3-3 (the stage-α class size) | `7a95449` | `.33` | YES, at the ℓ = 1 repeated-linear node |
| classical | resultant symmetry; the ultrametric inequality; uniqueness of `v`; convex duality (★) | — | `.30`, `.24`, `.31`, `.25` | YES |
| HE7 | §S4.1's exact-set argument | — | `.13` (the proof of HE6-1L is HE7's) | YES |
| HE7 + HE6R1 | (LIFT₂)/(SLOT₂) and the widened-box coverage | — | `.39` | **composition claim, not acceptance** |
| FGMN 1305.0775v3 | the higher-order machinery | ledger `63091ce` | `.40` | **NO — a target, not a discharge** |

### 5.2 Reverse-XREF rows — who consumes HE6 (rule 8)

`[TABLE]`

| # | consumer | designation | count | what is consumed | status |
|---|---|---|---|---|---|
| RX-1 | `HE7_PROOF_2026-08-08.md` | `HE6` 209 / `HE6-BOX-1` 11 / the landing heading **1** | HE6-BOX-1 as the obligation HE7 discharges; **and, inbound to HE7, HE6's PE2 F-1 coset correction, LANDED at `5da0552`** | **LANDED both directions** |
| RX-2 | `HE6R1_RECON_2026-08-08.md` | `HE6-BOX-1` 3 / `THEOREM HE6.A` 3 / `HE6R1-1/2/3` 15/13/10 | the widened box's ℓ = 1 branch, the four-case enumeration, and the three composition lemmas; **plus the `[r2]` F-4 repair, applied there** | LANDED |
| RX-3 | `T2_SIGMA_LADDER_MASTER_2026-08-12.md` | `THEOREM HE6.A` 14 + **nine pin names** (32/34/59/48/59/26/55/66/63) | the nine byte-pinned spans of §4.1 | **LANDED — the queue charge's subject** |
| RX-4 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | row 14 | “CHALLENGE (fresh, R6) \| **CERTIFIED 2026-08-12** — A3's 4 repairs folded; D2c: 4/4 DISCHARGED (`runs/cert2/D2c_he6_output.log`)” | LANDED — **supersedes `.62`'s “awaiting sol discharge-confirmation”** |

**Zero-orphan check.** `HE6-BOX-1` has count **0** in `GENIND_PROOF`, `TIGHTNESS_CENSUS`, `HYPOTHESIS_LEDGER`, `PROJECT_STATE` and the SOL ledger; `THEOREM HE6.A` likewise **0** in all five. **So HE6's mathematical content reaches the corpus through exactly three notes — HE7, HE6R1 and T2 — and its status reaches it through the SOL ledger.** Recorded because it means a chapter cut of HE6 has a small, fully enumerated consumer set.

### 5.3 The T2 edge summary (what the DAG should install)

For each pin, the edge T2 needs is `T2:<site> → EFF.HE6.<unit> @ span`. The nine edges are in §4.1. **Three structural notes for the DAG builder:**

1. **`HE6-PROOF` is a conjunction node.** Its own derivation consumes `HE6-ROOT-LABEL`, `HE6-TEST-PACKAGE` (statements), `HE6-ACCOUNT` (proofs of HE6-3/4), plus §S6.1 and §S3.2 — **the last two in no pin span**. So `T2 → HE6-PROOF` is not a leaf edge.
2. **`HE6-TEST-PACKAGE` and `HE6-ACCOUNT` are a statement/proof pair split across two pins.** HE6-3 and HE6-4 are *stated* in the first and *proved* in the second. T2 consumes both, which is correct; a consumer taking only one gets half a lemma.
3. **`HE6-BETA-GUARD` is a composite-reading pin** and T2 already treats it as one (“`HE6-TEST-PACKAGE`, read under `HE6-BETA-GUARD`”). **That device is the template for closing the A3 gap** — see OPEN-CALL 2.

---

## 6. TEETH — the inverse table (rule 6), both directions

### 6.1 Battery row → guarded unit(s)

`[TABLE]`

| leg / tooth | preregistration | guards | disposition |
|---|---|---|---|
| HE6-GEN (72,315) | P1 `.46` | `.30`'s `(†)` identity; `.17`(c),(d) | clean pass; **fractional heights `ℓ′ ∈ {1,2,3}`** — the mechanism that kills (SEP) |
| HE6-SEP (4,232) | P2 `.46` | `.30`(d)'s strictness transfer = LEMMA HE6-4 | clean pass; spot value 42 vs 40 |
| HE6-XI (24 + 6) | P3 `.46` | `.17`(b)'s height clause; mutual genericity | clean pass |
| HE6-SIG (2,226 PARI) | P4 `.46` | `.18` THEOREM HE6.A's dictionary | clean pass, 0 bad; **char-0 only** (`.43`) |
| HE6-RANK | P5 `.46` | the *old* family's inadequacy (a negative control) | clean pass; 3 → 1 spurious vectors |
| HE6-T-UNDET2 | `.52` | `.51` | fired |
| HE6-T-PLANT | `.52` | the checker's refusal behaviour | fired — **tests the instrument, not the note** |
| HE6-T-FLIP | `.52` | the oracle's discriminating power | fired |
| HE6-T-BADKEY | `.52` | `.14`'s `gcd(u,ℓ) = 1` hypothesis | fired — **certifies a hypothesis load-bearing** |
| HE6-T-CASEB | `.37`, `.52` | — | fired — **certifies `.36` (HE6-BOX-1) REAL and `.18`'s separability hypothesis SHARP** |

### 6.2 Guarded unit → battery row (inverse direction)

`[TABLE]`

| unit | guarded by | class |
|---|---|---|
| `.09` `HE6-PEEL-CONVENTION` | — | **PROOF-ONLY** (a hypothesis + a peel argument) |
| `.13` `HE6-LIFT-1L` | the he6r1 battery leg P3 (per `.13`'s route 7); HE7's tooth HE7-T-LIFT2SHARP (route 6) | **externally guarded** — no HE6 leg tests it |
| `.14` `HE6-FAMILY` | HE6-T-BADKEY (the `gcd(u,ℓ)=1` hypothesis) | partially guarded |
| `.15` `HE6-SLOT-SEAM` | — | **PROOF-ONLY** (a scope audit of GENHN-2's proof) |
| `.16` LEMMA HE6-0 | — | **PROOF-ONLY** |
| `.17` `HE6-TEST-PACKAGE` (b),(c),(d) | HE6-GEN, HE6-XI | battery-guarded |
| `.17`(e),(f) = HE6-3, HE6-4 | HE6-GEN, HE6-SEP | battery-guarded |
| `.17`(a),(g) = HE6-0′, HE6-5 | — | **PROOF-ONLY** (`f₁ = 1` rows cannot exercise HE6-5's `f₁ ≥ 2` reach) |
| `.18` THEOREM HE6.A | HE6-SIG (742 octics, 0 exceptions) | battery-guarded at the bite; proof-only at `μ ≥ 5`, `f₁ ≥ 2`, `d ≥ 2` ambients |
| `.19` COROLLARY HE6.B | HE6-T-CASEB + HE6R1-T-CRACK (both branches certified undecided) | **the exclusion is guarded; the inclusion is proof-only** |
| `.29` `HE6-ROOT-LABEL` | — | **PROOF-ONLY** |
| `.30` `HE6-ACCOUNT` | HE6-GEN, HE6-SEP | battery-guarded |
| `.31` LEMMA HE6-5's proof | — | **PROOF-ONLY** |
| `.32` `HE6-PROOF` | HE6-SIG (its conclusion) | conclusion-guarded, argument proof-only |
| `.36` HE6-BOX-1 | HE6-T-CASEB — **certifies it REAL** | inverted guard |
| `.46`–`.52` | — | they *are* the guards |
| `.54`–`.62` appends | — | **AUDIT-produced**, see 6.4 |

### 6.3 PROOF-ONLY rows (rule 16) — the note's own coverage-hole sentences

Eight units are proof-carried. The note supplies the coverage sentences:

HE6-BOX-3 (`.42`):

> “NOT exercised by machine: f₁ ≥ 2 stage genres (so the σ prediction
> {(2,2),(2,2)} of §S2 at (1,2,4) is proof-only), μ ≥ 5, d ≥ 2 ambients, and
> embedded genres. The proofs are uniform in all of these.”

HE6-BOX-4 (`.43`):

> “PARI `factorpadic` exists only on the ℤ_p
> side, so the char-p rows are scored against the reader plus the resultant
> identities”

§S9 (`.53`):

> “**What the machine leg establishes** (instrument grade, not acceptance)”

So `.09`, `.15`, `.16`, `.17`(a), `.17`(g), `.29`, `.31` and the deep reach of `.18` are proof-carried. **Two were later found DEFECTIVE by decorrelated reads** — `.15` by A3 F-1 and `.31` by A3 F-4 — and **both defects were in exactly this proof-only set**. That is the sharpest available evidence for rule 16's existence.

### 6.4 AUDIT dispositions (rule 27) — findings no tooth could produce

`[TABLE]`

| unit | AUDIT class | why no tooth applies |
|---|---|---|
| `.12`/`.13` the (LIFT) strike | `decorrelated-model audit` ×2 | found **independently twice** (Codex PE1 finding 4 and HE7's own FINDING HE7-F1) at two different frames; no HE6 leg tests reachability |
| `.19` the HE6.B scope strike | `in-house hostile pass` | a scope sentence's complement, not a computable quantity |
| `.22` the ψ-cancellation re-proof | `in-house hostile pass` | PE1 finding 5's counter-instance `ξ = −θ` is a *proof* defect with a true conclusion |
| `.48` the runner-pin repair | `arithmetic recount` + `stale self-description` | a provenance defect: a pin naming unrecoverable bytes, plus an unexplained edit window |
| `.55` Correction 1 | `arithmetic recount` | an exhaustive subset-sum over 18 config counts |
| `.56` `HE6-BETA-GUARD` | `in-house hostile pass` | a domain-of-definition defect, invisible to any numerical leg |
| `.58` A3 F-1 | `decorrelated-model audit` | a **vacuous display** consumed by three lemmas and pinned 48× by T2 |
| `.59` A3 F-2 | `decorrelated-model audit` | an unstated positivity assumption inside a proof |
| `.60` A3 F-3 | `decorrelated-model audit` | an “exactly” that should be “only” |
| `.61` A3 F-4 | `decorrelated-model audit` | **an internal contradiction between two spans of the same note, 506 lines apart, surviving four hostile passes** |

**Every one of HE6's eleven post-composition corrections is audit-produced.** Five came from in-house hostile passes, six from decorrelated reads (Codex PE1, HE7's own finding, and the four A3 items). **Not one came from a tooth** — and the note's five teeth all fired clean throughout.

### 6.5 Zero-orphan check

**Battery rows → units: zero orphans.** All five legs and all five teeth guard at least one inventoried unit (6.1) — with two teeth (HE6-T-PLANT, HE6-T-FLIP) guarding the *instrument* rather than a statement, recorded as such.

**Units → guards: 62 units, 22 guarded, 40 unguarded.** The 40 decompose as: 8 PROOF-ONLY (6.3), 1 open obligation (`.36`, inversely guarded), 5 preregistrations (guards, not guarded), and 26 records/scope/append units covered by §4's pin verification and §5's grep verification instead. **No unit is silently unguarded.**

---

## 7. Arithmetic audit and fidelity audit (compile-time, mechanical)

### 7.1 Arithmetic audit — what was recomputed and what it found

**Confirmed exactly (no discrepancies):**

- **All nine pin spans**: 18 delimiter lines, each `grep -cFx` = **1**, each first line strictly preceding its last, each span's content matching the pin's name. **Nine of nine.**
- **T2's own three span statements** (L3863, L4041, L4059) reproduce exactly against HEAD, including the sub-span cite **HE6:644–648** ⊂ [639,666].
- **The prefix pin** `234668cb…` localizes uniquely to line **993**.
- **All five valued md5 pins** reproduce byte-exactly; the **withdrawn** pin `959fff4052e9…` matches nothing under `verification/` — confirming PE2's sweep.
- **`.09`'s counter-instance** `f = Φ′(Φ′+π²)` at `Φ′ = x−π`: `A₀ = 0`, one root with `dv(Φ′(ρ)) = ∞`, `Σ_λ L_λ = 1 ≠ μ = 2`, and the displayed `κ = 2κ` collapse ✓.
- **`.11`'s witness** `(e₁,h) = (2,3) ⟹ i₀ = 1, a₀ = −1, ϖ = xπ^{−1}`, and `dv(ϖ(ξ)) = i₀h + e₁a₀ = 1` exactly ✓.
- **`.12`'s two counter-instances**: `(1,2,1)` at `k = 0` reaches only `F_Q ⊊ K` ✓; `(3,1,2)` at `k = 1` has `T(1) = ∅` ✓ — **both check against the replacement's own `T(k)` formula**, confirming “the two findings name ONE defect”.
- **`.13`'s `(2,2,3)` witness in full**: `i₀(3) = 1`, `T(3) = {0}`, `n(3) = x`, `ϖ(θ)³/n(3)(θ) = θ²π^{−3}`, `q(3) = 1`, prediction `{2η, η}` matching PE2's realized `{η, 2η}`, and the `[r1]` bare span `{1,2}` disjoint from it ✓. Fullness at `k = 9 = (D′−1)h` with `|F₉^×| = 8` ✓.
- **`.13`'s threshold implication** `k ≥ (D′−1)h ⟹ k ≥ (i₀+e₁(f₁−1))h`, since `i₀+e₁(f₁−1) ≤ D′−1` ✓.
- **`.14`'s degree bound** `1 + ℓt ≤ ℓd` for `t ≤ d−1` ✓.
- **`.15`'s sign**: `res(ϖ^k/n(k)) = η^q ⟹ res(n(k)/ϖ^k) = η^{−q}` ✓; witness `γ = 1`, ϖ-read `= 2η` ✓.
- **`.20`'s entire §S2**: `L_λ = ℓd ≥ 4 ⟹ μ ≥ 4 ⟹ n ≥ 8` ✓; the bite polygon `(0,2u)–(4,0)` of slope `u/2`, `u` odd ✓; `Q^{f₁} ≥ 3` at both genres ✓; both predicted σ ✓.
- **`.21`'s neighbour bites**: `(SEP)` needs `2+3+4 = 9`, so `μ ≥ 9`, `n ≥ 18` ✓; HE6-BOX-1 at `L_λ = 4 = μ`, `n = 8` ✓.
- **`.22`'s divisibility** `e₁ | (D′−i)h ⟹ e₁ | i` ✓; `dv(π^{f₁h}) = D′h` ✓; PE1 finding 5's `ξ = −θ` witness ✓.
- **`.24`'s valuation** `dv(y_ρ^ℓ/ϖ(ρ)^u) = ℓλ − u = 0` ✓; `[ι_ρ(K)(β_ρ):F_Q] = f₁d_r` ✓.
- **`.25`'s Step 1 case 2 inequality chain**, re-derived line by line to `ℓ(κ−D′h) + (ℓD′−D′+1)ε > 0` ✓.
- **`.27`'s three-case minimisation** `dκ + t(δ−κ)` ✓.
- **`.28`'s `mod ℓ` step** and its normalizer bookkeeping ✓.
- **`.30`'s sampling and triangular elimination**, both re-derived ✓; and `(d)`'s comparison `ℓd_rD′h_F(λ) = D″h_F(λ)` ✓.
- **`.32`'s four-step sandwich**, every step ✓, including `Σ_rN_r = D′L_λ` and `e·f = N_r` forcing equality.
- **`.45`'s design arithmetic**: 6 rows × 3 configs = **18 config counts** ✓, matching `.55`'s subset-sum domain.
- **`.50`'s entire σ table**: SPLIT PARI `200+200+185+157 = 742` ✓; INERT 742 ✓; ALPHA2 742 ✓; grand total `742×3 = 2,226` ✓; **all four ALPHA2 breakdowns sum to their row counts** (`153+30+17=200`, `176+11+13=200`, `162+12+11=185`, `127+13+17=157`) ✓; members `209+299+185+157+79+57 = 986` ✓.
- **`.51`'s three spurious vectors** `(8,0),(4,4),(0,8)` ✓.
- **`.55`'s corrections** `986` and `2,958 = 3×986` ✓, both matching the Q3 table exactly.
- **`.56`'s instance** `ℓδ − u = 4 − 5 = −1` ✓, and both failure modes (`res = 0` above, undefined below) ✓.
- **`.58`'s exponent identity** `(k−jh)/e₁ + th = (k−ih)/e₁` at `j = i+e₁t` ✓ — re-derived by hand, agreeing with the orchestrator's own re-derivation.
- **`.59`'s three ingredients** `Σn_λ = D′μ`, `ΣL_λ = μ`, `Σc_{λᵢ} = D′B` ✓.
- **`.60`'s implication and its converse's failure** ✓.
- **`.62`'s three line cites** L392–393, L612, L106–107 ✓ — **all exact**.

**Findings — two, neither a mathematical error:**

**AF-1 — `72,315` is not reproducible from the note's displayed figures.** §S9 reports it and Correction 1 re-derives it “arithmetically as Σ members × 3 configs × tests/member”, but `72,315 = 45 × 1,607` (1,607 prime) and `72,315 / 2,958 ≈ 24.45` is not an integer, so tests/member must vary by row — a quantity the note never displays. **Recorded as not independently verified**, honestly rather than passed. The figure has an artifact behind it (`he6_checks_results.json`, md5 verified) and PE2's isolated re-run reproduced it, so it is *warranted*; it is simply not *recomputable from the note*.

**AF-2 — the frozen `1,385` was unreconstructable, and the note says so.** Not a compiler finding but the note's own (`.55`); recorded here because it is the one figure in §S9 that the committed artifacts cannot produce, and because its corrected replacement (**986**) is exactly the sum of the Q3 table's members column — which the frozen headline sat directly above.

### 7.2 Fidelity audit

- **Every CANONICAL STATEMENT is a verbatim quotation.** **No `[ASSEMBLED]` statement appears in this specification** — every one of the 62 units quotes its source span directly, which is possible here because HE6's objects are uniformly displayed as blockquoted lemmas or headed sections.
- **No quantifier, index, inequality direction, exponent, valuation, height, slope, sign, or class size was altered anywhere.** The places where a sign, a quantifier or an “exactly” is discussed as *wrong* (`.15`, `.38`, `.56`, `.60`) are the note's own corrections, quoted.
- **Truncations inside quotations: one**, at `.38`, marked with an explicit note that the intervening development is quoted at its own lines.
- **Rule 14 IS triggered and IS honoured.** §S9 Q3's fixed-width ASCII σ table is emitted **twice** at `.50` — verbatim as the source display, then as a `[TABLE]` transcription — and labelled “emission 1 of 2” / “emission 2 of 2”. **This is the first note in queue 8b where rule 14's letter applies**; EFF-HEX3 and EFF-HMENU3 each recorded that it did not.
- **Terminal punctuation, `∎` marks and LaTeX displays preserved as written.** Strikethrough reproduced, since it marks supersession (`.12`, `.19`, `.22`).
- **All 8 commit hashes, 5 valued md5 pins, 1 prefix pin, 1 withdrawn pin and 14 artifact filenames verified** (§4.3). Zero failures, zero `UNPINNED`.
- **23 external designations plus 9 pin names grep-verified with counts recorded inline** (§4.1–4.2). **Zero NEAR-MISS dispositions** — unusually, every designation HE6 cites exists as written. **Zero invented names, zero designation OPEN-CALLs.**
- **The nine pin spans were verified under T2's own protocol** (`grep -cFx` = 1 on both delimiters, first before last), not merely by content match — because that is the protocol T2's edges depend on.
- **Status and mathematics kept as distinct predicates:** the acceptance record governs grade (`.54`), the SOL ledger governs certification (§5.2 RX-4), and the pin table governs T2's consumption.
- **Every cross-note status claim checked against the target's FULL append chain (rule 10)** — which is how the HE7 landing (`.13`) was confirmed and the “awaiting sol discharge-confirmation” (`.62`) was found stale.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — `LEMMA HE6-0` is consumed by two pinned spans and is itself in no pin span. FOR-0b (T2 owner).

`LEMMA HE6-0` (the disk criterion) sits at **L240–242**, in the two-line gap between `HE6-SLOT-SEAM` [215,238] and `HE6-TEST-PACKAGE` [244,287]. It is consumed **inside** `HE6-ACCOUNT` [525,604] — HE6-3(a)'s proof reads “Every root ρ has λ_ρ = dv(Φ′(ρ)) > D′h (**LEMMA HE6-0** applied to HE3-0's (T1)/(T2))” — and it drives the entire case split of §S3.3 (`.25`). **Its proof (§S3.1, `.22`) is likewise in no pin span**, and is itself corrected by A3 F-3.

Similarly, **§S6.1 (the proof of LEMMA HE6-5) and §S3.2 (the proof of LEMMA HE6-0′) are in no pin span**, though both statements are inside `HE6-TEST-PACKAGE`. So `HE6-PROOF`'s five inputs comprise three pinned spans and two unpinned proofs (`.32`, §5.3 note 1).

**The compiler has invented no span.** **Decision needed:** whether T2 owes a tenth pin (`HE6-0` plus its §S3.1 proof) and, separately, whether the statement/proof split for HE6-0′ and HE6-5 should be pinned as `HE6-TEST-PACKAGE` already pins HE6-3/HE6-4's statements against `HE6-ACCOUNT`'s proofs. **Nothing is wrong with T2 as it stands** — its consumption may not reach HE6-0 at all — but a chapter cut assembled from the nine pins would omit a lemma two of them consume.

### OPEN-CALL 2 — three of the four A3 corrections lie OUTSIDE every pin span, and two of them correct heavily-pinned text. FOR-0b / FOR-0d — the most consequential item in this compilation.

The 2026-08-12 A3 fold corrects four body spans. **All four corrections sit at L1061–1204, outside all nine pin spans.** Their targets:

| A3 finding | corrects | target's pin | T2 count | consequence |
|---|---|---|---|---|
| **F-1** (`.58`) | `LEMMA HE6-0″`'s slot residue `γ` → `γ_k(A)` | **`HE6-SLOT-SEAM` [215,238]** | **48** | a consumer pinning the span gets a display A3 shows is **vacuous** |
| **F-2** (`.59`) | `LEMMA HE6-3(a)`'s inference from `c₀ = 0` | **`HE6-ACCOUNT` [525,604]** | **55** | a consumer pinning the span gets a proof with an unstated positivity assumption |
| **F-3** (`.60`) | §S3.1's “equality exactly at” | *(none — §S3.1 is unpinned)* | — | no edge affected |
| **F-4** (`.61`) | §S6.1's “ϖ ∈ O[x]” | *(none directly; but HE6-5's **statement** is in `HE6-TEST-PACKAGE`)* | 59 | the statement is pinned, its corrected proof is not |

**F-1 is the sharp case.** `HE6-SLOT-SEAM` is T2's second-most-cited HE6 pin, T2 L1616 describes it as “**the corrected normalized-slot/seam display**”, and A3 F-1 is precisely the correction that *makes* it normalized. **If T2's r10/r11-era reading predates the A3 fold, the pin's byte content and T2's description of it have diverged.** This compilation cannot determine T2's intent — `grep -cF 'A3' T2_SIGMA_LADDER_MASTER_2026-08-12.md` and the master's own dating would have to be read against the fold's date, which is a T2-side question.

**The remedy already exists in T2's own practice.** Its r11 round pinned HE6's post-PE4 Correction 2 as its own span, `HE6-BETA-GUARD` [1036,1047], and installed the composite reading “`HE6-TEST-PACKAGE`, read under `HE6-BETA-GUARD`” (`.56`). **The same device applied to A3 F-1 and F-2 would close the gap:** two new pins, say at [1061,1113] and [1115,1154], with `HE6-SLOT-SEAM` and `HE6-ACCOUNT` read under them.

**Decision needed:** whether T2 (a) adds the two pins and the composite readings, (b) extends the two existing spans, or (c) records that its consumption is confined to clauses A3 does not touch. **The compiler has applied nothing and invented no span.** Because this touches another accepted note's pin protocol, it may need Asvin rather than either owner.

### OPEN-CALL 3 — the 9 m 34 s post-run edit window is disclosed, bounded, and permanently unresolvable. FOR-0d — NEEDS ASVIN (as a corpus-policy question).

`.48` records that the committed runner's mtime postdates both artifacts by 9 m 34 s, that “what that window contained is not known”, and that the as-run bytes are unrecoverable (the `959fff4052e9…` pin matches nothing — **independently confirmed here**). PE2 bounded the consequence by re-running the committed runner in isolation and reproducing the artifacts.

**That bound is the right one and it is checkable**, but it establishes “the committed instrument generates the committed verdict”, not “the committed instrument produced the committed verdict”. **The gap is permanent** — no future pass can recover the lost bytes.

**Decision needed:** whether the corpus accepts a reproduced-not-reproducible provenance as sufficient for an ACCEPTED note's machine leg (in which case the convention should be written down, since the same pattern will recur), or whether §S9's numbers should carry a standing disclosure wherever they are cited. **HE6 is ACCEPTED 2/2 and ledger-CERTIFIED with this gap disclosed and unclosed**, so the precedent is already set; what is undecided is whether it is a precedent or an exception.

### Recorded source defects and reading hazards (flagged, not silently repaired)

1. **`.11` vs `.31`: the note contradicted itself for four rounds** on `ϖ`'s coefficient ring (`K₀[x]` at L107, `O[x]` at L613, 506 lines apart). Resolved by A3 F-4; recorded because four hostile passes read both spans and neither flagged it.
2. **`.01`, `.02`, `.03`, `.41`, `.53`: “attempt 0/2” appears in five places.** Only `.53` is superseded by name; the rest are `STALE-SELF-DESCRIPTION`.
3. **`.62`: “awaiting sol discharge-confirmation” is superseded** by SOL ledger row 14 (**CERTIFIED**, D2c 4/4 DISCHARGED). Verified.
4. **AF-1: `72,315` is warranted by artifacts but not recomputable from the note.**
5. **`.47`'s `1,385` is unreconstructable** — the note's own Correction 1, with **zero consumers** audited.
6. **`.48`: a pin that named unrecoverable bytes**, plus an unexplained edit window. Disclosed, bounded, permanent (OPEN-CALL 3).
7. **`.20`'s `{(2,2),(2,2)}` prediction and `.31`'s `f₁ ≥ 2` reach are proof-only** — HE6-BOX-3 fences both, and the battery is `f₁ = 1` throughout. A consumer must not cite the 742-octic result as evidence for either.
8. **`.19`/`.36`: the box's ℓ = 1 branch lives in another note.** A chapter cut of HE6 alone gets half of HE6-BOX-1 and none of the four-case enumeration.
9. **`.39`: “Both suppliers are at attempt grade 0/2” is an as-of record** from `[r1]` and is not re-adjudicated here.
10. **`.23`: HE6's node threshold `D′h` diverges from HE3's and GENHN's `S = e₁h` at `f₁ ≥ 2`.** Reconciled by proof inside HE6; a consumer mixing the two conventions at `f₁ ≥ 2` would mix two numbers under one role.

### Exhaustive residual judgment list

There are no other unresolved HE6 mathematical or scope judgments. HE6-BOX-1 (`.36`, machine-certified real), the (LIFT₂)/(SLOT₂) composition (`.38`, `.39`), the FGMN target (`.40`), the machine-coverage fence (`.42`) and the oracle asymmetry (`.43`) are the note's own displayed standing fences, not compiler ambiguities; the stale grade vocabulary, the unreconstructable headline, and the convention divergence are classified above as bookkeeping. The three OPEN-CALLs are the complete list of judgments the compiler could not make from the text.

### Compilation summary

- **62 statement units**, of which **nine are T2 pin units emitted with verified span identities** — the queue charge's deliverable.
- **The pin table (§1, §4.1) is the DAG key**: nine pins, nine spans, 18 delimiter lines each `grep -cFx` = 1, T2 counts 32/34/59/48/59/26/55/66/63, with T2's own named consumption sites quoted and verified for each.
- **32 external designations and pin names grep-verified**, **zero NEAR-MISS**, zero invented names, zero designation OPEN-CALLs.
- **8 commits + 5 valued md5 pins + 1 prefix pin + 14 artifacts verified; zero failures; zero `UNPINNED`** — and the note's one *withdrawn* pin independently confirmed unrecoverable.
- **4 reverse-XREF consumer edges**, with a fully enumerated consumer set (HE7, HE6R1, T2, the SOL ledger) — `HE6-BOX-1` and `THEOREM HE6.A` have count **0** in GENIND, the census, the hypothesis ledger and PROJECT_STATE.
- **One SERIES** (the seven-member ARC series `.01` → `.02` → `.03` → `.41` → `.53` → `.54` → `.62`), **twelve supersession chains** (C-1…C-12), and **five distinct SUPERSESSION KINDs**.
- **Rule 14 triggered and honoured** for the first time in queue 8b (`.50`, the σ table, emitted twice).
- **Arithmetic audit: every recomputable number reproduced exactly** — the full σ table with all four ALPHA2 breakdowns, all three witnesses (`(1,2,1)`, `(3,1,2)`, `(2,2,3)`), `.25`'s inequality chain, `.30`'s elimination, `.32`'s sandwich, `.58`'s exponent identity, `.59`'s three ingredients, and all three of `.62`'s line cites. Two findings, neither a mathematical error.
- **Honest headline for a chapter cut:** **all eleven of HE6's post-composition corrections were audit-produced; none came from a tooth**, and the five teeth fired clean throughout. Two of the corrections landed on proof-only spans (rule 16's set), one was an internal contradiction that survived four hostile passes, and **three of the four most recent corrections sit outside every T2 pin span** — which is OPEN-CALL 2 and the single most actionable finding here.

EFF-HE6 COMPILED: 62 statements / 32 xrefs verified / 3 open calls
