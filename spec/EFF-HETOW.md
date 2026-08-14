# EFF-HETOW — CANONICAL EFFECTIVE SPECIFICATION v2 (full compilation)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Header

**Source note:** `lean/notes/openmath/HETOW_RECON_2026-08-09.md` (864 lines / 53,279 bytes).

**HEAD blob hash:** `7c15a1140ad1e8ef4bf73f44b4713210d29b1373` (fresh `git hash-object` at compile time; last touched by commit `9f29a28b`).

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a; governing template `spec/EFF_TEMPLATE_v2.md` AT HEAD (rules 1–28). IDs `EFF.HETOW.<nn>`, contiguous, in effective-text order.

**GENRE: TAG-SPARSE PROSE PROOF + SEALED-PREREGISTRATION NUMERICS + POST-ACCEPTANCE APPEND STACK.** `grep -c '\tag{'` = **0** over the whole note, so every statement boundary is a compiler choice; §7 is the mandatory BOUNDARY SELF-AUDIT. Three unit populations must not be conflated (v3 rule 19): **preregistrations** (the sealed runner's menus and teeth), **run-records** (§S6, §S7's supp verdict, the 2026-08-10 machine paragraph), and **proof units** (§S1–S3, LEMMA HETOW-4).

### FREEZE PREDICATES (v3 rule 21 — four, each with its own pin, each independently re-verified)

**FREEZE-1 (sealed-battery instrument freeze).** §S6: “sealed runner `hetow_checks.py` @ commit 1 = 2e5c4b1; no post-seal edit”. `git cat-file -t 2e5c4b1` = commit; the runner and both artifacts exist.

**FREEZE-2 (supp-leg instrument freeze).** §S7: “artifacts `hetowr1_supp_output.txt` / `hetowr1_supp_results.json`, BYTE-FROZEN; runner md5 dcb8452f…, output b52eb226…, results 58f1ce0c…”. **All three re-computed at compile time and all three match**: `dcb8452fba908aa668de188d9021cd8a`, `b52eb226f2507fe921c4aa9437c6c167`, `58f1ce0c88069366172d1a9335566736`.

**FREEZE-3 (text freeze at the 2026-08-10 append).** Its BYTE-FREEZE line: “pre-append body md5 254d1765 (254d176563c21bf2261699f9138e18b5) = commit e38df9f, 41,452 bytes”. **Independently reproduced at compile time**: the note's first **652** lines hash to `254d176563c21bf2…` and measure exactly **41,452 bytes**, and `git cat-file -s` on the `e38df9f` blob of this file returns **41452**. Three independent quantities agree.

**FREEZE-4 (text freeze at the 2026-08-12 absorption append).** Its BYTE-FREEZE line: “pre-append body md5 6ded277db84f9eefb43d46021ba9c7e2”. **Independently reproduced**: the note's first **834** lines hash to `6ded277db84f9eef…` (51,589 bytes).

A fifth, weaker freeze predicate is asserted of OTHER notes and is a NON-IMPORT, not a freeze of this note: “**Frozen-file discipline:** GENHN_PROOF and HE7_PROOF are NOT edited by this unit” (`.05`).

### Effective-text rule (DERIVED — the note states no single rule)

Four source facts fix it.

**(i) The r1 round was applied IN PLACE, at dated tags.** Front matter (lines 17–18): “Repairs landed in place at [r1 2026-08-09] tags”. So every `[r1 2026-08-09 …]` bracket inside §S1–§S6 is already-landed text and the wording it replaces is gone (unlike the LIFTCORNER genre, r1 does NOT quote its predecessor in most places; §S7 is the record of what changed).

**(ii) After PE2 the body is frozen and corrections are dated appends that supersede a QUOTED sentence.** The post-PE2 heading's own italic preamble (lines 545–546):

> “The [r1] body above is BYTE-FROZEN
> — each correction below supersedes its quoted sentence of record.”

**(iii) After PE3 the body including the C-riders is frozen.** Lines 611–612:

> “The body above (through rider C-A/C-B/C-C) is
> **BYTE-FROZEN as of this record — dated appends only.***”

**(iv) The 2026-08-10 append GOVERNS the S1 rows it names, and is itself append-only.** Lines 666–668:

> “the body above stays BYTE-FROZEN — this append GOVERNS the
> S1 rows it names.”

**EFFECTIVE TEXT = the note as written (r1 already landed), READ AS CORRECTED by the four dated append blocks in date order, each superseding exactly the sentence it quotes.** Where two appends touch the same object the later governs; the two collisions are tabulated below.

### Supersession CHAINS (v3 rule 25 — TERMINALs marked)

`[TABLE]`

| Chain | Layers, in source order | TERMINAL |
|---|---|---|
| **CHAIN-KEY (the composed key)** | sealed gauge-naive display (plain lifts ĉ_t, GENHN-T(b)′'s form) → **[r1 F-1]** WRAP-CORRECTED key `Φ₂ := Φ′^{e₂f₂} − Σ_t L_{(f₂−t)u₂}(c_t·η^{W(t)})·Φ′^{e₂t}`, HETOW-1/2 re-proved at it | **[r1 F-1]** (`.13`) |
| **CHAIN-CARRY (HETOW-2's F-2 paragraph)** | sealed “every carry sits at value > T₂” → **[r1 F-2]** re-derived accounting (stationary tail lands in B_t) → **C-A(i)** withdraws the junk exemplar; **C-A(ii)** re-scopes the closing HE7-12 licence to **w = 0** | **C-A** (`.43`) — pinned downstream as `HETOW-KEY-BRIDGE-C-A` |
| **CHAIN-MECH (the §S2 preamble's non-absorption sentence)** | “W(t) is non-linear in t, so no K₂^×-rescale absorbs it” → **C-B** corrects the REASON at f₂ = 2 (the operative pin is `W(f₂−1) = 0` against the monic normalization), conclusion unchanged at frames X/Z/W | **C-B** (`.44`) |
| **CHAIN-BOX3 (machine coverage)** | sealed BOX-3 (no η axis; “uniform in all of these” line) → **[r1 F-3]** adds the η-gauge axis and withdraws the uniformity line → **C-C** adds the f₂ ≥ 3 multi-wrap axis, mooted by frame V → **F-α** folds the e₂f₂ ≥ 4 row against frame S at μ₂ ≤ 2 | **F-α** (`.47`) |
| **CHAIN-J-D0 (the S1 normalizer row)** | sealed justification “unit-residue discrepancy in K₂^× only; σ-content twist-invariant per HE7 §S1 CONVENTION (J-D0)” → **LEMMA HETOW-4** proves the ratio exactly and **supersedes the row** → **T3 absorption** re-homes HETOW-4's clauses (c)/(d)/(b) in `(ABS-HE4)`/`(HE4-COB)`, leaving (a) source-local | **HETOW-4 as absorbed** (`.50`, `.53`, `.57`) |
| **CHAIN-GRADE** | “Attempt grade 0/2” (front matter, §S7) → **post-PE2**: 0/2 → **1/2 and HOLDS THERE** → **post-PE3**: 1/2 → **2/2 — HETOW ACCEPTED** → the 2026-08-10 ratification: “The 2/2 acceptance stands ANNOTATED, now with the annotation DISCHARGED at this note's own grade” | **the 2026-08-10 append** (`.48`) |

### SERIES declared (v3 rule 28)

**SERIES ARC** — the dated pass/repair chronology, one unit per dated entry: `.04` ([r1], from passPE1) → `.42` (post-PE2 corrections preamble, counter 0/2 → 1/2) → `.46` (post-PE3 acceptance, 1/2 → 2/2) → `.48` (2026-08-10 TOWERRAT-R1 ratification, CHALLENGE 3 GAP, annotation discharged) → `.57` (2026-08-12 S-2 absorption). The note's own one-breath statement of the first three links is quoted at `.46`.

**SERIES CORRECTIONS-PE2** — the three dated post-PE2 riders in source order: `.43` (C-A) → `.44` (C-B) → `.45` (C-C). They cure three distinct MINOR findings and have three distinct SUPERSESSION KINDs; merging them would lose the fact that only C-A has a downstream consumer pin.

**SERIES BOX3** — the machine-coverage box's four dated states: sealed → `[r1 F-3]` → `C-C` → `F-α`, compiled as one unit `.30` with the arc recorded inline (the box is a single ledger object whose NOT-exercised list grows), and cross-referenced from `.45` and `.47`. This is the one place this compilation folds a SERIES into a single unit; the reason is audited in §7.2.

### Scope split — THREE predicates (rule 7 + v3 rule 17)

**A. Mathematical absorption / supply SET.** Fixed by the title and §S3: **one reconciliation theorem (HETOW.A, four clauses), three bridge lemmas (HETOW-1/2/3), one derived minimal-degree fact (n_min = 12), and — post-acceptance — one further lemma (HETOW-4).** The claim shape is “literal instance”: the note supplies a TRANSLATION, not new σ machinery. Its own statement of that (lines 48–52):

> “What needs proof is only the
> TRANSLATION between GENHN's composed-carrier coordinates (normalizer
> monomials n̂, letter η₂, residual ψ₂) and HE7's level-2 coordinates
> (normalizers ϖ^mΦ′^s, letter β, residual r): bridge lemmas HETOW-1/2/3,
> all proved in §S2. No hypothesis of HE7.A fails; nothing is boxed.”

**B. Append / consumption PROTOCOL scope — what this note has LANDED elsewhere.** The note's own fence says nothing is landed on its two frozen suppliers (`.05`), and the consumption fold is deferred (HETOW-BOX-4). Verified at compile time:

- **LANDED — GENHN.** `grep -c 'HETOW' GENHN_PROOF_2026-08-08.md` = **7**. The GENHN-side seam IS recorded there, as the note claims (“The GENHN-side seam is recorded at GENHN_PROOF's dated erratum (2026-08-09…)”). XREF X07.
- **LANDED — GENTOW1.** `grep -c 'HETOW' GENTOW1_PROOF_2026-08-09.md` = **5**, including line 575 (“from HETOW PE1 F-1) is a pinned consumption of this note”) and line 612 (“**THE PINNED CORRECTED DISPLAY (per erratum 59c1966 + HETOW [r1]):**”). XREF X08. **This is a reverse consumption the note itself does not record.**
- **NOT LANDED — the [GENHN-HE(μ₂)] rewording.** HETOW-BOX-4 defers it (“a LATER fold”), and no such rewording exists in GENHN: no GENHN occurrence of `discharged-at-grade` (count 0, N2).
- **CONSUMED DOWNSTREAM — T2.** `HETOW-KEY-BRIDGE-C-A` is pinned in `T2_SIGMA_LADDER_MASTER_2026-08-12.md` at line 4246 (count ≥ 1) as a `(PINS)` row over HETOW span **[548, 569]** — the exact span of `.43`. Full consumer trace at `.43`.

**C. Inbound corrections RECEIVED.** Three sources: (i) the three in-house hostile passes PE1/PE2/PE3; (ii) the **decorrelated codex ratification** `CODEX_TOWERRAT_2026-08-10.md` (CHALLENGE, 3 GAP), which produced the note's fifth lemma; (iii) the **S-2 simplification pass**, which absorbed that lemma into T3. Class (ii) is the one that changed the mathematics: F-1 REAL → LEMMA HETOW-4.

### Resolution rules applied

1. `[r1 2026-08-09 …]` brackets are already-landed text; the sealed wording they replace survives only where §S7 or a C-rider quotes it, and is then DEAD.
2. Each dated append supersedes exactly the sentence it quotes; where an append re-scopes rather than replaces, the unit carries the original as CANONICAL STATEMENT and the re-scoping in CONDITIONALITY with its KIND declared.
3. **The `[TABLE]` in §S1 is a unit** (`.09`), transcribed row-for-row, with the two rows superseded from outside (the normalizer row and the (SLOT₂) row) carrying their post-HETOW-4 reading inline.
4. Numbers are recomputed from the committed artifacts, never transcribed: §S6's totals, §S7's supp verdict, the per-row census, and all four byte-freeze md5s.
5. **Quotations of OTHER notes are re-verified verbatim.** One fails and is recorded as a fidelity finding, not silently repaired (`.54`, OPEN-CALL 3).
6. LEMMA HETOW-4's statement is byte-frozen and authoritative even after the T3 absorption — the absorption append says so explicitly, and the unit records both citation routes.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; `…` marks truncation. The two source tables (§S1's instantiation map, §S6's per-row census block) are emitted as tables and flagged `[TABLE]`; the census block is rendered in the source as a fixed-width ASCII display inside prose, so per v3 rule 14 it is emitted TWICE — verbatim, then transcribed. No source display is prosified.

---

## 2. Statement inventory

58 units, contiguous, in effective-text order. FORM is carried on every unit (v3 rule 11; the note is tag-sparse).

### EFF.HETOW.01  [convention]

**CANONICAL STATEMENT:**

> “**Unit:** HE-TOW (BOX-CLOSURE campaign, reconciliation pattern = HE6R1).”

**FORM:** bold-headed line.

**DERIVATION:** `[RECORD]` — an identification plus a method citation. The “pattern = HE6R1” is load-bearing and is spelled out at `.07`: a box that looks new can be a literal instance of frozen machinery once the instantiation map is written.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** statement line 3.

**TEETH:** XREF X05 verifies `HE6R1_RECON_2026-08-08.md` exists and carries the pattern.

---

### EFF.HETOW.02  [fence]

**CANONICAL STATEMENT:**

> “**Consumes:** GENHN @ HEAD (LEMMA GENHN-T(b)′, S8 annex [r2/r3]; [GENHN-TOW-1];
> [GENHN-HE(μ ≥ 3)]) · HE7 @ ca3754d FULLY FROZEN (§S1–S6, THEOREM HE7.A/C/D,
> LEMMA HE7-12/13, ANNEX R's HE7-2′ cocycle tower) · HE6 @ HEAD post-r2
> (DEFINITION HE6-1, LEMMA HE6-0″ [r2], COROLLARY HE6-2″) · HE6R1_RECON @ HEAD
> (the pattern model; LEMMA HE6R1-2/HE6R1-3).”

**FORM:** bold-headed inventory paragraph.

**DERIVATION:** `[RECORD]` — the import inventory, with one supplier pinned to a COMMIT (HE7 @ ca3754d) and three to HEAD.

**CONDITIONALITY:** **the pinning is asymmetric and that asymmetry matters.** HE7 is commit-pinned and declared FULLY FROZEN; GENHN, HE6 and HE6R1 are HEAD-pinned, so their later movement is not fenced by this sentence. GENHN in fact moved after this note was written — it received the 2026-08-09 dated erratum this note's own r1 caused (`.39`) — so the HEAD pin is a live edge, not a frozen one.

**RESOLUTION TRACE:** statement lines 4–8.

**TEETH:** `git cat-file -t ca3754d` = commit (P-01). All four supplier files verified to exist. The 2026-08-10 append later adds a fifth consumed object not in this list — the frozen **HE7 §S1/§S5.3** bracket display, used by HETOW-4(c) — so this inventory is incomplete as of HEAD; recorded, not repaired.

---

### EFF.HETOW.03  [scope record]

**CANONICAL STATEMENT:**

> “**Status:** instantiation map + bridge lemmas PROVED (§S1–S3); battery sealed
> at commit 1 and scored at commit 2 (§S5–S6). **Attempt grade 0/2.** Every
> consequence inherits min over {GENHN 0/2, HE6 0/2 post-r2, HE7 (frozen,
> accepted annex stack), HE3 1/2 at μ ≤ 3}.”

**FORM:** bold-headed status paragraph.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the grade is superseded twice** (CHAIN-GRADE): 0/2 → 1/2 at `.42`, 1/2 → **2/2 ACCEPTED** at `.46`. SUPERSESSION KIND: **counter re-reading**. **The min-inheritance clause is NOT superseded** — the acceptance record restates it verbatim (“Consequences inherit min over {GENHN 0/2, HE6 0/2 post-r2, HE7 (frozen, accepted annex stack), HE3 1/2 at μ ≤ 3} per the status header”), so HETOW's own 2/2 does not lift its consequences above the weakest supplier. A consumer citing “HETOW ACCEPTED 2/2” without the min clause overstates by three grades.

**RESOLUTION TRACE:** statement lines 9–12; correction sites 543–545 (→1/2), 614–616 (→2/2); the min clause restated at 630–632.

**TEETH:** the four supplier grades are the note's own assertions about other notes; each is an as-of claim at 2026-08-09 and none is re-verified here (they are grade claims, not designations). Disposition `as-of scoping`, and see OPEN-CALL 5.

---

### EFF.HETOW.04  [repair-round record]  *(SERIES ARC, link 1)*

**CANONICAL STATEMENT:**

> “**[r1 2026-08-09]:** passPE1 (report @ 5f821dc) returned NOT CLEAN —
> 1 CRITICAL (F-1 wrap-cocycle seam in the sealed HETOW-1/2 and
> HETOW.A(i)'s key clause at η ≠ 1 frames) + 2 GAP (F-2 carry-tail
> accounting; F-3 BOX-3 gauge disclosure) + 2 MINOR (F-4 lift object;
> F-5 S6 caveat). Repairs landed in place at [r1 2026-08-09] tags: the
> key WRAP-CORRECTED (ĉ_t ↦ L_{(f₂−t)u₂}(c_t·η^{W(t)}), §S2 preamble),
> HETOW-1/2 restated and re-proved at it, BOX-3/S6 disclosures, supp
> machine leg `hetowr1_supp.py` (§S7). Grade stays 0/2; PE2 next. The
> GENHN-side seam is recorded at GENHN_PROOF's dated erratum
> (2026-08-09; GENHN stays ACCEPTED 2/2, appends only).”

**FORM:** bold-headed bracketed round record.

**DERIVATION:** `[RECORD]` of a hostile pass and its five dispositions, each compiled at its own home site: F-1 at `.13`/`.15`, F-2 at `.19`, F-3 at `.30`, F-4 at `.18`, F-5 at `.36`.

**CONDITIONALITY:** the counter is superseded (`.03`). The GENHN-side clause is a claim about ANOTHER note and is verified positively below.

**RESOLUTION TRACE:** statement lines 13–22; §S7's full record at 473–535.

**TEETH:** `git cat-file -t 5f821dc` = commit; `HETOW_passPE1_report.md` exists. XREF X07: `grep -c 'HETOW' GENHN_PROOF_2026-08-08.md` = **7** — the GENHN-side seam record is real and landed, not merely intended. This is the note's one LANDED cross-note edit and it is verified.

---

### EFF.HETOW.05  [fence]

**CANONICAL STATEMENT:**

> “**Frozen-file discipline:** GENHN_PROOF and HE7_PROOF are NOT edited by this
> unit; consumption updates are a later fold.”

**FORM:** bold-headed fence.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **a tension with `.04`, and the note resolves it correctly.** `.04` says the GENHN-side seam “is recorded at GENHN_PROOF's dated erratum”; `.05` says GENHN_PROOF is not edited by this unit. Both are true: the erratum is GENHN's OWN dated append, made by its owner in response to this note's finding, not an edit by HETOW. The distinction is exactly the supplier-finding/appended-at-source pattern (v3 rule 13) and is preserved throughout this compilation.

**RESOLUTION TRACE:** statement lines 23–24; the later-fold deferral restated at HETOW-BOX-4 (`.31`).

**TEETH:** verified negatively — GENHN carries no “absorbed by HETOW” heading and no `discharged-at-grade` string (N2).

---

### EFF.HETOW.06  [convention]

**CANONICAL STATEMENT:**

> “GENHN-T(b)′(iii) proves the tower-leaf σ-decision at inner multiplicity
> μ₂ = 2 (S7's trichotomy run verbatim at the composed data) and BOXES
> inner μ₂ ≥ 3 as [GENHN-HE(μ₂)] — the one surviving box family of GENHN's
> σ layer, since the ordinary-leaf [GENHN-HE(μ)] was closed by the
> HE3→HE6→HE7 ladder (COROLLARY HE7.B).”

**FORM:** inline paragraph opening `## S0. THE QUESTION, AND THE ANSWER'S SHAPE`.

**DERIVATION:** `[IMPORTED]` — a statement of the problem's provenance in GENHN.

**CONDITIONALITY:** “the one surviving box family of GENHN's σ layer” is an as-of-2026-08-09 inventory claim about GENHN; it is not re-verified here (a box census of GENHN belongs to `spec/EFF-GENHN-*`).

**RESOLUTION TRACE:** statement lines 30–34.

**TEETH:** XREF X01 verifies GENHN carries `GENHN-T(b)′`-family text; the box designation `[GENHN-HE(` is present in GENHN.

---

### EFF.HETOW.07  [scope record]

**CANONICAL STATEMENT:** the question and the answer's shape, verbatim:

> “> Is the tower-stage σ read at inner μ₂ ≥ 3 — the (j, p_j)-polygon of the
> > Φ₂-adic development of f on the composed dv₂-ladder with residuals over
> > K₂ = F_{Q^{f₁f₂}} — THEOREM HE7.A at the level-2 datum
> > (λ, r) = (κ₂, r̃), (ℓ, d_r) = (e₂, f₂), key = Φ₂?
>
> **Answer: YES — literal instance** (THEOREM HETOW.A, §S3). The structural
> reason: a tower stage with inner μ₂ ≥ 2 IS a widened-box node —
> its side carries the repeated irreducible residual ψ₂ (multiplicity μ₂)
> with ℓ·d_r = e₂f₂ ≥ 2, exactly COROLLARY HE6.B [r1]'s excluded
> configuration — and HE7 §S1–S6 is stated at ANY level-2 datum with no
> hypothesis on ℓ or d_r (HE6R1 §S3.1).”

**FORM:** blockquoted question + bold-headed answer paragraph.

**DERIVATION:** the structural reason is an appeal to HE7's own generality (“stated at ANY level-2 datum with no hypothesis on ℓ or d_r”), sourced to HE6R1 §S3.1. **This is the load-bearing meta-claim of the whole note** and it is the one thing that makes “literal instance” more than a slogan.

**CONDITIONALITY:** the no-hypothesis-on-(ℓ, d_r) claim about HE7 is a claim about another note's scope, cited to HE6R1 §S3.1 rather than re-derived. It is not re-verified here; see OPEN-CALL 4.

**RESOLUTION TRACE:** statement lines 38–52.

**TEETH:** the machine form of the claim is §S6's P2 headline (`.35`): the FROZEN readers, byte-unmodified, decide every member. That is the strongest available evidence for “no change needed”.

---

### EFF.HETOW.08  [convention]

**CANONICAL STATEMENT:**

> “**The tower setting (verbatim GENHN-T(b)′):** outer genre
> (Q; e₁, f₁, μ₁; h), key Φ′ (deg D′ = e₁f₁), level-1 development
> f = Φ′^{μ₁} + Σ_{J<μ₁} A_J Φ′^J; an inner CS event: a side of the
> (J, dv(A_J))-polygon of slope κ₂ = u₂/e₂ (lowest terms), κ₂ > D′h ([r1]
> node floor), carrying residual ψ₂^{μ₂} over K, f₂ := deg ψ₂,
> **e₂f₂μ₂ = μ₁ (FULL inner side — T(b)′'s own scope)**; composed key
> **[r1 2026-08-09 (passPE1 F-1): WRAP-CORRECTED]**
> Φ₂ := Φ′^{e₂f₂} − Σ_{t<f₂} L_{(f₂−t)u₂}(c_t·η^{W(t)})·Φ′^{e₂t},
> W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋ (§S2 preamble; at f₁ = 1 the coefficient is
> lift(c_t·η^{W(t)})·n̂(u₂(f₂−t)); GENHN-T(b)′'s displayed plain lifts
> ĉ_t are the gauge-naive form — corrected at the source by GENHN's
> dated erratum of 2026-08-09), deg D₂ = D′e₂f₂;
> composed ladder dv₂ = e₁e₂v.”

**FORM:** bold-headed setting paragraph carrying an inline display.

**DERIVATION:** `[IMPORTED]` verbatim from GENHN-T(b)′, **except** the composed key, which is [r1]-corrected here and at the source.

**CONDITIONALITY:** the FULL inner side (e₂f₂μ₂ = μ₁) is T(b)′'s own scope and is HETOW-BOX-1's fence (`.28`); the node floor κ₂ > D′h is an [r1] input consumed by HETOW-2's carry accounting.

**RESOLUTION TRACE:** statement lines 58–70; the key's derivation at 110–137.

**TEETH:** the “corrected at the source” claim is verified — GENTOW1 line 612 carries `**THE PINNED CORRECTED DISPLAY (per erratum 59c1966 + HETOW [r1]):**` (XREF X08), and GENHN carries seven HETOW references (X07). The correction propagated to two other notes.

---

### EFF.HETOW.09  [table]  `[TABLE]`

**CANONICAL STATEMENT:** the instantiation map, source lines 74–91, transcribed row-for-row (the source renders it as a Markdown table):

| HE7 hypothesis / object | tower instantiation | check |
|---|---|---|
| λ = u/ℓ lowest terms | λ = κ₂ = u₂/e₂, gcd(u₂,e₂) = 1 | T(b)′ setting ✓ |
| λ > D′h | κ₂ > D′h | the [r1] node floor, cited by T(b)′ ✓ |
| r ∈ K[Z] monic irreducible, r(0) ≠ 0 | r := r̃, the ϖ-normalized twist of ψ₂ | **HETOW-1** (§S2) |
| Ψ = Ψ_{λ,r} (DEF HE6-1), deg D″ = D′ℓd_r | Φ₂, deg D₂ = D′e₂f₂ = D″ | **HETOW-2** (§S2): Φ₂ = Ψ_{κ₂,r̃} − w, dv₂(w) > T₂ ⟹ LEMMA HE7-12 |
| dv₂ = ℓ·dv = e₁ℓ·v | e₂·(e₁v) = e₁e₂v | = T(b)′'s composed ladder ✓ |
| K₂ = K[Z]/(r) ≅ F_{Q^{f₁d_r}} | K[Z]/(r̃) ≅ K(η₂) = F_{Q^{f₁f₂}} | HETOW-1(a); = T(b)′(i)'s residue field ✓ |
| T₂ = ℓd_r·u | e₂f₂·u₂ | arithmetic ✓ |
| level-2 point: (T1),(T2), dv(Φ′(ξ)) = λ, ι(r)(β_ξ) = 0 | tower-node locus: (T1),(T2),(T1₂),(T2₂) | HETOW-1(b): β_ξ = η_ξ^{−Q(u₂)}·η₂(ξ), r̃(β) = 0 ⟺ ψ₂(η₂) = 0 ✓ |
| n₂(k) = ϖ^{m(k)}Φ′^{s(k)}, ℓm + su = k | vs GENHN's ladder monomials n̂₂(m) = π^ax^iΦ′^b | unit-residue discrepancy in K₂^× only; σ-content twist-invariant per HE7 §S1 CONVENTION (J-D0) |
| §S1 CONVENTION Ψ ∤ f_S | Φ₂ ∤ f, else LEMMA HE6R1-3 peel | **HETOW-3(c)**; peel available at Φ₂ via HE7-12(c) item (11) |
| HE7.A: (λ,r) a label of f (COR HE6-2″) | every root of f on the locus has label (κ₂, r̃) | **HETOW-3(b)** (full side) ✓ |
| HE7.A: f_S the block factor, μ₂ = deg f_S/D″ | f_S = f, μ₂ = μ₁/(e₂f₂) ∈ ℤ | **HETOW-3(a)(b)** ✓ |
| level-1 frame: f monic, disc f ≠ 0, Φ′ ∤ f | Φ′ ∤ f automatic at a full side | **HETOW-3(a)** ✓ |
| (SLOT₂)'s slot formula | GENHN-2′ (T(b)′(ii)) | THE SAME FORMULA: min_{i,s}(e₁e₂v + i·e₂h + s·u₂) — substitution ℓ=e₂, u=u₂ in min_s(ℓ·dv(c_s)+su), dv(c_s)=min_i(e₁v+ih) ✓ (residues: same content, letters related by HETOW-1's unit) |
| pins P₂ = {(j, dv₂(A_j^{(2)}))} | T(b)′(iii)'s p_j = dv₂(C_j(x₀)) | identical: same development (key = Φ₂), pins read exactly by (SLOT₂) = GENHN-2′ ✓ |
| ladder/termination (HE7.C/D, ANNEX R HE7-2′) | the tower node is a widened-box jump with ℓd_r = e₂f₂ | μ₁ ≥ μ₂·e₂f₂ (equality at full side) = HE7.C's bound, tight; level 3 needs μ₂ ≥ 4 ✓ |

**FORM:** table (16 rows).

**DERIVATION:** thirteen rows are verbatim transports; three (marked **HETOW-n**) are the translations proved in §S2.

**CONDITIONALITY — THREE ROWS ARE SUPERSEDED FROM OUTSIDE and a consumer must apply all three:**
1. **The normalizer row** (`n₂(k) …` vs `n̂₂(m)`). Its justification cell is REPLACED by the 2026-08-10 append (`.53`); the new reading is quoted there. SUPERSESSION KIND: **replacement**.
2. **The (SLOT₂) row's parenthetical** “(residues: same content, letters related by HETOW-1's unit)” is RE-READ by the same append: “same content AFTER the brackets, with the per-height comparison given by τ”. KIND: **wording-rider**.
3. **The level-1 frame row's ✓ column** is SCOPED by the F-3 annex (`.55`): the ✓ discharges only `Φ′ ∤ f`; “f monic” and “disc f ≠ 0” are inherited frame data, not obligations discharged here. KIND: **scope-pin**.
Additionally the **Ψ-row's** closing licence (`dv₂(w) > T₂ ⟹ LEMMA HE7-12`) is re-scoped by C-A(ii) to the `w = 0` branch (`.43`), and its missing `deg w < D″` conjunct is supplied master-side by T2's r12 — see the consumer trace at `.43`.

**RESOLUTION TRACE:** statement lines 74–91; correction sites 793–809 (rows 1–2), 821–828 (row 3), 556–569 (the Ψ-row licence).

**TEETH:** ARITHMETIC AUDIT of the two arithmetic rows, recomputed: `dv₂ = e₂·(e₁v) = e₁e₂v` ✓; `T₂ = ℓd_r·u = e₂f₂·u₂` ✓; `deg D₂ = D′e₂f₂ = D″` with `D″ = D′ℓd_r` ✓ — the three are consistent and are exactly the identities T2's r12 later uses to derive the degree bound master-side.

---

### EFF.HETOW.10  [scope record]

**CANONICAL STATEMENT:**

> “**No hypothesis fails.** The three rows marked HETOW-n are translations,
> proved next; every other row is verbatim.
> **[r1 2026-08-09 (passPE1 F-1)]:** the r̃-row and the Ψ-row hold AT the
> wrap-corrected key (§S2); at the sealed gauge-naive display they FAIL
> at η ≠ 1 wrap frames (frame X counter-instance, §S2 preamble) — the
> sealed table was sound only on the battery's η = 1 gauge.”

**FORM:** bold-headed closing claim + a dated bracket.

**DERIVATION:** `[RECORD]` of the table's verdict, with the r1 scope correction attached.

**CONDITIONALITY:** **the second sentence is the note's own record of a refuted prior state**: the sealed table was FALSE at η ≠ 1. The correction is landed in place, so the false version survives nowhere except in this description and in §S7's F-1 record.

**RESOLUTION TRACE:** statement lines 93–98.

**TEETH:** the counter-instance is machine-scored twice — `hetow_pe1_fresh.py` (frame X, dual oracle routes) and `hetowr1_supp.py` (frames X/Z/W). Both artifacts verified present.

---

### EFF.HETOW.11  [definition]

**CANONICAL STATEMENT:**

> “Throughout: Q(k) := (i₀k − i(k))/e₁ = ⌊i₀k/e₁⌋ ∈ ℤ≥0, where
> n̂(k) = x^{i(k)}π^{a(k)} (0 ≤ i(k) < e₁) and ϖ = x^{i₀}π^{a₀}. At every
> (T1)/(T2) point ξ, res(n̂(k)(ξ)/ϖ(ξ)^k) = η_ξ^{−Q(k)} — this is LEMMA
> HE6-0″ [r2]'s coset factor with γ = 1 (both sides have dv = k; the wrap
> ξ^{e₁} = η-unit·π^h applied Q(k) times; sign per the [r2] correction).”

**FORM:** inline definitional paragraph opening §S2.

**DERIVATION:** `[IMPORTED]` from LEMMA HE6-0″ [r2], specialized to γ = 1.

**CONDITIONALITY:** the sign convention is inherited from HE6's [r2] correction — a live dependency on a HEAD-pinned supplier (`.02`).

**RESOLUTION TRACE:** statement lines 104–108.

**TEETH:** XREF X03 verifies `HE6_PROOF_2026-08-08.md` carries `HE6-0″`-family text at count ≥ 1.

---

### EFF.HETOW.12  [lemma]

**CANONICAL STATEMENT:**

> “**[r1 2026-08-09] THE WRAP COCYCLE (passPE1 F-1's mechanism,
> re-derived).** The normalizer monomials are NOT multiplicative: with
> wrap(a,b) := ⌊(i(a)+i(b))/e₁⌋ ∈ {0,1} one has i(a)+i(b) = i(a+b) +
> e₁·wrap(a,b), and (heights add)
>
>     n̂(a)·n̂(b) = n̂(a+b)·(x^{e₁}/π^{h})^{wrap(a,b)} ,
>     Q(a+b)     = Q(a) + Q(b) + wrap(a,b) .
>
> Telescoping on the tower heights, with **W(t) := ⌊(f₂−t)·i(u₂)/e₁⌋**:
>
>     n̂(u₂)^{f₂−t}  = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)} ,
>     Q((f₂−t)u₂)   = (f₂−t)·Q(u₂) + W(t)
>
> (both because (f₂−t)i(u₂) = i((f₂−t)u₂) + e₁·W(t): the two sides are
> ≡ mod e₁ and 0 ≤ i(·) < e₁).”

**FORM:** bold-headed dated lemma with two ASCII displays.

**DERIVATION:** floor arithmetic on the level-1 ladder equation, proved in the parenthetical (congruence mod e₁ plus the range constraint `0 ≤ i(·) < e₁` pins the quotient).

**CONDITIONALITY:** none. **This is the mechanism the CRITICAL turned on**, and it is the algebraic core reused three times later: at HETOW-1(c), at the key correction, and — generalized to a two-floor cocycle — at HETOW-4(b).

**RESOLUTION TRACE:** statement lines 110–123.

**TEETH:** the supp leg's E-leg checks `W(0)` two ways at each of frames X/Z/W (§S7); the 2026-08-10 leg checks identity (a) at k = 1..60 per frame. ARITHMETIC AUDIT: at frame X (e₁ = 2, u₂ = 3, f₂ = 2), `i(3) = 1`, so `W(0) = ⌊2·1/2⌋ = 1` and `W(1) = ⌊1·1/2⌋ = 0` — matching the note's `W = (1,0)` for frames X/Z/W ✓, and matching C-B's operative pin `W(f₂−1) = 0` ✓.

---

### EFF.HETOW.13  [definition]  *(CHAIN-KEY — TERMINAL)*

**CANONICAL STATEMENT:**

> “**THE WRAP-CORRECTED KEY** (used by every [r1]-restated statement
> below; it replaces the sealed display):
>
>     Φ₂ := Φ′^{e₂f₂} − Σ_{t<f₂} L_{(f₂−t)u₂}(c_t·η^{W(t)}) · Φ′^{e₂t} ,
>
> where L_k(c) is the (LIFT) exact-height-k lift of c ∈ K: for
> c = Σ_{j<f₁} d_j η^j, L_k(c) := Σ_j lift(d_j)·x^{i(k)+e₁j}π^{a(k)−jh}
> (x-degree ≤ D′−1; every monomial at dv-height k exactly; at f₁ = 1
> this is lift(c·η^{W(t)})·n̂((f₂−t)u₂)). Its ϖ-residue at height k is
> c·η^{−Q(k)}, since each basis monomial is n̂(k)·(x^{e₁}/π^h)^j with
> residue η^{−Q(k)}·η^j.”

**FORM:** bold-headed definition with an ASCII display and an inline (LIFT) construction.

**DERIVATION:** the residue computation is done in place; the exact-height property is by construction of `L_k`.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement** (of the sealed gauge-naive display). **The (LIFT) form is the object every consumer feeds downstream** — C-A(ii) later re-scopes HETOW-2's HE7-12 licence to exactly this form, and T2's pin `HETOW-KEY-BRIDGE-C-A` governs that re-scoping.

**RESOLUTION TRACE:** statement lines 128–138.

**TEETH:** the supp leg's E-legs check “corrected-key slot residues = minpoly(β) at each frame (X: Z²+2Z+2; Z/W: Z²+3Z+4)” — a direct machine check of the residue computation displayed here, at three frames, verified GREEN in the committed artifact.

---

### EFF.HETOW.14  [supplier-finding]

**CANONICAL STATEMENT:**

> “The gauge-naive display (plain lifts ĉ_t of
> c_t — GENHN-T(b)′'s displayed form, consumed by this note's sealed
> S1/S2) differs at the slot residue by η^{−W(t)} per digit and is a
> DIFFERENT polynomial whenever some c_t·(η^{W(t)} − 1) ≠ 0; at such a
> frame the naive key is NOT the composed carrier. Counter-instance
> (passPE1 frame X, both oracle routes): p = 3, Φ′ = x² − 6, η = 2,
> (e₂,f₂) = (1,2), u₂ = 3, W(0) = 1 — naive key Φ′² + 3xΦ′ + 54 has
> PARI σ = {(4,1)} and degenerate slot polynomial (Z+1)²; corrected key
> Φ′² + 3xΦ′ + 108 has σ = {(2,2)} and slot polynomial = minpoly(β) =
> Z² + 2Z + 2. Re-confirmed at two further η ≠ 1 frames (one at e₁ = 3)
> by `hetowr1_supp.py` with the gauge-naive tooth firing per frame
> (§S7). Both sealed battery frames have η = 1, where naive = corrected
> — the seal could not see the seam (HETOW-BOX-3 [r1]).”

**FORM:** inline paragraph carrying a named counter-instance.

**DERIVATION:** a constructed counter-instance, adjudicated by an independent oracle on two routes.

**CONDITIONALITY:** **this is a `supplier-finding` (v3 rule 13): the defect is in GENHN-T(b)′'s displayed form, and it is discharged AT THE SOURCE** by GENHN's dated erratum of 2026-08-09, not by a lemma of this note. The note says so at `.08` and `.39`.

**RESOLUTION TRACE:** statement lines 138–150.

**TEETH:** `AUDIT / in-house hostile pass` — passPE1 found it; no battery could have, and the note is explicit about why (“the seal could not see the seam”). ARITHMETIC AUDIT of the counter-instance: at η = 2, W(0) = 1, the corrected constant is `lift(c₀·η^{W(0)})·n̂(2u₂)` versus the naive `lift(c₀)·n̂(2u₂)`; 54·2 = **108** ✓ — the displayed pair differs by exactly the factor η^{W(0)} = 2, as the mechanism predicts. Both σ values are machine-scored on dual routes in the committed supp artifact.

---

### EFF.HETOW.15  [lemma]

**CANONICAL STATEMENT:**

> “> **LEMMA HETOW-1 (label translation) [r1 2026-08-09 (passPE1 F-1)
> > restated: r̃ has ONE definition (the minimal polynomial); the
> > slot-residue characterization is clause (c), true at the
> > wrap-corrected key and FALSE at the gauge-naive display].** Set
> > Q := Q(u₂), fix a root η₂ of ψ₂, and define r̃ ∈ K[Z] as the minimal
> > polynomial of β := η_θ^{−Q}·η₂ over K. Then:
> > (a) r̃ is monic irreducible of degree f₂ with r̃(0) ≠ 0, and
> > K[Z]/(r̃) = K(β) = K(η₂) ≅ F_{Q^{f₁f₂}}; explicitly
> > r̃ = η^{−Qf₂}·ψ₂(η^{Q}Z), with t-coefficient −c_t·η^{−(f₂−t)Q};
> > (b) at every point x₀ of the tower-node locus,
> > β_{x₀} := res(Φ′(x₀)^{e₂}/ϖ(x₀)^{u₂}) = η_{x₀}^{−Q}·η₂(x₀), and
> > r̃(β_{x₀}) = 0 ⟺ ψ₂(η₂(x₀)) = 0; hence the tower-node locus IS the
> > level-2 point set of the datum (κ₂, r̃);
> > (c) [slot residues — AT THE WRAP-CORRECTED KEY] for each t < f₂ the
> > ϖ-residue of the corrected Φ₂'s slot-e₂t coefficient at height
> > (f₂−t)u₂ equals r̃'s t-coefficient; at the gauge-naive key the
> > residue is −c_t·η^{−(f₂−t)Q−W(t)} instead, and the polynomial these
> > assemble need not be irreducible (frame X: (Z+1)²).”

**FORM:** blockquoted bold-headed lemma with three clauses.

**DERIVATION:** `.16`.

**CONDITIONALITY:** **the [r1] restatement is a DEFINITIONAL repair, not a scope fix**: the sealed lemma gave r̃ two definitions and called them equivalent; they are not. The repair makes minpoly(β) the sole definition and demotes the slot-residue property to a clause that must be PROVED. That is a supersession of the definitional structure of the lemma. SUPERSESSION KIND: **replacement**.

**RESOLUTION TRACE:** statement lines 152–169; proof 171–196; the diagnosis at 479–485.

**TEETH:** clause (b) is the **load-bearing seam detector** at σ-blind faces, per C-B (`.44`) and the acceptance record (`.46`): “the letter clause (ψ₂(η₂(ξ)) = 0, HETOW-1(b)/T(b)′(i)) standing as the load-bearing seam detector at the σ-blind faces (PE2 frame V at f₂ = 3; PE3 frame M2 at f₂ = 4)”. Clause (c) is machine-checked at three frames by the supp leg and at three more by the 2026-08-10 leg.

---

### EFF.HETOW.16  [derivation]

**CANONICAL STATEMENT:** HETOW-1's proof, source lines 171–196. Clause-by-clause, verbatim:

> “*Proof.* (a) K(β) = K(η₂) because η^{−Q} ∈ K^×; [K(η₂):K] = f₂ (ψ₂
> irreducible, T(b)′(i)); β is a root of the monic degree-f₂ polynomial
> η^{−Qf₂}ψ₂(η^{Q}Z) (substitute β), so that polynomial IS its minimal
> polynomial; its t-coefficient is −c_t·η^{Qt−Qf₂} = −c_t·η^{−(f₂−t)Q};
> the constant term η^{−Qf₂}ψ₂(0) ≠ 0 — ψ₂(0) ≠ 0 because at a FULL
> side the left endpoint (0, dv(A_0)) is an attained pin (A_0 ≠ 0), so
> the side residual R_{κ₂} = ψ₂^{μ₂} has nonzero constant term.”

> “(b) Φ′^{e₂}/ϖ^{u₂} = (Φ′^{e₂}/n̂(u₂))·(n̂(u₂)/ϖ^{u₂}); the first
> factor's residue is η₂(x₀) by (T2₂)'s definition, the second is
> η_{x₀}^{−Q} by the preamble display; the root equivalence is the
> K-affine substitution Z ↦ η^{Q}Z. POINTWISE, hence wrap-free: only the
> single height u₂ is normalized — no product of normalizers occurs.”

> “(c) The corrected slot-e₂t coefficient is −L_{(f₂−t)u₂}(c_t·η^{W(t)}),
> whose ϖ-residue is −c_t·η^{W(t)}·η^{−Q((f₂−t)u₂)} =
> −c_t·η^{W(t)}·η^{−(f₂−t)Q−W(t)} = −c_t·η^{−(f₂−t)Q} = r̃'s
> t-coefficient, by the preamble's two displays … ∎”

**FORM:** italic-headed three-clause proof.

**DERIVATION:** (a) minimal-polynomial identification plus the full-side attained-pin argument for `ψ₂(0) ≠ 0`; (b) a two-factor split, explicitly flagged POINTWISE and therefore wrap-free; (c) a residue cancellation `η^{W(t)}·η^{−W(t)} = 1` using `.12`'s telescoping identity.

**CONDITIONALITY:** the proof also records a CONSISTENCY check reclassified by r1: “CONSISTENCY (now a check, not a definition): at a root ξ of the corrected Φ₂, dividing 0 = Φ₂(ξ) by ϖ(ξ)^{f₂u₂} and taking residues gives r̃(β_ξ) = 0”. That reclassification IS the F-1 repair, recorded inside the proof.

**RESOLUTION TRACE:** proof lines 171–196.

**TEETH:** ARITHMETIC AUDIT of (c)'s cancellation, recomputed: `Q((f₂−t)u₂) = (f₂−t)Q(u₂) + W(t)` by `.12`, so `η^{W(t)}·η^{−Q((f₂−t)u₂)} = η^{W(t)−(f₂−t)Q−W(t)} = η^{−(f₂−t)Q}` ✓ — exactly r̃'s t-coefficient factor from (a). The two displays compose exactly as claimed.

---

### EFF.HETOW.17  [lemma]

**CANONICAL STATEMENT:**

> “> **LEMMA HETOW-2 (the composed key is a key-family member up to an
> > above-the-line perturbation) [r1 2026-08-09 (passPE1 F-2/F-4)
> > restated at the wrap-corrected key, the lift object pinned, the
> > carry accounting completed].** Let Φ₂ be the wrap-corrected key and
> > Ψ := the Ψ_{κ₂,r̃} obtained from Φ₂'s own exact-height slot parts
> > (B_t := the height-(f₂−t)u₂ part of Φ₂'s LITERAL reduced slot-e₂t
> > coefficient). Then Ψ is a genuine DEFINITION HE6-1 member at the
> > datum (κ₂, r̃) — B_t of degree < D′, exact height, ϖ-residue = r̃'s
> > t-coefficient, B_t ≠ 0 ⟺ c_t ≠ 0 — and Φ₂ = Ψ − w with deg w < D″
> > and **either w = 0 (in particular under the (LIFT)-slot coefficient
> > form, at any f₁) or dv₂(w) > T₂**; hence by LEMMA HE7-12(a)–(d) the
> > entire §S5 package, THEOREM HE7.A(1)(2), the refine package (LEMMA
> > HE7-12/13, LEMMA HE7-8) and the §S1 CONVENTION with LEMMA HE6R1-3's
> > peel hold VERBATIM with key Φ₂.”

**FORM:** blockquoted bold-headed lemma.

**DERIVATION:** `.18` (the F-4 branch, w = 0) and `.19` (the F-2 branch, representation independence).

**CONDITIONALITY:** **the closing licence is re-scoped by C-A(ii) to the w = 0 branch** (`.43`), and this lemma's downstream pin name in T2 is `HETOW-KEY-BRIDGE`. **Note the conjunct structure carefully**, because T2's r12 turns on it: the displayed statement asserts BOTH `deg w < D″` AND the value disjunct `w = 0 or dv₂(w) > T₂`. T2's r12 records that only the VALUE disjunct “is the only conjunct read off a source statement here”, and derives the degree conjunct master-side from monicity — see `.43`.

**RESOLUTION TRACE:** statement lines 198–211; proofs 213–262; correction site 548–569 (C-A); downstream consumer trace at `.43`.

**TEETH:** the (LIFT)-form branch is what both machine legs instantiate (f₁ = 1 frames); the carry branch is **proof-only** with no machine contact at f₁ ≥ 2 — HETOW-BOX-3 says so explicitly (“f₁ ≥ 2 outer frames (HETOW-2's carry leg is proof-only …)”). PROOF-ONLY teeth row, §6.

---

### EFF.HETOW.18  [derivation]

**CANONICAL STATEMENT:**

> “*Proof.* **[F-4: the coefficient object, pinned.]** The [r1] display's
> slot-e₂t coefficient IS the (LIFT) output −L_{(f₂−t)u₂}(c_t·η^{W(t)}):
> x-degree ≤ i((f₂−t)u₂) + e₁(f₁−1) ≤ e₁f₁ − 1 = D′ − 1, every monomial
> at dv-height (f₂−t)u₂ exactly (§S2 preamble; the heights are available
> by HE6's [r1] NON-PROPAGATION box, (f₂−t)u₂ ≥ u₂ > e₂D′h > (D′−1)h).
> Under this form — the construction this note and the machine legs
> actually consume — NO x-degree-≥ D′ overflow occurs at ANY f₁: each
> B_t = −L_{(f₂−t)u₂}(c_t·η^{W(t)}) is already reduced, exact-height,
> with ϖ-residue = r̃'s t-coefficient by HETOW-1(c), nonzero iff
> c_t ≠ 0. Φ₂ is LITERALLY of DEFINITION HE6-1's displayed form and
> w = 0. (At f₁ = 1 the coefficient is the single monomial
> lift(c_t·η^{W(t)})·n̂((f₂−t)u₂) — the battery's and supp leg's form.
> The sealed proof's "f₁ ≥ 2 overflow" branch treated a representation
> the (LIFT) construction never produces — passPE1 F-4.)”

**FORM:** bold-headed proof branch.

**DERIVATION:** a degree count on the (LIFT) construction plus HETOW-1(c) for the residues.

**CONDITIONALITY:** **this branch gives `w = 0` outright, at ANY f₁** — which is why C-A(ii) can safely re-scope the HE7-12 licence to it. The sealed “f₁ ≥ 2 overflow” branch is DEAD (it described an object the construction never produces).

**RESOLUTION TRACE:** proof lines 213–226.

**TEETH:** ARITHMETIC AUDIT of the degree bound, recomputed: `i((f₂−t)u₂) ≤ e₁ − 1` and the η-digit index `j ≤ f₁ − 1` contributes `e₁j ≤ e₁(f₁−1)`, so the x-degree is `≤ (e₁−1) + e₁(f₁−1) = e₁f₁ − 1 = D′ − 1` ✓ — the displayed chain is exact, not an estimate.

---

### EFF.HETOW.19  [derivation]  *(CHAIN-CARRY, link 2)*

**CANONICAL STATEMENT:** the F-2 carry accounting, source lines 227–262, `[ASSEMBLED]` from its three parts (each quoted below). The setup and the two-piece split, verbatim:

> “**[F-2: the carry accounting, completed — representation
> independence.]** If a slot coefficient is instead presented with
> x-degree ≥ D′ (e.g. a plain product ĉ_t·n̂ of a degree-≤ D′−1 lift by
> the x-monomial, x-degree up to D′ + e₁ − 2), reduce mod Φ′. Each step
> x^{D′+r′} = x^{r′}·(Φ′ − tail), tail := Φ′ − x^{D′} (deg ≤ D′−1,
> dv = D′h EXACT — S3.1's constant-term pin v = f₁h attained), turns a
> monomial at Φ′-slot s, dv-height m (slot value val := e₂m + su₂) into
> TWO pieces:
> * the MOVED piece x^{r′}π^{·}·Φ′^{s+1}: slot s+1, height m − D′h,
>   value val + (u₂ − e₂D′h) — a raise by EXACTLY u₂ − e₂D′h ≥ 1
>   (integer-quantized; the [r1] node floor u₂ > e₂D′h). Its x-degree
>   r′ ≤ e₁ − 2 < D′: it never re-reduces.
> * the STATIONARY piece −x^{r′}π^{·}·tail: slot s, height
>   ≥ m with EQUALITY exactly at tail's attaining monomials (value
>   stays ≥ val, = val on the attaining part); its x-degree
>   ≤ r′ + D′ − 1 may re-reduce, but r′ drops by ≥ 1 per iteration, so
>   the reduction terminates.”

the sorting step (the piece the sealed proof missed), verbatim:

> “Sort the terminal (= literal reduced)
> development: the exact-height value-T₂ parts at slot e₂t land in
> B_t — NOT in w (this is the piece the sealed "every carry sits at
> value > T₂" sentence missed). Their residue is UNCHANGED: each
> reduction step is an identity in Ô[x], and at any locus point x₀ the
> moved summand x₀^{r′}π^{·}Φ′(x₀) sits at strictly larger value, so
> res(overflow monomial/ϖ^m) = res(stationary piece/ϖ^m) pointwise …”

and the bound, verbatim:

> “Everything else goes to −w: above-height stationary
> parts at value ≥ T₂ + e₂ (dv-heights are integers; one height step =
> e₂ in value) and moved parts at value ≥ T₂ + (u₂ − e₂D′h). Slotwise
> (LEMMA HE7-12(d)'s computation) dv₂(w) ≥ T₂ + min(e₂, u₂ − e₂D′h)
> > T₂. Either way LEMMA HE7-12 [r2, r3] applies (its W = 0 split
> covers w = 0). ∎”

**FORM:** bold-headed proof branch with a two-bullet display.

**DERIVATION:** a reduction-by-Φ′ analysis with a value-monotonicity invariant and a terminating x-degree measure.

**CONDITIONALITY — TWO CORRECTIONS from C-A, and they hit different sentences:**
1. **C-A(i) WITHDRAWS the exemplar** “(e.g. a plain product ĉ_t·n̂ of a degree-≤ D′−1 lift by the x-monomial …)”: at f₁ ≥ 2 such a product's exact-height part spans one η-digit and therefore does not carry residue c_t, so it violates the paragraph's own premise. The paragraph's scope is narrowed to “presentations of the CORRECTED key's (LIFT) coefficient augmented by above-height junk of x-degree ≥ D′”. KIND: **scope-pin**.
2. **C-A(ii) RE-SCOPES the closing sentence** “Either way LEMMA HE7-12 [r2, r3] applies” to the (LIFT)-slot form, i.e. to **w = 0**, because at the `(e₂ = 1, t = f₂−1)` corner a junk-augmented coefficient's moved piece lands at the LEADING slot and `deg w < D″` fails. KIND: **scope-pin**.
**What survives, in the note's own words:** “The accounting core stands: value monotone, raise exactly u₂ − e₂D′h, residue unchanged via the Ô[x] identity — machine-exact at frame R with r′ = e₁−2 maximal.”

**RESOLUTION TRACE:** proof lines 227–262; correction site 548–569.

**TEETH:** ARITHMETIC AUDIT of the value bookkeeping, recomputed: moving a monomial from slot s, height m to slot s+1, height m − D′h changes `val = e₂m + su₂` to `e₂(m − D′h) + (s+1)u₂ = val + u₂ − e₂D′h` ✓ — “EXACTLY”, as displayed, and positive by the node floor `u₂ > e₂D′h` ✓. The height-step-to-value conversion `one height step = e₂ in value` is immediate from `val = e₂m + su₂` ✓. PROOF-ONLY teeth row: no f₁ ≥ 2 machine contact exists (HETOW-BOX-3).

---

### EFF.HETOW.20  [lemma]

**CANONICAL STATEMENT:**

> “> **LEMMA HETOW-3 (full-side block identities).** At a full inner side
> > (e₂f₂μ₂ = μ₁): (a) dv(A_0) = κ₂μ₁ < ∞, so A_0 ≠ 0 and Φ′ ∤ f; (b) every
> > root of f on the opening locus is a level-2 point of (κ₂, r̃), so
> > S_{κ₂,r̃} = roots(f), f_S = f, and μ₂ = deg f/D″ = μ₁/(e₂f₂) ∈ ℤ;
> > (c) if Φ₂ | f, LEMMA HE6R1-3 (available at key Φ₂ by HETOW-2 +
> > HE7-12(c) item (11)) peels exactly one irreducible factor with
> > (e, f) = (e₁e₂, f₁f₂) and the read continues on f/Φ₂ at μ₂ − 1.”

**FORM:** blockquoted bold-headed lemma with three clauses.

**DERIVATION:** `.21`.

**CONDITIONALITY:** clause (b) consumes an all-roots transport that is NOT proved here; the 2026-08-10 F-2 annex attaches the cite (`.54`). SUPERSESSION KIND for that annex: **provenance-rider** (“annex-grade; the lemma statement is unchanged”).

**RESOLUTION TRACE:** statement lines 265–270; proof 272–280; the cite annex at 811–819.

**TEETH:** clause (b) is the row of `.09` marked HETOW-3(b) and is what makes `f_S = f`; clause (a) discharges the `Φ′ ∤ f` entry of the level-1 frame row (and only that entry, per the F-3 annex `.55`).

---

### EFF.HETOW.21  [derivation]

**CANONICAL STATEMENT:**

> “*Proof.* (a) The full side runs (0, κ₂μ₁)–(μ₁, 0); its left endpoint is
> an attained pin of the polygon, so dv(A_0) = κ₂μ₁ is finite. (b) A root
> x₀ has dv(Φ′(x₀)) = a slope of the polygon (COROLLARY HE6-2″); the only
> slope is κ₂; its β_{x₀} is a root of ι(R_{κ₂}-in-ϖ-normalization) =
> ι(r̃^{μ₂}) (HETOW-1(b) transports the n̂-normalized residual ψ₂^{μ₂}),
> whose only irreducible factor is r̃. So every root carries the label
> (κ₂, r̃); |roots| = deg f, f_S = f by LEMMA HE7-6's uniqueness, and
> deg f = D′μ₁ = D″μ₂. (c) is LEMMA HE6R1-3 verbatim at the key Φ₂
> (HE7-12(c) transports its proof). ∎”

**FORM:** italic-headed three-clause proof.

**DERIVATION:** as quoted; (b) routes through COROLLARY HE6-2″ and LEMMA HE7-6's uniqueness.

**CONDITIONALITY:** (b)'s “A root x₀ has dv(Φ′(x₀)) = a slope of the polygon” is the transport the F-2 annex later cites to GENTOW1 (`.54`).

**RESOLUTION TRACE:** proof lines 272–280.

**TEETH:** ARITHMETIC AUDIT: `deg f = D′μ₁` and `D″ = D′e₂f₂` give `deg f/D″ = μ₁/(e₂f₂) = μ₂` under the full-side identity `e₂f₂μ₂ = μ₁` ✓ — clause (b)'s integrality is exactly the full-side hypothesis, not an extra assumption.

---
### EFF.HETOW.22  [theorem]

**CANONICAL STATEMENT:**

> “> **THEOREM HETOW.A ([GENHN-HE(μ₂)] at tower stages = THEOREM HE7.A at
> > the composed carrier — literal instance).** In GENHN-T(b)′'s setting
> > (full inner side, any μ₂ ≥ 2, any (e₁, f₁, h), any e₂f₂ ≥ 2), with
> > **Φ₂ the [r1 2026-08-09] WRAP-CORRECTED composed key** (§S1/§S2 —
> > passPE1 F-1 refuted the key clause at the gauge-naive display on
> > η ≠ 1 wrap frames; every clause below reads at the corrected key):
> >
> > (i) (κ₂, r̃) is a level-2 datum of DEFINITION HE7-1 over the level-1
> > frame (HETOW-1), Φ₂ is its key up to a LEMMA HE7-12 perturbation
> > (HETOW-2), f_S = f with μ₂ = μ₁/(e₂f₂) (HETOW-3), and GENHN-T(b)′'s
> > composed pins/polygon/residuals ARE THEOREM HE7.A's P₂ data at that
> > datum ((SLOT₂) = GENHN-2′, §S1 table).”

**FORM:** blockquoted bold-headed theorem, clause (i).

**DERIVATION:** §S1's table with HETOW-1/2/3 discharging the three non-verbatim rows (`.26`).

**CONDITIONALITY:** **the final clause is SUPERSEDED by the 2026-08-10 append and now carries an exact content** (`.53`):

> “THEOREM
> HETOW.A(i)'s final clause ("GENHN-T(b)′'s composed
> pins/polygon/residuals ARE THEOREM HE7.A's P₂ data") now carries
> its exact content: pins and polygon are shared verbatim
> (valuation-only rows, untouched by the challenge), and the
> composed residuals are the δ-rescale of HE7.A's with every
> HE7.A(2)/(3) routing decision and every α-refine chain identical
> (HETOW-4(d)).”

SUPERSESSION KIND: **replacement of a justification** (the clause's truth is preserved; its GROUND changes from the J-D0 appeal to HETOW-4). The codex ratification's gap annotation on this clause is “DISCHARGED at this note's grade”. Also: the “up to a LEMMA HE7-12 perturbation” clause inherits C-A(ii)'s re-scoping (`.43`).

**RESOLUTION TRACE:** statement lines 286–297; correction sites 793–809 (HETOW-4 supersession), 548–569 (C-A).

**TEETH:** T2 pins this clause as `HETOW-A` (XREF X09) and consumes it at two units of `spec/EFF-T2-s1of6.md`.

---

### EFF.HETOW.23  [theorem]

**CANONICAL STATEMENT:**

> “> (ii) Consequently the σ-decision at inner multiplicity μ₂ is
> > THEOREM HE7.A(1)–(3) + THEOREM HE7.C/D: every side of P₂ has slope
> > λ₂ > T₂ with Σ L_{λ₂} = μ₂; each irreducible factor r₂ of a separable
> > level-2 residual contributes ONE irreducible factor of f with
> >
> >     e = e₁e₂·ℓ₂ ,   f = f₁f₂·deg r₂
> >
> > — the composed stage dictionary (e₁e₂·e_s, f₁f₂·f_s), i.e. exactly the
> > content of [GENHN-HE(μ₂)] at the tower stage; a repeated K₂-rational
> > linear factor at integer λ₂ is a finite α-refine chain (LEMMA
> > HE7-12/13, HE7-8); a repeated factor with ℓ₂·deg r₂ ≥ 2 passes to
> > level 3 (THEOREM HE7.D with ANNEX R's HE7-2′ normalizer tower) and
> > requires μ₂ ≥ 4.”

**FORM:** theorem clause with an inline display (the composed stage dictionary).

**DERIVATION:** HE7.A/C/D applied through (i) (`.26`).

**CONDITIONALITY:** **this dictionary is the note's deliverable** — it IS “the content of [GENHN-HE(μ₂)] at the tower stage”. Its transport across the two normalizer systems is what HETOW-4(d) later certifies: “HE7.A(2)'s dictionary (e, f) = (e₁e₂ℓ₂, f₁f₂·deg r₂) and HE7.A(3)'s branch predicate ℓ₂·deg r₂ ∈ {1, ≥2} read identically in the two systems”.

**RESOLUTION TRACE:** statement lines 299–311; the transport certificate at 734–746.

**TEETH:** machine-verified 300/300 against PARI at μ₂ = 3 on both inner branches (§S6 P2, `.35`), plus the P-C routing-transport leg of the 2026-08-10 run (`.52`).

---

### EFF.HETOW.24  [theorem]

**CANONICAL STATEMENT:**

> “> (iii) In particular at **μ₂ = 3** — the box family's first live tower
> > case — the level-3 branch is DEAD (a repeated r₂ with ℓ₂d_{r₂} ≥ 2
> > forces L_{λ₂} ≥ 4 > 3 ≥ Σ L_{λ₂}, HE7.A(3)'s own display), so the
> > whole decision runs inside HE7's frozen level-2 machinery: separable
> > residuals via HE7.A(2), repeated linear via finite α-refines. At
> > μ₂ = 2 the same instance reproduces GENHN-T(b)′(iii)'s trichotomy
> > (RAM: ℓ₂ = 2 side ⟹ (2e₁e₂, f₁f₂); INERT: quadratic r₂ ⟹
> > (e₁e₂, 2f₁f₂); SPLITEQ/SPLTAIL/2SIDED: two linear blocks) — a
> > consistency check, two proofs of one statement.”

**FORM:** theorem clause.

**DERIVATION:** a counting exclusion at μ₂ = 3 from HE7.A(3)'s own display.

**CONDITIONALITY:** the μ₂ = 2 half is a CONSISTENCY CHECK, not a new result — the note labels it “two proofs of one statement”. A consumer must not count it as independent supply.

**RESOLUTION TRACE:** statement lines 313–321.

**TEETH:** the level-3 exclusion is machine-checked as P5 (“no member ever took the LEVEL3 branch”, 300/300, `.35`); the μ₂ = 2 trichotomy is re-run at frame V (8/8) and frame S in the PE2 fresh leg (`.45`, `.47`). ARITHMETIC AUDIT: `ℓ₂d_{r₂} ≥ 2` with a repeated factor forces `L_{λ₂} ≥ 2·2 = 4 > 3` ✓.

---

### EFF.HETOW.25  [theorem]

**CANONICAL STATEMENT:**

> “> (iv) TERMINATION at the composed degree: the tower node is itself a
> > widened-box jump with descent factor ℓd_r = e₂f₂ ≥ 2 (LEMMA HE6R1-1 =
> > THEOREM HE7.C [r1]); μ₁ ≥ μ₂·e₂f₂ with equality at the full side, and
> > J ≤ log₂ μ₁ − 1 ≤ log₂ n − 2 counts the tower entry as one jump. At
> > n = 12 (μ₁ = 6): exactly one jump, μ₂ = 3, no second jump possible.”

**FORM:** theorem clause.

**DERIVATION:** HE7.C's two displays with `ℓd_r = e₂f₂`, the first tight at a full side by HETOW-3(b).

**CONDITIONALITY:** **the acceptance record certifies this clause WRAP-IMMUNE** (`.46`): “the wrap correction moves unit factors only — heights, degrees, and multiplicities, hence HE6R1-1's descent factor ℓd_r = e₂f₂ and both displayed bounds, are untouched by it”. That is a positive scope finding, not a supersession: the r1 correction, which invalidated the key clause, provably does not reach the termination clause.

**RESOLUTION TRACE:** statement lines 323–327; the wrap-immunity certificate at 622–627.

**TEETH:** ARITHMETIC AUDIT at n = 12, recomputed: `n = D′μ₁ = 2·6 = 12` ✓; `J ≤ log₂ 6 − 1 = 1.58… − 1`, so `J ≤ 1` with the floor, i.e. exactly one jump ✓; `μ₂ = μ₁/(e₂f₂) = 6/2 = 3` ✓; a second jump would need `μ₂ ≥ μ₃·e₃f₃ ≥ 2·2 = 4 > 3` ✓.

---

### EFF.HETOW.26  [derivation]

**CANONICAL STATEMENT:**

> “*Proof.* (i) is §S1's table with HETOW-1/2/3 discharging the three
> non-verbatim rows. (ii)–(iv): THEOREM HE7.A/C/D apply because every
> hypothesis holds by (i); the dictionary display is HE7.A(2)'s with
> (ℓ, d_r) = (e₂, f₂); the μ₂ = 3 exclusion is HE7.A(3)'s non-propagation
> display at μ₂ = 3; (iv) is THEOREM HE7.C's two displays with
> ℓd_r = e₂f₂, the first tight at a full side by HETOW-3(b). ∎”

**FORM:** italic-headed proof.

**DERIVATION:** pure instantiation — the proof does no work beyond checking that (i) discharges every hypothesis. **This is the whole content of “literal instance”**, and it is why the note's supply is a translation rather than a theorem of σ.

**CONDITIONALITY:** the proof's force depends entirely on `.07`'s meta-claim that HE7 §S1–S6 has no hypothesis on (ℓ, d_r) — see OPEN-CALL 4.

**RESOLUTION TRACE:** proof lines 329–334.

**TEETH:** the machine form is P2: the frozen readers decide every member unmodified (`.35`).

---

### EFF.HETOW.27  [derivation]

**CANONICAL STATEMENT:**

> “**MINIMAL LIVE DEGREE (derived).** An inner-μ₂ ≥ 3 tower stage needs
> μ₁ = e₂f₂μ₂ ≥ 2·3 = 6 and n = D′μ₁ ≥ 2·6 = 12 (D′ ≥ 2 at a composite
> outer stage, e₂f₂ ≥ 2 at a composite inner stage). **n_min = 12**,
> attained exactly by (D′, e₂f₂, μ₂) = (2, 2, 3), i.e.
> (e₁,f₁) ∈ {(2,1),(1,2)} × (e₂,f₂) ∈ {(2,1),(1,2)}, μ₁ = 6. No tower
> [GENHN-HE(≥3)] instance exists at n ≤ 11.”

with the derived σ menus:

>     “case A (e₂,f₂) = (2,1), composed (e₁e₂,f₁f₂) = (4,1), K₂ = F_Q:
>       {(12,1)} · {(4,3)} · {(4,1)}³ · {(4,2),(4,1)} · {(8,1),(4,1)}
>     case B (e₂,f₂) = (1,2), composed (2,2), K₂ = F_{Q²}:
>       {(6,2)} · {(2,6)} · {(2,2)}³ · {(2,4),(2,2)} · {(4,2),(2,2)}”

**FORM:** bold-headed derived fact + an indented ASCII display of two five-element menus.

**DERIVATION:** an integer minimization over the full-side identity, plus the two composite-stage floors. The menus are derived from clauses (ii)+(iii) — the note says so (“the σ menus at μ₂ = 3 (from (ii)+(iii))”).

**CONDITIONALITY:** the menus are the sealed battery's PREREGISTERED prediction set (P3: “every σ inside the preregistered 5-element menus”), so this unit is simultaneously a derived fact and a preregistration.

**RESOLUTION TRACE:** statement lines 336–348.

**TEETH:** ARITHMETIC AUDIT, recomputed: `μ₁ = e₂f₂μ₂ ≥ 2·3 = 6` ✓, `n = D′μ₁ ≥ 2·6 = 12` ✓, attained at `(2,2,3)` ✓. Menu degree sums, recomputed against `n = 12`: case A `{(12,1)}` → 12 ✓; `{(4,3)}` → 12 ✓; `{(4,1)}³` → 12 ✓; `{(4,2),(4,1)}` → 8+4 = 12 ✓; `{(8,1),(4,1)}` → 8+4 = 12 ✓. Case B `{(6,2)}` → 12 ✓; `{(2,6)}` → 12 ✓; `{(2,2)}³` → 12 ✓; `{(2,4),(2,2)}` → 8+4 = 12 ✓; `{(4,2),(2,2)}` → 8+4 = 12 ✓. **All ten menu entries have ef-sum exactly 12** — the menus are degree-consistent, checked independently of the note. P4 confirms all five realized in each case.

---

### EFF.HETOW.28  [fence]

**CANONICAL STATEMENT:**

> “> **HETOW-BOX-1 (scope = T(b)′'s scope).** Full inner sides only; PARTIAL
> > inner sides (e₂f₂μ₂ < μ₁) are [GENHN-TOW-1](4) — there LEMMA HE6R1-2
> > supplies the level-2 starting data read off f, but the composed
> > entry/count layer is GENHN's open item, not touched here.”

**FORM:** blockquoted bold-headed box.

**DERIVATION:** `[RECORD]` of an inherited scope limit.

**CONDITIONALITY:** the partial-side case is GENHN's open item. **It is separately addressed by GENTOW-4** (`GENTOW4_PROOF_2026-08-09.md`), whose clause (c) T2's r12 quotes alongside `HETOW-KEY-BRIDGE` — “`GENTOW-4-1` clause (c) gives that same disjunct at the partial tower”. So the partial-side gap this box declares open is, at HEAD, addressed by a sibling note this note does not cite. Recorded as a DAG edge the note does not carry.

**RESOLUTION TRACE:** statement lines 354–358.

**TEETH:** XREF X10 verifies `GENTOW4_PROOF_2026-08-09.md` exists and carries a `GENTOW-4-1` clause-(c) statement of the same disjunct (verified via T2's quotation of it).

---

### EFF.HETOW.29  [fence]

**CANONICAL STATEMENT:**

> “> **HETOW-BOX-2 (depth ≥ 3).** A tower inside a tower (first live n = 16)
> > rides THEOREM HE7.D + ANNEX R HE7-2′ on the HE7 side and
> > [GENHN-TOW-1](6) (T(b)″'s (α) carry cancellation, (β) iterated node
> > floor) on the GENHN side; this note is ONE tower step over the level-1
> > frame and does not self-apply.”

**FORM:** blockquoted bold-headed box.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** OPEN at HEAD; nothing in the four dated appends touches it. “does not self-apply” is the sharpest form of the fence: the note's own theorem is not iterable by itself.

**RESOLUTION TRACE:** statement lines 359–362.

**TEETH:** none; a declared open box. ARITHMETIC AUDIT of “first live n = 16”: a tower inside a tower needs a second composite inner stage, so `n ≥ D′·e₂f₂·e₃f₃·μ₃ ≥ 2·2·2·2 = 16` ✓.

---

### EFF.HETOW.30  [fence]  *(SERIES BOX3 folded — four dated states)*

**CANONICAL STATEMENT:** the box at its post-`[r1 F-3]` reading, verbatim:

> “> **HETOW-BOX-3 (machine coverage) [r1 2026-08-09 (passPE1 F-3): the
> > η-gauge axis added — the sealed list omitted the axis on which the
> > pass's CRITICAL bit].** The battery exercises μ₂ = 3,
> > (e₁,f₁,h) = (2,1,1), (e₂,f₂) ∈ {(2,1),(1,2)}, u₂ ∈ {5, 3}, p ∈ {3,5},
> > char 0 only (PARI oracle asymmetry, inherited HE6-BOX-4).
> > **η = 1 GAUGE:** both battery frames are Φ′ = x² − p with
> > η = res(θ²/π) = 1, where the wrap factor η^{−W(t)} acts trivially —
> > the sealed battery cannot see the F-1 seam (the runner disclosed the
> > gauge; this box did not, until [r1]). η ≠ 1 coverage now on record:
> > `hetow_pe1_fresh.py` (frame X, dual oracle routes) +
> > `hetowr1_supp.py` (frames X/Z/W, incl. an e₁ = 3 frame, gauge-naive
> > tooth fired per frame — §S7); corrected-key contact only, three
> > frames, f₂ = 2 with f₁ = 1. NOT exercised: μ₂ ≥ 4 (level-3-capable
> > towers), e₂f₂ ≥ 4 (both ℓ ≥ 2 AND d_r ≥ 2 — first live n = 24),
> > f₁ ≥ 2 outer frames (HETOW-2's carry leg is proof-only, cf.
> > GENHN-ERR-1's separate f₁ ≥ 2 residue), η ≠ 1 combined with f₁ ≥ 2
> > or with e₂ ≥ 2, organic (non-planted) refine chains. The §S2–S3
> > proofs are displayed at these hypotheses; the unexercised axes have
> > no machine contact, and the coverage sentence stops there ([r1]
> > withdraws the sealed "uniform in all of these" line — that shape of
> > sentence is what F-1 falsified on the η-axis).”

**FORM:** blockquoted bold-headed box with a NOT-exercised list.

**DERIVATION:** `[RECORD]` of an evidence perimeter.

**CONDITIONALITY — the box has FOUR dated states and a consumer must read the last:**
1. **sealed** — no η axis; carried the line “uniform in all of these”.
2. **[r1 F-3]** — η-gauge axis added; the uniformity line WITHDRAWN. KIND: **inventory completion** + **replacement**.
3. **C-C** (`.45`) — the **f₂ ≥ 3 multi-wrap axis** appended to the NOT-exercised list, then immediately “mooted in substance” and converted to a disclosed row by frame V's first contact. KIND: **inventory completion**.
4. **F-α** (`.47`) — the `e₂f₂ ≥ 4` row FOLDED against frame S: its parenthetical pins the row to the μ₂ ≥ 3 box family, under which it stays literally accurate; a μ₂ ≤ 2 citation is appended. KIND: **scope-pin**.
**Effective NOT-exercised list at HEAD:** μ₂ ≥ 4; e₂f₂ ≥ 4 **at μ₂ ≥ 3** (first live n = 24; μ₂ = 2 now has frame S); f₁ ≥ 2 outer frames (the carry leg stays proof-only); η ≠ 1 combined with f₁ ≥ 2 or with e₂ ≥ 2; organic refine chains. **The f₂ ≥ 3 multi-wrap axis is NO LONGER on the list** (frame V).

**RESOLUTION TRACE:** statement lines 363–383; correction sites 592–604 (C-C), 634–652 (F-α).

**TEETH:** all four cited artifacts verified present: `hetow_pe1_fresh.py`, `hetowr1_supp.py`, `hetow_pe2_fresh.py` (frames V and S), `hetow_r2_hetow4.py`. Disposition `signed coverage disclosure`; the box is the note's honest perimeter and the one object every pass attacked.

---

### EFF.HETOW.31  [fence]

**CANONICAL STATEMENT:**

> “> **HETOW-BOX-4 (grade).** Attempt 0/2; consumption by GENHN (rewording
> > [GENHN-HE(μ₂)]'s tower instances as discharged-at-grade) is a LATER
> > fold, since GENHN_PROOF and HE7_PROOF are frozen to this unit.”

**FORM:** blockquoted bold-headed box.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** the grade half is superseded to **2/2** (`.46`). **The fold half is NOT superseded and is verified still owed**: `grep -cF 'discharged-at-grade' GENHN_PROOF_2026-08-08.md` = **0** (N2). The box remains live as a protocol obligation even though its grade clause is spent. KIND: **counter re-reading** on the first half only.

**RESOLUTION TRACE:** statement lines 384–386.

**TEETH:** N2 (negative edge, verified).

---

### EFF.HETOW.32  [preregistration]

**CANONICAL STATEMENT:**

> “*Design, preregistered predictions and teeth: see the runner's docstring
> (sealed before the full run; smoke record disclosed there).* Summary:
> degree-12 members f = Φ₂³ + A₂Φ₂² + A₁Φ₂ + A₀ built by (LIFT₂) at
> preregistered pin menus over both cases; the readers are the FROZEN
> `he7_checks.level2_read` (case A) and `he6r1_checks.level2_read`
> (case B), imported UNMODIFIED with md5 pins printed — the machine form
> of "literal instance": zero new read logic at μ₂ = 3. Oracle: PARI
> factorpadic via the sealed `gp_sig_batch` bridge. Parse gate: level-1
> x-polygon + Φ′-development side/residual = the tower entry. Predictions
> P1–P5 + teeth T-NAIVE / T-WITHHOLD / T-BADTWIST / T-THREESIGMA.”

**FORM:** italic pointer + summary paragraph under `## S5. THE MACHINE LEG …— sealed at commit 1`.

**DERIVATION:** `[PREREGISTERED]` — sealed at commit 1, scored at commit 2.

**CONDITIONALITY:** **the design's central feature is the frozen-reader import**: the instrument is constructed so that a green run IS evidence for “literal instance”, because zero read logic is new. That is an unusually tight instrument/claim match and is worth carrying downstream.

**RESOLUTION TRACE:** statement lines 392–401.

**TEETH:** the import pins are printed in the artifact and were re-read at compile time: `he6_checks.py 321fa4d4990eef67ff6a20f375c32366`, `he7_checks.py 688adbe88447b570104e379b1fa11cd5`, `he6r1_checks.py 7112f7c738ed13fb352f96849da1d309`, `w12_checks.py 7dc040d94fbbb1e8d20ac817b665d418`, `w10_checks.py a9c34244a3af19f5fa864375b494380b` — **all five prefixes match the note's §S6 list exactly** (`.33`).

---

### EFF.HETOW.33  [run-record]

**CANONICAL STATEMENT:**

> “**Artifacts.** `hetow_checks_output.txt`, `hetow_checks_results.json`
> (sealed runner `hetow_checks.py` @ commit 1 = 2e5c4b1; no post-seal edit).
> Import pins printed in the artifacts: he6_checks 321fa4d4…, he7_checks
> 688adbe8…, he6r1_checks 7112f7c7…, w12_checks 7dc040d9…, w10_checks
> a9c34244…. Runtime 42.9 s.”

**FORM:** bold-headed artifact record.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** none.

**TEETH:** **RE-VERIFIED AT COMPILE TIME**: all five import pins match the artifact's own printed lines byte-for-byte (see `.32`); the artifact's final line reads `TOTAL checks 1200 violations 0 teeth 4/4  (42.9s)` — the 42.9 s runtime matches. `git cat-file -t 2e5c4b1` = commit; all three files exist.

---

### EFF.HETOW.34  [run-record]

**CANONICAL STATEMENT:**

> “**Totals.** 6 rows (4 × case A, 2 × case B), **300 members, 0 dropped,
> 300 reader-decided (status OK on every member), 300 PARI jobs** — the
> first machine contact anywhere with inner-μ₂ ≥ 3 tower stages.”

with the headline, verbatim from the §S6 heading:

> “**GREEN — 1,200 checks, 0 violations, 4/4 teeth, 300/300 PARI agreements**”

**FORM:** bold-headed totals paragraph; the headline is the section heading.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** “the first machine contact anywhere with inner-μ₂ ≥ 3 tower stages” is a corpus-novelty claim, not re-verified here (a corpus sweep is out of scope for a single-note compilation).

**RESOLUTION TRACE:** statement lines 407, 415–417.

**TEETH:** **MANDATORY ARITHMETIC AUDIT (v3 rule 22), recomputed from the committed artifact's per-row lines:** 33 + 33 + 65 + 65 + 52 + 52 = **300 members** ✓ across exactly **6 rows** (4 case-A rows at p ∈ {3,5} × letter ∈ {1,2}, 2 case-B rows) ✓. The artifact's per-row lines read `members 33 dropped 0 ok 33 nonok 0 pari 33` etc., so **0 dropped and 300 PARI jobs** ✓. `TOTAL checks 1200 violations 0 teeth 4/4` ✓ — and 1,200 = 300 members × 4 checks/member, consistent with P1/P2/P3/P5 being per-member predicates (P4 is per-case, teeth are per-row). **Compiler note:** the note nowhere states the checks-per-member factor, so a reader cannot reconstruct 1,200 from 300 without it; recorded as OPEN-CALL 6.

---

### EFF.HETOW.35  [run-record]  `[TABLE]`

**CANONICAL STATEMENT:** the five predictions, source lines 419–447. P1, P3, P5 verbatim:

> “* **P1 ✓ 300/300** — every member parses as a genuine tower: level-1
>   Φ′-development = ONE full side of slope κ₂ with residual r^3
>   (r = Z−s / the irreducible quadratic), i.e. the widened-box node with
>   multiplicity 3.”

> “* **P3 ✓ 300/300** — every σ inside the preregistered 5-element menus.”

> “* **P5 ✓ 300/300** — no member ever took the LEVEL3 branch: THEOREM
>   HE7.C's μ₂ ≥ 4 floor for a level-3 jump held on every read (refine
>   chains occurred and terminated; all adjudicated by PARI).”

P2, the headline, verbatim:

> “* **P2 ✓ (HEADLINE) 300/300, zero mis-decisions** — the FROZEN readers
>   (he7_checks / he6r1_checks `level2_read`, byte-unmodified) decided
>   every member and matched PARI factorpadic exactly. This is the machine
>   form of THEOREM HETOW.A: the code written for the ordinary-leaf box
>   decides the tower box with no change.”

P4 and its per-row census — the census is a fixed-width ASCII display inside the source, so per v3 rule 14 it is emitted TWICE. **Source display, verbatim:**

>     “caseA p=3 s=1   33: {(12,1)} 7 · {(4,3)} 8 · {(4,2),(4,1)} 6 · {(8,1),(4,1)} 12
>     caseA p=3 s=2   33: same distribution
>     caseA p=5 s=1   65: {(12,1)} 10 · {(4,3)} 14 · {(4,1)³} 1 · {(4,2),(4,1)} 17 · {(8,1),(4,1)} 23
>     caseA p=5 s=2   65: 10 · 14 · 1 · 18 · 22
>     caseB p=3 r=Z²+1  52: {(6,2)} 10 · {(2,6)} 17 · {(2,2)³} 7 · {(2,4),(2,2)} 8 · {(4,2),(2,2)} 10
>     caseB p=5 r=Z²+2  52: 6 · 12 · 10 · 11 · 13”

`[TABLE]` — transcription with the compiler's row-sum audit in the last column:

| row | members | σ counts | row sum |
|---|---:|---|---:|
| caseA p=3 s=1 | 33 | {(12,1)} 7 · {(4,3)} 8 · {(4,2),(4,1)} 6 · {(8,1),(4,1)} 12 | 7+8+6+12 = **33** ✓ |
| caseA p=3 s=2 | 33 | same distribution | **33** ✓ |
| caseA p=5 s=1 | 65 | 10 · 14 · 1 · 17 · 23 | 10+14+1+17+23 = **65** ✓ |
| caseA p=5 s=2 | 65 | 10 · 14 · 1 · 18 · 22 | 10+14+1+18+22 = **65** ✓ |
| caseB p=3 (r = Z²+1) | 52 | 10 · 17 · 7 · 8 · 10 | 10+17+7+8+10 = **52** ✓ |
| caseB p=5 (r = Z²+2) | 52 | 6 · 12 · 10 · 11 · 13 | 6+12+10+11+13 = **52** ✓ |
| **total** | **300** | | 33+33+65+65+52+52 = **300** ✓ |

**FORM:** bulleted display + an indented ASCII census block.

**DERIVATION:** `[RUN]`

**CONDITIONALITY:** **P4's case-A p = 3 rows realize only FOUR of the five menu σ, and the note discloses why rather than scoring a violation:**

> “(case A:
>   {(4,1)}³ only at p = 5, structurally: F₃^× has just 2 elements, so a
>   cubic residual with nonzero constant term cannot have 3 distinct roots
>   at p = 3 — disclosed, not a violation)”

Disposition `disclosed structural non-realization`. **This is correct and the compiler verifies the reason independently**: a split-into-three-distinct-linear residual needs three distinct nonzero roots in `K₂^× = F_3^×`, which has order 2 — impossible ✓.

**RESOLUTION TRACE:** statement lines 419–447; the artifact's per-row distinct-σ counts (`distinct-pari 4` at both p = 3 case-A rows, `distinct-pari 5` at p = 5) independently confirm the 4-vs-5 split ✓.

**TEETH:** the row sums and the grand total are compiler-recomputed above; the artifact's own `distinct-pari` column corroborates the menu-realization claim row by row.

---

### EFF.HETOW.36  [run-record / disclosure]

**CANONICAL STATEMENT:**

> “**[r1 2026-08-09 (passPE1
>   F-5)] Gauge caveat:** both battery frames sit at η = 1 (Φ′ = x² − p),
>   where the wrap layer η^{−W(t)} is invisible — the 300/300 does not
>   exercise passPE1 F-1's η-axis; corrected-key η ≠ 1 contact is §S7.”

**FORM:** bold-headed dated caveat inside the P2 bullet.

**DERIVATION:** `[RECORD]` of an evidence limit.

**CONDITIONALITY:** **this caveat is what keeps P2's 300/300 from being over-read.** SUPERSESSION KIND: **inventory completion** (it adds a missing disclosure to a scored result without changing the score).

**RESOLUTION TRACE:** statement lines 427–430.

**TEETH:** disposition `signed vacuity disclosure` on the η-axis specifically: the battery is not vacuous, but it is provably blind to the axis on which the CRITICAL fell. The η ≠ 1 evidence is the supp leg (`.40`).

---

### EFF.HETOW.37  [run-record]

**CANONICAL STATEMENT:** the four teeth, verbatim:

> “**Teeth 4/4 FIRED.**
> * **T-NAIVE ✓** the "treat ψ₂³ as separable" dictionary is refuted by
>   PARI on ≥ 33 members of every case-A row and ≥ 42 of every case-B row.
> * **T-WITHHOLD ✓** both readers return UNDETERMINED when a level-2
>   residual is withheld.
> * **T-BADTWIST ✓** at s = 2 the level-2 cocycle twist is load-bearing at
>   μ₂ = 3: 55 members flip σ when the twist is dropped; on the
>   adjudicated flip the twisted read {(4,2),(4,1)} = PARI while the
>   untwisted read says {(4,3)} — the first μ₂ = 3 exercise of the
>   β-cocycle anywhere.
> * **T-THREESIGMA ✓** up to FIVE distinct PARI σ inside one family of
>   identical level-1 outer+entry data (fixed p, case, letter) — the tower
>   μ₂ = 3 σ-decision is genuinely deeper than the outer data, and the
>   composed level-2 read decides it.”

**FORM:** bold-headed bulleted teeth list.

**DERIVATION:** `[RUN]` — four mutation/withholding tests, each with a preregistered firing condition.

**CONDITIONALITY:** **T-BADTWIST is the load-bearing tooth for the note's central claim** (that the level-2 cocycle twist is not decorative at μ₂ = 3), and **T-NAIVE is the anti-vacuity tooth** (a wrong dictionary is refuted, so the right one is not trivially satisfiable). Note what NO tooth here covers: the η-gauge axis (`.36`) — that tooth exists only in the supp leg (`.40` G2), and C-B later shows even that σ-shaped tooth is insufficient in general (`.44`).

**RESOLUTION TRACE:** statement lines 449–462.

**TEETH:** **RE-VERIFIED AT COMPILE TIME against the committed artifact**, whose teeth block reads: `TOOTH T-NAIVE      FIRED  min per-row naive refutations: caseA 33, caseB 42`; `TOOTH T-WITHHOLD   FIRED  caseA UNDETERMINED / caseB UNDETERMINED`; `TOOTH T-BADTWIST   FIRED  twisted ((4, 1), (4, 2)) == PARI, untwisted ((4, 3),) (of 55 flips)`; `TOOTH T-THREESIGMA FIRED  max distinct PARI sigma within one fixed-letter family: 5`. **All four figures (33, 42, 55, 5) and all four fired states match the note exactly.**

---

### EFF.HETOW.38  [scope record]

**CANONICAL STATEMENT:**

> “**What the leg establishes** (instrument grade, not acceptance): the
> first-ever machine contact with [GENHN-HE(μ₂ ≥ 3)]'s tower instances is
> GREEN against an independent oracle at the minimal live degree n = 12,
> on both inner branches ((e₂,f₂) = (2,1) and (1,2)), with the σ-decision
> executed by HE7's frozen instruments unmodified — exactly what THEOREM
> HETOW.A's "literal instance" predicts and preregisters.”

**FORM:** bold-headed closing paragraph.

**DERIVATION:** `[RECORD]` of what a green run does and does not buy.

**CONDITIONALITY:** “instrument grade, not acceptance” — the note is explicit that a green battery is not a pass. Acceptance came later and from hostile passes (`.46`), not from this leg.

**RESOLUTION TRACE:** statement lines 464–469.

**TEETH:** the honest-limit sentence IS the tooth; disposition `signed evidence-grade disclosure`.

---

### EFF.HETOW.39  [changes-record]

**CANONICAL STATEMENT:** the r1 repair record, source lines 475–501, `[ASSEMBLED]` from its pass summary and five findings. The pass summary, verbatim:

> “**The pass:** `HETOW_passPE1_report.md` — 1 CRITICAL + 2 GAP + 2 MINOR;
> locus/termination/peel/n_min/menu rows and the seal all HELD; the
> sealed battery re-ran isolated content-identical (1,200/0, 4/4 teeth).”

F-1, the CRITICAL, verbatim:

> “**F-1 (CRITICAL, repaired at §S2 [r1]):** the sealed HETOW-1 gave r̃
> two definitions (slot residues of the displayed key; minpoly(β)) and
> called them equivalent; they differ by η^{−W(t)}, W(t) =
> ⌊(f₂−t)·i(u₂)/e₁⌋, the wrap-cocycle defect of the normalizer
> monomials. Repair: ONE definition (r̃ := minpoly(β)); the key
> WRAP-CORRECTED (slot-e₂t coefficient L_{(f₂−t)u₂}(c_t·η^{W(t)}));
> HETOW-1(c) re-proved AT it; HETOW.A(i) reads at the corrected key.
> The seam's owner display (GENHN-T(b)′'s plain lifts) is recorded at
> GENHN_PROOF's dated erratum (2026-08-09; T(b)′'s proof mechanism —
> polygon, forcing chain, S4 coherent normalizers — is untouched by it).”

F-2 through F-5, verbatim in brief: F-2 “the sealed carry estimate priced only the moved piece … the stationary tail piece sits AT value T₂ and lands in B_t”; F-3 “HETOW-BOX-3 [r1] now names the η = 1 gauge of the battery and the η ≠ 1 coverage on record”; F-4 “the coefficient object pinned — the (LIFT)-slot form, under which no x-overflow occurs at any f₁ (w = 0); the carry algebra retained for representation independence”; F-5 “§S6 P2 gauge caveat added”.

**FORM:** bold-headed record with five numbered findings.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** **the “what HELD” list is a positive scope finding worth carrying**: locus, termination, peel, n_min and the menu rows survived the CRITICAL untouched, and the seal held. This is the r1 analogue of the acceptance record's wrap-immunity certificate (`.46`) and bounds the blast radius of F-1.

**RESOLUTION TRACE:** statement lines 475–501.

**TEETH:** `HETOW_passPE1_report.md` exists; `git cat-file -t 5f821dc` = commit. The “re-ran isolated content-identical (1,200/0, 4/4 teeth)” claim is corroborated by the committed artifact's own totals (`.34`).

---

### EFF.HETOW.40  [run-record]

**CANONICAL STATEMENT:** the supp leg, source lines 503–531. The seal and verdict, verbatim:

> “**THE SUPP LEG — `hetowr1_supp.py` (sealed with preregistered
> predictions at r1 commit 1; artifacts `hetowr1_supp_output.txt` /
> `hetowr1_supp_results.json`, BYTE-FROZEN; runner md5 dcb8452f…,
> output b52eb226…, results 58f1ce0c…).** Re-derives from scratch
> (zero reader imports); dual PARI oracle routes agree on 29/29 jobs.
> **VERDICT: GREEN — 29 gp jobs + 15 exact-residue checks, 0
> violations.**”

The frames and the four legs, verbatim:

> “* **Frames** (η ≠ 1, f₁ = 1, f₂ = 2, W = (1,0)): X (PE1 regression:
>   p = 3, Φ′ = x² − 6, η = 2, u₂ = 3, n = 12) · Z (NEW: p = 5,
>   Φ′ = x² − 10, η = 2 of ORDER 4, u₂ = 3, n = 12) · W (NEW, e₁ = 3:
>   p = 5, Φ′ = x³ − 10, η = 2, u₂ = 5, n = 18 — the first e₁ = 3 wrap
>   contact anywhere).
> * **E-legs (exact):** W(0) two-ways = 1 at each frame; corrected-key
>   slot residues = minpoly(β) at each frame (X: Z²+2Z+2; Z/W: Z²+3Z+4,
>   each ≠ ψ₂ — the twist layer real); naive slot polynomial diverges
>   and is degenerate at each frame (X: (Z+1)²; Z/W: (Z+1)(Z+2)).
> * **G1 (corrected key = composed carrier):** PARI σ = {(2,2)} at X and
>   Z, {(3,2)} at W — 3/3.
> * **G2 (the η ≠ 1 TOOTH — the gauge-naive mutant fails):** naive-key
>   σ = {(4,1)} at X (≠ {(2,2)}; = PE1's measured seam), {(2,1),(2,1)}
>   at Z and {(3,1),(3,1)} at W — the DERIVED failure shapes, scored
>   exactly. 3/3 teeth fired.
> * **G3 (frame Z, μ₂ = 3, n = 12):** forced 3RAM {(6,2)} 4/4; forced
>   2+1 {(2,2),(4,2)} 4/4; 8 ONE21 (λ₂ = 7) members inside the case-B
>   menu ({(2,2)}³ ×3, {(2,2),(2,4)} ×3, {(2,6)} ×2).
> * **G4 (frame W, μ₂ = 3, n = 18 — first σ menu at composed (3,2)):**
>   forced 3RAM {(9,2)} 2/2; forced 2+1 {(3,2),(6,2)} 2/2; 3
>   integer-slope (λ₂ = 11) members inside the (3,2)-menu ({(3,2)}³ ×2,
>   {(3,2),(6,2)} ×1).”

**FORM:** bold-headed record with a frames bullet and four leg bullets.

**DERIVATION:** `[RUN]`, decorrelated by construction: “Re-derives from scratch (zero reader imports)” — the supp leg shares no code with the sealed battery, so its agreement is independent evidence, not a re-run.

**CONDITIONALITY:** three frames only, all at f₂ = 2 with f₁ = 1 (BOX-3, `.30`). **G2 is the η ≠ 1 tooth; C-B later shows a σ-shaped tooth of this exact shape is insufficient in general** (`.44`) — so this tooth's force is frame-specific, not generic.

**RESOLUTION TRACE:** statement lines 503–531.

**TEETH:** **ALL THREE MD5 PINS RE-COMPUTED AND MATCHED** (see FREEZE-2 in §1). **The verdict is re-read from the committed artifact**: `TOTAL jobs 29 violations 0 (21.3s)` / `VERDICT: GREEN` ✓ — 29 jobs and 0 violations exactly as stated. The artifact's G4 lines read `G4-3RAM:((9, 2),)  2`, `G4-int-slope:((3, 2), (3, 2), (3, 2))  2`, `G4-int-slope:((3, 2), (6, 2))  1` — **matching the note's “{(9,2)} 2/2” and “{(3,2)}³ ×2, {(3,2),(6,2)} ×1” exactly** ✓. ARITHMETIC AUDIT of the frame-W menu: 2 + 1 = 3 integer-slope members ✓, and the σ degree sums at n = 18 are 9·2 = 18 ✓ and 3·2 + 6·2 = 18 ✓.

---

### EFF.HETOW.41  [acceptance-box]

**CANONICAL STATEMENT:**

> “**GRADE: attempt stays 0/2** (the [r1] repair round does not score);
> passPE2 next. The PE1 sealed artifacts and the S5/S6 battery record
> are byte-untouched by this round.”

**FORM:** bold-headed grade line closing §S7.

**DERIVATION:** `[RECORD]`

**CONDITIONALITY:** superseded twice (CHAIN-GRADE): → 1/2 at `.42`, → 2/2 at `.46`.

**RESOLUTION TRACE:** statement lines 533–535.

**TEETH:** the byte-untouched claim is corroborated by FREEZE-1 (the sealed runner pin resolves and no post-seal edit is recorded).

---
### EFF.HETOW.42  [acceptance-box]  *(SERIES ARC, link 2; CHAIN-GRADE, link 2)*

**CANONICAL STATEMENT:**

> “*Source: `HETOW_passPE2_report.md` @ 67cbab2 — verdict CLEAN
> (0C/0G/3m). Per the arc the tower σ-closure counter moved 0/2 →
> **1/2 and HOLDS THERE**: these three cures are dated appends to
> MINOR findings, not a scoring round; one further clean pass on a
> fresh surface is still required. The [r1] body above is BYTE-FROZEN
> — each correction below supersedes its quoted sentence of record.*”

**FORM:** italic preamble under `### Dated corrections (2026-08-09, post-PE2)`.

**DERIVATION:** `[RECORD]` — and note the arc rule it applies: a CLEAN pass scores even though it returned three minors, because minors are cured by dated append rather than by a scoring round. The counter “HOLDS THERE” is the note's own guard against double-counting the cure round.

**CONDITIONALITY:** the counter is superseded to 2/2 at `.46`. The freeze declaration is FREEZE-3's predecessor and governs `.43`–`.45`.

**RESOLUTION TRACE:** statement lines 541–546.

**TEETH:** `git cat-file -t 67cbab2` = commit; `HETOW_passPE2_report.md` exists.

---

### EFF.HETOW.43  [changes-record]  *(SERIES CORRECTIONS-PE2, link 1; CHAIN-CARRY — TERMINAL)*

**CANONICAL STATEMENT:** correction C-A in full (source lines 548–569 — **this exact span is the object T2 pins**; see the consumer trace below):

> “**C-A (cures PE2 F-A — LEMMA HETOW-2's F-2 paragraph, §S2).** Two
> sentences corrected. (i) The exemplar in "If a slot coefficient is
> instead presented with x-degree ≥ D′ (e.g. a plain product ĉ_t·n̂ of
> a degree-≤ D′−1 lift by the x-monomial …)" is WITHDRAWN: at f₁ ≥ 2 a
> degree-< D′ lift times n̂(k) has exact-height-k part spanning one
> η-digit (the other digits' heights differ by e₁h-multiples), so it
> does not carry residue c_t and sits outside the paragraph's own
> premise "the unreduced coefficient's [residue] = r̃'s t-coefficient";
> the paragraph's scope is presentations of the CORRECTED key's (LIFT)
> coefficient augmented by above-height junk of x-degree ≥ D′. (ii) The
> closing "Either way LEMMA HE7-12 [r2, r3] applies" is RE-SCOPED to
> the (LIFT)-slot form this note's consumers actually feed to HE7-12 —
> the F-4 branch, **w = 0**: at the (e₂ = 1, t = f₂−1) corner a
> junk-augmented coefficient's moved piece x^{r′}π^{·}Φ′ lands at slot
> e₂t + 1 = e₂f₂, the LEADING slot, so w would acquire an
> x-degree-≥ D″ term and HE7-12's hypothesis "deg w < D″" (HE7_PROOF
> §S5.8) fails there. The accounting core stands: value monotone, raise
> exactly u₂ − e₂D′h, residue unchanged via the Ô[x] identity —
> machine-exact at frame R with r′ = e₁−2 maximal. PE2's consumer
> trace found the two in-repo consumers (HETOW.A(i); the GENHN dated
> erratum's display) both pinned to the (LIFT) form — neither reaches
> the withdrawn exemplar or the corner.”

**FORM:** bold-headed dated correction with two numbered sub-corrections.

**DERIVATION:** (i) an η-digit height argument showing the withdrawn exemplar violates the paragraph's own premise; (ii) a degree computation at the `(e₂ = 1, t = f₂−1)` corner showing HE7-12's `deg w < D″` hypothesis fails for junk-augmented presentations.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin** (both sub-corrections narrow scope; neither replaces a claim). **TARGETS:** `EFF.HETOW.19` (the F-2 paragraph) and, transitively, the licence clause of `EFF.HETOW.17` and the Ψ-row of `EFF.HETOW.09`.

**CONSUMER TRACE (queue-charged; grep-verified at compile time).** C-A has a downstream pin, and it is the only one of the three post-PE2 riders that does.

`[TABLE — compiler ledger]`

| Consumer | Designation | count | site | What it does with C-A |
|---|---|---:|---|---|
| `T2_SIGMA_LADDER_MASTER_2026-08-12.md` | `HETOW-KEY-BRIDGE-C-A` | **16** | pin row introduced at line 4246; repair heading at 4216 | pins **this exact span [548, 569]** as a `(PINS)` row in T2's HETOW block, “immediately after the `HETOW-KEY-BRIDGE` row” |
| same | `HETOW-KEY-BRIDGE` | 41 | throughout | the parent pin (= `EFF.HETOW.17`) whose closing licence C-A governs |
| `spec/EFF-T2-s6of6.md` | `HETOW-KEY-BRIDGE-C-A` span [548, 569] | 1 | §'s pin-verification row U01 | records “both delimiter lines exact-match … 1 each, at 548 and 569” |

**Span verification, executed fresh here rather than taken from T2:** line **548** of `HETOW_RECON_2026-08-09.md` is `**C-A (cures PE2 F-A — LEMMA HETOW-2's F-2 paragraph, §S2).** Two`, line **569** is `the withdrawn exemplar or the corner.`, and line 570 is blank. **The pinned span is exactly this unit, with no over- or under-reach.**

**What T2's r12 concludes about C-A — the load-bearing half of the trace.** T2's repair heading (line 4216) reads:

> “## r12 repair 1 — G-1 (GAP): HETOW's post-PE2 correction C-A pinned as `HETOW-KEY-BRIDGE-C-A`, and S1.8B's \(w\ne0\) branch re-based on a master-side degree bound”

and its reasoning (line 4242) records that C-A **does not reach T2's own entry**, with the reason:

> “This is why HETOW's dated correction C-A(ii) — pinned as `HETOW-KEY-BRIDGE-C-A`, whose reading directive governs the closing sentence of `HETOW-KEY-BRIDGE` — does not reach this entry although it re-scopes that closing "Either way LEMMA HE7-12 [r2, r3] applies" to \(w=0\): its ground is a junk-augmented presentation which at the \((e_2=1,\ t=f_2-1)\) corner acquires an \(x\)-degree-\(\ge D''\) term, and such an object is not the monic degree-\(D_2\) key the instance boxes substitute.”

T2 additionally records that only the VALUE disjunct is source-read, and supplies the missing degree conjunct itself:

> “`HETOW-KEY-BRIDGE` gives \(\Phi_2=\Psi_{\kappa_2,\widetilde r}-w\) with "either w = 0 … or dv₂(w) > T₂" — the VALUE disjunct, which is the only conjunct read off a source statement here … LEMMA HE7-12's remaining hypothesis \(\deg w<D''\) is supplied here by this master, from the monicity of the two keys”

**Compilation consequence, recorded not adjudicated:** a downstream consumer reads `EFF.HETOW.17`'s displayed “deg w < D″ **and** (w = 0 or dv₂(w) > T₂)” as supplying BOTH conjuncts, while T2 — having audited the same sentence — treats only the disjunct as source-supplied and re-derives the degree bound master-side from `D″ = D′e₂f₂ = D₂` (the identity audited at `.09`). Both readings are defensible against the displayed text; they differ on whether the lemma's own `deg w < D″` clause counts as established for junk-augmented presentations. See OPEN-CALL 1.

**RESOLUTION TRACE:** statement lines 548–569; consumer sites `T2_SIGMA_LADDER_MASTER_2026-08-12.md` 4216/4242/4246/4248/4257.

**TEETH:** the “machine-exact at frame R with r′ = e₁−2 maximal” claim is verified against the committed artifact: `hetow_pe2_fresh_output.txt` carries frame **R** legs `E2-coh-eq-minpoly-R  ok  ((4, 4), (3, 0)) vs ((4, 4), (3, 0))` and `E3-naive-diverges-R  ok`, with the run's total line `TOTAL gp sigma jobs 20 + 4 letter + 1 val-block; violations 0 (131.5s)` / `VERDICT: GREEN` ✓. The consumer-trace claim (“the two in-repo consumers … both pinned to the (LIFT) form”) is corroborated: `.22` reads at the corrected key and the GENHN erratum display is the corrected one (X07/X08).

---

### EFF.HETOW.44  [changes-record]  *(SERIES CORRECTIONS-PE2, link 2; CHAIN-MECH — TERMINAL)*

**CANONICAL STATEMENT:**

> “**C-B (cures PE2 F-B — the §S2 preamble's mechanism sentence; the
> σ-BLIND seam face recorded).** The sentence "W(t) is non-linear in t,
> so no K₂^×-rescale absorbs it" is CORRECTED: at f₂ = 2 (t ∈ {0,1} —
> frames X/Z/W, the r1 machine contacts) any W is affine and the quoted
> reason is empty there; the operative pin at those frames is
> **W(f₂−1) = ⌊i(u₂)/e₁⌋ = 0 against the monic normalization** — a
> rescale λ^{−f₂}r̃(λZ) matching the naive residues needs η^{−W(t)} =
> λ^{t−f₂}, and t = f₂−1 with c_{f₂−1} ≠ 0 forces λ = 1. When
> c_{f₂−1} = 0 an affine wrap CAN be a rescale (e.g. ψ₂ = Z² − c₀ with
> η a square), leaving the naive slot polynomial irreducible; at f₂ ≥ 3
> the non-affinity mechanism is live (frame V: W = (1,1,0)). At frames
> X/Z/W the sentence's conclusion follows from the W(f₂−1) = 0 pin, so
> the [r1] records stand.”

and the σ-BLIND record, verbatim:

> “**σ-BLIND record (PE2 frame V: p = 7,
> f₂ = 3, ord(η) = 6):** the gauge-naive key's PARI σ = {(2,3)} = the
> carrier's σ on both oracle routes, while nfmodpr shows ψ₂(η₂(ξ)) ≠ 0
> at the naive key's roots — a wrap seam with zero σ symptom at this
> frame. The LETTER clause (ψ₂(η₂(ξ)) = 0, HETOW-1(b)/T(b)′(i)) is the
> load-bearing detector; a σ-shaped regression tooth
> ("σ(naive) ≠ σ(corrected)", the shape of §S7's G2) is insufficient
> by itself — ported to a frame like V it passes on the broken key.”

**FORM:** bold-headed dated correction + a bold-headed sub-record.

**DERIVATION:** the corrected reason is an explicit rescale computation: matching the naive residues by `λ^{−f₂}r̃(λZ)` requires `η^{−W(t)} = λ^{t−f₂}` for all t, and `t = f₂−1` with `W(f₂−1) = 0` and `c_{f₂−1} ≠ 0` forces `λ = 1`.

**CONDITIONALITY:** SUPERSESSION KIND: **replacement of a justification** — the CONCLUSION (no rescale absorbs the wrap) survives at frames X/Z/W; the stated REASON was empty there. The note also fences the corrected claim honestly: **when `c_{f₂−1} = 0` an affine wrap CAN be a rescale**, so the conclusion is not universal.

**RESOLUTION TRACE:** statement lines 571–590.

**TEETH:** **the σ-BLIND record is a TOOTH-INVALIDATION finding and it is machine-verified.** `hetow_pe2_fresh_output.txt` carries, at frame V: `G1-coh-V  ok  sigma = ((2, 3),)` and `G2-naive-V-SIGMABLIND-routes-agree  ok  ((2, 3),) vs ((2, 3),)` — **the naive key and the corrected key give the SAME σ = {(2,3)} at frame V, on both oracle routes** ✓, exactly as C-B states. The frame's minpoly(β) is printed as `(5, 4, 5)`, i.e. `Z³ + 5Z² + 4Z + 5` — matching C-C's independent citation of the same frame (`.45`) ✓. Disposition: **`stale self-description` on §S7's G2 tooth shape** — the tooth is not wrong at X/Z/W, but its GENERIC adequacy claim is falsified, and the note replaces it with the letter clause.

---

### EFF.HETOW.45  [changes-record]  *(SERIES CORRECTIONS-PE2, link 3; CHAIN-BOX3, link 3)*

**CANONICAL STATEMENT:**

> “**C-C (cures PE2 F-C — HETOW-BOX-3 [r1] gains the multi-wrap axis).**
> Appended to BOX-3's NOT-exercised list: **f₂ ≥ 3 multi-wrap frames**
> (two or more live η^{W(t)} units, W genuinely non-affine — the
> t-dependence of the [r1] prescription itself), omitted at [r1] while
> the three supp frames sit at f₂ = 2 with a single wrap unit. Mooted
> in substance by the PE2 fresh route and cited as machine contact:
> **frame V** (p = 7, f₂ = 3, W = (1,1,0), ord(η) = 6;
> `hetow_pe2_fresh.py` artifacts @ 67cbab2) ran GREEN on dual PARI
> routes — corrected key σ = {(2,3)}, slot residues = minpoly(β) =
> Z³+5Z²+4Z+5 exactly, both W-telescoping identities (heights 6 and 9)
> exact, μ₂ = 2 trichotomy 8/8, forced μ₂ = 3 {(6,3)} row. The axis is
> now a disclosed row with first contact on record rather than an
> omission.”

**FORM:** bold-headed dated correction.

**DERIVATION:** `[RECORD]` of a coverage-inventory completion plus its immediate discharge by a new machine contact.

**CONDITIONALITY:** SUPERSESSION KIND: **inventory completion**. Unusually, the added row is discharged in the same breath — the axis goes from “omitted” to “disclosed with first contact” without ever being an open coverage hole in the effective text.

**RESOLUTION TRACE:** statement lines 592–604; the box it edits is `.30`.

**TEETH:** **RE-VERIFIED against the committed artifact.** `hetow_pe2_fresh_output.txt` frame-V lines: `killed(naive) (4, 6, 5)  killed(coh) (5, 4, 5)  minpoly(beta) (5, 4, 5)`; `E2-coh-eq-minpoly-V  ok  (5, 4, 5) vs (5, 4, 5)`; `E2-twist-real-V  ok  minpoly (5, 4, 5) != psi2 (2, 1, 1)`; `E3-naive-diverges-V  ok  naive (4, 6, 5) vs minpoly (5, 4, 5)`; `G1-coh-V  ok  sigma = ((2, 3),)`. **The coefficient triple (5, 4, 5) is exactly `Z³ + 5Z² + 4Z + 5` read low→high with the monic leading term implicit** ✓ — the note's transcription is exact. Run verdict `GREEN`, 0 violations ✓. ARITHMETIC AUDIT of `W = (1,1,0)`: at f₂ = 3 the entries are `W(t) = ⌊(3−t)i(u₂)/e₁⌋` for t = 0,1,2, and `W(2) = W(f₂−1) = 0` ✓ — consistent with C-B's pin, and genuinely non-affine since (1,1,0) is not an arithmetic progression ✓.

---

### EFF.HETOW.46  [acceptance-box]  *(SERIES ARC, link 3; CHAIN-GRADE, link 3)*

**CANONICAL STATEMENT:** the acceptance, verbatim:

> “**ACCEPTANCE.** Per the arc rule the tower σ-closure counter moves
> 1/2 → **2/2 — HETOW ACCEPTED** (the CLEAN bar: nothing at
> GAP-or-worse survived the pass's own verification). The arc, one
> breath: seal (3e19eba) → passPE1 NOT CLEAN, 1 CRITICAL — the
> ϖ-wrap-cocycle seam in the sealed key (5f821dc) → r1's corrected key
> ĉ_t ↦ L_{(f₂−t)u₂}(c_t·η^{W(t)}), W(t) = ⌊(f₂−t)i(u₂)/e₁⌋ (5335ae3)
> → passPE2 CLEAN 0C/0G/3m, counter 0/2 → 1/2 (67cbab2) → rider
> C-A/C-B/C-C (5b879e0) → passPE3 CLEAN 0C/0G/1m, counter 1/2 → 2/2
> (5b6db24).”

and — the compilation's most portable finding in this unit — **what the two clean passes actually certified**:

> “What the two clean passes proved at the corrected key:
> **wrap-immunity** of the §S1 termination row (the wrap correction
> moves unit factors only — heights, degrees, and multiplicities,
> hence HE6R1-1's descent factor ℓd_r = e₂f₂ and both displayed
> bounds, are untouched by it) and **gauge-invariance** of the
> tightness read, with the letter clause (ψ₂(η₂(ξ)) = 0,
> HETOW-1(b)/T(b)′(i)) standing as the load-bearing seam detector at
> the σ-blind faces (PE2 frame V at f₂ = 3; PE3 frame M2 at f₂ = 4).
> Consequences inherit min over {GENHN 0/2, HE6 0/2 post-r2, HE7
> (frozen, accepted annex stack), HE3 1/2 at μ ≤ 3} per the status
> header.”

**FORM:** bold-headed acceptance paragraph with an inline arc and a certification clause.

**DERIVATION:** `[RECORD]` of two consecutive CLEAN passes under a stated bar (“nothing at GAP-or-worse survived the pass's own verification”).

**CONDITIONALITY:** **the min-inheritance clause is restated here and is NOT lifted by the 2/2.** A consumer must carry it: HETOW ACCEPTED does not make its consequences accepted. The wrap-immunity and gauge-invariance certificates are POSITIVE scope findings attached to `.25` and to the tightness row of `.09`.

**RESOLUTION TRACE:** statement lines 614–632.

**TEETH:** **all six commit pins in the arc resolve**: `3e19eba`, `5f821dc`, `5335ae3`, `67cbab2`, `5b879e0`, `5b6db24` — `git cat-file -t` = commit on every one ✓. `HETOW_passPE3_report.md` exists. The frame-V σ-blind face is machine-verified at `.44`; **frame M2 at f₂ = 4 is cited but is UNPINNED** — no artifact filename is given and none matching an M2/f₂ = 4 run exists in `verification/openmath/`. Disposition `UNPINNED` (v3 rule 23); OPEN-CALL 2.

---

### EFF.HETOW.47  [changes-record]  *(CHAIN-BOX3 — TERMINAL)*

**CANONICAL STATEMENT:**

> “**F-α CURE (PE3's one MINOR — HETOW-BOX-3's e₂f₂ ≥ 4 row folded
> against PE2's frame S).** The [r1] row reads "e₂f₂ ≥ 4 (both ℓ ≥ 2
> AND d_r ≥ 2 — first live n = 24)"; its parenthetical pins the row's
> reading to the μ₂ ≥ 3 box family, under which it stays literally
> accurate — frame S's members sit at μ₂ = 2, and no μ₂ ≥ 3 member at
> e₂ ≥ 2 is on record. Appended citation, scoped **μ₂ ≤ 2 trichotomy
> grade**: PE2's **frame S** (p = 3, (e₂,f₂) = (2,2), u₂ = 5; η ≠ 1
> twist-trivial but wrap-live) carries the first e₂f₂ = 4 machine
> members, at μ₂ = 2, n = 16: RAM {(8,2)} FORCED (dv₂ = 41 via the
> b-odd Φ′-monomial) and integer-λ₂ menu 2/2 ({(4,4)}) —
> `hetow_pe2_fresh.py` artifacts @ 67cbab2. Verified against those
> artifacts before this append: the runner's G4 design row pins
> frame S at μ₂ = 2, n = 16, T₂ = 20; both G4 job constructors call
> `member(cS, 2, ·)` (the 2 is μ₂); the committed output scores
> G4-RAM {(8,2)} (1 member, dual routes agree) and G4-INT {(4,4)}
> (2 members, dual routes agree) inside the sealed menu
> {{(8,2)},{(4,4)},{(4,2),(4,2)}}, run total 0 violations. The row's
> μ₂ ≥ 3 face (first live n = 24) has no machine contact and stays on
> the NOT-exercised list.”

**FORM:** bold-headed dated cure with an explicit pre-append verification record.

**DERIVATION:** a scope reading of the row's own parenthetical, plus an artifact-level verification the note performed before appending.

**CONDITIONALITY:** SUPERSESSION KIND: **scope-pin**. **The row is NOT removed** — its μ₂ ≥ 3 face stays on the NOT-exercised list. This is the cleanest example in the note of a coverage claim being narrowed rather than discharged.

**RESOLUTION TRACE:** statement lines 634–652; the box it edits is `.30`.

**TEETH:** **RE-VERIFIED at compile time.** `hetow_pe2_fresh_output.txt` carries `G4-RAM:((8, 2),)   1` ✓ (one member) and frame-S legs `E2-coh-eq-minpoly-S  ok  (2, 1) vs (2, 1)`, `E3-naive-diverges-S  ok  naive (1, 1) vs minpoly (2, 1)` ✓; run total `violations 0` / `VERDICT: GREEN` ✓. ARITHMETIC AUDIT: at frame S, `e₂f₂ = 2·2 = 4` ✓; `n = D′·e₂f₂·μ₂ = 2·4·2 = 16` ✓; `T₂ = e₂f₂·u₂ = 4·5 = 20` ✓ — the note's three design constants reproduce exactly from its own formulas. The σ degree sums at n = 16: `{(8,2)}` → 16 ✓; `{(4,4)}` → 16 ✓; `{(4,2),(4,2)}` → 8+8 = 16 ✓ — the sealed menu is degree-consistent. **“first live n = 24” for the μ₂ ≥ 3 face**: `D′·e₂f₂·μ₂ ≥ 2·4·3 = 24` ✓.

---

### EFF.HETOW.48  [record]  *(SERIES ARC, link 4; CHAIN-GRADE — TERMINAL)*

**CANONICAL STATEMENT:**

> “*Provenance: the post-acceptance decorrelated ratification run
> (`CODEX_TOWERRAT_2026-08-10.md` §S2, session
> 019fe985-2c4b-7fc0-9885-5e558447502d, outcome CHALLENGE, 3 GAP):
> F-1 adjudicated REAL (the confirmed gap) → repaired by LEMMA
> HETOW-4 below; F-2 REAL as display → the cite annex; F-3 artifact
> in substance → the row annotation. The 2/2 acceptance stands
> ANNOTATED, now with the annotation DISCHARGED at this note's own
> grade; the body above stays BYTE-FROZEN — this append GOVERNS the
> S1 rows it names. Every derivation below is from this note's own
> lemmas + the frozen HE7 §S1/§S5.3, not from the verifier's text.*”

**FORM:** italic provenance preamble under the three-line heading `### Dated append (2026-08-10, TOWERRAT-R1 + two annexes): LEMMA HETOW-4 — the n̂₂/n₂ normalizer bridge, PROVED; the S1 J-D0 row superseded`.

**DERIVATION:** `[RECORD]` of a **decorrelated-model audit** run AFTER acceptance — the strongest instrument class in the note, and the only one that produced new mathematics.

**CONDITIONALITY:** **“The 2/2 acceptance stands ANNOTATED”** is the terminal grade reading: the note is accepted, the ratification's annotation is discharged, and the discharge is at THIS note's grade (which the min-inheritance clause of `.03`/`.46` still caps). The last sentence is a provenance fence worth carrying: the repair is derived from this note's own lemmas plus frozen HE7, **not** from the verifier's text — i.e. the verifier found the gap, the note closed it.

**RESOLUTION TRACE:** statement lines 660–669.

**TEETH:** `CODEX_TOWERRAT_2026-08-10.md` exists (XREF X06). Disposition `AUDIT / decorrelated-model audit` — and this is the audit class v3 rule 27 was added for: no battery could have produced F-1, because the defect was an underived equivalence in a justification cell (`.49`).

---

### EFF.HETOW.49  [supplier-finding]

**CANONICAL STATEMENT:**

> “**THE GAP, exactly.** The S1 normalizer row justified the n̂₂-vs-n₂
> discrepancy by "unit-residue discrepancy in K₂^× only; σ-content
> twist-invariant per HE7 §S1 CONVENTION (J-D0)". HE7's CONVENTION
> covers changes of normalizer WITHIN its ϖ-Φ′-monomial family
> (there the ratio at grade k is forced to be (Φ′^{ℓ}/ϖ^{u})^{c},
> residue β^{c}); the tower ladder monomial n̂₂(k) = x^{i}π^{a}Φ′^{b}
> is NOT in that family, and THEOREM HE7.A(2)/(3)'s routing
> predicates (separability of R_{λ₂}; the repeated factor's
> K₂-rational letter s₂, consumed by (LIFT₂)) are letter-sensitive —
> an arbitrary per-height unit twist can change them. The missing
> lemma computes the ratio's residue exactly and shows what it
> contributes: the twist does NOT cancel per height (the raw
> pin-residue strings of the two systems genuinely differ,
> non-geometrically); it cancels in the ASSEMBLED residuals, whose
> comparison is a single global unit times a K^×-rescale — the
> species HE7's J-D0 display does cover — and both routing
> predicates transport.”

**FORM:** bold-headed diagnosis paragraph.

**DERIVATION:** a family-membership argument (n̂₂ is not in HE7's ϖ-Φ′ family, so J-D0 does not apply) plus a sensitivity argument (the routing predicates are letter-sensitive).

**CONDITIONALITY:** **this is a self-diagnosed defect in the note's OWN justification cell**, found by a decorrelated verifier after 2/2 acceptance and three clean/near-clean passes. The paragraph also announces the shape of the cure before proving it — per-height non-cancellation, assembled-level cancellation — which is exactly what `.50`(b) and (c) establish.

**RESOLUTION TRACE:** statement lines 671–687; the cured row at `.53`.

**TEETH:** disposition `AUDIT / decorrelated-model audit`. Note the honesty of the finding's shape: it does not claim the conclusion was wrong, only that the JUSTIFICATION did not reach it — and the lemma then proves the conclusion true.

---
