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
