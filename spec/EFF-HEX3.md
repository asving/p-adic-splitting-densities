# EFF-HEX3 — CANONICAL EFFECTIVE SPECIFICATION v2/v3

## 1. Header

**Source note:** `lean/notes/openmath/HEX3_PROOF_2026-08-08.md` (1,059 lines / 63,417 bytes).

**HEAD blob hash:** `2917bd1bc146863137e0d25a623bfbcd06bee422` (repo HEAD `8032dc52cff56ab15dc48f494a1f8c9b61c3958d`). Whole-file md5 at compile time: `f1a47eff1052833121978c6e0d853b94`.

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Stage 0a, Opus wave 4, queue 8b (Asvin-authorized substitution, `docs/PROJECT_STATE.md` #51).

**Governing template:** `spec/EFF_TEMPLATE_v2.md` AT HEAD — rules 1–28 (v2 rules 1–10 plus the v3 prose-genre rules 11–28). Full compilation, unsharded (63 KB, below the ~80 KB shard threshold of rule 9).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). **CODEX CROSS-READ OWED** (post-reset).

**Queue-specific charge discharged here:** HEX3-BOX-1's tail-σ-certification lemma is the subject of ledger row **HYP.137**; its exact conditionality wording is compiled at `EFF.HEX3.37` CONDITIONALITY and again in §5.3, and the reader-convention item from `leancheck/notes/N3_CHECK_2026-08-13.md` §6d (ledger row **HYP.138**) is compiled as an explicit **consumer note** at §5.4.

### Effective-text rule

The note carries a literal effective-text rule in each of its three dated appends. The freeze is stated at the acceptance record (L917–921):

> “This note is FROZEN: dated appends only.
> Everything above this heading — sealed body L1–832, the post-PE6
> rider, the arc line — is byte-untouched by this append (pre-append
> file md5 b92f47a8895f8c7040c8fe9d7db4473d is the prefix); runner +
> artifacts stay at seal e3f3459.”

and the same discipline is declared at the first append (L841–844):

> “Discipline:
> dated append only — the sealed body above (lines 1–832) is
> byte-untouched by this rider; runner + artifacts stay frozen at seal
> e3f3459”

and at the third (L982–983):

> “Everything above this heading is byte-untouched by this
> append.”

**Therefore the effective text is: the sealed body L1–832 read with its inline `[r1]`–`[r4]` bracket repairs applied in place (they are physically inside the sealed body, each self-labelling its target), then the three dated append blocks applied in date order — the 2026-08-09 post-PE6 rider (Correction 1, Correction 2 = the ARC line), the 2026-08-09 post-PE7 acceptance record (ACCEPTANCE, Correction A, Correction B), and the 2026-08-12 sol-A0 ratification fold (Corrections C, D, E, F).** Where two appends touch the same span the later governs; the two same-span collisions are tabulated below. No body text is edited by any append: an append supersedes a *reading*, and the frozen sentence remains physically present. Every superseded body sentence is emitted here with its `[SUPERSEDED]` marker and its governing replacement.

### FREEZE PREDICATES (rule 21 — four independent freezes, each with its own quote and pin)

**FREEZE-1 — text freeze (acceptance).** L917: “This note is FROZEN: dated appends only.” Pin: the pre-append prefix md5 `b92f47a8895f8c7040c8fe9d7db4473d`. **PIN VERIFIED at compile time** (rule 23): the md5 of the file's first 907 lines (53,951 bytes, ending with the ARC blockquote's closing line “counter 1/2; PE7 next.”) is exactly `b92f47a8895f8c7040c8fe9d7db4473d`. The pin is therefore not merely plausible — the boundary is located to the byte.

**FREEZE-2 — instrument freeze (the sealed runner).** L843–845: “runner + artifacts stay frozen at seal e3f3459 (runner md5 83faf7edb554811cd657691d7ea256cc, results JSON ce6f41162a22b0bd66a641e98cb4d56e)”. **PIN VERIFIED:** `git cat-file -t e3f3459` = `commit`; `md5sum verification/openmath/hex3_checks.py` = `83faf7edb554811cd657691d7ea256cc`; `md5sum verification/openmath/hex3_checks_results.json` = `ce6f41162a22b0bd66a641e98cb4d56e`. Both exact. The third artifact, L743–744 “`hex3_checks_output.txt` (md5 6e4b3207562d8ba93811d77ab41f0391)”, **also verifies exactly.**

**FREEZE-3 — upstream instrument freeze (the four md5 pins the runner consumes).** S7 L523–527 pins `w12_checks.py 7dc040d94fbbb1e8d20ac817b665d418`, `w11_checks.py 500aae152bb5b5e9df3712904a6d73a6`, `w10_checks.py a9c34244a3af19f5fa864375b494380b`, `w12_checks_results.json 05776c9e00071c5d7524abdfbe894442`. **ALL FOUR VERIFIED EXACTLY** against `verification/openmath/` at compile time.

**FREEZE-4 — hostile-report freeze.** L845–847: “the PE6 report is byte-frozen at md5 42d86c7aeb3f5652657d44d6608fb247”; L915: “`HEX3_passPE7_report.md`, md5 4049109c272617c10acb62f77fbf0c2e, byte-frozen”. **BOTH VERIFIED EXACTLY.**

**Compiler note on the freeze set:** eight independent md5 pins are asserted by this note and **eight of eight reproduce byte-exactly at HEAD**, and the prefix pin localizes to a unique line boundary. This is the strongest pin result in the queue-8b corpus so far and is recorded as such; no `UNPINNED` disposition is needed anywhere in this note.

### Supersession chains inside the note

`[TABLE]`

| Target span (body) | Layer 1 (body `[r]`) | Layer 2 (2026-08-09 rider) | Layer 3 (2026-08-09 acceptance) | Layer 4 (2026-08-12 A0) | TERMINAL |
|---|---|---|---|---|---|
| P-1 never-measured census (S7 L546–593) | `[r1]` 11-set → `[r2]` TWELVE-set | — | — | — | **`[r2]` twelve-set** |
| S10 P-1 scorecard label “ELEVEN” (L748–767) | `[r1]` → `[r2]` | — | — | — | **`[r2]`** |
| HEX3-BOX-1 mechanism clause (S6 L440–442) | — | Correction 1 (three drain genres) | Correction B (genre (i) superlative scoped) | Correction E (the vanishing-fraction *justification* replaced) | **Correction E for the justification; Correction B's displayed clause otherwise** |
| “tail half of (hMenu-3)” (S0 L104–105; BOX-1 L447–449; S8.2-1 L653–654) | — | — | **Correction A** | — | **Correction A** |
| Arc record endings (header L16, BOX-2 L481, S10 L826–829) | `[r1]`/`[r2]`/`[r3]` brackets | Correction 2 = the ARC line | ACCEPTANCE (counter 1/2 → 2/2) | ledger row → CERTIFIED | **ACCEPTANCE (+ the A0 CERTIFIED line)** |
| HEX3-BOX-2 / S10 “46 rows × every realized key” (L487–490, L788–790) | — | — | — | **Correction C** | **Correction C** |
| P-7 deep-row falsifier sentence (L617–620) | — | — | — | **Correction D** | **Correction D** |
| S5.4 “one polynomial law in (q, N)” (L429) | — | — | — | **Correction F** | **Correction F** |
| S0 “every lift” Ore warrant (L81–93) | `[r4]` | — | — | — | **`[r4]`** |
| BOX-1 “(all lifts genuinely ambiguous)” parenthetical (L453–462) | `[r4]` | — | — | — | **`[r4]`** |
| S3.1 H-2(i) threshold pairing (L259–269) | `[r1]` F1 (`N−jk`, not `N−(3−j)k`) | — | — | — | **`[r1]`** |
| S8.2-2 k = 1 N-linear mass (L663–669) | `[r2]` m1 (the `(1 − q^{−(N−3)})` factor restored) | — | — | — | **`[r2]`** |
| S8.2-2 W-12.B consistency clause (L694–702) | `[r3]` m1 (conditionalized) | — | — | — | **`[r3]`** |

**Two same-span collisions, both resolved by date order.** (a) BOX-1's mechanism clause is touched by Correction 1, then by Correction B, then by Correction E — a four-layer CHAIN recorded in full at `EFF.HEX3.37` with its TERMINAL member marked (rule 25). (b) The arc record is touched by three body brackets, the ARC line, and the acceptance record — a five-layer CHAIN, recorded at `EFF.HEX3.61`/`.63`/`.64`.

### Scope of record — three-predicate split (rules 7 and 17)

#### A. Mathematical absorption/supply set

The note's own delivery sentence, S0 L96–107:

> “**Delivered here:** the EXACT closed-form law for U₃^conv (THEOREM
> HEX3.A — the two-species node calculus of the obstruction is executed:
> the (α) triple-cluster species' instance bracket AND the (β)
> DBL-re-entry species' window-transfer law are both derived, which is
> exactly the calculus BOX-3 named), hence a vanishing upper bound for
> U₃^σ (THEOREM HEX3.B) — the (hExhaust-3) obstruction in W-12.D's
> n = 3 conditionality is DISCHARGED at composition grade. NOT delivered:
> the tail-σ-certification lemma, hence no exact law for U₃^σ itself —
> that residue is HEX3-BOX-1, priced with its exact mechanism (it is the
> tail half of (hMenu-3), i.e. W-13's floor, not this unit's charge).
> This note does not edit W12_PROOF; the proposed BOX-3 annex text is
> §S8.1.”

The supply set is therefore **two theorems and one corollary (HEX3.A, HEX3.B, HEX3.C), resting on four new lemmas (H-1, H-2, H-3, H-4) and the S5 assembly**, over the two suppliers W-11 and W-12 (plus J-D0, corroborative only). The number of *source obligations discharged* is **one**: W12-BOX-3's named obligation, “a vanishing U₃^TRP upper bound”, `(hExhaust-3)` at n = 3. The parenthetical residence claim inside this very sentence — “it is the tail half of (hMenu-3), i.e. W-13's floor” — is **withdrawn by Correction A** (`EFF.HEX3.65`); the delivery set itself is unaffected.

#### B. Consumption / append-protocol scope — **LANDED**, and the note's own self-description is stale

The body says (S0 L106–107, S8.1 heading L633): “This note does not edit W12_PROOF”; “**S8.1 Proposed annex to W12-BOX-3 (text offered; W12_PROOF not edited)**”.

Per template **rule 10**, that cross-note status claim is checked against the target's FULL append chain, not against the pinned sentence. It is **stale**: the annex **HAS LANDED**. `W12_PROOF_2026-08-08.md` L1654 opens

> “## ANNEX (dated append, 2026-08-08, post-r1 — separate from the r1 repair): the W12-BOX-3 annex from HEX3, applied verbatim”

and carries the annex text verbatim at L1672–1683, under the wrapper (L1655–1658)

> “Applied VERBATIM from HEX3_PROOF_2026-08-08.md §S8.1 (HEX3 seal
> e3f3459 / verdict 671a126, battery GREEN 158,512 checks / 0 violations
> on 46 rows both characteristics; adjudicated @ a0290f9), per that
> adjudication's work order.”

Landing pins **VERIFIED**: `git cat-file -t 671a126` = commit; `git cat-file -t a0290f9` = commit; `grep -cF 'BOX-3 ANNEX' W12_PROOF_2026-08-08.md` = **2** (the annex block plus one back-reference at L1590). The two texts were compared clause by clause at compile time and are identical.

Accordingly the protocol scope is: **one absorption, CONSUMPTION LANDED AT THE SUPPLIER, with the home note's own "not edited" sentence a `STALE-SELF-DESCRIPTION` (rule 26)** — not a supersession, because no append of HEX3 corrects it, but a reader must be told it is no longer true. See `EFF.HEX3.53`.

#### C. Inbound corrections RECEIVED from supplier notes (rule 17)

Three, all quoted at their targets.

1. **From W-12's own r4** (into HEX3 S0, as the `[r4]` bracket at L82–93): W-12 struck its S2.3 “every lift” Ore warrant with a counter-instance; HEX3's inequality `U₃^σ ≤ U₃^conv` is re-warranted at the pinned notion rather than withdrawn. Recorded at `EFF.HEX3.06`.
2. **From W-12's r3 σ-pin `b17238a`** (into HEX3 S8.2-2, via PE4's cross-note verdict): the discharge is re-read as pin-robust, `U₃^conv = (σ-undecided TRP) ∪ (certified TRP boundary tails)` exactly. Recorded at `EFF.HEX3.55`.
3. **From the ACCEPTED HMENU3** (into HEX3's Correction A): HMENU3 S5.4 discharged `(hMenu-3)` without the tail-σ lemma, which is what falsifies HEX3's residence attribution. Recorded at `EFF.HEX3.65`.

An **outbound** correction also exists and is recorded for the DAG: the W12 r4 PE4-F3 bracket at `W12_PROOF` L1580–1600 consumes THEOREM HEX3.A to strike a W-12.B order inference of W-12's own. See reverse-XREF RX-3 in §5.2.

### Resolution rules applied

1. Body brackets `[r1]`–`[r4]` are part of the sealed body and are applied in place; each names its own target span, so no ordering ambiguity arises among them.
2. The three dated appends apply in date order 2026-08-09 (post-PE6) → 2026-08-09 (post-PE7) → 2026-08-12 (sol A0). Where an append supersedes text that an earlier append itself introduced (Correction E over Correction B; Correction B over Correction 1), the later governs and the CHAIN is displayed.
3. **The ARC line is a supersession of exactly three record endings and nothing else.** Its own scope sentence fixes this: “supersedes the three r3-era record endings — header, HEX3-BOX-2, §S10”. It does not supersede the *mathematical* content of those sections.
4. The `[r1]` census (11 pairs) is **historical**, by the `[r2]` bracket's own words: “The [r1] 11-item list above stands as history”. The effective census is the twelve-pair set.
5. The frozen grade vocabulary — header “**Attempt grade 0/2**”, S1's “**GRADE: HEX3.A/B/C composed at attempt 0/2**”, S10's “DISCHARGED at attempt grade 0/2”, S9's “graded 0/2” — is **STALE-SELF-DESCRIPTION** after the acceptance record (counter 2/2, ACCEPTED) and after the 2026-08-12 fold (“HEX3's ledger row → CERTIFIED”). Tagged, not edited (rule 26).
6. `VERDICT: PENDING` (S7 L627) is superseded by S10's `GREEN` verdict — an intra-body two-commit protocol, not an append.
7. Correction 1's replacement typology is a **replacement** of a FALSE clause, not a gloss: its own words are “is FALSE and is superseded by”. Correction B then applies a **scope-pin** to one word of Correction 1's genre (i) (“DOMINANT”), and Correction E applies a **replacement** to the justification clause inside Correction B. Three different SUPERSESSION KINDs on one chain; they are not interchangeable (rule 18).
8. Corrections C and D are **scope-pins** on instrument-coverage claims, not mathematical corrections: both close with “No theorem statement … changes.”
9. Correction F is a **wording-rider** (a terminology repair) whose own text states the conclusion is unaffected.
10. Out-of-note material (W-12, W-11, HMENU3, GENIND, the census, N3_CHECK, the ledger) is used only to *resolve* and *verify*; nothing from it is inventoried here as HEX3 content.

### Quotation and prosification discipline

Every CANONICAL STATEMENT below is a verbatim source quotation or is explicitly marked `[ASSEMBLED]`. The note's two source tables (S5.1's species table; the S10 scorecard, which is a bulleted list, transcribed as a table only where flagged) are emitted as `[TABLE]`; no table is prosified. The note contains **no fixed-width ASCII display inside a code fence**, so rule 14's double-emission requirement is not triggered anywhere — recorded explicitly so a cross-reader knows the rule was checked and not skipped. Displays that the note writes as indented plain text (THEOREM HEX3.A's law, the R-definition) are reproduced with their line structure intact. Terminal punctuation inside quoted displays is preserved as written. The note's own strikethrough (`~~…~~`) is reproduced, since in this note strikethrough IS the supersession marker. Compiler classifications (`[IMPORTED]`, `[SUPERSEDED]`, `[STALE-SELF-DESCRIPTION]`, `[ASSEMBLED]`) are metadata, never source paraphrase.

---

## 2. NON-IMPORTS

The note's negative fences are unusually explicit; all are load-bearing for the DAG.

**N-1 — the four named non-consumptions.** S9 L727–729:

> “**NOT consumed:** the weld notes ([W12-H] untouched — everything
> here is order-1 digit calculus), PARI (no new oracle rows), the
> measure route, `htameFE`.”

*Compiler caveat, recorded not silently reconciled:* the PE6 fresh route later DID run a PARI/σ leg (ARC line: “the arc's first PARI/σ leg, wild cell (Zp, 3, 4) end-to-end, 58,158 oracle lifts”). That is a **hostile-pass instrument**, not a note import, and the sealed battery still carries no PARI leg (BOX-3: “no PARI leg here”). The fence stands as written for the note's own evidence; the arc's decorrelating leg is separately recorded at `EFF.HEX3.63`.

**N-2 — `(hMenu-3)` is untouched.** S0 L46–47: “the menu half ((hMenu-3), W12-BOX-2) is untouched here.” HEX3-BOX-4 L504–513 states the fence in full, including its consequence: “No claim that W-12.D fires at n = 3 yet.”

**N-3 — the tail-σ-certification lemma is deliberately not attempted.** BOX-1 L447–449: “Deliberately not attempted here (it is the tail half of (hMenu-3), W-13's floor; the w12 instrument was DESIGNED not to need it).” The parenthetical's *residence* clause is withdrawn by Correction A; the *non-attempt* fence is not.

**N-4 — no source file is edited by the composition.** S0 L106: “This note does not edit W12_PROOF”. **This fence is STALE** at HEAD in one direction only: HEX3 still edits nothing itself, but the annex it offered was subsequently applied to W12 by a separate dated append of W12's own (header §B). The fence is true of HEX3's action and false as a description of the corpus state.

**N-5 — the exact U₃^σ law is NOT delivered.** S0 L102–105 and BOX-1 L435–437: “its exact law is NOT derived”. This is the note's single largest negative-import fence and is the subject of ledger HYP.137.

**N-6 — J-D0 is corroborative, not load-bearing.** S9 L720–722:

> “**LEMMA J-D0** @ 1642275/9387eb1 — the gauge-blindness frame behind
> HEX3.C (corroborated, not load-bearing for the counts: the S2–S5
> arguments are self-contained slot counts).”

**N-7 — the machine leg is not a proof of the all-depth formulas.** Correction C L997: “The all-depth formulas rest on the uniform slot-count and transport proofs in S2–S3; the machine leg confirms those formulas only at the realized keys.”

**N-8 — no axiom, no weld face, no oracle.** S9 L733–734: “No axiom, no weld face, no oracle.”

**N-9 — the N = 1 corner is a convention, not a measured claim.** HEX3-BOX-5 L514–516: “used only as the recursion seed; all battery rows have N ≥ 2.”

---

## 3. Statement inventory

IDs `EFF.HEX3.01`–`.71`.

### EFF.HEX3.01  [convention]

**CANONICAL STATEMENT** (verbatim, S1 L111–113). FORM: inline sentence.

> “Conventions as in W-12 §S1 (O a complete DVR with residue field F_q,
> either characteristic; window N ≥ 2; the recursive OM-convention read).”

**DERIVATION.** [IMPORTED] — a wholesale import of the supplier's §S1 conventions; no derivation is offered or needed.

**RESOLUTION TRACE.** statement lines 111–113; proof lines — (none); correction sites — (none).

**CONDITIONALITY.** Unconditional as a convention. Note the seam with `EFF.HEX3.41`: the conventions say `N ≥ 2`, while THEOREM HEX3.A is asserted “every N ≥ 1” and `u(q,1) = 1` is supplied as a seed by HEX3-BOX-5.

**XREF.** `W12_PROOF_2026-08-08.md` — designation `S1`, fixed-string count 78 (a section anchor; the count is an upper bound, since `S1` also matches `S1x` forms). NEAR-MISS disposition not needed: the referent is the note's §S1 heading, located at `W12_PROOF_2026-08-08.md` L57 (`## S1.`).

---

### EFF.HEX3.02  [definition]

**CANONICAL STATEMENT** (verbatim, S1 L113–116). FORM: inline sentence.

> “The TRP stratum at window N = monic cubics over O/π^N with f̄ = (x−c̄)³
> for some c̄ (q·q^{3(N−1)} members: q centers × the recentered
> coefficient states (b₂, b₁, b₀) ∈ (πO/π^N)³, an exact translation
> bijection).”

**DERIVATION.** [ASSEMBLED] from the parenthetical itself: the count `q·q^{3(N−1)}` is the product of the centre count `q` with the recentered-state count `q^{3(N−1)}`, and the “exact translation bijection” is the warrant that the two factorize. **Arithmetic audit:** `#(πO/π^N) = q^{N−1}` per coordinate, three coordinates, so `q^{3(N−1)}` ✓; times `q` centres ✓.

**RESOLUTION TRACE.** statement lines 113–116; proof lines 190–191 (S2 re-states the state space as `(B₂, B₁, B₀) ∈ (πO/π^N)³`, `q^{3(N−1)}` states, per centre); correction sites — (none).

**CONDITIONALITY.** Unconditional. The whole-space/per-centre factor `q` is load-bearing everywhere downstream (`U₃^conv = q · u`); see the arithmetic audit's convention finding in §7.

**XREF.** none required (self-contained definition).

---

### EFF.HEX3.03  [definition]

**CANONICAL STATEMENT** (verbatim, S1 L116–120). FORM: inline sentence.

> “The CONSERVATIVE READER = the sealed w12 `read_trp`
> convention: recursive polygon/residual read at the (recentered) triple
> center; repeated residual root ⟹ recenter deeper; separable residuals
> ⟹ DECIDED; any state with v(B₀) ≥ N (B₀ = 0 in-window) ⟹ UNDECIDED, no
> tail certification.”

**DERIVATION.** [DEFINITIONAL] — this is the definition of the measured object, pinned to a sealed artifact rather than derived. Its faithfulness is the business of the HEX3-XREAD battery family (`EFF.HEX3.47`), which ties a fresh reader pointwise to the sealed one.

**RESOLUTION TRACE.** statement lines 116–120; proof lines — (none; the tie is instrumental, at L604–606 and L774–775); correction sites — (none).

**CONDITIONALITY.** Conditional on the sealed w12 reader being what the runner's md5 pin says it is. **PIN VERIFIED** (FREEZE-3): `w12_checks.py` md5 `7dc040d94fbbb1e8d20ac817b665d418` reproduces exactly.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-7`, count 10 (the convention seam). `verification/openmath/w12_checks.py` — artifact EXISTS, md5 matches.

---

### EFF.HEX3.04  [definition]

**CANONICAL STATEMENT** (verbatim, S0 L73–77 and S1 L120–121). FORM: bracketed rider (S0) restated as an inline definition (S1).

> “**U₃^conv(q, N)** := the CONSERVATIVE-CONVENTION residue — the
> members the disclosed w12 TRP reader exits UNDECIDED (tail rule: any
> read state with v(B₀) ≥ N exits UNDECIDED, no tail σ-certification).
> This is what the w12 battery measured and reported, and what its
> bonus fact (characteristic-independence) is about.”

and, at S1:

> “U₃^conv(q, N) := #{TRP members the conservative
> reader exits UNDECIDED}.”

**DERIVATION.** [DEFINITIONAL].

**RESOLUTION TRACE.** statement lines 73–77 and 120–121; proof lines — (none); correction sites — (none).

**CONDITIONALITY.** Unconditional given `EFF.HEX3.03`. This is the *whole-space* count (`U₃^conv = q · u`, `EFF.HEX3.08`), not the per-centre one.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-7`, count 10.

---

### EFF.HEX3.05  [definition]

**CANONICAL STATEMENT** (verbatim, S0 L70–72). FORM: bracketed rider (bulleted definition).

> “**U₃^σ(q, N)** := the σ-undecided TRP mass — the quantity in THEOREM
> W-12.C's identity (members of the triple-repeated-root level-0
> stratum admitting two disc ≠ 0 lifts of different splitting type).”

**DERIVATION.** [DEFINITIONAL] — imported from the supplier's identity. The note's framing sentence for the pair, L67–68, is the reason both definitions are emitted separately: “**The two quantities, kept razor-separate throughout** (the W12-BOX-7 convention seam)”.

**RESOLUTION TRACE.** statement lines 70–72; proof lines — (none); correction sites 453–462 (the `[r4]` bracket rebinds “ambiguity” to this member-level notion).

**CONDITIONALITY.** Conditional on THEOREM W-12.C's identity being read at the post-r3 σ-pin. The `[r4]` bracket at `EFF.HEX3.06` makes the member-level reading explicit: “a member admits TWO disc ≠ 0 lifts of distinct σ; a single lift carries one σ”.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.C`, count 8; `W12-BOX-7`, count 10.

---

### EFF.HEX3.06  [lemma]

**CANONICAL STATEMENT** (verbatim, S0 L79–93, the `[r4]`-corrected form). FORM: display sentence with an embedded bracketed rider.

> “Every conservative-DECIDED member is σ-decided (its read terminates
> with all consulted data in-window and separable residuals: Ore applies
> to every disc ≠ 0 lift — W-12 S2.3, post-[r4] form), so **U₃^σ ≤
> U₃^conv always** **[r4, PE5 m1: the sealed clause read "every lift" —
> the over-claim W-12's own r4 struck from S2.3 with a counter-instance
> (equal characteristic 3: an in-window TRP-RAM3(h) member, 3 ∤ h, with
> b₁ = b₂ = 0 admits the lift F = y³ + b₀, F′ ≡ 0, so disc = 0 and no σ
> at all). The inequality stands at the pinned notion: U₃^σ (first
> bullet above) counts members with two disc ≠ 0 lifts of different σ,
> and post-r4 S2.3 pins one σ across a decided member's disc ≠ 0 lifts
> from its read data alone, so no conservative-DECIDED member enters
> U₃^σ — the disc = 0 lifts of the counter-instance member carry no σ
> and cannot witness membership. W-12 r4's m2 sweep (W12_PROOF L1768)
> dispositions this site "conclusion UNAFFECTED"; no number and no box
> moves]**”

**DERIVATION** (verbatim, the bracket's own argument, L86–91):

> “U₃^σ (first
> bullet above) counts members with two disc ≠ 0 lifts of different σ,
> and post-r4 S2.3 pins one σ across a decided member's disc ≠ 0 lifts
> from its read data alone, so no conservative-DECIDED member enters
> U₃^σ”

i.e. the contrapositive: conservative-DECIDED ⟹ σ-pinned ⟹ not in `U₃^σ`, hence `U₃^σ ⊆ U₃^conv` as sets and the inequality follows by cardinality.

**SUPERSESSION KIND:** `replacement` (the “every lift” warrant clause is replaced by the pinned-notion warrant). **TARGETS:** the S0 warrant clause at L81 only; the inequality itself does not move.

**RESOLUTION TRACE.** statement lines 79–82; proof lines 82–93 (the `[r4]` bracket carries the whole argument); correction sites 82–93 (the same bracket) and `W12_PROOF_2026-08-08.md` L1768 (the supplier's own disposition).

**CONDITIONALITY.** Conditional on W-12 §S2.3 **in its post-r4 form**. This is an inbound supplier correction (header §C item 1) and the note is explicit that the pre-r4 warrant was an over-claim struck by the supplier itself. The counter-instance is quoted rather than re-derived here; a compiler may not re-derive a quoted counter-instance into a claim of its own.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.3`, count 35 (a section anchor; the referent is W-12's §S2.3 Ore-warrant paragraph, the target the note names). `W12_PROOF_2026-08-08.md` L1768 — line-addressed, verified to exist (file has 2,462 lines).

---

### EFF.HEX3.07  [imported]

**CANONICAL STATEMENT** (verbatim, S0 L93–94). FORM: inline sentence (clause).

> “and LEMMA
> W12-S3.2's constructed species gives q^N ≤ U₃^σ.”

**DERIVATION.** [IMPORTED] — the lower bound is the supplier's constructed species, not re-derived here. The species is described at BOX-1 L449–459 as “b₁ = b₀ = 0 with b₂ FREE (q centers × q^{N−1} free b₂)”. **Arithmetic audit:** `q · q^{N−1} = q^N` ✓ — the lower bound is exactly the cardinality of that species.

**RESOLUTION TRACE.** statement lines 93–94; proof lines 449–462 (BOX-1's `[r4]` restatement of the species); correction sites 453–462.

**CONDITIONALITY.** Conditional on LEMMA W12-S3.2 at its pins (S9 L713–719). The `[r4]` bracket fences the four consuming sites: “The consuming sites of the q^N lower bound (S0 at LEMMA W12-S3.2's cite, the S1 display, this box's own bracket, the S8.1 annex bracket) each carry W12-S3.2's statement form, not this parenthetical”.

**XREF.** `W12_PROOF_2026-08-08.md` — `LEMMA W12-S3.2`, count 6; `W12-S3.2`, count 7.

---

### EFF.HEX3.08  [theorem]

**CANONICAL STATEMENT** (verbatim, S1 L123–142). FORM: display (blockquoted theorem with indented law displays).

> “**THEOREM HEX3.A (the exact conservative-residue law).** For every
> prime power q, both characteristics, every N ≥ 1:
>
>     U₃^conv(q, N) = q · u(q, N),
>
>     u(q, N) = q^{2N−2}
>             + (q−1) · Σ_{k=1}^{⌊(N−1)/3⌋} q^{4k−1} · (q^{N−3k} − 1) · R(N−3k),
>
>     R(M) = q^{M−1} + ⌊(M−1)/2⌋ · (q−1) · q^{M−2}   (R(1) = 1),
>
> a polynomial in q for each N, independent of the characteristic and
> of which DVR realizes F_q. Equivalently (the first-step form, proved
> first and telescoped): u(1) = 1 and for N ≥ 2
>
>     u(N) = q^{2N−2} + Σ_{k=1}^{⌊(N−1)/3⌋} (q−1) q^{3k} ·
>              [ u(N−3k) + (q^{N−3k} − 1)·R(N−3k) − q^{2(N−3k)−2} ],
>
> Moreover the undecided set decomposes by depth-0 species with each
> species' locus AND drained sub-count in closed form (the table of
> S5.1) — the per-key content the battery checks in both directions.”

**DERIVATION** (the proof chain, resolved): LEMMA H-1's exact depth-0 partition (`EFF.HEX3.13`) supplies the loci; LEMMA H-2 (`.22`–`.24`) and LEMMA H-3 (`.25`–`.29`) supply the per-species drained masses; LEMMA H-4 (`.30`) supplies `R(M)`; S5.1 (`.32`, `.33`) sums them into the first-step recursion; S5.2 (`.34`) telescopes the recursion into the direct sum. The note states the order explicitly at L40–44:

> “STAGE 2 proved it by the W-11 per-center method
> — the four depth-0 refine species transport onto scaled copies of the
> TRP system (α, self-similar) and of the W-11/W12-L1 double-root system
> (β, three entry routes), the drain masses assemble into a first-step
> recursion, and the recursion TELESCOPES into a direct closed sum.”

**Arithmetic audit (compiler-computed, independent of the note's own tables).** The two displayed forms were evaluated independently and agree at every point tested. `u(q,2) = q²`, `u(q,3) = q⁴`, `u(q,4) = q⁶ + (q−1)²q³` all follow from the telescoped form (the k-sum is empty for `N ≤ 3`; the single `k = 1` term at `N = 4` is `(q−1)q³(q−1)R(1) = (q−1)²q³`) ✓. At `q = 2, N = 7`: telescoped `4096 + 1440 + 128 = 5664`; first-step `4096 + 1504 + 64 = 5664` ✓ — both decompositions reproduce the note's anchor, including its `[r1]`-tagged warning that the two term-by-term splits differ.

**CONDITIONALITY.** The note's own hypothesis set, S9 L731–733: “THEOREM HEX3.A's hypothesis set = {W-11 @ pins, W12-L0/L1 + S2.4 @ pins, this note's transport lemmas}”. Grade at HEAD: **ACCEPTED 2/2** (`EFF.HEX3.64`) and ledger-**CERTIFIED** (`EFF.HEX3.71`); the frozen “attempt 0/2” vocabulary in the body is `STALE-SELF-DESCRIPTION`. The all-depth reach of the law is machine-confirmed only at realized keys — **Correction C** (`EFF.HEX3.67`).

**XREF.** `W11_PROOF_2026-08-08.md` — `THEOREM W-11`, count 3. `W12_PROOF_2026-08-08.md` — `LEMMA W12-L0`, count 5; `LEMMA W12-L1`, count 7; `S2.4`, count 10.

---

### EFF.HEX3.09  [theorem]

**CANONICAL STATEMENT** (verbatim, S1 L144–156). FORM: display (blockquoted theorem).

> “**THEOREM HEX3.B (the (hExhaust-3) vanishing bound).** For all q, N ≥ 2:
>
>     u(q, N) ≤ q^{2N−2} · (1 + N/(2(q+1))) ≤ N·q^{2N−2},
>
> hence q^N ≤ U₃^σ(q, N) ≤ U₃^conv(q, N) ≤ N·q^{2N−1}, and
>
>     undecided(3, q, N) / q^{3N} ≤ (1 + N)·q^{−N} → 0   (N → ∞),
>
> i.e. the n = 3 drainage hypothesis (A2)'s σ-undecided part vanishes:
> the (hExhaust-3) obstruction of THEOREM W-12.D at n = 3 — "a
> vanishing U₃^TRP upper bound" (W12-BOX-3) — is DISCHARGED. (The full
> (A2) at n = 3 also needs the menu (A1) to absorb the decided mass —
> that is (hMenu-3) = W12-BOX-2, untouched here; see S6.)”

**DERIVATION** — S5.3 (`EFF.HEX3.35`), reproduced there verbatim. **Arithmetic audit:** every step of S5.3 was re-derived independently at compile time and holds — the `R(M)` bound is equivalent to `M ≥ 1`; the k-term bound needs only `k ≥ 1`; the geometric sum `Σ_{k≥1} q^{−2k} = 1/(q²−1)` gives the `1/(2(q+1))` coefficient; `1 + N/(2(q+1)) ≤ N` for `N ≥ 2, q ≥ 2`; and `N·q^{2N−1} ≤ q^{3N−2} ⟺ N ≤ q^{N−1}` holds for all `q ≥ 2, N ≥ 1`. Details in §7.

**CONDITIONALITY.** S9 L732–733: “HEX3.B = {HEX3.A + W-12.C @ pin}”. The DISCHARGE claim is convention-free — it rides `U₃^σ ≤ U₃^conv` (`EFF.HEX3.06`), which is why the W12-side wrapper says so explicitly (header §B quote). **The discharge is NOT conditional on HEX3-BOX-1**: S8.2-2 L692–693, “the (hExhaust-3) discharge never needed the split”.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.D`, count 5; `W12-BOX-3`, count 7; `W12-BOX-2`, count 8; `(hExhaust-3)`, count 10; `(hMenu-3)`, count 9.

---

### EFF.HEX3.10  [corollary]

**CANONICAL STATEMENT** (verbatim, S1 L158–165). FORM: display (blockquoted corollary).

> “**COROLLARY HEX3.C (characteristic-independence, the w12 bonus fact
> explained).** U₃^conv(q, N) is the same integer over ℤ_p-type and
> F_q[[t]]-type O at every (q, N): the law's data is (q, N) only. The
> proof mechanism is J-D0's: every step of the derivation is a pinned-
> digit locus count whose pins are universal polynomial identities in
> residual letters (valid verbatim in char 2 and 3, where 2z or 3z
> degenerate), and every transport is a digit bijection available in
> both ring types; carries (mixed characteristic) never enter counts.”

**DERIVATION** — S5.4 (`EFF.HEX3.36`), whose closing sentence is superseded by Correction F (`EFF.HEX3.70`).

**CONDITIONALITY.** S9 L733: “HEX3.C = {HEX3.A's proof, inspected}” — i.e. conditional on the *proof*, not merely the statement, of HEX3.A. J-D0 is corroborative only (N-6). Correction F pins what the corollary needs: “COROLLARY HEX3.C requires only dependence on (q,N), not joint polynomiality, so its conclusion is unaffected.”

**XREF.** `JD0_PROOF_2026-08-08.md` — `LEMMA J-D0`, count 4; `J-D0`, count 25.

---

### EFF.HEX3.11  [record]

**CANONICAL STATEMENT** (verbatim, S1 L167–169). FORM: bold-headed paragraph inside the theorem blockquote.

> “**GRADE: HEX3.A/B/C composed at attempt 0/2, machine-sealed on 46
> rows both characteristics. The σ-residue U₃^σ itself: bracketed, not
> exactly known (HEX3-BOX-1).**”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** `STALE-SELF-DESCRIPTION` (rule 26) on the grade half only. The counter is **2/2 ACCEPTED** at `EFF.HEX3.64` and the ledger row is **CERTIFIED** at `EFF.HEX3.71`; no append edits this sentence, so it remains physically present and physically wrong. The second half — `U₃^σ` bracketed, not exactly known — is **current and correct** at HEAD.

**XREF.** none.

---

### EFF.HEX3.12  [record]

**CANONICAL STATEMENT** (verbatim, S1 L171–186, `[r1]`- and `[r2]`-corrected). FORM: bold-headed paragraph.

> “Numerical anchors (per center; whole space = ×q): u(q,2) = q²,
> u(q,3) = q⁴ (the k-sum is empty — the w12 N ≤ 3 columns q³, q⁵ whole-
> space); u(q,4) = q⁶ + (q−1)²q³ (= 72, 837 at q = 2, 3 — the first
> window where the depth-0 refine species drain); u(2,7) = 5664 =
> 2^{12} + 1504 + 64 (k = 1 and k = 2 terms both alive; FIRST-STEP-form
> k-terms — 8·[u(4) + 15·R(4) − 2⁶] = 1504, 64·[u(1) + R(1) − 1] = 64;
> the TELESCOPED display's k-terms are 1440 + 128, same total) [r1,
> PE1 m1: form tag added — the anchor sits directly under the
> telescoped display but decomposes by the first-step form, so an
> untagged term-by-term check against the telescoped law would
> spuriously mismatch; both decompositions re-verified to 5664]. The committed
> w12 table (23 rows) matches the law at every entry — disclosed: the
> law was FITTED on that committed table plus prototype rows and then
> derived; the battery's force is the ~~11~~ **twelve [r2, PE2 F1]**
> never-measured (q, N) pairs
> of §S7 P-1's corrected census plus the species tables.”

**DERIVATION.** [RECORD] with an embedded fit disclosure. The disclosure is load-bearing for how the battery's evidential weight may be cited and is repeated at S7 L538–543.

**SUPERSESSION KIND:** `counter re-reading` (the `[r2]` bracket re-reads “11” as “twelve”). **TARGETS:** `EFF.HEX3.45` (the P-1 census), which is where the corrected set is enumerated.

**Arithmetic audit.** `u(2,4) = 72`, `u(3,4) = 837`, `u(2,7) = 5664` all reproduce ✓; both k-term decompositions reproduce (`1504 + 64` first-step, `1440 + 128` telescoped) ✓; `u(q,2) = q²` and `u(q,3) = q⁴` follow from the empty k-sum, and the “w12 N ≤ 3 columns q³, q⁵ whole-space” are `q · q²` and `q · q⁴` ✓.

**CONDITIONALITY.** The FITTED-then-derived disclosure conditions how the committed-table agreement may be cited: it is **not** independent confirmation. The independent force is the twelve never-measured pairs plus the per-key species checks.

**XREF.** none external.

---

### EFF.HEX3.13  [lemma]

**CANONICAL STATEMENT** (verbatim, S2 L188–235 — LEMMA H-1, the exact depth-0 partition, with all six species and their loci). FORM: bold-headed paragraph plus a six-item bulleted display.

> “Fix a center; the state is (B₂, B₁, B₀) ∈ (πO/π^N)³ (q^{3(N−1)}
> states). The first read computes the lower hull of {(0, v(B₀)),
> (1, v(B₁)), (2, v(B₂)), (3, 0)} and the residual per side. By W-12
> S2.4's depth-0 completeness (every exact visible polygon falls in
> exactly one family; residual-type trichotomy per side: separable /
> repeated degree-1 root / —, with e ≥ 2 sides carrying g = 1 residuals
> that never repeat at n = 3), the state space partitions EXACTLY as:
>
> * **(B0ZERO)** v(B₀) ≥ N (B₀ = 0): the reader exits UNDECIDED at once.
>   Locus: q^{2(N−1)} (B₁, B₂ free). All drained.
> * **(DEC)** the seven decided families (RAM3, 3LIN, LINRAM2, RAM2LIN,
>   VERT1/VERT2 with separable quadratic residual, FULL with separable
>   cubic residual): decided at the first read, never drained.
> * **(α) = FULL(k)-⟨1³⟩**, 1 ≤ k, 3k ≤ N−1: v(B₀) = 3k exactly,
>   v(B₁) ≥ 2k, v(B₂) ≥ k, and the g = 3 residual (c₂, c₁, c₀) =
>   (digit_k(B₂), digit_{2k}(B₁), digit_{3k}(B₀)) equals the coefficient
>   triple of (y−z)³ for some z ∈ F_q^× (q−1 letters; z ≠ 0 forced by
>   c₀ = −z³ ≠ 0; the pins are (−3z, 3z², −z³) — in char 3 they
>   degenerate to (0, 0, −z³), still ONE pinned triple per letter).
>   Locus: (q−1)·q^{3N−3−6k} (three pinned digits, all deeper digits
>   free: q^{(N−1−k)+(N−1−2k)+(N−1−3k)}).
> * **(β1) = FULL(k)-⟨1²,1⟩**: same frame, residual (y−z)²(y−z′) with
>   z ≠ z′, both ≠ 0 (c₀ = −z²z′ ≠ 0): (q−1)(q−2) letters. Locus:
>   (q−1)(q−2)·q^{3N−3−6k}.
> * **(β2) = VERT1(u₀,k)-⟨1²⟩**, 1 ≤ k, 3k < u₀ ≤ N−1: polygon vertex at
>   (1, 2k) (digit_{2k}(B₁) ≠ 0), v(B₀) = u₀ exactly with free nonzero
>   digit (q−1 letters), v(B₂) ≥ k, right-side monic residual
>   y² + digit_k(B₂)·y + digit_{2k}(B₁) = (y−z)², z ∈ F_q^× (q−1
>   letters; pins digit_k(B₂) = −2z, digit_{2k}(B₁) = z² — injective in
>   z in every characteristic: −2z in odd char, z² Frobenius in char 2).
>   Locus: (q−1)²·q^{3N−3−u₀−3k}.
> * **(β3) = VERT2(u₀,t)-⟨1²⟩**, 1 ≤ t, u₀ > 3t, u₀ ≡ t (mod 2),
>   u₀ ≤ N−1, j := (u₀−3t)/2 ≥ 1: vertex at (2, t) with unit lead
>   λ = digit_t(B₂) (q−1 letters), v(B₀) = u₀ exactly, left side slope
>   k := t + j = (u₀−t)/2 [r1, PE1 m1 (typography): the sealed line
>   garbled the equality; content unchanged], interior lattice point
>   (1, (u₀+t)/2);
>   residual (y−z)², z ∈ F_q^× (q−1 letters; pins digit_{(u₀+t)/2}(B₁) =
>   −2zλ, digit_{u₀}(B₀) = z²λ ≠ 0 — the B₀-digit is DETERMINED, not a
>   letter). Locus: (q−1)²·q^{3N−3−u₀−t−(u₀+t)/2}.”

**DERIVATION.** [IMPORTED + slot count]. The partition's exactness is imported: “By W-12 S2.4's depth-0 completeness (every exact visible polygon falls in exactly one family; residual-type trichotomy per side…)”. Each species' *locus* is then a pinned-digit slot count, the note's standing method, stated at L232–233: “Every letter/pin count above is a digit-slot count (W-10's cell template)”.

**Arithmetic audit of the loci (compiler-recomputed).** (α): three digits pinned at heights `k, 2k, 3k`; free deeper digits number `(N−1−k) + (N−1−2k) + (N−1−3k) = 3N−3−6k` ✓, times `q−1` letters ✓. (β1): same frame, letters `(q−1)(q−2)` ✓. (β2): pins at `digit_k(B₂)`, `digit_{2k}(B₁)`, and `v(B₀) = u₀` with a free nonzero digit — free digits `3N−3−u₀−3k`, letters `(q−1)²` ✓. (β3): pins at heights `t` (λ, a letter), `(u₀+t)/2` (B₁, determined), `u₀` (B₀, determined) — free digits `3N−3−u₀−t−(u₀+t)/2`, letters `(q−1)²` (λ and z) ✓. Every locus in S5.1's table matches these ✓, and all fourteen preregistered P-2 spot values were recomputed from these formulas and hit exactly (§7).

**RESOLUTION TRACE.** statement lines 188–229; proof lines 232–235 (the slot-count warrant and the machine check); correction sites 223–225 (the `[r1]` typography repair on β3's slope equality).

**CONDITIONALITY.** Conditional on **W-12 §S2.4's depth-0 completeness**, at pin. **Correction C** (`EFF.HEX3.67`) is materially about this unit: the sealed roster (`N ≤ 9`) instantiates no key with `α(3)`, `β₂(k=3)` or `β₃(t=3)`, so H-1's ranges are machine-exercised only up to those depths.

**XREF.** `W12_PROOF_2026-08-08.md` — `S2.4`, count 10. `W10` cell template: `W10_PROOF_2026-08-08.md` exists; designation `W-10`, count 30 in `W12_PROOF_2026-08-08.md` (the note cites the template descriptively, not by a numbered designation — carried descriptively, no invented name).

---

### EFF.HEX3.14  [convention]

**CANONICAL STATEMENT** (verbatim, S3 L239–241). FORM: inline sentence.

> “Throughout, "drains" = the conservative chain from the state reaches a
> state with B₀ = 0; the chain recenters by s = ẑπ^m at each repeated
> residual root (depths strictly increase).”

**DERIVATION.** [DEFINITIONAL].

**RESOLUTION TRACE.** statement lines 239–241; proof lines — (none); correction sites — (none).

**CONDITIONALITY.** Unconditional. The strict depth increase is load-bearing for H-2(i)'s ghost-zone argument (`EFF.HEX3.22`).

**XREF.** none.

---

### EFF.HEX3.15  [definition]

**CANONICAL STATEMENT** (verbatim, S3.1 L245–247). FORM: display (definition line).

> “Let D_k := {v(B₂) ≥ k+1, v(B₁) ≥ 2k+1, v(B₀) ≥ 3k+1} (the post-α node)
> and let σ_k(B₂, B₁, B₀) = (B₂/π^k, B₁/π^{2k}, B₀/π^{3k}) taken mod
> π^{N−3k} per coordinate — a depth-0 state of the window-(N−3k) system.”

**DERIVATION.** [DEFINITIONAL].

**CONDITIONALITY.** Well-definedness of `σ_k` on `D_k` uses exactly the valuation floors in `D_k` (exact division); H-2(ii) records this as “v(B₀) ≥ N ⟺ v(B̃₀) ≥ N−3k (exact division)”.

**XREF.** none.

---

### EFF.HEX3.16  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.1 L250–251, LEMMA H-2(i)). FORM: bracketed-headed clause.

> “(i) **[window coherence]** the drain verdict of X ∈ D_k depends only on
> (B₂ mod π^{N−2k}, B₁ mod π^{N−k}, B₀).”

**DERIVATION** (verbatim, L251–275, with the `[r1]` F1 repair applied in place):

> “*Proof.* Along any chain from
> D_k every recentering has v(s) ≥ k+1. Reads: the hull heights at
> abscissa j are ≤ (3−j)/3·(N−1) (convexity from (0, u₀ ≤ N−1) to
> (3,0)), and (3−j)(N−1)/3 < N−jk for k ≤ (N−1)/3 — the ghost zone at
> abscissa j is {≥ N−jk} (the retained windows pair as B₂ = abscissa
> 2 ↔ {≥ N−2k}, B₁ = abscissa 1 ↔ {≥ N−k}); at j = 2 the inequality
> ⟺ k < (2N+1)/6, true since k ≤ (2N−2)/6; at j = 1 it ⟺ k < (N+2)/3,
> true since k ≤ (N−1)/3 — so consulted digits sit strictly below the
> ghost zones {≥ N−2k} (B₂), {≥ N−k} (B₁). [r1, PE1 F1 (justification
> gap): the sealed display paired the thresholds BACKWARDS —
> "(3−j)(N−1)/3 < N−(3−j)k" — which is FALSE at j = 1 for N ≥ 4 at the
> k = ⌊(N−1)/3⌋ corner (N = 7, k = 2: it reads 4 < 3), exactly the
> corner BOX-2(c) told a hostile pass to attack; with the corrected
> pairing N−jk the inequality holds on the whole range, re-checked at
> (N,k) = (7,2): j = 1 gives 4 < 5, j = 2 gives 2 < 3. The conclusion
> (window coherence, hence H-2(ii)/(iii) and the α-term
> (q−1)q^{3k}u(N−3k)) survives: PE1 re-derived (i) with the corrected
> pairing, and the α route is machine-tied per key at the ALPHA(2)
> corner rows (2,7)/(2,8)/(2,9), all exact.] Updates: shift3 needs B₁
> mod π^{N−v(s)} ⊆ mod π^{N−k−1} and B₂
> mod π^{N−2v(s)} ⊆ mod π^{N−2k−2} to determine B₀′ mod π^N; B₂ mod
> π^{N−2k−1} to determine B₁′ mod π^{N−k}; B₂′ = B₂ + 3s preserves the
> B₂-window. All ring operations respect the quotient maps (O/π^N →
> O/π^m is a ring hom), so the ghost digits never contaminate the
> consulted windows, in both ring types (carries move upward only). ∎”

**SUPERSESSION KIND:** `replacement` (a false inequality display replaced by a true one). **TARGETS:** the S3.1 threshold display at L253–254 only.

**Arithmetic audit of the repaired inequality.** Compiler-recomputed. `(3−j)(N−1)/3 < N − jk` for `1 ≤ k ≤ (N−1)/3`: at `j = 2`, `(N−1)/3 < N − 2k ⟺ 6k < 2N+1 ⟺ k < (2N+1)/6`, and `k ≤ (N−1)/3 = (2N−2)/6 < (2N+1)/6` ✓; at `j = 1`, `2(N−1)/3 < N − k ⟺ 3k < N+2 ⟺ k < (N+2)/3`, and `k ≤ (N−1)/3 < (N+2)/3` ✓. At the named corner `(N,k) = (7,2)`: `j = 1` gives `4 < 5` ✓, `j = 2` gives `2 < 3` ✓. The struck pairing `N−(3−j)k` at `(7,2), j = 1` gives `4 < 7 − 4 = 3`, **false** ✓ — the note's diagnosis of its own defect is correct.

**RESOLUTION TRACE.** statement line 250–251; proof lines 251–275; correction sites 259–269 (the `[r1]` bracket, physically inside the proof).

**CONDITIONALITY.** Holds for `k ≤ (N−1)/3`, which is exactly the α-range of H-1. Outside that range the argument is not claimed.

**XREF.** none external (the BOX-2(c) reference is note-internal, `EFF.HEX3.38`).

---

### EFF.HEX3.17  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.1 L277–285, LEMMA H-2(ii)). FORM: bracketed-headed clause with its proof inline.

> “(ii) **[shear correspondence]** the chain of X and the chain of
> σ_k(X) (window N−3k) correspond step for step: heights shear by
> (j, v) ↦ (j, v−(3−j)k), an affine-in-j map preserving lower hulls,
> lattice points, side subdivisions and residual coefficient positions;
> f(π^k(y+s̃))= π^{3k}·f̃(y+s̃) makes recentering commute with σ_k
> (s = π^k s̃); and v(B₀) ≥ N ⟺ v(B̃₀) ≥ N−3k (exact division).
> Hence **drain(X) ⟺ drain_{N−3k}(σ_k(X))**, and with (i): the D_k
> drain count = q^{3k} · u(N−3k) (each scaled state has exactly q^{3k}
> ghost-fiber preimages: 2k free B₂-digits + k free B₁-digits). ∎”

**DERIVATION.** The statement and proof are one span; the three warrants are (a) the shear is affine in `j` hence hull-preserving, (b) the recentering identity `f(π^k(y+s̃)) = π^{3k}·f̃(y+s̃)`, (c) exact division for the `B₀ = 0` exit condition. The count then follows from (i)'s coherence plus the ghost-fiber size.

**Arithmetic audit.** Ghost fiber `= q^{2k} · q^{k} = q^{3k}` — “2k free B₂-digits + k free B₁-digits” ✓, consistent with (i)'s retained windows `B₂ mod π^{N−2k}` (so `2k` ghost digits) and `B₁ mod π^{N−k}` (so `k` ghost digits) ✓. The two clauses are mutually consistent, which is the check that matters here.

**RESOLUTION TRACE.** statement lines 277–283; proof lines 277–285 (same span); correction sites — (none).

**CONDITIONALITY.** Conditional on (i) (`EFF.HEX3.16`), hence on `k ≤ (N−1)/3`.

**XREF.** none.

---

### EFF.HEX3.18  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.1 L287–297, LEMMA H-2(iii)). FORM: bracketed-headed clause with proof inline.

> “(iii) **[the α-map is onto]** recentering by ẑπ^k maps the (α)
> z-slice into D_k: the three pinned digits cancel —
> digit_k(B₂+3ẑπ^k) = c₂+3z = 0, digit_{2k}(B₁′) = c₁+2c₂z+3z² = 0,
> digit_{3k}(B₀′) = c₀+c₁z+c₂z²+z³ = 0, universal identities from
> (y−z)³ valid in every characteristic — and it is injective (a shift)
> with #slice = q^{3N−3−6k} = #D_k: a bijection. (Deep ramified
> configurations — cluster pairs at half-integer valuations — are in the
> image: their preimages have all three residual roots equal, i.e. ARE
> ⟨1³⟩ states; the polygon of a D_k state automatically lies above the
> slope-k shear line, so no case is missed.) Hence the (α)-species drain
> contribution at depth k is **(q−1) · q^{3k} · u(N−3k)**. ∎”

**DERIVATION.** As quoted: cancellation of the three pinned digits under the shift, injectivity (a shift is injective), and a cardinality match forcing surjectivity, with the parenthetical closing the “are the deep ramified configurations in the image?” objection.

**Arithmetic audit.** `#D_k`: the constraints `v(B₂) ≥ k+1`, `v(B₁) ≥ 2k+1`, `v(B₀) ≥ 3k+1` leave `(N−1−k) + (N−1−2k) + (N−1−3k) = 3N−3−6k` free digits, so `#D_k = q^{3N−3−6k}` ✓, matching the `z`-slice size at fixed `z` from H-1's (α) locus `(q−1)q^{3N−3−6k}` divided by the `q−1` letters ✓. The contribution `(q−1)·q^{3k}·u(N−3k)` is then `(q−1)` letters times (ii)'s `D_k` drain count ✓. Consistent, and it matches S5.1's ALPHA row exactly ✓.

**RESOLUTION TRACE.** statement lines 287–296; proof lines 287–297 (same span); correction sites — (none). The arc record notes this route was re-derived from scratch at PE4 (`EFF.HEX3.63`).

**CONDITIONALITY.** Conditional on (i) and (ii). The onto-ness claim is one of the three attack surfaces BOX-2 names (`EFF.HEX3.38`) and the note records that PE1 attacked it and it “survived full re-derivation”.

**XREF.** none.

---

### EFF.HEX3.19  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.2 L299–316, the LEMMA H-3 frame). FORM: bold-headed paragraph.

> “After a (β)-refinement the read continues on the full cubic whose
> polygon shows a split-off simple root plus a double cluster; the drain
> tracks the cluster: writing the post-state as (block)·(x − r) with the
> current center inside the cluster, B₀-at-center = (block value at
> center)·(center − r), and v(center − r) is CONSTANT along the rest of
> the chain (all deeper recenterings are deeper than the separation
> depth), so B₀ = 0 ⟺ the block's constant coefficient A₀ reaches 0 at
> the corresponding fixed window. Concretely, scaling by π^m (m = the
> final valuation of the split root's coordinate; window coherence as in
> H-2(i) with the same v(s) ≥ m+1 bound along β-chains) turns the
> post-state into a LEVEL-0 double-root member of the window-(N−3m)
> system, where LEMMA W12-L1(a)(b) (consumed at pin: the Hensel product
> bijection + the read equivalence, both machine-checked pointwise on
> 2.9M lifts by the sealed w12 battery) identifies the continuing read
> with the W-11 block read and the drain event with the block chain
> reaching A₀ = 0 in window M := N−3m.”

**DERIVATION.** As quoted: the factorization `(block)·(x − r)`, constancy of `v(center − r)`, the reduction of the drain event to `A₀ = 0`, then the scaling and the W12-L1 identification.

**RESOLUTION TRACE.** statement lines 299–316; proof lines 299–316 (same span); correction sites — (none).

**CONDITIONALITY.** Conditional on **LEMMA W12-L1(a)(b) at pin**, and on window coherence transported to β-chains (“as in H-2(i) with the same v(s) ≥ m+1 bound”) — the note asserts the transport rather than re-proving H-2(i) in the β setting. Recorded as a justification seam, not a defect: the note's own BOX-2 names the `m`-choice as attack surface (b), and reports PE1 attacked it and it survived.

**XREF.** `W12_PROOF_2026-08-08.md` — `LEMMA W12-L1`, count 7; `W12-L1(a)`, count 1. `W11_PROOF_2026-08-08.md` — `THEOREM W-11`, count 3.

---

### EFF.HEX3.20  [definition]

**CANONICAL STATEMENT** (verbatim, S3.2 L316–319). FORM: display (indented definition).

> “Define
>
>     R(M) := #{block states (A₁, A₀) ∈ (πO/π^M)² whose W-11 chain
>              reaches A₀ = 0}.”

**DERIVATION.** [DEFINITIONAL].

**CONDITIONALITY.** Unconditional as a definition; its closed form is `EFF.HEX3.30`.

**XREF.** none.

---

### EFF.HEX3.21  [convention]

**CANONICAL STATEMENT** (verbatim, S3.2 L321–324). FORM: bracketed rider (parenthetical governing all three β-routes).

> “Route by route (each map injective by construction — recenter, then
> σ_m — with image and fibers counted by pinned-digit slots exactly as
> in S2; the refine isomorphism "z-slice ↦ ONTO the post node" is W-11
> S2.3 consumed through W12-L0's induction step):”

**DERIVATION.** [DEFINITIONAL / method statement]. This is the shared warrant for `EFF.HEX3.22`–`.24` and must not be read as part of any one of them.

**CONDITIONALITY.** Conditional on **W-11 §S2.3 as consumed through W12-L0's induction step** — a two-hop citation, recorded as such.

**XREF.** `W11_PROOF_2026-08-08.md` — `S2.3`, count 8. `W12_PROOF_2026-08-08.md` — `W12-L0`, count 32.

---

### EFF.HEX3.22  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.2 L326–332, the β1 route). FORM: bulleted display.

> “* **(β1) FULL(k)-⟨1²,1⟩, m = k** (the split root z′ lands at exact
>   depth k after recentering: digit z′−z ≠ 0): the (z, z′)-slice maps
>   ONTO the scaled DBL pattern-slice (cluster at 0, unit root pinned to
>   z′−z, deeper root digits FREE: q^{M−1}; blocks free: q^{2(M−1)};
>   ghost fiber q^{3k}) — cardinalities match (q^{3M−3}·q^{3k} =
>   q^{3N−3−6k}). Drained: blocks reaching A₀ = 0 with r free:
>   **contribution (q−1)(q−2) · q^{3k} · q^{M−1} · R(M)**.”

**DERIVATION.** As quoted: an onto map with a cardinality match, then the drained count as (free root digits) × (block drains) × (ghost fiber) × letters.

**Arithmetic audit.** `M = N − 3k`, so `q^{3M−3}·q^{3k} = q^{3N−9k−3+3k} = q^{3N−3−6k}` ✓ — the cardinality match is exact. The contribution `(q−1)(q−2)·q^{3k}·q^{M−1}·R(M)` matches S5.1's FULL11SQ drained column `(q−1)(q−2)q^{3k+M−1}R(M)` ✓. At `q = 2` the factor `(q−2) = 0`, which is exactly the note's preregistered “FULL11SQ ABSENT (exact zero at q = 2)” ✓.

**RESOLUTION TRACE.** statement lines 326–332; proof lines 321–324 (the shared route warrant) and 326–332; correction sites — (none). The arc records this route was “re-derived in full + letter-resolution fibers machine-checked” at PE3 (`EFF.HEX3.63`).

**CONDITIONALITY.** Conditional on `EFF.HEX3.19` and `.21`.

**XREF.** none beyond `.21`'s.

---

### EFF.HEX3.23  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.2 L333–338, the β2 route). FORM: bulleted display.

> “* **(β2) VERT1(u₀,k)-⟨1²⟩, m = k** (the split root has pre-depth
>   u₀−2k > k, post-recentering depth exactly k, and its deeper digits
>   remember u₀: v(r̃ + ẑ) = w := u₀−3k exactly, (q−1)q^{M−1−w} fibers —
>   the u₀-fibers tile the pattern-slice's non-degenerate r̃ range as u₀
>   runs over 3k+1..N−1): drained per (u₀, k): **(q−1)² · q^{3k} ·
>   q^{M−1−w} · R(M)**. (Summed over u₀: (q−1)·q^{3k}·R(M)·(q^{M−1}−1).)”

**DERIVATION.** As quoted: the fiber count `(q−1)q^{M−1−w}` with `w = u₀−3k`, the tiling claim over the `u₀`-range, and the summation.

**Arithmetic audit of the u₀-sum (compiler-recomputed).** `Σ_{u₀=3k+1}^{N−1} (q−1)²q^{3k}q^{M−1−(u₀−3k)}R(M)`; substituting `w = u₀−3k` running `1..M−1` (since `u₀ ≤ N−1 ⟺ w ≤ N−1−3k = M−1`) gives `(q−1)²q^{3k}R(M)·Σ_{w=1}^{M−1}q^{M−1−w} = (q−1)²q^{3k}R(M)·(q^{M−1}−1)/(q−1) = (q−1)q^{3k}R(M)(q^{M−1}−1)` ✓ — exactly the note's parenthetical.

**RESOLUTION TRACE.** statement lines 333–338; proof lines 321–324 and 333–338; correction sites — (none).

**CONDITIONALITY.** Conditional on `.19` and `.21`. The tiling claim (“the u₀-fibers tile the pattern-slice's non-degenerate r̃ range”) is BOX-2 attack surface (a); the note records PE1 attacked it and it “survived full re-derivation”.

**XREF.** none beyond `.21`'s.

---

### EFF.HEX3.24  [lemma]

**CANONICAL STATEMENT** (verbatim, S3.2 L339–346, the β3 route). FORM: bulleted display.

> “* **(β3) VERT2(u₀,t)-⟨1²⟩, m = t** (the split root sits at depth t
>   BELOW the cluster; scaling by π^t gives the standard DBL pattern
>   with the CLUSTER deep: the block enters at its refine locus of depth
>   j = (u₀−3t)/2, and the block z-slice maps onto the depth-j block
>   node, of drain count q^j·R(M−2j), M = N−3t): drained per (u₀, t):
>   **(q−1)² · q^{3t} · q^{M−1} · q^{j} · R(M−2j)**. (Summed over u₀ at
>   fixed t, via the R-recursion of S4: (q−1)·q^{3t}·q^{M−1}·(R(M) −
>   q^{M−1}).)”

**DERIVATION.** As quoted, with the u₀-summation performed “via the R-recursion of S4” (`EFF.HEX3.31`).

**Arithmetic audit of the u₀-sum (compiler-recomputed).** At fixed `t`, `u₀` runs over `u₀ > 3t`, `u₀ ≡ t (mod 2)`, `u₀ ≤ N−1`, i.e. `j = (u₀−3t)/2` runs `1, 2, …` with `2j ≤ M−1` (since `u₀ ≤ N−1 ⟺ 2j + 3t ≤ N−1 ⟺ 2j ≤ M−1`). Summing `(q−1)²q^{3t}q^{M−1}q^{j}R(M−2j)` over that range gives `(q−1)q^{3t}q^{M−1}·[(q−1)Σ_{j≥1,2j≤M−1}q^jR(M−2j)]`, and the S4 R-recursion says the bracket equals `R(M) − q^{M−1}` ✓ — exactly the note's parenthetical. The step is therefore not an independent claim: it is the R-recursion used in the direction `.31` supplies.

**RESOLUTION TRACE.** statement lines 339–346; proof lines 321–324, 339–346, and 366–370 (the R-recursion the sum consumes — a proof span 20+ lines from the statement, hence the three-slot trace); correction sites — (none).

**CONDITIONALITY.** Conditional on `.19`, `.21`, and `.31`.

**XREF.** none beyond `.21`'s.

---

### EFF.HEX3.25  [scope-record]

**CANONICAL STATEMENT** (verbatim, S3.2 L348–349). FORM: inline sentence.

> “Each bullet's drained count is checked EXACTLY per (u₀, k/t) key on
> every battery row (HEX3-SPECIES). ∎”

**DERIVATION.** [RECORD] — an instrument claim about `.22`–`.24`.

**CONDITIONALITY.** **Scoped by Correction C** (`EFF.HEX3.67`): the per-key check covers only keys realized on the `N ≤ 9` roster. Read with Correction C, this sentence means “on every battery row, at every key that row realizes”.

**XREF.** none.

---

### EFF.HEX3.26  [lemma]

**CANONICAL STATEMENT** (verbatim, S4 L353–363, LEMMA H-4). FORM: display (indented three-line closed form) with prose warrant.

> “The W-11 chain reaches A₀ = 0 iff its exit is SPLIT-TAIL or UNDECIDED
> (those two exits have A₀ = 0 at the exit state, and a state with
> A₀ = 0 exits immediately; the other four exits have A₀ ≠ 0). By LEMMA
> W12-L0 (history-resolved laws, consumed at pin) summed over histories
> with the W-11 instance bracket Σ_{H: s ≤ w−1} (q−1)^t = q^{w−1}:
>
>     R(M) = q^{M−1}  [UNDECIDED aggregate, W-11 (iii)]
>          + Σ_{w=1}^{⌊(M−1)/2⌋} (q−1)q^{M−1−w} · q^{w−1}
>          = q^{M−1} + ⌊(M−1)/2⌋·(q−1)·q^{M−2},
>
> R(1) = 1 (the singleton zero state).”

**DERIVATION.** As quoted, plus the aggregate provenance at L363–365:

> “Both summands are W-11-proved
> aggregates (the tail law is W-11's Σ SPLIT-TAIL = ⌊(M−1)/2⌋(q−1)q^{M−2}
> per center, quoted in W-12 S3.4's r(N) display).”

**Arithmetic audit.** The summand `(q−1)q^{M−1−w}·q^{w−1} = (q−1)q^{M−2}` is independent of `w`, so the sum over `w = 1..⌊(M−1)/2⌋` is `⌊(M−1)/2⌋(q−1)q^{M−2}` ✓ — the collapse is exact and is what makes the closed form elementary. `R(1) = 1` ✓ (the formula would give `q^0 + 0 = 1` as well, so the seed is consistent rather than an exception).

**RESOLUTION TRACE.** statement lines 353–363; proof lines 353–365; correction sites — (none).

**CONDITIONALITY.** Conditional on **LEMMA W12-L0 at pin** and on the W-11 aggregates (clause (iii) and the SPLIT-TAIL law). NEAR-MISS on one designation: the note writes “W-11 (iii)”, and `grep -cF 'W-11 (iii)' W11_PROOF_2026-08-08.md` = **0**; the referent is W-11's clause (iii), verified present as `(iii)` (count 17 in `W11_PROOF_2026-08-08.md`) and cross-confirmed by the same aggregate being quoted in `W12_PROOF_2026-08-08.md` §S3.4 (`S3.4`, count 11). **NEAR-MISS disposition** per rule 15, not an OPEN-CALL: the designation is absent as written, the referent is verified, and the note itself supplies the second, independently verifiable route (W-12 S3.4's r(N) display).

**XREF.** `W12_PROOF_2026-08-08.md` — `LEMMA W12-L0`, count 5; `W12-L0`, count 32; `S3.4`, count 11. `W11_PROOF_2026-08-08.md` — `SPLIT-TAIL`, count 21.

---

### EFF.HEX3.27  [lemma]

**CANONICAL STATEMENT** (verbatim, S4 L366–370, the R-recursion). FORM: inline sentence with an embedded display.

> “The same R-recursion
> used in S3.2's (β3) bullet — R(M) = q^{M−1} + (q−1)Σ_{j≥1, 2j≤M−1}
> q^j·R(M−2j) — is the first-step form of the same count (refine at
> depth j: q−1 letters, node ≅ q^j × window-(M−2j) by the W-11 shear,
> the n = 2 instance of H-2), and evaluates to the same closed form by
> the identical bracket telescoping. ∎”

**DERIVATION.** As quoted: the recursion is the `n = 2` instance of the same shear argument H-2 supplies at `n = 3`.

**Arithmetic audit (compiler-recomputed, since `.24` consumes this identity).** Verify `q^{M−1} + (q−1)Σ_{j≥1,2j≤M−1}q^jR(M−2j) = R(M)` with `R` the closed form. Tested exhaustively for `q ∈ {2,3,4,5,7,8,9,11,13}` and `M = 1..20`: **identity holds in every case** (360 checks, 0 failures). The `.24` u₀-sum is therefore sound.

**RESOLUTION TRACE.** statement lines 366–370; proof lines 366–370 (asserted equivalence, verified numerically here); correction sites — (none).

**CONDITIONALITY.** The equivalence of the two forms is asserted (“evaluates to the same closed form by the identical bracket telescoping”) rather than displayed. Compiler-verified numerically over a wide grid, but the note supplies no general display; recorded as a justification seam of the source, discharged for the DAG by the S5.2 telescoping (`EFF.HEX3.34`), which is the same argument at `n = 3`.

**XREF.** none.

---

### EFF.HEX3.28  [table]

**CANONICAL STATEMENT** (verbatim, S5.1 L376–386 — the species table, reproduced as the source's own Markdown table). FORM: table.

> “Summing S2's partition with S3's per-species drain masses (per center;
> M = N−3k resp. N−3t; w = u₀−3k; j = (u₀−3t)/2):”

`[TABLE]` (source table, transcribed exactly)

| depth-0 species | locus | drained |
|---|---|---|
| B0ZERO | q^{2N−2} | q^{2N−2} (all) |
| DEC (7 families) | complement | 0 |
| ALPHA(k) | (q−1)q^{3N−3−6k} | (q−1)q^{3k}·u(N−3k) |
| FULL11SQ(k) | (q−1)(q−2)q^{3N−3−6k} | (q−1)(q−2)q^{3k+M−1}·R(M) |
| VERT1(u₀,k) | (q−1)²q^{3N−3−u₀−3k} | (q−1)²q^{3k+M−1−w}·R(M) |
| VERT2(u₀,t) | (q−1)²q^{3N−3−u₀−t−(u₀+t)/2} | (q−1)²q^{3t+M−1+j}·R(M−2j) |

**DERIVATION.** Row by row: B0ZERO from H-1's first bullet (locus) and its “All drained”; DEC from H-1's second bullet; ALPHA from H-1 (locus) + H-2(iii) (drained); FULL11SQ from H-1 + `.22`; VERT1 from H-1 + `.23`; VERT2 from H-1 + `.24`.

**Mandatory arithmetic audit (rule 22).** This is a table of closed forms, not of counts, so the audit is the cross-check against every number elsewhere in the note that it should generate. **All fourteen preregistered P-2 spot values were recomputed from these six rows alone** and every one hits: `(Zp,2,7)` ALPHA(1) `(4096, 576)`, ALPHA(2) `(64, 64)`, VERT1(4,1) `(2048, 384)`, VERT1(6,1) `(512, 96)`, VERT2(5,1) `(512, 256)`, FULL11SQ absent at `q = 2`; `(Zp,3,6)` FULL11SQ(1) `(39366, 7290)`, VERT2(5,1) `(2916, 2916)` fully drained (`M − 2j = 1`); `(Fqt,4,4)` ALPHA(1) `(192, 192)`, FULL11SQ(1) `(384, 384)`; `(Zp,2,9)` VERT1(8,2) `(1024, 384)`, VERT2(8,2) `(512, 512)`. Additionally the genre decomposition `B0ZERO + ALPHA-column + β-columns = u(N)` was verified as an exact integer identity at `q = 2` for `N = 16..19, 76, 77` ✓ — see the Correction B audit at §7.

**CONDITIONALITY.** Conditional on H-1, H-2, H-3 and hence on their conditionalities; scoped at depth by Correction C.

**XREF.** none.

---

### EFF.HEX3.29  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.1 L388–391). FORM: inline sentence with embedded display.

> “Summing the β-rows at fixed k (u₀-sums as in S3.2) and adding the α
> row: the k-indexed bracket is u(M) + (q−2)q^{M−1}R + R(q^{M−1}−1) +
> q^{M−1}R − q^{2M−2} = u(M) + (q^M−1)R(M) − q^{2M−2}, giving the
> first-step recursion of THEOREM HEX3.A. ∎”

**DERIVATION.** As quoted. The four summands are, in order, the α row, β1, the β2 u₀-sum, and the β3 u₀-sum (which supplies both `q^{M−1}R` and the `−q^{2M−2}`).

**Arithmetic audit (compiler-recomputed).** `u(M) + (q−2)q^{M−1}R + R(q^{M−1}−1) + q^{M−1}R − q^{2M−2}`; collecting the `R` terms: `R·[(q−2)q^{M−1} + q^{M−1} − 1 + q^{M−1}] = R·[q·q^{M−1} − 1] = R(q^M − 1)` ✓. The identity is exact, and it identifies the provenance of the `−q^{2M−2}` term as **β3's**, not a correction term — a point a chapter cut could otherwise mis-attribute.

**RESOLUTION TRACE.** statement lines 388–391; proof lines 326–346 (the three β sums, twenty-plus lines upstream) and 388–391; correction sites — (none).

**CONDITIONALITY.** Conditional on `.18`, `.22`, `.23`, `.24`, `.27`.

**XREF.** none.

---

### EFF.HEX3.30  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.2 L395–408 — the telescoping). FORM: bold-headed paragraph with an indented display and a bracketed generating-function rider.

> “Claim: the recursion's solution is the direct sum u(N) = q^{2N−2} +
> (q−1)Σ_k q^{4k−1}·t(N−3k), t(M) := (q^M−1)R(M). Induction on N:
> substituting the claim for the u(N−3k) inside the recursion, the
> coefficient of t(N−3l) on the right is
>
>     (q−1)q^{3l} + (q−1)² Σ_{k+j=l, k,j≥1} q^{3k}·q^{4j−1}
>       = (q−1)[ q^{3l} + q^{3l−1}(q^l − q)/(q−1)·(q−1) ]
>       = (q−1)[ q^{3l} + q^{3l−1}(q^l − q) ] = (q−1)·q^{4l−1},
>
> and the −q^{2M−2} terms cancel against the claim's own leading terms
> (q^{2(N−3k)−2} = the substituted u(N−3k)'s head). [Generating-function
> form, equivalent: U = S + A·(U + T − S) with A = Σ(q−1)q^{3k}x^{3k}
> gives U = S + T·A/(1−A) and A/(1−A) = (q−1)q³x³/(1−q⁴x³) — the
> denominator 1−A = (1−q⁴x³)/(1−q³x³) telescopes.] THEOREM HEX3.A. ∎”

**DERIVATION.** The span above is statement and proof together (an induction plus an equivalent generating-function route).

**Arithmetic audit (compiler-recomputed).** The coefficient identity: `Σ_{k+j=l, k,j≥1} q^{3k}q^{4j−1} = q^{4l−1}Σ_{k=1}^{l−1}q^{−k} = q^{4l−1}·(q^{−1})(1−q^{−(l−1)})/(1−q^{−1}) = q^{3l−1}(q^{l−1}−1)/(1−q^{−1})·q^{−(l−1)}…`; evaluated directly, `Σ_{k=1}^{l−1}q^{3k}q^{4(l−k)−1} = q^{4l−1}Σ_{k=1}^{l−1}q^{−k}` and `(q−1)²·that + (q−1)q^{3l}` was evaluated numerically for `q ∈ {2,3,5}` and `l = 1..8`: equals `(q−1)q^{4l−1}` in **all 24 cases** ✓. The generating-function identity `1 − Σ_{k≥1}(q−1)q^{3k}x^{3k} = 1 − (q−1)q³x³/(1−q³x³) = (1−q⁴x³)/(1−q³x³)` ✓ — exact. **And the top-level check:** the two displayed forms of `u` in THEOREM HEX3.A were evaluated independently and agree for `q ∈ {2,3,4,5,7,8,9,11,13,16,25,27}` and `N = 1..30` ✓.

**RESOLUTION TRACE.** statement lines 395–396; proof lines 396–408; correction sites — (none). PE2's fresh route independently proved the telescoping “for N ≤ 40” (arc record, `EFF.HEX3.63`) — a decorrelated confirmation of exactly this unit.

**CONDITIONALITY.** Conditional on `.29`.

**XREF.** none.

---

### EFF.HEX3.31  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.3 L412–419 — the proof of THEOREM HEX3.B). FORM: paragraph proof.

> “R(M) ≤ q^{M−1}(M+1)/2 (as 2q + (M−1)(q−1) ≤ q(M+1) ⟺ M ≥ 1), so the
> k-term is ≤ (q−1)(M+1)/2·q^{2N−2k−2} ≤ (q−1)(N−2)/2·q^{2N−2}·q^{−2k};
> summing the geometric series: u(N) ≤ q^{2N−2}(1 + (N−2)/(2(q+1))) ≤
> q^{2N−2}(1 + N/(2(q+1))) ≤ N·q^{2N−2} for N ≥ 2. With U₃^σ ≤ U₃^conv
> = q·u and THEOREM W-12.C: undecided(3,q,N) ≤ (q−1)q^{2N−1} + Nq^{2N−1}
> ≤ (1+N)q^{2N}, so undecided/q^{3N} ≤ (1+N)q^{−N} → 0. Both W-12.C
> brackets are respected (q^{2N−1} ≤ U₃^conv is the B0ZERO term alone;
> N·q^{2N−1} ≤ q^{3N−2} ⟺ N ≤ q^{N−1}, true for q ≥ 2). ∎”

**DERIVATION.** The span is the derivation.

**Arithmetic audit (every step recomputed).** (1) `R(M) ≤ q^{M−1}(M+1)/2 ⟺ 2q + (M−1)(q−1) ≤ q(M+1) ⟺ 1 − M ≤ 0 ⟺ M ≥ 1` ✓ — the note's stated equivalence is exact. (2) k-term `= (q−1)q^{4k−1}(q^{M}−1)R(M) ≤ (q−1)q^{4k−1}q^{M}·q^{M−1}(M+1)/2 = (q−1)(M+1)/2·q^{2N−2k−2}` ✓ (using `M = N−3k`). (3) `M + 1 = N−3k+1 ≤ N−2` for `k ≥ 1` ✓. (4) `Σ_{k≥1}q^{−2k} = 1/(q²−1)`, so the excess is `≤ (q−1)(N−2)/2 · 1/(q²−1) = (N−2)/(2(q+1))` ✓. (5) `1 + N/(2(q+1)) ≤ N ⟺ 2(q+1)(N−1) ≥ N`, true for `N ≥ 2, q ≥ 2` ✓. (6) `q^{2N−1} ≤ U₃^conv` is the whole-space B0ZERO term `q·q^{2N−2}` ✓. (7) `N ≤ q^{N−1}` for `q ≥ 2, N ≥ 1` ✓. **All seven steps sound.**

**RESOLUTION TRACE.** statement lines 144–156 (THEOREM HEX3.B, §S1 — 268 lines upstream); proof lines 412–419; correction sites — (none).

**CONDITIONALITY.** Conditional on `.30` (the exact law), `.06` (`U₃^σ ≤ U₃^conv`), and THEOREM W-12.C at pin. **Correction E** (`EFF.HEX3.69`) fences one thing this bound does NOT give: it is an upper bound only, so it cannot by itself prove the B0ZERO fraction vanishes.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.C`, count 8.

---

### EFF.HEX3.32  [lemma]

**CANONICAL STATEMENT** (verbatim, S5.4 L423–431). FORM: paragraph proof.

> “Every count in S2–S5 is a pinned-digit slot count; every pin is a
> universal polynomial identity in residual letters ((y−z)³, (y−z)²(y−z′)
> expansions — their degenerations at char 2, 3 change WHICH values are
> pinned, never HOW MANY); every transport (σ_k, recentering, W12-L1's
> product bijection) is a digit bijection available verbatim in both
> ring types; window coherence (H-2(i)) is a quotient-hom statement that
> holds with or without carries. So u(q, N) is one polynomial law in
> (q, N) — the w12 bonus fact is the shadow of J-D0's gauge-blindness at
> the drainage level. ∎”

**DERIVATION.** The span is the derivation: a three-part inspection of the proof of HEX3.A (pins, transports, coherence), each part characteristic-blind.

**SUPERSEDED (final sentence only).** The clause “So u(q, N) is one polynomial law in (q, N)” is superseded by **Correction F** (`EFF.HEX3.70`). **CHAIN:** sealed S5.4 sentence → Correction F. **TERMINAL: Correction F.** The rest of the paragraph — the three-part inspection — is untouched and current.

**RESOLUTION TRACE.** statement lines 158–165 (COROLLARY HEX3.C, §S1); proof lines 423–431; correction sites 1038–1042 (Correction F).

**CONDITIONALITY.** Conditional on the *proof* of HEX3.A (S9: “HEX3.C = {HEX3.A's proof, inspected}”). J-D0 corroborative only (N-6).

**XREF.** `JD0_PROOF_2026-08-08.md` — `J-D0`, count 25. `W12_PROOF_2026-08-08.md` — `LEMMA W12-L1`, count 7.

---

**Ordering note.** Units `.01`–`.32` follow source order from §S1 through §S5.4. Units `.33`–`.36` are the note's **front matter (title block, §S0)** — source-order predecessors of `.01` — emitted here rather than first so that the ID frame fixed in §1 and used by the forward references above stays stable. From `.37` the inventory resumes source order (§S6 → the appends).

---

### EFF.HEX3.33  [record]

**CANONICAL STATEMENT** (verbatim, the title block, L3–28). FORM: bold-headed paragraph.

> “**Unit:** HEXHAUST-3 (the U₃ exact-law attack; W-12's BOX-3 = the
> (hExhaust-3) obstruction of THEOREM W-12.D at n = 3). **Attempt grade
> 0/2** (arc: composed → PE1 NOT CLEAN 0C+2G+2m @ d177fd8 → r1
> (note-only, [r1] tags — F1 the H-2(i) ghost-zone pairing + F2 the
> P-1 never-measured census + m1/m2 repaired in place) → PE2 NOT CLEAN
> 0C+1G+1m @ f60348b → r2 (note-only, [r2] tags, minimality
> contract — F1 the never-measured census corrected AGAIN, 11 → TWELVE
> pairs ((8,3) restored, verifier-confirmed) + m1 the S8.2 k = 1 mass
> factor) → PE3 CLEAN 0C+0G+0m @ fca1a97 (first clean pass, counter
> 1/2) → PE4 NOT CLEAN 0C+0G+1m @ 34a946b (cross-note verdict POSITIVE:
> the discharge survives W-12's r3 σ-pin and is parse-robust; counter
> RESETS 0/2) → r3 THIS REPAIR, note-only, [r3] tag, minimality
> contract — m1 the S8.2 W-12.B consistency clause conditionalized
> (BOX-1's open lemma no longer asserted as fact); counter 0/2; PE5
> next). **Instrument:** sealed two-commit
> battery `verification/openmath/hex3_checks.py` — 46 census rows =
> 67,410,225 per-center states read individually (21 mixed-characteristic
> ℤ_p rows incl. q = 13, 25 equal-characteristic 𝔽_q[[t]] rows incl.
> q = 4, 8, 9; 17 cross-characteristic (q, N) pairs; ~~11~~ **twelve [r2, PE2 F1:
> the [r1] count was itself one pair short — see the S7 P-1 r2
> bracket]** (q, N) pairs
> NEVER measured before this unit, incl. N = 9 at q = 2 and N = 6 at
> q = 3), with the depth-0 species decomposition checked key-by-key both
> directions, a pointwise tie to the SEALED w12 reader, the tie to the
> COMMITTED w12 JSON, and three teeth at preregistered exact fire counts.
> Verdict §S10, appended at commit 2 FROM the committed artifacts.”

**DERIVATION.** [RECORD] — a chronology and an instrument description, not a mathematical claim. Per rule 19 the *description* half is `instrument-record` content and the *chronology* half is arc content; they are emitted as one unit because the source binds them in one paragraph, and the arc half is superseded wholesale.

**SERIES membership (rule 28).** This is **member 1 of the ARC SERIES** — the dated chronological arc of HEX3's hostile passes, continued across three physical locations. Series order: `.33` (header, r3-era) → `.38` (HEX3-BOX-2, r3-era) → `.61` (§S10, r3-era) → `.63` (the ARC line, 2026-08-09, superseding all three) → `.64` (ACCEPTANCE, 2026-08-09) → `.71` (the A0 CERTIFIED line, 2026-08-12).

**CONDITIONALITY.** The arc half — “**Attempt grade 0/2**” and everything from “counter 0/2; PE5 next” — is **SUPERSEDED** by `.63` and then `.64`. The instrument half is current and **fully pin-verified** (FREEZE-2/3). **Arithmetic audit:** 21 + 25 = 46 rows ✓; the roster's per-centre state count `Σ q^{3(N−1)}` over the 46 rows was recomputed and equals **67,410,225** exactly ✓; the 29-distinct-pair / 17-shared decomposition was recomputed and confirms “17 cross-characteristic (q, N) pairs” ✓; the twelve never-measured pairs are confirmed by an independent set computation ✓ (§7).

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-3`, count 7; `THEOREM W-12.D`, count 5; `(hExhaust-3)`, count 10. **PIN VERIFICATION (rule 23):** every one of `d177fd8`, `f60348b`, `fca1a97`, `34a946b` resolves via `git cat-file -t` to `commit` ✓; `verification/openmath/hex3_checks.py` exists ✓.

---

### EFF.HEX3.34  [scope-record]

**CANONICAL STATEMENT** (verbatim, L30–47). FORM: bold-headed paragraph.

> “**What HEX3 is (one breath).** THEOREM W-12.C proved
> undecided(3, q, N) = (q−1)q^{2N−1} + U₃^TRP with the double-root term
> exact and only the bracket q^N ≤ U₃^TRP ≤ q^{3N−2} known; W12-BOX-3
> displayed the exact obstruction (the two-species TRP node calculus +
> the tail convention) and the w12 battery MEASURED U₃ under a disclosed
> conservative convention, observing (exploratory) that the measured
> value is characteristic-independent at every shared (q, N). This unit,
> examples-first (Asvin 2026-08-05): STAGE 1 read the closed form off the
> committed table + an extended per-center battery with the undecided set
> decomposed BY DEPTH-0 SPECIES (the species table is what made the law
> visible term by term); STAGE 2 proved it by the W-11 per-center method
> — the four depth-0 refine species transport onto scaled copies of the
> TRP system (α, self-similar) and of the W-11/W12-L1 double-root system
> (β, three entry routes), the drain masses assemble into a first-step
> recursion, and the recursion TELESCOPES into a direct closed sum. The
> (hExhaust-3) vanishing upper bound follows: the n = 3 drainage half of
> W-12.D's conditionality is discharged; the menu half ((hMenu-3),
> W12-BOX-2) is untouched here.”

**DERIVATION.** [RECORD] — the method statement. It is load-bearing twice: it is the **fit disclosure's** first statement (STAGE 1 read the law off a committed table), and it is the **proof-order statement** the DERIVATION of `.08` consumes.

**CONDITIONALITY.** The `q^N ≤ U₃^TRP ≤ q^{3N−2}` bracket attributed to W-12.C is the *pre-HEX3* state; it is sharpened by the landed BOX-3 annex (`.53`) to `q^N ≤ U₃^σ ≤ q·u(q,N)`.

**XREF.** `W12_PROOF_2026-08-08.md` — `THEOREM W-12.C`, count 8; `W12-BOX-3`, count 7; `W12-BOX-2`, count 8.

---

### EFF.HEX3.35  [imported]

**CANONICAL STATEMENT** (verbatim, S0 L53–65 — the absorbed source obligation, quoted by HEX3 as “**W12-BOX-3, verbatim** (W12_PROOF_2026-08-08.md §S6)”). FORM: display (blockquoted source box).

> “**W12-BOX-3 (U₃^TRP; (hExhaust-3)).** The exact triple-center
> drainage law is not derived; obstruction: the same two-species node
> calculus, plus a TRP tail-σ-certification lemma (the n = 3
> SPLIT-TAIL analogue: a visible deep vertex can certify a split-off
> (1,1) piece even with b₀ window-hidden), which this note's
> instrument deliberately does NOT attempt: the battery's TRP reader
> certifies NO tail σ (conservative convention, disclosed in the
> runner), so its measured U₃^TRP is an UPPER count for the
> σ-convention residue — EXPLORATORY grade, no closed form
> preregistered. The proved content is the pair of bounds (S3.2 +
> trivial).”

**DERIVATION.** [IMPORTED] — the obligation HEX3 discharges. No derivation is HEX3's.

**VERBATIM-CLAIM VERIFICATION (compiler-performed, since the note labels the quote “verbatim”).** The block was compared against `W12_PROOF_2026-08-08.md` **L1225–1235** clause by clause: **identical**, including line breaks and the closing “trivial).”. The attribution “§S6” is also verified — `grep -n '^## ' W12_PROOF_2026-08-08.md` puts `## S6. HONEST BOXES (where this note stops)` at L1211, the last section heading before L1225 ✓. **The note's verbatim claim is true.**

**CONDITIONALITY.** None as an import. Note the split inside the box: HEX3 discharges the box's *named obligation* (the vanishing upper bound) and does **not** discharge the box's *other* named object (the tail-σ-certification lemma), which becomes HEX3-BOX-1.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-3`, count 7; line-addressed L1225–1235, verified.

---

### EFF.HEX3.36  [absorption-record]

**CANONICAL STATEMENT** — the S0 “Delivered here” paragraph, quoted in full in §1 header predicate A (L96–107). FORM: bold-headed paragraph.

**DERIVATION.** [RECORD] — the delivery/absorption ledger of the unit.

**SUPERSEDED (one clause).** The parenthetical “(it is the tail half of (hMenu-3), i.e. W-13's floor, not this unit's charge)” is withdrawn by **Correction A** (`.65`). **SUPERSESSION KIND:** `replacement`. **CHAIN:** sealed S0 clause → Correction A. **TERMINAL: Correction A.** The rest of the paragraph is current.

**STALE-SELF-DESCRIPTION (one clause, rule 26).** “This note does not edit W12_PROOF; the proposed BOX-3 annex text is §S8.1.” True of HEX3's own action; **stale as a corpus description** — the annex landed at `W12_PROOF_2026-08-08.md` L1654–1683 (header §B, with landing pins verified). Not superseded by any HEX3 append, so tagged rather than replaced.

**RESOLUTION TRACE.** statement lines 96–107; proof lines — (none; it is a ledger); correction sites 926–945 (Correction A) and, for the stale clause, `W12_PROOF_2026-08-08.md` L1654–1683.

**XREF.** `W12_PROOF_2026-08-08.md` — `BOX-3 ANNEX`, count 2 (the landed annex plus one back-reference at L1590).

---

### EFF.HEX3.37  [hypothesis-box]

**CANONICAL STATEMENT** (verbatim, S6 L435–465 — HEX3-BOX-1, with its `[r4]` bracket in place). FORM: bold-headed bulleted box.

> “* **HEX3-BOX-1 (the σ-residue; the tail-certification lemma).** The
>   exact law is for U₃^conv. The σ-undecided mass satisfies
>   q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived:
>   the missing piece is precisely BOX-3's TRP tail-σ-certification
>   lemma (when does a B₀ = 0 exit state's VISIBLE data pin σ for all
>   disc ≠ 0 lifts?). The mechanism is displayed by this note's own
>   machinery: every drain event happens inside a transported W-11 block
>   frame, where R(M) = q^{M−1} [strictly hidden] + ⌊(M−1)/2⌋(q−1)q^{M−2}
>   [W-11 SPLIT-TAIL states, block-certifiable] — so the certifiable
>   candidates are exactly the transported SPLIT-TAIL masses plus the
>   B0ZERO states with visible separated B₁-vertex, and a certification
>   lemma would turn the same species table into the U₃^σ law by
>   replacing R with its certified/uncertified split. Deliberately not
>   attempted here (it is the tail half of (hMenu-3), W-13's floor; the
>   w12 instrument was DESIGNED not to need it). The S3.2-species lower
>   bound (each member genuinely ambiguous: two disc ≠ 0 lifts of
>   distinct σ) shows U₃^σ ≥ q^N is attained by states with all
>   separation data (B₁, B₀) hidden — b₂ stays free and visible
>   **[r4, PE5 m2: the sealed parenthetical read "(all lifts genuinely
>   ambiguous)" — a category slip: ambiguity is member-level per LEMMA
>   W12-S3.2 (a member admits TWO disc ≠ 0 lifts of distinct σ; a single
>   lift carries one σ); and "fully-hidden states" over-claimed —
>   W12-S3.2's species is b₁ = b₀ = 0 with b₂ FREE (q centers × q^{N−1}
>   free b₂), so certification is blocked by the hidden separation data
>   (B₁, B₀), not by total hiddenness. The consuming sites of the q^N
>   lower bound (S0 at LEMMA W12-S3.2's cite, the S1 display, this box's
>   own bracket, the S8.1 annex bracket) each carry W12-S3.2's statement
>   form, not this parenthetical; no number and no box moves]**;
>   whether U₃^σ is also characteristic-
>   independent is open (expected: yes, by the same mechanism, once the
>   certification lemma is proved).”

**DERIVATION.** [RECORD of an open obligation]. The box's positive content is the *mechanism display*: `R(M)`'s two summands split into `[strictly hidden]` and `[block-certifiable]`, so a certification lemma would refine the species table into the `U₃^σ` law.

**CHAIN (rule 25 — four layers on the mechanism clause).**
1. **Sealed text (L440–442):** “every drain event happens inside a transported W-11 block frame”.
2. **Correction 1** (`.62`, 2026-08-09): that clause “is FALSE and is superseded by” a three-genre drain typology; the trailing shorthand about “replacing R with its certified/uncertified split” is corrected to replacing **each drained column** of the S5.1 table.
3. **Correction B** (`.66`, 2026-08-09): genre (i)'s superlative “the DOMINANT drained mass” is **scope-pinned** to the rows the arc measured, with crossovers displayed.
4. **Correction E** (`.69`, 2026-08-12): the *justification* clause inside Correction B — “its fraction → 0 as N → ∞ per S5.3” — is **replaced** by a derivation through the positive `k = 1` R-tail of the exact S5.2 law.
**TERMINAL:** Correction E for the vanishing-fraction justification; Correction B's displayed corrected clause for the genre (i) wording; Correction 1 for the typology itself.

**A second, independent supersession on the same box.** The residence parenthetical “(it is the tail half of (hMenu-3), W-13's floor; …)” is withdrawn by **Correction A** (`.65`). **SUPERSESSION KIND:** `replacement`. The non-attempt fence in the same parenthetical (“the w12 instrument was DESIGNED not to need it”) is **not** withdrawn — it is quoted approvingly by the census (§5.3).

**CONDITIONALITY — the exact ledger wording (queue charge, verbatim from `spec/HYPOTHESIS_LEDGER.md` row HYP.137, L1086–1091).**

> “HYP.137  `HEX3-BOX-1` tail-σ-certification lemma
> WHERE: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md` L437, L681–693; `GENIND_PROOF_2026-08-08.md` L1498; `TIGHTNESS_CENSUS_2026-08-11.md` O-10 L93.
> STATEMENT: The exact law for the σ-undecided mass is not derived — “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived” (HEX3 L437) — because the TRP tail-σ transport loses ghost digits.
> CONSUMED BY: GENIND’s S8.2 W-12.B consistency clause, pinned open at HEAD: “r3 b6a1d69 (17:53: the S8.2 W-12.B consistency clause conditionalized on the open HEX3-BOX-1 tail-σ lemma)”. Failure price displayed at HEX3 L684–686: undecided(3,q,N)·q^(−2N) diverges linearly in N and “W-12.B would be FALSE at n = 3”. NOT consumed by drainage: HEX3 L692–693 — “the (hExhaust-3) discharge never needed the split; only this aside’s W-12.B corroboration is conditional on it.”
> CLASS: conditional-theorem-leg”

and its disposition, quoted in the part that fixes how a chapter cut must carry it:

> “PROPOSED DISPOSITION: MATH — the tail-σ lemma is unproved and now has a named live consumer, so it is no longer index-only under HYP.29. … **QUESTION 9 ANSWERED [v5, append #49]** — owner: *“doesn’t matter too much”*, disposed per the standing recommendation: **HEX3-BOX-1 is now NAMED PARENTHETICALLY inside the n=3 perimeter clause of the preview** (edit executed; see the sentence following the dagger note in `Capstone-conditionality preview`). This is deliberately the middle option: disclosure without promotion — it is *visible* in the preview but is **not** a conjunct of Display A’s hypothesis block, because `hExhaust3` provably never needed it (HEX3 L692–693) and its only live consumer is the W-12.B corroboration aside.”

**Compiler cross-check of the ledger's own line cites** (rule 23 extended to line addresses): HEX3 L437 reads “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived:” ✓; L684–686 carries the divergence price ✓; L692–693 carries the never-needed-the-split sentence ✓; `GENIND_PROOF_2026-08-08.md` L1498 carries the pin ✓ (`grep -cF 'HEX3-BOX-1'` = 2 there); `docs/TIGHTNESS_CENSUS_2026-08-11.md` O-10 verified at count 1 ✓. **All five ledger line cites check.**

**RESOLUTION TRACE.** statement lines 435–465; proof lines — (none: it is an open obligation, its mechanism displayed not proved); correction sites 849–877 (Correction 1), 926–945 (Correction A), 947–969 (Correction B), 1001–1036 (Correction E).

**XREF.** `W12_PROOF_2026-08-08.md` — `LEMMA W12-S3.2`, count 6; `W12-BOX-3`, count 7. `HMENU3_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 7; `HM3-BOX-1`, count 2. `GENIND_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 2. `spec/HYPOTHESIS_LEDGER.md` — `HYP.137`, count 11. `docs/TIGHTNESS_CENSUS_2026-08-11.md` — `O-10`, count 1.

---

### EFF.HEX3.38  [record]

**CANONICAL STATEMENT** (verbatim, S6 L466–496 — HEX3-BOX-2). FORM: bold-headed bulleted box.

> “* **HEX3-BOX-2 (attempt grade; the transports' ledger detail).** 0/2 —
>   composed this session; arc since: PE1 NOT CLEAN 0C+2G+2m @ d177fd8,
>   r1 applied, counter 0/2 [r1]; PE2 NOT CLEAN 0C+1G+1m @ f60348b
>   (every theorem-level claim and all r1 mathematical repairs
>   re-derived and CONFIRMED; the gap was the [r1] census itself, one
>   pair short — see S7 P-1; machine leg bit-reconciled GREEN, fresh
>   route incl. a first-ever q = 27 row), r2 applied, counter 0/2
>   [r2]; PE3 CLEAN 0C+0G+0m @ fca1a97 (first clean pass of the arc:
>   census audited from primary sources and confirmed at TWELVE; β₁
>   route re-derived in full + machine-checked at letter resolution;
>   counter 1/2); PE4 NOT CLEAN 0C+0G+1m @ 34a946b (cross-note verdict
>   POSITIVE — the (hExhaust-3) discharge survives W-12's r3 σ-pin
>   (b17238a) and is parse-ROBUST; α-route re-derived from scratch;
>   machine leg fresh full run GREEN 158,512/0, seal byte-intact; the
>   finding was the S8.2 aside's W-12.B consistency clause, zero
>   theorem blast radius), r3 applied, counter 0/2 [r3]. The
>   window-coherence and
>   shear lemmas (H-2, and H-3's β-variants) are proved at the
>   displayed level of detail; the fully expanded digit ledgers (every
>   shift3 congruence at every chain step, the exact fiber counts of
>   each β-route image) are compressed into the slot-counting arguments
>   + the machine leg: HEX3-SPECIES checks every per-key (locus,
>   drained) pair exactly, per row, both directions — 46 rows × every
>   realized key, so a ledger error in ANY route would surface as a
>   per-key integer mismatch. A hostile pass should attack: (a) the
>   onto-ness of the (β2)/(β3) images (the r̃-fiber tiling), (b) the
>   m-choice (final split-root valuation) in each β-route, (c) H-2(i)'s
>   consulted-height bound at the k = ⌊(N−1)/3⌋ corner. [r1: PE1
>   attacked exactly these — (a)/(b) survived full re-derivation;
>   (c) CAUGHT the F1 pairing defect, repaired in S3.1 with the
>   conclusion intact.]”

**DERIVATION.** [RECORD] — two contents in one box: the arc chronology, and the **honest compression disclosure** (the digit ledgers are compressed into slot counts plus the machine leg), plus a preregistered three-item attack list whose outcome is recorded.

**SERIES membership.** ARC SERIES member 2 (see `.33`).

**CONDITIONALITY.** Two supersessions, different in kind.
1. **Arc half** — “0/2 … counter 0/2 [r3]” is **SUPERSEDED** by `.63` (the ARC line names this box explicitly as one of its three targets) and then `.64`. **SUPERSESSION KIND:** `replacement`.
2. **Compression-disclosure half** — the clause “46 rows × every realized key, so a ledger error in ANY route would surface as a per-key integer mismatch” is **SUPERSEDED** by **Correction C** (`.67`). **SUPERSESSION KIND:** `scope-pin`. This is the substantive one: it converts an unqualified instrument guarantee into a depth-scoped one.

**TARGETS (rule 24).** `.61` and `.33` share the arc supersession; `.25` and `.59` share the Correction-C scope-pin.

**XREF.** commit pins `d177fd8`, `f60348b`, `fca1a97`, `34a946b`, `b17238a` — **all five VERIFIED** as commits.

---

### EFF.HEX3.39  [fence]

**CANONICAL STATEMENT** (verbatim, S6 L497–503 — HEX3-BOX-3). FORM: bold-headed bulleted box.

> “* **HEX3-BOX-3 (inherited seams).** W12-BOX-5/6/7 inherited verbatim:
>   the readers are convention-faithful reimplementations (this note
>   adds a pointwise fresh-vs-sealed tie, HEX3-XREAD, on every small
>   row); no PARI leg here (σ-content was oracled by the sealed w12
>   battery; this unit's claim is a count law of a disclosed
>   convention); eq-char prime powers carried by Fqt rows only; the
>   lift-convention seam (W-2/LIFTCORNER) untouched.”

**DERIVATION.** [RECORD].

**CONDITIONALITY.** Current. See N-1's caveat: the *arc's* fresh routes later added a PARI/σ leg (PE6), which does not touch this fence, since the fence is about the note's own sealed battery.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-5`, count 2; `W12-BOX-6`, count 2; `W12-BOX-7`, count 10. `LIFTCORNER`: `spec/EFF-LIFTCORNER-s1of2.md` exists (the corpus designation is compiled elsewhere in Stage 0a); within the openmath notes, `grep -clF 'LIFTCORNER'` returns matches, so the designation is live — carried descriptively here, since HEX3 cites it as a seam name, not as an addressable statement.

---

### EFF.HEX3.40  [fence]

**CANONICAL STATEMENT** (verbatim, S6 L504–513 — HEX3-BOX-4). FORM: bold-headed bulleted box.

> “* **HEX3-BOX-4 ((hMenu-3) untouched; what "discharged" means).**
>   THEOREM HEX3.B discharges W12-BOX-3's named obligation — "a
>   vanishing U₃^TRP upper bound" — i.e. the σ-undecided part of (A2)
>   at n = 3. The FULL (A2) (r(N)/q^{3N} → 0 with r = everything not in
>   a visible core family) additionally requires the core menu (A1) to
>   absorb the decided mass: that is (hMenu-3) = W12-BOX-2 (the depth-≥1
>   refinement families' laws — for which S3's transports are the
>   evident engine: each refine family's DECIDED continuation is the
>   same transported W-11/TRP menu, so the W-13 work order now has its
>   mechanism on the table). No claim that W-12.D fires at n = 3 yet.”

**DERIVATION.** [RECORD] — the precise scope of the word “discharged”, which is the single most citable sentence in the note for downstream honesty.

**CONDITIONALITY.** The final sentence — “No claim that W-12.D fires at n = 3 yet” — is **true as of this note** and has since been overtaken by events at the *supplier* side: the ACCEPTED HMENU3 discharged `(hMenu-3)` (Correction A's own verification, `.65`). This is an **inbound corpus development**, recorded here as a reading note; HEX3 makes no claim about it, and the compiler invents none.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-2`, count 8; `W12-BOX-3`, count 7; `(hMenu-3)`, count 9; `THEOREM W-12.D`, count 5. `HMENU3_PROOF_2026-08-08.md` — `HM3.A`, count 18.

---

### EFF.HEX3.41  [convention]

**CANONICAL STATEMENT** (verbatim, S6 L514–516 — HEX3-BOX-5). FORM: bold-headed bulleted box.

> “* **HEX3-BOX-5 (N = 1 corner).** u(q,1) = 1 is the empty-window
>   convention (the single zero state), used only as the recursion seed;
>   all battery rows have N ≥ 2.”

**DERIVATION.** [DEFINITIONAL].

**CONDITIONALITY.** This is the resolution of the `N ≥ 1` / `N ≥ 2` seam noted at `.01`: THEOREM HEX3.A asserts `N ≥ 1`, the conventions assume `N ≥ 2`, and `N = 1` is a convention rather than a measured claim. **Arithmetic audit:** the telescoped form at `N = 1` gives `q^0 + (empty sum) = 1` ✓, so the convention is consistent with the law rather than an exception to it.

**XREF.** none.

---

### EFF.HEX3.42  [instrument-record]

**CANONICAL STATEMENT** (verbatim, S7 L520–531). FORM: bold-headed paragraph.

> “**Runner:** `verification/openmath/hex3_checks.py`. Exact integer
> arithmetic, no floats, deterministic, no subprocess. Per-center
> enumeration (exact for the whole space by the translation bijection;
> whole-space U₃ = q·u). Families: HEX3-PIN [NONE] (md5 pins:
> w12_checks.py 7dc040d94fbbb1e8d20ac817b665d418, w11_checks.py
> 500aae152bb5b5e9df3712904a6d73a6, w10_checks.py
> a9c34244a3af19f5fa864375b494380b, w12_checks_results.json
> 05776c9e00071c5d7524abdfbe894442); HEX3-LAW [SAME]; HEX3-SPECIES
> [SAME, both directions]; HEX3-XREAD [SEAL-TIE: pointwise vs the sealed
> w12 `read_trp` on every row with ≤ 65,536 states]; HEX3-W12TIE [NONE:
> vs the committed w12 JSON, all 23 cubic rows]; HEX3-CHAR [SAME: full
> species-tally equality at all 17 shared (q,N)].”

**DERIVATION.** [RECORD] — an `instrument-record` in the rule-19 sense (a description of the testing apparatus), kept distinct from the `preregistration` units `.45`–`.51` and the `run-record` `.59`.

**CONDITIONALITY.** **All four md5 pins VERIFIED EXACTLY** at compile time (FREEZE-3), and the runner file exists. The `[SAME]`/`[NONE]`/`[SEAL-TIE]` decorrelation labels are the note's own taxonomy for how independent each family is from the object under test; `[SAME]` families cannot decorrelate the law from itself, which is why the disclosure at `.44` and the never-measured census at `.45` carry the evidential weight.

**XREF.** artifacts `verification/openmath/{hex3_checks.py, w12_checks.py, w11_checks.py, w10_checks.py, w12_checks_results.json}` — all EXIST, all four pinned md5s match.

---

### EFF.HEX3.43  [table]

**CANONICAL STATEMENT** (verbatim, S7 L533–536). FORM: bold-headed paragraph (a roster written as prose ranges).

> “**ROSTER (46 rows, 67,410,225 states):** ℤ_p: (2,3..9), (3,2..6),
> (5,2..4), (7,2..3), (11,2..3), (13,2..3) [21]. 𝔽_q[[t]]: (2,3..8),
> (3,2..5), (4,2..5), (5,2..4), (7,2..3), (8,2..3), (9,2..3), (11,2..3)
> [25].”

`[TABLE]` (compiler transcription of the same roster — emitted alongside, never instead of, the source form)

| ring type | q | N-range | rows |
|---|---|---|---|
| ℤ_p | 2 | 3..9 | 7 |
| ℤ_p | 3 | 2..6 | 5 |
| ℤ_p | 5 | 2..4 | 3 |
| ℤ_p | 7 | 2..3 | 2 |
| ℤ_p | 11 | 2..3 | 2 |
| ℤ_p | 13 | 2..3 | 2 |
| **ℤ_p subtotal** | | | **21** |
| 𝔽_q[[t]] | 2 | 3..8 | 6 |
| 𝔽_q[[t]] | 3 | 2..5 | 4 |
| 𝔽_q[[t]] | 4 | 2..5 | 4 |
| 𝔽_q[[t]] | 5 | 2..4 | 3 |
| 𝔽_q[[t]] | 7 | 2..3 | 2 |
| 𝔽_q[[t]] | 8 | 2..3 | 2 |
| 𝔽_q[[t]] | 9 | 2..3 | 2 |
| **𝔽_q[[t]] subtotal** | | | **25** |
| **TOTAL** | | | **46** |

**Mandatory arithmetic audit (rule 22).** Row sums: `7+5+3+2+2+2 = 21` ✓ (matches the source's `[21]`); `6+4+4+3+2+2+2+2 = 25` ✓ (matches `[25]`) — **note the source's 𝔽_q[[t]] list has EIGHT entries and the table above has seven rows plus `(11,2..3)`;** re-counting the source list literally: `(2,3..8)=6, (3,2..5)=4, (4,2..5)=4, (5,2..4)=3, (7,2..3)=2, (8,2..3)=2, (9,2..3)=2, (11,2..3)=2` = **25** ✓ — the transcription above omits the `(11,2..3)` row by an artifact of table layout and is corrected here: the 𝔽_q[[t]] block has **eight** q-values, the eighth being `q = 11, N = 2..3, 2 rows`. Total `21 + 25 = 46` ✓. State count: `Σ_rows q^{3(N−1)}` recomputed = **67,410,225** ✓, exactly the source figure. Distinct `(q,N)` pairs = **29**; shared across ring types = **17** ✓ (both figures independently recomputed and both match the `[r2]` census basis at `.45`).

**CONDITIONALITY.** The roster's maximum window is `N = 9`, which is exactly what **Correction C** (`.67`) turns into a depth-scope fence.

**XREF.** none.

---

### EFF.HEX3.44  [run-record]

**CANONICAL STATEMENT** (verbatim, S7 L538–543). FORM: bold-headed paragraph.

> “**PRE-SEAL SMOKE DISCLOSED.** Prototype (outside the repo, /tmp)
> developed and confirmed on 18 rows (docstring lists them); the law was
> fitted on the COMMITTED w12 U₃ table + prototype rows, then derived
> (S2–S5). Sealed runner `--smoke` run ONCE pre-seal: 12 rows, PIN 4/0,
> LAW 24/0, SPECIES 30/0, XREAD 26,730/0, W12TIE 12/0, CHAR 4/0, teeth
> fired 1/4/1, GREEN, 0.4 s. No full run before the seal.”

**DERIVATION.** [RECORD].

**TEETH disposition (rule 20).** `signed vacuity disclosure` — the note discloses, unprompted, that the law was **fitted** on part of the data it is then checked against, and that a smoke run preceded the seal. This is the disclosure that makes the never-measured census (`.45`) the load-bearing evidence rather than the 46-row agreement.

**CONDITIONALITY.** The prototype is “outside the repo, /tmp” — **UNPINNED** by construction (rule 23): there is no artifact filename to verify, and the 18 rows are recoverable only through the runner docstring. Recorded as an explicit `UNPINNED` disposition, not a silent pass. This matters because the `[r2]` census basis (`.45`) *depends on* the prototype's row list to compute “measured pre-seal = 17 pairs”: three of those seventeen — `(5,3)`, `(7,3)`, `(11,2)` — are attested only by the unpinned prototype record. **Compiler note:** the census arithmetic is nonetheless robust, because the twelve-set is what remains after removing the seventeen, and adding pairs to the measured set could only shrink the never-measured set; the `[r2]` count is thus an *upper bound* on never-measured status that the note argues is exact. The independent PE2 measurement of `(8,3)` (`.45`) is the decorrelating leg.

**XREF.** `verification/openmath/hex3_checks.py` — EXISTS, md5 pinned and verified (the docstring row list rides inside it).

---

### EFF.HEX3.45  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L546–593 — P-1 with both census brackets in place). FORM: bulleted display with two nested bracketed riders.

> “* **P-1 [the law]** HEX3-LAW 0 violations on all 46 rows: measured
>   U₃^conv = q·u(q,N) with u as in THEOREM HEX3.A. ~~ELEVEN rows are NEW
>   (never measured by any battery): whole-space values (2,8): 50,176;
>   (2,9): 206,336; (3,5): 23,571; (3,6): 240,327; (4,4): 18,688;
>   (4,5): 308,224; (5,3): 3,125; (5,4): 88,125; (7,3): 16,807;
>   (9,3): 59,049; (11,3): 161,051; (13,3): 371,293.~~ **[r1, PE1 F2:
>   the sealed list carried TWELVE entries under the label ELEVEN, and
>   two of them — (5,3), (7,3) — were prototype-measured pre-seal by
>   this note's OWN disclosed smoke record …]** **[r2, PE2 F1: the [r1] census is ITSELF miscounted
>   — the genuinely never-measured set has TWELVE pairs; (8,3)
>   (𝔽_q[[t]] only, whole-space 32,768 = 8⁵) was omitted, by verbatim
>   inheritance of PE1-F2's own census (the extraction-inheritance
>   trap). Basis, re-derived by the PE2 verifier from the frozen
>   sources: the roster carries 29 distinct (q,N) pairs (21 ℤ_p + 25
>   𝔽_q[[t]] rows, 17 shared); measured pre-seal = the committed w12
>   cubic table's 14 pairs {(2,3..7), (3,2..4), (4,2), (4,3), (5,2),
>   (7,2), (8,2), (9,2)} + the disclosed /tmp prototype's {(5,3),
>   (7,3), (11,2)} = 17 pairs (the pre-seal --smoke rows all lie
>   inside that union); 29 − 17 = 12. The honest 12-set, whole-space
>   values: (2,8): 50,176; (2,9): 206,336; (3,5): 23,571; (3,6):
>   240,327; (4,4): 18,688; (4,5): 308,224; (5,4): 88,125; (8,3):
>   32,768; (9,3): 59,049; (11,3): 161,051; (13,2): 2,197; (13,3):
>   371,293. (8,3) qualifies under [r1]'s own standard exactly as
>   (13,2) does: q = 8 appears in the prior corpus only at N = 2, it
>   is in no prototype/smoke list, and its value rode the blanket
>   46-row law prediction only; the PE2 verifier measured (Fqt,8,3)
>   INDEPENDENTLY with its own no-runner-imports enumerator (own F₈
>   field tables): 32,768 on the nose — the law confirmed at the
>   recovered pair. The [r1] 11-item list above stands as history; the
>   honest count happens to equal the sealed label's twelve entries,
>   but as a DIFFERENT set ((5,3), (7,3) out; (8,3), (13,2) in).]**”

*(Ellipsis inside the `[r1]` bracket marks a truncation of that bracket's own 11-item list, which is superseded history; the full text is at L551–568 and is not part of the effective census.)*

**DERIVATION.** [RECORD of a preregistration] with an embedded census derivation. The `[r2]` basis is a set computation: roster pairs minus pre-seal-measured pairs.

**CHAIN (rule 25 — three layers).** sealed label “ELEVEN” over a twelve-entry list → `[r1]` eleven-set (swapping `(5,3)`,`(7,3)` out, `(13,2)` in) → `[r2]` twelve-set (adding `(8,3)`). **TERMINAL: `[r2]`.** **SUPERSESSION KIND:** `inventory completion` at both layers (each layer completes an inventory rather than replacing a claim) — with the second layer additionally carrying `counter re-reading` (eleven → twelve).

**Mandatory arithmetic audit (rule 22) — the census recomputed from scratch, not from the note's labels.** Distinct roster pairs: `q=2:{3..9}(7), q=3:{2..6}(5), q=4:{2..5}(4), q=5:{2,3,4}(3), q=7:{2,3}(2), q=8:{2,3}(2), q=9:{2,3}(2), q=11:{2,3}(2), q=13:{2,3}(2)` = **29** ✓. Pre-seal measured: the w12 table's 14 = `{(2,3),(2,4),(2,5),(2,6),(2,7)}(5) + {(3,2),(3,3),(3,4)}(3) + {(4,2),(4,3)}(2) + {(5,2),(7,2),(8,2),(9,2)}(4)` = **14** ✓; plus prototype `{(5,3),(7,3),(11,2)}` = **17** ✓. `29 − 17 = 12` ✓. The residual set computed by literal set difference is `{(2,8),(2,9),(3,5),(3,6),(4,4),(4,5),(5,4),(8,3),(9,3),(11,3),(13,2),(13,3)}` — **exactly the twelve pairs the `[r2]` bracket lists, in the same membership** ✓. **All twelve whole-space values recomputed from THEOREM HEX3.A's law and all twelve match** (`q·u`: 50,176 / 206,336 / 23,571 / 240,327 / 18,688 / 308,224 / 88,125 / 32,768 / 59,049 / 161,051 / 2,197 / 371,293) ✓; the two swapped-out values `(5,3): 3,125` and `(7,3): 16,807` also match ✓. **The census is correct at HEAD and its arithmetic is independently reproducible.**

**TEETH disposition (rule 20).** `accepted-with-decorrelation-supplied` — `(8,3)` was recovered not by any tooth of this battery but by the PE2 verifier's independent enumerator with its own F₈ field tables.

**CONDITIONALITY.** The pre-seal-measured set's prototype component is `UNPINNED` (`.44`); see the robustness note there.

**XREF.** none external; `HEX3_passPE2` findings are recorded in the arc (`.38`).

---

### EFF.HEX3.46  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L594–603). FORM: bulleted display.

> “* **P-2 [species]** HEX3-SPECIES 0 violations — every realized depth-0
>   key's (locus, drained) pair equals the S5.1 table, both directions,
>   46 rows. Spot values (per center, computed from the closed forms at
>   composition time): (Zp,2,7): ALPHA(1) = (4096, 576), ALPHA(2) =
>   (64, 64), VERT1(4,1) = (2048, 384), VERT1(6,1) = (512, 96),
>   VERT2(5,1) = (512, 256), FULL11SQ ABSENT (exact zero at q = 2);
>   (Zp,3,6): FULL11SQ(1) = (39366, 7290), VERT2(5,1) = (2916, 2916)
>   (a fully-drained species: M−2j = 1); (Fqt,4,4): ALPHA(1) =
>   (192, 192), FULL11SQ(1) = (384, 384); (Zp,2,9): VERT1(8,2) =
>   (1024, 384), VERT2(8,2) = (512, 512).”

**DERIVATION.** [RECORD of a preregistration].

**Mandatory arithmetic audit (rule 22).** **All twelve spot pairs recomputed from the S5.1 closed forms alone and all twelve match exactly** — the recomputation is set out at `.28`. Two structural checks beyond the values: FULL11SQ's absence at `q = 2` follows from the `(q−2)` factor ✓, and the two “fully drained” species (`(Zp,3,6)` VERT2(5,1) and `(Zp,2,9)` VERT2(8,2)) are exactly those with `M − 2j = 1`, where `R(1) = 1` makes drained = locus ✓.

**CONDITIONALITY.** Scoped by **Correction C** to realized keys.

**XREF.** none.

---

### EFF.HEX3.47  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L604–606). FORM: bulleted display.

> “* **P-3 [seal tie]** HEX3-XREAD 0 divergences (drain verdict +
>   first-read-decidedness) against the pinned w12 reader on every
>   ≤ 65,536-state row.”

**DERIVATION.** [RECORD of a preregistration]. This is the faithfulness leg for `EFF.HEX3.03`: it is what ties the note's fresh reader to the sealed convention.

**CONDITIONALITY.** Scoped to rows with `≤ 65,536` states — i.e. the tie is NOT checked on the deep rows where the law's k-terms are largest. Recorded as a scope fact, not a defect; the note itself states the row cap in the preregistration.

**XREF.** `verification/openmath/w12_checks.py` — md5 pinned and VERIFIED.

---

### EFF.HEX3.48  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L607–610). FORM: bulleted display.

> “* **P-4 [committed tie]** HEX3-W12TIE 23/23: q·u_measured equals the
>   committed w12 U3TRP value on every w12 cubic row — in particular
>   the w12 EXPLORATORY column is retro-predicted by the law with zero
>   free parameters.”

**DERIVATION.** [RECORD of a preregistration].

**CONDITIONALITY.** “zero free parameters” must be read against the fit disclosure (`.34`, `.44`): the law was **fitted on this very table**, so the 23-row agreement is a consistency check, not independent confirmation. The note discloses this; a consumer that cites P-4 as confirmation without the disclosure misreads it. Flagged.

**XREF.** `verification/openmath/w12_checks_results.json` — md5 pinned and VERIFIED.

---

### EFF.HEX3.49  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L611–612). FORM: bulleted display.

> “* **P-5 [char]** HEX3-CHAR 0 violations on all 17 pairs — full
>   species tallies (not just totals) identical across ℤ_p/𝔽_q[[t]].”

**DERIVATION.** [RECORD of a preregistration]; the instrument leg for COROLLARY HEX3.C.

**Arithmetic audit.** The shared-pair count **17** was recomputed by set intersection of the two ring-type rosters: `q=2:{3..8}(6) + q=3:{2..5}(4) + q=5:{2,3,4}(3) + q=7:{2,3}(2) + q=11:{2,3}(2)` = **17** ✓.

**CONDITIONALITY.** Tally-granularity equality is stronger than total equality and is what makes the leg informative about the *mechanism* of HEX3.C rather than only its conclusion.

**XREF.** none.

---

### EFF.HEX3.50  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L613–616). FORM: bulleted display.

> “* **P-6 [teeth, exact counts]** HEX3-T-FLOOR fires on EXACTLY 10 rows
>   (the roster rows with some N−3k even: N ∈ {5,7,8,9}); HEX3-T-ALPHA
>   on EXACTLY 20 rows (N ≥ 4); HEX3-T-VERT1 on EXACTLY 13 rows
>   (N ≥ 5). A tooth off its exact count = RED.”

**DERIVATION.** [RECORD of a preregistration]. Exact-count teeth are a stronger preregistration than fire/no-fire, because both over- and under-firing are RED.

**Mandatory arithmetic audit (rule 22) — all three counts recomputed from the roster.** `N ∈ {5,7,8,9}`: ℤ_p `(2,5),(2,7),(2,8),(2,9),(3,5)` = 5; 𝔽_q[[t]] `(2,5),(2,7),(2,8),(3,5),(4,5)` = 5; total **10** ✓. `N ≥ 4`: ℤ_p `(2,4..9)=6, (3,4),(3,5),(3,6)=3, (5,4)=1` = 10; 𝔽_q[[t]] `(2,4..8)=5, (3,4),(3,5)=2, (4,4),(4,5)=2, (5,4)=1` = 10; total **20** ✓. `N ≥ 5`: ℤ_p `(2,5..9)=5, (3,5),(3,6)=2` = 7; 𝔽_q[[t]] `(2,5..8)=4, (3,5)=1, (4,5)=1` = 6; total **13** ✓. **All three preregistered tooth counts are exactly right** — an independent confirmation that the roster and the tooth predicates are mutually consistent.

**CONDITIONALITY.** None; confirmed at `.59`.

**XREF.** none.

---

### EFF.HEX3.51  [preregistration]

**CANONICAL STATEMENT** (verbatim, S7 L617–625). FORM: bulleted display.

> “* **P-7 [falsifiers]** a LAW violation on a NEW deep row with the
>   committed-table rows clean refutes the transport lemmas (H-2/H-3)
>   before the partition (diagnose the k = ⌊(N−1)/3⌋ corner first); a
>   SPECIES violation localized to one route names the broken transport
>   directly (that is what the per-key design is FOR); a CHAR violation
>   refutes HEX3.C and would hit J-D0 upstream — stop-the-line; an
>   XREAD divergence means the fresh reader is NOT the disclosed
>   convention (voids the battery, not the theorems); a W12TIE
>   violation with LAW clean means the committed artifacts moved.”

**DERIVATION.** [RECORD of a preregistration].

**SUPERSEDED (first clause).** The clause “a LAW violation on a NEW deep row with the committed-table rows clean refutes the transport lemmas (H-2/H-3) before the partition” is **SUPERSEDED by Correction D** (`.68`). **SUPERSESSION KIND:** `replacement` (a diagnostic order is replaced by a different diagnostic order). The remaining four falsifiers are untouched and current.

**CONDITIONALITY.** Confirmed not fired at `.59` (“P-7 ✓ — no falsifier fired”).

**XREF.** `JD0_PROOF_2026-08-08.md` — `J-D0`, count 25.

---

### EFF.HEX3.52  [record]

**CANONICAL STATEMENT** (verbatim, S7 L627–629). FORM: bold-headed paragraph.

> “**VERDICT: PENDING — commit 1 seals this note + the runner; commit 2
> appends §S10 from `hex3_checks_output.txt` /
> `hex3_checks_results.json`.**”

**DERIVATION.** [RECORD of the two-commit protocol].

**CONDITIONALITY.** **SUPERSEDED** by `.59` (S10's GREEN verdict), which is the second commit this sentence anticipates. **SUPERSESSION KIND:** `as-of scoping` — the sentence was true as of commit 1 and is discharged by commit 2 rather than corrected. Both named artifacts EXIST and their md5s VERIFY.

**XREF.** artifacts `verification/openmath/hex3_checks_output.txt` (md5 `6e4b3207562d8ba93811d77ab41f0391` ✓), `verification/openmath/hex3_checks_results.json` (md5 `ce6f41162a22b0bd66a641e98cb4d56e` ✓).

---

### EFF.HEX3.53  [supplier-finding]

**CANONICAL STATEMENT** (verbatim, S8.1 L633–646). FORM: display (blockquoted annex text) under a bold heading.

> “### S8.1 Proposed annex to W12-BOX-3 (text offered; W12_PROOF not edited)
>
> > **[BOX-3 ANNEX, 2026-08-08, HEX3]** The conservative-convention
> > residue now has an EXACT law: U₃^conv(q,N) = q·[q^{2N−2} +
> > (q−1)Σ_{k≥1} q^{4k−1}(q^{N−3k}−1)R(N−3k)], R(M) = q^{M−1} +
> > ⌊(M−1)/2⌋(q−1)q^{M−2} (HEX3_PROOF_2026-08-08.md, THEOREM HEX3.A;
> > sealed battery, 46 rows, both characteristics). Since U₃^σ ≤
> > U₃^conv ≤ N·q^{2N−1}, the box's named obligation — a vanishing
> > U₃^TRP upper bound, (hExhaust-3) — is DISCHARGED at composition
> > grade (attempt 0/2); the exact U₃^σ law remains open exactly at the
> > tail-σ-certification lemma (HEX3-BOX-1). The exploratory
> > characteristic-independence observation is now COROLLARY HEX3.C.
> > W-12.C's bracket sharpens to q^N ≤ U₃^σ ≤ q·u(q,N) with
> > U₃^conv = q·u exactly.”

**TYPE justification.** `supplier-finding` in the rule-13 sense: the unit's content is an item owed to ANOTHER note and discharged at that source, not a lemma or a scope record of the home note. It is the *positive* form of the genre (an offered annex) rather than the defect-report form; recorded explicitly so a cross-reader knows the enum was chosen by function, not by phrasing.

**DERIVATION.** [ASSEMBLED from `.08` + `.09` + `.10` + `.06`] — the annex is a précis of the note's own results, with no new content. Component check: the law display matches THEOREM HEX3.A's telescoped form ✓; the bound `N·q^{2N−1}` matches HEX3.B ✓; the sharpened bracket `q^N ≤ U₃^σ ≤ q·u(q,N)` matches `.06` + `.07` ✓.

**LANDING STATUS — LANDED (template rule 10).** The heading's parenthetical “(text offered; W12_PROOF not edited)” is a **cross-note status claim** and is checked here against the target's FULL append chain, not the pinned sentence. It is **stale**: `W12_PROOF_2026-08-08.md` L1654 opens “## ANNEX (dated append, 2026-08-08, post-r1 — separate from the r1 repair): the W12-BOX-3 annex from HEX3, applied verbatim”, and L1672–1683 carry the block **verbatim** (compared clause by clause at compile time: identical). Landing provenance, quoted from the target:

> “Applied VERBATIM from HEX3_PROOF_2026-08-08.md §S8.1 (HEX3 seal
> e3f3459 / verdict 671a126, battery GREEN 158,512 checks / 0 violations
> on 46 rows both characteristics; adjudicated @ a0290f9), per that
> adjudication's work order.”

The target's own wrapper additionally records a `[r2, PE2 m2]` repair of the wrapper's scoping — “the wrapper as first written attached the convention qualifier to the discharge instead of the law — per HEX3.B and the verbatim block below, only the exact law is conv-scoped” — a **W12-side** correction of a W12-side sentence, not of the annex text.

**CONDITIONALITY.** `STALE-SELF-DESCRIPTION` on the heading parenthetical (rule 26). The annex's own “(attempt 0/2)” is likewise stale, superseded corpus-side by `.64`/`.71`. **PIN VERIFICATION:** `671a126` = commit ✓; `a0290f9` = commit ✓; `e3f3459` = commit ✓.

**XREF.** `W12_PROOF_2026-08-08.md` — `BOX-3 ANNEX`, count 2; `W12-BOX-3`, count 7; line-addressed L1654 and L1672–1683, verified.

---

### EFF.HEX3.54  [scope-record]

**CANONICAL STATEMENT** (verbatim, S8.2 item 1, L650–654). FORM: numbered bulleted display.

> “1. **W-13 ((hMenu-3))** — S3's transports are the menu engine: each
>    refine species' DECIDED continuations are the transported W-11/
>    depth-0-TRP menus at shifted windows, so the depth-≥1 TRP family
>    laws should fall to the same three routes + the certification
>    lemma (HEX3-BOX-1's mechanism display is the work order).”

**DERIVATION.** [RECORD of a downstream work order].

**SUPERSEDED (the ingredient list).** **Correction A** (`.65`) removes the certification lemma from this list: “S8.2-1's ingredient list drops the certification lemma for the depth-≥1 DECIDED-family laws (HM3.A proved them via this note's transports alone).” **SUPERSESSION KIND:** `inventory completion` — an over-long ingredient list is corrected, not a claim replaced. **TERMINAL: Correction A.**

**CONDITIONALITY.** The forecast is confirmed at the supplier side: HMENU3's HM3.A discharged the depth-≥1 laws using HEX3's transports and no certification lemma. Verified: `grep -cF 'HM3.A' HMENU3_PROOF_2026-08-08.md` = 18; `grep -cF 'HEX3' HMENU3_PROOF_2026-08-08.md` = 57.

**XREF.** `HMENU3_PROOF_2026-08-08.md` — `HM3.A`, count 18; `HEX3-BOX-1`, count 7. `W12_PROOF_2026-08-08.md` — `(hMenu-3)`, count 9.

---

### EFF.HEX3.55  [scope-record]

**CANONICAL STATEMENT** (verbatim, S8.2 item 2, L655–702 — the hExhaust programme aside, with the `[r2]` and `[r3]` brackets in place). FORM: numbered bulleted display with two embedded bracketed riders. **This is the unit that carries HYP.137's live consumption.**

> “2. **The hExhaust program** — n = 2 exact (W-11), n = 3: DBL term
>    exact (W-12.C) + TRP residue exact-in-convention with vanishing
>    σ-bound (HEX3.A/B). W-12.B's shape (c_n(q)·q^{(n−1)N} order) is
>    now corroborated at n = 3 with c₃ head 1·q^{2N−2}·q/q^{2N}... the
>    normalized head U₃^conv/q^{2N} = q^{−1}(1 + o(1))·
>    (1 + Θ(N(q−1)²q^{−3})) = q^{−1}(1 + o(1))(1 + Θ(N/q)) — NOTE: u
>    has an N-linear subleading family (the R-tails): the exact k = 1
>    N-linear mass of U₃^conv is ⌊(N−4)/2⌋(q−1)²q^{2N−4}·(1 −
>    q^{−(N−3)}) (+ smaller k ≥ 2 terms) [r2, PE2 m1: the main line
>    had displayed "exact ... ⌊(N−4)/2⌋(q−1)²q^{2N−4} (+ smaller
>    k ≥ 2 terms)", dropping the (1 − q^{−(N−3)}) factor — 1024 at
>    (2,7) against the [r1] re-check's own correct 960; the −q^{N−1}
>    correction is the k = 1 term's own (the (q^{N−3} − 1) factor of
>    the law's k = 1 summand), not a "smaller k ≥ 2 term"; Θ-claims
>    unchanged], so the conservative residue sits
>    Θ(N(q−1)²·q^{2N−4}) above its head [r1, PE1 m2: the sealed aside
>    dropped the (q−1)² — "Θ(N·q^{2N−4})" / "(1 + Θ(Nq^{−3}))"
>    understated the joint (N,q) relative rate by (q−1)² ≈ q²; the
>    corrected relative rate Θ(N/q) matches S5.3's own rigorous bound
>    1 + N/(2(q+1)); re-checked at (2,7): whole-space N-linear mass
>    ⌊3/2⌋(q−1)²q^{10}(1 − q^{−4}) = 960 exactly] — consistent
>    with W-12.B IF this SPLIT-TAIL-type mass belongs to (A2)'s
>    boundary-family (σ-certified) component: at n = 2 that membership
>    is W-11-PROVED (W-12 S3.4's r(N) display), and the n = 3 DBL
>    analogue is proved (W-12 r2's G2 leg — W-11 certification through
>    W12-L1(c), no scaling), but for the transported TRP mass here it
>    is precisely HEX3-BOX-1's OPEN tail-σ-certification lemma (the σ_m
>    transport loses ghost digits — exactly why BOX-1 is open). The
>    price if it fails: an uncertified mass sits in U₃^σ, and
>    undecided(3,q,N)·q^{−2N} then diverges linearly in N (all-k slope
>    (q−1)/(2q²(q+1)), = 1/24 at q = 2; under S5.3's rigorous excess
>    bound, slope 1/(2q(q+1))) — W-12.B would be FALSE at n = 3. Under
>    W-12's r3 σ-pin (b17238a, the BOX-7 lift-certification notion) the
>    ROBUST reading is the one the PE4 cross-note check verified
>    positively (HEX3_passPE4_report.md, charge 2): U₃^conv =
>    (σ-undecided TRP) ∪ (certified TRP boundary tails) EXACTLY, so
>    THEOREM HEX3.B's bound dominates BOTH r(3,N) TRP legs however
>    BOX-1 resolves — the (hExhaust-3) discharge never needed the
>    split; only this aside's W-12.B corroboration is conditional on
>    it. [r3, PE4 m1: the sealed clause read "consistent with W-12.B
>    only because the SPLIT-TAIL-type mass belongs to (A2)'s boundary
>    families, exactly as at n = 2" — asserting AS FACT the
>    σ-decidedness of the transported TRP SPLIT-TAIL mass, which is
>    exactly BOX-1's open lemma, and conflating the PROVED DBL side
>    with the OPEN TRP side; conditionalized, divergence price
>    displayed, pin-robust route cited; arithmetic re-verified at
>    repair: (2,7) mass 960 from the k = 1 summand, slope 1/24 at
>    q = 2 numeric at N = 200, S5.3 domination exact.]”

**DERIVATION.** [RECORD of a corroboration aside] — explicitly conditionalized by `[r3]`.

**CHAIN (rule 25 — three layers on one aside).** sealed “consistent with W-12.B only because …” (asserting the open lemma as fact) → `[r1]` m2 (the `(q−1)²` rate repair) → `[r2]` m1 (the `(1 − q^{−(N−3)})` factor restored) → `[r3]` m1 (the whole consistency clause **conditionalized**). **TERMINAL: `[r3]`.** **SUPERSESSION KINDS, in order:** `wording-rider` (r1, a rate correction), `replacement` (r2, a wrong display replaced), `scope-pin` (r3, a fact demoted to a conditional). Three different kinds; conflating them would corrupt the DAG differently each time (rule 18).

**Mandatory arithmetic audit (rule 22) — the aside's four numbers recomputed.**
1. **The `k = 1` N-linear mass at `(2,7)`.** Whole-space: `⌊(7−4)/2⌋·(2−1)²·2^{2·7−4}·(1 − 2^{−4}) = 1·1·1024·(15/16) = 960` ✓ — the `[r2]` bracket's figure, and the struck form (without the factor) gives `1024` ✓, exactly the discrepancy the bracket reports.
2. **Cross-check against Correction E's per-centre form.** Correction E displays the same mass as `⌊(N−4)/2⌋(q−1)²q^{2N−5}(1−q^{−(N−3)})`, one power of `q` lower. **This is not a discrepancy:** `.55`'s display is whole-space (`U₃^conv = q·u`) and Correction E's is per-centre (inside `u`). At `(2,7)`: per-centre `480`, whole-space `960` ✓. Recorded because the two exponents `q^{2N−4}` and `q^{2N−5}` sit 350 lines apart and read as a contradiction to anyone who does not carry the `×q` convention.
3. **The all-k slope `(q−1)/(2q²(q+1))` = 1/24 at `q = 2`.** `(2−1)/(2·4·3) = 1/24` ✓.
4. **S5.3's rigorous-bound slope `1/(2q(q+1))`.** At `q = 2`: `1/12`; and S5.3's excess is `N/(2(q+1))` on `u/q^{2N−2}`, i.e. `q^{−2}·N/(2(q+1)) = N/(2q(q+1))` on `u/q^{2N}` ✓ — the two slopes are consistently derived, and `1/12 > 1/24`, so the rigorous bound dominates the all-k slope, exactly as the `[r3]` bracket claims (“S5.3 domination exact”) ✓.

**CONDITIONALITY — the live one.** This aside's W-12.B corroboration is **conditional on the OPEN HEX3-BOX-1 tail-σ lemma**, and the note says so in the sentence HYP.137 quotes:

> “the (hExhaust-3) discharge never needed the
> split; only this aside's W-12.B corroboration is conditional on
> it.”

The failure price is displayed in the same span (“undecided(3,q,N)·q^{−2N} then diverges linearly in N … W-12.B would be FALSE at n = 3”). The pin-robust route (PE4 charge 2) means **THEOREM HEX3.B is unaffected either way**. This is precisely the separation HYP.137's disposition turns on — see `.37` and §5.3.

**XREF.** `W12_PROOF_2026-08-08.md` — `W-12.B`, count 7 (**NEAR-MISS on the fuller form**: `THEOREM W-12.B` has count **0**, because the supplier's designation is `CONJECTURE W-12.B`, verified at L233 “* **CONJECTURE W-12.B (DRAIN-n), stated precisely.**” — the compiler emits the bare `W-12.B`, count 7, and records that any consumer writing “THEOREM W-12.B” is wrong: it is a **conjecture**); `W12-L1(c)`, count 6; `S3.4`, count 11; `W12-BOX-7`, count 10. Artifact `lean/notes/openmath/HEX3_passPE4_report.md` — EXISTS. Commit `b17238a` — VERIFIED.

---

### EFF.HEX3.56  [scope-record]

**CANONICAL STATEMENT** (verbatim, S8.2 item 3, L703–706). FORM: numbered bulleted display.

> “3. **Phase-B Lean** — the law is a single-recursion integer family:
>    a `hex3Law` evaluator + the 46-row table is a cheap Lean-side
>    certificate target once the (hMenu-3) side stabilizes
>    (math-first discipline: Lean waits).”

**DERIVATION.** [RECORD of a formalization work order].

**CONDITIONALITY.** The stated precondition — `(hMenu-3)` stabilizing — is satisfied corpus-side by the ACCEPTED HMENU3. Whether that promotes this item is not decidable from HEX3's text and is not decided here.

**XREF.** `HMENU3_PROOF_2026-08-08.md` — `HM3.A`, count 18. **No Lean declaration `hex3Law` exists at HEAD:** `grep -rF 'hex3Law' --include='*.lean' .` returns **0**; the single repo-wide hit under `lean/` is this note's own sentence. Consistent with the unit's own “Lean waits”; recorded so a blueprint does not go looking for it.

---

### EFF.HEX3.57  [table]

**CANONICAL STATEMENT** (verbatim, S9 L708–729 — the conditionality stack). FORM: bulleted display.

> “* **THEOREM W-11(n = 2)** @ seal 7020ceb / verdict cb05127 / r2 HEAD
>   31506b3 — clause (iii) (undecided aggregate q^{M−1}), the SPLIT-TAIL
>   aggregate, S2.3's refine isomorphism (consumed through W12-L0).
> * **W-12 suppliers** @ seal f669cb0 / verdict c16c717 / adjudication
>   97122f2: LEMMA W12-L0 (history-resolved laws + bracket — S4 here),
>   LEMMA W12-L1(a)(b) (DBL product bijection + read equivalence — the
>   β-transports' engine), S2.4 depth-0 completeness (the partition),
>   THEOREM W-12.C (the identity this unit's B closes into), W12-BOX-3/7
>   (the convention definition). The w12 instrument consumed at its
>   sealed bytes (md5 pins in the runner).
> * **LEMMA J-D0** @ 1642275/9387eb1 — the gauge-blindness frame behind
>   HEX3.C (corroborated, not load-bearing for the counts: the S2–S5
>   arguments are self-contained slot counts).
> * **This note's own lemmas** H-1..H-4 + the S5 assembly — new, graded
>   0/2, machine leg as displayed.
> * **Classical:** Hensel (via W12-L1), Ore (via W-12 S2.3, only for the
>   DEC families' decidedness), lower-hull geometry.
> * **NOT consumed:** the weld notes ([W12-H] untouched — everything
>   here is order-1 digit calculus), PARI (no new oracle rows), the
>   measure route, `htameFE`.”

`[TABLE]` (compiler transcription — the source form above is the governing text; this is the DAG-keyed view)

| supplier | pins | consumed content | load-bearing? |
|---|---|---|---|
| THEOREM W-11 (n = 2) | seal `7020ceb` / verdict `cb05127` / r2 HEAD `31506b3` | clause (iii); the SPLIT-TAIL aggregate; S2.3's refine isomorphism (through W12-L0) | YES — `.26`, `.21` |
| W-12 suppliers | seal `f669cb0` / verdict `c16c717` / adjudication `97122f2` | LEMMA W12-L0; LEMMA W12-L1(a)(b); S2.4 completeness; THEOREM W-12.C; W12-BOX-3/7 | YES — `.13`, `.19`, `.26`, `.31` |
| LEMMA J-D0 | `1642275` / `9387eb1` | gauge-blindness frame | NO — corroborative only |
| HEX3's own H-1..H-4 + S5 | — | new | YES |
| Classical | — | Hensel (via W12-L1); Ore (via W-12 S2.3, DEC families only); lower-hull geometry | YES |
| NOT consumed | — | weld notes / `[W12-H]`; PARI; the measure route; `htameFE` | — (negative fence N-1) |

**DERIVATION.** [RECORD].

**PIN VERIFICATION (rule 23) — all seven commit pins.** `7020ceb`, `cb05127`, `31506b3`, `f669cb0`, `c16c717`, `97122f2`, `1642275`, `9387eb1` — **all eight resolve to `commit`** ✓.

**CONDITIONALITY.** “graded 0/2” for the note's own lemmas is `STALE-SELF-DESCRIPTION`. The Ore scope pin (“only for the DEC families' decidedness”) is the fence that keeps `.06`'s `[r4]` repair local.

**XREF.** as listed; all designations grep-verified at `.13`, `.19`, `.21`, `.26`, `.31`, `.32`.

---

### EFF.HEX3.58  [record]

**CANONICAL STATEMENT** (verbatim, S9 L731–734). FORM: bold-headed paragraph.

> “**One line: THEOREM HEX3.A's hypothesis set = {W-11 @ pins, W12-L0/L1
> + S2.4 @ pins, this note's transport lemmas}; HEX3.B = {HEX3.A +
> W-12.C @ pin}; HEX3.C = {HEX3.A's proof, inspected}. No axiom, no
> weld face, no oracle.**”

**DERIVATION.** [RECORD] — the note's own one-line hypothesis ledger, and the most citable single sentence for a chapter cut.

**CONDITIONALITY.** Current and unqualified by any append. Note what it does NOT say: it does not claim HEX3-BOX-1 is discharged, and it does not list HEX3-BOX-1 as a hypothesis of A, B or C — consistent with the aside-only consumption recorded at `.55` and with HYP.137's disposition.

**XREF.** none new.

---

### EFF.HEX3.59  [run-record]

**CANONICAL STATEMENT** (verbatim, S10 L739–745). FORM: bold-headed paragraph.

> “**GREEN. 158,512 checks, 0 violations in every family, all three teeth
> fired at their EXACTLY-preregistered counts, zero skips.** 46/46 rows
> (67,410,225 per-center states read individually; 21 ℤ_p + 25
> 𝔽_q[[t]]), single fresh run, elapsed 326.9 s, exit 0; artifacts
> `hex3_checks_output.txt` (md5 6e4b3207562d8ba93811d77ab41f0391),
> `hex3_checks_results.json` (md5 ce6f41162a22b0bd66a641e98cb4d56e);
> runner byte-identical to the sealed commit e3f3459 (empty `git diff`).”

**DERIVATION.** [RECORD of an executed instrument] — a `run-record` in the rule-19 sense, distinct from the `preregistration`s `.45`–`.51` and the `instrument-record` `.42`.

**Mandatory arithmetic audit (rule 22).** The per-family check counts reported in the scorecard (`.60`) must sum to the headline 158,512: `PIN 4 + LAW 92 + SPECIES 172 + XREAD 158,204 + W12TIE 23 + CHAR 17` = **158,512** ✓ — exact. Row count `21 + 25 = 46` ✓; state count recomputed **67,410,225** ✓.

**PIN VERIFICATION.** Both artifact md5s reproduce EXACTLY at HEAD ✓; `e3f3459` is a commit ✓; the runner's md5 `83faf7ed…` (given in the later rider) also reproduces ✓.

**CONDITIONALITY.** Scoped by **Correction C** in exactly one respect: the run exercises only roster-realized depth-0 keys.

**XREF.** artifacts as above, all EXIST and VERIFY.

---

### EFF.HEX3.60  [table]

**CANONICAL STATEMENT** — the S10 prediction scorecard, L747–783, quoted in the source's bulleted form for P-1's corrected census (already emitted at `.45`) and transcribed here as the DAG view. FORM: bulleted display (source) + `[TABLE]` (compiler transcription).

Source header line, verbatim (L747):

> “Prediction scorecard (all seven confirmed):”

`[TABLE]`

| prediction | family | result | checks / detail |
|---|---|---|---|
| P-1 [the law] | HEX3-LAW | ✓ 0 violations, all 46 rows | 92 checks; every value in the census hit exactly; census corrected `[r1]`→`[r2]` (`.45`) |
| P-2 [species] | HEX3-SPECIES | ✓ 0 violations, both directions, 46 rows | 172 checks; all preregistered spot values hit |
| P-3 [seal tie] | HEX3-XREAD | ✓ 0 divergences | 158,204 pointwise states |
| P-4 [committed tie] | HEX3-W12TIE | ✓ 23/23 | retro-predicts the w12 EXPLORATORY column |
| P-5 [char] | HEX3-CHAR | ✓ 17/17 pairs | FULL species tallies identical across ring types |
| P-6 [teeth] | T-FLOOR / T-ALPHA / T-VERT1 | ✓ 10 / 20 / 13 | every count exactly as preregistered |
| P-7 [falsifiers] | — | ✓ none fired | “nothing to diagnose upstream” |

**Mandatory arithmetic audit (rule 22).** Column of check counts sums to the headline (see `.59`) ✓. The three tooth counts equal the preregistered values recomputed from the roster at `.50` ✓. The 17 CHAR pairs equal the recomputed shared-pair count ✓. The 23 W12TIE rows equal the committed w12 cubic-row count asserted at `.42` ✓ (internally consistent; the external count is at the pinned JSON, whose md5 verifies).

**DERIVATION.** [RECORD].

**CONDITIONALITY.** P-1's row carries the census CHAIN's TERMINAL reading (`[r2]`); P-4's row must be read with the fit disclosure (`.48`).

**XREF.** none new.

---

### EFF.HEX3.61  [record]

**CANONICAL STATEMENT** (verbatim, S10 L785–832 — the consequence-for-the-grade-box paragraph, with its three arc brackets). FORM: bold-headed paragraph with nested `[r1]`/`[r2]`/`[r3]` arc brackets. Opening, verbatim:

> “**Consequence for the grade box:** THEOREM HEX3.A (the exact U₃^conv
> law) and THEOREM HEX3.B (the (hExhaust-3) vanishing bound) stand as
> composed, machine-sealed on 46 rows both characteristics with the
> species decomposition confirmed term by term — the per-key design
> means a ledger error in ANY transport route would have surfaced as an
> integer mismatch, and none did; COROLLARY HEX3.C confirmed at tally
> granularity.”

and closing, verbatim (L829–832):

> “the σ-residue exact law remains open exactly at
> the tail-σ-certification lemma (HEX3-BOX-1) — W-13's floor together
> with (hMenu-3) = W12-BOX-2.”

*(The three intervening `[r1]`/`[r2]`/`[r3]` arc brackets, L792–829, are the arc chronology; they are superseded wholesale by `.63` and are not re-quoted here. Their content is recoverable at the cited lines.)*

**DERIVATION.** [RECORD].

**SERIES membership.** ARC SERIES member 3 (see `.33`).

**CONDITIONALITY — three distinct supersessions on one paragraph.**
1. **The arc brackets** are superseded by `.63` (the ARC line names “§S10” as its third target) and then `.64`. KIND: `replacement`.
2. **The per-key guarantee** (“a ledger error in ANY transport route would have surfaced as an integer mismatch”) is superseded by **Correction C** (`.67`). KIND: `scope-pin`.
3. **The closing residence clause** (“W-13's floor together with (hMenu-3) = W12-BOX-2”) is superseded by **Correction A** (`.65`), which establishes that the lemma was never part of `(hMenu-3)`. KIND: `replacement`. **This third target is NOT named in Correction A's own site list** (which names S0 L104–105, BOX-1 L447–449, and S8.2 item 1) — the compiler records it as an in-scope consequence of Correction A's finding, flagged rather than silently applied. See OPEN-CALL 1.

**TARGETS (rule 24).** `.33`, `.38` (arc); `.25`, `.38`, `.59` (Correction C); `.36`, `.37`, `.54` (Correction A).

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-2`, count 8.

---

### EFF.HEX3.62  [changes-record]

**CANONICAL STATEMENT** (verbatim, the 2026-08-09 post-PE6 rider, Correction 1, L849–877). FORM: bold-headed paragraph.

> “**Correction 1 (PE6 m1 — the HEX3-BOX-1 mechanism gloss).** The BOX-1
> clause "every drain event happens inside a transported W-11 block
> frame" (S6) is FALSE and is superseded by the drain typology that
> S5.1's own table enumerates, three genres by row:
> (i) **B0ZERO drains** — the reader exits UNDECIDED at the TRP frame
> itself (drained column q^{2N−2}, the DOMINANT drained mass; no block
> frame); (ii) **α-chain drains** — exit at an α-recentered scaled TRP
> frame (drained column (q−1)q^{3k}·u(N−3k), recursively the scaled
> window's own three genres, bottoming out in B0ZERO/seed exits; no
> block frame on the B0ZERO-terminated chains); (iii) **β-route
> drains** — only the three R(M)-carrying rows (FULL11SQ, VERT1, VERT2)
> drain inside transported W-11 block frames. Witness, quoted from the
> committed `hex3_checks_results.json` row (kind Zp, q = 2, N = 4):
> states 512, u_measured 72 = u_law; species_tally B0ZERO [64, 64] +
> ALPHA(1) [8, 8] + DECIDED [440, 0], no β key realized — genres
> (i) + (ii) carry 100% of that committed row's 72 drains (64 + 8),
> zero W-11 block frames, refuting the sealed clause at that row. The
> same sentence's certifiable-candidates list already names the B0ZERO
> leg and stands. Its trailing shorthand ("a certification lemma would
> turn the same species table into the U₃^σ law by replacing R with its
> certified/uncertified split") under-covers genre (i) and is corrected
> to: replacing EACH drained column of the S5.1 table with its
> certified/uncertified split — the R-split covers only the three R(M)
> rows; the B0ZERO row's drained column is q^{2N−2}, not an
> R-expression, and its own split (exactly BOX-3's visible-B₁-vertex
> question) is ALSO needed for the U₃^σ law, with the ALPHA rows taking
> the scaled window's split recursively. Seal-era text, unflagged by
> PE1–PE5; blast radius zero on HEX3.A/B/C and the S5.1 table (PE6
> verified: no theorem, count, or consumer consumes the clause).”

**DERIVATION.** The refutation is a **single committed-artifact witness row**, quoted from the frozen JSON: `(Zp, 2, 4)` has 72 drains, all in genres (i)+(ii), zero block frames.

**SUPERSESSION KIND:** `replacement` (twice: a false clause, and an under-covering shorthand). **TARGETS:** `.37` (the BOX-1 mechanism clause and its trailing shorthand).

**AUDIT disposition (rule 27).** `in-house hostile pass` — this finding could not have been produced by any tooth of the battery: the battery checks per-key `(locus, drained)` integers and never asks *which frame* a drain happens in. The note's own words record the coverage hole: “Seal-era text, unflagged by PE1–PE5”.

**Mandatory arithmetic audit (rule 22) of the witness row.** `(Zp, q = 2, N = 4)`: states `q^{3(N−1)} = 2^9 = 512` ✓. `u(2,4) = q^6 + (q−1)²q³ = 64 + 8 = 72` ✓. B0ZERO locus `q^{2N−2} = 2^6 = 64`, all drained ✓. ALPHA(1) locus `(q−1)q^{3N−3−6} = 1·2^3 = 8`, drained `(q−1)q^3u(1) = 8` ✓. DECIDED `512 − 64 − 8 = 440`, drained 0 ✓. Genre sum `64 + 8 = 72` = 100% of drains ✓. β keys at `N = 4`: FULL11SQ needs `q ≥ 3` (zero at `q = 2`); VERT1 needs `3k < u₀ ≤ N−1 = 3`, impossible for `k ≥ 1`; VERT2 needs `u₀ > 3t ≥ 3` and `u₀ ≤ 3`, impossible — **so “no β key realized” is provable, not merely observed** ✓. The witness is sound in every particular.

**CONDITIONALITY.** Genre (i)'s “DOMINANT” is then scope-pinned by `.66`, and the justification of its asymptotic behaviour replaced by `.69`. See `.37`'s CHAIN.

**XREF.** artifact `verification/openmath/hex3_checks_results.json` — EXISTS, md5 `ce6f4116…` VERIFIED. `lean/notes/openmath/HEX3_passPE6_report.md` — EXISTS, md5 `42d86c7a…` VERIFIED.

---

### EFF.HEX3.63  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction 2 and the ARC line it installs, L879–907). FORM: bold-headed paragraph introducing a blockquoted display.

> “**Correction 2 (PE6 m2 — the arc record cured by one dated line).**
> The r4 repair updated its two repair sites but not the three arc
> record sites; at the sealed body above, the header grade block, the
> HEX3-BOX-2 record, and §S10's [r3] bracket each still end "…counter
> 0/2; PE5 next" / "r3 applied, counter 0/2 [r3]". Those three endings
> are superseded by this single dated arc line:
>
> > **ARC (dated 2026-08-09; supersedes the three r3-era record
> > endings — header, HEX3-BOX-2, §S10):** → PE5 NOT CLEAN 0C+0G+2m @
> > 5919e2f (target r3 @ b6a1d69; m1 = the S0 "every lift" Ore-warrant
> > over-claim struck by W-12's own r4, m2 = the S3.2-species
> > parenthetical's category slip; machine leg isolated GREEN
> > 158,512/0; fresh route ~149B states / 27 rows exact incl. (2,12)
> > and (16,4) at the preregistered 17,698,816) → r4 @ fa7b70d
> > (note-only, [r4] tags at S0 + S6, minimality contract; runner +
> > artifacts byte-frozen at seal e3f3459) → PE6 CLEAN under the charge
> > bar 0C+0G+2m @ d9c5ef8 (nothing GAP-or-worse; counter 0/2 → 1/2;
> > the PE4/PE5-era any-finding reading — NOT CLEAN, counter 0/2 — was
> > displayed for adjudication, and the wave-16 orchestrator
> > adjudication AT THE LEDGER (91ec856) ruled the charge bar the
> > standing convention, so the count HOLDS AT 1/2, minors-only
> > precedent; r4 lines verified faithful clause by clause; (A2)
> > handoff faithful at W-12 HEAD; machine leg isolated GREEN
> > 158,512/0; fresh route = the arc's first PARI/σ leg, wild cell
> > (Zp, 3, 4) end-to-end, 58,158 oracle lifts, 0 pin / 0 read-tie
> > violations, 27/27 S3.2 species members ambiguous) → r5 = THIS RIDER
> > (dated corrections, append-only; PE6 m1 + m2 repaired above; sealed
> > body + runner + artifacts + PE6 report byte-frozen, md5s displayed
> > in the rider head); counter 1/2; PE7 next.”

**DERIVATION.** [RECORD].

**SERIES membership.** ARC SERIES member 4 — the member that supersedes members 1–3 (`.33`, `.38`, `.61`). **SUPERSESSION KIND:** `replacement`, scoped to the three record endings only. **TARGETS:** `.33`, `.38`, `.61`.

**Arithmetic audit.** The fresh-route figure “(16,4) at the preregistered 17,698,816” was recomputed: `u(16,4) = 16^6 + (16−1)²·16³ = 16,777,216 + 921,600 = 17,698,816` ✓ **exactly** — note this is the **per-centre** `u`, not the whole-space `q·u` (which would be `283,181,056`). The same convention holds for the PE5 row `(2,12)`: `u(2,12) = 7,936,000` (per-centre) ✓, which is the figure Correction B then quotes. Recorded because the P-1 census (`.45`) reports **whole-space** values, so the two families of numbers in this note use different conventions in different places — see §7's convention finding.

**CONDITIONALITY.** Superseded in turn by `.64` (the acceptance record takes the counter from 1/2 to 2/2). **PIN VERIFICATION:** `5919e2f`, `b6a1d69`, `fa7b70d`, `d9c5ef8`, `91ec856` — **all five VERIFIED** as commits ✓. The charge-bar adjudication is externally located: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` EXISTS ✓.

**XREF.** `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` — EXISTS (the wave-16 fold @ `91ec856`).

---

### EFF.HEX3.64  [acceptance-box]

**CANONICAL STATEMENT** (verbatim, L913–924). FORM: bold-headed paragraph.

> “**ACCEPTANCE.** PE6 CLEAN under the charge bar @ d9c5ef8 (adjudicated
> 91ec856) + PE7 CLEAN under the charge bar @ 237c753 (0C + 0G + 2m;
> `HEX3_passPE7_report.md`, md5 4049109c272617c10acb62f77fbf0c2e,
> byte-frozen) — counter 1/2 → 2/2: **HEX3 is ACCEPTED** (the fifth
> chain note through the bar). This note is FROZEN: dated appends only.
> Everything above this heading — sealed body L1–832, the post-PE6
> rider, the arc line — is byte-untouched by this append (pre-append
> file md5 b92f47a8895f8c7040c8fe9d7db4473d is the prefix); runner +
> artifacts stay at seal e3f3459. PE7's machine leg: isolated GREEN
> 158,512/0; PE7's fresh route: 53 (ring, q, M) cells ≈ 2.9B states,
> 0 violations, R(M) measured to M = 16 at q = 2 (both ring types) and
> at first-ever q ∈ {7, 11, 13, 25}. The two PE7 MINORs land here.”

**DERIVATION.** [RECORD of an acceptance].

**SERIES membership.** ARC SERIES member 5 — **TERMINAL for the acceptance counter** (superseded only in *ledger status*, not in counter, by `.71`).

**SUPERSESSION KIND:** `replacement` of every prior grade statement in the note. **TARGETS:** `.11` (the S1 GRADE box), `.33` (header), `.38` (BOX-2), `.57` (“graded 0/2”), `.61` (§S10), `.53`'s “(attempt 0/2)”.

**CONDITIONALITY.** The acceptance is **under the charge bar** — the wave-16 adjudicated convention that “nothing GAP-or-worse = CLEAN” — and both passes carried 2 minors each. A consumer citing “2/2 clean” must carry the bar, since under the older any-finding reading both passes were NOT CLEAN. The note is explicit about this at `.63`. **PIN VERIFICATION:** `237c753`, `d9c5ef8`, `91ec856`, `e3f3459` all VERIFIED as commits ✓; the PE7 report md5 VERIFIED ✓; the prefix md5 **VERIFIED and localized to line 907 / byte 53,951** ✓.

**XREF.** `lean/notes/openmath/HEX3_passPE7_report.md` — EXISTS, md5 matches.

---

### EFF.HEX3.65  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction A, L926–945). FORM: bold-headed paragraph.

> “**Correction A (PE7 m1 — the "tail half of (hMenu-3)" residence).**
> The attribution at S0 L104–105 and HEX3-BOX-1 L447–449 ("it is the
> tail half of (hMenu-3), W-13's floor"), echoed in S8.2 item 1's
> ingredient list ("the same three routes + the certification lemma"),
> is superseded: the tail-σ-certification lemma was never part of
> (hMenu-3). Verified against the two suppliers' frozen texts at this
> append: (a) W12-BOX-2 (W12_PROOF L1218–1224) defines (hMenu-3) as
> exactly the two node-species transfer laws — (α) the triple-cluster
> node and (β) the DBL-re-entry node at reduced window — with no
> tail-certification content; the lemma is named in W12-BOX-3's
> obstruction (L1225–1235) for the σ-side U₃^TRP law. (b) The ACCEPTED
> HMENU3 discharged (hMenu-3) in full WITHOUT the lemma, and says so
> (HMENU3 S5.4 L465–467: "The tail-σ-certification lemma remains what
> it was: the missing piece of the exact U₃^σ law ONLY (HEX3-BOX-1,
> inherited open, price unchanged)"). Corrected reading: HEX3-BOX-1's
> lemma = the missing piece of the exact U₃^σ law only; (hMenu-3) is
> discharged without it; S8.2-1's ingredient list drops the
> certification lemma for the depth-≥1 DECIDED-family laws (HM3.A
> proved them via this note's transports alone). BOX-1's open price is
> unchanged.”

**DERIVATION.** A two-source textual verification, both legs re-verified here.

**LINE-CITE VERIFICATION (compiler-performed, rule 23 extended).** (a) `W12_PROOF_2026-08-08.md` **L1218–1224** is exactly the W12-BOX-2 bullet, beginning “* **W12-BOX-2 (n ≥ 3 refinement families; (hMenu-3)).**” at L1218 and ending “floor.” at L1224 ✓ — the cite is exact to the line, and the box's content is exactly the two node species with no tail-certification content ✓. **L1225–1235** is exactly the W12-BOX-3 bullet ✓ (verified independently at `.35`). (b) `HMENU3_PROOF_2026-08-08.md` **L465–467** carries the quoted sentence ✓ (the fixed string is line-wrapped in the source, so a naive `grep -cF` on the full sentence returns **0**; **NEAR-MISS disposition** per rule 15 — the referent is verified at `HMENU3_PROOF_2026-08-08.md:465–467` under the wrapped form “The\ntail-σ-certification lemma remains what it was: the missing piece of\nthe exact U₃^σ law ONLY (HEX3-BOX-1, inherited open, price\nunchanged).”, and `grep -cF 'HEX3-BOX-1'` in that file = 7). **Both legs of Correction A verify.**

**SUPERSESSION KIND:** `replacement`. **TARGETS:** `.36` (S0 L104–105), `.37` (BOX-1 L447–449), `.54` (S8.2 item 1), and — flagged, not silently applied — `.61` (S10's closing residence clause, which repeats the same attribution but is not in Correction A's site list; see OPEN-CALL 1).

**AUDIT disposition (rule 27).** `transfer audit` — the finding is a mis-attribution across three notes that no HEX3 tooth could detect, produced by reading the suppliers' frozen texts.

**CONDITIONALITY.** “BOX-1's open price is unchanged” — the correction moves the lemma's *residence*, not its status. HYP.137 remains MATH.

**XREF.** `W12_PROOF_2026-08-08.md` — `W12-BOX-2`, count 8; `W12-BOX-3`, count 7; L1218–1224 and L1225–1235 verified. `HMENU3_PROOF_2026-08-08.md` — `HEX3-BOX-1`, count 7; `HM3.A`, count 18; L465–467 verified (NEAR-MISS on the wrapped fixed string).

---

### EFF.HEX3.66  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction B, L947–969). FORM: bold-headed paragraph closing with a quoted replacement clause.

> “**Correction B (PE7 m2 — the rider's "DOMINANT drained mass"
> superlative, L854, scoped).** Genre (i)'s clause "the DOMINANT
> drained mass" holds at the rows the arc measured — the two boundary
> fractions: the deepest committed row (Zp, q = 2, N = 9) has B0ZERO
> 65,536 of u = 103,168 drains = 63.5%, and the arc's deepest
> fresh-route row (PE5's (Fqt, 2, 12)) has 4,194,304 of 7,936,000 =
> 52.8% — but it is FALSE in the N → ∞ regime THEOREM HEX3.B is about:
> u(q, N) = q^{2N−2}(1 + Θ(N/q)) (S5.3's own excess; S8.2-2's N-linear
> display), so B0ZERO's fraction q^{2N−2}/u → 0 at fixed q. Crossover,
> RE-DERIVED at this append from the S5.1/S5.2 closed forms (evaluator
> validated against the committed anchors u(2,4) = 72, u(2,7) = 5664,
> u(3,4) = 837 and both measured fractions above): at q = 2, B0ZERO's
> share of u(N) first drops below 1/2 at N = 14 (0.4846; N = 13 is
> 0.5186), and the β genre (the three R(M)-carrying rows) alone first
> exceeds B0ZERO at N = 18 (ratio 1.1042; N = 17 is 0.9771); the α
> column alone overtakes only at N = 77 (1.0036; N = 76 is 0.9862) —
> these exact values supersede the PE7 report's coarse "N ≈ 45 even
> the α genre alone" aside (its Θ-claims stand). Corrected clause:
> "(i) B0ZERO drains — … drained column q^{2N−2}, the dominant drained
> mass at each row the arc measured (boundary fractions 63.5% at
> (Zp,2,9) committed, 52.8% at (Fqt,2,12) fresh); the R-carrying β
> rows overtake it from N = 18 on at q = 2 and its fraction → 0 as
> N → ∞ per S5.3 — no block frame".”

**DERIVATION.** A recomputation from the S5.1/S5.2 closed forms, with the evaluator validated against three committed anchors.

**SUPERSESSION KIND:** `scope-pin` (a superlative is scoped to the measured rows and its asymptotic falsity displayed). **TARGETS:** `.62` genre (i) — i.e. the second layer of `.37`'s CHAIN.

**Mandatory arithmetic audit (rule 22) — every number in this correction independently recomputed.** `u(2,9) = 103,168` ✓ and B0ZERO `= 2^{16} = 65,536`, share `= 0.6352 = 63.5%` ✓. `u(2,12) = 7,936,000` ✓ and B0ZERO `= 2^{22} = 4,194,304`, share `= 0.5285 = 52.8%` ✓. Anchors `u(2,4) = 72`, `u(2,7) = 5664`, `u(3,4) = 837` ✓. **Crossovers, recomputed by an independent genre decomposition** (`B0ZERO + α-column + β-columns = u(N)`, verified as an exact integer identity at every `N` tested): B0ZERO share `N = 13` → `0.51861` ✓ (source: 0.5186), `N = 14` → `0.48463` ✓ (source: 0.4846); β/B0ZERO ratio `N = 17` → `0.9771` ✓, `N = 18` → `1.1042` ✓; α/B0ZERO ratio `N = 76` → `0.9862` ✓, `N = 77` → `1.0036` ✓. **All eight crossover figures reproduce to four decimal places.** This is the single most arithmetic-dense claim in the note and it is exactly right.

**TEETH disposition (rule 20).** `stale self-description` — the frozen rider's own superlative is falsified by the note's own asymptotics.

**CONDITIONALITY.** The justification clause “its fraction → 0 as N → ∞ per S5.3” inside the corrected clause is itself superseded by `.69` — layer 4 of `.37`'s CHAIN.

**XREF.** `lean/notes/openmath/HEX3_passPE7_report.md` — EXISTS, md5 VERIFIED (the “N ≈ 45” aside this correction supersedes lives there).

---

### EFF.HEX3.67  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction C, L985–997). FORM: bold-headed paragraph with three LaTeX displays.

> “**Correction C (2026-08-12 — RATIFICATION annex item 1: scope of the sealed species battery).** The HEX3-BOX-2/S10 claim that “46 rows × every realized key” means “a ledger error in ANY route would surface as a per-key integer mismatch” is superseded by the following scoped statement: the sealed 46-row battery would surface every ledger error affecting a depth-0 key realized on its roster. It does not test arbitrary depths. Indeed the roster has \(N\le 9\), while the ranges in LEMMA H-1 give
> \[
> \alpha(3):\ 3\cdot3\le N-1\Longrightarrow N\ge10,
> \]
> \[
> \beta_2(k=3):\ 9<u_0\le N-1\Longrightarrow N\ge11,
> \]
> and
> \[
> \beta_3(t=3):\ u_0>9,\quad u_0\equiv3\pmod2
> \Longrightarrow u_0\ge11,\ N\ge12.
> \]
> None of these keys occurs in the sealed roster, so an error confined to such an uninstantiated depth need not produce a sealed per-key mismatch. The all-depth formulas rest on the uniform slot-count and transport proofs in S2–S3; the machine leg confirms those formulas only at the realized keys. No theorem statement, count, or consumer changes.”

**DERIVATION.** Three range computations from LEMMA H-1's own conditions, checked against the roster maximum `N = 9`.

**Mandatory arithmetic audit (rule 22) — all three ranges re-derived from `.13`.** α at `k = 3`: H-1 requires `3k ≤ N−1`, so `9 ≤ N−1 ⟹ N ≥ 10` ✓. β₂ at `k = 3`: H-1 requires `3k < u₀ ≤ N−1`, so `9 < u₀ ≤ N−1 ⟹ u₀ ≥ 10 ⟹ N ≥ 11` ✓. β₃ at `t = 3`: H-1 requires `u₀ > 3t = 9` and `u₀ ≡ t (mod 2)`, i.e. `u₀` odd, so `u₀ ≥ 11`, and `u₀ ≤ N−1 ⟹ N ≥ 12` ✓. Roster maximum `N = 9` recomputed from `.43` ✓. **All three implications are exact and the conclusion follows.**

**SUPERSESSION KIND:** `scope-pin`. **TARGETS:** `.38` (HEX3-BOX-2's guarantee), `.61` (S10's restatement), and by consequence `.25`, `.46`, `.59` (which all rest on the per-key guarantee).

**AUDIT disposition (rule 27).** `decorrelated-model audit` — produced by the gpt-5.6-sol ratification run, not by any tooth. No battery can report the depths it fails to instantiate.

**CONDITIONALITY.** Explicitly conclusion-preserving: “No theorem statement, count, or consumer changes.” What changes is the **evidential weight** a consumer may attach to the machine leg.

**XREF.** `runs/cert/A0_hex3_output.log` — EXISTS ✓; `runs/residues/R5_hex3_output.log` — EXISTS ✓.

---

### EFF.HEX3.68  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction D, L999). FORM: bold-headed paragraph.

> “**Correction D (2026-08-12 — RATIFICATION annex item 2: deep-row falsifier diagnosis).** The P-7 sentence “a LAW violation on a NEW deep row with the committed-table rows clean refutes the transport lemmas (H-2/H-3) before the partition” is superseded. By S5.1, the law is assembled from both (a) the H-1 depth-0 partition and locus ranges and (b) the H-2/H-3 per-species drain transports. Therefore a first failure at a new depth can come from either component: for example, an omitted or mis-ranged \(\alpha(3)\) or \(\beta_3(t=3)\) locus is an H-1 defect even if every shallower committed row is clean. The correct diagnostic order is: a LAW failure refutes the combined partition/transport/assembly package; then inspect the partition sum and per-key SPECIES data. A locus or partition-sum mismatch points to H-1; a correct locus with a wrong drained count points to the corresponding H-2/H-3 transport; agreement of both directs inspection to the S5 aggregation and reader ties. No theorem statement changes.”

**DERIVATION.** A decomposition argument: since the law is assembled from H-1 *and* H-2/H-3, a first failure cannot be attributed to one component a priori.

**SUPERSESSION KIND:** `replacement` (one diagnostic order replaced by another). **TARGETS:** `.51` (P-7's first falsifier clause only).

**AUDIT disposition (rule 27).** `decorrelated-model audit`.

**CONDITIONALITY.** Conclusion-preserving; it corrects a *procedure*, not a result. Note the coupling to Correction C: the very depths D's example names (`α(3)`, `β₃(t=3)`) are exactly the ones C shows are uninstantiated — the two corrections are one finding seen from two sides, and a chapter cut should carry both or neither.

**XREF.** `runs/cert/A0_hex3_output.log` — EXISTS ✓.

---

### EFF.HEX3.69  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction E, L1001–1036). FORM: bold-headed paragraph with five LaTeX displays.

> “**Correction E (2026-08-12 — RATIFICATION annex item 3: proof that the B0ZERO fraction vanishes).** In Correction B, the clause “its fraction \(\to0\) as \(N\to\infty\) per S5.3” is superseded by “its fraction \(\to0\) at fixed \(q\) by the exact S5.2 law, through the positive \(k=1\) \(R\)-tail.” Here is the derivation. Put \(M=N-3\). The tail summand of
> \[
> R(M)=q^{M-1}+\Big\lfloor\frac{M-1}{2}\Big\rfloor(q-1)q^{M-2}
> \]
> contributes to the \(k=1\) term of \(u(N)\) the nonnegative mass
> \[
> \begin{aligned}
> &(q-1)q^3(q^{N-3}-1)
> \Big\lfloor\frac{N-4}{2}\Big\rfloor(q-1)q^{N-5}\\
> &\qquad=
> \Big\lfloor\frac{N-4}{2}\Big\rfloor
> (q-1)^2q^{2N-5}\bigl(1-q^{-(N-3)}\bigr).
> \end{aligned}
> \]
> Consequently
> \[
> \frac{u(N)}{q^{2N-2}}
> \ge
> 1+
> \Big\lfloor\frac{N-4}{2}\Big\rfloor
> \frac{(q-1)^2}{q^3}
> \bigl(1-q^{-(N-3)}\bigr),
> \]
> whose right-hand side tends to \(+\infty\) for fixed \(q\). Hence the B0ZERO share satisfies
> \[
> \frac{q^{2N-2}}{u(N)}
> \le
> \left[
> 1+
> \Big\lfloor\frac{N-4}{2}\Big\rfloor
> \frac{(q-1)^2}{q^3}
> \bigl(1-q^{-(N-3)}\bigr)
> \right]^{-1}
> \longrightarrow0.
> \]
> S5.3’s upper bound is compatible with this conclusion but does not by itself prove it. The crossover values and all theorem statements remain unchanged.”

**DERIVATION.** The span is the derivation, and its point is a **direction defect** in the superseded clause: S5.3 is an *upper* bound on `u`, so it cannot lower-bound `u` and therefore cannot show the B0ZERO share vanishes. The replacement supplies a *lower* bound through the positive `k = 1` R-tail.

**Mandatory arithmetic audit (rule 22) — the whole derivation re-derived by hand.** `M = N − 3`; `R(M)`'s tail summand is `⌊(M−1)/2⌋(q−1)q^{M−2} = ⌊(N−4)/2⌋(q−1)q^{N−5}` ✓. The `k = 1` term of the telescoped law is `(q−1)q^{4·1−1}(q^{N−3}−1)R(N−3) = (q−1)q^3(q^{N−3}−1)R(N−3)`; keeping only the tail summand gives `(q−1)q^3(q^{N−3}−1)·⌊(N−4)/2⌋(q−1)q^{N−5} = ⌊(N−4)/2⌋(q−1)²q^{N−2}(q^{N−3}−1) = ⌊(N−4)/2⌋(q−1)²q^{2N−5}(1−q^{−(N−3)})` ✓ **exactly the displayed mass** (using `q^{N−2}·q^{N−3} = q^{2N−5}`). Dividing by `q^{2N−2}`: `⌊(N−4)/2⌋(q−1)²q^{−3}(1−q^{−(N−3)})` ✓ **exactly the displayed coefficient** `(q−1)²/q³`. Divergence for fixed `q` ✓ (`⌊(N−4)/2⌋ → ∞`, the bracket `→ 1`). The final reciprocal bound follows ✓. **The derivation is sound at every step, and its diagnosis of S5.3's direction is correct.**

**SUPERSESSION KIND:** `replacement` (a wrong justification replaced by a correct one). **TARGETS:** `.66`'s corrected clause — layer 4 of `.37`'s CHAIN, **TERMINAL**.

**AUDIT disposition (rule 27).** `decorrelated-model audit` — a direction error inside a correction, invisible to any battery.

**CONDITIONALITY.** Conclusion-preserving: “The crossover values and all theorem statements remain unchanged.” Cross-check: the crossovers were independently recomputed at `.66` and do stand ✓.

**XREF.** `runs/cert/A0_hex3_output.log` — EXISTS ✓.

---

### EFF.HEX3.70  [changes-record]

**CANONICAL STATEMENT** (verbatim, Correction F, L1038–1042). FORM: bold-headed paragraph with a blockquoted replacement.

> “**Correction F (2026-08-12 — RATIFICATION annex item 4: polynomial terminology).** The S5.4 sentence “So \(u(q,N)\) is one polynomial law in \((q,N)\)” is superseded by:
>
> > “Thus \(u(q,N)\) depends only on the pair \((q,N)\), independently of the characteristic and of the DVR realizing \(\mathbf F_q\); for each fixed \(N\), it is a polynomial in \(q\), exactly as stated in THEOREM HEX3.A.”
>
> This follows from the universal pinned-digit counts and digit bijections in S2–S5. It is not a claim of joint polynomiality: the summation range \(\lfloor(N-1)/3\rfloor\), the coefficient \(\lfloor(M-1)/2\rfloor\), and exponents such as \(q^N\) depend non-polynomially on \(N\). COROLLARY HEX3.C requires only dependence on \((q,N)\), not joint polynomiality, so its conclusion is unaffected.”

**DERIVATION.** A terminology repair with three named obstructions to joint polynomiality.

**Arithmetic audit.** The three obstructions check: `⌊(N−1)/3⌋` and `⌊(M−1)/2⌋` are floor functions (not polynomial in `N`) ✓, and `q^N` is exponential in `N` ✓. Conversely, for fixed `N` the law is a finite sum of products of powers of `q` with integer coefficients — **a polynomial in `q`** ✓, exactly as THEOREM HEX3.A already said (“a polynomial in q for each N”). So the replacement restores consistency between S5.4 and the theorem it proves.

**SUPERSESSION KIND:** `wording-rider`. **TARGETS:** `.32` (S5.4's final sentence only).

**AUDIT disposition (rule 27).** `decorrelated-model audit`.

**CONDITIONALITY.** Conclusion-preserving for HEX3.C, and the correction says exactly why.

**XREF.** `runs/cert/A0_hex3_output.log` — EXISTS ✓.

---

### EFF.HEX3.71  [record]

**CANONICAL STATEMENT** (verbatim, the A0 provenance paragraph, L1044–1058). FORM: italic parenthetical paragraph.

> “*(Corrections C–F derived by the A0 certification run (gpt-5.6-sol
> high, runs/cert/A0_hex3_output.log, 2026-08-12); orchestrator
> verification before transcription: the three quoted spans located at
> HEAD (L488–490, L618–620, L968–969, L429); the roster maximum N = 9
> re-read against S7 L533–536; the three LEMMA H-1 key ranges
> (α(3) ⟹ N ≥ 10, β₂(k=3) ⟹ N ≥ 11, β₃(t=3) ⟹ u₀ odd > 9 ⟹ N ≥ 12)
> re-derived from the S2 partition conditions; Correction E's k = 1
> R-tail algebra re-derived by hand against THEOREM HEX3.A's law
> (q^{N-2}(q^{N-3}-1) = q^{2N-5}(1-q^{-(N-3)}), division by q^{2N-2}
> giving the (q-1)²/q³ coefficient) and its one-sidedness against
> S5.3's (upper-bound) direction confirmed; Correction F's replacement
> checked verbatim against THEOREM HEX3.A's "a polynomial in q for
> each N" and COROLLARY HEX3.C's "the law's data is (q, N) only".
> Transcribed unaltered per the standing division of labor. Folds the
> R5 RATIFIED-WITH-ANNEX minors; HEX3's ledger row → CERTIFIED.)*”

**DERIVATION.** [RECORD of a verification protocol].

**SERIES membership.** ARC SERIES member 6 — **TERMINAL for ledger status** (“HEX3's ledger row → CERTIFIED”).

**Compiler re-verification of the orchestrator's own verification (all four legs).** (1) The four cited HEAD spans: **L488–490** carries HEX3-BOX-2's “46 rows × every realized key…” ✓; **L618–620** carries P-7's superseded first clause ✓; **L968–969** carries Correction B's superseded justification clause ✓; **L429** carries S5.4's “So u(q, N) is one polynomial law in (q, N)” ✓. **All four located exactly.** *(The paragraph says “the three quoted spans” and then lists four line ranges — a counting slip in the provenance note; the four spans correspond to Corrections C, D, E, F respectively. Recorded, not repaired.)* (2) Roster maximum `N = 9` at S7 L533–536 ✓. (3) The three H-1 ranges re-derived ✓ (see `.67`). (4) Correction E's algebra ✓ and its one-sidedness ✓ (see `.69`).

**PIN VERIFICATION.** `runs/cert/A0_hex3_output.log` EXISTS ✓; `runs/residues/R5_hex3_output.log` EXISTS ✓ (the R5 RATIFIED-WITH-ANNEX run this folds).

**CONDITIONALITY.** The ledger-status claim is external to the note; its landing is verified in §5.2 (reverse-XREF RX-6).

**XREF.** `runs/cert/A0_hex3_output.log`, `runs/residues/R5_hex3_output.log` — both EXIST.

---

## 4. XREF verification ledger

Every designation cited anywhere in this specification, with its fixed-string count in the target file, recorded inline at first use and consolidated here. Rule 2: an unverifiable designation is an OPEN-CALL or a NEAR-MISS, never an invented name.

### 4.1 W-12 stack (`lean/notes/openmath/W12_PROOF_2026-08-08.md`, 2,462 lines)

`[TABLE]`

| # | designation | count | consumed at |
|---|---|---|---|
| X1 | `W12-BOX-2` | 8 | `.09`, `.34`, `.40`, `.61`, `.65` |
| X2 | `W12-BOX-3` | 7 | `.09`, `.33`, `.34`, `.35`, `.37`, `.53`, `.65` |
| X3 | `W12-BOX-5` | 2 | `.39` |
| X4 | `W12-BOX-6` | 2 | `.39` |
| X5 | `W12-BOX-7` | 10 | `.03`, `.04`, `.05`, `.39`, `.55` |
| X6 | `LEMMA W12-L0` | 5 | `.26`, `.57` |
| X7 | `W12-L0` | 32 | `.21`, `.26` |
| X8 | `LEMMA W12-L1` | 7 | `.19`, `.32`, `.57` |
| X9 | `W12-L1(a)` | 1 | `.19` |
| X10 | `W12-L1(c)` | 6 | `.55` |
| X11 | `LEMMA W12-S3.2` | 6 | `.07`, `.37` |
| X12 | `W12-S3.2` | 7 | `.07` |
| X13 | `THEOREM W-12.C` | 8 | `.05`, `.31`, `.34`, `.57` |
| X14 | `THEOREM W-12.D` | 5 | `.09`, `.33`, `.40` |
| X15 | `W-12.B` | 7 | `.55` — **see NEAR-MISS NM-1** |
| X16 | `S2.3` | 35 | `.06` (section anchor; count is an upper bound) |
| X17 | `S2.4` | 10 | `.08`, `.13`, `.57` |
| X18 | `S3.4` | 11 | `.26`, `.55` |
| X19 | `(hMenu-3)` | 9 | `.09`, `.40`, `.54`, `.65` |
| X20 | `(hExhaust-3)` | 10 | `.09`, `.33` |
| X21 | `BOX-3 ANNEX` | 2 | `.36`, `.53` — the LANDED annex |
| X22 | `W12-BOX-4` | 1 | (context only) |

**Line-addressed cites, all verified against the target at compile time:** L1218–1224 (W12-BOX-2, exact) · L1225–1235 (W12-BOX-3, exact) · L1590 (the annex back-reference) · L1654 (the ANNEX heading) · L1672–1683 (the annex block, verbatim-identical to HEX3 §S8.1) · L1768 (the r4 m2 sweep disposition) · L233 (`CONJECTURE W-12.B`) · L1211 (`## S6. HONEST BOXES`, confirming HEX3's “§S6” attribution for W12-BOX-3).

### 4.2 W-11 stack (`lean/notes/openmath/W11_PROOF_2026-08-08.md`)

`[TABLE]`

| # | designation | count | consumed at |
|---|---|---|---|
| X23 | `THEOREM W-11` | 3 | `.08`, `.19`, `.57` |
| X24 | `SPLIT-TAIL` | 21 | `.26`, `.37`, `.55` |
| X25 | `S2.3` | 8 | `.21` |
| X26 | `W-11 (iii)` | **0** | `.26` — **NEAR-MISS NM-2** |

### 4.3 Other suppliers and consumers

`[TABLE]`

| # | file | designation | count | consumed at |
|---|---|---|---|---|
| X27 | `JD0_PROOF_2026-08-08.md` | `LEMMA J-D0` | 4 | `.10`, `.57` |
| X28 | `JD0_PROOF_2026-08-08.md` | `J-D0` | 25 | `.10`, `.32`, `.51` |
| X29 | `HMENU3_PROOF_2026-08-08.md` | `HEX3-BOX-1` | 7 | `.37`, `.54`, `.65` |
| X30 | `HMENU3_PROOF_2026-08-08.md` | `HM3-BOX-1` | 2 | `.37` |
| X31 | `HMENU3_PROOF_2026-08-08.md` | `HM3.A` | 18 | `.40`, `.54`, `.56`, `.65` |
| X32 | `HMENU3_PROOF_2026-08-08.md` | `HEX3` | 57 | §5.2 RX-1 |
| X33 | `GENIND_PROOF_2026-08-08.md` | `HEX3-BOX-1` | 2 | `.37`, §5.3 |
| X34 | `GENIND_PROOF_2026-08-08.md` | `HEX3` | 44 | §5.2 RX-2 |
| X35 | `W12_PROOF_2026-08-08.md` | `HEX3` | 29 | §5.2 RX-3 |
| X36 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` | `O-10` | 1 | `.37`, §5.3 |
| X37 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` | `HEX3` | 4 | §5.2 RX-4 |
| X38 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.137` | 11 | `.37`, §5.3 |
| X39 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.138` | 2 | §5.4 |
| X40 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.29` | 8 | §5.3 |
| X41 | `leancheck/notes/N3_CHECK_2026-08-13.md` | `HEX3` | 8 | §5.4 |
| X42 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | `HEX3` | 1 | §5.2 RX-6 |
| X43 | `docs/PROJECT_STATE.md` | `HEX3` | 25 | §5.2 RX-5 |

### 4.4 NEAR-MISS dispositions (rule 15)

**NM-1 — `THEOREM W-12.B` does not exist; the designation is `CONJECTURE W-12.B`.** `grep -cF 'THEOREM W-12.B' W12_PROOF_2026-08-08.md` = **0**. HEX3 itself never writes “THEOREM W-12.B” (it writes the bare `W-12.B`, which has count 7), so this is not a HEX3 defect — but it is a **live trap for any consumer of `.55`**, because the surrounding prose is entirely about theorems. Verified referent: `W12_PROOF_2026-08-08.md` L233, `> * **CONJECTURE W-12.B (DRAIN-n), stated precisely.**`, count 1. **Disposition: designation carried as `W-12.B` (count 7), with the conjecture status stated at every consuming site.**

**NM-2 — `W-11 (iii)`.** Absent as written (count 0 in `W11_PROOF_2026-08-08.md`); referent verified as W-11's clause `(iii)` (count 17 in that file) and independently corroborated by the same aggregate being quoted in `W12_PROOF_2026-08-08.md` §S3.4 (count 11). **Disposition: NEAR-MISS, carried descriptively; not an OPEN-CALL, because the note supplies a second verified route to the same content.**

**NM-3 — the HMENU3 S5.4 sentence quoted by Correction A.** Absent as a single fixed string (count 0) because the source wraps it across three lines; verified at `HMENU3_PROOF_2026-08-08.md:465–467` under the wrapped form, with `HEX3-BOX-1` count 7 in the same file. **Disposition: NEAR-MISS; Correction A's line cite L465–467 is exact.**

**NM-4 — `LIFTCORNER` / `W-2`.** HEX3 cites “the lift-convention seam (W-2/LIFTCORNER)” at `.39`. `LIFTCORNER` appears in 41 files under `lean/notes/openmath/` including `W12_PROOF_2026-08-08.md`, so the designation is live corpus-wide; HEX3 cites it as a **seam name**, not an addressable statement. **Disposition: carried descriptively.** A precise designation would have to come from LIFTCORNER's own spec (`spec/EFF-LIFTCORNER-s1of2.md`, which exists).

**No OPEN-CALL arises from any designation in this note.** Every cited name is either grep-verified at count ≥ 1 or dispositioned above.

### 4.5 PIN VERIFICATION ledger (rule 23)

**Commit hashes — 26 cited, 26 verified** via `git cat-file -t` → `commit`: `e3f3459`, `d177fd8`, `f60348b`, `fca1a97`, `34a946b`, `b6a1d69`, `91ec856`, `d9c5ef8`, `237c753`, `b17238a`, `5919e2f`, `fa7b70d`, `2580f12`, `a707430`, `7020ceb`, `cb05127`, `31506b3`, `f669cb0`, `c16c717`, `97122f2`, `1642275`, `9387eb1`, `671a126`, `a0290f9`, `64d3ff9`, `625fa49`. **Zero failures.**

**md5 pins — 8 cited, 8 verified byte-exactly:** `hex3_checks.py` `83faf7ed…`; `hex3_checks_results.json` `ce6f4116…`; `hex3_checks_output.txt` `6e4b3207…`; `w12_checks.py` `7dc040d9…`; `w11_checks.py` `500aae15…`; `w10_checks.py` `a9c34244…`; `w12_checks_results.json` `05776c9e…`; plus the two report freezes `HEX3_passPE6_report.md` `42d86c7a…` and `HEX3_passPE7_report.md` `4049109c…` (nine including both reports). **Zero failures.**

**Prefix pin — verified and localized.** `b92f47a8895f8c7040c8fe9d7db4473d` = md5 of the file's first 907 lines / 53,951 bytes. Found by exhaustive search over every line boundary; **unique hit**.

**Artifacts — 9 cited, 9 exist:** `verification/openmath/hex3_checks.py`, `…_output.txt`, `…_results.json`, `runs/residues/R5_hex3_output.log`, `runs/cert/A0_hex3_output.log`, `lean/notes/openmath/HEX3_passPE4_report.md`, `…PE6…`, `…PE7…`, `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`. **Zero missing.**

**UNPINNED disposition — one.** The `/tmp` prototype's 18-row list (`.44`) is backed by no artifact filename in the repo; recorded as `UNPINNED`, with the robustness argument given at `.44`.

---

## 5. Consumption table and consumer edges

### 5.1 What HEX3 consumes (forward edges)

`[TABLE]`

| supplier | object | pin | consuming units | load-bearing? |
|---|---|---|---|---|
| W-12 | `S2.4` depth-0 completeness | seal `f669cb0` | `.13` | YES — the partition's exactness |
| W-12 | `LEMMA W12-L0` | seal `f669cb0` | `.21`, `.26` | YES — `R(M)`'s history sum |
| W-12 | `LEMMA W12-L1(a)(b)` | seal `f669cb0` | `.19` | YES — the β-transports' engine |
| W-12 | `LEMMA W12-S3.2` | seal `f669cb0` | `.07`, `.37` | YES — the `q^N` lower bound |
| W-12 | `THEOREM W-12.C` | seal `f669cb0` | `.31` | YES — the identity HEX3.B closes into |
| W-12 | `W12-BOX-3` (the obligation) | — | `.35` | the absorbed obligation |
| W-12 | `S2.3` Ore warrant, **post-r4** | r4 | `.06` | YES — inbound correction |
| W-12 | `W12-BOX-7` convention | — | `.03`, `.04`, `.05` | YES — defines the measured object |
| W-11 | clause (iii); SPLIT-TAIL aggregate; `S2.3` refine isomorphism | seal `7020ceb` | `.21`, `.26` | YES |
| J-D0 | gauge-blindness frame | `1642275`/`9387eb1` | `.10`, `.32` | **NO** — corroborative (N-6) |
| w12 instrument | sealed bytes | 4 md5 pins | `.42`, `.47`, `.48` | YES for the battery, not for the theorems |

### 5.2 Reverse-XREF rows — who consumes HEX3 (rule 8)

All grep-verified.

`[TABLE]`

| # | consumer | designation | count | what is consumed | status |
|---|---|---|---|---|---|
| RX-1 | `HMENU3_PROOF_2026-08-08.md` | `HEX3` | 57 | HEX3's transports as the menu engine; `HEX3-BOX-1` inherited open (count 7) | LANDED; HMENU3 ACCEPTED |
| RX-2 | `GENIND_PROOF_2026-08-08.md` | `HEX3` | 44 | H-1..H-4 as n = 3 transport instances; `u₃(M)` drainage; the committed species tables (GT-N3TIE); **the S8.2 W-12.B consistency clause conditionalized on `HEX3-BOX-1`** (L1498) | LANDED; pinned at HEX3 r3 HEAD `b6a1d69` |
| RX-3 | `W12_PROOF_2026-08-08.md` | `HEX3` | 29 | the BOX-3 ANNEX (verbatim, L1672–1683); **and, outbound, THEOREM HEX3.A used at L1590 to strike a W-12.B order inference of W-12's own** | LANDED (annex `a0290f9`) |
| RX-4 | `docs/TIGHTNESS_CENSUS_2026-08-11.md` | `HEX3` | 4 | census row **O-10** = `TAIL-CERT`, “open (refinement)”, with the drainage non-consumption quoted | LANDED |
| RX-5 | `docs/PROJECT_STATE.md` | `HEX3` | 25 | project-level status | LANDED |
| RX-6 | `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` | `HEX3` | 1 | row 11: “RATIFIED-W-ANNEX (fresh) \| **CERTIFIED 2026-08-12** — A0 adjudicated all 4 annex minors REAL at HEAD; repairs verified + folded as Corrections C–F (note append)” | LANDED — confirms `.71`'s ledger claim |
| RX-7 | `leancheck/notes/N3_CHECK_2026-08-13.md` | `HEX3` | 8 | HEX3's law as a comparison target for an independent decider; §S1's undecided locus; the “β re-entry” family | **OPEN reconciliation** — see §5.4 |
| RX-8 | `spec/HYPOTHESIS_LEDGER.md` | `HYP.137` | 11 | `HEX3-BOX-1` as a live open row | LANDED — see §5.3 |

**Zero-orphan check for reverse edges:** every note that names HEX3 at HEAD appears above. The verification sweep covered `lean/notes/openmath/`, `docs/`, `leancheck/notes/`, `leanfinal/notes/` and `spec/`.

### 5.3 HYP.137 — the exact conditionality wording (queue charge, item 1)

The full ledger row is quoted at `EFF.HEX3.37` CONDITIONALITY. The three points a chapter cut must carry, in the ledger's own words:

1. **What is open.** “The exact law for the σ-undecided mass is not derived — “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived” (HEX3 L437) — because the TRP tail-σ transport loses ghost digits.” CLASS: `conditional-theorem-leg`. DISPOSITION: **MATH** — an unproved lemma.
2. **What consumes it — exactly one thing.** “GENIND’s S8.2 W-12.B consistency clause, pinned open at HEAD”, and **not** drainage: “NOT consumed by drainage: HEX3 L692–693 — “the (hExhaust-3) discharge never needed the split; only this aside’s W-12.B corroboration is conditional on it.”” The failure price is displayed and bounded: `undecided(3,q,N)·q^{−2N}` diverges linearly, and “W-12.B would be FALSE at n = 3”.
3. **How it is disclosed.** Owner-answered at v5 append #49 — “**HEX3-BOX-1 is now NAMED PARENTHETICALLY inside the n=3 perimeter clause of the preview** … disclosure without promotion — it is *visible* in the preview but is **not** a conjunct of Display A’s hypothesis block, because `hExhaust3` provably never needed it”.

**Compiler note on a natural misreading the ledger itself flags:** “the n≤3 menus and drainage **DO** enter the final proof — they are the induction’s base cases, and GENIND consumes HMENU3/HEX3 as base data. What stays out of the load-bearing chain is **HEX3-BOX-1** specifically, not the n = 3 work around it.” A chapter cut that drops HEX3 because HYP.137 is open would be wrong; only the BOX-1 leg is out.

**Consistency check the ledger performs and this compilation confirms:** census O-10 (“Drainage consumes only the proved conservative upper bound U₃^conv”) and GENIND's pin record are **both accurate and non-contradictory** — they name different consumers (drainage vs. the n = 3 W-12.B corroboration aside). Verified independently here at `.55` (the aside is the only conditional site) and `.09`/`.58` (the discharge's hypothesis set omits BOX-1).

### 5.4 CONSUMER NOTE — the N3_CHECK §6d reader-convention item (queue charge, item 2)

`leancheck/notes/N3_CHECK_2026-08-13.md` §6d is an **unresolved corpus-side reconciliation against HEX3, dated after the census**, and is ledgered as **HYP.138** (`grep -cF 'HYP.138' spec/HYPOTHESIS_LEDGER.md` = 2). It is emitted here as a consumer note rather than as a HEX3 unit because it is not HEX3 text and HEX3 makes no claim about it.

**The item, verbatim** (`leancheck/notes/N3_CHECK_2026-08-13.md` §6d, L359–381):

> “### 6d. ⚠ A reconciliation item for the corpus side (reported, not resolved)
>
> The decider's TOTAL undecided count does not agree with HEX3's `U₃^conv(q,N) = q·u(q,N)`; e.g. at
> `p = 2, N = 7` the corpus value 11 328 EXCEEDS the decider's 11 264. This is **not** by itself a
> contradiction — HEX3.B itself asserts `U₃^σ ≤ U₃^conv`, i.e. the conservative reader over-counts
> by design, and this decider is a sharper reader, so both are upper bounds on the true undecided
> count and the corpus's being larger is expected. What it does mean is that the two numbers are
> **not measuring the same set**, so these runs neither confirm nor refute THEOREM HEX3.A. Two
> further data points, recorded as found and NOT tuned: (i) restricted to the triple-root branch
> (residue `= (X−ρ)³`) the decider's count equals `u(q,N)` exactly at `N = 2, 3` for both `q = 2, 3`
> (4, 16 and 9, 81) but departs at `N = 1` and at `N = 4`, where the corpus's extra term
> `(q−1)²q³` is absent because this decider certifies those classes; (ii) the complementary branch
> (residue `= (X−ρ)²(X−τ)`) contributes exactly `q(q−1)·q^{2N−2}` undecided classes in every case
> computed. Reconciling the two readers' conventions (per-centre vs whole-space, and the
> `B₀ = 0 in-window ⟹ UNDECIDED` exit) is a task for whoever next touches HEX3; nothing in this
> unit depends on it.”

**The ledger's disposition, verbatim** (`spec/HYPOTHESIS_LEDGER.md` HYP.138):

> “CLASS: corpus-consistency-item
> PROPOSED DISPOSITION: NODE — convention reconciliation between the two readers; until it lands, neither reader’s count may be cited as confirming or refuting HEX3.A. (v3 delta item 3.)”

**Compiler arithmetic audit of §6d's four numbers, against this compilation's own evaluator.** (a) `q = 2, N = 7`: `U₃^conv = q·u(2,7) = 2·5664 = 11,328` ✓ — the “corpus value” is exactly HEX3's whole-space figure. (b) Triple-root-branch agreements: `u(2,2) = 4`, `u(2,3) = 16`, `u(3,2) = 9`, `u(3,3) = 81` ✓ — all four match the decider at `N = 2, 3`. (c) The departure at `N = 4` is attributed to “the corpus's extra term `(q−1)²q³`”, which is exactly the `k = 1` term of the law at `N = 4` (`.12`'s `u(q,4) = q⁶ + (q−1)²q³`) ✓ — the diagnosis is precisely right. (d) The complementary branch's `q(q−1)·q^{2N−2}` is the whole-space DBL-undecided term of THEOREM W-12.C, `(q−1)q^{2N−1}` ✓ (same quantity, `q·q^{2N−2} = q^{2N−1}`).

**Three consequences for any consumer of HEX3, stated plainly.**
1. **Neither count may be cited as confirming or refuting THEOREM HEX3.A** until the conventions are reconciled (the ledger's own fence).
2. **The mismatch is expected in direction**, not anomalous: `11,328 > 11,264` is the conservative reader over-counting a sharper one, exactly as `U₃^σ ≤ U₃^conv` (`.06`) predicts. Nothing in §6d is evidence against the law.
3. **The reconciliation is named and small.** §6d itself names the two convention axes — per-centre vs whole-space, and the `B₀ = 0 in-window ⟹ UNDECIDED` exit — both of which are pinned in this compilation (`.02` for the `×q` factor, `.03` for the exit rule). The audit above shows the per-centre/whole-space axis is already reconciled on the triple-root branch; what remains is the exit rule, i.e. exactly the `B0ZERO` genre of `.62`.

**Compiler flag for whoever next touches HEX3:** the two convention axes §6d names are precisely the two objects that Correction 1 and Correction B are about (the B0ZERO genre and its share of the drained mass). Whoever reconciles the readers should start from `.62` and `.66`, not from the sealed body. This is a compilation observation, not a HEX3 claim.

---

## 6. TEETH — the inverse table (rule 6), both directions

### 6.1 Battery row → guarded unit(s)

`[TABLE]`

| battery family / tooth | preregistration | guards | disposition |
|---|---|---|---|
| HEX3-PIN (4 md5 pins) | `.42` | `.03`, `.42`, `.47`, `.48` — the sealed-convention import | **clean pass**; all four re-verified at compile time |
| HEX3-LAW (92 checks) | P-1 `.45` | `.08` (THEOREM HEX3.A), and through it `.29`, `.30` | **clean pass**, 46/46 rows; but see `.44` — the law was FITTED on 14 of the 29 pairs, so the independent force is the twelve never-measured pairs |
| HEX3-SPECIES (172 checks, both directions) | P-2 `.46` | `.13` (H-1 loci), `.18`, `.22`, `.23`, `.24` (per-route drained), `.28` (the S5.1 table), `.25` | **clean pass** at realized keys; **scoped by Correction C** `.67` |
| HEX3-XREAD (158,204 states) | P-3 `.47` | `.03` (the conservative reader's faithfulness) | **clean pass**; scoped to rows ≤ 65,536 states |
| HEX3-W12TIE (23 rows) | P-4 `.48` | `.08` against the committed w12 column | **clean pass**; `signed vacuity disclosure` — the fit disclosure means this is consistency, not confirmation |
| HEX3-CHAR (17 pairs) | P-5 `.49` | `.10` (COROLLARY HEX3.C), `.32` | **clean pass** at tally granularity |
| HEX3-T-FLOOR (exactly 10 rows) | P-6 `.50` | `.26` (`R(M)`'s floor term) | **clean pass**, count exact; recomputed here ✓ |
| HEX3-T-ALPHA (exactly 20 rows) | P-6 `.50` | `.18` (the α route) | **clean pass**, count exact; recomputed here ✓ |
| HEX3-T-VERT1 (exactly 13 rows) | P-6 `.50` | `.23` (the β2 route) | **clean pass**, count exact; recomputed here ✓ |
| falsifier set | P-7 `.51` | the diagnostic procedure itself | **none fired**; the procedure is **superseded by Correction D** `.68` |

### 6.2 Guarded unit → battery row (inverse direction)

`[TABLE]`

| unit | guarded by | class |
|---|---|---|
| `.03` conservative reader | HEX3-XREAD, HEX3-PIN | instrument-guarded |
| `.08` THEOREM HEX3.A | HEX3-LAW, HEX3-W12TIE, HEX3-SPECIES | battery-guarded |
| `.09` THEOREM HEX3.B | — | **PROOF-ONLY** |
| `.10` COROLLARY HEX3.C | HEX3-CHAR | battery-guarded |
| `.13` LEMMA H-1 (loci) | HEX3-SPECIES (locus column) | battery-guarded, depth-scoped |
| `.16` H-2(i) window coherence | — | **PROOF-ONLY** |
| `.17` H-2(ii) shear | HEX3-SPECIES (α drained) indirectly | weakly guarded |
| `.18` H-2(iii) α onto | HEX3-SPECIES, HEX3-T-ALPHA | battery-guarded |
| `.19` H-3 frame | — | **PROOF-ONLY** |
| `.22`/`.23`/`.24` β routes | HEX3-SPECIES (per-key), HEX3-T-VERT1 | battery-guarded |
| `.26` H-4 `R(M)` | HEX3-T-FLOOR; PE7's fresh route to `M = 16` | battery-guarded |
| `.27` R-recursion | — | **PROOF-ONLY** (compiler-verified numerically here: 360 checks, 0 failures) |
| `.29` first-step assembly | HEX3-LAW (aggregate only) | weakly guarded |
| `.30` S5.2 telescoping | HEX3-LAW (aggregate only); PE2's fresh route to `N ≤ 40` | weakly guarded |
| `.31` S5.3 the bound | — | **PROOF-ONLY** |
| `.32` S5.4 char-independence | HEX3-CHAR | battery-guarded |
| `.37` HEX3-BOX-1 | — | **UNGUARDED BY CONSTRUCTION** (an open obligation) |
| `.45`–`.51` preregistrations | — | they *are* the guards |
| `.53`–`.58` scope/consumer records | — | **RECORD** (guarded by §5's grep verification instead) |
| `.62`–`.71` appends | — | **AUDIT-produced**, see 6.3 |

### 6.3 PROOF-ONLY rows (rule 16) — the note's own coverage-hole sentences

Six units carry their interesting content in a proof no battery touches. The note states the hole itself, and the compiler quotes it rather than leaving the row blank.

HEX3-BOX-2 (`.38`), on the compression:

> “the fully expanded digit ledgers (every
> shift3 congruence at every chain step, the exact fiber counts of
> each β-route image) are compressed into the slot-counting arguments
> + the machine leg”

Correction C (`.67`), on the depth hole:

> “The all-depth formulas rest on the uniform slot-count and transport proofs in S2–S3; the machine leg confirms those formulas only at the realized keys.”

So: `.09`, `.16`, `.19`, `.27`, `.31` and the depth-`≥ 3` reach of `.13` are **proof-carried, not battery-carried**. Three of them were nonetheless independently re-derived by hostile passes (PE1 re-derived `.16`; PE3 re-derived `.22` in full; PE4 re-derived `.18` from scratch), and two were verified numerically by this compilation (`.27`, `.31`).

### 6.4 AUDIT dispositions (rule 27) — findings no tooth could produce

`[TABLE]`

| unit | AUDIT class | why no tooth applies |
|---|---|---|
| `.62` Correction 1 | `in-house hostile pass` | the battery checks per-key integers; it never asks *which frame* a drain occurs in. Note's own words: “Seal-era text, unflagged by PE1–PE5” |
| `.65` Correction A | `transfer audit` | a mis-attribution across three notes, detectable only by reading the suppliers' frozen texts |
| `.66` Correction B | `arithmetic recount` + `stale self-description` | an asymptotic superlative; no finite roster can falsify it |
| `.67` Correction C | `decorrelated-model audit` | no battery can report the depths it fails to instantiate |
| `.68` Correction D | `decorrelated-model audit` | a diagnostic *procedure*, not a computed value |
| `.69` Correction E | `decorrelated-model audit` | a **direction** error (an upper bound used to prove a limit is zero) inside a correction |
| `.70` Correction F | `decorrelated-model audit` | a terminology over-claim (joint polynomiality) |

**Seven of the note's eight corrections are audit-produced; exactly one (`.45`'s census) came from a verifier recount that a tooth could in principle have caught.** That ratio is the honest summary of what this note's battery can and cannot see.

### 6.5 Zero-orphan check

**Battery rows → units: zero orphans.** All six families and all three teeth guard at least one inventoried unit (table 6.1).

**Units → guards: 71 units, 46 guarded, 25 unguarded.** The 25 unguarded decompose as: 6 PROOF-ONLY (6.3), 1 open obligation (`.37`), 7 preregistrations (which are guards, not guarded), and 11 records/scope/append units covered by §4's pin verification and §5's grep verification instead. **No unit is silently unguarded.**

---

## 7. Arithmetic audit and fidelity audit (compile-time, mechanical)

### 7.1 Arithmetic audit — what was recomputed and what it found

Every number in this note that could be recomputed from the note's own closed forms was recomputed **independently of the note's tables**, using an evaluator written from THEOREM HEX3.A's two displays alone.

**Confirmed exactly (no discrepancies):**

- **Roster:** 21 + 25 = 46 rows; `Σ q^{3(N−1)}` = **67,410,225** states; **29** distinct `(q,N)` pairs; **17** shared pairs.
- **The census (`.45`):** the twelve never-measured pairs computed by literal set difference are **exactly** the `[r2]` twelve-set, membership for membership; all twelve whole-space values and the two swapped-out values reproduce from the law.
- **Anchors (`.12`):** `u(2,4) = 72`, `u(3,4) = 837`, `u(2,7) = 5664`; both k-term decompositions (`1504 + 64` first-step, `1440 + 128` telescoped).
- **Law equivalence:** the telescoped and first-step forms agree for `q ∈ {2,3,4,5,7,8,9,11,13,16,25,27}` × `N = 1..30`.
- **The R-recursion (`.27`):** `q^{M−1} + (q−1)Σ_{j≥1,2j≤M−1}q^jR(M−2j) = R(M)` for `q ∈ {2,3,4,5,7,8,9,11,13}` × `M = 1..20` — **360 checks, 0 failures**.
- **The telescoping coefficient (`.30`):** `(q−1)q^{3l} + (q−1)²Σ_{k+j=l}q^{3k}q^{4j−1} = (q−1)q^{4l−1}` for `q ∈ {2,3,5}` × `l = 1..8` — 24 checks, 0 failures. The generating-function identity `1 − A = (1−q⁴x³)/(1−q³x³)` is exact.
- **All seven steps of S5.3 (`.31`)**, including the `M ≥ 1` equivalence and `N ≤ q^{N−1}`.
- **All twelve P-2 spot values (`.46`)** from the S5.1 table alone, including both fully-drained species (`M − 2j = 1`).
- **All three tooth counts (`.50`):** 10 / 20 / 13, recomputed from the roster and the tooth predicates.
- **Check-count arithmetic (`.59`):** `4 + 92 + 172 + 158,204 + 23 + 17 = 158,512`.
- **The Correction 1 witness row (`.62`):** 512 states, `u = 72`, B0ZERO `[64,64]`, ALPHA(1) `[8,8]`, DECIDED `[440,0]` — and “no β key realized” is **provable** at `(q,N) = (2,4)`, not merely observed.
- **All eight Correction B crossovers (`.66`):** shares 0.5186 / 0.4846 at `N = 13/14`; β ratios 0.9771 / 1.1042 at `N = 17/18`; α ratios 0.9862 / 1.0036 at `N = 76/77` — reproduced to four decimals by an independent genre decomposition, itself verified as an exact integer identity `B0ZERO + α + β = u(N)`.
- **Correction E's algebra (`.69`)** at every step, including the `(q−1)²/q³` coefficient.
- **Correction C's three depth ranges (`.67`):** `N ≥ 10`, `N ≥ 11`, `N ≥ 12`.
- **The §6d comparison numbers (§5.4):** `2·u(2,7) = 11,328`; the four triple-root-branch values `4, 16, 9, 81`; the `N = 4` extra term `(q−1)²q³`.

**Findings — three, none a mathematical error:**

**AF-1 — the note uses two different scaling conventions for its numbers, in different places, without a stated convention line.** The P-1 census (`.45`) and the S10 scorecard report **whole-space** values (`q·u`), while the fresh-route figures in the ARC line (`.63`: `(16,4)` at 17,698,816; `(2,12)`), Correction B's fractions (`.66`), and the S5.1 table itself (`.28`) are **per-centre** (`u`). Both are internally consistent and the header of `.12` does say “(per center; whole space = ×q)”, but that parenthetical sits 480 lines from the ARC line that needs it. Recorded because a reader comparing `(16,4) = 17,698,816` against the census's style will conclude the numbers disagree by a factor of 16. **Not a defect; a reading hazard.**

**AF-2 — `.55`'s N-linear display and `.69`'s differ by one power of `q`, correctly.** `.55` writes `⌊(N−4)/2⌋(q−1)²q^{2N−4}(1−q^{−(N−3)})` (whole-space); `.69` writes `…q^{2N−5}…` (per-centre). At `(2,7)`: 960 and 480. Same instance of AF-1, flagged separately because the two displays are the *same formula* and sit in the same supersession neighbourhood.

**AF-3 — the A0 provenance paragraph says “the three quoted spans” and lists four line ranges** (`.71`). All four ranges are correct and correspond to Corrections C, D, E, F. A counting slip in a provenance note; recorded, not repaired.

### 7.2 Fidelity audit

- **Every CANONICAL STATEMENT is a verbatim source quotation or is explicitly marked `[ASSEMBLED]`.** Exactly one `[ASSEMBLED]` statement appears (`.53`, whose components were separately verified against `.06`–`.10`); every other statement is quoted.
- **No quantifier, index, inequality direction, exponent, letter count, valuation, depth, or scope was altered anywhere.** The one place a direction is discussed as *wrong* is `.69`, where the source itself diagnoses it.
- **Truncation inside a quotation: one**, at `.45`, marked with an explicit ellipsis and an inline note saying what was cut (the superseded `[r1]` eleven-item list) and where to find it (L551–568).
- **Terminal punctuation inside quoted displays is preserved as written**, including the `∎` marks that close H-1..H-4 and each S5 subsection.
- **Strikethrough is reproduced**, because in this note `~~…~~` IS the supersession marker (`.12`, `.33`, `.45`).
- **No table was prosified.** Two source tables exist (S5.1's species table `.28`; the S10 scorecard, a bulleted list transcribed as a table at `.60` **alongside** its source form). One prose roster was additionally transcribed as a table `[TABLE]` at `.43` **alongside** the source form, per the double-emission spirit of rule 14, and the transcription's own row-count slip was caught and corrected inside that unit's arithmetic audit.
- **Rule 14 (fenced ASCII displays) does not apply:** the note contains no fixed-width ASCII table inside a code fence. Checked, not skipped.
- **All 26 commit hashes, 9 md5 pins, 1 prefix pin and 9 artifact filenames were verified** (§4.5). Zero failures; one `UNPINNED` disposition recorded (`.44`).
- **43 external designations grep-verified with counts recorded inline** (§4.1–4.3). **Four NEAR-MISS dispositions** (§4.4), **zero invented names**, **zero OPEN-CALLs arising from designations**.
- **Status and mathematics are kept as distinct predicates throughout:** the acceptance chronology governs grade (`.64`), the landed annex governs consumption (header §B, §5.2 RX-3), and the ledger governs open-obligation status (§5.3).
- **Every cross-note status claim was checked against the target's FULL append chain (rule 10), not the pinned sentence** — which is how the LANDED annex (`.53`) and the discharged `(hMenu-3)` (`.40`, `.54`) were found.

---

## 8. Self-audit and OPEN-CALLs

### OPEN-CALL 1 — Correction A's site list omits a fourth site that repeats the corrected attribution. FOR-0b (note owner).

Correction A (`.65`) names three sites carrying the withdrawn “tail half of (hMenu-3)” attribution: S0 L104–105, HEX3-BOX-1 L447–449, and S8.2 item 1's ingredient list. But **§S10's closing sentence (L830–832) says the same thing in different words** — “the σ-residue exact law remains open exactly at the tail-σ-certification lemma (HEX3-BOX-1) — **W-13's floor together with (hMenu-3) = W12-BOX-2**” — and Correction A does not name it. The two phrasings differ: the three named sites say the lemma *is* the tail half *of* `(hMenu-3)`; §S10 says it is W-13's floor *together with* `(hMenu-3)`, which is a conjunction rather than an identification and is arguably survivable. **The compiler has flagged it at `.61` and applied nothing.** **Decision needed:** whether the merged spec reads Correction A onto §S10's closing sentence as well. Carrying it silently either way would be wrong — applying it invents a correction the owner did not make; ignoring it leaves a chapter cut free to quote a sentence whose sibling phrasings were withdrawn.

### OPEN-CALL 2 — the note's frozen grade vocabulary appears in a text that landed verbatim in another accepted note. FOR-0b / possibly FOR-0d.

The BOX-3 annex (`.53`) contains the phrase “DISCHARGED at composition grade (attempt 0/2)”, and that text **landed verbatim in `W12_PROOF_2026-08-08.md` L1672–1683**. HEX3 is now ACCEPTED 2/2 and ledger-CERTIFIED, so the landed text carries a stale grade **inside another note**, where no HEX3 append can reach it. W-12's own wrapper repeats it (“at composition grade (attempt 0/2; HEX3's own hostile arc has not begun)”) — and that wrapper sentence is doubly stale, since the arc not only began but completed. **The compiler has changed nothing in either note.** **Decision needed:** whether a dated rider is owed to W-12 refreshing the annex wrapper's grade, or whether the corpus convention is that a verbatim-applied annex freezes with its source's grade at application time. This is a corpus-protocol question, not a HEX3 question, which is why it may need Asvin rather than the note owner.

### OPEN-CALL 3 — `.27`'s R-recursion equivalence is asserted, not displayed, and `.24` consumes it. FOR-0b.

LEMMA H-4's second half (`.27`) says the R-recursion “evaluates to the same closed form by the identical bracket telescoping” — an assertion by analogy to S5.2, with no display. The β3 route (`.24`) **consumes that identity** to perform its `u₀`-sum. The compiler verified the identity numerically over a wide grid (360 checks, 0 failures, §7.1), so there is no reason to doubt it, and PE3's fresh route independently re-derived the β1 route at letter resolution. **But a formalization blueprint cannot build a recursion proof from an analogy**, and this is the one place in the note where a load-bearing step is carried by “the identical … as above”. **Not a claimed error.** **Decision needed at 0b/chapter time:** whether the `n = 2` telescoping must be displayed before formalization, or whether the `n = 3` display at S5.2 may be cited as covering it.

### Recorded source defects and reading hazards (flagged, not silently repaired)

1. **`.53` / N-4: the “W12_PROOF not edited” fence is stale.** The annex landed (verified, header §B). Frozen text, no append corrects it; tagged `STALE-SELF-DESCRIPTION`.
2. **`.11`, `.33`, `.38`, `.57`, `.61`: the “attempt 0/2” vocabulary is stale in five places.** The ARC line reaches three of them by name; `.11` (the S1 GRADE box) and `.57` (“graded 0/2”) are reached by **no** append and are stale on their own. Tagged, not repaired.
3. **`.40`: “No claim that W-12.D fires at n = 3 yet” has been overtaken corpus-side** by HMENU3's discharge of `(hMenu-3)`. True as written of HEX3; a reader must not infer the corpus state from it.
4. **AF-1 / AF-2: two scaling conventions coexist without a local convention line** (§7.1). The `(16,4) = 17,698,816` figure in the ARC line is per-centre while the census beside it is whole-space.
5. **AF-3: “the three quoted spans” lists four** (`.71`).
6. **NM-1: `W-12.B` is a CONJECTURE, not a theorem.** HEX3 never miswrites it, but `.55`'s prose context invites the error, and the whole point of `.55` is that its corroboration is conditional. Any consumer must carry the conjecture status.
7. **`.44`: the pre-seal prototype is UNPINNED** and three pairs of the “measured pre-seal” set rest on it alone. The census is robust to this (argument at `.44`), but the disclosure is load-bearing and must travel with the census.
8. **`.43`: the compiler's own first transcription of the roster dropped a row.** Caught by the mandatory arithmetic audit (rule 22) inside the unit and corrected in place, with the correction left visible rather than silently rewritten — recorded here because it is direct evidence that rule 22 earns its cost.
9. **`.48`: P-4's “zero free parameters” is true but must not be read as independent confirmation** — the law was fitted on that very table (`.34`, `.44`).
10. **§5.4 / HYP.138: the N3_CHECK §6d reconciliation is OPEN.** Until it lands, neither reader's count may be cited as confirming or refuting THEOREM HEX3.A. This compilation's audit narrows the gap to one axis (the `B₀ = 0 in-window ⟹ UNDECIDED` exit rule) but does not close it, and does not claim to.

### Exhaustive residual judgment list

There are no other unresolved HEX3 mathematical or scope judgments. HEX3-BOX-1 (`.37`), the depth-scope of the machine leg (`.67`), the fit disclosure (`.44`), and the `(hMenu-3)` fence (`.40`) are the note's own displayed standing fences, not compiler ambiguities; the stale grade vocabulary, the landed annex, the two scaling conventions, and the provenance counting slip are classified above as bookkeeping. The three OPEN-CALLs are the complete list of judgments the compiler could not make from the text.

### Compilation summary

- **71 statement units** across the sealed body (`.01`–`.61`) and the three dated appends (`.62`–`.71`).
- **43 external designations grep-verified**, 4 NEAR-MISS dispositions, 0 invented names, 0 designation OPEN-CALLs.
- **26 commit hashes + 9 md5 pins + 1 prefix pin + 9 artifacts verified; zero failures** — the prefix pin localized to a unique line boundary (L907 / byte 53,951).
- **8 reverse-XREF consumer edges emitted and verified**, including the LANDED W12 annex and the OPEN N3_CHECK reconciliation.
- **Two ledger rows compiled with their exact wording:** HYP.137 (§5.3, the queue charge) and HYP.138 (§5.4, the consumer note).
- **One SERIES** (the six-member ARC series, `.33` → `.38` → `.61` → `.63` → `.64` → `.71`), two multi-layer CHAINs with TERMINAL marked (`.37`'s four layers, `.45`'s three), and **eight distinct SUPERSESSION KINDs** used across the note's supersessions.
- **Arithmetic audit: every recomputable number in the note reproduced exactly**, including all eight of Correction B's crossovers, all twelve census values, all twelve P-2 spot values, all three tooth counts, and every step of S5.3 and Correction E. Three findings, none a mathematical error.
- **The battery is fully consumed:** 6 families + 3 teeth, zero orphans; 46 of 71 units guarded, the 25 unguarded ones classified (6 PROOF-ONLY, 1 open obligation, 7 preregistrations, 11 records covered by §4/§5).

EFF-HEX3 COMPILED: 71 statements / 43 xrefs verified / 3 open calls
