# EFF-T3 CROSS-READ — Opus spec-verification arm (2026-08-13)

**Role.** Independent source-to-statement review of `spec/EFF-T3.md` (compiled by
gpt-5.6-sol high, PHASE-0a pilot) against its source
`lean/notes/openmath/T3_COCYCLE_TELESCOPE_2026-08-12.md`. I did NOT author the spec.
READ-ONLY: no repo file was modified except this report.

**Provenance checks (all pass).**
- `git hash-object` of the note = `34cc4d40dceda561b56e1deb8f7167c7e5500c8f` — matches the
  spec's HEAD blob hash exactly. Note is clean in the working tree; last touched by commit
  `4c9bbae8` ("T3 consumption record …").
- The note's structure is base (lines 1–1217) + exactly one round, `r1 (2026-08-12)` whose
  sole item R1-G1 is an explicit "Replace §8.2 in full" (lines 1226–1338) + the ACCEPTANCE
  RECORD (1345–1357) + the post-acceptance consumption/narrowing record (1360–1369). So the
  effective text = base with §8.2 replaced. I re-derived this independently; it agrees with
  the spec's resolution rules 1–3.

**Method for layer 1.** Rather than sampling, I mechanically extracted **all 96 quoted
blocks** from the spec and tested each for verbatim containment in the note under a
normalization that removes only presentational reflow (whitespace, `\boxed{…}` unwrapping,
`\\[2mm]` spacing, `**` emphasis, math-delimiter tokens, typographic-quote folding). Script:
`scratchpad/verb.py`. That is a strict superset of the requested 10-statement adversarial
audit; I then hand-re-derived the 13 blocks with the richest resolution traces (every
`[ASSEMBLED]` unit — .19, .20, .21, .23, .24, .25, .26, .27, .28, .29, .31 — plus the two
random picks .07 and .13) against the note's own chronology.

---

## LAYER 1 — FIDELITY SPOT-AUDIT

### 1.1 Verbatim claim: essentially sound

**88 of 96 quoted blocks are byte-verbatim** modulo presentational reflow. The 8 exceptions
are, without exception, terminal-punctuation or nested-quote restyling — no quantifier,
index, inequality, inverse, rung, or direction was altered anywhere in the spec. The
exceptions, quoted exactly:

| Spec unit | Spec text | Note text (line) | Class |
|---|---|---|---|
| EFF.T3.19 CONDITIONALITY | "Unconditional at the landed \(i=2\) rung." | `Unconditional at the landed \(i=2\) rung` (908, table cell) | added terminal period |
| EFF.T3.20 CONDITIONALITY | "Comparison/routing block unconditional on its stated source hypotheses." | same, no period (909, table cell) | added terminal period |
| EFF.T3.23 | "'\(w\)-blind' means …" | `“\(w\)-blind” means …` (724) | double→single quote restyle |
| EFF.T3.24 (G5-TWIST) | `2\le j\le n+1.` | `2\le j\le n+1,` (740) | comma→period inside a display claimed verbatim |
| EFF.T3.28 | "The unit's scope of record is therefore TWO absorptions + one documented non-instance; GENTOW-6.4 retains its own certified proof." | note continues `(the blueprint's third target was honestly narrowed at revision).` (1364–1366) | **truncation without ellipsis** |
| EFF.T3.28 | "…dated 'absorbed by S-2 as instance' appends…" | `"absorbed by S-2 as instance"` (1367) | quote restyle |
| EFF.T3.29 | `\operatorname{res}(x^2/5)=2.` | `…=2,` (r1, 1249) | comma→period |
| OPEN-CALL 4 | "the blueprint's third target was honestly narrowed at revision." | `…at revision).` (1366) | period placement |

Only the EFF.T3.28 truncation is load-bearing: the elided parenthetical is precisely the
clause that decides OPEN-CALLs 3/4/5. Dropping it inside the quotation that the spec calls
dispositive, while quoting it separately three sections later, is the one quoting defect
worth fixing.

### 1.2 Where the ASSEMBLED blocks silently drop load-bearing sentences

`[ASSEMBLED]` blocks concatenate verbatim components; the risk is the *gaps*. Four gaps are
real (verified: zero occurrences of each phrase anywhere in the spec):

1. **EFF.T3.19 (ABS-G2) omits the instantiation claim.** Note §3, line 495: *"GENTOW2's
   expansion, peel, positive-degree elimination, exact-grade digit law, and root-evaluation
   calculation are precisely (BR1)–(BR5)."* This is the sentence that discharges the
   hypotheses of T3-BR at the i=2 rung — i.e. the entire reason ABS-G2 is unconditional. The
   spec quotes the analogous sentence for GENTOW5-W in EFF.T3.21 ("…instantiate (BR1)–(BR5)")
   but not for GENTOW2. Asymmetric, and it is the one fact a formalizer needs to build the
   instance. **Severity: real, must fix.**
2. **EFF.T3.26 (G6-NONINSTANCE) omits the substance of the non-instance argument.** Note
   §6.1, lines 851–859: *"Once the projection equation has been proved independently,
   \((v+c_g)-c_g=v\) is only an additive cancellation. It does not prove triangularity, digit
   bijectivity, lift-stability, exclusion of unread digits, exact undercut attainment, or the
   shifted cap."* and *"Encoding the additive translation in a formal multiplicative group
   would still not recover the filtration or cap assertions."* The spec keeps only the
   withdrawal-tooth sentence. The two dropped sentences are the *signed non-applicability
   argument* — exactly what the fleet protocol's TEETH disposition "signed non-applicability"
   will have to cite. **Severity: real, must fix.**
3. **EFF.T3.31 trace over-claims.** Its RESOLUTION TRACE says "base §9, items 1–3, 8–16", but
   honesty-ledger item **13** ("The GENTOW6 E11 riders correct **adjacent source and record**
   statements; they do not change T3's carrier") is not among the quoted fences (0 hits for
   "adjacent source"). Semantically near-covered by EFF.T3.27's closing quote, but the trace
   as written is false. **Severity: minor (trace accuracy), fix by quoting item 13 or
   correcting the range to "1–3, 8–12, 14–16".**
4. **EFF.T3.25 omits its scope opener** (note line 768: *"The residual conditionality is
   independent of the corrected lift range."*). Compensated by the closing quote it does keep
   ("This range repair does not itself discharge … and does not weaken (G5-COND)").
   **Severity: cosmetic.**

### 1.3 One unflagged paraphrase

EFF.T3.20's CONDITIONALITY renders the note's §4 five-row **absorption-boundary table**
(lines 607–614) as five prose bullets. This is a reformatting paraphrase of displayable
text, contrary to the spec's own fidelity rule 2 and unmarked by `[ASSEMBLED]`. Content is
faithful (I checked each row; the only wording loss is "coefficient telescope and polynomial
rescaling" in the clause-(c) row). **Fix: quote the table.** Template consequence: the
format needs an explicit rule for *tables* — they are displayable and must be reproduced,
not prosified.

### 1.4 The two random picks and the r1 supersession

- **EFF.T3.07 (BR1)**: verbatim ✓, conditionality correct ✓, teeth mapping correct
  (§8.2 boundary frame + mutants 2 and 3) ✓.
- **EFF.T3.13 (ρ_t/R(Z) setup)**: verbatim ✓; its TEETH correctly bind the *r1* comparison
  parameters (q_CMP = 2, H₀ = 6, D = 3), not the superseded base §8.2 (which used q = 1 for
  both ports and asserted the scalar 3 without deriving it) ✓.
- **EFF.T3.29** reproduces r1's §8.2 in full and correctly marks base 940–1000 historical ✓.
  No other spec unit draws on base §8.2. **The single supersession in this note is resolved
  correctly.**

**LAYER 1 VERDICT: PASS with 3 required fixes** (the §3 instantiation sentence, the §6.1
non-instance argument, the EFF.T3.28 truncation) **and 3 minors** (item-13 trace, §4 table
prosified, terminal punctuation inside quoted displays).

---

## LAYER 2 — THE 12 OPEN CALLS, ADJUDICATED

Governing external evidence I used (all in-repo, all readable by the compiler):

- **[BP]** `docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` line 22: *"**T3 the cocycle-telescope
  lemma** — GENTOW2-B″, HETOW-4, and GENTOW-6.4 (the 𝒯-free cap) are three proofs of one
  telescoping-cocycle-monomial shape."* — this is "the blueprint" the narrowing record names.
- **[AP2]** `GENTOW2_PROOF_2026-08-09.md:1501` and **[APH]** `HETOW_RECON_2026-08-09.md:837`:
  landed *"Dated absorption append (2026-08-12 — S-2/LEMMA COCYCLE-TELESCOPE)"* blocks, each
  citing *"blueprint protocol (`docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` §5.3 item 4)"*
  and the consumption-check leg PASS. **`GENTOW5_WI_2026-08-10.md` has no such append.**
- **[T1TAGS]** `T1_GAUGE_COCYCLE_2026-08-12.md` real display tags: `C2-wrap`(177),
  `C2-cocycle`(199), `C2-vartheta`(214), `C2-recursion`(229), `C2-level-1`(250),
  `C3-dictionary`(285), `C3-Theta`(362), `C3-B-law`(384), `C2-zero-normalizer`(1322);
  section anchors `#### 1.1 Carrier and domain`(22), `#### (C2) …`(155), `#### (C3) …`(271).
- **[D3i]** `GENTOW5_PROOF_2026-08-09.md:2299–2312`, the post-D3i corrigendum.

| # | Compiler's open call | My adjudication | Decider |
|---|---|---|---|
| 1 | No literal "effective text is…" sentence in the acceptance record | **NOT ambiguous.** Two independent in-note rules fix it: (a) r1's own heading *"R1-G1 — Replace §8.2 in full with the following"* is a self-executing textual replacement; (b) the acceptance chronology *"r1 applied → T3P2 CLEAN → T3P3 CLEAN"* certifies that the two clean passes ran on base+r1. Effective = base ⊖ §8.2 ⊕ R1-G1. The spec's inference is correct; only its framing ("cannot be populated") is wrong. | **me** — template fixes the header field |
| 2 | Acceptance list "three absorptions (GENTOW2-B″, HETOW-4, GENTOW-6.4)" internally impossible | **Not a contradiction — a category slip.** By [BP] that triple is the *blueprint's three target proofs*, not the note's absorption set. The acceptance paragraph is enumerating targets and calling them absorptions. Resolution: read it as "three **targets**", and record the defect. | **me** (spec text); an optional corrigendum append to the note is **Asvin**'s call |
| 3 | GENTOW5-W(i) missing from the final scope | **Compiler missed the governing distinction.** The note's own boxed (T3-A0) absorption set is {GENTOW2-B″, HETOW-4(c)+routing, [GENTOW5-W(i)]} and §7 says *"The absorption count is three source conclusions, not four."* The narrowing record counts **blueprint-target dispositions** (2 absorbed + 1 non-instance = the 3 targets of [BP]), and its append instruction landed on exactly the two target notes [AP2],[APH]. **ABS-G5W is a genuine absorption added at revision that was never a consumption-check leg and has no dated append.** Correct disposition: EFF.T3.21 = **SUPPLIED (note-internal, per T3-A0 + §7), NOT consumption-checked, append outstanding** — an open bookkeeping obligation, *not* a scope exclusion. The spec's "NOT IN FINAL TWO-ABSORPTION SCOPE" row invites a downstream chapter-cut to drop a proved unit from the DAG. | **me** (spec text) + **Asvin/orchestrator** for the *action* (run the missing third-leg consumption check on GENTOW5-W and land its append) |
| 4 | "the blueprint's third target" referent | **RESOLVED by [BP]**: the blueprint's targets are ordered GENTOW2-B″, HETOW-4, GENTOW-6.4 — the third is **GENTOW-6.4**. The appends' provenance lines ("§5.3 item 4") confirm the same protocol. No ambiguity survives. | **me** |
| 5 | Base §7 ledger after narrowing | **Compiler resolved it backwards.** §7 is the note's mathematical ledger and is *not* superseded: it is consistent with T3-A0 and with the fact that GENTOW-6.4 never incremented the count ("GENTOW-6.4 does not increment it"). The narrowing record governs a *different predicate* — which absorptions are consumption-checked and get appends. Fix spec resolution rules 5/6/8 and EFF.T3.28 accordingly: two records, two predicates, no supersession. | **me** → codex revision |
| 6 | T1 setup designation descriptive | **Compiler missed [T1TAGS] — and the defect is larger than flagged.** T1 has a full display-tag family; **none** of the spec's six T1 XREF designations occurs in the T1 note. Four of them (`T1-C2`, `T1-TEL`, `T1-THETA`, `T1-DICT`) are **asserted as if they were T1 units** without any flag — they are T3-local display tags. Correct mappings: `T1-C2` → `C2-cocycle` (+`C2-zero-normalizer` for N(0)=1); `T1-TEL` → `C2-vartheta` + `C2-recursion`; `T1-THETA` → `C3-Theta`; `T1-DICT` → `C3-dictionary`; setup → `T1 §1.1 Carrier and domain` + `(C2)` §155. Deciding quote *inside T3 itself*: §10 row *"T1 C2–C3 is the authoritative orientation seam"* and §11.2 *"T1's conditional **C3**-B-law"* — the note already speaks T1's tag language. | **me** → codex revision (mechanical remap) |
| 7 | T1 wrap designation | **RESOLVED:** T1 `C2-wrap` (line 177), with `C2-level-1` (250) for the level-1 residue T3 declines to repeat. Same governing quote as #6. | **me** |
| 8 | GENTOW5 primitive supplier perimeter (5 facts, one XREF) | **Genuinely under-specified in T3** — T3 says only "the certified level-\(i\) … package". Not a compiler error; the finer units exist in `GENTOW5_WI_2026-08-10.md` §S1 (SETTING+STATEMENT) / §S2 (PROOF). Correct handling: keep the single XREF but mark it `PERIMETER-UNRESOLVED → EFF-GENTOW5_WI §S2`, and carry it as a 0c cross-spec reconciliation row. | **me** (defer to 0c) |
| 9 | Outer ψ₁ leg source designation | **Compiler fabricated a designation.** The spec emits `GENTOW5_PROOF…:S11.5-OUTER-ψ₁-LEG`, but S11.5 is titled *"Clause (b)'s residual display RE-INDEXED"* — a different object. The only source sentence is [D3i] line 2307: *"ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted)"*, which **does not name** the accepted statement. This violates the spec's own fidelity rule 9. Fix: delete XREF 17, replace with an open-obligation row "ψ₁ leg source statement UNNAMED in T3 and in the GENTOW5 post-D3i corrigendum → resolve at EFF-GENTOW5". (XREF 14 `S11.3-FIXED-z₁-LETTER-POWER` **is** correct — S11.3 is "(a)@i=1: the pinned-w₁ display RE-SCOPED".) | **me** → codex revision |
| 10 | No inventory type for non-instances / regressions / open obligations | **Valid format defect, confirmed.** `instance-record` is doing three incompatible jobs (ABS-G2 the absorbed instance, G6.4 the *non*-instance, E11 the rider record, FRAME-C the battery, and the scope record EFF.T3.28). Template fix in layer 4. | **me** → template change |
| 11 | Teeth granularity (one battery row guards several units) | **Valid, and the design doc already demands the missing artifact**: REVISION 2's node schema requires "TEETH disposition per source battery row (Lean theorem / executable regression / signed non-applicability)". 0a must therefore emit the **inverse** table (row → guarded units → disposition), which the pilot lacks. Template fix in layer 4. | **me** → template change |
| 12 | Unnamed "surrounding tower correctness theorem" | **Genuinely open and corpus-wide, not a T3 defect.** The identical sentence appears in `T1_GAUGE_COCYCLE_2026-08-12.md` (line 434 and honesty item 9 at 1215), also unnamed. It cannot be an XREF; it is a **0b hypothesis-closure-ledger row** (named obligation, capstone-facing). | **needs Asvin** at 0b/0d (it decides how residual factor patterns become splitting types — a trust-boundary interface) |

**Disposition counts (partition of 12): resolved-by-me 11 (#1–#11) — of which **4 require a
codex revision run** to apply to the spec text (#3, #5, #6, #9) and 2 are template-level
(#10, #11) · **needs-Asvin 1** (#12, the unnamed tower-correctness theorem → 0b ledger row).
Separately, #3 carries an orchestrator/Asvin **action** item that is not a spec question: the
GENTOW5-W consumption check was never run and its dated append never landed.

---

## LAYER 3 — COMPLETENESS

### 3.1 Load-bearing units the spec MISSED

Verified by phrase-grep against the spec (each phrase below: 0 hits in `spec/EFF-T3.md`).

1. **(T3-A0) — the note's own boxed absorption set is absent entirely** (`T3-A0`: 1 hit in
   the note, **0 in the spec**). Note §0 lines 28–35 box:
   {GENTOW2-B″, HETOW-4(c) with its routing block, [GENTOW5-W(i)]}. This is the single most
   consequential omission: the spec adjudicates T3's absorption scope for 60 lines without
   ever inventorying the note's own tagged statement of that scope. **Must be added as a
   statement block**, with the narrowing record attached as its scope annotation.
2. **The §1 negative-import fence** (line 146): *"T1's attained-origin factor \(z^\nu\), HE6
   coefficient \(\gamma_k(A)\), integral-lift domain, and WELD-M-PKG scope fence are not
   needed in the abstract T3 proof."* Absent. For the DAG this is an explicit
   **no-edge** declaration — exactly the kind of fact that prevents a formalizer from
   importing a heavy dependency. (The related exclusion of T1's conditional B-law *is*
   present in the spec's prose under the XREF table, but without its `C3-B-law` designation.)
3. **The whole of §2.4 (the proof).** Only the fence sentence at 403–404 survives. See 4.2 —
   this is a format defect, not compiler negligence, but the effect is that EFF-T3 cannot
   feed a chapter blueprint's `PROOF (steps)` field.
4. **§7's count sentence** (line 913): *"The absorption count is three source conclusions,
   not four. GENTOW-6.4 does not increment it."* Quoted nowhere; only paraphrased inside
   OPEN-CALL 5. It is the note's own arithmetic on the very question the spec adjudicates.
5. **§8's inherited-evidence sentence** (919): *"The certified tower campaign is inherited
   evidence for the source packages and their folded riders. It is not, by itself, a
   certification of this rewritten T3."* Absent. This is a provenance fence with formalization
   consequences (it says the tower campaign's machine record does not transfer).
6. **§10 CHANGES table (23 rows) — dropped wholesale** (0 hits for "CHANGES from"). The spec's
   traces *use* it implicitly ("folds the post-D3i GENTOW5 corrigendum") without citing it.
   For a note whose only round is r1, §10 **is** the supersession record vs the 2026-08-10
   composition; every RESOLUTION TRACE line should cite its §10 row.
7. **§11 hostile-arc plan + the acceptance criterion box** (lines 1204–1214: *"two clean
   hostile passes + the revised machine battery + all mandatory teeth firing"*) — absent.
   The 10 attacks overlap the teeth, but the acceptance criterion is the note's own
   definition of "accepted" and belongs in the header.
8. **Honesty-ledger item 13** — see layer 1.3.

### 3.2 Teeth / battery inventory: complete, but only in one direction

I enumerated every battery row in the note and checked its appearance in some unit's TEETH
field: **§8.1 (4 seam checks), §8.3 (8 per-absorption regressions), §8.4 (8 mandatory
mutants) — all 20 rows are consumed, zero orphans**, and §8.2 (the frame) and §8.5 (the open
coverage item) are promoted to units EFF.T3.29/.30. That is a genuinely good result.

What is missing is the **inverse table**, which REVISION 2's node schema explicitly demands
("TEETH disposition per source battery row (Lean theorem / executable regression / signed
non-applicability)"): row → guarded units → disposition. Two rows also need a disposition
decision that the pilot format has nowhere to record:

- §8.3(3) "GENTOW5-W … level-3 LW3 boundary instance" and §8.3(4)/(5)/(6) + mutants
  8.4(5)/(6)/(7) guard EFF.T3.21–25 — the units the spec demotes out of the supply list. If
  the demotion stood, seven battery rows would guard nothing. This is independent evidence
  for my OPEN-CALL-3 adjudication.
- §8.3(7) must be labelled `NON_INSTANCE_REGRESSION` — a "signed non-applicability" teeth
  disposition, the only one in the note, and the exact case the type enum cannot express.

### 3.3 Consumption table: the header's scope adjudication is HALF RIGHT

The spec's header claims the *"scope of record = TWO absorptions + one documented
non-instance"* reading governs. **Verdict: correct for the consumer-facing supply/append
protocol; wrong if read as governing the note's mathematical absorption set.**

- Correct half: only GENTOW2-B″ and HETOW-4 passed consumption checks, and exactly those two
  notes received dated "absorbed by S-2" appends (`GENTOW2_PROOF:1501`, `HETOW_RECON:837`).
  GENTOW-6.4 is confirmed NOT ABSORBED, agreeing with (G6-NONINSTANCE).
- Wrong half: "TWO" counts *blueprint-target dispositions*, not the note's absorptions. By
  [BP] the blueprint's three targets are GENTOW2-B″/HETOW-4/GENTOW-6.4; the narrowing
  sentence's own clause "the blueprint's third target was honestly narrowed" refers to
  GENTOW-6.4. ABS-G5W is a **fourth** absorption introduced at revision, listed in T3-A0 and
  §7, never a consumption-check leg, with **no append landed on `GENTOW5_WI_2026-08-10.md`**.
  Its correct status is "absorbed per the note; consumption check + append OUTSTANDING",
  not "unresolved / out of scope".

### 3.4 Missing XREF edges (DAG-relevant)

The consumption table has 22 rows; I found **7+ consumer designations with no row**: the
(G5-COND) chain cites GENTOW5 units `(a)@n`, `Corollary 6.4`, `(b)@n`, `S11.1.1`, `S11.1.3`,
`(c)@n`, `(e)@n` — all real designations in `GENTOW5_PROOF_2026-08-09.md` (S11.1.1 "descent
floor" at line 1818, etc.). EFF.T3.23 quotes the chain but XREFs only `S12.1-[R-i2]`. Each of
those is a DAG edge the chapter cut will need.

Verified-good XREFs (I checked each designation exists in its target): GENTOW2 `S5.1`
(=LEMMA GENTOW2-B′) and `S5.2` (=LEMMA GENTOW2-B″) ✓; HETOW `LEMMA HETOW-4` clauses (a)–(d) ✓
(and the landed append at HETOW:845–860 independently confirms the exact clause-by-clause
absorption boundary the spec records) ✓; GENTOW6_PROOF `S6.2` (=THE 𝒯-FREE CAP LEMMA — LEMMA
GENTOW-6.4) ✓; GENTOW6_BOXES `E11` F-1…F-4 ✓ (the E11 annex fold at 1571–1643; exact label is
"post-C11, 2026-08-12; F-1"); GENTOW5 `S11.3` ✓, `S12.1 [R-i2]` ✓, `S12.2 [R-i4]` ✓, post-D3i
corrigendum ✓. **Bad: the six T1 designations (none exists in T1) and `S11.5-OUTER-ψ₁-LEG`
(wrong section).** 7 of 22 XREF rows need repair.

---

## LAYER 4 — FORMAT VERDICT FOR THE 25-NOTE SWEEP

### 4.1 What worked

- **Header + numbered resolution rules.** Cheap, auditable, and it forced the compiler to
  state its supersession theory explicitly — which is why I could falsify rule 5/6 in ten
  minutes instead of reverse-engineering a judgment.
- **CANONICAL STATEMENT as quotation.** 88/96 blocks byte-verbatim. The "quote, never
  paraphrase" instruction demonstrably held under pressure.
- **RESOLUTION TRACE** — accurate except one over-claimed range; cheap on a one-round note.
- **TEETH per unit** — all 20 battery rows consumed, no orphans.
- **SELF-AUDIT** — the pilot's best result. 12 open calls, 8 genuinely load-bearing, and it
  refused to silently decide the hard one (GENTOW5 scope). That is exactly the behavior the
  cross-read gate is designed to reward; a compiler that had quietly picked an answer would
  have shipped a corrupted DAG.

### 4.2 What fought the note (the spec's own self-audit caught 2 of these 6)

1. **No PROOF / DERIVATION field — the format's biggest defect, and unflagged.** All of §2.4
   plus the §3/§5 instantiation derivations are dropped. But the chapter node format
   (BLUEPRINT_PHASE_DESIGN §2) requires `PROOF (steps)` per node. If 0a emits statements
   without derivations, every chapter run must re-read the source notes anyway and the
   effective spec is not "the input the formalization blueprints consume". **Fix: add a
   `DERIVATION` field — the note's own proof, quoted/step-numbered, with each step's
   justification tagged `by <EFF-ID> | by XREF | computation | definitional`.**
2. **Type enum too small** (compiler's OC-10, valid). `instance-record` carried five
   incompatible roles. **Fix the enum to:** `definition | convention | hypothesis | lemma |
   instance-record | non-instance | regression-record | battery-frame | scope-record |
   open-obligation`.
3. **Tables have no home.** The §4 absorption-boundary table was prosified (unflagged
   paraphrase); the §7 ledger and §10 CHANGES table were dropped. For proof notes, tables
   *are* the ledgers. **Fix: tables are displayable — reproduce as tables; a `LEDGER` field
   for note-level ledger tables.**
4. **No negative-import / non-edge field.** The §1 "not needed" fence and the C3-B-law
   exclusion are the note's anti-dependency declarations. **Fix: `NON-IMPORTS` field.**
5. **XREF designations unverified.** 7 of 22 rows point at designations absent from (or
   mislocated in) the target note. **Fix: every XREF must be grep-verified in the target
   file and the run must print the verification; unverifiable pointers must be emitted as
   `DESCRIPTIVE (unverified)` or as open-obligation rows — never as bare designations.**
6. **Consumer-designation edges dropped** (the 7 GENTOW5 chain units). **Fix: every source
   designation appearing in a quoted statement must appear in the consumption table.**

### 4.3 CHANGES the 0a charge template needs before the sweep fires (9)

1. Add the `DERIVATION` field (4.2#1) — the single highest-value change.
2. Replace the type enum (4.2#2).
3. Add `NON-IMPORTS`, and a `LEDGER` rule for tables (4.2#3, #4).
4. **XREF verification protocol** (4.2#5): grep-verify in target; mark unverified explicitly.
5. **Add a TEETH INVENTORY section** — the inverse table (battery row → guarded EFF-IDs →
   disposition ∈ {Lean theorem, executable regression, signed non-applicability}), as the
   node schema already requires.
6. **Header field rewrite:** "effective-text rule — quote it if the acceptance record states
   one; otherwise DERIVE it and state the two facts that fix it (the round's own replacement
   instruction + the acceptance chronology)". T3 had no literal rule and probably most notes
   don't; the current wording pushed the compiler into a spurious open call.
7. **Add a SCOPE-OF-RECORD block with a mandatory two-predicate split**: (i) the note's own
   mathematical claim set (its boxed/tagged absorption or theorem list), (ii) the
   consumption/append-protocol scope. The pilot's one substantive error came from collapsing
   these. Require the compiler to quote the note's own boxed scope display first.
8. **Require external-record checks before opening a scope call**: the absorbed notes' dated
   appends and `docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md` §5.3 are in-repo and would have
   closed OPEN-CALLs 2, 3, 4, 5 at compile time. Name these files in the charge.
9. **Quoting hygiene**: no terminal-punctuation edits inside quoted displays; truncation only
   with an explicit ellipsis; preserve the note's quote characters.

### 4.4 Cost projection for the sweep

Pilot: 36,072 B source → 47,814 B spec = **1.33×**, 31 statements at ~1.54 KB/statement, on
the corpus's **smallest** note.

Anchor density varies by an order of magnitude, and this is the load-bearing fact for sizing
(measured `\tag{` per KB): T3 0.72 · T1 0.31 · T2 0.15 · GENIND 0.06 · **GRTJB 0.00 · HE7
0.00 · GENTOW5_PROOF 0.00**. T3 is the *tagged-display genre* (every load-bearing statement
carries a `\tag`), which is exactly why "quote the tagged display" worked. The big prose
proofs anchor on §-headers and bold `LEMMA/THEOREM` instead (GRTJB: 4 named theorems
JB-DEV/VTX/TREE/CREAD + a §0M CONDITIONALITY MATRIX, 187 declaration keywords, 18 headers;
HE7: 448 declaration keywords). **The pilot therefore validates the format only on the
tagged genre — roughly 40% of corpus bytes — and gives no evidence on statement-boundary
choice in untagged prose notes, where "resolve, never invent" is under real strain.**

Corpus (the design doc's 26-note list, resolved to 28 files): **2.97 MB**, of which T3 is
36 KB. Projection at genre-differentiated ratios (≈1.3× for compressed T-units, ≈0.4–0.6×
for prose proofs): **≈1.3–2.2 MB of spec text, ≈350–600k output tokens** across the sweep.

Per-run feasibility: 13 of the 28 files exceed 100 KB; a 240 KB note is ~70k input tokens
plus 60–140 KB of output. Combined with the known ~10-minute external kill on codex runs
(memory: >8 min needs nohup+disown), **single runs stay feasible only up to ~80 KB** (14
files). Recommended shape:

| Band | Files | Runs each | Total runs |
|---|---|---|---|
| < 80 KB (T3, T4, T5, W11, HMENU3, HEX3, GENTOW1/3/4, HETOW, SIGMALAW, GENTOW5_WI, GENTOW6_PROOF, HE6, HE6R1) | ~15 | 1 | ~15 |
| 80–160 KB (GENTOW2, GENTOW6_BOXES, WELDMASTER, HE3, GENTOW5_PROOF, GENH4, LIFTCORNER, GENHN, W12, HE7) | ~10 | 2–3 (by §) | ~25 |
| > 160 KB (T1 200 K, GENIND 223 K, GRTJB 240 K, GRTJC 217 K) | ~4 | 3–4 | ~14 |
| T2 (433 K) | 1 | 5–6 + merge | ~6 |

**≈55–65 codex runs, not 25** — with a per-note header/resolution-rules run first (cheap,
fixes the supersession theory once) and a merge/renumber pass per sharded note. Sharding is
by the note's own § structure, with a shared EFF-ID prefix and a final cross-shard XREF
reconciliation. Budget note: the codex 7-day window was at 61% with a Tue 2026-08-18 reset,
so a 60-run sweep almost certainly straddles the reset — sequence the tagged T-units and the
DAG-critical notes (T1, T2, GENTOW5_PROOF, W12) before the cap and the long prose proofs
after it.

---

## VERDICT

**Sweep-readiness: GO-WITH-TEMPLATE-CHANGES (9)** — the charge template needs §4.3's nine
changes, and the pilot spec itself needs the four codex-revision fixes (layer 1.2 items 1–2,
the EFF.T3.28 truncation, the 7 XREF rows, and the scope-record split of OPEN-CALLs 3/5).
The compilation is otherwise sound: the one supersession in the note is resolved correctly,
88/96 quotations are byte-verbatim, the battery is fully consumed, and the self-audit
honestly surfaced the one call it should not have made alone.

