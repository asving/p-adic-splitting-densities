# EFF-HE7 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51) — mixed
provenance carried forward from all three shards, each independently stamped identically.
CODEX CROSS-READ OWED (post-reset) — none of the three shards, and no fold performed by
this merge run, has been through an adversarial pass; that obligation is inherited whole.
PROSE-GENRE PILOT — HE7 is (with GRTJB and GENIND) one of the tag-sparse prose-proof notes
piloting the boundary-self-audit and format-evidence machinery template v2 rule 9
anticipates; this merge additionally pilots the MERGE of a tag-sparse note sharded three
ways, including two format constructs (SERIES, supersession CHAIN) the pilot's shards
invented and flagged as v2 gaps (§7 below).**

## 1. Merge header

**Source note:** `lean/notes/openmath/HE7_PROOF_2026-08-08.md` (2652 lines).

**HEAD blob hash:** `af1686858e7faea56549eb4a42130eeab648d61d` — cited identically by all
three source shards' headers, and independently confirmed by fresh `git hash-object`
against the working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/HE7_PROOF_2026-08-08.md
af1686858e7faea56549eb4a42130eeab648d61d
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**
All three shards additionally record the file's last-touching commit as `fe589460`.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md`.

**Merged from:** `spec/EFF-HE7-s1of3.md` (HOME lines 1–1246; 63 statements, 55 xrefs,
5 open calls), `spec/EFF-HE7-s2of3.md` (HOME lines 1247–1972; 41 statements, 25 xrefs,
5 open calls), `spec/EFF-HE7-s3of3.md` (HOME lines 1973–2652; 33 statements, 30 xrefs,
5 open calls). **137 statements, 110 raw XREF citations, 15 raw open calls total before
merge-time dedup.** This file supersedes the three shards as the citable unit for all
downstream consumption; any consumer citing `EFF.HE7.*` from this point on cites the
contiguous IDs below, not the shard-local `EFF.HE7.sKof3.*` IDs. The three shard files are
**not deleted** — they remain the run-of-record trace of the sharded compilation, and in
particular remain the place where each unit's own §6 BOUNDARY SELF-AUDIT entry (the
prose-genre pilot's per-boundary reasoning) lives in full; this merged file's §7 carries
forward only the format-level conclusions (the SERIES, the two CHAINs, the edge list),
not the forty-plus individual boundary arguments.

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–63, is already contiguous from 1).
Shard 2 carries a **+63** offset (01–41 → 64–104). Shard 3 carries a **+104** offset
(01–33 → 105–137). Every `EFF.HE7.sKof3.NN` occurrence — full form and the bare `` `.NN` ``
shorthand used throughout each shard's own prose — has been mechanically rewritten
throughout the merged statement inventory below, under the following disambiguation rule
recovered from the shards' own citation discipline and verified against all 1,400+
occurrences before the rewrite was accepted:

> **A bare `` `.NN` `` reference is resolved against the shard most recently named by a
> full-form `EFF.HE7.sKof3.NN` citation earlier in the same statement unit; absent any
> such prior citation within the unit, it resolves against the unit's own home shard.**
> Context resets at every `### EFF.HE7.sKof3.NN` unit boundary (a unit never inherits
> reference context from its predecessor).

This is exactly the convention visible on the page: e.g. shard 3's `.09`'s CONDITIONALITY
opens "Targets: `EFF.HE7.s1of3.09` (rider (i), and through it `` `.35` ``, `` `.41` ``) and
`EFF.HE7.s2of3.33`(a) (rider (ii))" — the two bare refs `.35`/`.41` continue the just-named
shard-1 context (→ merged `.35`, `.41`, unchanged, since shard 1's offset is 0), and the
explicit switch to `EFF.HE7.s2of3.33` re-establishes shard-2 context (→ merged `.96`)
before the unit ends. The rewrite was performed mechanically (script, not hand-transcription,
to guarantee zero arithmetic slips at 137 units and ~1,400 citation sites) and then
audited: **zero leftover `sKof3` substrings anywhere in the merged statement inventory
(§3)** — the handful that survive elsewhere in this header and in §7 are deliberate
quotations of the original shard-local notation, illustrating the rewrite rule itself, and
never occur inside a rewritten citation (exhaustive
regex sweep), **zero out-of-range renumbered IDs** (every resolved ID lies in 1–137), and
the eleven cross-shard citation chains sampled by hand in §7 below all resolve to the
unit the source shard's own prose names. See §8's fidelity audit for the full method note.

### Header unification and blob-hash check

All three shards' front matter carries the **identical** compiled-by/cross-read-owed/
prose-genre-pilot stamp (reproduced verbatim above) and the identical HEAD blob hash.
Shards 2 and 3 additionally cross-cite the hash as "identical to the hash cited by shard 1
[and shard N]" — a three-way mutual confirmation this merge re-verified against the
working tree rather than trusting the shards' mutual citation alone.

### Governing effective-text record (unified from all three shards' independent derivations)

HE7 states no single "the effective text is …" sentence anywhere in its 2,652 lines; all
three shards derive the same rule independently from four converging facts, reproduced
here once (each shard reproduces all four, since each needed the whole rule to resolve its
own range):

**(i) The accepted body is frozen at PE3** (ANNEX F-1's head):

> "HE7 was **ACCEPTED 2/2** at PE3 (report `HE7_passPE3_report.md`, commit 111ac7f):
> 0 CRITICAL, 0 GAP, 1 MINOR — FINDING F-1, with remark R-a folded into it. The accepted
> text is byte-frozen; per the report's closing sentence the owed repair is this dated
> annex (the HMENU3 ANNEX-A pattern: appended, dated, nothing above edited)."

**(ii) Every later repair is a dated annex naming its exact target** (ANNEX R's head):

> "The accepted body above (through ANNEX F-1) is BYTE-FROZEN — md5 verified identical
> before and after this append — and per the annex pattern nothing above is edited: each
> repair is stated as a dated annex definition/lemma/rider naming its exact target."

**(iii) The note is now closed to everything but dated appends** (the final dated line):

> "**HE7-BOX-1 (arc record) — final dated line (2026-08-09).** With the annex stack
> accepted 2/2 (4a613d8, a472155), the CHALLENGE discharged, and the three owed
> one-liners landed above, this note — body + ANNEX F-1 + ANNEX R + this micro-annex —
> is **FULLY FROZEN**: dated appends only."

**(iv) `[r1]`/`[r2]`/`[r3]` were applied IN-TEXT, not by append** — every such bracket
inside the base body (lines 1–1972) is already-landed base text, not a supersession still
to be applied.

**EFFECTIVE TEXT = the whole 2,652-line file exactly as written (r1/r2/r3 already landed
in-text), READ AS CORRECTED by every later dated rider/annex that names an earlier
sentence, with no earlier sentence ever deleted** — every correction is a supersession
that quotes its target and leaves the target byte-intact above it. **Two independent
freeze predicates coexist and are never conflated below** (per shard 2's header):
**text-freeze** (the acceptance chronology, §7.1's SERIES) and **instrument-freeze** (the
§S10/§S11 battery sealed at commit `1956151`; every instrument defect found after that
seal is *disclosed*, never repaired — seven such disclosures are carried at their units).

### Scope of record — mandatory THREE-predicate split

Template v2 rule 7 asks for two predicates (absorption/supply vs. append/consumption
protocol). **HE7 needed a third, and all three shards say so identically** (shard 1 §6.3
item 7: "the v2 header has no slot for this predicate"): the note is not just a supplier
that lands nothing on others, it is also a **receiver** of four dated corrections from its
own suppliers, landing on its own frozen text from outside. The three predicates are kept
distinct everywhere below:

**A. ABSORPTION / mathematical supply set.** §S9's own inventory sentence (homed in
shard 2, `EFF.HE7.64`) is the authoritative statement:

> "**What is proved here, with no residue.** (SLOT₂) §S3; (LIFT₂) §S4 (and the corrected
> level-1 (LIFT), LEMMA HE7-L1); the level-2 transfer of every HE6 §S3–S6 lemma §S5,
> including the one new estimate §S5.3 and the block-factor reduction §S5.5; **[r2] the
> refined-key package and the derived strict slope increase §S5.8 (LEMMAS HE7-12/HE7-13 —
> PE1 FINDING F-1's gap, closed)**; the level-i package by induction §S6; (REF-TERM) §S7;
> TERMINATION §S7; the n = 8 closure §S8."

with the five HE7-BOXes (`.70`–`.78`, `.106`) as its declared residue, ANNEX-LEMMA HE7-13′
(`.96`) added post-acceptance, and ANNEX R's R1–R5 (`.108`–`.124`) discharging the
Codex-ratification repair queue at annex grade. HE7's problem statement is HE6-BOX-1 and
its exact residue (HE6 §S7.1/§S7.2, `.03`, `.10`).

**B. APPEND / consumption-protocol scope.** **HE7 lands NOTHING on any supplier, and the
note says so at least seven times across its length** (collected once here rather than
per-shard): "DISCHARGED at the source" (`.21`, on HE6's own r1 repair of FINDING HE7-F1);
"executed there or not at Asvin's discretion" (`.120`, the optional HE6R1-side gcd
widening); "owned at the source by HE6's owed repair round … this append is the
note-to-owner on the frozen copy" (`.132`); "the source-side cure is HE6R1's post-PE2
micro-annex, same wave" (`.136`); "the source-side cure is HE6R1's dated acceptance
record (post-PE3), same wave" (`.137`); the HE7-BOX-1 append's own rationale, "under the
acceptance freeze it cannot be inserted there, so it lives here" (`.103`). **Zero dated
consumption appends are claimed landed on any supplier (HE6, HE6R1, GENHN, HE3, GENIND,
W-12) by this note, and none is invented anywhere below.**

**C. INBOUND corrections received** (the predicate template v2 has no header slot for at
all — recorded identically by all three shards as a v2 gap, §7.3 below). **Four supplier
corrections land on HE7's own frozen text, all four homed in shard 3, all four targeting
shard 1:** HE6 PE2 F-1 (the η_θ^{−q(k)} coset correction to LEMMA HE7-L1, `.132`), HE6 PE3
obs-1 (the res(·)-correct restatement of the same, `.135`, **chain TERMINAL**), HE6R1 PE2
F-1 (the §S5.5 scalar correction, `.136`), HE6R1 PE3 F-1 (the pin-height correction to the
same, `.137`, **chain TERMINAL**). Plus, inbound to shard 2's own range: the five Codex
ratification findings (`.105`–`.124`, discharged by ANNEX R) and the three annex-pass
one-liners (`.129`–`.131`). **Nine inbound items in the note's final 680 lines** (shard 3's
own count).

### Resolution rules applied (merged; each shard's own numbered rule-list is a restriction
of this one to its HOME range — nothing below is dropped, only consolidated)

1. **HOME is determined by an edit's destination section, not its physical line position**
   (the same rule T1's merge used, rule 9 there): a directive physically drafted in one
   shard's range whose destination is an earlier or later shard's section resolves that
   other shard's unit and is not re-emitted as a separate statement. This is HE7's
   dominant resolution mechanism — twelve of shard 3's thirty-three units and five of
   shard 2's forty-one exist *only* to supersede text homed elsewhere (§7.3's edge table).
2. `[r1]`/`[r2]`/`[r3]` brackets throughout the base body (lines 1–1972) are already-landed
   text, applied at their own sites in chronology; the later bracket governs the earlier
   text it names.
3. **ANNEX F-1** (homed in shard 2) riders exactly two in-range shard-1 sentences by name
   (THEOREM HE7.A(3)'s `[r2]` wiring sentence, `.14`; §S6(iii)'s block sentence, `.51`) and
   falsifies LEMMA HE7-13's conclusion outside its pure-node hypothesis (`.45`'s scope pin,
   discharged by ANNEX-LEMMA HE7-13′, `.96`); it also **continues** the HE7-BOX-1 arc
   series opened in its own range (§7.1).
4. **ANNEX R** (homed in shard 3) discharges the Codex-ratification repair queue: F1 by
   ANNEX-DEF HE7-2′ + ANNEX-LEMMA R1-a + ANNEX-THEOREMS R1-b/R1-c + the R1.2 transfer
   audit (ANNEX-COROLLARY R1-d re-proves THEOREM HE7.D and COROLLARY HE7.B(ii)); F2 by
   ANNEX-LEMMA R2-a (a *license*, not a supersession — it supplies the missing gcd step of
   the §S1 CONVENTION's equivalence chain without editing the display); F3/F5 by wording
   riders; F4 by inventory completion. It supersedes ten shard-1 units and two shard-2
   units by name (§7.3's edge table), and explicitly changes **no mathematics** in shard
   2's §S9–§S11 range (its own scope adjudication: "the whole machine record" and "every
   sealed artifact and pin of §S10/§S11" are excluded).
5. **Four supplier-side dated corrections** (post-ANNEX-R, homed in shard 3) land on
   shard-1 text: two chained corrections to LEMMA HE7-L1's realized-set display (`.132`
   then `.135`, TERMINAL) and two chained corrections to the §S5.5 cocycle scalar (`.136`
   then `.137`, TERMINAL) — the merge's two supersession CHAINs, §7.2.
6. Out-of-range statements are **not** emitted as units merely because they resolve
   in-range text: §S9's boxes, §S10/§S11's battery and verdict, ANNEX F-1's new lemma, and
   ANNEX R's new definitions/lemmas/theorems/corollary are each homed once, at their own
   physical section, per rule 1.
7. External repo records (report files, `verification/openmath/*` artifacts, commit
   hashes) are reading notes only, never edits. **Fifteen commit hashes cited across the
   whole note were resolved with `git cat-file -t` — all fifteen are real commits in this
   repository** (§4's consolidated pin-verification list).
8. Where a defect in the sealed §S10/§S11 instrument (frozen at commit `1956151`) is found
   after the seal, the disclosure **is** the effective text and the instrument's behaviour
   is unchanged — seven such disclosures are carried at their units, never presented as
   repairs (this is the instrument-freeze predicate, independent of text-freeze).

### Quotation and table discipline

Unchanged from all three shards: CANONICAL STATEMENTs are verbatim source quotations or
explicitly marked `[ASSEMBLED]`; every source table is transcribed as a table and marked
`[TABLE]`; the note's three ASCII source tables (Q1's thirteen-row σ table and Q3's two
threshold tables, all homed in shard 2) are each emitted **twice** per shard 2's own
extension of the rule — verbatim as the source's fixed-width ASCII display, then again as
a `[TABLE]` Markdown transcription — because transcribing an ASCII display loses the
source bytes and quoting it verbatim alone violates template rule 5. Compiler-authored
ledgers (XREF tables, consumption ledgers, TEETH inverse tables, the SERIES/CHAIN/edge
tables of §7) are marked `[TABLE — compiler ledger]` and are not source statement units.

---

## 2. NON-IMPORTS (consolidated from all three shards; dedup marked)

`[TABLE — compiler ledger, consolidated from shard 1 §4 (15 rows), shard 2 §4 (14 rows),
shard 3 §4 (13 rows) = 42 raw rows, 2 dedup pairs → 40 distinct rows below]`

**Dedup count for this section: 2** — shard 3's own NON-IMPORTS table flags one of these
itself ("Same fence as `.08`/`.48`"); the other (the DEFINITION HE7-2 non-consumption
fence) is verified identical by direct comparison of the quoted sentences (shard 3's
"Scope of F1" row quotes shard 1's fence verbatim plus one trailing clause). Every other
row below is specific to its own section and asserted by exactly one shard.

| Fence | Explicit material NOT imported, NOT claimed, or NOT exercised | Unit(s) |
|---|---|---|
| Base change | "No base change." — re-asserted at three further consumption sites | `.04`, `.13`, `.16`, `.62` |
| Order-≥2 machinery | "No Ore theorem, no Montes/GMN index theorem, no higher-order residual-polynomial operator, no theorem of the product" — HE6 §S7.3's FGMN citation targets are not used; replaced by §S6's induction | `.04` |
| Irreducibility of test polynomials | "No irreducibility of any test polynomial, at any level"; the order-2 key and Ψ₂ are "never assumed irreducible"; "Neither requires Ψ irreducible" | `.04`, `.06`, `.18`, `.27` |
| Refine transfer / weld face | "(d) GENHN-4 (refine transfer), hence no W-9 graded weld face"; LEMMA HE7-8 "needs no 'binomial kill' (GENHN-4/GENHN.A(iv))" | `.04`, `.53` |
| GENHN.C citation | GENHN.C is consumed "as an argument template only, and only at §S8" — its statement is about a stage over a DVR and Ψ is not known irreducible; the five cases are re-derived from THEOREM HE7.A instead | `.03`, `.63` |
| HE3's stage route | HE3 needed "the resolvent over a stage ring (hence a DVR, hence irreducibility)" — the route HE7's own method replaces | `.18`, `.37` |
| Multiplicity-weighted class size (HE7-BOX-4, base) | "the multiplicity-weighted exact value \|S_{λ,r}\| = D′ℓ·m·d_r is **not needed** — the upper bound suffices" | `.15` |
| The gcd step | The §S1 CONVENTION's second equivalence is **not formal** at a reducible key — not proved by HE7 itself; supplied by ANNEX-LEMMA R2-a | `.09` |
| Peel irreducibility | LEMMA HE6R1-3's irreducibility half "which no textual argument of this note supplies" | `.38`, `.60` |
| Level-i restatements | "The level-i restatements of HE6R1-1/2/3 are not separately displayed here" | `.51` |
| §S6 gives no bound on i | "Nothing above bounds i; §S7 does." | `.52` |
| Discriminant-invariance route | Termination is "handled here by completeness rather than by the discriminant" | `.56` |
| Mixed-node continuation (post-hoc) | LEMMA HE7-13's conclusion is not claimed outside its pure-node hypothesis; ANNEX F-1: "genuinely FALSE at mixed nodes"; the naive whole-key continuation is refuted with a machine witness | `.45`, `.97` |
| DEFINITION HE7-2 not consumed at level ≤ 2 **[DEDUP — s1's fence and s3's "Scope of F1" quote the identical sentence; s3 adds one trailing clause]** | "the level-2 core §S1–S5, §S7, §S8, THEOREM HE7.A/HE7.A′/HE7.C, COROLLARY HE7.B(i) and the whole machine record do NOT consume DEFINITION HE7-2 (§S1 defines n₂ directly); first live at level 3, i.e. n ≥ 16" | `.47`, `.17`, `.106` |
| No invariance under CHANGING normalizer systems **[DEDUP — s1 + s3 R1.2 item 3 assert the identical fence; shard 3 says so itself, "Same fence as .08/.48"]** | R1.2 item 3: "no invariance under CHANGING systems is consumed anywhere … what is consumed is COHERENCE of one fixed system" | `.08`, `.48`, `.113` item 3 |
| HE7-BOX-4 (declined product link) | "We do not prove \|S_{λ,r}\| = D′ℓ·m_r·d_r … the exact link is a COUNT-side question … boxed"; after [r1]: "the closed form … stays unproved and unneeded" | `.73`, `.74` |
| Block-exponent link (one level over) | "The link between the multiplicity m … and the block exponent k … is NOT claimed"; "Likewise not claimed: L_{C_{λ₂,Z−s₂}} ≥ 2" | `.99` |
| Machine coverage (base) | "NOT exercised by machine: d_r ≥ 2 …, f₁ ≥ 2 stage genres, μ ≥ 5, level 3 …, and embedded genres" | `.70` |
| Machine coverage (after `[r1]`) | "what stays unexercised anywhere is d_r ≥ 3, f₁ ≥ 2 stage genres, μ ≥ 5 (hence proper blocks — LEMMA HE6R1-2's own configuration is proof-only) and level 3" | `.71` |
| Peel coverage | "Not exercised: a peel at μ₂ ≥ 3, and a peel at a PROPER block (both need μ ≥ 5, i.e. n ≥ 10)" | `.75` |
| Oracle asymmetry | "PARI `factorpadic` exists only on the ℤ_p side, so the char-p rows are scored against the reader plus the resultant identities" | `.72` |
| Instrument independence | "The instrument reuses HE6's rings, resultants, level-1 reader and member enumerator by import … the level-1 leg is byte-identical to the sealed HE6 code" | `.76` |
| Evidence grade | "What the machine leg establishes (instrument grade, not acceptance)" | `.92` |
| Repair vs disclosure | Seven instrument defects "byte-frozen, so disclosed here rather than edited"; "no repair is possible on a frozen instrument and none is needed" | `.85`, `.86` |
| Annex scope (F-1) | "The annex covers exactly PE3 F-1 plus the folded R-a remark and NOTHING else"; "No other display is touched" | `.93`, `.95` |
| Annex grade (F-1) | "the annex text itself is a post-acceptance append and has NOT been through a hostile pass" | `.93` |
| Blast radius (F-1) | ANNEX F-1's full "What does not move" list — the body's statements, sealed artifacts, HE7.A at pure nodes, §S8's dictionary, HE7.B's grade sentences, every box | `.104` |
| The naive continuation refuted | "The naive whole-f_S continuation is REFUTED, not merely unproved" — with a machine witness | `.97` |
| Slot disjointness (declined mechanism) | "the mechanism is NOT slot disjointness … What protects the companion classes on-disk is RESIDUE SEPARATION" | `.96` |
| Scope of HE7-2′ | "replaces DEFINITION HE7-2's normalizer line and base sentence, everything else unchanged"; "levels 1 and 2 are byte-unchanged" | `.107` |
| Annex grade (ANNEX R) | "this annex is a post-ratification append and has NOT itself been through a hostile pass"; R1.2 "none of it has been through a hostile pass" | `.105`, `.115` |
| Honesty invariant on R1-d | "had any site failed, this corollary would instead be an OPEN box, per the honesty invariant" | `.114` |
| Level-3 leg's limits | "(i) members are ℤ_p only … (ii) g₂ = 1 throughout — the within-class deep twist ϑ_t (t ≥ 1) is structurally invisible at this family … not every letter of R1-b" | `.117` |
| Existential direction | "the body's sentences still claim only what they proved" — the machine witnesses do not lift R3's rider | `.122` |
| R4's blast radius | "LEMMA HE7-12(c)'s CONCLUSION is unaffected — the erratum is citation-completeness on one sentence, no transfer breaks" | `.123` |
| R5's blast radius | "Nothing consumes the group structure" | `.124` |
| Source-side ownership (×4) | The optional HE6R1 erratum; "owned at the source by HE6's owed repair round"; "the source-side cure is HE6R1's post-PE2 micro-annex"; "the source-side cure is HE6R1's dated acceptance record (post-PE3)" | `.120`, `.133`, `.136`, `.137` |
| Non-propagation of the coset defect | The four-site enumeration: "None of THEOREM HE7.A/HE7.A′/HE7.C/HE7.D, COROLLARY HE7.B, the annex stack, or a sealed number moves." | `.133` |
| Scope of the line-value form | "it agrees with the pin-height form exactly when j₁ = 0 … at ℓ = 1 … the dated line's ℓ = 1 sentences stand as written" | `.137` |
| What does not move (ANNEX R) | The full list at `.126`, and its four-item "what moves, all additive" complement | `.126` |

---
## 3. Statement inventory (137 units, contiguous, in source order)

### EFF.HE7.01  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the title headline plus the Status block, lines 1–15, quoted verbatim]

> “# HE7 — **HE6-BOX-1 CLOSED**: (LIFT₂) and (SLOT₂) PROVED (with the level-1 (LIFT) threshold CORRECTED), the whole level ladder proved by ONE induction, and the ladder proved to **TERMINATE** (depth ≤ log₂n − 2; at n = 8 exactly one level, μ₂ = 2) — so the level-2 read decides σ on the three-σ family that certified the box”

> “**Unit:** HE7 (the two final lemmas of the uniformity program).
> **Status:** complete at commit 2. Statements §S1–S2; proofs §S3–S8; battery
> §S10 (runner sealed at commit 1 with preregistered P1–P5 and six teeth,
> `verification/openmath/he7_checks.py`); verdict §S11 (**GREEN, 0 violations,
> 6/6 teeth, 1,335/1,335 PARI agreements** — **[r1]** on the Ψ ∤ f_S stratum;
> the remaining 8 of 1,587 members are the peel stratum, decided in the r1 leg
> below, so 1,587/1,587 net). Level-2 frame §S1; (SLOT₂) §S3;
> (LIFT₂) §S4 (with **FINDING HE7-F1**, HE6's level-1 (LIFT) over-stated —
> non-propagating); the transfer audit §S5 (every HE6 §S3–S6 lemma one level
> up, including the ONE genuinely new estimate, §S5.3); the level ladder at
> **every** level by one induction §S6; **TERMINATION** §S7; the n = 8 closure
> and THEOREM HE7.A §S8; COROLLARY HE7.B and the boxes §S9; battery §S10;
> verdict §S11. **Attempt grade 0/2** — no hostile pass has run on this note.”

**CONDITIONALITY:** **The grade sentence is HISTORICAL and superseded.** “Attempt grade 0/2 — no hostile pass has run on this note” is superseded, in chronological order, by §S9's `[r2]` (PE1 ran: 0C/1G/3M, grade stays 0/2), §S9's `[r3]` (PE2 CLEAN: 0/2 → 1/2), ANNEX F-1's BOX-1 append (PE3 CLEAN: 1/2 → **2/2, HE7 IS ACCEPTED**), ANNEX R's BOX-1 append (ratification CHALLENGE — acceptance **ANNOTATED, not revoked**, on THEOREM HE7.D / COROLLARY HE7.B(ii) / HE7.A(3)-level-3 only), and the final dated line (annex stack ACCEPTED 2/2, CHALLENGE discharged, note **FULLY FROZEN**). All five are homed in shards 2–3.

**DERIVATION:** Not a mathematical unit; the record is the note's own status chronology.

**RESOLUTION TRACE:** Base lines 1–15; status superseded at lines 1285–1304 (§S9 `[r2]`/`[r3]`), 1948–1959 (ANNEX F-1 BOX-1 append), 2442–2462 (ANNEX R BOX-1 append), 2493–2497 (final dated line).

**TEETH:** The §S10/§S11 battery is the tooth of record for the numbers quoted here; inventoried in shard 2.

---

### EFF.HE7.02  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 17–38.

> “**[r1] 2026-08-08 REPAIR ROUND (post-HE6R1).** The reconciliation note
> `HE6R1_RECON_2026-08-08.md` (verdict 850e77e) returned two findings against
> THIS note, both applied here, every site tagged `[r1]`:
> **FINDING HE6R1-F1** — THEOREM HE7.A(3)'s trichotomy and THEOREM HE7.C's jump
> condition repeat HE6.B's four-case enumeration error one level up (a repeated
> level-2 factor of degree ≥ 2 at ℓ₂ = 1 admits no α-refine); reworded to the
> widened box with **identical bounds** (LEMMA HE6R1-1), non-propagation at
> n ≤ 15 re-derived independently in §S2 and §S7.
> **FINDING HE6R1-F2** — the hypothesis **Ψ ∤ f_S** was never stated (the
> level-2 analogue of Codex PE1 finding 2's Φ′ ∤ f); added as a §S1 CONVENTION
> with the peel of **LEMMA HE6R1-3**, and displayed at every consumption site
> (THEOREM HE7.A, COROLLARY HE7-7″, §S5.5, §S8's dictionary).
> Also folded: HE6 §S1's (LIFT) is now **LEMMA HE6-1L [r1]** (HE6's R3 adopted
> LEMMA HE7-L1 verbatim), so this note's level-1 consumption is a citation
> rather than a correction — the use-site threshold check is displayed in §S4.3.
> The runner and artifacts of §S10/§S11 are **BYTE-FROZEN at seal 1956151**; the
> Ψ | f_S stratum they already isolate (8 of 1,587 members, status
> `DEGENERATE-key-divides`) is decided by the peel in the additive
> post-seal leg `verification/openmath/he7r1_supp.py` (§S11 [r1]: 8/8 decided,
> 2/2 PARI on σ(f) AND 2/2 PARI on σ(Ψ)). **Attempt grade stays 0/2 post-r1** —
> a repair round does not upgrade an arc, and the r1 text owes a fresh hostile
> pass.”

**CONDITIONALITY:** The grade clause is superseded exactly as at `.01`. The substantive content (both findings applied in-text) is what makes resolution rule 2 correct: there is no separate r1 round-block to apply — the r1 text IS the base text of this range.

**DERIVATION:** Round record, not a derivation. The two findings' mathematical content is discharged at `.14` (F-1, the widened trichotomy) and `.09`/`.38`/`.60` (F-2, the Ψ ∤ f_S convention and its peel).

**RESOLUTION TRACE:** Base lines 17–38; the “verbatim” claim in the HE6-1L fold clause is re-scoped “as-of the r1 landing” by the dated line at 2555–2569 (see `.20`).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F1` — grep-verified count **4**.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — grep-verified count **4**.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-1` — grep-verified count **9**.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — grep-verified count **8**.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — grep-verified count **4**.

**TEETH:** `he7r1_supp.py` (8/8 peels, 2/2 + 2/2 PARI) — the r1 leg; inventoried in §5 and homed as a verdict unit in shard 2.

---

### EFF.HE7.03  [fence]

**CANONICAL STATEMENT:** [ASSEMBLED — §S0's five positive-consumption bullets, lines 42–71, quoted verbatim; the sixth (negative) bullet is `.04`]

> “## S0. WHAT THIS UNIT CONSUMES
>
> * **HE6 @ 1f5a417** (`lean/notes/openmath/HE6_PROOF_2026-08-08.md`) —
>   DEFINITION HE6-1 (the enlarged test family Ψ_{κ,r}), LEMMA HE6-0 (disk
>   criterion), LEMMA HE6-0′ (local forcing), LEMMA HE6-1 (the ξ-side),
>   LEMMA HE6-2 / HE6-2′ (the two evaluation displays), COROLLARY HE6-2″,
>   LEMMA HE6-3 (slope counts, (SEP)-free), LEMMA HE6-4 (nonemptiness),
>   LEMMA HE6-5 (Galois equivariance), THEOREM HE6.A, and the ϖ-convention of
>   §S1. **HE6-BOX-1 (§S7.1) and its exact residue (§S7.2) are this unit's
>   problem statement.**
> * **[r1] HE6 @ r1 + HE6R1_RECON @ 850e77e** — HE6 §S1's (LIFT) is now
>   **LEMMA HE6-1L [r1]**, which is LEMMA HE7-L1 of §S4.1 verbatim (HE6's repair
>   R3 adopted this note's form), so the level-1 lift is CITED here, not
>   corrected; and three reconciliation lemmas are consumed: **LEMMA HE6R1-1**
>   (the widened jump condition, HE7.C's bounds — §S2, §S7),
>   **LEMMA HE6R1-2** (block projection: μ₂, the level-2 sides and the residual
>   radical are computable from f at a PROPER block, without exhibiting f_S —
>   §S5.5, and it supersedes HE7-BOX-4 in read form), **LEMMA HE6R1-3** (the
>   level-2 peel at Ψ | f_S — §S1 CONVENTION, §S5.5, §S8).
> * **GENHN @ HEAD** — LEMMA GENHN-2 (**THE SLOT LEMMA**) as the ladder's base
>   case, and its "twist (letters only)" paragraph (the normalizer cocycle is
>   a letter twist; counts are twist-blind). GENHN.C's §S7 case analysis is
>   consumed **as an argument template only**, and only at §S8: every input it
>   uses is re-supplied at level 2 by this note.
> * **HE3 @ 7a95449** — DEFINITION 1/2 (stage resolvent, polygon, labels,
>   decided leaves); the elementary convex duality (★) of HE3-3 step 1.
> * **Classical only** — resultant symmetry, the ultrametric inequality,
>   uniqueness (hence Galois invariance) of the extension of v to K̄₀,
>   completeness of O, integral closedness of O, and the existence of
>   irreducibles of every degree over a finite field.”

**CONDITIONALITY:** The HE6-1L clause's “verbatim” is re-scoped as-of the r1 landing (see `.20`). Everything else is a declaration, not a claim.

**DERIVATION:** Declaration, not derivation.

**RESOLUTION TRACE:** Base lines 42–71; the HE6-1L verbatim clause re-scoped at 2555–2569.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:DEFINITION HE6-1` — count **7**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0` — count **17**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0′` — count **5**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1` — count **15**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-2` — count **10**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-2′` — count **4**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:COROLLARY HE6-2″` — count **1**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-4` — count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-5` — count **5**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:THEOREM HE6.A` — count **19**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-1` — count **9**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.C` — count **19**.
XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-3` — count **15**.

**Designation counted but NOT emitted as an XREF:** the GENHN “twist (letters only)” paragraph is quoted by phrase, not designation; fixed-string `twist (letters only)` has count **0** in `GENHN_PROOF_2026-08-08.md`, whose own heading (line 729) reads `**The twist (letters only).**` with a terminal period inside the bold. The referent is unique and verified at that line; carried descriptively. Recorded as source defect 1 in §8.

**TEETH:** NONE (import declaration).

---

### EFF.HE7.04  [fence]

**CANONICAL STATEMENT:** verbatim, lines 72–78.

> “* **NOT consumed (deliberate, inherited from HE6).** (a) **No base change.**
>   (b) **No Ore theorem, no Montes/GMN index theorem, no higher-order
>   residual-polynomial operator, no theorem of the product** — the FGMN
>   citation targets displayed in HE6 §S7.3 are *not* used; this note replaces
>   them with the induction of §S6. (c) **No irreducibility of any test
>   polynomial**, at any level. (d) GENHN-4 (refine transfer), hence no W-9
>   graded weld face.”

**CONDITIONALITY:** None — this is the note's own negative-import fence, load-bearing for the DAG. It is re-asserted at three consumption sites: THEOREM HE7.A's closing sentence (`.13`), COROLLARY HE7.B (`.16`), and LEMMA HE7-8's “**The argument needs no "binomial kill"** (GENHN-4/GENHN.A(iv))” (`.53`).

**DERIVATION:** Declaration, not derivation. Its discharge is the note's own architecture: (b) is discharged by §S6's induction replacing the FGMN citation targets; (c) by (SLOT₂)/(LIFT₂)'s proofs (`.11`, `.12`), which never assume Ψ irreducible; (d) by §S7's completeness argument (`.53`).

**RESOLUTION TRACE:** Base lines 72–78; untouched by any later round.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-4` — count **6**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:W-9` — count **13**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S7.3` — count **1**.

**TEETH:** NONE (negative fence).

---

### EFF.HE7.05  [hypothesis]

**CANONICAL STATEMENT:** verbatim, lines 84–91 (the inherited level-1 frame).

> “Inherited from HE6 §S1: O a complete DVR, π a uniformizer, v(π) = 1,
> K₀ = Frac(O), residue field F_Q, both characteristics, v extended uniquely
> to K̄₀. Φ′ ∈ O[x] monic irreducible of degree D′ = e₁f₁, all roots of
> v = h/e₁ with gcd(h, e₁) = 1; dv := e₁v; ψ ∈ F_Q[T] irreducible of degree
> f₁; K := F_Q(η_θ) ≅ F_{Q^{f₁}} with η_θ = res(θ^{e₁}π^{−h}); for a (T1)/(T2)
> point ξ, ι_ξ : K → k̄ is the F_Q-embedding η_θ ↦ η_ξ. ϖ := x^{i₀}π^{a₀} with
> i₀h + e₁a₀ = 1, 0 ≤ i₀ < e₁, so dv(ϖ(ξ)) = 1 exactly at every (T1)/(T2)
> point. f is monic on the genre-G opening locus with disc f ≠ 0.”

**CONDITIONALITY:** Inherited hypothesis set; unconditional as a hypothesis. `disc f ≠ 0` is load-bearing at `.36` (LEMMA HE7-6: f_S | f because f is separable), `.53` (LEMMA HE7-8's contradiction), and `.62` (THEOREM HE7.A′'s hypothesis). The ϖ-convention is the level-1 normalizer choice that makes `.20`'s fold-rider (a) apply — and it is exactly what the shard-3 dated correction from HE6 PE2 F-1 shows to be a TWISTED read at level 1 (see `.19`).

**DERIVATION:** Hypothesis, not derivation. The one derived clause — “so dv(ϖ(ξ)) = 1 exactly at every (T1)/(T2) point” — follows from `i₀h + e₁a₀ = 1` and `dv = e₁v` on a point with `dv(ξ) = h`, `v(π) = 1`.

**RESOLUTION TRACE:** Base lines 84–91; untouched by later rounds. ANNEX-DEF HE7-2′ (shard 3) reproduces this frame as the level-1 datum with `n₁(k) := ϖ^k` — “levels 1 and 2 are byte-unchanged”.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S1` — grep-verified count **7** (a SECTION-ANCHOR pointer, not a lemma designation: the fixed string also matches `S10`/`S11` prefixes, so the count is an upper bound on genuine `§S1` hits. The referent — HE6 §S1's frame and ϖ-convention — is independently pinned by `LEMMA HE6-1L`, count **4**, which lives in that section).

**TEETH:** NONE (hypothesis).

---

### EFF.HE7.06  [definition]

**CANONICAL STATEMENT:** verbatim, lines 93–109.

> “**DEFINITION HE7-1 (the level-2 datum).** A pair (λ, r) with
> λ = u/ℓ ∈ ℚ in lowest terms, λ > D′h, and r ∈ K[Z] monic irreducible with
> r(0) ≠ 0, d_r := deg r. Attached objects:
>
> * **the order-2 key** Ψ := Ψ_{λ,r} of DEFINITION HE6-1, monic of degree
>   **D″ := D′ℓd_r**; *never assumed irreducible*;
> * **the level-2 value** **dv₂ := ℓ·dv = e₁ℓ·v**;
> * **the level-2 residue field** **K₂ := K[Z]/(r) = K(β) ≅ F_{Q^{f₁d_r}}**;
> * **the level-2 disk threshold** **T₂ := ℓd_r·u = ℓ²d_r·λ**;
> * **a level-2 point** = a ξ ∈ K̄₀ with (T1), (T2), dv(Φ′(ξ)) = λ and
>   ι_ξ(r)(β_ξ) = 0, where β_ξ := res(Φ′(ξ)^ℓ/ϖ(ξ)^u);
> * **the level-2 transport** ι_ξ^{(2)} : K₂ → k̄, the ι_ξ-semilinear
>   embedding with β ↦ β_ξ (well defined because β_ξ is a root of the
>   irreducible ι_ξ(r));
> * **the level-2 normalizer system** **n₂(k) := ϖ^{m(k)}Φ′^{s(k)}** where
>   ℓ·m(k) + s(k)·u = k with 0 ≤ s(k) < ℓ — possible and unique because
>   gcd(u, ℓ) = 1. At every level-2 point, dv₂(n₂(k)(ξ)) = k EXACTLY.”

**CONDITIONALITY:** Unconditional definition. Two hypotheses inside it are machine-certified load-bearing: `gcd(u, ℓ) = 1` (tooth HE7-T-SLOT2TIE: at gcd ≠ 1 the slot-min is not exact and no level-2 residue is well defined) and `λ > D′h` (inherited from DEFINITION HE6-1, consumed at `.25`). **“never assumed irreducible” is a standing NON-IMPORT** re-asserted at `.13`, `.18`, `.62`.

**DERIVATION:** Definition. The one derived clause — `n₂(k)`'s existence/uniqueness — is Bézout at `gcd(u, ℓ) = 1`; the exactness clause `dv₂(n₂(k)(ξ)) = k` is `dv₂(ϖ(ξ)) = ℓ` (from `.05`) plus `dv₂(Φ′(ξ)) = ℓλ = u`, giving `ℓm(k) + s(k)u = k`.

**RESOLUTION TRACE:** Base lines 93–109; untouched by any later round. ANNEX-DEF HE7-2′ (shard 3, lines 2034–2037) explicitly REPRODUCES this: “At i = 1 the recursion reproduces §S1's n₂(k) = ϖ^{m(k)}Φ′^{s(k)} verbatim, and the transport tower reproduces DEFINITION HE7-1's ι^{(2)}: **levels 1 and 2 are byte-unchanged.**”

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:DEFINITION HE6-1` — count **7**.

**TEETH:** HE7-T-SLOT2TIE (gcd hypothesis load-bearing) · Q2/HE7-SLOT2 (12,632 exactness identities).

---

### EFF.HE7.07  [definition]

**CANONICAL STATEMENT:** verbatim, lines 111–116 (the substitution table, with its exactness verification).

> “The substitution table that makes every HE6 statement transfer is
>
>     (e₁, f₁, h, D′, Φ′, dv, ϖ, K, D′h)  ↦  (ℓ, d_r, u, ℓd_r, Ψ, dv₂, n₂(1), K₂, T₂),
>
> and it is exact: D′ = e₁f₁ ↦ ℓd_r = D″/D′, D′h ↦ ℓd_r·u = T₂,
> gcd(h, e₁) = 1 ↦ gcd(u, ℓ) = 1, deg ψ = f₁ ↦ deg r = d_r.”

**CONDITIONALITY:** Unconditional. This dictionary is the engine of the whole §S5 transfer audit and of §S6's induction; every “transfers verbatim” verdict in §S5 is a claim ABOUT this substitution.

**DERIVATION:** The four exactness checks are displayed inline and are definitional identities from `.06` (`D″ = D′ℓd_r`, `T₂ = ℓd_r·u`) plus DEFINITION HE7-1's `gcd(u, ℓ) = 1` and `d_r := deg r`.

**RESOLUTION TRACE:** Base lines 111–116; generalised (not superseded) by DEFINITION HE7-2's level recursion at `.50`, itself corrected by ANNEX-DEF HE7-2′.

**TEETH:** Indirect — every §S5 “transfers verbatim” verdict rides this table; the level-2 machine legs (Q1–Q5) are its instance test at i = 1.

---

### EFF.HE7.08  [convention]

**CANONICAL STATEMENT:** verbatim, lines 118–134.

> “**CONVENTION (the level-2 twist is REAL — HE6's twist-free convention is
> NOT available one level up).** At level 1 HE6 could take all normalizers to
> be powers of the single element ϖ, killing the cocycle. At level 2 the
> normalizers ϖ^{m}Φ′^{s} genuinely mix two generators, and
>
>     n₂(k)·n₂(k′) / n₂(k+k′) = (Φ′^{ℓ}/ϖ^{u})^{c},
>     c := ( s(k) + s(k′) − s(k+k′) ) / ℓ  ∈ ℤ,
>
> whose residue at a level-2 point ξ is **β_ξ^{c}** — a nonzero element of
> ι_ξ^{(2)}(K₂). Consequently every level-2 residual polynomial is defined
> only relative to a FIXED choice of n₂, and changing the choice multiplies
> its coefficients by explicit powers of β. **Every statement used below is
> twist-invariant** (vanishing/non-vanishing at a residue, degree, and the
> multiset of irreducible factors up to K₂^×-scaling), which is GENHN's
> "counts are twist-blind, letters are twisted" (J-D0) at level 2. The
> battery's reader carries the twist explicitly, and tooth **HE7-T-BADTWIST**
> shows that dropping it mispredicts σ — so this is not a bookkeeping remark.”

**CONDITIONALITY:** Unconditional at level 2. **Generalised at every level by ANNEX-LEMMA R1-a (shard 3),** whose clause (iv) states: “At i = 2, (R1.1) gives τ₂(a,b) = Λ₁^{c₁(a,b)} — exactly §S1's CONVENTION display with its integer c.” The displayed `c ∈ ℤ` is sharpened there to `c ∈ {0, 1}` (R1-a(ii)); the display is not edited, and `{0,1} ⊂ ℤ` so nothing conflicts. **The twist-invariance clause is the note's own load-bearing scope fence** and is re-audited item-by-item at ANNEX R R1.2 (shard 3).

**DERIVATION:** [ASSEMBLED — the display is a one-line computation from `.06`] `n₂(k)n₂(k′)/n₂(k+k′) = ϖ^{m(k)+m(k′)−m(k+k′)}Φ′^{s(k)+s(k′)−s(k+k′)}`; the two exponent sums satisfy `ℓ·(m-sum) + u·(s-sum) = 0` and `s`-sum `≡ 0 (mod ℓ)`, so with `c := (s-sum)/ℓ` the quotient is `(Φ′^ℓ/ϖ^u)^c`. Its residue at a level-2 point is `β_ξ^c` by DEFINITION HE7-1's `β_ξ := res(Φ′(ξ)^ℓ/ϖ(ξ)^u)`.

**RESOLUTION TRACE:** Base lines 118–134; extended (not superseded) by ANNEX-LEMMA R1-a(ii)(iii)(iv) at 2046–2065.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.

**TEETH:** HE7-T-BADTWIST (21 (p, s, member) reads change when the twist is dropped; twisted read == PARI 480/480) — the twist is machine-load-bearing.

---

### EFF.HE7.09  [convention]

**CANONICAL STATEMENT:** verbatim, lines 136–154.

> “**CONVENTION [r1, HE6R1-F2] (the standing level-2 hypothesis: Ψ ∤ f_S).**
> Throughout §S2–S8, **Ψ ∤ f_S** — equivalently the Ψ-development's constant
> coefficient A₀^{(2)} ≠ 0, equivalently dv₂(Ψ(ρ)) < ∞ at every root ρ of f_S.
> *This is not a restriction: if Ψ | f_S then* **LEMMA HE6R1-3 (the level-2
> peel)** *gives gcd(f_S, Ψ) = Ψ with Ψ IRREDUCIBLE over O of degree D″ and*
>
>     e(Ψ) = e₁ℓ ,      f(Ψ) = f₁d_r ,
>
> *a SIMPLE factor (disc f_S ≠ 0), so f_S = Ψ·f_S′ with Ψ ∤ f_S′, every root
> of f_S′ still a level-2 point, and every statement below applied to f_S′
> with μ₂ − 1 in place of μ₂; the peel happens at most once.* Without the
> convention a root ρ of f_S with Ψ(ρ) = 0 has dv₂(Ψ(ρ)) = ∞ and carries NO
> finite level-2 label, so COROLLARY HE7-7″ fails, P₂ loses its j = 0 pin and
> THEOREM HE7.A(1)'s Σ_{λ₂}L_{λ₂} = μ₂ is false — the exact level-2 analogue
> of the Φ′ | f stratum at level 1 (HE6's §S1 CONVENTION [r1], Codex PE1
> finding 2). This was found BY the machine: HE7's own sealed battery isolates
> the stratum as status `DEGENERATE-key-divides` (8 of 1,587 members) and the
> reconciliation note named it FINDING HE6R1-F2; the post-seal leg
> `he7r1_supp.py` decides all 8 by the peel (§S11 [r1]).”

**CONDITIONALITY:** **The displayed equivalence chain was UNDERIVED as landed, and is closed only by ANNEX-LEMMA R2-a (shard 3).** ANNEX R R2 states the defect exactly (lines 2338–2346): the first equivalence is polynomial division, but “The second needs Ψ ∤ f_S ⟹ gcd(Ψ, f_S) = 1 — NOT formal, because Ψ is never assumed irreducible”. ANNEX-LEMMA R2-a supplies `gcd(F, Ψ) ∈ {1, Ψ}` for monic `F` with Galois-stable (T1)/(T2) root set, closing the chain. **Codex graded this a GAP as stated; the note flags the grade for Asvin** (line 2389–2395) — recorded as OPEN-CALL 1. The peel clause itself rests on LEMMA HE6R1-3, an external lemma the note consumes without reproving (its irreducibility half is machine-tested only, per `.02`'s A5 leg — “which no textual argument of this note supplies”, line 1425).

**DERIVATION:** [ASSEMBLED] The convention's *content* is cited, not derived: the peel is **LEMMA HE6R1-3** (external, `HE6R1_RECON`). The note derives two things inline: (a) why the convention is needed — “a root ρ of f_S with Ψ(ρ) = 0 has dv₂(Ψ(ρ)) = ∞ and carries NO finite level-2 label, so COROLLARY HE7-7″ fails, P₂ loses its j = 0 pin and THEOREM HE7.A(1)'s Σ_{λ₂}L_{λ₂} = μ₂ is false”; (b) why the peel fires at most once — Ψ is a SIMPLE factor because `disc f_S ≠ 0` (`.05`). The level-genericity of both is `.49`; the level-i restatement is not separately displayed (`.51`).

**RESOLUTION TRACE:** Base lines 136–154 (landed at r1). Equivalence chain licensed at 2348–2387 (ANNEX-LEMMA R2-a + consumption rider (i)). Level-generic at 1051–1058 (`.49`).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — count **4**.
XREF: `lean/notes/openmath/CODEX_HE6PE1_2026-08-08.md:F2` — grep-verified count **4**. (The note's own wording “Codex PE1 finding 2” has fixed-string count **0** in the target — the report capitalises it, `Finding 2` count **1**, `findings 2` count **1** — so the XREF is emitted at the report's own repair-queue designation `F2`, whose row is “**R2 (CRITICAL, F2): add the Φ′ ∤ f convention**”. Recorded as source defect 4 in §8.)

**TEETH:** The sealed battery's `DEGENERATE-key-divides` status (8 of 1,587) — the stratum was found BY the machine · `he7r1_supp.py` A1–A5 (8/8, 8/8, 8/8, 2/2 PARI σ(f), 2/2 PARI σ(Ψ)).

---

### EFF.HE7.10  [scope-record]

**CANONICAL STATEMENT:** verbatim, line 156.

> “The two lemmas HE6 §S7.2 named as its exact residue, stated here in full.”

**CONDITIONALITY:** None. This sentence is the note's own identification of its problem statement with HE6's boxed residue, and it is the claim §S9 later qualifies: “Under-counted: three items beyond (LIFT₂) and (SLOT₂) are needed and were not named” (line 1259, shard 2), plus two more at `[r1]`. So the sentence is TRUE as a description of what HE6 named, and INCOMPLETE as a description of what HE7 needed — the note says so itself.

**DERIVATION:** Pointer sentence; the discharge is `.11` and `.12`.

**RESOLUTION TRACE:** Base line 156; qualified at 1257–1273 (§S9, shard 2).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S7.2` — count **5**.

**TEETH:** NONE.

---

### EFF.HE7.11  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 158–175 — **(SLOT₂)**.

> “**(SLOT₂) [PROVED, §S3].** Let C ∈ O[x] with deg C < D″ and let
> C = Σ_{s<ℓd_r} c_s·Φ′^{s} (deg c_s < D′) be its Φ′-development. Then at
> **every** level-2 point ξ,
>
>     dv₂(C(ξ)) = min_{s<ℓd_r} ( ℓ·dv(c_s) + s·u )   EXACTLY,
>
> where dv(c_s) := min_{i<D′}(e₁v(c_{s,i}) + ih) is the level-1 slot value.
> Moreover: (a) the minimising s all lie in ONE class mod ℓ; (b) writing that
> class as s₀ + ℓt (t < d_r) and m₀ := m(k), s₀ := s(k) for k the minimum,
> the residue is
>
>     res( C(ξ)/n₂(k)(ξ) ) = ι_ξ^{(2)}( Σ_{t<d_r} γ_t·β^{t} ) ≠ 0,
>     γ_t := res( c_{s₀+ℓt}(θ)/ϖ(θ)^{m₀−tu} ) ∈ K,
>
> an element of K₂ depending on C and k only (not on ξ). (c) For an
> ARBITRARY ξ ∈ K̄₀ the inequality
> dv₂(C(ξ)) ≥ min_s( ℓ·dv_ξ(c_s) + s·ℓ·dv(Φ′(ξ)) ) holds, with
> dv_ξ(c) := min_i(e₁v(c_i) + i·dv(ξ)).”

**CONDITIONALITY:** **Unconditional at level 2**, on DEFINITION HE7-1's hypotheses (`gcd(u, ℓ) = 1`; `r` irreducible of degree `d_r`) plus the level-1 SLOT LEMMA (GENHN-2). Explicitly **not** conditional on Ψ irreducible (`.18`). At level i ≥ 3 the analogous statement is ANNEX-THEOREM R1-b (shard 3), whose residue display carries an extra fixed twist unit `ϑ_t`; R1-b's own scope sentence records that at i = 1 “every θ_t = 1 (ϖ-powers multiply) and the display is (SLOT₂) byte-for-byte”, so **this unit is untouched by the ANNEX R repair**.

**DERIVATION:** [ASSEMBLED — §S3, lines 320–360, Steps 1–3 verbatim plus the closing sentence]

> “Let ξ be a level-2 point and C = Σ_{s<ℓd_r}c_sΦ′^{s} with deg c_s < D′
> (unique, since deg C < D′ℓd_r and Φ′ is monic of degree D′).
>
> **Step 1 (the term values, exactly).** ξ satisfies (T1)/(T2), so the level-1
> SLOT LEMMA (GENHN-2) gives dv(c_s(ξ)) = dv(c_s) EXACTLY for every s, hence
> dv₂(c_s(ξ)) = ℓ·dv(c_s). Also dv₂(Φ′(ξ)) = ℓ·dv(Φ′(ξ)) = ℓλ = u. Therefore
>
>     dv₂( c_s(ξ)·Φ′(ξ)^{s} ) = ℓ·dv(c_s) + s·u   EXACTLY, for every s.   (S3.1)
>
> **Step 2 (class separation — no cross-class ties).** ℓ·dv(c_s) + s·u ≡ s·u
> (mod ℓ), and s ↦ s·u mod ℓ is a bijection of ℤ/ℓ because gcd(u, ℓ) = 1.
> Hence two slots s ≢ s′ (mod ℓ) have term values in distinct classes mod ℓ, so
> they are never equal. The minimum of (S3.1) is therefore attained inside a
> single class s₀ + ℓ·{0,…,d_r−1} — **exactly ℓ classes of exactly d_r slots
> each**, the (e₁, f₁) pattern of GENHN-2 with (e₁, f₁) ↦ (ℓ, d_r).
>
> **Step 3 (within-class: the residue, and no cancellation).** Let k be the
> minimum, s₀ = s(k), m₀ = m(k), and write the class slots as s₀ + ℓt,
> t < d_r. A slot attains iff ℓ·dv(c_{s₀+ℓt}) + (s₀+ℓt)u = k, i.e. iff
> dv(c_{s₀+ℓt}) = m₀ − tu (recall ℓm₀ + s₀u = k). Divide the attaining terms by
> n₂(k)(ξ) = ϖ(ξ)^{m₀}Φ′(ξ)^{s₀}; since ϖ^{m₀} = ϖ^{m₀−tu}·ϖ^{tu},
>
>     c_{s₀+ℓt}(ξ)Φ′(ξ)^{s₀+ℓt} / n₂(k)(ξ)
>         = [ c_{s₀+ℓt}(ξ)/ϖ(ξ)^{m₀−tu} ] · [ Φ′(ξ)^{ℓ}/ϖ(ξ)^{u} ]^{t} .  (S3.2)
>
> The first bracket has dv = 0 and, by the residue clause of GENHN-2 together
> with the transport identity (the residue at ξ of a level-1 slot is the
> ι_ξ-image of the residue at θ — HE6-1 Step 2), residue ι_ξ(γ_t) with
> γ_t = res(c_{s₀+ℓt}(θ)/ϖ(θ)^{m₀−tu}) ∈ K; γ_t ≠ 0 exactly for the attaining
> t. The second bracket has residue β_ξ^{t}. Summing over the class,
>
>     res( C(ξ)/n₂(k)(ξ) ) = Σ_{t<d_r} ι_ξ(γ_t)·β_ξ^{t}
>                          = ι_ξ^{(2)}( Σ_{t<d_r} γ_t β^{t} ).            (S3.3)
>
> Now r is irreducible over K of degree d_r, so **{1, β, …, β^{d_r−1}} is a
> K-basis of K₂**; since the γ_t lie in K and at least one attaining γ_t is
> nonzero, the sum (S3.3) is **nonzero**. Hence dv₂(C(ξ)) equals the minimum
> exactly — there is no cancellation to be had — and the residue is the stated
> element of K₂, which depends only on (C, k). Clause (c) is the ultrametric
> inequality applied twice (to the Φ′-development and then inside each c_s),
> with no exactness claimed. ∎”

Justification tags: Step 1 `by XREF LEMMA GENHN-2` + definitional; Step 2 `computation` (Bézout/bijection at gcd(u, ℓ) = 1); Step 3 `by XREF LEMMA GENHN-2` (residue clause) + `by XREF LEMMA HE6-1` Step 2 (transport identity) + `computation` (K-basis independence); clause (c) `by` the ultrametric inequality (classical, `.04`'s "Classical only" list at `.03`).

**RESOLUTION TRACE:** Base lines 158–175 (statement) + 320–360 (proof); untouched by every later round. ANNEX-THEOREM R1-b (shard 3) generalises without editing: “At i = 1 every θ_t = 1 … and the display is (SLOT₂) byte-for-byte.”

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1` — count **15**.

**TEETH:** Q2 / HE7-SLOT2 (P2): `v(Res(f, C)) = 2·dv₂(C)` EXACTLY for `deg C < D″ = 4` on both level-2 classes, **0 violations in 12,632 checks** · HE7-T-SLOT2TIE (at `gcd(u, ℓ) ≠ 1` the classes share heights and exactness fails).

---

### EFF.HE7.12  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 177–191 — **(LIFT₂)**.

> “**(LIFT₂) [PROVED, §S4].** Let k ∈ ℤ and put s₀ := s(k), m₀ := m(k). If
>
>     m₀ ≥ (d_r − 1)·u + (D′ − 1)·h                                    (†₂)
>
> then for **every** c ∈ K₂ there is C ∈ O[x] with deg C < D″, level-2 slot
> value exactly k (for c ≠ 0), and level-2 residue
> res(C(ξ)/n₂(k)(ξ)) = ι_ξ^{(2)}(c) at every level-2 point ξ. A k-uniform
> sufficient condition is
>
>     k ≥ (ℓd_r − 1)·u + ℓ·(D′ − 1)·h.                                 (‡₂)
>
> Both bounds are satisfied with room to spare wherever this note uses
> (LIFT₂) (§S4.3). The hypothesis (†₂) is **not removable**: §S4.2 exhibits
> heights at which the residue map is not surjective, and tooth
> HE7-T-LIFT2SHARP verifies the exact reachable set by enumeration.”

**CONDITIONALITY:** Unconditional at level 2, on (†₂)/(‡₂) and on LEMMA HE7-L1 at the `d_r` within-class heights `m_t = m₀ − tu`. **The level-1 lemma it invokes (LEMMA HE7-L1 = HE6-1L) had its realized-set display corrected by the shard-3 dated append (the η_θ^{−q(k)} coset).** The correction's own NON-PROPAGATION enumeration (line 2534–2537) covers exactly this use site: “the (LIFT₂) proof (§S4.2, L436–437) calls HE7-L1 only at m_t ≥ (D′−1)h — full-T heights, the surjectivity clause — so its exact-residue choices γ_t stand”. So **(LIFT₂) is unmoved by the correction**; the sharpness statement `.22` is where the coset wording matters. At level i ≥ 3 the analogue is ANNEX-THEOREM R1-c, which adds one pre-twist line (lift `γ_t·ϑ_t^{−1}` instead of `γ_t`) and leaves the bound recursion unchanged.

**DERIVATION:** [ASSEMBLED — §S4.2, lines 434–444, verbatim]

> “*Proof of (LIFT₂).* Let k, s₀ = s(k), m₀ = m(k) with (†₂), and let c ∈ K₂.
> Expand c = Σ_{t<d_r}γ_tβ^{t} in the K-basis {β^t} (unique). For each t with
> γ_t ≠ 0 put m_t := m₀ − tu; then m_t ≥ m₀ − (d_r−1)u ≥ (D′−1)h by (†₂), so
> LEMMA HE7-L1 supplies c_{s₀+ℓt} ∈ O[x] with deg < D′, dv(c_{s₀+ℓt}) = m_t and
> res(c_{s₀+ℓt}(θ)/ϖ(θ)^{m_t}) = γ_t. Set c_{s} := 0 for all other s and
> C := Σ_s c_sΦ′^{s}; then deg C < D′ℓd_r = D″. By construction
> ℓ·dv(c_{s₀+ℓt}) + (s₀+ℓt)u = ℓm_t + s₀u + ℓtu = ℓm₀ + s₀u = k for every t
> with γ_t ≠ 0, and the omitted slots contribute +∞, so by (SLOT₂) the level-2
> slot value is exactly k and the residue is ι_ξ^{(2)}(Σ_tγ_tβ^t) =
> ι_ξ^{(2)}(c). For (‡₂): m₀ = (k − s₀u)/ℓ ≥ (k − (ℓ−1)u)/ℓ, and
> k ≥ (ℓd_r−1)u + ℓ(D′−1)h gives m₀ ≥ (d_r−1)u + (D′−1)h = (†₂). ∎”

Justification tags: the K-basis expansion `by EFF.HE7.06` (`K₂ = K(β)`, `deg r = d_r`); the per-slot lift `by EFF.HE7.19` (LEMMA HE7-L1); the slot-value and residue readout `by EFF.HE7.11` ((SLOT₂)); (‡₂) ⟹ (†₂) `computation`.

**RESOLUTION TRACE:** Base lines 177–191 (statement) + 434–444 (proof); untouched. Level-i analogue ANNEX-THEOREM R1-c at 2165–2182 (shard 3). Level-1 supplier corrected at 2501–2553, with non-propagation to THIS site enumerated there as item (i).

**TEETH:** Q3 / HE7-LIFT1 + HE7-LIFT2 (P3): exact reachable sets vs closed-form thresholds in **ten frames**, 5/5 level-1 and 5/5 level-2 · HE7-T-LIFT2SHARP (the sharpness tooth; deliberately run at `f₁ ≥ 2`, `d_r ≥ 2` because the σ rows cannot reach them).

---

### EFF.HE7.13  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 197–216 and 250–251 — **THEOREM HE7.A, clauses (1) and (2), plus the closing fence.** (Clause (3), which has a different supersession history and is the exact target of ANNEX F-1's rider, is `.14`; the boundary call is audited at §6 item 6.)

> “**THEOREM HE7.A (THE LEVEL-2 READ DECIDES — HE6.A one level up).** Let
> (λ, r) be a level-2 datum arising as a label of f (LEMMA HE6-2″), let
> S := S_{λ,r} be its label class and f_S ∈ O[x] the monic factor of f with
> root set S (LEMMA HE7-6), **with Ψ ∤ f_S** (§S1 CONVENTION [r1]; if Ψ | f_S,
> peel by LEMMA HE6R1-3 first and read f_S′ at μ₂ − 1). Put
> μ₂ := deg f_S / D″ ∈ ℤ_{≥1} and let
> f_S = Ψ^{μ₂} + Σ_{j<μ₂}A_j^{(2)}Ψ^{j} be the Ψ-development,
> P₂ := lower hull of {(j, dv₂(A_j^{(2)}))}_{j ≤ μ₂}. Then:
>
> 1. every side of P₂ has slope λ₂ > T₂, and Σ_{λ₂} L_{λ₂} = μ₂;
> 2. for every slope λ₂ = u₂/ℓ₂ of P₂ with **separable** level-2 residual
>    R_{λ₂} ∈ K₂[Z] and every monic irreducible r₂ | R_{λ₂},
>
>        |S_{λ₂,r₂}| = D″·ℓ₂·deg r₂ ,
>
>    and S_{λ₂,r₂} is the root set of a single monic irreducible factor of f
>    over O with
>
>        e = e₁·ℓ·ℓ₂ ,      f = f₁·d_r·deg r₂ ;”

> “The proof uses **no base change, no irreducibility of Ψ, and no order-≥2
> citation**.”

**CONDITIONALITY:** Conditional on the standing convention **Ψ ∤ f_S** (`.09`), whose equivalence chain is licensed only by ANNEX-LEMMA R2-a (shard 3). Clause (2) is additionally conditional on **separability of R_{λ₂}**; the inseparable case is clause (3) (`.14`), and the *simple factor of an inseparable residual* — decided by neither (2) nor (3) as written — is ANNEX F-1's folded remark R-a (shard 2), which routes it to HE7-13′(a)'s block. **Both clauses are untouched by every one of the five ratification findings** (ANNEX R BOX-1 append, line 2450: “the level-2 core (§S1–S5, §S7, §S8, THEOREM HE7.A/HE7.A′/HE7.C, COROLLARY HE7.B(i), the whole machine record) is untouched by all five findings”).

**DERIVATION:** [ASSEMBLED — §S5.7's *Proof of THEOREM HE7.A(1)(2)*, lines 787–796, verbatim]

> “*Proof of THEOREM HE7.A(1)(2).* (1) is LEMMA HE7-9(a) plus
> Σ_{λ₂}n_{λ₂} = deg f_S = D″μ₂ with n_{λ₂} = D″L_{λ₂}. (2) is HE6 §S6.2
> verbatim with the substitution: the classes S_{λ₂,r₂} partition the slope's
> roots (R_{λ₂} separable), Σ_{r₂}|S_{λ₂,r₂}| = n_{λ₂} = D″L_{λ₂} =
> Σ_{r₂}D″ℓ₂deg r₂; each class is nonempty (LEMMA HE7-10) and Galois-stable
> (LEMMA HE7-11) with every member of degree ≥ D″ℓ₂deg r₂ over K₀ (LEMMA
> HE7-5), so |S_{λ₂,r₂}| ≥ D″ℓ₂deg r₂; the sandwich forces equality, each
> class is a single Galois orbit, i.e. the root set of one monic irreducible
> factor of f_S (hence of f) of that degree; and e ≥ e₁ℓℓ₂, f ≥ f₁d_rd_{r₂}
> with ef = D″ℓ₂d_{r₂} = (e₁ℓℓ₂)(f₁d_rd_{r₂}) forces equality on both. ∎”

Justification tags: (1) `by EFF.HE7.41` (LEMMA HE7-9(a) and (b)); (2) `by XREF HE6 §S6.2` (the transferred sandwich) + `by EFF.HE7.41` (HE7-10 nonemptiness) + `by EFF.HE7.42` (HE7-11 Galois) + `by EFF.HE7.29` (HE7-5 local forcing) + `by EFF.HE7.07` (the substitution table).

**RESOLUTION TRACE:** Base lines 197–216, 250–251 (statement, with the `[r1]` Ψ ∤ f_S hypothesis already landed) + 787–796 (proof). Untouched by ANNEX F-1 and by all five ANNEX R findings. Its label-class partition is re-derived per block at ANNEX-LEMMA HE7-13′(a) (shard 2).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:COROLLARY HE6-2″` — count **1**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S6.2` — count **3**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:THEOREM HE6.A` — count **19** (the level-1 statement this is “one level up”).

**TEETH:** Q1 / HE7-READ2 + HE7-SIG2 (P1): the level-2 read predicts σ member by member, **1,335 PARI jobs, 1,335 agree, 0 mismatch** · HE7-T-CASEB-SEP · HE7-T-RANK · HE7-T-WITHHOLD.

---

### EFF.HE7.14  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 217–248 — **THEOREM HE7.A clause (3), the `[r1]` widened trichotomy, with its `[r2]` wiring sentence and its non-propagation derivation.**

> “3. **[r1, HE6R1-F1 — the widened trichotomy]** at a slope λ₂ = u₂/ℓ₂ whose
>    residual R_{λ₂} has a repeated irreducible factor r₂ of multiplicity
>    m₂ ≥ 2, split on the product **ℓ₂·deg r₂** (NOT on ℓ₂ alone):
>    if **ℓ₂·deg r₂ = 1** (so ℓ₂ = 1, λ₂ ∈ ℤ and r₂ = Z − s₂ with s₂ ∈ K₂
>    **K₂-rational**) the level-2 α-refine Ψ ↦ Ψ − w exists — (LIFT₂)
>    supplies w at height λ₂ with residue s₂ **because s₂ ∈ K₂** — and the
>    refine chain is FINITE (LEMMA HE7-8), so the read continues — **[r2,
>    HE7-PE1 F-1]** the read AT the refined key Ψ − w (and at every iterate
>    Ψ − W of the chain) is licensed by **LEMMA HE7-12** (§S5.8): dv₂(w) =
>    λ₂ > T₂, so the whole §S5 package and clauses (1)(2) hold verbatim at
>    the refined key, and the strict slope increase λ₂^{(0)} < λ₂^{(1)} < ⋯
>    that LEMMA HE7-8 consumes is **LEMMA HE7-13**, derived, not assumed;
>    if **ℓ₂·deg r₂ ≥ 2** the read
>    passes to level 3, which is the same statement one level further up
>    (THEOREM HE7.D) and cannot occur unless μ₂ ≥ 4 (THEOREM HE7.C [r1]).
>    *The pre-r1 text split on ℓ₂ = 1 vs ℓ₂ ≥ 2 and so claimed an α-refine at
>    (ℓ₂, deg r₂) = (1, ≥ 2), where NO ŝ₂ exists: its residue would have to be
>    a root β₂ of r₂, and β₂ ∈ K₂(β₂) ∖ K₂ is not a value of (LIFT₂). This is
>    HE6.B's enumeration error one level up (FINDING HE6R1-F1).*
>    **Non-propagation at μ₂ ≤ 3 (re-derived here, not transcribed).** The
>    mis-stated branch and the level-3 branch both need a repeated r₂ with
>    m₂ ≥ 2 and ℓ₂·deg r₂ ≥ 2, hence a side of length
>    L_{λ₂} = ℓ₂·deg R_{λ₂} ≥ ℓ₂·m₂·deg r₂ = m₂·(ℓ₂ deg r₂) ≥ 2·2 = 4, hence
>    **μ₂ ≥ Σ_{λ₂}L_{λ₂} ≥ 4** by clause (1). So at every μ₂ ≤ 3 — in
>    particular at every n ≤ 15 (COROLLARY HE7.B(i): D′ ≥ 2 gives
>    μ ≤ ⌊n/D′⌋ ≤ 7 and THEOREM HE7.C gives μ₂ ≤ μ/2 ≤ 7/2, hence
>    **μ₂ ≤ ⌊μ/2⌋ ≤ 3 since μ₂ ∈ ℤ_{≥1}** — [r2, HE7-PE1 F-3] the pre-r2
>    display "μ₂ ≤ μ/2 ≤ 3" is false at μ = 7 without the integer floor;
>    ⌊7/2⌋ = 3, so the conclusion is unchanged) and at n = 8 (μ₂ = 2) —
>    clause (3)'s
>    only live case is ℓ₂·deg r₂ = 1, where the old and new statements
>    coincide: §S8's dictionary and the n = 8 closure are untouched.”

**CONDITIONALITY:** **Three live conditionalities, all cross-shard.**
(a) **ANNEX F-1 riders the `[r2]` wiring sentence** (target 1, quoted verbatim there at lines 1638–1648). Its “Read as”: *at a PURE node (R_{λ₂} a power of Z − s₂ on a single side) — verbatim. At a MIXED node, the citation routes through ANNEX-LEMMA HE7-13′ below: the node is first split into its class blocks (clause (a)); the refine is the α-refine OF THE REPEATED CLASS'S OWN BLOCK, whose node IS pure, so LEMMAS HE7-12/HE7-13/HE7-8 apply to it verbatim; every other class is read at its own block.* The mixed-node case is **first live at μ₂ = 3, i.e. n = 12**, and **vacuous at every machine-certified degree (μ₂ = 2 forces pure)**.
(b) **The level-3 branch inherits the ANNEX R repair** (line 2248): “THEOREM HE7.A(3)'s level-3 branch inherits the repair the same way”, i.e. THEOREM HE7.D is read through ANNEX-DEF HE7-2′.
(c) The whole clause rests on the standing convention Ψ ∤ f_S (`.09`).

**DERIVATION:** The clause carries its own two derivations inline, both quoted above: (i) the refutation of the pre-r1 branch — “its residue would have to be a root β₂ of r₂, and β₂ ∈ K₂(β₂) ∖ K₂ is not a value of (LIFT₂)”, `by EFF.HE7.12` ((LIFT₂) realises exactly K₂); (ii) the non-propagation arithmetic `L_{λ₂} = ℓ₂·deg R_{λ₂} ≥ ℓ₂·m₂·deg r₂ = m₂·(ℓ₂ deg r₂) ≥ 4` hence `μ₂ ≥ 4`, `by EFF.HE7.13` (clause (1)) + `computation`, with the ⌊·⌋ floor supplied at `[r2, HE7-PE1 F-3]`. The α-refine's existence is `by EFF.HE7.12`; its finiteness `by EFF.HE7.53` (LEMMA HE7-8); the refined-key license `by EFF.HE7.44` (LEMMA HE7-12); the strict slope increase `by EFF.HE7.45` (LEMMA HE7-13). The μ₂ ≥ 4 gate for the level-3 branch is re-derived inside `.15`'s DERIVATION (§S7).

**RESOLUTION TRACE:** Base lines 217–248 (r1 widening + r2 wiring + r2 floor already landed). Riddered at 1638–1648 (ANNEX F-1 target 1) and 1818–1826 (its wiring paragraph); the μ₂ ≥ 4 gate re-derived per block at 1782–1786 (HE7-13′(a)); level-3 branch repaired at 2248 (ANNEX-COROLLARY R1-d).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F1` — count **4**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-1` — count **9**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6.B` — count **6**.

**TEETH:** Q1's 42 α-refine firings (all one-step) · `he7r2_supp.py` B1–B5 (42/42, 210/210, 42/42, 42/42, 13/13) · the PE3 probe `he7_pe3_probe12.py` (144/144 at μ₂ = 3, n = 12 — the first machine contact of the mixed case this clause's rider governs) · `he7annex_supp.py` (96/96 at μ₂ = 4, n = 16).

---

### EFF.HE7.15  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 253–277 — **THEOREM HE7.C [r1] (TERMINATION)**, with its `[r1]` widening rider.

> “**THEOREM HE7.C [r1] (TERMINATION — the ladder is FINITE at every n).** A
> node requiring a level jump — **a side of slope λ = u/ℓ carrying a repeated
> irreducible residual factor r (multiplicity m ≥ 2) with ℓ·deg r ≥ 2**, which
> is exactly HE6-BOX-1's configuration in its WIDENED form (COROLLARY HE6.B
> [r1]: the complement of "separable residual, or repeated only at a
> K-rational linear factor at an integer slope"; the pre-r1 condition
> "ℓ ≥ 2" omitted the ℓ = 1, deg r ≥ 2 branch) — satisfies μ ≥ 4, and the
> level-2 problem it opens has
>
>     μ₂ ≤ μ / (ℓ·d_r) ≤ μ/2 .
>
> Hence the number J of level jumps in any history satisfies
> **J ≤ log₂ μ − 1 ≤ log₂ n − 2**; interleaved α-refines are finite
> (LEMMA HE7-8) and every other step strictly decreases μ. In particular:
> **at n = 8 (μ = 4, D′ = 2) there is exactly ONE jump, and the level-2
> problem has μ₂ = 2 — level 3 is degenerate. The first n at which a level-3
> object can be needed is n = 16.**
>
> **[r1] The widening costs NOTHING in the bounds** (= LEMMA HE6R1-1): both
> displays only ever use the product ℓ·d_r ≥ 2 — the first as
> L_λ ≥ ℓ·m·d_r = m(ℓd_r) ≥ 4, the second as μ₂ ≤ deg R_λ/d_r ≤ μ/(ℓd_r) —
> and ℓ·d_r ≥ 2 IS the widened box's defining inequality, supplied by both of
> its branches (ℓ ≥ 2 with d_r ≥ 1, and ℓ = 1 with d_r ≥ 2). So J, the n = 8
> verdict and the n = 16 threshold are literally unchanged; the pre-r1 proof
> of the bounds is reused verbatim with "ℓ ≥ 2" replaced by "ℓd_r ≥ 2" (§S7).”

**CONDITIONALITY:** **The final sentence's existential is SUPERSEDED by ANNEX R R3 (shard 3).** R3 states (lines 2399–2405) that the sentence “The first n at which a level-3 object can be needed is n = 16” claims an existential the displays do not prove; the displays prove only `J ≥ 2 ⟹ μ ≥ 8 ⟹ n ≥ 16`. **Rider, quoted verbatim from R3:**

> “**Rider: read both sentences
> as "level 3 / J = 2 is unreachable below n = 16; n = 16 is the first
> degree NOT EXCLUDED by the bound."** No consumer uses more (THEOREM
> HE7.C's gate, COROLLARY HE7.B(i)'s n ≤ 15 clause and §S8's "level 3 is
> degenerate" all consume the necessary direction).”

The existential direction was later *exhibited* by ANNEX R R1.3's constructed n = 16 family (79/79, machine-instance grade), but the body's sentences still claim only what they proved. Otherwise unconditional and **untouched by all five ratification findings**.

**DERIVATION:** [ASSEMBLED — §S7's *Proof of THEOREM HE7.C [r1]*, lines 1136–1168, verbatim]

> “*Proof of THEOREM HE7.C [r1].* A node needs a level jump exactly in
> HE6-BOX-1's WIDENED configuration: a side of slope λ = u/ℓ carrying a repeated
> irreducible residual factor r of **multiplicity m ≥ 2** with
> **ℓ·d_r ≥ 2** (d_r = deg r). *That this is exactly the jump set is the
> four-case enumeration of COROLLARY HE6.B [r1]: a separable residual is decided
> by THEOREM HE6.A at every ℓ; a repeated K-rational linear factor at an integer
> slope (ℓ = d_r = 1) is decided by HE3's stage-α recentering, an α-refine; the
> complement is a repeated irreducible r with ℓ·d_r ≥ 2 — the pre-r1 condition
> "ℓ ≥ 2" dropped its ℓ = 1, d_r ≥ 2 half (FINDING HE6R1-F1). Both displays
> below use only the product ℓ·d_r ≥ 2, so they are unchanged: this is
> LEMMA HE6R1-1.* Then
>
>     μ ≥ L_λ = ℓ·deg R_λ ≥ ℓ·m·d_r = m·(ℓ·d_r) ≥ 2·2 = 4 ,
>
> so **μ ≥ 4** at every jump. The level-2 problem is f_S with
> μ₂ = deg f_S/D″ = |S_{λ,r}|/(D′ℓd_r) ≤ n_λ/(D′ℓd_r) = D′L_λ/(D′ℓd_r) =
> deg R_λ/d_r ≤ μ/(ℓd_r) ≤ μ/2 (LEMMA HE6-3(b) for n_λ = D′L_λ; the
> multiplicity-weighted exact value |S_{λ,r}| = D′ℓ·m·d_r is **not needed** —
> the upper bound suffices). Iterating: if jumps occur at levels 1..J then
> μ_i ≥ 4 for i ≤ J and μ_J ≤ μ/2^{J−1}, so 4 ≤ μ/2^{J−1}, i.e.
> **J ≤ log₂ μ − 1**; with μ ≤ n/D′ ≤ n/2 this is **J ≤ log₂ n − 2**. Every
> non-jump step either strictly decreases μ (a decided split) or is an α-refine
> (finite, LEMMA HE7-8) or terminates the branch (μ = 1: a single irreducible
> factor of the current key's degree, σ read off). Hence the read is a finite
> tree. At n = 8: D′ ≥ 2 and μ ≥ 4 force D′ = 2, μ = 4, so J ≤ 1 and the one
> jump lands at μ₂ ≤ 4/(ℓd_r) = 4/2 = **2** — a level-3 jump would need
> μ₂ ≥ 4, impossible. **[r1]** The "μ₂ ≥ 4" here is the widened condition's own
> bound, re-derived at level 2: a level-3 jump needs a repeated level-2
> irreducible r₂ with m₂ ≥ 2 and ℓ₂·deg r₂ ≥ 2, hence
> L_{λ₂} ≥ m₂(ℓ₂ deg r₂) ≥ 4, hence μ₂ ≥ 4 (THEOREM HE7.A(1)) — so the widening
> does not open a level-3 door at μ₂ ≤ 3, and the mis-stated α-refine branch of
> the pre-r1 HE7.A(3) is likewise vacuous there. The first degree at which J = 2
> is possible is n = D′μ with μ ≥ 8, i.e. **n = 16**. ∎”

Justification tags: the jump-set identification `by XREF COROLLARY HE6.B [r1]` + `by XREF LEMMA HE6R1-1`; `μ ≥ 4` `computation`; the `μ₂` bound `by XREF LEMMA HE6-3(b)` + `computation` (**explicitly NOT** by the multiplicity-weighted class size, which is HE7-BOX-4's declined link); the iteration `computation`; α-refine finiteness `by EFF.HE7.53`; the level-2 re-derivation `by EFF.HE7.13` (clause (1)). **The closing n = 16 sentence carries R3's rider.**

**RESOLUTION TRACE:** Base lines 253–277 (statement) + 1136–1168 (proof), r1 already landed. Both n = 16 sentences riddered at 2397–2412 (ANNEX R R3). Machine witnesses for the existential direction at 2294–2334 (R1.3's run record).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:COROLLARY HE6.B` — count **6**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-1` — count **9**.
XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-3` — count **15** (the stage-α recentering's home note; the specific "stage-α recentering" phrase is carried descriptively — see source defect 2 in §8).

**TEETH:** Q1's 42 one-step α-refines (“(REF-TERM) in action, never approaching the bound”) · `he7rannex_supp.py` (79/79 constructed two-jump n = 16 witnesses — the existential direction, machine-instance grade).

---

### EFF.HE7.16  [corollary]

**CANONICAL STATEMENT:** verbatim, lines 279–305 — **COROLLARY HE7.B**.

> “**COROLLARY HE7.B (HE6-BOX-1 CLOSES; the program consequence, stated at
> the grade the composition supports).** (i) At every leaf whose history's
> boxed nodes all have μ₂ = deg f_S/D″ ≤ 3 — sufficiently μ ≤ 7 (THEOREM
> HE7.C: μ₂ ≤ μ/2 ≤ 7/2 with μ₂ ∈ ℤ, so μ₂ ≤ ⌊7/2⌋ = 3 [r2, HE7-PE1 F-3]),
> hence at **every** leaf of every degree **n ≤ 15** (n ≤ 15 forces
> μ ≤ ⌊n/D′⌋ ≤ ⌊15/2⌋ = 7 since D′ ≥ 2 at a composite stage and μ ∈ ℤ
> [r2]), and at every one of HE6-BOX-1's machine-certified live
> configurations (n = 8) — the σ-decision holds: THEOREM HE7.A + THEOREM
> HE7.C decide σ with no base change and no order-≥2 citation, so
> **[GENHN-HE(μ)] holds at EVERY leaf at those degrees** and HE6's
> COROLLARY HE6.B loses its exclusion clause there — **[r1]** the exclusion
> clause being the WIDENED one (COROLLARY HE6.B [r1]), whose ℓ = 1 /
> deg r ≥ 2 branch §S1–S6 decides as a LITERAL instance (HE6R1_RECON §S3.2,
> ten items checked), and the boxed node's level-2 starting data (μ₂, the
> level-2 sides, the residual up to its radical) being read off f by
> **LEMMA HE6R1-2** when the block is PROPER — the configuration that first
> occurs at μ ≥ 5, i.e. n ≥ 10, hence inside this clause's own region.
> (ii) At every degree, the
> same conclusion holds with the level-i lemmas of THEOREM HE7.D in place of
> the level-2 ones; THEOREM HE7.D is proved by the induction of §S6, whose
> inductive step is exactly §S3–S5 with the substitution table, so (ii) is
> complete **modulo the arc grade of this note** (§S9). Consequently
> **[GENHN-HE(μ)] holds at every leaf**, HE6-BOX-1 is discharged, and through
> HE6.B + GENIND.B + W-12.D the uniformity theorem's conditional stack
> reduces to **arc grades + the named hardening boxes** — no open piece of
> mathematics remains in the σ-decision chain. **This is a composition
> claim at attempt grade 0/2, not an acceptance claim** (§S9).”

**CONDITIONALITY:** **Split by clause; this is the note's single most conditionality-laden unit.**
- **(i) is UNTOUCHED by all five ratification findings** (ANNEX R BOX-1 append names “COROLLARY HE7.B(i)” in the untouched list, line 2451). It rests on THEOREM HE7.A (`.13`, `.14`), THEOREM HE7.C (`.15`), and the external LEMMA HE6R1-2 for the proper-block start.
- **(ii) carried the ratification ANNOTATION and is RE-PROVED by ANNEX-COROLLARY R1-d** (shard 3, lines 2237–2253): “COROLLARY HE7.B(ii) consumes THEOREM HE7.D as a package and is re-proved with it, with its OWN conditionality sentence ("modulo the arc grade of this note", §S9) unchanged.” The re-proof is at **annex grade** (post-ratification append, never hostile-passed).
- **(ii)'s clause “whose inductive step is exactly §S3–S5” is superseded by dated correction M-B** (shard 3, line 2491): read it as *“with (SLOT) := ANNEX-THEOREM R1-b, (LIFT) := ANNEX-THEOREM R1-c, and the §S5 transfer audited per R1.2 (ANNEX-COROLLARY R1-d)”*.
- The closing grade sentence (“attempt grade 0/2, not an acceptance claim”) is superseded by the acceptance chronology at `.01`; ANNEX F-1's closing list confirms “COROLLARY HE7.B's grade sentences” do not move as *text*.

**DERIVATION:** [ASSEMBLED — the corollary is a composition; its two derivations are displayed inline] (i) `μ ≤ ⌊n/D′⌋ ≤ ⌊15/2⌋ = 7` at `D′ ≥ 2`, then `μ₂ ≤ ⌊μ/2⌋ = 3` `by EFF.HE7.15` + `computation` (the two ⌊·⌋ floors are the `[r2, HE7-PE1 F-3]` repair); then the σ-decision `by EFF.HE7.13`+`.14`+`.15`; the widened branch's literal decidability `by XREF HE6R1_RECON §S3.2`; the proper-block start `by XREF LEMMA HE6R1-2`. (ii) `by EFF.HE7.17`/`.48` (THEOREM HE7.D) — as corrected by ANNEX-COROLLARY R1-d.

**RESOLUTION TRACE:** Base lines 279–305 (r1 and r2 landed). (ii) re-proved at 2237–2253; its inductive-step clause riddered at 2491 (M-B); (i) confirmed untouched at 2450–2452.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ)]` — count **1**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:COROLLARY HE6.B` — count **6**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:S3.2` — count **6**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND.B` — count **19**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W-12.D` — count **19**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-1` — count **9**.

**TEETH:** The whole §S10/§S11 battery is (i)'s evidence at n = 8; `he7annex_supp.py` (n = 16) and `he7rannex_supp.py` (n = 16, level-3 fired) are the first machine contact of the (ii)-region. **No tooth discharges (ii)'s inductive claim** — it is proof-only, at annex grade.

---

### EFF.HE7.17  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 307–314 — **THEOREM HE7.D, the §S2 display.** (The §S6 display of the same theorem is `.48`; the two are separate units because dated correction M-B names the §S2 one specifically — boundary audit §6 item 12.)

> “**THEOREM HE7.D (the ladder at every level).** The level-0 datum
> (Φ_0 = x, w_0 = v, ℓ_0 = e₁, g_0 = f₁, u_0 = h, K_0 = F_Q) and the
> recursion of DEFINITION HE7-2 generate, at every level i ≥ 0, objects
> (Φ_i, w_i, ℓ_i, g_i, u_i, K_i, T_i, n_i) for which (SLOT_i), (LIFT_i), the
> disk criterion, the two evaluation displays, the slope counts, the
> nonemptiness certificate, Galois equivariance and the class-size theorem
> all hold, with the SAME proofs. Level 1 is GENHN-2 + HE6 §S3–S6; level 2 is
> §S3–S5 of this note; the inductive step is §S6.”

**CONDITIONALITY:** **This display carried the ratification CRITICAL (Codex F1) and is DISCHARGED only by ANNEX R, at annex grade.**
- The clause “**with the SAME proofs**” is superseded by dated correction M-B (line 2491): read it as *“with (SLOT) := ANNEX-THEOREM R1-b, (LIFT) := ANNEX-THEOREM R1-c, and the §S5 transfer audited per R1.2 (ANNEX-COROLLARY R1-d)”*.
- “the recursion of DEFINITION HE7-2” must be read through **ANNEX-DEF HE7-2′**, since DEFINITION HE7-2's own normalizer line and base sentence were **incompatible** (R1.0, lines 1992–2005: “The two are incompatible… THEOREM HE7.D's proof was unproved as displayed”).
- Scope of the defect, adjudicated (lines 2008–2011): “the level-2 core §S1–S5, §S7, §S8, THEOREM HE7.A/HE7.A′/HE7.C, COROLLARY HE7.B(i) and the whole machine record do NOT consume DEFINITION HE7-2 (§S1 defines n₂ directly); first live at level 3, i.e. n ≥ 16.”
- **Honest grade** (line 2255–2259): “R1-a/R1-b/R1-c are full displayed proofs; R1.2 is a transfer audit of exactly §S6's and LEMMA HE7-12(c)'s kind; none of it has been through a hostile pass.”

**DERIVATION:** The §S2 display is a forward statement; its proof is §S6's inductive step, carried at `.48` — as corrected by ANNEX-COROLLARY R1-d.

**RESOLUTION TRACE:** Base lines 307–314. Defect stated at 1992–2011; recursion replaced at 2013–2037 (ANNEX-DEF HE7-2′); (SLOT)/(LIFT) re-proved at 2101–2182 (R1-b, R1-c); transfer audited at 2184–2235 (R1.2 items 1–7); theorem re-proved at 2237–2253 (R1-d); the “SAME proofs” clause riddered at 2491 (M-B).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F1` — count **4**.

**TEETH:** `he7rannex_supp.py` — 79 members, σ == PARI 79/79, the **first machine σ at a fired level-3 node anywhere in the program**, running the CORRECTED HE7-2′ chain; tooth P3 flips 18/79 when the deep letter is dropped. Disclosure (ii) there: `g₂ = 1` throughout, so “the within-class deep twist ϑ_t (t ≥ 1) is structurally invisible at this family” — the leg covers the τ-cocycle substance of F1, **not every letter of R1-b**.

---

### EFF.HE7.18  [fence]

**CANONICAL STATEMENT:** verbatim, lines 362–371 — the §S3 non-circularity fence.

> “**Remark (what makes this work, and why it is not circular).** Two facts,
> and only two: gcd(u, ℓ) = 1 separates the ℓ classes (the level-2 analogue of
> "dv ≡ ih mod e₁ separates the e₁ classes"), and r irreducible of degree d_r
> makes the d_r within-class residues K-independent (the level-2 analogue of
> "{1, η, …, η^{f₁−1}} are F_Q-independent because deg ψ = f₁"). **Neither
> requires Ψ irreducible.** That is precisely why the level-2 machinery is
> available where HE3's stage-CS route was not: HE3 needed the *resolvent over
> a stage ring* (hence a DVR, hence irreducibility), whereas (SLOT₂) is a
> statement about the values and residues of polynomials in x evaluated at
> points of K̄₀.”

**CONDITIONALITY:** None. This is a NON-IMPORT fence (“Neither requires Ψ irreducible”) plus the note's own account of why HE3's route is not available — the fence that separates HE7's method from HE3's and licenses `.04`(c).

**DERIVATION:** The two facts are exactly Steps 2 and 3 of `.11`'s DERIVATION; the HE3 contrast is a declaration about HE3's method, not a claim about HE3's text.

**RESOLUTION TRACE:** Base lines 362–371; untouched. Re-asserted at §S8's “Relation to GENHN.C” (`.63`: “Ψ is not known irreducible”).

XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-BOX-6` — count **12** (HE3's own boxed defect; the “stage-CS route” is carried descriptively — see source defect 2 in §8).

**TEETH:** HE7-T-SLOT2TIE (the `gcd(u, ℓ) = 1` half of the two facts, machine-load-bearing).

---

### EFF.HE7.19  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — the frozen display (lines 379–388) verbatim, followed by the res(·)-corrected effective reading (lines 2583–2585) verbatim. The correction is a dated append; the frozen display is byte-untouched and is quoted first because it is what every in-note citation names.]

Frozen display:

> “**LEMMA HE7-L1 ((LIFT), corrected).** Fix k ∈ ℤ_{≥0} and let i₀ = i₀(k) be
> the unique 0 ≤ i₀ < e₁ with i₀h ≡ k (mod e₁). The set of residues realised
> as res(C(θ)/ϖ(θ)^{k}) by C ∈ O[x] with deg C < D′ and dv(C) = k is
>
>     { Σ_{t ∈ T(k)} c_t·η_θ^{t} : c_t ∈ F_Q, not all 0 },
>     T(k) := { t < f₁ : k ≥ (i₀ + e₁t)·h } ,
>
> and it is ALL of K^× iff T(k) = {0, …, f₁−1} iff
> **k ≥ (i₀(k) + e₁(f₁−1))·h**; a k-uniform sufficient condition is
> **k ≥ (D′−1)h**. If T(k) = ∅ the height k is not attained at all.”

**EFFECTIVE READING of the realized-set display** (dated correction, 2026-08-09, from HE6 PE2 F-1, in the res(·)-correct form of the HE6 PE3 obs-1 line):

> “    η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ)),
>     realized set = η_θ^{−q(k)} · { Σ_{t ∈ T(k)} c_t·η_θ^{t} :
>                                    c_t ∈ F_Q, not all 0 }”

**CONDITIONALITY:** **The sub-threshold exact-set clause is CORRECTED; the two boundary clauses are not.** The dated append's own words (lines 2510–2523): “The display omits the normalizer twist: read after division by ϖ^k (not by the canonical height-k attaining monomial n(k) = x^iπ^a), the realized set is the COSET … Both boundary clauses are twist-invariant: at full T(k) the coset is still ALL of K^× (η^{−q}·K^× = K^×), and T(k) = ∅ is untouched.” The correction is machine-witnessed at `(e₁, f₁, h) = (2, 2, 3)`, `O = ℤ₃`, `Φ′ = x⁴ + 729`, `k = 3`: “the realized ϖ-read set is {η, 2η} = η^{−1}·F₃^× — disjoint from the displayed {1, 2} = F₃^×”. **NON-PROPAGATION is enumerated site-by-site** at lines 2531–2551 (four sites, all consuming only full-T heights or twist-invariant clauses); it is carried at `.12`, `.22`, `.25` and at `.48`. HE7's own arc never adjudicated the sub-threshold clause: “HE7's arc verified the twist-invariant fullness/emptiness clauses of HE7-L1 only.”

**DERIVATION:** [ASSEMBLED — the proof at lines 404–411, verbatim]

> “*Proof.* dv(C) = min_i(e₁v(a_i) + ih) with i < D′ = e₁f₁. The slot i
> contributes at height k iff e₁v(a_i) = k − ih ≥ 0 with v(a_i) ∈ ℤ_{≥0}, which
> forces i ≡ i₀ (mod e₁) and k ≥ ih. The class-i₀ slots are i₀ + e₁t,
> t < f₁; the attainable ones are exactly T(k), and by GENHN-2 the residue at
> height k is Σ_{t}res(a_{i₀+e₁t})η_θ^{t} with res(a_{i₀+e₁t}) ranging freely
> over F_Q for t ∈ T(k) and forced to 0 otherwise. Surjectivity onto K needs all
> f₁ coefficients free, i.e. T(k) full, i.e. k ≥ (i₀ + e₁(f₁−1))h; and
> max_k (i₀(k) + e₁(f₁−1))h = (e₁−1+e₁f₁−e₁)h = (D′−1)h. ∎”

Justification tags: slot-contribution congruence `computation`; the free-residue clause `by XREF LEMMA GENHN-2`; the two thresholds `computation`. **The proof as displayed inherits the same coset defect** — it reads residues after dividing by ϖ^k, and the dated append's identity `C(θ)/ϖ(θ)^k = [C(θ)/n(k)(θ)]·[n(k)(θ)/ϖ(θ)^k] = γ·η_θ^{−q(k)}` is what supplies the missing factor.

**RESOLUTION TRACE:** Base lines 379–388 (statement) + 404–411 (proof). Corrected at 2501–2553 (dated correction from HE6 PE2 F-1: the coset form and the −q direction), then at 2571–2591 (dated line from HE6 PE3 obs-1: the res(·) form, and the factor placed OUTSIDE the braces as in HE6-1L [r2]). The dated correction records the display's byte-identity with HE6-1L: “the two display lines (the realized set and T(k)) are byte-identical between HE6-1L (HE6 §S1 L118–119) and HE7-L1 (this note L383–384) — diff re-run empty at this append”.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — count **2**.
XREF: `lean/notes/openmath/HE6_passPE2_report.md:F-1` — grep-verified count **6**.
XREF: `lean/notes/openmath/HE6_passPE3_report.md:obs-1` — grep-verified count **1**.

**TEETH:** Q3 / HE7-LIFT1 (P3) — the five level-1 frames' reachable-height tables, exhaustive. **Disclosed limitation** (line 2544–2546): “its frames sat at q(k) = 0 on each proper-T height tested ((2, 2, 1): q(0) = q(1) = 0; (3, 1, 2): T(1) = ∅), where the coset factor is 1” — i.e. the sealed tooth could not have seen the coset defect.

---

### EFF.HE7.20  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 390–402 — the `[r1]` fold box.

> “**[r1] FOLD: this statement is now HE6's own.** HE6's repair R3 struck
> §S1's (LIFT) and adopted LEMMA HE7-L1 **verbatim** as **LEMMA HE6-1L [r1]**
> (HE6_PROOF §S1), so at level 1 this note CITES rather than corrects: read
> "LEMMA HE7-L1" below as "LEMMA HE6-1L = LEMMA HE7-L1". Two riders travel
> with the fold. (a) HE6-1L's RIDER records that the residue is read after
> dividing by ϖ^k, not by the canonical normalizer n(k) = x^iπ^a, the two
> differing by the fixed element η_θ^{q} ∈ K^×; **this note uses ϖ-powers at
> level 1 throughout** (the level-2 normalizers are n₂(k) = ϖ^{m(k)}Φ′^{s(k)},
> whose level-1 part is a ϖ-power), so the twist of the rider never enters
> and the γ_t of (SLOT₂)(b) are exactly HE6-1L's residues. (b) Codex PE1
> finding 4 and FINDING HE7-F1 are ONE defect found twice; HE6-1L cites both
> finders and carries the sharper (per-height) threshold, which is the form
> used here.”

**CONDITIONALITY:** **The word “verbatim” is re-scoped by a dated line** (2555–2569), quoted:

> “The
> §S4.1 fold-box sentence "HE6's repair R3 struck §S1's (LIFT) and
> adopted LEMMA HE7-L1 **verbatim** as **LEMMA HE6-1L [r1]**" is to be
> read **as-of the r1 landing**: at that landing the two display lines
> (the realized set and T(k)) were byte-identical and the surrounding
> prose differed by the 5 cosmetic byte-diffs enumerated at
> HE6R1_RECON's R3 row (cec49ba: `^k` vs `^{k}`; "which is ALL" vs
> "and it is ALL"; `{0,…,f₁−1}` vs `{0, …, f₁−1}`; `))h` vs `))·h`;
> ";" vs "." before the T(k) = ∅ clause) — display-identical, not
> verbatim. Post-r2 the two texts diverge by exactly the η_θ^{−q(k)}
> coset correction, which BOTH notes now carry”.

**Rider (a) is the fold-box clause that the HE6 PE2 F-1 correction partially overturns.** The dated correction (line 2520–2521) upholds rider (a)'s *identity* — “the fold rider (a)'s "differing by η_θ^{q}" identity is correct as an identity” — but the rider's *conclusion* (“so the twist of the rider never enters”) is exactly the sentence the correction shows to be false at sub-threshold heights, and true at HE7's own use sites: item (i) of the non-propagation enumeration keeps rider (b)'s consequence, “the fold rider (b)'s "the γ_t of (SLOT₂)(b) are exactly HE6-1L's residues" survives”, because `.12` calls HE7-L1 only at full-T heights. **Boundary of validity: rider (a)'s never-enters conclusion holds at full-T heights only.**

**DERIVATION:** Provenance record, not a derivation.

**RESOLUTION TRACE:** Base lines 390–402; “verbatim” re-scoped at 2555–2569; rider (a)'s scope pinned at 2501–2553 (item (i) at 2534–2537).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.
XREF: `lean/notes/openmath/CODEX_HE6PE1_2026-08-08.md:finding 4` — grep-verified count **1** (line 268, the η-power normalization factor); the report's own queue designation `F4` has count **3**.

**TEETH:** NONE directly; the fold's consequence is exercised by Q3's level-1 frames (`.19`).

---

### EFF.HE7.21  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 413–430 — **FINDING HE7-F1**.

> “**FINDING HE7-F1 (on HE6 §S1's (LIFT), classification: statement
> over-reach, NON-PROPAGATING).** HE6 states (LIFT) as "for every c ∈ K^× and
> every k ∈ ℤ_{≥0} there is C ∈ O[x] with deg C < D′, dv(C) = k and
> res(C(θ)/ϖ(θ)^k) = c". As written this is **false**: at
> (e₁, f₁, h) = (3, 1, 2) the height k = 1 is attained by no C at all
> (attainable heights are {3a + 2i : a ≥ 0, i < 3} = {0,2,3,4,5,…}); at
> (e₁, f₁, h) = (2, 2, 1) the heights k = 0 and k = 1 realise only
> F_Q ⊊ K. **No HE6 theorem is affected:** every use of (LIFT) in HE6 is at
> k = (d−t)u with t < d and u = ℓκ > ℓD′h ≥ D′h > (D′−1)h (DEFINITION HE6-1
> requires κ > D′h), and the t = d coefficient is B_d := 1 (height 0, residue
> 1 ∈ F_Q, no lift needed). The corrected hypothesis **k ≥ (D′−1)h** should be
> appended to HE6 §S1's (LIFT); this note uses only the corrected form. The
> finding is machine-confirmed by tooth HE7-T-LIFT2SHARP, which computes the
> reachable sets by enumeration in five frames.
> **[r1] DISCHARGED at the source:** HE6's r1 round applied exactly this
> repair (R3) — (LIFT) struck, LEMMA HE6-1L [r1] installed in its place — so
> the finding is closed, not merely recorded, and HE6's own non-propagation
> check is the one displayed above.”

**CONDITIONALITY:** Closed, per its own `[r1]` clause. **This is the note's clearest instance of the append/consumption-protocol scope (header §B): the finding is discharged AT THE SOURCE by HE6's own repair round, not by an append landed on HE6 by HE7.** The claim “No HE6 theorem is affected” is a claim about HE6's uses, not about HE7's; HE7's own use sites are checked separately at `.24`/`.25`.

**DERIVATION:** [ASSEMBLED — the two counterexample computations are displayed inline] at `(3,1,2)`: attainable heights `{3a + 2i : a ≥ 0, i < 3} = {0,2,3,4,5,…}` so `k = 1` is unattained; at `(2,2,1)`: `T(0) = T(1) = {0}`, so only `F_Q ⊊ K` is realised — both `by EFF.HE7.19` (`T(k)` computed from LEMMA HE7-L1). Non-propagation: every HE6 use has `k = (d−t)u` with `u = ℓκ > ℓD′h ≥ D′h > (D′−1)h` `by XREF DEFINITION HE6-1` (`κ > D′h`) + `computation`, plus the `t = d` case at height 0.

**RESOLUTION TRACE:** Base lines 413–430 (r1 discharge already landed); untouched by later rounds.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:DEFINITION HE6-1` — count **7**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.

**TEETH:** HE7-T-LIFT2SHARP — “computes the reachable sets by enumeration in five frames”; Q3's level-1 table exhibits `(3,1,2)`: `k < thr` NOT surjective `{1}`, `k` not attained at all `{1}`.

---

### EFF.HE7.22  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 446–456 — the (LIFT₂) **sharpness** statement.

> “**Sharpness (the exact reachable set).** Running the same bookkeeping without
> (†₂): the level-2 heights at which ALL of K₂ is reachable are exactly
>
>     W₂ = { k : m(k) − t·u ∈ W₁ for every t < d_r },
>     W₁ = { k : k ≥ (i₀(k) + e₁(f₁−1))h }   (LEMMA HE7-L1),
>
> so (†₂)/(‡₂) are sufficient but not necessary, and below them the failure is
> genuine (a proper subgroup-coset of K₂ is reached, or the height is not
> attained at all). Tooth **HE7-T-LIFT2SHARP** computes W₁ and W₂ exhaustively
> in ten frames and checks both halves: every k above the closed-form threshold
> IS surjective, and some k below it is NOT.”

**CONDITIONALITY:** **The phrase “a proper subgroup-coset of K₂” is SUPERSEDED by ANNEX R R5 (shard 3).** Quoted verbatim from R5 (lines 2430–2439):

> “§S4.2's sharpness sentence "below them the failure is genuine (a
> proper subgroup-coset of K₂ is reached, or the height is not attained
> at all)" mislabels the reachable set. **Rider: read "a proper
> subgroup-coset of K₂" as "the nonzero elements of a proper F_Q-linear
> subspace (a punctured proper subspace)"** — LEMMA HE7-L1's own display
> already gives the correct object ({Σ_{t∈T(k)} c_t·η_θ^t : c_t ∈ F_Q,
> not all 0}). Codex's witness checks: in K₂ = F₈ with reachable slots
> {1, β}, the set {1, β, 1+β} has size 3 — no additive subgroup/coset
> (sizes are powers of 2) and no multiplicative one (F₈^× has order 7).
> Nothing consumes the group structure; tooth HE7-T-LIFT2SHARP verifies
> the exact sets by enumeration.”

Note the interaction with `.19`: the corrected LEMMA HE7-L1 display makes the level-1 object a **coset** `η_θ^{−q(k)}·(punctured subspace)`; the HE6 PE2 F-1 append's own item (ii) (line 2538–2541) says of this very display that “its sub-threshold sentence already reads "a proper subgroup-coset of K₂ is reached" — coset-correct as written”. **The two riders point in opposite directions on the same phrase** (R5: “subgroup-coset” is wrong, it is a punctured subspace; the HE6-side append: “coset” is right, because of the ϖ-twist). Both are true of different objects — R5 speaks of the shape *inside* the braces, the HE6-side append of the *external* `η_θ^{−q}` factor. **Recorded as OPEN-CALL 2** (which wording the merged spec should carry).

**DERIVATION:** [ASSEMBLED] The `W₂` characterisation is “the same bookkeeping without (†₂)” — i.e. `.12`'s DERIVATION with the per-`t` full-residue requirement `m_t = m(k) − tu ∈ W₁` kept as a condition rather than implied, `by EFF.HE7.12` + `by EFF.HE7.19` (`W₁` is LEMMA HE7-L1's full-`T(k)` set). The “sufficient but not necessary” claim is `by` the tooth's exhaustive enumeration (Q3's level-2 table: e.g. `(2,1,1,2,2,5)` has `thr₂ = 17` with 12 non-surjective `k < thr₂`).

**RESOLUTION TRACE:** Base lines 446–456; “subgroup-coset” riddered at 2428–2440 (ANNEX R R5); cross-read against 2538–2541 (HE6 PE2 F-1 item (ii)).

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F5` — grep-verified count **3**.

**TEETH:** HE7-T-LIFT2SHARP · Q3's two tables (five level-1 frames, five level-2 frames), **0 violations, ten frames verified exhaustively**.

---

### EFF.HE7.23  [definition]

**CANONICAL STATEMENT:** verbatim, lines 458–464 — the ladder-wide threshold recursion.

> “**The recursion behind the threshold.** Writing bound_i for the level-i
> uniform threshold, the proof gives
>
>     bound_{i+1} = (ℓ_i g_i − 1)·u_i + ℓ_i·bound_i ,    bound_0 = 0,
>
> i.e. bound₁ = (D′−1)h and bound₂ = (ℓd_r−1)u + ℓ(D′−1)h — one formula for the
> whole ladder (§S6).”

**CONDITIONALITY:** Unconditional. **Explicitly preserved by ANNEX R**: ANNEX-THEOREM R1-c's proof (line 2179–2182) states “The bound recursion is unchanged — values never see the twist”, and R1.2 item 1 puts “bounds” in the twist-free class. So the ANNEX R repair does not move this display.

**DERIVATION:** Read off `.12`'s proof: the `g_i` within-class heights are `m₀ − t·u_i` (`t < g_i`), each needing a level-`i` full-residue height `≥ bound_i`, and `m₀ ≥ (k − (ℓ_i−1)u_i)/ℓ_i`; solving for `k` gives `bound_{i+1} = (ℓ_ig_i − 1)u_i + ℓ_i·bound_i`. `by EFF.HE7.12` + `computation`. The two instances are `bound₁ = (D′−1)h` (`.19`) and `bound₂ = (‡₂)` (`.12`).

**RESOLUTION TRACE:** Base lines 458–464; consumed at 997 (THEOREM HE7.D's `(LIFT_i)` clause, `.48`) and 1012–1014 (§S6's (LIFT) step); re-stated unchanged at 2166–2168 and 2179–2182 (ANNEX-THEOREM R1-c).

**TEETH:** Q3's level-2 table verifies `thr₂` in five frames against exhaustive enumeration (`(2,1,1,2,1,5)`→7, `(2,1,1,2,2,5)`→17, `(2,2,1,2,2,7)`→27, `(3,1,2,2,3,13)`→73, `(1,2,1,3,2,11)`→58).

---

### EFF.HE7.24  [fence]

**CANONICAL STATEMENT:** verbatim, lines 468–480 — §S4.3's (‡₂) use-site check.

> “The level-2 test family (DEFINITION HE7-3 below) needs level-2 residues at
> heights (d₂−t)u₂ with t < d₂ and κ₂ = u₂/ℓ₂ > T₂, so
> u₂ = ℓ₂κ₂ > ℓ₂T₂ ≥ T₂ = ℓd_r·u. Then
>
>     (ℓd_r − 1)u + ℓ(D′−1)h < (ℓd_r − 1)u + u = ℓd_r·u ≤ u₂ ≤ (d₂−t)u₂ ,
>
> using ℓ(D′−1)h < ℓD′h < ℓλ = u (the DEFINITION HE6-1 hypothesis λ > D′h).
> The level-2 α-refine of THEOREM HE7.A(3) needs a lift at height λ₂ > T₂, and
> the same chain applies. So **(‡₂) never binds where it is used** — the
> threshold is a statement-hygiene item, not an obstruction. (At the machine's
> frame D′ = 2, f₁ = d_r = 1 it is vacuous, which is why HE6's battery could
> not see FINDING HE7-F1: tooth HE7-T-LIFT2SHARP runs in frames with f₁ ≥ 2 and
> d_r ≥ 2 on purpose.)”

**CONDITIONALITY:** Unconditional. This is a **scope fence on (LIFT₂)'s hypothesis**: it certifies that `.12`'s `(‡₂)` is never binding at any of HE7's own two use classes (the test family `.27`, and HE7.A(3)'s α-refine `.14`).

**DERIVATION:** The chain is displayed inline: `u₂ = ℓ₂κ₂ > ℓ₂T₂ ≥ T₂ = ℓd_r·u`, then `(ℓd_r − 1)u + ℓ(D′−1)h < ℓd_r·u ≤ u₂ ≤ (d₂−t)u₂`, using `ℓ(D′−1)h < ℓD′h < ℓλ = u` — `by EFF.HE7.06` (`T₂ := ℓd_r·u`, `u = ℓλ`) + `by XREF DEFINITION HE6-1` (`λ > D′h`) + `computation`.

**RESOLUTION TRACE:** Base lines 468–480; untouched. Consumed at `.12`, `.27`, `.14`, `.45`, and at ANNEX-LEMMA HE7-13′ (shard 2, line 1701: “it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3”).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:DEFINITION HE6-1` — count **7**.

**TEETH:** HE7-T-LIFT2SHARP, run at `f₁ ≥ 2` and `d_r ≥ 2` **on purpose** because the σ frame `D′ = 2, f₁ = d_r = 1` makes the threshold vacuous.

---

### EFF.HE7.25  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 482–509 — the `[r1]` level-1 use-site check.

> “**[r1] THE USE-SITE CHECK AGAINST THE CORRECTED LEVEL-1 THRESHOLD (displayed).**
> (‡₂) is the level-2 statement; what the fold of LEMMA HE6-1L makes newly
> checkable is the LEVEL-1 lift calls hidden inside the proof of (LIFT₂), which
> invoke HE6-1L at the d_r within-class heights m_t := m₀ − t·u (t < d_r) and
> therefore need **m_t ≥ (D′−1)h** — HE6-1L's uniform threshold — at every use
> site, not merely (‡₂). Every use site of this note has k > T₂ = ℓd_r·u
> (§S4.3's chain: k = (d₂−t)u₂ ≥ u₂ > ℓ₂T₂ ≥ T₂ for the test family, and
> k = λ₂ > T₂ for the α-refine of THEOREM HE7.A(3)). Since 0 ≤ s₀ = s(k) ≤ ℓ−1
> and ℓm₀ + s₀u = k,
>
>     m₀ = (k − s₀u)/ℓ ≥ (k − (ℓ−1)u)/ℓ > (ℓd_r·u − (ℓ−1)u)/ℓ
>        = (d_r − 1)u + u/ℓ = (d_r − 1)u + λ ,
>
> and hence for every t < d_r
>
>     m_t = m₀ − t·u ≥ m₀ − (d_r−1)u > λ > D′h > (D′−1)h ,
>     margin  m_t − (D′−1)h > λ − (D′−1)h > D′h − (D′−1)h = h ≥ 1 .
>
> So every level-1 call sits **strictly more than h above** HE6-1L's uniform
> threshold, a fortiori above its sharp per-height threshold
> (i₀(m_t) + e₁(f₁−1))h ≤ (D′−1)h; in particular T(m_t) is full, so the height
> is attained AND the residue map onto K is surjective — neither of HE6-1L's two
> failure modes (proper subgroup-coset, unattained height) can occur at a use
> site. At **ℓ = 1** the same check reads (‡₂) ≡ (†₂): m₀ = k > T₂ = d_r·λ, so
> m_t > d_rλ − (d_r−1)λ = λ > (D′−1)h with the identical margin — which is the
> HE6R1 reconciliation's §S3.2 item-2 verification, re-derived here rather than
> transcribed. **Verdict: the r1-corrected level-1 threshold is satisfied with
> margin > h at every §S4.3 use site, so no statement of this note moves.**”

**CONDITIONALITY:** Unconditional. **This unit is what makes the shard-3 coset correction non-propagating**: it proves `T(m_t)` is FULL at every use site, and the dated append's item (i) cites exactly this (“calls HE7-L1 only at m_t ≥ (D′−1)h — full-T heights, the surjectivity clause”). Its phrase “proper subgroup-coset” inherits ANNEX R R5's rider (`.22`), harmlessly — the clause asserts the failure mode does NOT occur.

**DERIVATION:** The two displays are the derivation, both `computation` from `.06` (`ℓm₀ + s₀u = k`, `0 ≤ s₀ ≤ ℓ−1`, `T₂ = ℓd_r·u`, `u = ℓλ`) + `by EFF.HE7.24` (`k > T₂` at every use site) + `by XREF DEFINITION HE6-1` (`λ > D′h`) + `by EFF.HE7.19` (the sharp per-height threshold `(i₀(m_t) + e₁(f₁−1))h ≤ (D′−1)h`). The `ℓ = 1` specialisation is displayed separately and is `computation`.

**RESOLUTION TRACE:** Base lines 482–509 (r1 landed); untouched. Consumed as the non-propagation ground at 2534–2537.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:S3.2` — count **6**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — count **4**.

**TEETH:** No direct tooth (it is a hypothesis-margin check). Its consequence is exercised wherever `.12` is: Q3's level-2 frames.

---

### EFF.HE7.26  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 515–517 — §S5's self-scope.

> “Each item states what is needed at level 2, and whether it transfers
> verbatim, needs a short new argument, or needs a genuinely new estimate.
> **Exactly one item is in the third class (§S5.3).**”

**CONDITIONALITY:** **The count is qualified by the note itself.** §S9 (shard 2, lines 1257–1273) records that §S5 was under-counted twice: “(a) the ξ-side Step-1 inequality needs a genuinely new two-offset estimate (§S5.3); (b) the general case needs the block-factor reduction (§S5.5) … (c) the recursion needs the α-refine termination (§S7)”, and then `[r1]` adds “(d) the block-factor reduction (§S5.5) does not by itself pin μ₂ when the block is PROPER … (e) the reduction to f_S needs **Ψ ∤ f_S**”. Further, `[r2]` added §S5.8 (LEMMAS HE7-12/HE7-13), a sixth item that is neither a verbatim transfer nor a short new argument. **So the “exactly one” claim is true of the §S5.1–S5.7 transfer audit as originally scoped, and false of the shard's final content.** Recorded as source defect 3 in §8.

**DERIVATION:** Scope declaration; discharged item-by-item at `.28`–`.42`.

**RESOLUTION TRACE:** Base lines 515–517; qualified at 1257–1273 (§S9) and superseded in scope by §S5.8's addition at 798–971 (`[r2]`).

**TEETH:** NONE (scope declaration).

---

### EFF.HE7.27  [definition]

**CANONICAL STATEMENT:** verbatim, lines 519–535 — **DEFINITION HE7-3**.

> “**DEFINITION HE7-3 (the level-2 test family; the residues carry the
> INVERSE TWIST).** For κ₂ = u₂/ℓ₂ ∈ ℚ in lowest terms with κ₂ > T₂, and
> r₂ = Z^{d₂} + Σ_{t<d₂}c_{2,t}Z^{t} ∈ K₂[Z] monic irreducible with
> r₂(0) ≠ 0, let c_t := (s(d₂u₂ − tu₂) + t·s(u₂) − s(d₂u₂))/ℓ be the twist
> exponents of §S1 at m₁ := d₂u₂, and choose by (LIFT₂) polynomials
> C_t ∈ O[x] with deg C_t < D″, level-2 slot value (d₂−t)u₂ and level-2
> residue
>
>     res( C_t(ξ)/n₂((d₂−t)u₂)(ξ) ) = ι_ξ^{(2)}( c_{2,t}·β^{c_{d₂} − c_t} )
>
> (C_t := 0 if c_{2,t} = 0) — legitimate because β^{c_{d₂}−c_t} ∈ K₂^× and
> (LIFT₂) realises every element of K₂ — and set
>
>     Ψ₂ := Ψ^{ℓ₂d₂} + Σ_{t<d₂} C_t·Ψ^{ℓ₂ t}  ∈ O[x],
>
> monic of degree D″ℓ₂d₂ (each C_tΨ^{ℓ₂t} has degree ≤ (D″−1) + D″ℓ₂t <
> D″ℓ₂d₂). Never assumed irreducible.”

**CONDITIONALITY:** Well-posed by `.12` ((LIFT₂) realises every element of K₂) at heights certified non-binding by `.24`. **The inverse twist is load-bearing, not cosmetic** (`.32`). At level i ≥ 3 the prescription is read through ANNEX R R1.2 item 2 (shard 3): “its prescription is ALREADY inverse-twisted; under HE7-2′ "inverse-twisted" means by the composite unit (available by R1-c, which absorbs any fixed K_{i+1}^×-unit into the lift). Same construction, same degrees.” Under LEMMA HE7-12(c) item (2) the family is built at the refined key `Ψ^{(w)}` verbatim.

**DERIVATION:** Definition. The two derived clauses are displayed inline: legitimacy (`β^{c_{d₂}−c_t} ∈ K₂^×` and (LIFT₂) surjective, `by EFF.HE7.12`) and the degree count (`deg(C_tΨ^{ℓ₂t}) ≤ (D″−1) + D″ℓ₂t < D″ℓ₂d₂`, `computation`). The twist exponents `c_t` are `.08`'s cocycle exponents evaluated at `m₁ := d₂u₂`.

**RESOLUTION TRACE:** Base lines 519–535; untouched. Carried to the refined key at 885–887 (HE7-12(c) item (2)); generalised at 2199–2202 (R1.2 item 2).

**TEETH:** Q4 / HE7-GEN2 (P4): 4,259 level-2 flat identities `ℓe₁·v(Res(f, Ψ₂)) = D″ℓ₂d₂·h_{F₂}(κ₂)` at rational level-2 heights, `ℓ₂ ∈ {1,2,3}` · **HE7-T-BADTWIST** — the tooth that found the inverse twist (`.32`).

---

### EFF.HE7.28  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 539–542 — **LEMMA HE7-4 (the level-2 disk criterion)**.

> “**LEMMA HE7-4.** For every ξ ∈ K̄₀,
> dv₂(Ψ(ξ)) = ℓ²d_r·min(dv(Φ′(ξ)), λ) + ℓ·ε(ξ) with ε(ξ) > 0 iff
> dv(Φ′(ξ)) = λ and ι_ξ(r)(β_ξ) = 0. Hence **dv₂(Ψ(ξ)) > T₂ iff ξ is a
> level-2 point**, and dv₂(Ψ(ξ)) ≤ T₂ otherwise.”

**CONDITIONALITY:** Unconditional; **entirely inherited** (§S5.1's own heading: “ALREADY PROVED IN HE6”). At the refined key it is replaced by LEMMA HE7-12(a)+(b), which HE7-12(c) item (3) certifies are “the only two facts §S5 ever consumes from HE7-4”.

**DERIVATION:** [ASSEMBLED — lines 544–548, verbatim]

> “*Proof.* For ξ satisfying (T1)/(T2) this is LEMMA HE6-2 multiplied by ℓ. For
> ξ failing (T1) or (T2), LEMMA HE6-0 gives δ := dv(Φ′(ξ)) = D′min(dv ξ, h) ≤
> D′h < λ and LEMMA HE6-1 Step 1 gives dv(Ψ(ξ)) = ℓd_r·δ, i.e. the same
> formula with min(δ,λ) = δ and ε = 0. ∎ *(No new work: the level-2 disk
> criterion is HE6's own §S3.3 Step 1 plus §S4, read in dv₂.)*”

Justification tags: on-disk `by XREF LEMMA HE6-2` (× ℓ); off-disk `by XREF LEMMA HE6-0` + `by XREF LEMMA HE6-1` Step 1.

**RESOLUTION TRACE:** Base lines 539–548; untouched. Superseded-in-role at the refined key by 819–832 (HE7-12(a)(b)).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-2` — count **10**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0` — count **17**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1` — count **15**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S3.3` — count **2**.

**TEETH:** `he7r2_supp.py` B2 — the off-disk value formula checked in resultant-sum form on five off-disk strata per member, **210/210** (with the `[r3]` vacuity disclosure at `.46`).

---

### EFF.HE7.29  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 552–554 — **LEMMA HE7-5 (the level-2 local forcing)**.

> “**LEMMA HE7-5.** If ρ is a root of f whose level-2 label is (λ₂, r₂) with
> λ₂ = u₂/ℓ₂ in lowest terms, then e₁ℓℓ₂ | e(L_ρ) and f₁d_rd_{r₂} | f(L_ρ);
> hence [L_ρ : K₀] ≥ D″ℓ₂d_{r₂}.”

**CONDITIONALITY:** Unconditional on the level-1 local forcing (LEMMA HE6-0′). Key-free: HE7-12(c) item (4) records that its proof “uses only v(Ψ(ρ)) ∈ (1/e(L_ρ))ℤ and the unit residue of Ψ(ρ)^{ℓ₂}/n₂(u₂)(ρ) — no property of the key's form”. Re-used without separability at ANNEX-LEMMA HE7-13′(a) (shard 2: “whose proof consumes only the value group and the unit residue at ρ — no separability”).

**DERIVATION:** [ASSEMBLED — lines 556–563, verbatim]

> “*Proof.* e₁ℓ | e(L_ρ) and f₁d_r | f(L_ρ) by LEMMA HE6-0′ at the level-1
> label. Write e(L_ρ) = e₁ℓe″. Since v(Ψ(ρ)) = λ₂/(e₁ℓ) = u₂/(e₁ℓℓ₂) must lie
> in (1/e(L_ρ))ℤ, we get u₂e″/ℓ₂ ∈ ℤ, and gcd(u₂, ℓ₂) = 1 forces ℓ₂ | e″. For
> the residue degree: ϖ(ρ), Φ′(ρ) ∈ L_ρ^×, so n₂(k)(ρ) ∈ L_ρ^× for every k;
> hence Ψ(ρ)^{ℓ₂}/n₂(u₂)(ρ) is a unit of O_{L_ρ} and its residue β₂ lies in
> k_{L_ρ}. Also ι_ρ^{(2)}(K₂) ⊆ k_{L_ρ} (η_ρ, β_ρ ∈ k_{L_ρ} by HE6-0′'s
> proof). β₂ is a root of the irreducible ι_ρ^{(2)}(r₂) ∈ ι_ρ^{(2)}(K₂)[Z], so
> [ι_ρ^{(2)}(K₂)(β₂) : F_Q] = f₁d_rd_{r₂} divides f(L_ρ). ∎”

Justification tags: the level-1 half `by XREF LEMMA HE6-0′`; the `ℓ₂ | e″` step `computation` (value group + `gcd(u₂, ℓ₂) = 1`); the residue-degree half `by XREF LEMMA HE6-0′`'s proof + `by EFF.HE7.06` (the transport `ι^{(2)}`) + `definitional` (minimal polynomial degree).

**RESOLUTION TRACE:** Base lines 552–563; untouched. Consumed at `.13` (the class-size sandwich), `.41`, and at HE7-13′(a).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0′` — count **5**.

**TEETH:** Indirect — Q1's `Σef = deg f` agreement member by member is the class-size sandwich's machine form, and this lemma is its lower bound.

---

### EFF.HE7.30  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 567–569 — **LEMMA HE7-7 (the level-2 ξ-side), the note's ONE genuinely new estimate.**

> “**LEMMA HE7-7 (the level-2 ξ-side).** Every root ξ of Ψ₂ is a level-2 point
> with dv₂(Ψ(ξ)) = κ₂ and ι_ξ^{(2)}(r₂)(β₂,ξ) = 0, where
> β₂,ξ := res(Ψ(ξ)^{ℓ₂}/n₂(u₂)(ξ)). No irreducibility of Ψ or Ψ₂ is used.”

**CONDITIONALITY:** Unconditional. §S5.3's heading marks it “THE ONE GENUINELY NEW ESTIMATE”. Its Step-1 estimate is the single place a new inequality was needed (`.33`). At the refined key it holds verbatim by HE7-12(c) item (5); at level i ≥ 3 by R1.2 item 3, whose only change is that “res(τ_t) enlarges from β^{c_t} to the composite unit — still fixed, still nonzero”.

**DERIVATION:** [ASSEMBLED — lines 571–638, Steps 1 and 2 verbatim, with the offsets display and its `[r2]` correction carried at `.31`]

> “*Proof.* Write Ψ₂ = Σ_{t≤d₂}C_tΨ^{ℓ₂t} with C_{d₂} := 1, and set
> δ := dv(Φ′(ξ)), δ₂ := dv₂(Ψ(ξ)).
>
> **Step 1 (ξ lies in the Ψ-disk).** Suppose not; by LEMMA HE7-4, δ₂ ≤ T₂ < κ₂.
> We show the t = d₂ term is the unique strict minimum, so Ψ₂(ξ) ≠ 0. The
> t = d₂ term has dv₂ = ℓ₂d₂δ₂, so it suffices that for every t < d₂
>
>     dv₂(C_t(ξ)) > ℓ₂(d₂ − t)·δ₂ .                                     (S5.1)”

[offsets ε₀, ε₁ and (S5.2): see `.31`]

> “By the ultrametric inequality applied inside each level-1 coefficient
> (HE6-1 Step 1's estimate) and then to the Φ′-development ((SLOT₂)(c)),
> writing C_t = Σ_s c_{t,s}Φ′^{s},
>
>     dv₂(C_t(ξ)) ≥ min_s ( ℓ·dv_ξ(c_{t,s}) + s·ℓδ )
>                ≥ min_s ( ℓ·dv(c_{t,s}) + s·u ) − (ℓd_r − 1)·ε₁ − ℓ(D′−1)·ε₀
>                = ℓ₂(d₂ − t)·κ₂ − (ℓd_r − 1)ε₁ − ℓ(D′−1)ε₀ ,            (S5.3)
>
> using s ≤ ℓd_r − 1 for the ε₁-loss and i ≤ D′−1 for the ε₀-loss, and
> (LIFT₂)'s prescription dv₂(C_t) = (d₂−t)u₂ = ℓ₂(d₂−t)κ₂ for the last step.
> Also, by LEMMA HE7-4, δ₂ = ℓd_r(ℓδ) = ℓd_r(u − ε₁) = T₂ − ℓd_r·ε₁ when
> ε₁ > 0, and δ₂ = T₂ when ε₁ = 0 (δ ≥ λ, no excess since ξ is not a level-2
> point). Substituting into (S5.1) and using ℓ₂(d₂−t) ≥ 1:
>
>     dv₂(C_t(ξ)) − ℓ₂(d₂−t)δ₂
>       ≥ ℓ₂(d₂−t)(κ₂ − T₂) + ℓ₂(d₂−t)·ℓd_r·ε₁ − (ℓd_r − 1)ε₁ − ℓ(D′−1)ε₀
>       ≥ (κ₂ − T₂) + [ℓd_r − (ℓd_r − 1)]·ε₁ − ℓ(D′−1)ε₀
>       = (κ₂ − T₂) + ε₁ − ℓ(D′−1)ε₀
>       = (κ₂ − T₂) + ℓ(λ − D′h) + ℓD′ε₀ − ℓ(D′−1)ε₀     [by (S5.2), ε₀ > 0]
>       = (κ₂ − T₂) + ℓ(λ − D′h) + ℓ·ε₀   > 0 ,
>
> and in the two remaining cases: ε₀ = 0 < ε₁ gives (κ₂−T₂) + ε₁ > 0; and
> ε₀ = ε₁ = 0 (i.e. δ ≥ λ with ξ not a level-2 point) gives (κ₂−T₂) > 0. In
> every case (S5.1) is STRICT. Hence every root of Ψ₂ is a level-2 point.
>
> **Step 2 (the height and the residue).** Now (SLOT₂) applies at ξ:
> dv₂(C_t(ξ)) = (d₂−t)u₂ exactly, and the term t of Ψ₂(ξ) has
> dv₂ = (d₂−t)u₂ + ℓ₂tδ₂ = ℓ₂[(d₂−t)κ₂ + tδ₂]. If δ₂ > κ₂ the minimum is
> attained only at t = 0, if δ₂ < κ₂ only at t = d₂; either way
> dv₂(Ψ₂(ξ)) < ∞, contradicting Ψ₂(ξ) = 0. So δ₂ = κ₂. Then every term has
> dv₂ = ℓ₂d₂κ₂; dividing by n₂(d₂u₂)(ξ) and collecting, term t becomes
> [C_t(ξ)/n₂((d₂−t)u₂)(ξ)]·[Ψ(ξ)^{ℓ₂}/n₂(u₂)(ξ)]^{t}·τ_t with
> res(τ_t) = β_ξ^{c_t} the explicit twist of §S1, so
>
>     0 = res( Ψ₂(ξ)/n₂(d₂u₂)(ξ) )
>       = Σ_t ι_ξ^{(2)}( c_{2,t}·β^{c_{d₂}−c_t}·β^{c_t} )·β₂,ξ^{t}
>       = ι_ξ^{(2)}( β^{c_{d₂}} )·ι_ξ^{(2)}(r₂)(β₂,ξ) ,
>
> the middle step by DEFINITION HE7-3's **inverse-twisted** prescription; since
> β^{c_{d₂}} ≠ 0, ι_ξ^{(2)}(r₂)(β₂,ξ) = 0. ∎”

Justification tags: (S5.1) reduction `by EFF.HE7.28` (LEMMA HE7-4); (S5.3) `by XREF LEMMA HE6-1` Step 1 + `by EFF.HE7.11`(c) + `by EFF.HE7.27`; the two-offset case split `by EFF.HE7.31` ((S5.2) as corrected at r2); Step 2 `by EFF.HE7.11` + `by EFF.HE7.08` (the twist) + `by EFF.HE7.27` (the inverse prescription).

**RESOLUTION TRACE:** Base lines 567–638; the offsets display corrected at 590–597 (`[r2, HE7-PE1 F-2]`, already landed — see `.31`). Carried to the refined key at 892–895 (HE7-12(c) item (5)); generalised at 2203–2213 (R1.2 item 3).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1` — count **15**.

**TEETH:** Q4/Q5 (HE7-GEN2 / HE7-SEP2): 4,259 flat identities + 191 strict (plus 5 infinite) excess certificates exactly at the level-2 labels · `he7r2_supp.py` B2's five off-disk strata “covering all three offset cases”.

---

### EFF.HE7.31  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 580–597 — the two offsets, the display **(S5.2)**, and its `[r2, HE7-PE1 F-2]` correction.

> “Introduce the two **offsets**
>
>     ε₀ := ( h − dv(ξ) )^{+} ,        ε₁ := ( u − ℓδ )^{+} = ℓ(λ − δ)^{+},
>
> and note (LEMMA HE6-0) that δ = D′·min(dv ξ, h), so
>
>     if ε₀ > 0 :  δ = D′(h − ε₀) and ε₁ = ℓ(λ − D′h) + ℓD′ε₀ > 0 ;
>     if ε₀ = 0 :  ε₁ = ℓ(λ − δ)⁺ — either ε₁ > 0 (δ < λ) or
>                  ε₁ = 0 (δ ≥ λ).                                     (S5.2)
>
> **[r2, HE7-PE1 F-2]** The pre-r2 display claimed at ε₀ = 0 the dichotomy
> "ε₁ ≥ ℓ(λ − D′h) > 0 unless δ ≥ λ, in which case ε₁ = 0" — false in the
> middle band D′h < δ < λ (e.g. (e₁,f₁,h) = (2,1,1), λ = 5/2, δ = 9/4:
> ε₁ = 1/2 < 1 = ℓ(λ − D′h)). The split actually consumed below (and by
> (S5.8.1)'s case analysis) is only **ε₁ > 0 vs ε₁ = 0**, which the
> corrected display supplies; the ε₀ > 0 branch below uses the first
> (unchanged) clause. No other step of this note consumed the false half
> (§S6's cascade uses δ_j < λ_j ⟹ ε_j > 0, also the corrected form).”

**CONDITIONALITY:** The corrected form is the effective one (the `[r2]` bracket is already landed). **The blast-radius sentence is the note's own non-propagation claim** and is itself load-bearing: it certifies that only two consumers exist ((S5.3)'s case analysis at `.30`, and (S5.8.1)'s at `.44`) and that §S6's cascade (`.48`) uses the corrected form. `(S5.2)` is cited by designation from `.44`'s proof and from the machine leg (“the (S5.2) [r2] middle band δ ∈ (D′h, λ) with ε₁ = 1/2”).

**DERIVATION:** The `ε₀ > 0` clause is `by XREF LEMMA HE6-0` (`δ = D′·min(dv ξ, h)`, so `δ = D′(h − ε₀)`) + `computation` (`ε₁ = ℓ(λ − δ) = ℓ(λ − D′h) + ℓD′ε₀ > 0` since `λ > D′h`). The `ε₀ = 0` clause is definitional (`ε₁ = ℓ(λ − δ)⁺` is positive iff `δ < λ`). The refutation of the pre-r2 half is the displayed counterexample `(e₁,f₁,h) = (2,1,1), λ = 5/2, δ = 9/4` giving `ε₁ = 1/2 < 1 = ℓ(λ − D′h)` — `computation`.

**RESOLUTION TRACE:** Base lines 580–597 with `[r2]` landed; untouched thereafter.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0` — count **17**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-2` — grep-verified count **2**.

**TEETH:** `he7r2_supp.py` B2 stratum 3 — “the (S5.2) [r2] middle band δ ∈ (D′h, λ) with ε₁ = 1/2” is one of the five off-disk strata, i.e. the corrected band is machine-exercised.

---

### EFF.HE7.32  [fence]

**CANONICAL STATEMENT:** verbatim, lines 640–649.

> “**Remark (the inverse twist is load-bearing, and the machine found it).** An
> earlier draft of DEFINITION HE7-3 prescribed res(C_t) = c_{2,t} outright. That
> builds the test polynomial of the TWISTED residual Σ_tc_{2,t}β^{c_t}Z^t
> instead of r₂ — and the twisted polynomial need not be irreducible, so its
> roots can carry the node's own label and the flat identity of LEMMA HE7-9
> acquires a spurious excess. The battery's HE7-GEN2 leg registered exactly
> that (excess 4 at ℤ_5, s = 2, κ₂ = 21/2 with r₂ of degree 2: measured 340 vs
> flat 336) and vanished on the corrected definition. At s = 1 — HE6's own
> configuration, where β = s = 1 — the twist is invisible, which is why no
> earlier unit of this program could have seen it.”

**CONDITIONALITY:** None; a record of a defect found and closed pre-seal. It is the load-bearing justification for `.27`'s inverse prescription and for `.08`'s “this is not a bookkeeping remark”.

**DERIVATION:** The failure mechanism is argued inline (`by EFF.HE7.27` + `by EFF.HE7.41` — the flat identity of LEMMA HE7-9); the numeric witness is `by` the battery's HE7-GEN2 leg.

**RESOLUTION TRACE:** Base lines 640–649; untouched. One level up at 2176 (R1-c's “the INVERSE twist, exactly DEFINITION HE7-3's inverse-twisted mechanism … applied one step deeper”).

**TEETH:** HE7-GEN2 (P4) — the pre-correction excess 4 at `ℤ_5, s = 2, κ₂ = 21/2`, measured 340 vs flat 336, vanishing on the corrected definition · HE7-T-BADTWIST.

---

### EFF.HE7.33  [fence]

**CANONICAL STATEMENT:** verbatim, lines 651–655.

> “**Remark (this is the only place where a NEW inequality was needed).** HE6's
> Step 1 had one offset (ε = h − dv(ξ)); at level 2 there are two (ε₀ and ε₁),
> and the estimate closes because the GAIN's coefficient on each offset exceeds
> the DEFICIT's: ℓd_r vs ℓd_r − 1 on ε₁, and ℓD′ vs ℓ(D′−1) on ε₀. That
> pattern is exactly what makes the general induction of §S6 go through.”

**CONDITIONALITY:** None as a description of the mechanism. Its “only place” quantifier is scoped by `.26`'s conditionality (§S9's under-count list). **The gain-exceeds-deficit pattern is the load-bearing architectural claim §S6's induction generalises**: it becomes (S6.1)–(S6.3)'s `ρ_j ≥ 0` cascade at `.48`.

**DERIVATION:** Read off `.30`'s (S5.3) chain: the coefficient comparison `ℓd_r` vs `ℓd_r − 1` and `ℓD′` vs `ℓ(D′−1)` is the arithmetic of the substituted display.

**RESOLUTION TRACE:** Base lines 651–655; generalised at 1023–1048 (§S6's ξ-side step) with the same pattern in recursion form.

**TEETH:** `he7r2_supp.py` B2 (the three offset cases exercised).

---

### EFF.HE7.34  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 659–664 — **LEMMA HE7-7′ (the two evaluation displays)**.

> “**LEMMA HE7-7′.** (a) For any level-2 point ξ with δ₂ := dv₂(Ψ(ξ)) and
> β₂ := res(Ψ(ξ)^{ℓ₂}/n₂(u₂)(ξ)) when defined,
> dv₂(Ψ₂(ξ)) = ℓ₂d₂·min(δ₂, κ₂) + ε₂(ξ) with ε₂(ξ) > 0 ⟺ δ₂ = κ₂ and
> ι_ξ^{(2)}(r₂)(β₂) = 0. (b) For any level-2 point ξ with dv₂(Ψ(ξ)) = κ₂,
> dv₂(f_S(ξ)) = h_{F₂}(κ₂) + δ(ξ) where h_{F₂}(κ₂) := min_j(dv₂(A_j^{(2)}) +
> jκ₂) and δ(ξ) > 0 ⟺ κ₂ is a slope λ₂ of P₂ and ι_ξ^{(2)}(R_{λ₂})(β₂) = 0.”

**CONDITIONALITY:** Unconditional; a verbatim transfer. Clause (b) presupposes the Ψ-development of `f_S`, hence the standing convention Ψ ∤ f_S (`.09`). At the refined key it holds by HE7-12(c) item (6); at level i ≥ 3 by R1.2 item 4.

**DERIVATION:** [ASSEMBLED — lines 666–671, verbatim]

> “*Proof.* Verbatim HE6 §S4 with (SLOT₂) in place of the SLOT LEMMA, dv₂ in
> place of dv, n₂ in place of ϖ-powers, and the twist of §S1 carried through
> the residual assembly exactly as in Step 2 above. The only clause needing a
> word: in (b) the attaining j on a λ₂-line satisfy j ≡ j₁ (mod ℓ₂) because
> the line height m₁ − λ₂(j−j₁) is an integer only then — same congruence
> argument, with gcd(u₂, ℓ₂) = 1. ∎ *(Transfers; no new inequality.)*”

Justification tags: the bulk `by XREF HE6 §S4` under `by EFF.HE7.07` (the substitution table); the congruence clause `computation` at `gcd(u₂, ℓ₂) = 1`; the twist carriage `by EFF.HE7.30` Step 2.

**RESOLUTION TRACE:** Base lines 659–671; untouched. **The `m₁`/`j₁` line-height bookkeeping named here is the same object the shard-3 HE6R1 PE3 F-1 dated line uses to repair `.39`'s cocycle exponent** (“the PIN height m₁ := dv₂(A^{(2)}_{j₁}) at the side's starting index j₁ … the normalization HE7-7′(b)'s own proof uses”).

**TEETH:** Q5 / HE7-SEP2 (P5): strict excess exactly at the level-2 labels, 191 + 5 certificates.

---

### EFF.HE7.35  [corollary]

**CANONICAL STATEMENT:** verbatim, lines 673–683 — **COROLLARY HE7-7″ [r1]**.

> “**COROLLARY HE7-7″ [r1] (the level-2 label of a root; HE6-2″ one level up).**
> **Assume Ψ ∤ f_S** (§S1 CONVENTION [r1]; this is the hypothesis FINDING
> HE6R1-F2 found missing — at a root ρ with Ψ(ρ) = 0 one has
> dv₂(Ψ(ρ)) = ∞, which is a slope of nothing, and the corollary's conclusion
> is simply false for that ρ; peel by LEMMA HE6R1-3 first).
> For ρ a root of f_S, dv₂(f_S(ρ)) = ∞ forces the excess in HE7-7′(b) to be
> infinite, hence **λ₂(ρ) := dv₂(Ψ(ρ)) is a slope of P₂ and
> ι_ρ^{(2)}(R_{λ₂})(β₂,ρ) = 0** — the level-2 label of ρ, well defined
> because R_{λ₂} is a fixed element of K₂[Z] once the n₂ convention is fixed.
> This is what makes the classes S_{λ₂,r₂} of THEOREM HE7.A(2) partition the
> slope's roots when R_{λ₂} is separable.”

**CONDITIONALITY:** Conditional on **Ψ ∤ f_S** (`.09`), whose equivalence chain is licensed only by ANNEX-LEMMA R2-a (shard 3, consumption rider (i): “the displayed equivalence chain is licensed by ANNEX-LEMMA R2-a with F = f_S — so COROLLARY HE7-7″, LEMMA HE7-9 and the label partition are licensed on the stated stratum exactly as consumed”). The final sentence's partition claim is extended to the NON-separable case at ANNEX-LEMMA HE7-13′(a) (shard 2), which proves the label classes partition regardless of separability.

**DERIVATION:** The proof is the displayed one-line argument: `dv₂(f_S(ρ)) = ∞` forces the excess in HE7-7′(b) to be infinite, hence positive — `by EFF.HE7.34`(b) — whose positivity criterion is exactly “κ₂ is a slope λ₂ of P₂ and `ι(R_{λ₂})(β₂) = 0`”. Well-definedness `by EFF.HE7.08` (the residual is fixed once `n₂` is).

**RESOLUTION TRACE:** Base lines 673–683 (r1 landed). Licensed at 2377–2380 (R2-a rider (i)); partition generalised at 1674–1676 and 1745–1747 (HE7-13′(a)).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:COROLLARY HE6-2″` — count **1**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — count **4**.

**TEETH:** Q5 / HE7-SEP2 · the sealed reader's `DEGENERATE-key-divides` status is exactly the stratum where this corollary fails, isolated by the machine.

---

### EFF.HE7.36  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 688–689 — **LEMMA HE7-6 (the block factor)**.

> “**LEMMA HE7-6 (the block factor).** S = S_{λ,r} is the root set of a monic
> factor f_S ∈ O[x] of f, and D″ | deg f_S.”

**CONDITIONALITY:** Unconditional, on `disc f ≠ 0` (`.05`) and integral closedness of O. **Key-free** (HE7-12(c) item (7): “LEMMA HE7-6 is about level-1 labels — key-free”). Re-run per class at HE7-13′(a) (shard 2: “LEMMA HE7-6's argument verbatim”).

**DERIVATION:** [ASSEMBLED — lines 691–699, verbatim]

> “*Proof.* Every root of f has a well-defined level-1 label (COROLLARY
> HE6-2″), and S is the set of roots with label (λ, r); S is Galois-stable
> (LEMMA HE6-5). Hence f_S := Π_{ρ∈S}(x − ρ) has coefficients fixed by
> Gal(K̄₀/K₀), i.e. in K₀, and integral over O (each ρ has v(ρ) = h/e₁ ≥ 0),
> so f_S ∈ O[x] since O is integrally closed; f_S | f because f is separable
> (disc f ≠ 0) and its roots are simple. For the divisibility: each Galois
> orbit inside S has size [L_ρ:K₀] = e(L_ρ)f(L_ρ), and e₁ℓ | e(L_ρ),
> f₁d_r | f(L_ρ) (LEMMA HE6-0′), so D″ = (e₁ℓ)(f₁d_r) divides every orbit
> size, hence divides deg f_S. ∎”

Justification tags: labels `by XREF COROLLARY HE6-2″`; Galois stability `by XREF LEMMA HE6-5`; descent to `O[x]` `by` integral closedness (classical, `.03`); divisibility `by XREF LEMMA HE6-0′`.

**RESOLUTION TRACE:** Base lines 688–699; untouched. Re-instantiated per class at 1678–1682 and 1745–1755 (HE7-13′(a), shard 2).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:COROLLARY HE6-2″` — count **1**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-5` — count **5**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0′` — count **5**.

**TEETH:** Indirect — Q1's per-member `Σef = 8` and the block reads.

---

### EFF.HE7.37  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 701–710 — the reduction to f_S.

> “Consequently we may and do run all level-2 lemmas on **f_S** rather than f:
> then every root of the polynomial under consideration is a level-2 point,
> f_S = Ψ^{μ₂} + Σ_{j<μ₂}A_j^{(2)}Ψ^{j} has top Ψ-coefficient 1 (monic by
> monic), and the level-2 configuration is *structurally identical* to the
> level-1 one (where f = Φ′^{μ} + … had top coefficient 1). This is what
> removes the "principal part" bookkeeping that a general Montes-style
> treatment needs; it is also the step that HE3's stage-CS route could not
> take, because there the inner object was the resolvent over R, whose roots
> are not roots of f. **Here f_S's roots ARE roots of f, so class sizes
> transport by construction.**”

**CONDITIONALITY:** **The sentence “every root of the polynomial under consideration is a level-2 point” silently excluded the Ψ | f_S stratum**; the note says so itself at `.38`. With the §S1 CONVENTION `[r1]` in force the reduction is sound. The reduction does NOT pin `μ₂` when the block is proper — that gap is `.39`.

**DERIVATION:** Scope/method declaration; its two substantive claims are `by EFF.HE7.36` (f_S is a monic O-factor with all roots level-2 points) and `definitional` (monic-by-monic gives top Ψ-coefficient 1).

**RESOLUTION TRACE:** Base lines 701–710; qualified at 712–732 (`[r1]` additions (a) and (b), `.38`/`.39`); re-applied per block at 1755–1757 (HE7-13′(a): “The reduction of §S5.5 applies to f_C exactly as to f_S”).

XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-BOX-6` — count **12** (the “original defect” this step repairs, per §S9).

**TEETH:** NONE directly (method step).

---

### EFF.HE7.38  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 712–720 — `[r1]` addition (a).

> “**[r1] TWO ADDITIONS THE RECONCILIATION SUPPLIES AT THIS EXACT STEP.**
> *(a) The stratum this reduction silently excluded (FINDING HE6R1-F2).* The
> sentence "every root of the polynomial under consideration is a level-2 point"
> is true, but a root ρ with Ψ(ρ) = 0 is a level-2 point with dv₂(Ψ(ρ)) = ∞: the
> Ψ-development then has A₀^{(2)} = 0, P₂ loses its j = 0 pin, and
> Σ_{λ₂}L_{λ₂} = μ₂ (THEOREM HE7.A(1)) fails by the missing block. The §S1
> CONVENTION [r1] excludes it and **LEMMA HE6R1-3** disposes of it: Ψ is then
> irreducible over O of degree D″ with (e, f) = (e₁ℓ, f₁d_r), a simple factor,
> and one peels f_S = Ψ·f_S′ once, running everything on f_S′ at μ₂ − 1.”

**CONDITIONALITY:** Rests on the external **LEMMA HE6R1-3**, whose irreducibility half HE7 does not reprove — “a direct oracle test of LEMMA HE6R1-3's *irreducibility of Ψ over O of degree D″ with (e,f) = (e₁ℓ, f₁d_r)*, **which no textual argument of this note supplies**” (§S11, line 1424–1425, shard 2). Level-generic at `.49`. At the refined key, HE7-12(c) item (11) re-derives the peel's hypothesis directly.

**DERIVATION:** The failure mechanism is displayed inline (`Ψ(ρ) = 0 ⟹ dv₂(Ψ(ρ)) = ∞ ⟹ A₀^{(2)} = 0 ⟹` no j = 0 pin `⟹ Σ L = μ₂` fails), `by EFF.HE7.13` (clause (1)) + `computation`. The disposal is `by XREF LEMMA HE6R1-3` (cited, not reproved).

**RESOLUTION TRACE:** Base lines 712–720 (r1 landed). Level-generic at 1051–1058; re-derived at the refined key at 905–911 (HE7-12(c) item (11)); machine-decided at 1415–1430 (§S11 `[r1]`, shard 2).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — count **4**.

**TEETH:** `he7r1_supp.py` A1–A5: 8/8 exact peels, 8/8 one-peel-only, 8/8 peeled reads, 2/2 PARI σ(f), **2/2 PARI σ(Ψ)** — the last is the only evidence for the irreducibility half.

---

### EFF.HE7.39  [instance-record]

**CANONICAL STATEMENT:** verbatim, lines 721–732 — `[r1]` addition (b), the proper-block read.

> “*(b) How the level-2 read STARTS when the block is PROPER (LEMMA HE6R1-2).*
> This subsection reduces to f_S but does not exhibit it: at a non-separable
> R_λ the HE6.A sandwich leaves slack D′ℓΣ_r(m_r−1)d_r, so deg f_S — hence
> μ₂ = deg f_S/D″ — is not pinned by HE6 + HE7 alone (first live at μ ≥ 5, i.e.
> n ≥ 10, inside COROLLARY HE7.B(i)'s region). **LEMMA HE6R1-2** closes it:
> with g := f/f_S one has r ∤ R_λ^{(g)}, hence dv₂(g(ξ)) = c_g is CONSTANT over
> level-2 points, hence h_{F₂,f}(κ₂) = h_{F₂,f_S}(κ₂) + c_g for every rational
> κ₂ > T₂ — so the > T₂ part of P₂(f) is P₂(f_S) translated: same breakpoints,
> slopes and lengths, giving μ₂ = Σ_{λ₂ > T₂}L_{λ₂}(f) and |S_{λ,r}| = D″μ₂
> **read off f**, with R_{λ₂}^{f} and R_{λ₂}^{f_S} of equal degree and equal
> radical (equal outright when separable). Every consumer below may therefore
> take μ₂, the level-2 sides and the residual from f itself.”

**CONDITIONALITY:** **The parenthesis “(equal outright when separable)” is FALSE as written and is corrected twice in shard 3.**
First correction (HE6R1 PE2 F-1 dated line, 2593–2620): the parenthesis “carries verbatim the clause HE6R1's PE1 F-3 falsified — nothing pins the scalar to 1”; the corrected reading is

>     R_{λ₂}^{f} = γ_g · β^{c₁(h_{F₂,f_S}(λ₂), c_g)} · R_{λ₂}^{f_S} ,

> “**equal up to a fixed K₂^× scalar per side when separable** — not
> equal outright.”

Second correction (HE6R1 PE3 F-1 dated line, 2624–2652), which supersedes the first line's **exponent argument**: the line value `h(λ₂)` need not be an integer off the first side at `ℓ₂ ≥ 2`, so the corrected argument is the **PIN height**:

>     R_{λ₂}^{f} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R_{λ₂}^{f_S} .

with scope: “it agrees with the pin-height form exactly when j₁ = 0 (a single-side level-2 polygon, or the first side); at ℓ = 1, s(·) ≡ 0 gives c₁ ≡ 0 and the scalar is γ_g alone”.
**Consumers are scale-invariant** (PE2 site check, quoted at 2615–2618): “THEOREM HE7.A(2) consumes the monic irreducible factors, the α-refine consumes residual roots, separability checks are scale-invariant.” **No sealed number, statement, or verdict moves.** The whole unit rests on the external **LEMMA HE6R1-2**, unproved here.

**DERIVATION:** Cited, not derived: the mechanism (constant `c_g`, translated polygon) is displayed inline but its justification is `by XREF LEMMA HE6R1-2`. The corrected scalar is derived in shard 3 from `by EFF.HE7.08` (the cocycle) + ANNEX-LEMMA R1-a(iii)(iv) + LEMMA HE6R1-2(a)'s no-excess display.

**RESOLUTION TRACE:** Base lines 721–732 (r1 landed). Scalar corrected at 2593–2622; exponent argument corrected at 2624–2652. Also declared a supersession of HE7-BOX-4 “in read form” (§S0 line 59 and §S9 line 1335–1341, shard 2).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/HE6R1_passPE2_report.md:F-1` — grep-verified count **3** (the first correction's source pass).
XREF: `lean/notes/openmath/HE6R1_passPE3_report.md:F-1` — grep-verified count **12** (the second correction's source pass — the pin-height argument).
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:THEOREM HE6.A` — count **19** (the sandwich whose slack is named).

**TEETH:** **NONE — proof-only.** §S9's HE7-BOX-2 `[r1]` states it explicitly: “what stays unexercised anywhere is d_r ≥ 3, f₁ ≥ 2 stage genres, μ ≥ 5 (hence proper blocks — LEMMA HE6R1-2's own configuration is proof-only) and level 3.” (Level 3 was subsequently exercised by `he7rannex_supp.py`; proper blocks were not.)

---

### EFF.HE7.40  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 743–745 — **(RES₂), the level-2 resultant symmetry.** (Physically inside §S5.6's proof; emitted as its own unit because it is cited **by designation** from §S6's inductive step (line 1019, as `(RES_i)`) and from §S8's GENHN.C comparison (line 1237). This is the shard's one deliberate departure from strict source order — boundary audit §6 item 15.)

> “The resultant symmetry
> Σ_{ρ}dv₂(g(ρ)) = e₁ℓ·v(±Res(f_S, g)) = Σ_{ξ:g(ξ)=0}dv₂(f_S(ξ)) holds for
> monic g ∈ O[x] because dv₂ = e₁ℓ·v is a positive multiple of v (**(RES₂)**).”

**CONDITIONALITY:** Unconditional; classical (resultant symmetry, `.03`'s “Classical only” list). **Key-free** — HE7-12(c) item (8) lists “(RES₂) (key-free)” among what HE7-9/HE7-10 consume. Level-generic: §S6 lists “(RES_i) (a positive multiple of v)” among the level-independent inputs.

**DERIVATION:** One line, displayed: resultant symmetry over `v`, scaled by the positive integer `e₁ℓ`. `by` classical resultant symmetry + `definitional` (`dv₂ := e₁ℓ·v`, `.06`).

**RESOLUTION TRACE:** Base lines 743–745; untouched. Cited at 1019 (§S6) and 1237 (§S8).

**TEETH:** Q2 / HE7-SLOT2 (P2) is the resultant identity in machine form: `v(Res(f, C)) = 2·dv₂(C)`, **12,632 checks, 0 violations** · Q4's 4,259 flat identities are (RES₂) applied to `Ψ₂`.

---

### EFF.HE7.41  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 736–741 — **LEMMA HE7-9 and LEMMA HE7-10**, emitted as ONE unit because a single proof discharges both and LEMMA HE7-10's proof obligations include LEMMA HE7-9's (†₂-count) setup (boundary audit §6 item 14).

> “**LEMMA HE7-9 (level-2 slope counts, (SEP)-free).** With
> n_{λ₂} := #{ρ : f_S(ρ) = 0, dv₂(Ψ(ρ)) = λ₂}: (a) P₂ has no slope ≤ T₂;
> (b) n_{λ₂} = D″·L_{λ₂} for every slope λ₂ of P₂.
>
> **LEMMA HE7-10 (level-2 nonemptiness).** For every slope λ₂ of P₂ and every
> monic irreducible r₂ | R_{λ₂}, the class S_{λ₂,r₂} is NONEMPTY.”

**CONDITIONALITY:** Unconditional given the standing convention Ψ ∤ f_S (`.09`; ANNEX-LEMMA R2-a's rider (i) names LEMMA HE7-9 among what it licenses). **(SEP)-free** — no separability of `R_λ` is used, which is what lets HE7-13′(a) (shard 2) run them on each block factor. At the refined key by HE7-12(c) item (8); at level i ≥ 3 by R1.2 item 1 (counts are twist-free).

**DERIVATION:** [ASSEMBLED — lines 743–772, verbatim, the joint proof]

> “*Proof.* The resultant symmetry
> Σ_{ρ}dv₂(g(ρ)) = e₁ℓ·v(±Res(f_S, g)) = Σ_{ξ:g(ξ)=0}dv₂(f_S(ξ)) holds for
> monic g ∈ O[x] because dv₂ = e₁ℓ·v is a positive multiple of v (**(RES₂)**).
> Fix r₂,₀ ∈ K₂[Z] irreducible of degree μ₂+1 (finite fields have
> irreducibles of every degree; deg r₂,₀ > μ₂ ≥ deg R_{λ₂} for every side, so
> r₂,₀ never divides a level-2 residual, and r₂,₀(0) ≠ 0). For each rational
> κ₂ > T₂ form Ψ₂ := Ψ₂,{κ₂,r₂,₀} (DEFINITION HE7-3, available by (LIFT₂) —
> §S4.3). Then LEMMA HE7-7 gives, for every root ξ of Ψ₂,
> dv₂(Ψ(ξ)) = κ₂ and ι^{(2)}(r₂,₀)(β₂) = 0, so LEMMA HE7-7′(b) gives
> dv₂(f_S(ξ)) = h_{F₂}(κ₂) exactly (no excess: β₂'s minimal polynomial over
> ι^{(2)}(K₂) has degree > deg R_{λ₂}); and LEMMA HE7-7′(a) gives
> dv₂(Ψ₂(ρ)) = ℓ₂(μ₂+1)·min(λ₂(ρ), κ₂) for every root ρ of f_S. Hence for
> every rational κ₂ > T₂
>
>     (†₂-count)   Σ_{λ₂} n_{λ₂}·min(λ₂, κ₂) = D″·h_{F₂}(κ₂)
>                                             = D″·Σ_{λ₂}L_{λ₂}·min(λ₂, κ₂),
>
> the last step being HE3-3's convex duality (★), valid verbatim at rational
> κ₂. Both clauses now follow by HE6-3's own argument: sampling κ₂ in
> (T₂, λ₂,min) forces the constant term to vanish and kills every slope ≤ T₂
> (clause (a)); sampling κ₂ in each gap (λ₂,i, λ₂,i+1) — always nonempty in ℚ —
> and eliminating from the largest slope down gives n_{λ₂} = D″L_{λ₂}
> (clause (b)). For LEMMA HE7-10, take Ψ₂ := Ψ₂,{λ₂,r₂} with r₂ | R_{λ₂}: the
> ξ-side of (RES₂) is now **strictly** greater than deg(Ψ₂)·h_{F₂}(λ₂) (every
> root ξ has ι^{(2)}(R_{λ₂})(β₂) = 0, so LEMMA HE7-7′(b) gives strict excess),
> while the ρ-side equals deg(Ψ₂)·h_{F₂}(λ₂) + Σ_{ρ∈S_{λ₂,r₂}}ε₂(ρ) by
> LEMMA HE7-7′(a) + LEMMA HE7-9 + (★). Comparing, the sum over S_{λ₂,r₂} is
> positive with every term positive, so the set is nonempty. ∎
> *(Transfers verbatim; the ONLY inputs beyond HE6's own §S5 are (SLOT₂),
> (LIFT₂), LEMMA HE7-6 and (RES₂).)*”

Justification tags: `by EFF.HE7.40` ((RES₂)); the auxiliary `r₂,₀` `by` finite-field existence of irreducibles of every degree (classical, `.03`); the test family `by EFF.HE7.27` + `by EFF.HE7.24`; the ξ-side `by EFF.HE7.30`; both displays `by EFF.HE7.34`; the (★) step `by XREF HE3-3` (convex duality); the two samplings `by XREF LEMMA HE6-3`'s own argument under `by EFF.HE7.07`; nonemptiness by strict-vs-equal comparison `computation`.

**RESOLUTION TRACE:** Base lines 736–772; untouched. Licensed at 2377–2380 (R2-a rider (i)); re-run per block at 1757–1764 (HE7-13′(a), shard 2); at the refined key at 901–903 (HE7-12(c) item (8)).

XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-3` — count **15**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-3` — count **12**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-4` — count **8** (HE6-4 is the level-1 nonemptiness this transfers; named in §S5.6's heading and in §S6(iii)).

**TEETH:** Q4/Q5 (P4, P5): **0 violations in 4,259 level-2 flat identities** and **191 strict + 5 infinite excesses exactly at the level-2 labels** — “the machine form of LEMMA HE7-9 and LEMMA HE7-10” · `he7r2_supp.py` B3 checks the HE7-9(b) count identity **at the refined key**, 42/42 (with the `[r3]` peel-guard disclosure at `.46`).

---

### EFF.HE7.42  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 776–777 — **LEMMA HE7-11 (Galois equivariance)**.

> “**LEMMA HE7-11.** For g ∈ Gal(K̄₀/K₀) and ρ ∈ S with level-2 label
> (λ₂, r₂), the root gρ has level-2 label (λ₂, r₂) — the same r₂ ∈ K₂[Z].”

**CONDITIONALITY:** Unconditional. Key-form-free (HE7-12(c) item (9): “needs only Ψ^{(w)} ∈ O[x] with Galois-fixed coefficients and g-fixed n₂ — both hold”). Separability-free — HE7-13′(a) records that its proof “nowhere uses separability of R_λ”. **At level i ≥ 3 the premise was not even well posed before ANNEX R** (R1.2 item 5: “n_{i+1}(k) is now a well-defined Laurent monomial in ϖ, Φ₁, …, Φ_i with O-coefficients — g-fixed (under the broken display this premise was not even well posed at i ≥ 2)”).

**DERIVATION:** [ASSEMBLED — lines 779–785, verbatim]

> “*Proof.* Ψ ∈ O[x] and each n₂(k) is a Laurent monomial in ϖ and Φ′, all with
> g-fixed coefficients; v is g-invariant. So dv₂(Ψ(gρ)) = λ₂ and
> β₂,gρ = ḡ(β₂,ρ) with ḡ ∈ Gal(k̄/F_Q) the induced residue automorphism. By
> LEMMA HE6-5, ι_{gρ} = ḡ∘ι_ρ; since β_{gρ} = ḡ(β_ρ), also
> **ι^{(2)}_{gρ} = ḡ∘ι^{(2)}_ρ** (both are the ι_{gρ}-semilinear embedding
> K₂ → k̄ sending β ↦ β_{gρ}). Hence
> ι^{(2)}_{gρ}(r₂)(β₂,gρ) = ḡ(ι^{(2)}_ρ(r₂)(β₂,ρ)) = 0. ∎”

Justification tags: g-invariance of v `by` uniqueness of the extension (classical, `.03`); the level-1 half `by XREF LEMMA HE6-5`; the transport equivariance `by EFF.HE7.06` (uniqueness of the semilinear embedding).

**RESOLUTION TRACE:** Base lines 776–785; untouched. Re-used at 1748–1749 (HE7-13′(a)); generalised at 2218–2223 (R1.2 item 5).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-5` — count **5**.

**TEETH:** Indirect — Q1's σ agreement (a class that were not Galois-stable would not be a single irreducible factor).

---

### EFF.HE7.43  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 801–810 — §S5.8's `[r2]` preamble: the gap PE1 found, and the slot-domination mechanism.

> “The pre-r2 text applied THEOREM HE7.A and the §S5 package to the REFINED
> key Ψ − w after an α-refine (HE7.A(3), §S8 row 5, inside LEMMA HE7-8's
> hypothesis) without a displayed lemma: Ψ − w is not of DEFINITION HE6-1's
> form, and §S5's proofs cite HE6-1/HE6-2 for the literal family Ψ_{κ,r}.
> The two lemmas below close that gap. The mechanism is **slot domination**:
> every occupied Φ′-slot of Ψ sits at slot value exactly T₂ (DEFINITION
> HE6-1: the slot s = ℓt carries dv(B_t) = (d_r−t)u, so its value is
> ℓ(d_r−t)u + ℓtu = T₂, and the monic top slot ℓd_r has value ℓd_r·u = T₂),
> while every occupied slot of the refine increment w sits at value
> ≥ dv₂(w) > T₂ — strictly above the line.”

**CONDITIONALITY:** None. This is the note's own statement of PE1 FINDING F-1 (a GAP) and the shape of its repair. **The slot-geometry claim is machine-verified**: `he7r2_supp.py` B1, 42/42.

**DERIVATION:** The slot-geometry computation is displayed inline: `by XREF DEFINITION HE6-1` (the key's coefficient heights `dv(B_t) = (d_r−t)u`) + `computation` (`ℓ(d_r−t)u + ℓtu = ℓd_r·u = T₂`), and `by EFF.HE7.11` (the slot-min definition) for `w`'s side.

**RESOLUTION TRACE:** Base lines 801–810 (r2 landed); untouched.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:DEFINITION HE6-1` — count **7**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-1` — grep-verified count **4**.

**TEETH:** `he7r2_supp.py` **B1** — “slot geometry (Ψ's occupied Φ′-slots all exactly at T₂; w's slot-min exactly λ₂ > T₂; (LIFT₂) contract res₂(w, λ₂) = s₂) — **42/42**”, with the `[r3]` (R-b) same-instrument-coupling disclosure decorrelated by PE2's independent instrument (634/634).

---

### EFF.HE7.44  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 812–857 — **LEMMA HE7-12 [r2] (SLOT-DOMINATION)**, clauses (a)–(d) including (d)'s `[r3]` `W ≠ 0` rider.

> “**LEMMA HE7-12 [r2] (SLOT-DOMINATION — the §S5 package survives every
> above-the-line perturbation of the key).** Let (λ, r) be a level-2 datum
> with key Ψ (DEFINITION HE7-1), and let w ∈ O[x], w ≠ 0, with deg w < D″
> and level-2 slot value ν := dv₂(w) = min_{s<ℓd_r}(ℓ·dv(c_s) + s·u) > T₂
> (w = Σ_s c_sΦ′^{s} its Φ′-development). Put Ψ^{(w)} := Ψ − w, monic of
> degree D″. Then, **with the level-2 point set of DEFINITION HE7-1
> unchanged** (it is defined by level-1 data, not by the key):
>
> (a) *(off-disk invariance)* for every ξ ∈ K̄₀ that is NOT a level-2
> point, with δ := dv(Φ′(ξ)), ε₀ := (h − dv ξ)⁺, ε₁ := (u − ℓδ)⁺,
>
>     dv₂(w(ξ)) − dv₂(Ψ(ξ)) ≥ (ν − T₂) + ε₁ − ℓ(D′−1)ε₀ > 0 ,      (S5.8.1)
>
> hence dv₂(Ψ^{(w)}(ξ)) = dv₂(Ψ(ξ)) = ℓ²d_r·min(δ, λ) = T₂ − ℓd_r·ε₁ —
> the SAME off-disk value formula as LEMMA HE7-4's;
>
> (b) *(on-disk)* at every level-2 point ξ, dv₂(w(ξ)) = ν exactly with
> residue res(w(ξ)/n₂(ν)(ξ)) = ι_ξ^{(2)}(c_w) for a fixed c_w ∈ K₂^×
> independent of ξ ((SLOT₂) applied to w), and dv₂(Ψ^{(w)}(ξ)) > T₂; with
> (a): **dv₂(Ψ^{(w)}(ξ)) > T₂ iff ξ is a level-2 point** — the disk
> criterion holds for Ψ^{(w)};
>
> (c) *(the package)* every statement of §S5 and THEOREM HE7.A(1)(2) —
> LEMMA HE7-4 (in the form (a)+(b)), LEMMA HE7-5, DEFINITION HE7-3's test
> family, LEMMA HE7-7, LEMMA HE7-7′, COROLLARY HE7-7″, LEMMA HE7-6,
> LEMMA HE7-9, LEMMA HE7-10, LEMMA HE7-11, the class-size sandwich, the
> §S1 CONVENTION with LEMMA HE6R1-3's peel, and LEMMA HE6R1-2's read —
> holds VERBATIM with Ψ^{(w)} in place of Ψ (same λ, r, dv₂, n₂, K₂, T₂,
> ι^{(2)}; labels and residues now read on Ψ^{(w)}), by the SAME proofs;
>
> (d) *(chains fold into one application)* if w₁, …, w_j each have degree
> < D″ and slot value > T₂ then W := w₁ + ⋯ + w_j has deg W < D″ and
> dv₂(W) ≥ min_i dv₂(w_i) > T₂ (the slot-min is ultrametric slotwise), so
> every iterate Ψ − W of a refine chain is covered by ONE instance of
> (a)–(c). **[r3, HE7-PE2 F-1]** (a)–(c) also hypothesize **W ≠ 0**, and
> (d) supplies it: in a refine chain the values dv₂(w_i) are pairwise
> DISTINCT (they are the strictly increasing slopes λ₂^{(0)} < λ₂^{(1)} <
> ⋯ of LEMMA HE7-13, inductively available at each step — the two lemmas
> induct together along the chain, the base W = w₁ being a single nonzero
> (LIFT₂) polynomial), so the slot-min is attained by the least-slope
> increment ALONE and dv₂(W) = min_i dv₂(w_i) < ∞ EXACTLY (ultrametric
> equality at a uniquely attained min), whence W ≠ 0. And at W = 0
> (excluded in a chain by the above, but allowed by the ≥-bound alone)
> the iterate is Ψ itself and §S5 applies directly — exactly the
> "W = 0 or as in LEMMA HE7-12(d)" split that LEMMA HE7-13's statement
> already makes.”

**CONDITIONALITY:** **Two live cross-shard items.**
(a) **Clause (c) item (7)'s dependency inventory is INCOMPLETE and is completed by ANNEX R R4** (shard 3, lines 2414–2426), quoted:

> “Item (7)'s sentence "LEMMA HE6R1-2's read consumes only the HE7-7/7′
> analogues, items (5)–(6)" is inaccurate. The full inventory (Codex F4
> = the orchestrator's pre-verdict key P-1 item 7, exact match): clause
> (a) also consumes **LEMMA HE6-4 and LEMMA HE6-2′** — LEVEL-1 lemmas,
> key-free, unchanged under Ψ ↦ Ψ^{(w)}; clause (b) also consumes
> **(LIFT₂), DEFINITION HE7-3's test family, LEMMA HE7-9(a), and THEOREM
> HE7.A(1)**; clause (c) again the test family and HE7-7/7′. All of
> these transfer to the refined key through items **(1), (2), (5), (6),
> (8)** of the same audit, so LEMMA HE7-12(c)'s CONCLUSION is unaffected
> — the erratum is citation-completeness on one sentence, no transfer
> breaks.”

(b) **Clause (d)'s `[r3]` parenthetical inherits ANNEX F-1's per-block reading** (line 1658–1662: “LEMMA HE7-12(d)'s [r3] parenthetical (the pairwise-distinct dv₂(w_i)) inherit the same reading: through HE7-13′ their justifications route per block”), discharged there by the second wiring bullet: “Along any path the increments' values dv₂(w_i) are the refined-at slopes of THAT path, strictly increasing by the previous bullet — pairwise distinct, so the [r3] ultrametric-equality argument applies verbatim. (Distinct blocks' chains live at DIFFERENT keys and never mix increments.)”

**DERIVATION:** [ASSEMBLED — lines 859–916, verbatim]

> “*Proof.* **(a).** By (SLOT₂)(c), dv₂(w(ξ)) ≥ min_s(ℓ·dv_ξ(c_s) + s·ℓδ).
> Each level-1 coefficient loses at most (D′−1)ε₀: dv_ξ(c) =
> min_i(e₁v(c_i) + i·dv ξ) ≥ min_i(e₁v(c_i) + ih) − (D′−1)(h − dv ξ)⁺ =
> dv(c) − (D′−1)ε₀ (i ≤ D′−1; if dv ξ ≥ h there is no loss). Each slot
> factor loses at most (ℓd_r−1)ε₁: s·ℓδ = su − s(u − ℓδ) ≥ su − (ℓd_r−1)ε₁
> (s ≤ ℓd_r−1; if ℓδ ≥ u there is no loss). Hence
>
>     dv₂(w(ξ)) ≥ ν − (ℓd_r − 1)ε₁ − ℓ(D′−1)ε₀ .
>
> For Ψ, LEMMA HE7-4 at a non-level-2 point gives ε(ξ) = 0, so
> dv₂(Ψ(ξ)) = ℓ²d_r·min(δ, λ) = ℓd_r·min(ℓδ, u) = ℓd_r(u − ε₁) =
> T₂ − ℓd_r·ε₁ (also when ε₁ = 0, where it is T₂). Subtracting gives
> (S5.8.1)'s displayed bound. Positivity, by the case split of (S5.2) [r2]
> on ε₁ at ε₀ = 0: if ε₀ > 0 then LEMMA HE6-0 gives δ = D′(h − ε₀), so
> ε₁ = ℓ(λ − D′h) + ℓD′ε₀ and ε₁ − ℓ(D′−1)ε₀ = ℓ(λ − D′h) + ℓε₀ > 0; if
> ε₀ = 0 and ε₁ > 0 the bound is (ν − T₂) + ε₁ > 0; if ε₀ = ε₁ = 0 it is
> ν − T₂ > 0. In every case dv₂(w(ξ)) > dv₂(Ψ(ξ)), so the ultrametric gives
> dv₂(Ψ^{(w)}(ξ)) = dv₂(Ψ(ξ)) exactly.
>
> **(b).** (SLOT₂) applies to w (deg w < D″, w ≠ 0): dv₂(w(ξ)) = ν exactly
> with the stated residue, ν > T₂; and dv₂(Ψ(ξ)) > T₂ (LEMMA HE7-4), so
> dv₂(Ψ^{(w)}(ξ)) ≥ min(dv₂(Ψ(ξ)), ν) > T₂.
>
> **(c)** is an audit of every use the §S3–S5 proofs make of the key.
> (1) (SLOT₂)/(LIFT₂) never mention Ψ — they are statements about C ∈ O[x]
> with deg C < D″, the Φ′-slots and the level-2 points, all key-free.
> (2) DEFINITION HE7-3's test family is built from (LIFT₂)-coefficients C_t
> (functions of Φ′ and ϖ only, unchanged) and powers of the key; replace
> Ψ by Ψ^{(w)} throughout. (3) LEMMA HE7-4 for Ψ^{(w)} is exactly (a)+(b) —
> and these two clauses (the off-disk value formula and the disk criterion)
> are the only two facts §S5 ever consumes from HE7-4. (4) LEMMA HE7-5's
> proof uses only v(Ψ(ρ)) ∈ (1/e(L_ρ))ℤ and the unit residue of
> Ψ(ρ)^{ℓ₂}/n₂(u₂)(ρ) — no property of the key's form; run it on Ψ^{(w)}
> verbatim. (5) LEMMA HE7-7 Step 1's estimate (S5.3) is about the C_t
> (unchanged); the key enters only through δ₂ := dv₂(key(ξ)) and its
> off-disk formula δ₂ = T₂ − ℓd_r·ε₁, supplied by (a); Step 2 consumes
> (SLOT₂) at the C_t, the n₂-twist algebra (key-free) and the δ₂ ⋚ κ₂
> dichotomy — verbatim. (6) LEMMA HE7-7′/COROLLARY HE7-7″: the developments
> in powers of the monic degree-D″ polynomial Ψ^{(w)} have coefficients of
> degree < D″, so (SLOT₂) applies to them; the congruence argument uses
> gcd(u₂, ℓ₂) = 1 only. (7) LEMMA HE7-6 is about level-1 labels — key-free;
> LEMMA HE6R1-2's read consumes only the HE7-7/7′ analogues, items (5)–(6).
> (8) LEMMA HE7-9/HE7-10 consume (RES₂) (key-free), the test family at
> Ψ^{(w)} (item 2), items (5)–(6), (★), and an irreducible r₂,₀ of degree
> μ₂+1 (key-free). (9) LEMMA HE7-11 needs only Ψ^{(w)} ∈ O[x] with
> Galois-fixed coefficients and g-fixed n₂ — both hold. (10) The class-size
> sandwich composes (4), (8), (9) as in §S5.7. (11) The §S1 CONVENTION and
> the peel at Ψ^{(w)}: LEMMA HE6R1-3's proof needs "every root of the key
> is a level-2 point" — a root ξ of Ψ^{(w)} has dv₂(Ψ^{(w)}(ξ)) = ∞ > T₂,
> so ξ is a level-2 point by (b)'s disk criterion; Galois stability,
> integral closedness of O and disc ≠ 0 are key-free; and deg Ψ^{(w)} = D″
> with e ≥ e₁ℓ, f ≥ f₁d_r forces (e, f) = (e₁ℓ, f₁d_r) by the same
> sandwich.
>
> **(d).** The Φ′-development of a sum is the sum of the developments, and
> on each level-1 coefficient dv is ultrametric, so each slot value of W is
> ≥ the min of the w_i's slot values at that slot; taking mins,
> dv₂(W) ≥ min_i dv₂(w_i) > T₂. ∎”

Justification tags: (a) `by EFF.HE7.11`(c) + `by EFF.HE7.28` + `by EFF.HE7.31` ((S5.2) as corrected) + `computation`; (b) `by EFF.HE7.11` + `by EFF.HE7.28`; (c) an eleven-item transfer audit, each item `by` the named unit; (d) `computation` (ultrametric slotwise), with the `W ≠ 0` half `by EFF.HE7.45` (LEMMA HE7-13's strict increase — the two lemmas induct together).

**RESOLUTION TRACE:** Base lines 812–916 (r2 landed; (d)'s `[r3]` rider landed at r3). Item (7) completed at 2414–2426 (ANNEX R R4); (d)'s parenthetical re-routed per block at 1658–1662 and 1841–1845 (ANNEX F-1). **Note the mutual induction with `.45`: (d)'s `W ≠ 0` cites HE7-13, and HE7-13's proof cites HE7-12(c)(d) — the note states the circularity is broken by simultaneous induction along the chain (“the two lemmas induct together along the chain, the base W = w₁ being a single nonzero (LIFT₂) polynomial”). Flagged, not repaired, at OPEN-CALL 3.**

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0` — count **17**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-4` — count **8** (added by R4).
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-2′` — count **4** (added by R4).
XREF: `lean/notes/openmath/HE7_passPE2_report.md:F-1` — grep-verified count **5**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F4` — grep-verified count **5**.

**TEETH:** `he7r2_supp.py` **B2** — “the off-disk inequality (S5.8.1) in resultant-sum form plus the invariance conclusion dv₂-Res(g, Ψ^{(1)}) = dv₂-Res(g, Ψ), on five off-disk strata per member covering all three offset cases — **210/210**”, **with the `[r3]` vacuity disclosure**: the δ = ∞ INEQUALITY half is vacuous on 41 of the 42 members (see `.46`).

---

### EFF.HE7.45  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 918–934 — **LEMMA HE7-13 [r2] (the strict slope increase along the refine chain)**.

> “**LEMMA HE7-13 [r2] (the strict slope increase along the refine chain —
> DERIVED, not assumed).** Let Ψ̃ = Ψ − W with W = 0 or as in LEMMA
> HE7-12(d), let f_S satisfy the standing convention at Ψ̃ (Ψ̃ ∤ f_S), and
> suppose the polygon of f_S with respect to Ψ̃ is the single side of
> integer slope λ₂ > T₂ with residual R₂ = (Z − s₂)^{μ₂}, s₂ ∈ K₂^×
> (the α-refine configuration: ℓ₂ = 1, the endpoint j = 0 attains, so
> s₂ ≠ 0). Let w be a (LIFT₂) polynomial at height λ₂ with residue s₂
> (it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w.
> Then EVERY root ρ of f_S has
>
>     dv₂(Ψ̃^{(1)}(ρ)) > λ₂    (possibly = ∞) ,                     (S5.8.2)
>
> and hence every slope of the polygon of f_S with respect to Ψ̃^{(1)}
> (after the peel of LEMMA HE6R1-3 at Ψ̃^{(1)}, if it fires) is > λ₂. In
> particular, along any α-refine chain of the read the slopes satisfy
> λ₂^{(0)} < λ₂^{(1)} < ⋯ strictly — LEMMA HE7-8's hypothesis is the
> read's actual configuration, derived.”

**CONDITIONALITY:** **PURE-NODE ONLY. Its conclusion-as-stated is FALSE outside the displayed hypothesis, and ANNEX F-1 says so in those words** (line 1626): “HE7-13's conclusion-as-stated is genuinely FALSE at mixed nodes”. PE3's constructed counter-instance is quoted verbatim from ANNEX F-1 (lines 1627–1631):

> “PE3's constructed counter-instance
> (p, u, s, λ₂) = (5, 5, 1, 11), R₂ = (Z−1)²(Z−2), pins
> (0,33),(1,23),(2,11),(3,0), has post-refine polygon (0,34),(2,11),(3,0)
> — **the λ₂ = 11 side SURVIVES the refine**, carrying the b = 2 class
> (PARI σ = {(4,1),(8,1)}, the (4,1) factor = the undisturbed b-class).”

**The displayed statement is NOT edited and is NOT wrong** — its hypothesis (“the single side … with residual R₂ = (Z − s₂)^{μ₂}”) excludes the counter-instance. What was wrong was the *wiring* at THEOREM HE7.A(3), which fired the refine at mixed nodes too; that is `.14`'s rider. The mixed case is supplied by **ANNEX-LEMMA HE7-13′** (shard 2), whose clause (b) is “LEMMA HE7-13's conclusion, held by the refined class alone”. Mixed nodes are **first live at μ₂ = 3 (n = 12)** and **vacuous at every machine-certified degree**. Additionally: the whole lemma rests on the standing convention at Ψ̃ (`.09`), licensed by ANNEX-LEMMA R2-a.

**DERIVATION:** [ASSEMBLED — lines 936–951, verbatim]

> “*Proof.* By the package at Ψ̃ (LEMMA HE7-12(c); §S5 itself when W = 0),
> every root ρ of f_S is a level-2 point carrying a label on Ψ̃. The single
> side has length μ₂, so LEMMA HE7-9(b) at Ψ̃ gives n_{λ₂} = D″L_{λ₂} =
> D″μ₂ = deg f_S: EVERY root ρ has dv₂(Ψ̃(ρ)) = λ₂, and COROLLARY HE7-7″ at
> Ψ̃ gives ι_ρ^{(2)}(R₂)(β₂,ρ) = 0 with β₂,ρ = res(Ψ̃(ρ)/n₂(λ₂)(ρ)) (ℓ₂ = 1,
> u₂ = λ₂). Since R₂ = (Z − s₂)^{μ₂} has the single root s₂,
> β₂,ρ = ι_ρ^{(2)}(s₂). By (LIFT₂)'s defining clause, dv₂(w(ρ)) = λ₂ with
> res(w(ρ)/n₂(λ₂)(ρ)) = ι_ρ^{(2)}(s₂). So Ψ̃^{(1)}(ρ) = Ψ̃(ρ) − w(ρ) is a
> difference of two elements of the same dv₂ and the SAME residue, whence
> (S5.8.2). For the polygon: dv₂(W + w) ≥ min(dv₂(W), λ₂) > T₂ (LEMMA
> HE7-12(d)), so the package holds at Ψ̃^{(1)}, and LEMMA HE7-9(b) at
> Ψ̃^{(1)} says each slope λ₂′ of the new polygon carries D″L_{λ₂′} > 0
> roots with dv₂(Ψ̃^{(1)}(ρ)) = λ₂′; by (S5.8.2) every such λ₂′ > λ₂. If
> instead Ψ̃^{(1)} | f_S, the peel (available at Ψ̃^{(1)} by LEMMA
> HE7-12(c) item 11) removes one factor Ψ̃^{(1)} and shifts the development
> by one block (§S5.5), leaving the same conclusion for f_S′. ∎”

Justification tags: package at Ψ̃ `by EFF.HE7.44`(c); every root at λ₂ `by EFF.HE7.41` (HE7-9(b)); the label `by EFF.HE7.35`; the lift `by EFF.HE7.12`; the residue cancellation `computation` (same value, same residue ⟹ strictly larger value); the new polygon `by EFF.HE7.44`(d) + `.41`; the peel branch `by EFF.HE7.44`(c) item (11) + `by EFF.HE7.37`.

**RESOLUTION TRACE:** Base lines 918–951 (r2 landed). Scope pinned and mixed case supplied at 1617–1727 (ANNEX F-1: the defect, the two riddered display sentences, ANNEX-LEMMA HE7-13′(a)–(e)). Note HE7-13′(a)'s own back-reference: at `k ≥ 2, ℓ₂ deg r = 1` the block's node is “LEMMA HE7-13's hypothesis EXACTLY (with the block's own μ₂ = L_C = k)”.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE7_passPE3_report.md:F-1` — grep-verified count **8**.

**TEETH:** `he7r2_supp.py` **B3** (42/42 strict increase + the HE7-9(b) count identity at the refined key) and **B4** (pre-refine residual is `(Z − s₂)²`, 42/42 — i.e. the hypothesis is verified, not assumed) · `he7annex_supp.py` **P5** (16/16 pure controls LOSE the λ₂ side “LEMMA HE7-13 as displayed”, while every mixed member RETAINS it — the mixed/pure boundary is machine-real).

---

### EFF.HE7.46  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 953–970 — the §S5.8 machine confirmation.

> “**Machine confirmation (additive leg `he7r2_supp.py`, §S11 [r2]).** On ALL
> 42 refine-path members of the sealed enumeration (re-generated
> member-for-member; the frozen artifact's refine histograms sum to 42):
> slot geometry — Ψ's occupied slots all at exactly T₂, w's slot-min exactly
> λ₂ > T₂ — 42/42; the off-disk inequality (S5.8.1) and invariance
> conclusion, in resultant-sum form on five off-disk strata covering all
> three offset cases (δ = ∞; δ > λ; δ ∈ (D′h, λ) — the (S5.2) [r2] middle
> band, ε₁ = 1/2; ε₀ = 1; δ = λ with wrong residue) — 210/210 ([r3]: the
> δ = ∞ INEQUALITY half is vacuous on 41 of the 42 — Φ′ | w at odd λ₂;
> invariance still checked on all — see §S11's [r3] disclosure); the strict
> slope increase (S5.8.2) with dv₂-resultants (pre-refine
> Σ_ρ dv₂(Ψ(ρ)) = 8λ₂ exactly, post-refine strictly greater) AND the
> LEMMA HE7-9(b) count identity Σ_ρ dv₂(Ψ^{(1)}(ρ)) = D″·Σ L·λ₂′ **at the
> refined key** — 42/42; 0 violations. Two concrete configurations (ℤ₃,
> s = 1, λ = 5/2, T₂ = 10, λ₂ = 11, s₂ = 1): Ψ's occupied slots
> {(s=0, 10), (s=2, 10)}, w's single slot (s=1, 11); member A:
> Σ dv₂(Ψ(ρ)) = 88 = 8·11 → Σ dv₂(Ψ^{(1)}(ρ)) = 92 = 4·(2·23/2), new slope
> 23/2 > 11; member B: 88 → 96 = 4·(2·12), new slope 12 > 11.”

**CONDITIONALITY:** **The 210/210 figure carries its own honesty disclosure, landed at r3 inside this very display and expanded at §S11 `[r3]`** (shard 2, lines 1475–1485): “Honest reading: "210/210" is 210 stratum passes, of which the δ = ∞ inequality instance was TESTED on 1; PE2's fresh leg re-verified this stratum non-vacuously (Res(Φ′, w) ≠ 0 on the majority of its 634 d_r = 2 members, all green).” Two further §S11 `[r3]` disclosures bear on this leg: (R-a) B3's peel-guard skip “never fired”; (R-b) B1's same-instrument coupling, decorrelated by PE2's independent instrument `he7_pe2_fresh.py` (634/634).

**DERIVATION:** Machine record, not a derivation. Its predicates are `.43` (B1), `.44`(a) (B2), `.45` (B3), and the pre-refine residual shape (B4).

**RESOLUTION TRACE:** Base lines 953–970 with the `[r3]` parenthetical landed; expanded at 1432–1451 (§S11 `[r2]` leg record) and 1473–1495 (§S11 `[r3]` disclosures), both shard 2.

**TEETH:** This unit IS a battery row: `he7r2_supp.py` B1–B5, 0 violations, 3.8 s, pins `he7_checks.py` 688adbe88447 / `he7_checks_results.json` f5bedab2ecda / `he6_checks.py` 321fa4d4990e / `he7r1_supp.py` 24ece42e4538.

---

### EFF.HE7.47  [definition]

**CANONICAL STATEMENT:** verbatim, lines 976–992 — **DEFINITION HE7-2 (level datum, and the level recursion)**.

> “**DEFINITION HE7-2 (level datum, and the level recursion).** A level-i
> datum is a tuple 𝔇_i = (Φ_i, D_i, w_i, ℓ_i, g_i, u_i, K_i, K_{i+1}, 𝒫_i)
> with Φ_i ∈ O[x] monic of degree D_i, w_i = c_i·v a positive rational
> multiple of v (integer-valued on the relevant elements), ℓ_i ≥ 1, g_i ≥ 1,
> u_i ∈ ℤ with gcd(u_i, ℓ_i) = 1, finite fields K_i ⊆ K_{i+1} with
> [K_{i+1} : K_i] = g_i, a set 𝒫_i ⊆ K̄₀ of level-i points, and
>
>     L_i := ℓ_i g_i ,   D_{i+1} := D_i L_i ,   w_{i+1} := ℓ_i·w_i ,
>     λ_i := u_i/ℓ_i ,   T_{i+1} := L_i·u_i ,   Φ_{i+1} := key of DEF HE7-3,
>     n_{i+1}(k) := n_i(m)·Φ_i^{s}  with ℓ_i m + s u_i = k, 0 ≤ s < ℓ_i,
>     𝒫_{i+1} := { ξ ∈ 𝒫_i : w_{i+1}(Φ_i(ξ)) = u_i, ι^{(i)}_ξ(r_i)(β_{i,ξ}) = 0 },
>
> subject to the **node condition λ_i > T_i** (for i ≥ 1) and r_i ∈ K_i[Z]
> monic irreducible of degree g_i. The level-0 datum is
> 𝔇_0 = (x, 1, v, e₁, f₁, h, F_Q, K, K̄₀) with T_0 := 0, and then D_1 = D′,
> w_1 = dv, T_1 = D′h, n_1 = ϖ-powers: **level 1 is HE6's frame, level 2 is
> §S1's.**”

**CONDITIONALITY:** **SUPERSEDED IN PART. The normalizer line and the base sentence are mutually incompatible and are REPLACED by ANNEX-DEF HE7-2′ (shard 3); everything else is unchanged.** The defect, quoted verbatim from ANNEX R R1.0 (lines 1992–2005):

> “DEFINITION HE7-2 displays the normalizer
> recursion `n_{i+1}(k) := n_i(m)·Φ_i^s (ℓ_i m + s u_i = k, 0 ≤ s < ℓ_i)`
> AND lists "n₁ = ϖ-powers" among the level-0 datum's outputs. The two are
> incompatible. At i = 0 the recursion (from any base n₀ — the level-0 datum
> declares none) gives n₁(k) = n₀(m)·x^{s(k)} with x-degree s(k) < e₁, while
> ϖ^k = x^{i₀k}π^{a₀k} has x-degree i₀k ≥ e₁ for k ≥ e₁ whenever i₀ ≥ 1 —
> equality is impossible regardless of n₀. Codex's witness: (e₁,h) = (2,3),
> k = 3, so i₀ = 1, a₀ = −1, ϖ = xπ^{−1}; the recursion's 2m + 3s = 3 with
> 0 ≤ s < 2 gives (m,s) = (0,1), hence n₁(3) = x, while ϖ³ = x³π^{−3}; the
> quotient ϖ³/n₁(3) = x²π^{−3} has dv = 0 and residue η_ξ ≠ 0 — generically
> ≠ 1 (the RIDER twist of §S4.1). So the recursive system and the claimed
> ϖ-power base are two DIFFERENT normalizer systems differing by a live
> twist, and §S6's "with the SAME proofs" had no coherent normalizer/cocycle
> convention: THEOREM HE7.D's proof was unproved as displayed. Because
> 𝒫_{i+1}'s defining letter β_{i,ξ} = res(Φ_i(ξ)^{ℓ_i}/n_i(u_i)(ξ)) is read
> THROUGH the normalizer system, the incoherence also left the level-(i+1)
> letters coordinate-ambiguous for i ≥ 2.”

**EFFECTIVE READING of the normalizer line and base sentence** (ANNEX-DEF HE7-2′, lines 2015–2019, homed in shard 3):

>     BASE (level 1):   n₁(k) := ϖ^k   (k ∈ ℤ),
>     RECURSION (i ≥ 1): n_{i+1}(k) := n_i(m_i(k))·Φ_i^{s_i(k)},
>                        ℓ_i·m_i(k) + s_i(k)·u_i = k,  0 ≤ s_i(k) < ℓ_i

with “The base is a DEFINITION, not a recursion output — this is the whole correction”, and “levels 1 and 2 are byte-unchanged”. **Scope of the defect, adjudicated: first live at level 3, i.e. n ≥ 16; the level-2 core does NOT consume DEFINITION HE7-2 (§S1 defines n₂ directly).**

**DERIVATION:** Definition. The one derived clause, `n_{i+1}`'s existence/uniqueness, is Bézout at `gcd(u_i, ℓ_i) = 1`.

**RESOLUTION TRACE:** Base lines 976–992. Defect at 1992–2011; replacement at 2013–2037; the attached objects (letter `Λ_i`, cocycle `τ_i`, transport tower) added at 2024–2032; coherence proved at 2039–2091 (ANNEX-LEMMA R1-a).

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F1` — count **4**.

**TEETH:** `he7rannex_supp.py` runs “the CORRECTED HE7-2′ chain — n₃(k) = n₂(m₂(k))·Ψ^{s₂(k)} with the τ₂-cocycle carried per R1-a”, 79/79 σ == PARI; tooth P3 flips 18/79 without the deep letter. **No tooth exercises the BROKEN display** — the defect was found by a decorrelated model, not by machine.

---

### EFF.HE7.48  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 994–1002 — **THEOREM HE7.D, the §S6 (operative) display.**

> “**THEOREM HE7.D.** At every level i ≥ 0 the following hold, with the proofs
> of §S3–S5 read through DEFINITION HE7-2:
> (SLOT_i) the slot-min at level i+1 is exact with nonzero residue in K_{i+1};
> (LIFT_i) surjectivity above bound_{i+1} = (L_i − 1)u_i + ℓ_i·bound_i
> (bound_0 = 0); the disk criterion; both evaluation displays; the block
> factor; the slope counts; nonemptiness; Galois equivariance; and the
> class-size theorem with
>
>     e = e₁·ℓ_1···ℓ_i·ℓ_{i+1} ,      f = f₁·g_1···g_i·g_{i+1} .”

**CONDITIONALITY:** **Carried the ratification CRITICAL; re-proved by ANNEX-COROLLARY R1-d at ANNEX GRADE.** Its clause “read through DEFINITION HE7-2” must be read through **ANNEX-DEF HE7-2′** (`.47`), and its (SLOT)/(LIFT) items are replaced by **ANNEX-THEOREM R1-b** / **ANNEX-THEOREM R1-c**, whose §S5 transfer is audited item-by-item at R1.2. R1-d's own honesty clause: “**No hole developed in the re-derivation** — the fold note's predicted repair (re-base + carry the cocycle through the τ mechanism) closed at every audited site; had any site failed, this corollary would instead be an OPEN box, per the honesty invariant.” **The bound recursion is explicitly unchanged** (`.23`). The §S2 display of the same theorem is `.17`, and the M-B rider attaches there.

**DERIVATION:** [ASSEMBLED — the inductive step, lines 1004–1048, verbatim]

> “*Proof (the inductive step).* Assume the package at levels ≤ i.
>
> **(SLOT).** §S3 verbatim: the ℓ_i classes of L_i = ℓ_ig_i slots separate
> because gcd(u_i, ℓ_i) = 1 (Step 2), the g_i within-class residues are
> K_i-independent because r_i is irreducible of degree g_i (Step 3), and the
> term values are exact by (SLOT_{i−1}) at level i (Step 1). Nothing else
> enters.
>
> **(LIFT).** §S4.2 verbatim, with LEMMA HE7-L1 replaced by (LIFT_{i−1}): the
> within-class heights are m₀ − t·u_i for t < g_i, and each needs a level-i
> full-residue height, giving bound_{i+1} = (L_i − 1)u_i + ℓ_i·bound_i.
>
> **(the disk criterion, both displays, the block factor, the slope counts,
> nonemptiness, Galois equivariance, the class-size theorem).** §S5.1, S5.4,
> S5.5, S5.6, S5.7 verbatim; each consumes only (SLOT), (LIFT), the ultrametric
> inequality, (RES_i) (a positive multiple of v), (★), the finite-field
> existence of irreducibles of every degree, Galois invariance of v, and
> completeness/integral-closedness of O — all level-independent.
>
> **(the ξ-side, §S5.3).** This is the only step whose inequality must be
> re-derived, and it closes by the following recursion. For arbitrary
> ξ ∈ K̄₀ set δ_j := w_j(Φ_j(ξ)), ε_j := (u_j − ℓ_jδ_j)^{+} and let Δ_j be the
> level-j deficit function, i.e. the largest loss in the level-j slot bound at
> ξ:
>
>     Δ_0 := 0 ,      Δ_{j+1} = (L_j − 1)·ε_j + ℓ_j·Δ_j                  (S6.1)
>
> (this is exactly (S5.3)'s two-term loss at j = 1, and the same estimate at
> every j: s ≤ L_j − 1 costs (L_j−1)ε_j, and each level-j coefficient loses at
> most Δ_j, scaled by ℓ_j when passing from w_j to w_{j+1}). Also, if ξ is not
> a level-(j+1) point then the disk criterion gives
> δ_{j+1} = T_{j+1} − L_j·ε_j when ε_j > 0 and δ_{j+1} ≤ T_{j+1} when ε_j = 0.
> Put ρ_j := ε_j − ℓ_j·Δ_j. Then, exactly as in §S5.3,
>
>     dv-excess of the t < d term over the t = d term
>         ≥ (κ_{i+1} − T_{i+1}) + ρ_i ,                                  (S6.2)
>
> and the recursion (S6.1) plus the node condition λ_j > T_j give
>
>     ρ_j ≥ ℓ_j·[ (λ_j − T_j) + ρ_{j−1} ] ,   ρ_0 = ε_0 ≥ 0 ,            (S6.3)
>
> hence ρ_j ≥ 0 for all j, with ρ_j > 0 as soon as some ε_{j'} > 0
> (j' ≤ j). Since κ_{i+1} > T_{i+1}, (S6.2) is strictly positive in every case,
> so the t = d term is the unique minimum and no root of the level-(i+1) test
> polynomial lies outside the level-(i+1) disk. ∎”

Justification tags: (SLOT) `by EFF.HE7.11` under `.07`'s substitution — **SUPERSEDED: this sentence is exactly what Codex F1 falsified at level ≥ 3; the operative argument is ANNEX-THEOREM R1-b**; (LIFT) `by EFF.HE7.12` — **likewise superseded by ANNEX-THEOREM R1-c**; the seven package items `by EFF.HE7.28`, `.34`, `.36`/`.37`, `.41`, `.42`, `.13` under `.40` ((RES_i)) and the classical list — **audited per R1.2 items 1–7**; the ξ-side recursion `by EFF.HE7.30`/`.31`/`.33` generalised, `computation`, and it is the one step R1.2 item 1 places in the twist-free class (“values, polygons, counts, degrees, bounds … never see residues at all: twist-free, §S6 verbatim”).

**RESOLUTION TRACE:** Base lines 994–1048. (SLOT)/(LIFT) sentences falsified at 2093–2099 and re-proved at 2101–2182; package audited at 2184–2235; theorem re-proved at 2237–2253. ANNEX R R1.1's preamble names the two sentences exactly: “These two replace §S6's "(SLOT). §S3 verbatim … Nothing else enters" and "(LIFT). §S4.2 verbatim" — the sentences F1 falsified at level ≥ 3 — by the actual arguments.”

XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-3` — count **15** (the (★) convex duality).

**TEETH:** `he7rannex_supp.py` — 79/79 at a fired level-3 node, with disclosure (ii): `g₂ = 1` throughout, so “the within-class deep twist ϑ_t (t ≥ 1) is structurally invisible at this family … the leg covers the τ-cocycle substance of F1, not every letter of R1-b”. **The induction at i ≥ 3 with g_i ≥ 2 remains machine-untouched.**

---

### EFF.HE7.49  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1050–1058 — `[r1]` item (i), the peel is level-generic.

> “**[r1] Both r1 items are level-generic, so the induction carries them.**
> (i) *The convention.* At level i the package is run on the block factor of
> the level-i label class, and it needs **Φ_{i+1} ∤ f_S^{(i)}** for the same
> reason (a root of the key has w_{i+1}(Φ_{i+1}(ρ)) = ∞ and no finite
> level-(i+1) label). LEMMA HE6R1-3's proof uses only: every root of the key is
> a level-(i+1) point, hence D_{i+1} | its local degree (the local forcing,
> LEMMA HE7-5 at level i); Galois stability + integral closedness of O; and
> disc ≠ 0 for simplicity. All three are in the level-i package, so the peel
> exists at every level, drops μ_{i+1} by 1, and fires at most once per level.”

**CONDITIONALITY:** Rests on the external LEMMA HE6R1-3 (its irreducibility half unproved here, `.38`). **The gcd step in its hypothesis chain is licensed only by ANNEX-LEMMA R2-a** (whose statement is explicitly stated for “any block factor f_C of ANNEX-LEMMA HE7-13′(a)”, i.e. at the same generality). R1.2 item 6 confirms the level-i transfer: “the peel and block lemmas consume values, degrees, Galois stability and vanishing predicates only (items 1, 4, 5)” — twist-blind.

**DERIVATION:** A transfer audit of LEMMA HE6R1-3's own inputs against the level-i package: local forcing `by EFF.HE7.29` at level i, Galois stability + integral closedness `by` the classical list, `disc ≠ 0` `by EFF.HE7.05`.

**RESOLUTION TRACE:** Base lines 1050–1058 (r1 landed). Licensed at 2348–2359 (R2-a); twist-audited at 2224–2227 (R1.2 item 6).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** No level-i tooth (proof-only above level 2). Level-2 instance: `he7r1_supp.py` 8/8.

---

### EFF.HE7.50  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1059–1069 — `[r1]` item (ii), the jump condition is level-generic, with its `[r2, HE7-PE1 F-4]` citation repair.

> “(ii) *The jump condition.* LEMMA HE6R1-1 is stated at every level: a node
> jumps iff its side carries a repeated irreducible r_i with
> **ℓ_i·deg r_i ≥ 2**, the α-refine case being ℓ_i = deg r_i = 1 (where
> **(LIFT_{i−1})** supplies the recentring constant because its residue lies
> in K_i — (LIFT_{i−1})'s residues lie in K_{(i−1)+1} = K_i by THEOREM
> HE7.D's indexing; **[r2, HE7-PE1 F-4]** the pre-r2 text wrote (LIFT_i),
> whose residues lie in K_{i+1}, an off-by-one in the citation only. The
> level-2 instance reads the same after the fix: the level-2 node's refine
> is i = 2, and (LIFT_{i−1}) = (LIFT_1) = (LIFT₂), with residues in K₂,
> exactly as THEOREM HE7.A(3) displays). Nothing in
> §S6's inductive step is sensitive to which of the two branches supplies
> ℓ_i·deg r_i ≥ 2.”

**CONDITIONALITY:** The `[r2]` repair is landed. **Note the indexing convention this clause fixes: `(LIFT_j)`'s residues lie in `K_{j+1}`, so the level-i α-refine needs `(LIFT_{i−1})`.** This is the same indexing ANNEX-THEOREM R1-c uses (“invoke (LIFT_{i−1}) at level-i height m_t”). Rests on the external LEMMA HE6R1-1 at every level, unproved here.

**DERIVATION:** The correction is an indexing computation: `(LIFT_{i−1})`'s residues lie in `K_{(i−1)+1} = K_i`, which is where the recentring constant must live; the level-2 instance is checked explicitly. `by EFF.HE7.48` (THEOREM HE7.D's indexing) + `computation`.

**RESOLUTION TRACE:** Base lines 1059–1069 (r1 + r2 landed); untouched. Re-used at 2224–2226 (R1.2 item 6: “the refine consumes (LIFT_{i−1})'s surjectivity onto K_i (R1-c, twist absorbed)”).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-1` — count **9**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-4` — grep-verified count **2**.

**TEETH:** No level-i tooth. Level-2 instance is `.14`'s.

---

### EFF.HE7.51  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1070–1078 — `[r1]` item (iii), the per-distinct-factor block split, and the level-i non-display fence.

> “(iii) *Several distinct repeated factors at one node.* Then
> the classification above is applied **per distinct factor**, each with its own
> block, by LEMMA HE6R1-2 — whose proof likewise consumes only items in the
> per-level package ((LIFT_i), the two evaluation displays, the slope counts,
> nonemptiness, and the level-i analogue of LEMMA HE6-4), so it transfers by the
> substitution table exactly like every other §S5 item. **The level-i
> restatements of HE6R1-1/2/3 are not separately displayed here**; they are
> transfers of the same kind §S6 already performs, and they inherit HE7-BOX-1's
> grade together with the three lemmas themselves.”

**CONDITIONALITY:** **This is ANNEX F-1's rider target 2.** Quoted verbatim from ANNEX F-1 (lines 1649–1656):

> “**§S6(iii)'s block sentence** ("*Several distinct repeated factors at
>    one node.* Then the classification above is applied **per distinct
>    factor**, each with its own block, by LEMMA HE6R1-2"). **Read as:**
>    "per distinct factor, REPEATED OR NOT — mixed nodes included";
>    ANNEX-LEMMA HE7-13′(a) is the displayed level-2 form of that block
>    split (proved from HE7-6/HE7-9/HE7-10/HE7-11, i.e. inside the §S5
>    package, so it transfers level-i by §S6's substitution table exactly
>    like every other §S5 item).”

The non-display fence (“The level-i restatements of HE6R1-1/2/3 are not separately displayed here”) is an explicit honesty declaration: the level-i forms of the three consumed reconciliation lemmas exist only as claimed transfers, and **they inherit HE7-BOX-1's grade** — which, at the acceptance chronology of `.01`, is now ACCEPTED 2/2 for the body and ANNEX-GRADE (unpassed) for the ANNEX R re-proof.

**DERIVATION:** A transfer audit of LEMMA HE6R1-2's inputs against the per-level package; `by EFF.HE7.07` (substitution table) + the named units. **Its inventory is the one ANNEX R R4 shows to be incomplete in the parallel sentence at HE7-12(c) item (7)** — R4 does not name §S6(iii), but the two sentences make the same claim about the same lemma, so the completed inventory (adding LEMMA HE6-4 and LEMMA HE6-2′ to clause (a), and (LIFT₂)/HE7-3/HE7-9(a)/HE7.A(1) to clause (b)) applies here too. **Recorded as OPEN-CALL 4** (whether R4's completion should be read onto §S6(iii)'s inventory as well).

**RESOLUTION TRACE:** Base lines 1070–1078 (r1 landed). Riddered at 1649–1656 (ANNEX F-1 target 2); the displayed level-2 form is ANNEX-LEMMA HE7-13′(a) at 1678–1694.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-4` — count **8**.

**TEETH:** `he7_pe3_probe12.py` (144/144, mixed nodes at μ₂ = 3) and `he7annex_supp.py` (96/96, two repeated classes at μ₂ = 4) — both are ANNEX F-1's legs, i.e. the machine evidence arrived with the rider, not with this sentence.

---

### EFF.HE7.52  [fence]

**CANONICAL STATEMENT:** verbatim, lines 1080–1081.

> “**Where the ladder's finiteness comes from.** Nothing above bounds i; §S7
> does.”

**CONDITIONALITY:** None. A negative claim about §S6: the induction is unbounded in i and supplies no termination. Load-bearing for the DAG — it says THEOREM HE7.D alone does not give a finite read.

**DERIVATION:** Declaration; discharged at `.15` and `.53`.

**RESOLUTION TRACE:** Base lines 1080–1081; untouched.

**TEETH:** NONE.

---

### EFF.HE7.53  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 1087–1098 — **LEMMA HE7-8 ((REF-TERM))**, the statement proper. (Its `[r2]` hypothesis-set box is `.54` and its `[r3]` mid-chain peel clause is `.55`; both are separate units because ANNEX F-1 riders the first by name and the charge names the second — boundary audit §6 items 17–18.)

> “**LEMMA HE7-8 ((REF-TERM) — α-refine chains are FINITE, characteristic-free).**
> Let 𝔇 be a level datum with key Ψ, μ₂ ≥ 2, and suppose the read performs an
> infinite chain of α-refines, i.e. keys Ψ^{(0)} = Ψ,
> Ψ^{(j+1)} = Ψ^{(j)} − w_j with dv₂(w_j) = λ₂^{(j)} and
> λ₂^{(0)} < λ₂^{(1)} < ⋯ **integers** (an α-refine happens only at ℓ₂ = 1,
> where the slope is an integer, so a strictly increasing chain of slopes
> tends to ∞), each step at a node whose polygon is the single side of length
> μ₂ with residual (Z − s_j)^{μ₂}. Then f_S is a perfect μ₂-th power in
> O[x] — contradicting disc f_S ≠ 0. Hence every α-refine chain is finite.
> **The argument needs no "binomial kill"** (GENHN-4/GENHN.A(iv)): the node
> condition dv₂(A_m^{(2,j)}) ≥ (μ₂−m)λ₂^{(j)} at each step, plus
> λ₂^{(j)} → ∞, is all that is used.”

**CONDITIONALITY:** Unconditional, on `disc f_S ≠ 0` (`.05`) and completeness of O. **The hypothesis set is PURE-NODE and single-`f_S`**; `.54` argues it is the read's actual configuration at pure nodes, `.55` handles interleaved peels, and ANNEX F-1's wiring bullet extends the argument to mixed nodes through the block route (“An infinite path therefore has an infinite all-refine tail on a fixed polynomial at pure single-side nodes with strictly increasing integer slopes — LEMMA HE7-8's hypothesis set, derived, and refuted by LEMMA HE7-8 as displayed”). The “no binomial kill” clause is a NON-IMPORT (`.04`(d)).

**DERIVATION:** [ASSEMBLED — lines 1117–1128, verbatim]

> “*Proof.* At the node of Ψ^{(j)} the polygon is the single side
> (0, μ₂λ₂^{(j)})–(μ₂, 0), so dv₂(A_m^{(2,j)}) ≥ (μ₂ − m)λ₂^{(j)} for every
> m < μ₂, and after recentering all these values strictly increase; since
> λ₂^{(j)} → ∞, dv₂(A_m^{(2,j)}) → ∞ for every m < μ₂. Now dv₂(A) → ∞ forces
> the Φ′-development coefficients of A, hence its O-coefficients, to converge
> π-adically to 0 (by (SLOT₂): dv₂(A) = min_s(ℓ dv(c_s) + su), so every
> dv(c_s) → ∞, so every v of every O-coefficient → ∞). The partial sums
> W_j := Σ_{j'≤j}w_{j'} therefore converge in the (complete) O-module of
> polynomials of degree < D″ to some W, and Ψ^{(j)} → Ψ − W coefficientwise.
> Passing to the limit in f_S = (Ψ^{(j)})^{μ₂} + Σ_{m<μ₂}A_m^{(2,j)}(Ψ^{(j)})^{m}
> gives f_S = (Ψ − W)^{μ₂} in O[x] (the A-terms vanish in the limit). With
> μ₂ ≥ 2 this makes disc f_S = 0. ∎”

Justification tags: the node inequality `definitional` (the single side's geometry); the coefficient convergence `by EFF.HE7.11` ((SLOT₂)'s slot-min formula); the limit `by` completeness of O (classical, `.03`); the contradiction `by EFF.HE7.05` (`disc f ≠ 0`).

**RESOLUTION TRACE:** Base lines 1087–1098 + 1117–1128; the `[r2]`/`[r3]` boxes at 1099–1115 (`.54`, `.55`). Extended to mixed nodes at 1828–1840 (ANNEX F-1's Termination bullet).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-4` — count **6**.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` — count **3**.

**TEETH:** Q1: the α-refine “fired on **42** members … and terminated in **one** step every time — (REF-TERM) in action, never approaching the bound” · PE2's fresh 634-member `ℓ = 1, d_r = 2` family “with the first 2-step refine chains” · `he7annex_supp.py` P4 (the tooth on the WRONG continuation: the naive single-key route CYCLES 48/48 at cap 24).

---

### EFF.HE7.54  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1099–1105 — LEMMA HE7-8's `[r2]` hypothesis-set box.

> “**[r2, HE7-PE1 F-1] The hypothesis set is the read's ACTUAL
> configuration, derived rather than presumed:** the polygon and residual
> of f_S at every iterate Ψ^{(j)} are well defined and read by the §S5
> package at the refined key — LEMMA HE7-12 (§S5.8) applies with
> W = w_0 + ⋯ + w_{j−1}, dv₂(W) > T₂ — and the strictly increasing slope
> clause λ₂^{(0)} < λ₂^{(1)} < ⋯ is LEMMA HE7-13, so an infinite chain of
> the read really has the properties this lemma refutes.”

**CONDITIONALITY:** **ANNEX F-1 explicitly re-reads this box** (line 1658–1662): “LEMMA HE7-8's [r2] box ("the hypothesis set is the read's ACTUAL configuration, derived") and LEMMA HE7-12(d)'s [r3] parenthetical (the pairwise-distinct dv₂(w_i)) inherit the same reading: through HE7-13′ their justifications route per block, where the displayed arguments apply verbatim”. Discharged there by the Termination bullet, which enumerates the four move-types (SPLIT / PEEL / REFINE / DECIDE-or-LEVEL-3) and shows an infinite path has an infinite all-refine tail at pure single-side nodes. **So the box holds at mixed nodes only THROUGH the block route, and the block route is annex-grade.**

**DERIVATION:** `by EFF.HE7.44` (LEMMA HE7-12 at `W = w_0 + ⋯ + w_{j−1}`) + `by EFF.HE7.45` (LEMMA HE7-13's strict increase).

**RESOLUTION TRACE:** Base lines 1099–1105 (r2 landed); re-read at 1658–1662 and discharged at 1828–1840 (ANNEX F-1).

XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-1` — grep-verified count **4**.

**TEETH:** `he7r2_supp.py` B3/B4 (the hypothesis is verified per member, not assumed: pre-refine residual `(Z − s₂)²` 42/42).

---

### EFF.HE7.55  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1106–1115 — LEMMA HE7-8's `[r3, HE7-PE2 F-2]` **mid-chain peel clause**.

> “**[r3, HE7-PE2 F-2] Peels interleaving the chain:** the sentence above
> fixes ONE (f_S, μ₂) along the whole chain, but a MID-chain peel (LEMMA
> HE6R1-3, routed inside LEMMA HE7-13) replaces f_S by f_S′ and drops μ₂
> by exactly 1 (§S5.5; §S6(i)'s display). Pigeonhole: μ₂ = 1 is decided,
> so at most μ₂ − 1 peels ever fire, and an infinite chain has an
> infinite constant-μ₂ tail on a fixed f_S^{(seg)} | f_S (separable, as
> f_S is) — to which the lemma's argument applies verbatim. At μ₂ = 2,
> every machine-certified degree, the corner is vacuous: a peel forces
> μ₂′ = 1 and ENDS the chain (the sealed record's 42 refine firings are
> all one-step, zero mid-chain peels).”

**CONDITIONALITY:** Landed at r3; **untouched by ANNEX F-1 and ANNEX R**, and inherited by ANNEX F-1's Termination bullet, which folds PEEL into the four move-types with the same pigeonhole (“PEEL (degree drops by D″; at most μ₂ − 1 ever fire, the [r3] pigeonhole at LEMMA HE7-8)”). **Machine-vacuous at every certified degree** (μ₂ = 2, zero mid-chain peels observed).

**DERIVATION:** Pigeonhole, displayed: each peel drops μ₂ by exactly 1 (`by EFF.HE7.37`/`.38` and `.49`), μ₂ = 1 is decided, hence at most μ₂ − 1 peels; an infinite chain therefore has an infinite constant-μ₂ tail on a fixed separable `f_S^{(seg)} | f_S`, and `.53`'s argument applies to that tail verbatim.

**RESOLUTION TRACE:** Base lines 1106–1115 (r3 landed); folded into the mixed-node termination at 1828–1840.

XREF: `lean/notes/openmath/HE7_passPE2_report.md:F-2` — grep-verified count **7**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** The sealed record's 42 refine firings, all one-step, **zero mid-chain peels** — i.e. the clause is machine-unexercised, and the note says so.

---

### EFF.HE7.56  [fence]

**CANONICAL STATEMENT:** verbatim, lines 1130–1134.

> “*(Note that this argument is uniform in the characteristic — it does not use
> 2 ∈ O^×, so it covers the equal-characteristic-2 Artin–Schreier corner where
> the naive "disc = A₁² − 4A₀ is refine-invariant" bound degenerates. That
> corner is the one W-12's r4 repair identified as the program's standard trap;
> it is handled here by completeness rather than by the discriminant.)*”

**CONDITIONALITY:** None. A method fence: the termination argument routes through completeness of O, not through the discriminant, and therefore survives characteristic 2.

**DERIVATION:** Read off `.53`'s proof, which uses only the node inequality, `λ₂^{(j)} → ∞`, completeness, and `disc f_S ≠ 0` as a *conclusion-side* contradiction (not as an invariant).

**RESOLUTION TRACE:** Base lines 1130–1134; untouched.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:r4` — grep-verified count **59** (a bare-round designation; the specific “r4 repair” claim is carried descriptively — see source defect 5 in §8).

**TEETH:** The battery's char-p rows (`F_3[[t]]`, `F_5[[t]]`) exercise equal characteristic, though not characteristic 2; **`p = 2` is exercised nowhere** in HE7's rows (`q ∈ {3,5,7}` char 0, `q ∈ {3,5}` char p). Recorded as OPEN-CALL 5.

---

### EFF.HE7.57  [instance-record]

**CANONICAL STATEMENT:** verbatim, lines 1174–1179 — the n = 8 frame.

> “At HE6-BOX-1's first bite — D′ = 2, (e₁,f₁,h) = (2,1,1), Φ′ = x²−π, μ = 4,
> deg f = 8, λ = u/2 with u odd, R_λ = (Z−s)², so ℓ = 2, d_r = 1, m = 2,
> D″ = 4, K₂ = K = F_q, T₂ = 2u — the block is everything (|S| = D′L_λ = 8), so
> f_S = f and μ₂ = 2. THEOREM HE7.C says no level 3 is reachable. THEOREM
> HE7.A therefore decides σ, and the possible level-2 configurations at μ₂ = 2
> are exhaustively:”

**CONDITIONALITY:** Unconditional at this frame. **“the block is everything” is what makes `.39`'s proper-block machinery unnecessary here** — the proper-block configuration is first live at μ ≥ 5, n ≥ 10. `K₂ = K = F_q` (`d_r = 1`) is exactly why the `d_r ≥ 2` coverage hole of HE7-BOX-2 exists.

**DERIVATION:** Instantiation of `.06` at `(e₁,f₁,h) = (2,1,1)`, `ℓ = 2`, `d_r = 1`; `|S| = D′L_λ = 8` `by EFF.HE7.41` (`n_λ = D′L_λ`) with `L_λ = ℓ·deg R_λ = 2·2 = 4`; no level 3 `by EFF.HE7.15`.

**RESOLUTION TRACE:** Base lines 1174–1179; untouched. ANNEX F-1's closing list confirms: “the n = 8 closure §S8 (μ₂ = 2, all nodes pure — the dictionary is untouched)”.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-1` — count **9**.

**TEETH:** The whole §S10 battery runs at exactly this frame (`(e₁,f₁,h) = (2,1,1)`, `Φ′ = x²−π`, `μ = 4`, `deg f = 8`, ALPHA2).

---

### EFF.HE7.58  [table]

**CANONICAL STATEMENT:** `[TABLE]` — verbatim source display, lines 1181–1188, then its markdown transcription (template rule 5: tables are transcribed as tables, never prosified).

Source display, verbatim:

>     level-2 polygon                        (ℓ₂, d_{r₂})   e = 4ℓ₂ , f = d_{r₂}   σ
>     ---------------------------------------------------------------------------------
>     one side, length 2, λ₂ ∉ ℤ             (2, 1)         (8, 1)                 {(8,1)}
>     one side, length 2, λ₂ ∈ ℤ, R₂ inert   (1, 2)         (4, 2)                 {(4,2)}
>     one side, length 2, λ₂ ∈ ℤ, R₂ split   (1, 1)×2       (4,1),(4,1)            {(4,1),(4,1)}
>     two sides of length 1                  (1, 1)×2       (4,1),(4,1)            {(4,1),(4,1)}
>     one side, λ₂ ∈ ℤ, R₂ = (Z−s₂)²         α-refine (LEMMAS HE7-12/13 + HE7-8 [r2]) → one of the above
>     [r1] Ψ | f (A₀^{(2)} = 0, no j = 0 pin) PEEL (LEMMA HE6R1-3): (4,1) ⊔ (4,1) {(4,1),(4,1)}

`[TABLE]` transcription:

| # | level-2 polygon | (ℓ₂, d_{r₂}) | e = 4ℓ₂ , f = d_{r₂} | σ |
|---|---|---|---|---|
| 1 | one side, length 2, λ₂ ∉ ℤ | (2, 1) | (8, 1) | {(8,1)} |
| 2 | one side, length 2, λ₂ ∈ ℤ, R₂ inert | (1, 2) | (4, 2) | {(4,2)} |
| 3 | one side, length 2, λ₂ ∈ ℤ, R₂ split | (1, 1)×2 | (4,1),(4,1) | {(4,1),(4,1)} |
| 4 | two sides of length 1 | (1, 1)×2 | (4,1),(4,1) | {(4,1),(4,1)} |
| 5 | one side, λ₂ ∈ ℤ, R₂ = (Z−s₂)² | α-refine (LEMMAS HE7-12/13 + HE7-8 [r2]) → one of the above | — | — |
| 6 | **[r1]** Ψ \| f (A₀^{(2)} = 0, no j = 0 pin) | PEEL (LEMMA HE6R1-3): (4,1) ⊔ (4,1) | — | {(4,1),(4,1)} |

**CONDITIONALITY:** Unconditional at μ₂ = 2. Row 5's “→ one of the above” is upgraded from a pointer to displayed mathematics at `.59`; row 6 is the `[r1]` peel row explained at `.60`. **The exhaustiveness claim holds only WITH row 6** — that is `.60`'s whole point. **Untouched by ANNEX F-1** (“the n = 8 closure §S8 (μ₂ = 2, all nodes pure — the dictionary is untouched)”) and by ANNEX R.

**DERIVATION:** Case enumeration of the μ₂ = 2 polygon: one side of length 2 (with λ₂ ∉ ℤ forcing ℓ₂ = 2; with λ₂ ∈ ℤ the residual is a quadratic, inert or split or a square) or two sides of length 1 — `by EFF.HE7.13` clause (1) (Σ L = μ₂ = 2); letters `by EFF.HE7.13` clause (2) (`e = e₁ℓℓ₂ = 4ℓ₂`, `f = f₁d_r deg r₂ = deg r₂`); row 5 `by EFF.HE7.14`; row 6 `by EFF.HE7.09`/`.38`.

**RESOLUTION TRACE:** Base lines 1181–1188 (r1 row added, r2 row-5 upgrade at 1190–1197); untouched thereafter.

**TEETH:** Q1: all three σ values occur on every row of the battery, “exactly the three outputs of THEOREM HE7.A's μ₂ = 2 dictionary (§S8), and no fourth value ever appears”, 1,335/1,335 PARI · `he7r1_supp.py` decides the 8 members of dictionary row 6.

---

### EFF.HE7.59  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1190–1197 — the `[r2]` upgrade of dictionary row 5.

> “**[r2, HE7-PE1 F-1] The fifth row's "→ one of the above" is now displayed
> mathematics, not a pointer:** after the refine the four polygon rows (and,
> if Ψ^{(1)} | f, the sixth row's peel) are read AT THE REFINED KEY, which
> LEMMA HE7-12 (§S5.8) licenses — the §S5 package and THEOREM HE7.A(1)(2)
> hold verbatim at Ψ − w since dv₂(w) = λ₂ > T₂ — and the re-read lands at a
> strictly larger slope by LEMMA HE7-13, so the loop terminates (LEMMA
> HE7-8). The sealed battery takes this path on 42 members (all decided,
> §S11 [r2]).”

**CONDITIONALITY:** At μ₂ = 2 all nodes are pure, so `.45`'s pure-node hypothesis is met and ANNEX F-1's mixed-node rider is vacuous here (“mixed nodes need μ₂ ≥ 3”). **Note the phrase “the fifth row” denotes the α-refine row here and the PEEL row at `.60`** — the same phrase, two different rows. Recorded as source defect 6 in §8.

**DERIVATION:** `by EFF.HE7.44` (the package at Ψ − w) + `by EFF.HE7.13` (clauses (1)(2) at the refined key) + `by EFF.HE7.45` (strictly larger slope) + `by EFF.HE7.53` (termination).

**RESOLUTION TRACE:** Base lines 1190–1197 (r2 landed); untouched.

XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-1` — grep-verified count **4**.

**TEETH:** 42 refine-path members, all decided (§S11 `[r2]`); `he7r2_supp.py` B1–B5.

---

### EFF.HE7.60  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1199–1215 — the `[r1]` peel row.

> “**[r1] THE FIFTH ROW (FINDING HE6R1-F2) — why the exhaustive claim needed it,
> and why the alphabet does not change.** The four polygon rows above all presume
> a finite j = 0 pin, i.e. Ψ ∤ f; the stratum Ψ | f is a fifth case, and it is
> NOT empty at n = 8 (HE7's own sealed battery isolates 8 of 1,587 members there
> as status `DEGENERATE-key-divides`). It is decided by the peel: LEMMA HE6R1-3
> gives Ψ irreducible over O of degree D″ = 4 with
> (e, f) = (e₁ℓ, f₁d_r) = (4, 1), a simple factor, so f = Ψ·f′ with Ψ ∤ f′,
> deg f′ = 4 = D″ and μ₂′ = 1 — and at μ₂′ = 1 every root of f′ is a level-2
> point, so D″ = 4 divides its local degree (LEMMA HE6-0′), forcing f′
> irreducible with (e, f) = (e₁ℓℓ₂, f₁d_r·deg r₂) = (4, 1). Hence
> **σ = {(4,1), (4,1)}**, already the third letter of the table: the three-σ
> alphabet and the "no fourth value possible" claim survive verbatim. Machine
> confirmation in this very frame (additive post-seal leg `he7r1_supp.py`, §S11
> [r1]): 8/8 peels exact with A₁^{(2)} ≠ 0 (one peel only), 8/8 peeled reads
> σ(f′) = {(4,1)}, and PARI `factorpadic` agrees on both halves —
> **2/2 on σ(f) = {(4,1),(4,1)} and 2/2 on σ(Ψ) = {(4,1)}**, the latter a direct
> oracle test of the peel's irreducibility-and-letter claim.”

**CONDITIONALITY:** Rests on the external **LEMMA HE6R1-3**; its irreducibility half is evidenced only by the `σ(Ψ)` oracle test (§S11 `[r1]` A5: “which no textual argument of this note supplies”). The peel-at-most-once claim is `A₁^{(2)} ≠ 0`, machine-checked 8/8, not proved textually at this frame.

**DERIVATION:** `by XREF LEMMA HE6R1-3` (Ψ irreducible, degree D″, `(e,f) = (e₁ℓ, f₁d_r)`, simple); then `deg f′ = 4 = D″` and `μ₂′ = 1`; then `by XREF LEMMA HE6-0′` (`D″ | [L_ρ:K₀]`) forces `f′` irreducible with `(e,f) = (4,1)` — `computation` inside a degree-4 polynomial.

**RESOLUTION TRACE:** Base lines 1199–1215 (r1 landed); untouched. Machine record at 1415–1430 (§S11 `[r1]`).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0′` — count **5**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — count **4**.

**TEETH:** `he7r1_supp.py` A1–A5 (8/8, 8/8, 8/8, 2/2, 2/2), 0 violations, 3.3 s.

---

### EFF.HE7.61  [fence]

**CANONICAL STATEMENT:** verbatim, lines 1217–1222.

> “**These three σ are exactly the three values HE6's tooth HE6-T-CASEB
> observed** on members with identical outer data — {(8,1)}, {(4,2)},
> {(4,1),(4,1)} — with no fourth value possible. So the level-2 read is not
> merely *a* deeper read: it is the read whose output alphabet is precisely the
> observed σ-alphabet of the undecided family, and P1 of the battery tests
> that it picks the right letter **member by member against PARI**.”

**CONDITIONALITY:** None. This is the note's own claim that the dictionary's output alphabet MATCHES an independently observed alphabet — a decorrelation claim against HE6's sealed tooth, not against HE7's own reader.

**DERIVATION:** Comparison of `.58`'s σ column with HE6's HE6-T-CASEB observations; “no fourth value possible” is `by EFF.HE7.58` (the enumeration is exhaustive given row 6).

**RESOLUTION TRACE:** Base lines 1217–1222; untouched.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-T-CASEB` — count **4**.

**TEETH:** HE6's HE6-T-CASEB (foreign-note tooth consumed as evidence) · HE7's own HE7-T-CASEB-SEP: “three distinct PARI σ inside ONE family of identical outer data, and the level-2 read predicts all 8/8”.

---

### EFF.HE7.62  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 1224–1231 — **THEOREM HE7.A′ [r1]**.

> “**THEOREM HE7.A′ [r1] (the bite, unconditionally).** At every member of the
> n = 8 box configuration with disc f ≠ 0, σ(f) is decided by the level-2
> read of §S1–S5 — **after one peel (LEMMA HE6R1-3) on the Ψ | f stratum** —
> with the five-row dictionary above; the argument uses no base
> change, no irreducibility of Ψ **as a hypothesis** (on the peel stratum
> irreducibility of Ψ is a CONCLUSION, not an assumption), and no order-≥2
> citation. In particular HE6-BOX-1's machine-certified live configurations
> are all decided, the peel stratum included.”

**CONDITIONALITY:** **“unconditionally” is scoped to the n = 8 box configuration**, and the peel leg rests on the external LEMMA HE6R1-3. **Untouched by all five ratification findings** (named in ANNEX R BOX-1's untouched list) and by ANNEX F-1. Note the display says “the five-row dictionary above” while `.58` has SIX rows — the same off-by-one as `.59`/`.60`'s “fifth row” (source defect 6, §8).

**DERIVATION:** Composition: `.57` (the frame) + `.58` (the exhaustive dictionary) + `.13`+`.15` (the σ-decision) + `.60` (the peel row).

**RESOLUTION TRACE:** Base lines 1224–1231 (r1 landed); untouched.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-1` — count **9**.

**TEETH:** Q1 (1,335/1,335) + `he7r1_supp.py` (8/8 + 2/2 + 2/2) — jointly “1,587/1,587 members decided, 1,337 PARI σ(f) jobs … with 0 mis-decisions”.

---

### EFF.HE7.63  [fence]

**CANONICAL STATEMENT:** verbatim, lines 1233–1243.

> “**Relation to GENHN.C.** At μ₂ = 2 the level-2 read is a quadratic resolvent
> read, so THEOREM HE7.A′ can equivalently be obtained by re-running GENHN.C's
> §S7 trichotomy one level up. Every input GENHN.C's proof consumes is supplied
> here at level 2: (T1)/(T2) at level 2 = the level-2 point condition +
> LEMMA HE7-5; exact dv of the resolvent coefficients = (SLOT₂); the norm count
> = (RES₂) + LEMMA HE7-9; the one refine step of stage-SPLITEQ = the level-2
> α-refine (LEMMA HE7-8, available by (LIFT₂)). We do not *cite* GENHN.C at
> level 2 — its statement is about a stage over a DVR, and Ψ is not known
> irreducible — we re-derive the same five cases from THEOREM HE7.A. The
> agreement of the two routes is an internal decorrelation, exactly as HE6
> §S6.4 was for μ ≤ 3.”

**CONDITIONALITY:** None. **This is simultaneously a NON-IMPORT fence** (“We do not *cite* GENHN.C at level 2”) **and a decorrelation claim.** It is the sentence §S0's third bullet anticipates: “GENHN.C's §S7 case analysis is consumed **as an argument template only**, and only at §S8”.

**DERIVATION:** An input-by-input audit of GENHN.C's consumption list against the level-2 package: `by EFF.HE7.29` ((T1)/(T2) at level 2), `by EFF.HE7.11` (exact dv), `by EFF.HE7.40`+`.41` (the norm count), `by EFF.HE7.53`+`.12` (the refine step).

**RESOLUTION TRACE:** Base lines 1233–1243; untouched.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.C` — count **19**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S6.4` — count **1**.

**TEETH:** The two-route agreement is itself an internal decorrelation, not a machine tooth; the machine decorrelation is PARI (Q1).

---

### EFF.HE7.64  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1249–1255 — the note's own supply list.

> “**What is proved here, with no residue.** (SLOT₂) §S3; (LIFT₂) §S4 (and the
> corrected level-1 (LIFT), LEMMA HE7-L1); the level-2 transfer of every HE6
> §S3–S6 lemma §S5, including the one new estimate §S5.3 and the block-factor
> reduction §S5.5; **[r2] the refined-key package and the derived strict
> slope increase §S5.8 (LEMMAS HE7-12/HE7-13 — PE1 FINDING F-1's gap,
> closed)**; the level-i package by induction §S6; (REF-TERM) §S7;
> TERMINATION §S7; the n = 8 closure §S8.”

**CONDITIONALITY:** **“with no residue” is scoped by the five boxes that immediately follow** (`.67`–`.75`) and by the two under-count records (`.65`, `.66`). Two items on the list acquired conditionality after this sentence was written: “the level-i package by induction §S6” carried the ratification CRITICAL and is discharged only at ANNEX-COROLLARY R1-d, at annex grade (shard 3); and “(REF-TERM) §S7” needs ANNEX F-1's block route at mixed nodes (`.97`). Every other item is untouched by all five ratification findings.

**DERIVATION:** Inventory, not derivation. Each item's proof is the shard-1 unit named: (SLOT₂) `EFF.HE7.11`; (LIFT₂) `.12`; LEMMA HE7-L1 `.19`; §S5's transfer `.28`–`.42`; §S5.3 `.30`; §S5.5 `.36`–`.39`; §S5.8 `.43`–`.46`; §S6 `.47`–`.52`; §S7 `.53`–`.56`; §S8 `.57`–`.63`.

**RESOLUTION TRACE:** Base lines 1249–1255 (with the `[r2]` clause landed). Item “§S6” annotated at 2442–2462 and re-proved at 2237–2253 (shard 3); item “§S7” extended at 1828–1840 (`.34`).

**TEETH:** The whole §S10/§S11 battery is this list's evidence at n = 8; `.29` is the note's own statement of exactly what the machine leg does and does not establish.

---

### EFF.HE7.65  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1257–1265 — the base under-count record.

> “**What HE6 §S7.2 got right, and one thing it under-counted.** Right: the two
> named lemmas are exactly the missing inputs for the *slot algebra*, and the
> substitution table is exact. Under-counted: three items beyond (LIFT₂) and
> (SLOT₂) are needed and were not named — (a) the ξ-side Step-1 inequality
> needs a genuinely new two-offset estimate (§S5.3); (b) the general case needs
> the block-factor reduction (§S5.5) to avoid principal-part bookkeeping — and
> this is the step whose absence was HE3-BOX-6's original defect; (c) the
> recursion needs the α-refine termination (§S7), which HE6 did not mention.
> All three are proved here, so the residue is closed, not moved.”

**CONDITIONALITY:** **“three items” is itself under-counted** — `.66` adds two more at `[r1]`, and §S5.8's `[r2]` addition (LEMMAS HE7-12/HE7-13) is a sixth item that is neither a verbatim transfer nor a short new argument. **This is the sentence that falsifies shard 1's `.89`** (“Exactly one item is in the third class”). The closing claim “the residue is closed, not moved” holds at n ≤ 15 and, for the level-i package, only at annex grade.

**DERIVATION:** An audit of HE6 §S7.2's named residue against what §S3–S8 actually needed; each of (a)/(b)/(c) is discharged at the named section.

**RESOLUTION TRACE:** Base lines 1257–1265; extended at 1266–1273 (`[r1]`, `.66`) and, in substance, by §S5.8 at 798–971 (shard 1).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:S7.2` — grep-verified count **5**.
XREF: `lean/notes/openmath/HE3_PROOF_2026-08-08.md:HE3-BOX-6` — grep-verified count **12**.

**TEETH:** NONE (an audit record).

---

### EFF.HE7.66  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1266–1273 — the `[r1]` extension of the under-count.

> “**[r1] TWO MORE ITEMS this note itself under-counted, both supplied by the
> reconciliation and neither open mathematics:** (d) the block-factor reduction
> (§S5.5) does not by itself pin μ₂ when the block is PROPER — **LEMMA HE6R1-2**
> does, in read form off f (which also supersedes HE7-BOX-4's declined count);
> (e) the reduction to f_S needs **Ψ ∤ f_S**, absent here and supplied by the
> §S1 CONVENTION [r1] with **LEMMA HE6R1-3**'s peel (FINDING HE6R1-F2). Both were
> found by composing this note against HE6 r1, i.e. by the reconciliation, not by
> a reading of this note alone.”

**CONDITIONALITY:** “neither open mathematics” is true only because both are supplied by EXTERNAL lemmas HE7 consumes without reproving. (d)'s supplier (LEMMA HE6R1-2) is proof-only and machine-unexercised (`.70`/`.71`); (e)'s supplier (LEMMA HE6R1-3) has its irreducibility half evidenced only by the `σ(Ψ)` oracle test (`.83`). **Additionally, (e)'s equivalence chain was underived at a reducible key until ANNEX-LEMMA R2-a** (shard 3). The closing methodological sentence — “found by composing this note against HE6 r1 … not by a reading of this note alone” — is the note's own account of why single-note review missed them.

**DERIVATION:** Record, not derivation; the two supplies are cited.

**RESOLUTION TRACE:** Base lines 1266–1273 (r1 landed); (e)'s chain licensed at 2348–2387 (shard 3).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — count **4**.

**TEETH:** (e): `he7r1_supp.py` A1–A5. (d): **NONE — proof-only** (`.70`'s `[r1]` list names it).

---

### EFF.HE7.67  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1275–1284 — **HE7-BOX-1 (arc grade) [r1]**, the base box.

> “**HE7-BOX-1 (arc grade) [r1].** Attempt grade **0/2** — no hostile pass has
> run on this note, and the r1 round does not upgrade it (a repair round never
> does): the r1 text — the widened HE7.A(3)/HE7.C, the Ψ ∤ f_S convention, the
> §S4.3 use-site display and §S8's fifth row — owes a fresh hostile pass, as do
> the three consumed reconciliation lemmas (HE6R1-1/2/3), which have never been
> attacked. Every consequence inherits the minimum over its suppliers
> {GENHN 0/2 post-r1 erratum (battery GREEN), HE6 0/2 post-r1 (battery GREEN),
> HE6R1 0/2 (battery GREEN), HE3 1/2 at μ ≤ 3, GENIND 0/2, W-12 0/2,
> classical}. COROLLARY HE7.B is therefore a
> **composition claim at 0/2**, not an acceptance.”

**CONDITIONALITY:** **The grade is superseded four times**, each by a dated continuation of THIS box: `.68` (`[r2]`, PE1 ran, stays 0/2), `.69` (`[r3]`, PE2 CLEAN, 0/2 → 1/2), `.103` (ANNEX F-1's append, PE3 CLEAN, 1/2 → **2/2, ACCEPTED**), and ANNEX R's append (shard 3: ratification CHALLENGE, acceptance **ANNOTATED not revoked**), closed by the final dated line (annex stack ACCEPTED 2/2, CHALLENGE discharged, note FULLY FROZEN). **The SUPPLIER-MINIMUM clause is NOT superseded and is the box's durable content**: HE7's consequences still inherit the minimum over GENHN/HE6/HE6R1/HE3/GENIND/W-12, and the note gives no updated supplier-grade table. Whether the supplier minima have since moved is outside HE7's own text — recorded as OPEN-CALL 1.

**DERIVATION:** Grade record; the minimum-over-suppliers rule is the campaign's standing convention, applied here.

**RESOLUTION TRACE:** Base lines 1275–1284 (r1 landed); continued at 1285–1293, 1294–1304, 1948–1959, 2442–2462, 2493–2497.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-1` — count **9**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND.B` — count **19**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:W-12` — grep-verified count **100** (a note-wide tag, not an addressable statement; the addressable consumer designation is `W-12.D`, count **19**).

**TEETH:** The arc itself is the tooth of record; per-pass batteries are inventoried in §5.

---

### EFF.HE7.68  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1285–1293 — HE7-BOX-1's `[r2]` continuation.

> “**[r2] PE1 HAS NOW RUN (report `HE7_passPE1_report.md`): 0 CRITICAL,
> 1 GAP (F-1, the refined-key read), 3 MINOR (F-2/F-3/F-4), machine leg
> bit-identical GREEN + a fresh n = 12 peel family 2,552/2,552.** This r2
> round repairs all four findings (F-1 by LEMMAS HE7-12/HE7-13, §S5.8,
> wired at HE7.A(3), LEMMA HE7-8 and §S8 row 5; F-2/F-3/F-4 at their
> displays) and adds the additive leg `he7r2_supp.py` (§S11 [r2]). A repair
> round never upgrades the grade: **attempt grade stays 0/2**, and the
> 2-clean count starts only at the next fresh hostile pass (PE2) on the
> post-r2 text.”

**CONDITIONALITY:** Grade superseded onward (`.69`, `.103`). **F-1's repair (LEMMAS HE7-12/HE7-13) is itself later found incomplete at mixed nodes** — PE3's F-1 (`.94`) is a defect in exactly the wiring this round installed. So the `[r2]` sentence “repairs all four findings” is true at pure nodes and incomplete at mixed nodes, which is ANNEX F-1's whole subject.

**DERIVATION:** Round record. The four repairs are at `EFF.HE7.43`–`.46` (F-1), `.31` (F-2), `.14`/`.16` (F-3, the ⌊·⌋ floor), `.50` (F-4, the off-by-one).

**RESOLUTION TRACE:** Base lines 1285–1293 (r2 landed); F-1's repair re-scoped at 1617–1662 (ANNEX F-1).

XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-1` — grep-verified count **4**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-2` — count **2**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-3` — grep-verified count **2**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-4` — count **2**.

**TEETH:** PE1's own legs: “machine leg bit-identical GREEN + a fresh n = 12 peel family **2,552/2,552**” (a foreign-arc regression on a fresh instrument) · the r2 additive leg `he7r2_supp.py` (`.21`).

---

### EFF.HE7.69  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1294–1304 — HE7-BOX-1's `[r3]` continuation.

> “**[r3] PE2 HAS NOW RUN (report `HE7_passPE2_report.md`): CLEAN — 0
> CRITICAL, 0 GAP, 3 MINOR + 2 remarks; machine leg bit-identical GREEN,
> plus a fresh 634-member ℓ = 1, d_r = 2 (K₂ = F_{p²}) α-refine family,
> σ == PARI 634/634, with the first 2-step refine chains — so the 2-clean
> count STARTS: attempt grade 0/2 → 1/2.** This r3 round applies the
> three MINORs (F-1 at LEMMA HE7-12(d); F-2 at LEMMA HE7-8's [r2] box;
> F-3 plus remarks R-a/R-b as §S11 [r3] disclosures) — display and
> disclosure scale only, no statement or frozen number moved — so per the
> minors-only precedent (HMENU3-ANNEX-A; ledger fold b3c05be) the count
> **HOLDS at 1/2**; acceptance (2/2) needs one more fresh hostile pass
> (PE3) on the post-r3 text.”

**CONDITIONALITY:** Grade superseded at `.103` (PE3 CLEAN → 2/2). **The minors-only precedent is a PROTOCOL citation, not mathematics**: it licenses holding the counter at 1/2 across a display-only repair round. Its two pins are verified: `HMENU3_PROOF_2026-08-08.md:ANNEX A` count **5** (HE7's shorthand `HMENU3-ANNEX-A` has count **0** there — source defect 1), and `b3c05be` resolves to a real commit.

**DERIVATION:** Round record. The three repairs are at `EFF.HE7.44`(d) (F-1), `.54`/`.55` (F-2), `.23` here (F-3 + R-a/R-b as disclosures).

**RESOLUTION TRACE:** Base lines 1294–1304 (r3 landed); superseded in grade at 1948–1959.

XREF: `lean/notes/openmath/HE7_passPE2_report.md:F-1` — grep-verified count **5**.
XREF: `lean/notes/openmath/HE7_passPE2_report.md:F-2` — count **7**.
XREF: `lean/notes/openmath/HE7_passPE2_report.md:R-a` — grep-verified count **2**.
XREF: `lean/notes/openmath/HE7_passPE2_report.md:R-b` — grep-verified count **1**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:ANNEX A` — grep-verified count **5** (the referent of HE7's `HMENU3-ANNEX-A`; see source defect 1).

**TEETH:** PE2's fresh 634-member `ℓ = 1, d_r = 2` family, σ == PARI **634/634**, on an independent instrument (`he7_pe2_fresh.py`, “no he6/he7 import”) with the **first 2-step refine chains** — the strongest decorrelation in the HE7 stack.

---

### EFF.HE7.70  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1305–1313 — **HE7-BOX-2 (machine coverage)**.

> “**HE7-BOX-2 (machine coverage).** The battery exercises D′ = 2,
> (e₁,f₁) = (2,1), h = 1, μ = 4, d_r = 1 (so K₂ = K = F_p), λ ∈ {5/2, 7/2},
> q ∈ {3,5,7} in char 0 and q ∈ {3,5} in char p. NOT exercised by machine:
> d_r ≥ 2 (K₂ a proper extension — the twist and the within-class basis then
> have length ≥ 2), f₁ ≥ 2 stage genres, μ ≥ 5, level 3 (unreachable below
> n = 16 by THEOREM HE7.C, hence not exercisable at these degrees), and
> embedded genres. The proofs are uniform in all of these; the (LIFT₂)
> threshold leg (P3) *is* run in frames with f₁ ≥ 2 and d_r ≥ 2 precisely
> because the σ rows cannot reach them.”

**CONDITIONALITY:** **The NOT-exercised list is superseded twice.** `.71` (`[r1]`) discharges `d_r ≥ 2` via HE6R1's sibling battery and level-2 residue direction; and — out of range — ANNEX R R1.3's `he7rannex_supp.py` discharges **level 3** (79/79, “the first machine σ at a fired level-3 node anywhere in the program”). **What remains unexercised at HEAD:** `d_r ≥ 3`, `f₁ ≥ 2` stage genres, `μ ≥ 5` (hence PROPER blocks), embedded genres, `g₂ ≥ 2` at level 3 (ANNEX R R1.3 disclosure (ii)), and — **not named in any HE7 coverage list** — characteristic 2 (OPEN-CALL 3).

**DERIVATION:** Coverage declaration read off the §S10 rows (`.77`).

**RESOLUTION TRACE:** Base lines 1305–1313; partly discharged at 1314–1323 (`[r1]`) and at 2294–2334 (ANNEX R R1.3, shard 3).

**TEETH:** This unit IS the coverage ledger for every other tooth; its predicates are `.77`'s rows and `.78`'s legs.

---

### EFF.HE7.71  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1314–1323 — HE7-BOX-2's `[r1]` partial discharge.

> “**[r1] PARTLY DISCHARGED by a sibling battery.** The d_r ≥ 2 σ-coverage hole
> named here is now exercised — not by this note's frozen runner but by
> HE6R1's own leg (`he6r1_checks.py`): ℓ = 1, d_r = 2, K₂ = F_{p²}, μ = 4,
> μ₂ = 2, λ ∈ {3,5}, q ∈ {3,5,7} char 0 and {3,5} char p, 944 members with
> 677/682 PARI agreements and ZERO mis-decisions, the 5 non-agreements being
> exactly the Ψ | f_S peel stratum. So the residue-direction mechanism of
> (SLOT₂) and the d_r ≥ 2 (LIFT₂) threshold are both machine-exercised; what
> stays unexercised anywhere is d_r ≥ 3, f₁ ≥ 2 stage genres, μ ≥ 5 (hence
> proper blocks — LEMMA HE6R1-2's own configuration is proof-only) and
> level 3.”

**CONDITIONALITY:** **The closing “what stays unexercised anywhere” list is itself superseded on one item**: level 3 is exercised at ANNEX R R1.3 (79/79). The remaining items stand at HEAD. **The sentence “LEMMA HE6R1-2's own configuration is proof-only” is the note's own signed coverage hole** and is what makes `EFF.HE7.39` the shard-1 proof-only unit.

**DERIVATION:** Coverage record; the numbers are HE6R1's, consumed as foreign-note evidence.

**RESOLUTION TRACE:** Base lines 1314–1323 (r1 landed); the level-3 item discharged at 2294–2334 (shard 3).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:he6r1_checks.py` — grep-verified count **2**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.

**TEETH:** `he6r1_checks.py` — 944 members, 677/682 PARI, ZERO mis-decisions, the 5 non-agreements exactly the peel stratum. **Foreign-note regression consumed as coverage** (the runner is HE6R1's, not HE7's; HE7's own runner is byte-frozen).

---

### EFF.HE7.72  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1324–1326 — **HE7-BOX-3 (oracle asymmetry)**.

> “**HE7-BOX-3 (oracle asymmetry).** PARI `factorpadic` exists only on the
> ℤ_p side, so the char-p rows are scored against the reader plus the
> resultant identities. Inherited from HE6-BOX-4.”

**CONDITIONALITY:** Standing and undischarged. **Visible in Q1's table**: the four `F_p[[t]]` rows show `PARI = 0` and `agree = —`, i.e. 250 of the 1,587 members carry no independent oracle. **Compounded, out of range, by dated correction M-A** (shard 3), which reveals that even the ℤ_p side's oracle in the annex legs was the shared `pari_sigma16` (“factorpadic-EQUIVALENT” per the runner's own docstring), with actual `factorpadic` entering only at annex-pass #2's triple-oracle leg.

**DERIVATION:** Declaration of an instrument limitation.

**RESOLUTION TRACE:** Base lines 1324–1326; oracle-identity qualified at 2490 (M-A, shard 3).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-4` — grep-verified count **2**.

**TEETH:** Its own negation: Q1's char-p rows (79 + 57 + 57 + 57 = 250 members) are scored **without** PARI, against the reader plus Q2/Q4/Q5's resultant identities only.

---

### EFF.HE7.73  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1327–1334 — **HE7-BOX-4 (the multiplicity–principal-length link, DELIBERATELY NOT CLAIMED)**.

> “**HE7-BOX-4 (the multiplicity–principal-length link, DELIBERATELY NOT
> CLAIMED).** We do not prove |S_{λ,r}| = D′ℓ·m_r·d_r (the exact
> multiplicity-weighted class size, i.e. Montes' theorem of the product at
> the node). It is not needed: σ-decision uses only the level-2 polygon of
> the actual f_S, and TERMINATION uses only the upper bound
> μ₂ ≤ deg R_λ/d_r. The exact link is a COUNT-side question (it is what one
> would need to predict μ₂ from level-1 data alone, e.g. for a closed-form
> density at a boxed node) and is boxed here.”

**CONDITIONALITY:** Standing. **Partly superseded in READ form at `.74`** (the μ₂/|S| gap is closed off f by LEMMA HE6R1-2), and **restated one step over by ANNEX F-1's honesty box** (`.99`), which declines the analogous multiplicity-to-block-exponent link `k = m`. **This box is the DAG's density-side boundary**: it is precisely what a closed-form density at a boxed node would need, and HE7 declines it. Load-bearing for consumers of the uniformity program's count side.

**DERIVATION:** Declined-claim record; the two “not needed” justifications are `EFF.HE7.13` (σ-decision reads the actual f_S) and `.15` (TERMINATION uses only the upper bound, stated there in the proof's own words: “the multiplicity-weighted exact value … is **not needed**”).

**RESOLUTION TRACE:** Base lines 1327–1334; superseded-in-read-form at 1335–1341; restated one level over at 1867–1881 (`.36`).

**TEETH:** NONE — a declined claim has no tooth. `.36` records the machine observation `k = m` at every observed member, explicitly as an observation and not a claim.

---

### EFF.HE7.74  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1335–1341 — HE7-BOX-4's `[r1]` read-form supersession.

> “**[r1] SUPERSEDED IN READ FORM.** The gap this box leaves — μ₂ and
> |S_{λ,r}| unpinned when the block is proper — is closed by
> **LEMMA HE6R1-2(b)(c)**: |S_{λ,r}| = D″·μ₂ with μ₂ = Σ_{λ₂>T₂}L_{λ₂}(f) read
> off f, and per distinct factor |S_{λ,r_i}| = D′ℓd_{r_i}·μ₂^{(i)}. The
> multiplicities m_{r_i} are never consulted, so the closed form
> D′ℓ·m_r·d_r stays unproved and unneeded — the box survives only as the
> COUNT-side (density-from-level-1-data) question it names.”

**CONDITIONALITY:** Rests entirely on the external **LEMMA HE6R1-2(b)(c)**, whose clause (c) is the one carrying the “equal outright when separable” defect corrected twice from shard 3 (`EFF.HE7.39`). **Proof-only and machine-unexercised** (`.08`: “proper blocks — LEMMA HE6R1-2's own configuration is proof-only”).

**DERIVATION:** Cited, not derived.

**RESOLUTION TRACE:** Base lines 1335–1341 (r1 landed); the supplier's clause (c) corrected at 2593–2622 and 2624–2652 (shard 3).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.

**TEETH:** **NONE — proof-only.**

---

### EFF.HE7.75  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1342–1346 — **`[r1]` HE7-BOX-5 (the peel stratum's coverage)**.

> “**[r1] HE7-BOX-5 (the peel stratum's coverage).** The Ψ | f_S stratum is
> decided by LEMMA HE6R1-3 and machine-confirmed at n = 8 (8/8 peels, 2/2 PARI
> on σ(f), 2/2 PARI on σ(Ψ); §S11 [r1]) and at HE6R1's ℓ = 1, d_r = 2 frame
> (12/12, 5/5 PARI). Not exercised: a peel at μ₂ ≥ 3, and a peel at a PROPER
> block (both need μ ≥ 5, i.e. n ≥ 10). The lemma's proof is uniform in both.”

**CONDITIONALITY:** Standing; **not discharged by any later leg.** The PE3 probe (`.100`) runs at μ₂ = 3 but is a mixed-residual refine probe, not a peel probe; the annex leg (`.101`/`.102`) runs at μ₂ = 4 with no peel reported. **A peel at μ₂ ≥ 3 and a peel at a proper block remain machine-untouched at HEAD.** Note the interaction with `EFF.HE7.55`: the `[r3]` mid-chain-peel clause is likewise machine-vacuous (“zero mid-chain peels”), so the entire deep-peel region is proof-only.

**DERIVATION:** Coverage declaration; the uniformity claim (“The lemma's proof is uniform in both”) is a claim about LEMMA HE6R1-3's proof, made here without reproducing it.

**RESOLUTION TRACE:** Base lines 1342–1346 (r1 landed); untouched by every later round.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** `he7r1_supp.py` (8/8 + 2/2 + 2/2 at n = 8) · `he6r1_checks.py` (12/12, 5/5 PARI at ℓ = 1, d_r = 2) — both at μ₂ = 2 only.

---

### EFF.HE7.76  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1352–1362 — §S10's **Instrument**.

> “**Instrument.** Exact integer (and exact F_p[t]) Sylvester–Bareiss
> resultants; a fresh **level-2 reader** built literally from §S1 (Ψ-adic
> development of f; dv₂ from the Φ′-development slot-min; the level-2 polygon;
> the level-2 residual assembled WITH the explicit β-power twist; factorization
> over K₂; the THEOREM HE7.A dictionary; the level-2 α-refine of LEMMA HE7-8
> with a bounded loop); PARI `sig(f,p) = factorpadic + idealprimedec` as the
> independent σ oracle on the char-0 rows. Members are HE6's own enumeration —
> perturbations strictly above the λ-line — so every member of a row has the
> SAME outer data and only the deeper digits move. **The instrument reuses
> HE6's rings, resultants, level-1 reader and member enumerator by import, so
> the level-1 leg is byte-identical to the sealed HE6 code.**”

**CONDITIONALITY:** **The reuse-by-import sentence is a decorrelation LIMIT, not only a provenance claim**: the level-1 leg is byte-identical to HE6's, so HE7's battery cannot independently falsify a level-1 defect. This is exactly the mechanism by which FINDING HE7-F1 (shard 1 `.84`) and the later coset defect were invisible to HE6's own battery and needed a dedicated leg / a foreign pass. The `[r3]` remark R-b (`.86`) records the same coupling one level up for `he7r2_supp.py`.

**DERIVATION:** Instrument description; the reader is “built literally from §S1”, i.e. the predicates it implements are `EFF.HE7.06`, `.08`, `.11`, `.13`, `.53`.

**RESOLUTION TRACE:** Base lines 1352–1362; byte-frozen at seal 1956151 (line 1383–1385) and never edited. Oracle identity later qualified at 2490 (M-A, shard 3) for the ANNEX legs — **not for this sealed runner**, whose docstring names `factorpadic + idealprimedec` directly.

**TEETH:** This unit IS the instrument; every row of §5 runs on it or on a declared-independent replacement.

---

### EFF.HE7.77  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1364–1366 — §S10's **Rows**.

> “**Rows.** (e₁,f₁,h) = (2,1,1), Φ′ = x²−π, μ = 4, deg f = 8, ALPHA2
> (R_λ = (Z−s)², the HE6-BOX-1 node): ℤ_3, ℤ_5, ℤ_7 at λ = 5/2, ℤ_5 at
> λ = 7/2, F_3[[t]] and F_5[[t]] at λ = 5/2.”

**CONDITIONALITY:** These six named row-families expand to the **thirteen** rows of Q1's table (nine ℤ_p, four F_p[[t]]) once the twist-live letters `s ∈ {2,3}` are counted. **The row list is the source of HE7-BOX-2's coverage limits** (`.70`): `d_r = 1`, `f₁ = 1`, `μ = 4`, `q ∈ {3,5,7}`/`{3,5}` — and **no row has p = 2**.

**DERIVATION:** Row declaration; instantiates `EFF.HE7.57`'s frame.

**RESOLUTION TRACE:** Base lines 1364–1366; byte-frozen at seal 1956151.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-1` — count **9**.

**TEETH:** Q1's thirteen-row table (`.24`) is this declaration's realisation.

---

### EFF.HE7.78  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1368–1374 — §S10's **Legs (preregistered as P1–P5)**.

> “**Legs (preregistered as P1–P5 in the runner docstring).** HE7-READ2/HE7-SIG2
> (P1: the level-2 read vs PARI, member by member, on the three-σ family) ·
> HE7-SLOT2 (P2: v(Res(f,C)) = 2·dv₂(C) for C of degree < D″, both level-2
> classes) · HE7-LIFT1/HE7-LIFT2 (P3: the exact reachable sets W₁, W₂ vs the
> closed-form thresholds, ten frames) · HE7-GEN2 (P4: the level-2 flat
> resultant identity at rational level-2 heights) · HE7-SEP2 (P5: strict excess
> exactly at the level-2 labels).”

**CONDITIONALITY:** **Preregistered** — the predicates were sealed at commit 1 with the runner docstring, before the verdict run at commit 2. The `[r2]` disclosure (2) (`.85`) records one honesty wrinkle about the seal's self-description (a stale `WIP = False` comment), resolved by git: the runner was byte-identical between seal and verdict.

**DERIVATION:** Preregistration record. Each leg's mathematical predicate is a shard-1 unit: P1 `EFF.HE7.13`+`.58`; P2 `.11`+`.40`; P3 `.12`+`.19`+`.22`+`.23`; P4 `.27`+`.41`; P5 `.34`+`.41`.

**RESOLUTION TRACE:** Base lines 1368–1374; verdicts at 1497–1563 (`.24`–`.27`).

**TEETH:** The five legs ARE battery rows; inventoried in §5.

---

### EFF.HE7.79  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1376–1379 — §S10's **Teeth**.

> “**Teeth.** HE7-T-CASEB-SEP (the headline: ≥ 3 distinct PARI σ inside ONE
> constant-outer-data family, all predicted) · HE7-T-WITHHOLD · HE7-T-RANK ·
> HE7-T-LIFT2SHARP (FINDING HE7-F1 machine-confirmed) · HE7-T-BADTWIST ·
> HE7-T-SLOT2TIE.”

**CONDITIONALITY:** All six fired (`.91`). **HE7-T-LIFT2SHARP's blind spot is disclosed out of range** (shard 3, line 2544–2546): its frames sat at `q(k) = 0` on every proper-`T` height tested, so it could not have seen the `η_θ^{−q(k)}` coset defect it appears to guard.

**DERIVATION:** Tooth declaration; each tooth's target is a shard-1 hypothesis or display.

**RESOLUTION TRACE:** Base lines 1376–1379; verdicts at 1565–1582; HE7-T-LIFT2SHARP's blind spot disclosed at 2541–2546 (shard 3).

**TEETH:** Six rows in §5.

---

### EFF.HE7.80  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1383–1388 — §S10's `[r1]` byte-freeze declaration.

> “**[r1] BYTE-FREEZE + one additive leg.** `he7_checks.py` and its two artifacts
> are **byte-frozen at seal 1956151**: no predicate, row or number of §S10/§S11
> was touched by the r1 round. The one machine addition is
> `verification/openmath/he7r1_supp.py`, which *imports* the sealed runner,
> reproduces its enumeration member-for-member, and checks LEMMA HE6R1-3's peel
> on the 8 members the sealed reader left undecided (§S11 [r1]).”

**CONDITIONALITY:** **This is the instrument-freeze predicate, distinct from the text-freeze predicate** (resolution rule 7). It is why every subsequent instrument defect is DISCLOSED rather than repaired (`.85`, `.86`) and why every subsequent leg is ADDITIVE and imports the sealed runner. `git cat-file -t 1956151` = commit (verified). **The import-the-sealed-runner pattern is itself a decorrelation limit**, disclosed at `.86`(3) and answered by PE2's independent instrument.

**DERIVATION:** Protocol declaration.

**RESOLUTION TRACE:** Base lines 1383–1388 (r1 landed); the additive-leg pattern continues at 1432–1451 (r2), 1885–1896 and 1897–1946 (ANNEX F-1), 2263–2334 (ANNEX R, shard 3).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** `he7r1_supp.py` (`.83`).

---

### EFF.HE7.81  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1394–1401 — §S11's verdict headline and totals.

> “**GREEN — 0 violations, ALL SIX TEETH FIRED, 191.8 s.** Artifacts
> `he7_checks_output.txt` (md5 b2d095a2556a…), `he7_checks_results.json`
> (f5bedab2ecda…), runner-as-run `he7_checks.py` (688adbe88447…). Totals:
> **1,587 members** over thirteen rows (nine ℤ_p rows with the PARI oracle,
> four F_p[[t]] rows without it) · **1,335 PARI σ jobs** · **12,632 (SLOT₂)
> exactness identities** · **4,259 level-2 flat identities** · **191 + 5
> strict/infinite-excess (nonemptiness) certificates** · ten (LIFT)/(LIFT₂)
> frames verified exhaustively.”

**CONDITIONALITY:** **The scope sentence attached to these numbers changes at `[r1]`, the numbers do not** (`.82`). The three artifacts exist on disk (`verification/openmath/`: `he7_checks_output.txt`, `he7_checks_results.json`, `he7_checks.py` — 3/3 present).

**DERIVATION:** Machine verdict.

**RESOLUTION TRACE:** Base lines 1394–1401; scope re-read at 1403–1413; net totals restated at 1429–1430.

**TEETH:** This unit is the verdict of rows P1–P5 + the six teeth.

---

### EFF.HE7.82  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1403–1413 — the `[r1]` re-reading of the totals.

> “**[r1] HOW TO READ THESE TOTALS AFTER FINDING HE6R1-F2.** The artifacts are
> byte-frozen (seal 1956151) and no number below changes; what changes is the
> scope sentence attached to them. Of the 1,587 members, **1,579 are on the
> Ψ ∤ f_S stratum** (reader status `OK`) and **8 are the Ψ | f_S stratum**
> (status `DEGENERATE-key-divides`, i.e. A₀^{(2)} = 0), which the sealed reader
> skipped without emitting a σ — 2 of them on a PARI row, which is exactly why
> one row reads members 124 / PARI 122 in Q1's table while every other row has
> PARI = members (209+243+161+125+**122**+150+105+115+105 = 1,335). So Q1's
> 1,335/1,335 is the σ verdict **on the Ψ ∤ f_S stratum**, which is precisely the
> stratum the r1 statements now name. Distribution of the 8: ℤ₃ λ=5/2 s=2 → 2,
> F₃[[t]] λ=5/2 s=1 → 3, F₅[[t]] λ=5/2 s=2 → 2, F₅[[t]] λ=5/2 s=3 → 1.”

**CONDITIONALITY:** None; this is the honest re-scoping of a frozen verdict. **The arithmetic is checkable and checks:** 209+243+161+125+122+150+105+115+105 = **1,335** ✓ (compiler-verified). The distribution of the 8 sums to 2+3+2+1 = **8** ✓. **One internal cross-check FAILS on a row label, not on a number.** Independently re-deriving the per-row degenerate count from Q1's own table as `members − (σ-column sum)` gives exactly four nonzero rows: `ℤ₃ λ=5/2 s=2` → **2** (124 − 122), `F₃[[t]] λ=5/2 s=1` → **3** (79 − 76), `F₅[[t]] λ=5/2 **s=1**` → **2** (57 − 55), `F₅[[t]] λ=5/2 s=3` → **1** (57 − 56); total **8** ✓. **Three of the four labels match the `[r1]` distribution exactly; the third does not — the note writes “F₅[[t]] λ=5/2 s=2 → 2” but Q1's F₅[[t]] rows carry only s = 1 and s = 3, and the row that is short by 2 is the s = 1 row.** The count and the total are right; the letter is wrong. Recorded as source defect 2 in §8. No statement or verdict depends on the letter.

**DERIVATION:** Arithmetic on the frozen artifact, displayed.

**RESOLUTION TRACE:** Base lines 1403–1413 (r1 landed); the 8 are decided at 1415–1430.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` — count **4**.

**TEETH:** The `DEGENERATE-key-divides` status is itself the tooth — the machine isolated the stratum before any human found the missing hypothesis (shard 1 `.72`: “This was found BY the machine”).

---

### EFF.HE7.83  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1415–1430 — the `[r1]` peel leg.

> “**[r1] THE PEEL LEG (additive, post-seal): the 8 are DECIDED, and PARI agrees
> on both halves.** `verification/openmath/he7r1_supp.py` imports the sealed
> runner, reproduces its member enumeration exactly (1,587 members, the same 8
> by row), and per degenerate member checks: **A1** A₀^{(2)} = 0 and
> Ψ·(Ψ + A₁^{(2)}) = f exactly in O[x] — **8/8**; **A2** A₁^{(2)} ≠ 0, so
> Ψ ∤ f′ and the peel happens ONCE — **8/8**; **A3** the sealed reader on
> f′ = Ψ + A₁^{(2)} returns status OK with σ(f′) = {(4,1)} at μ₂′ = 1 —
> **8/8**; **A4** PARI `factorpadic`: σ(f) = {(4,1),(4,1)} — **2/2** (the two
> char-0 members); **A5** PARI: **σ(Ψ) = {(4,1)}** — **2/2**, a direct oracle
> test of LEMMA HE6R1-3's *irreducibility of Ψ over O of degree D″ with
> (e,f) = (e₁ℓ, f₁d_r)*, which no textual argument of this note supplies.
> 0 violations, 3.3 s; artifacts `he7r1_supp_output.txt`,
> `he7r1_supp_results.json` (pins: `he7_checks.py` 688adbe88447,
> `he7_checks_results.json` f5bedab2ecda, `he6_checks.py` 321fa4d4990e).
> **Net over the two legs: 1,587/1,587 members decided, 1,337 PARI σ(f) jobs
> (1,335 sealed + 2 peel) with 0 mis-decisions, plus 2 PARI σ(Ψ) jobs.**”

**CONDITIONALITY:** **A5 is the ONLY evidence anywhere in HE7 for LEMMA HE6R1-3's irreducibility half**, and the note says so in the same sentence (“which no textual argument of this note supplies”). It rests on **2 members**. A3 runs the SEALED reader, so it is not decorrelated from the instrument; A4/A5 are PARI, which is.

**DERIVATION:** Machine record; predicates A1–A5 implement `EFF.HE7.09`/`.38`/`.60`.

**RESOLUTION TRACE:** Base lines 1415–1430 (r1 landed); the artifacts exist on disk (`he7r1_supp.py`, `he7r1_supp_output.txt`, `he7r1_supp_results.json` — 3/3 present).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** A1–A5 are five battery rows (§5).

---

### EFF.HE7.84  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1432–1451 — the `[r2]` slot-domination leg.

> “**[r2] THE SLOT-DOMINATION LEG (additive, post-PE1):
> `verification/openmath/he7r2_supp.py`** imports the sealed runner,
> reproduces its member enumeration exactly, isolates the refine-path
> members, and checks LEMMA HE7-12/HE7-13's displayed inequalities per
> member: **B1** slot geometry (Ψ's occupied Φ′-slots all exactly at T₂;
> w's slot-min exactly λ₂ > T₂; (LIFT₂) contract res₂(w, λ₂) = s₂) —
> **42/42**; **B2** the off-disk inequality (S5.8.1) in resultant-sum form
> plus the invariance conclusion dv₂-Res(g, Ψ^{(1)}) = dv₂-Res(g, Ψ), on
> five off-disk strata per member covering all three offset cases of the
> lemma (δ = ∞; δ > λ; the (S5.2) [r2] middle band δ ∈ (D′h, λ) with
> ε₁ = 1/2; ε₀ = 1; δ = λ with wrong residue) — **210/210**; **B3** the
> strict slope increase (S5.8.2): Σ_ρ dv₂(Ψ(ρ)) = 8λ₂ exactly pre-refine,
> strictly greater post-refine, every recomputed post-refine slope > λ₂,
> and the LEMMA HE7-9(b) count identity **at the refined key** — **42/42**;
> **B4** the pre-refine residual is (Z − s₂)² — **42/42**; **B5** per-row
> refine recount == the frozen artifact — **13/13 rows**. 0 violations,
> 3.8 s; artifacts `he7r2_supp_output.txt`, `he7r2_supp_results.json`
> (pins: `he7_checks.py` 688adbe88447, `he7_checks_results.json`
> f5bedab2ecda, `he6_checks.py` 321fa4d4990e, `he7r1_supp.py`
> 24ece42e4538).”

**CONDITIONALITY:** **Three disclosed weaknesses, all landed at `[r3]`** (`.86`): B2's δ = ∞ inequality half is vacuous on 41 of 42 members; B3's peel-guard skip exists (never fired); B1's (LIFT₂) contract is verified through the SAME module it tests. The third is answered by PE2's independent instrument (634/634); the first by PE2's fresh leg re-verifying the stratum non-vacuously.

**DERIVATION:** Machine record; predicates B1–B5 implement `EFF.HE7.43`/`.44`/`.45`.

**RESOLUTION TRACE:** Base lines 1432–1451 (r2 landed); disclosures at 1473–1495 (r3). Artifacts present on disk (3/3).

**TEETH:** B1–B5 are five battery rows (§5).

---

### EFF.HE7.85  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1453–1471 — the `[r2]` **four disclosures on the sealed instrument**.

> “**[r2] FOUR DISCLOSURES ON THE SEALED INSTRUMENT (byte-frozen, so
> disclosed here rather than edited; PE1 remarks R-a/R-b/R-c + one
> recount).** (1) *Refine recount:* the frozen `he7_checks_results.json`
> refine histograms sum to **42** refine-firing members, not the 41 stated
> in Q1's sentence below — a display slip of the note (the artifact was
> always 42); the r2 leg re-enumerates and checks all 42. (2) *Stale
> self-comment (R-a):* `he7_checks.py` line 140 reads "WIP = False # commit
> 1 sealed this True (smoke only); commit 2 flips it" — git shows the
> runner byte-identical between seal 1956151 and verdict 4c42f9d, i.e. WIP
> was already False at the seal and no in-history flip occurred; the smoke
> record in the docstring is the honest preregistration record, the comment
> is stale about itself and CANNOT be edited (byte-freeze). (3) *Silent
> PARI-drop guard (R-b):* `run_row` skips a PARI job that fails to parse
> (`if g is None: continue`) without raising a violation; audited over the
> sealed artifacts — every row has PARI = read-OK members (the one 124/122
> row is exactly the 2 key-divides members, which never reach the oracle),
> so **zero drops occurred**. (4) *Redundant degenerate test (R-c):* the
> reader's `any(v >= BIG for v in dv2s[:mu2]) and dv2s[0] >= BIG` is
> equivalent to its second conjunct — harmless, disclosed.”

**CONDITIONALITY:** All four are **signed non-repairs**: the instrument is byte-frozen, so each is disclosed with its audit rather than edited. Disclosure (1) is a **correction to the note's own prose** (41 → 42) and is applied at `.87`. Disclosure (3)'s audit is what licenses reading Q1's `124/122` row as the key-divides stratum rather than as dropped jobs.

**DERIVATION:** Audit records; (1) by re-summing the frozen histograms, (2) by git byte-comparison across two commits, (3) by cross-tabulating PARI counts against read-OK members over the sealed artifacts, (4) by inspection.

**RESOLUTION TRACE:** Base lines 1453–1471 (r2 landed); (1) applied in Q1's sentence at 1521–1524.

XREF: `lean/notes/openmath/HE7_passPE1_report.md:R-a` — grep-verified count **2**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:R-b` — grep-verified count **2**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:R-c` — grep-verified count **2**.

**TEETH:** Disposition **signed non-applicability / disclosed non-repair** for all four; (3) carries an affirmative audit result (zero drops).

---

### EFF.HE7.86  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1473–1495 — the `[r3, HE7-PE2]` **three further disclosures on the frozen r2 leg**.

> “**[r3, HE7-PE2] THREE FURTHER DISCLOSURES ON THE FROZEN r2 LEG (PE2's
> F-3 plus remarks R-a/R-b; instrument byte-frozen, so disclosed rather
> than edited).** (1) *B2's δ = ∞ coverage (F-3):* on the δ = ∞ stratum
> (g = Φ′) the QUANTITATIVE half of (S5.8.1) sits behind the guard
> `a_w < BIG` and is vacuous whenever Φ′ | w — at this frame (u odd, ℓ = 2,
> d_r = 1) exactly when λ₂ is odd, where s₀ = 1 — i.e. on **41 of the 42**
> members (λ₂ histogram re-counted at r3: 11 × 38, 12 × 1, 15 × 3; the one
> λ₂ = 12 member exercises it). Mathematically trivial there: Φ′ | w gives
> w(ξ) = 0 at every δ = ∞ point, so off-disk invariance is IMMEDIATE — and
> the invariance half WAS genuinely checked on all 42. Honest reading:
> "210/210" is 210 stratum passes, of which the δ = ∞ inequality instance
> was TESTED on 1; PE2's fresh leg re-verified this stratum non-vacuously
> (Res(Φ′, w) ≠ 0 on the majority of its 634 d_r = 2 members, all green).
> (2) *(R-a) B3's peel-guard skip:* the HE7-9(b) identity is skipped when
> the refined key divides f (`dv2s1[0] < BIG`); the skip never fired (all
> 42 post-refine resultants finite; PE2's identical fresh-leg guard never
> fired on 634) and B3's strict-increase half runs regardless —
> DISPOSITION: disclosed; no repair is possible on a frozen instrument and
> none is needed. (3) *(R-b) B1's same-instrument coupling:* the (LIFT₂)
> contract on the sealed `lift2` is verified through `dv2`/`res2` from the
> same module — DISPOSITION: accepted; decorrelation is supplied by PE2's
> independent instrument (`he7_pe2_fresh.py`, no he6/he7 import), which
> re-implements both sides and agrees 634/634.”

**CONDITIONALITY:** These three, plus `.85`'s four, are the seven standing instrument disclosures. **Disclosure (1) materially re-reads a headline number** (“210/210” is 210 stratum passes, one of which tested the δ = ∞ inequality) and is the single most important honesty item in the machine record. The λ₂ histogram check is arithmetically consistent: 38 + 1 + 3 = **42** ✓ (compiler-verified). The `he7_pe2_fresh.py` artifact exists on disk.

**DERIVATION:** Audit records; (1) by guard analysis plus a re-count of the λ₂ histogram, (2) by guard-firing audit, (3) by module-dependency inspection plus a decorrelated re-run.

**RESOLUTION TRACE:** Base lines 1473–1495 (r3 landed); untouched by later rounds.

XREF: `lean/notes/openmath/HE7_passPE2_report.md:R-a` — count **2**.
XREF: `lean/notes/openmath/HE7_passPE2_report.md:R-b` — count **1**.

**TEETH:** Dispositions: (1) **signed vacuity disclosure** with an external non-vacuous re-verification; (2) **disclosed non-repair**, guard never fired; (3) **accepted with decorrelation supplied** (`he7_pe2_fresh.py`, 634/634).

---

### EFF.HE7.87  [table]

**CANONICAL STATEMENT:** `[TABLE]` — **Q1 (HE7-READ2 / HE7-SIG2 — P1, THE HEADLINE)**, lines 1497–1524. Prose verbatim, then the source's ASCII table verbatim, then its `[TABLE]` transcription.

> “**Q1 (HE7-READ2 / HE7-SIG2 — P1 confirmed; THE HEADLINE) ✓ 1,335 PARI jobs,
> 1,335 agree, 0 mismatch.** On the HE6-BOX-1 node (ALPHA2: ℓ = 2,
> R_λ = (Z−s)², one label class of size 8 = deg f, σ UNDECIDED by the outer
> data), the level-2 read predicts σ **member by member** and PARI
> `factorpadic` confirms every prediction, on nine rows and both letters
> s = 1 (twist trivial) and s ∈ {2,3} (twist live):”

Source display, verbatim:

>     row                     s   members  PARI  agree  {(8,1)}  {(4,2)}  {(4,1),(4,1)}
>     Z_3  λ=5/2              1     209     209   209     161      31         17
>     Z_5  λ=5/2              1     243     243   243     219      14         10
>     Z_7  λ=5/2              1     161     161   161     144      11          6
>     Z_5  λ=7/2              1     125     125   125     105      10         10
>     Z_3  λ=5/2  twist live  2     124     122   122     102      10         10
>     Z_5  λ=5/2  twist live  2     150     150   150     135      13          2
>     Z_5  λ=5/2  twist live  3     105     105   105      84      11         10
>     Z_7  λ=5/2  twist live  3     115     115   115      99       8          8
>     Z_5  λ=7/2  twist live  2     105     105   105      88       8          9
>     F_3[[t]] λ=5/2          1      79       0     —       61      13          2
>     F_3[[t]] λ=5/2  twist   2      57       0     —       47       5          5
>     F_5[[t]] λ=5/2          1      57       0     —       45       7          3
>     F_5[[t]] λ=5/2  twist   3      57       0     —       49       5          2

`[TABLE]` transcription:

| row | s | members | PARI | agree | {(8,1)} | {(4,2)} | {(4,1),(4,1)} |
|---|---|---|---|---|---|---|---|
| Z_3 λ=5/2 | 1 | 209 | 209 | 209 | 161 | 31 | 17 |
| Z_5 λ=5/2 | 1 | 243 | 243 | 243 | 219 | 14 | 10 |
| Z_7 λ=5/2 | 1 | 161 | 161 | 161 | 144 | 11 | 6 |
| Z_5 λ=7/2 | 1 | 125 | 125 | 125 | 105 | 10 | 10 |
| Z_3 λ=5/2 twist live | 2 | 124 | 122 | 122 | 102 | 10 | 10 |
| Z_5 λ=5/2 twist live | 2 | 150 | 150 | 150 | 135 | 13 | 2 |
| Z_5 λ=5/2 twist live | 3 | 105 | 105 | 105 | 84 | 11 | 10 |
| Z_7 λ=5/2 twist live | 3 | 115 | 115 | 115 | 99 | 8 | 8 |
| Z_5 λ=7/2 twist live | 2 | 105 | 105 | 105 | 88 | 8 | 9 |
| F_3[[t]] λ=5/2 | 1 | 79 | 0 | — | 61 | 13 | 2 |
| F_3[[t]] λ=5/2 twist | 2 | 57 | 0 | — | 47 | 5 | 5 |
| F_5[[t]] λ=5/2 | 1 | 57 | 0 | — | 45 | 7 | 3 |
| F_5[[t]] λ=5/2 twist | 3 | 57 | 0 | — | 49 | 5 | 2 |

Closing prose, verbatim (lines 1519–1524):

> “All three σ values occur on every row, exactly the three outputs of THEOREM
> HE7.A's μ₂ = 2 dictionary (§S8), and no fourth value ever appears. The
> level-2 α-refine of LEMMA HE7-8 fired on **42** members ([r2] recount from
> the frozen artifact's refine histograms; the pre-r2 sentence said 41 — a
> prose slip, see the [r2] disclosures above) and terminated in
> **one** step every time — (REF-TERM) in action, never approaching the bound.”

**CONDITIONALITY:** **Scoped to the Ψ ∤ f_S stratum** by `.82`; the remaining 8 members are `.83`'s. **The `Z_3 s=2` row's `124 members / 122 PARI` is the visible signature of the peel stratum**, audited at `.85`(3). **Compiler arithmetic audit of the whole table (all thirteen rows recomputed):** the nine ℤ_p rows' members sum to **1,337**, of which PARI = **1,335** (the 2 key-divides members never reach the oracle) ✓; all thirteen rows sum to 1,337 + 250 = **1,587** ✓, matching `.81`'s total; and `members − (σ-column sum)` is **0 on nine rows** and nonzero on exactly four — `ℤ₃ s=2` → 2, `F₃[[t]] s=1` → 3, `F₅[[t]] s=1` → 2, `F₅[[t]] s=3` → 1, total **8** ✓, matching `.82`'s degenerate count. **The σ columns therefore count READ-OK members, not members** — which the note never says in so many words, and which is the only way the four short rows are consistent. The four short rows are also the ONLY place the char-p half of the peel stratum is visible at all, since those rows have no PARI column. (The one label mismatch this audit exposes is source defect 2.)

**DERIVATION:** Machine verdict against an independent oracle.

**RESOLUTION TRACE:** Base lines 1497–1524, with the `[r2]` 41 → 42 recount already landed inside the closing sentence; scope re-read at 1403–1413.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-1` — count **9**.

**TEETH:** P1 is the headline battery row; HE7-T-CASEB-SEP, HE7-T-RANK and HE7-T-WITHHOLD ride it.

---

### EFF.HE7.88  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1526–1530 — **Q2 (HE7-SLOT2 — P2)**.

> “**Q2 (HE7-SLOT2 — P2 confirmed) ✓ 0 violations in 12,632 checks:**
> v(Res(f, C)) = 2·dv₂(C) EXACTLY for C ∈ O[x] of degree < D″ = 4 exercising
> both level-2 classes mod ℓ, in both characteristics. Since the two classes
> have opposite parity, any within-class cancellation or cross-class tie would
> break this identity; it is the machine form of (SLOT₂)'s exactness clause.”

**CONDITIONALITY:** Unconditional at the row frame. The “opposite parity” argument is what makes the identity a genuine test of both clauses (a) and the exactness of `EFF.HE7.11`, not merely of the min formula.

**DERIVATION:** `by EFF.HE7.11` + `by EFF.HE7.40` ((RES₂) at `dv₂ = 2v` in this frame, `e₁ℓ = 2`).

**RESOLUTION TRACE:** Base lines 1526–1530; untouched.

**TEETH:** P2, one row; guards `EFF.HE7.06`, `.11`, `.40`, and HE7-T-SLOT2TIE is its planted mutant.

---

### EFF.HE7.89  [table]

**CANONICAL STATEMENT:** `[TABLE]` — **Q3 (HE7-LIFT1 / HE7-LIFT2 — P3, and FINDING HE7-F1 machine-confirmed)**, lines 1532–1555. Prose verbatim, the two source ASCII tables verbatim, then their `[TABLE]` transcriptions.

> “**Q3 (HE7-LIFT1 / HE7-LIFT2 — P3 confirmed, and FINDING HE7-F1
> machine-confirmed) ✓** The reachable-height sets computed by exhaustive
> enumeration match the closed forms of LEMMA HE7-L1 and (LIFT₂) in all ten
> frames: every k above the threshold is surjective (5/5 level-1, 5/5 level-2),
> and below it surjectivity genuinely fails —”

Source displays, verbatim:

>     level 1 (e₁,f₁,h)  (D′−1)h   k < thr NOT surjective   k not attained at all
>     (3,1,2)               4              {1}                      {1}
>     (2,2,1)               3             {0,1}                      —
>     (3,2,1)               5            {0,1,2}                     —
>     (2,1,3)               3              {1}                      {1}
>     (2,3,1)               5           {0,1,2,3}                    —

>     level 2 (e₁,f₁,h,ℓ,d_r,u)     thr₂    #k < thr₂ NOT surjective
>     (2,1,1,2,1,5)                   7               2
>     (2,1,1,2,2,5)                  17              12
>     (2,2,1,2,2,7)                  27              21
>     (3,1,2,2,3,13)                 73              60
>     (1,2,1,3,2,11)                 58              46

`[TABLE]` transcriptions:

| level 1 (e₁,f₁,h) | (D′−1)h | k < thr NOT surjective | k not attained at all |
|---|---|---|---|
| (3,1,2) | 4 | {1} | {1} |
| (2,2,1) | 3 | {0,1} | — |
| (3,2,1) | 5 | {0,1,2} | — |
| (2,1,3) | 3 | {1} | {1} |
| (2,3,1) | 5 | {0,1,2,3} | — |

| level 2 (e₁,f₁,h,ℓ,d_r,u) | thr₂ | #k < thr₂ NOT surjective |
|---|---|---|
| (2,1,1,2,1,5) | 7 | 2 |
| (2,1,1,2,2,5) | 17 | 12 |
| (2,2,1,2,2,7) | 27 | 21 |
| (3,1,2,2,3,13) | 73 | 60 |
| (1,2,1,3,2,11) | 58 | 46 |

Closing prose, verbatim (lines 1552–1555):

> “So HE6 §S1's unqualified (LIFT) is refuted as stated (the (3,1,2) row: the
> height k = 1 is attained by **no** C at all), the corrected threshold is
> exactly right, and both are invisible at the battery's σ frame
> (f₁ = d_r = 1), which is why FINDING HE7-F1 required a dedicated leg.”

**CONDITIONALITY:** **This leg's blind spot is disclosed out of range** (shard 3, line 2544–2546): “its frames sat at q(k) = 0 on each proper-T height tested ((2, 2, 1): q(0) = q(1) = 0; (3, 1, 2): T(1) = ∅), where the coset factor is 1”. So Q3 confirms LEMMA HE7-L1's **fullness/emptiness** clauses and is silent on its **exact-set** clause — the clause the later coset correction repairs. The tables' `thr₂` values are `EFF.HE7.23`'s recursion evaluated at each frame; compiler check on the first: `(ℓd_r − 1)u + ℓ(D′−1)h = (2·1−1)·5 + 2·(2−1)·1 = 5 + 2 = 7` ✓.

**DERIVATION:** Exhaustive enumeration against the closed forms of `EFF.HE7.19` and `.12`/`.22`/`.23`.

**RESOLUTION TRACE:** Base lines 1532–1555; blind spot disclosed at 2541–2546 (shard 3).

**TEETH:** P3 (two rows) + HE7-T-LIFT2SHARP.

---

### EFF.HE7.90  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1557–1563 — **Q4/Q5 (HE7-GEN2 / HE7-SEP2 — P4, P5)**.

> “**Q4/Q5 (HE7-GEN2 / HE7-SEP2 — P4, P5 confirmed) ✓** 0 violations in 4,259
> level-2 flat identities ℓe₁·v(Res(f, Ψ₂)) = D″ℓ₂d₂·h_{F₂}(κ₂) at rational
> LEVEL-2 heights κ₂ = u₂/ℓ₂ > T₂ with ℓ₂ ∈ {1,2,3} — heights no element of
> the LEVEL-1 stage ring can occupy — and 191 STRICT excesses (plus 5 infinite
> ones, where the test polynomial reproduces a factor of f) exactly at the
> level-2 labels. This is HE6's own P1/P2 pair one level up, i.e. the machine
> form of LEMMA HE7-9 and LEMMA HE7-10.”

**CONDITIONALITY:** Unconditional at the row frame. The parenthetical “heights no element of the LEVEL-1 stage ring can occupy” is the note's own claim that the level-2 test family reaches genuinely new heights — the observational content that distinguishes the level-2 read from a level-1 one.

**DERIVATION:** `by EFF.HE7.27` (the test family), `.40`+`.41` (the identity and the excess criterion), `.34` (both evaluation displays).

**RESOLUTION TRACE:** Base lines 1557–1563; untouched. HE7-GEN2 is also the leg that caught the inverse-twist defect pre-seal (`EFF.HE7.32`).

**TEETH:** P4 and P5, two rows.

---

### EFF.HE7.91  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1565–1582 — **Q6 (teeth: 6/6 FIRED)**.

> “**Q6 (teeth: 6/6 FIRED).**
> * **HE7-T-CASEB-SEP ✓ (the box certificate turned into a separation
>   certificate)** three distinct PARI σ inside ONE family of identical outer
>   data, and the level-2 read predicts all 8/8.
> * **HE7-T-RANK ✓** the outer read gives one label class of size 8 with three
>   σ compatible; the level-2 read gives exactly one per member, 8/8 == PARI.
> * **HE7-T-WITHHOLD ✓** with one side's level-2 residual withheld the reader
>   reports UNDETERMINED — it does not silently accept.
> * **HE7-T-LIFT2SHARP ✓** the two tables of Q3.
> * **HE7-T-BADTWIST ✓ 21 (p, s, member) reads CHANGE when the β-power twist
>   is dropped, while the TWISTED read == PARI on 480/480** (and 83 further
>   flips across the full rows). Examples: at p = 3, s = 2 the untwisted read
>   says {(4,1),(4,1)} where the truth is {(4,2)}, and {(4,2)} where the truth
>   is {(8,1)}. **The level-2 normalizer cocycle is machine-load-bearing** —
>   and it is invisible at s = 1, HE6's own configuration.
> * **HE7-T-SLOT2TIE ✓** at gcd(u, ℓ) ≠ 1 the ℓ level-2 classes share heights,
>   so the slot-min is not exact and no level-2 residue is well defined —
>   DEFINITION HE7-1's gcd hypothesis is load-bearing.”

**CONDITIONALITY:** All six fired. **HE7-T-LIFT2SHARP's blind spot** (`.79`, `.89`) is the one qualification. **HE7-T-BADTWIST is the tooth with the widest downstream reach**: it is cited as the reason `.76`'s reader carries the twist, as the reason DEFINITION HE7-3's inverse prescription is load-bearing, and — one level up, out of range — as the reason ANNEX R R1.2 item 3 refuses invariance under CHANGING normalizer systems (“that stronger claim is false, which is HE7-T-BADTWIST's very tooth”), with a level-3 analogue firing 18/79 at ANNEX R R1.3.

**DERIVATION:** Tooth verdicts; each names its target hypothesis.

**RESOLUTION TRACE:** Base lines 1565–1582; HE7-T-BADTWIST generalised at 2203–2213 and 2309–2315 (shard 3).

**TEETH:** Six rows in §5.

---

### EFF.HE7.92  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1584–1599 — **What the machine leg establishes**.

> “**What the machine leg establishes** (instrument grade, not acceptance): that
> the level-2 read of §S1–S5 **decides σ on the exact family HE6 certified as
> undecidable from the outer data**, against an independent oracle, on 1,335
> octics with 0 exceptions **on the Ψ ∤ f_S stratum** ([r1]: the remaining 8
> members are the peel stratum, decided by the additive leg — 8/8, with PARI
> agreeing 2/2 on σ(f) and 2/2 on σ(Ψ)), in both characteristics and at both
> trivial and nontrivial twist; that (SLOT₂)'s exactness holds on 12,632
> instances; that
> (LIFT₂)'s threshold is exactly the closed form, in frames the σ rows cannot
> reach; that LEMMA HE7-9/HE7-10's identities hold at fractional LEVEL-2
> heights on 4,259 instances; that the α-refine terminates (42 firings [r2
> recount], always
> one step); and that two hypotheses — the twist and gcd(u, ℓ) = 1 — are
> load-bearing rather than decorative. Box HE7-BOX-1 unchanged: **attempt grade
> 0/2, no hostile arc has run**; nothing here upgrades the conditionality
> display of COROLLARY HE7.B.”

**CONDITIONALITY:** **The closing grade sentence is superseded** by the arc chronology (`.68`, `.69`, `.103`, and ANNEX R's append). **The substantive scope sentence — “instrument grade, not acceptance” — is NOT superseded and is the note's own statement of what machine evidence is worth.** It is the cleanest available statement of the campaign's evidence hierarchy and should survive the merge intact.

**DERIVATION:** Summary of `.81`–`.91`.

**RESOLUTION TRACE:** Base lines 1584–1599; grade superseded at 1285–1304, 1948–1959, 2442–2462, 2493–2497.

**TEETH:** This unit is the roll-up of every row in §5.

---

### EFF.HE7.93  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the ANNEX F-1 heading (line 1603) and its Provenance-and-scope paragraph (1605–1615), both verbatim]

> “## ANNEX F-1 (2026-08-09, post-acceptance; PE3 F-1) — the mixed-residual rider: ANNEX-LEMMA HE7-13′ (the refine acts PER CLASS), the block reading of HE7.A(3)/§S6(iii), and the R-a disposition. The frozen accepted body above is NOT edited.”

> “**Provenance and scope.** HE7 was **ACCEPTED 2/2** at PE3 (report
> `HE7_passPE3_report.md`, commit 111ac7f): 0 CRITICAL, 0 GAP, 1 MINOR —
> FINDING F-1, with remark R-a folded into it. The accepted text is
> byte-frozen; per the report's closing sentence the owed repair is this
> dated annex (the HMENU3 ANNEX-A pattern: appended, dated, nothing above
> edited). The annex covers exactly PE3 F-1 plus the folded R-a remark and
> NOTHING else. Honesty of grade: the annex text itself is a
> post-acceptance append and has NOT been through a hostile pass; what it
> formalizes is the per-class continuation the PE3 verifier derived and
> machine-verified at the defect's exact configuration (144/144 PARI,
> artifacts committed at b574f25), plus the additive annex leg below.”

**CONDITIONALITY:** **This IS the governing effective-text rule for everything above line 1603** (header (i)). Its own honesty clause is load-bearing: **ANNEX F-1 has never been through a hostile pass as written** — its content was derived and machine-verified by the PE3 *verifier*, then formalized here by the author. `git cat-file -t 111ac7f` = commit ✓; `git cat-file -t b574f25` = commit ✓. The annex stack was subsequently ACCEPTED 2/2 by annex-pass #1 and #2 (shard 3, lines 2480–2487), which retroactively supplies the hostile arc this paragraph disclaims.

**DERIVATION:** Provenance record.

**RESOLUTION TRACE:** Base lines 1603–1615; the annex stack's own acceptance recorded at 2478–2487 (shard 3).

XREF: `lean/notes/openmath/HE7_passPE3_report.md:F-1` — grep-verified count **8**.
XREF: `lean/notes/openmath/HE7_passPE3_report.md:R-a` — grep-verified count **2**.
XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:ANNEX A` — count **5** (the pattern named; HE7's shorthand `HMENU3-ANNEX-A` has count **0** there — source defect 1).

**TEETH:** The PE3 probe (144/144, `.100`) and the annex leg (`.101`/`.102`).

---

### EFF.HE7.94  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1617–1633 — **the defect, as found at PE3**.

> “**The defect (as found at PE3).** THEOREM HE7.A(3) [r2] fires the
> α-refine at any slope λ₂ = u₂/ℓ₂ whose residual R_{λ₂} has a repeated
> irreducible factor r₂ with ℓ₂·deg r₂ = 1 — including MIXED residuals
> (the repeated linear factor shares its side with other classes, e.g.
> R_{λ₂} = (Z−a)²(Z−b)), first live at μ₂ = 3, i.e. n = 12, inside
> COROLLARY HE7.B(i)'s n = 12–15 sub-region, and vacuous at every
> machine-certified degree (μ₂ = 2 forces pure). But the lemmas the wiring
> cites there have pure-node hypotheses: LEMMA HE7-13 supposes "the single
> side of integer slope λ₂ … with residual R₂ = (Z − s₂)^{μ₂}", and LEMMA
> HE7-8's chain hypothesis likewise. HE7-13's conclusion-as-stated is
> genuinely FALSE at mixed nodes: PE3's constructed counter-instance
> (p, u, s, λ₂) = (5, 5, 1, 11), R₂ = (Z−1)²(Z−2), pins
> (0,33),(1,23),(2,11),(3,0), has post-refine polygon (0,34),(2,11),(3,0)
> — **the λ₂ = 11 side SURVIVES the refine**, carrying the b = 2 class
> (PARI σ = {(4,1),(8,1)}, the (4,1) factor = the undisturbed b-class).
> And §S6(iii)'s per-block sentence names only "several distinct REPEATED
> factors at one node", not a repeated factor mixed with simple ones.”

**CONDITIONALITY:** None — this is the note's own refutation of a claim in its frozen body. **It is the single most consequential honesty item in the HE7 stack**: an accepted (2/2) note records that one of its displayed lemmas' conclusions is FALSE outside its hypothesis, and that the *wiring* which invoked it was over-broad. **Scope: mixed nodes are first live at μ₂ = 3 (n = 12), inside COROLLARY HE7.B(i)'s own n ≤ 15 region, and vacuous at every machine-certified degree.**

**DERIVATION:** A constructed counter-instance, displayed with its pins and its post-refine polygon, and confirmed by PARI. `by` PE3's construction; re-run bit-identically at `.100`.

**RESOLUTION TRACE:** Base lines 1617–1633; the repair is `.95`–`.98`. Targets `EFF.HE7.14` (the over-broad wiring), `.45` (the pure-node lemma), `.51` (§S6(iii)'s narrow sentence), `.53`/`.54` (LEMMA HE7-8's chain hypothesis).

XREF: `lean/notes/openmath/HE7_passPE3_report.md:F-1` — count **8**.

**TEETH:** `he7_pe3_probe12.py` — 144 members, σ == PARI 144/144, “the counter-instance to the pure-node conclusion recorded”.

---

### EFF.HE7.95  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1635–1662 — **the two display sentences this annex riders**.

> “**The two display sentences this annex riders (named exactly; neither is
> edited).**
>
> 1. **THEOREM HE7.A(3), the [r2, HE7-PE1 F-1] wiring sentence** ("the
>    read AT the refined key Ψ − w (and at every iterate Ψ − W of the
>    chain) is licensed by **LEMMA HE7-12** (§S5.8) … and the strict slope
>    increase λ₂^{(0)} < λ₂^{(1)} < ⋯ that LEMMA HE7-8 consumes is
>    **LEMMA HE7-13**, derived, not assumed"). **Read as:** at a PURE node
>    (R_{λ₂} a power of Z − s₂ on a single side) — verbatim. At a MIXED
>    node, the citation routes through ANNEX-LEMMA HE7-13′ below: the node
>    is first split into its class blocks (clause (a)); the refine is the
>    α-refine OF THE REPEATED CLASS'S OWN BLOCK, whose node IS pure, so
>    LEMMAS HE7-12/HE7-13/HE7-8 apply to it verbatim; every other class is
>    read at its own block.
> 2. **§S6(iii)'s block sentence** ("*Several distinct repeated factors at
>    one node.* Then the classification above is applied **per distinct
>    factor**, each with its own block, by LEMMA HE6R1-2"). **Read as:**
>    "per distinct factor, REPEATED OR NOT — mixed nodes included";
>    ANNEX-LEMMA HE7-13′(a) is the displayed level-2 form of that block
>    split (proved from HE7-6/HE7-9/HE7-10/HE7-11, i.e. inside the §S5
>    package, so it transfers level-i by §S6's substitution table exactly
>    like every other §S5 item).
>
> LEMMA HE7-8's [r2] box ("the hypothesis set is the read's ACTUAL
> configuration, derived") and LEMMA HE7-12(d)'s [r3] parenthetical (the
> pairwise-distinct dv₂(w_i)) inherit the same reading: through HE7-13′
> their justifications route per block, where the displayed arguments
> apply verbatim (see "wiring" below). No other display is touched.”

**CONDITIONALITY:** **This unit is the supersession instruction itself.** Its four targets are all in shard 1: `EFF.HE7.14`, `.51`, `.54`, `.44`(d). **SUPERSESSION KIND: scope-pin** (the displays stay true; their *citation route* is re-directed) — not a wording replacement. The closing fence “No other display is touched” is a load-bearing scope limit on the whole annex.

**DERIVATION:** Rider instruction; its mathematical content is `.33` (ANNEX-LEMMA HE7-13′) and `.34` (the wiring).

**RESOLUTION TRACE:** Base lines 1635–1662; discharged at 1664–1816 (`.33`) and 1818–1855 (`.34`).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.
XREF: `lean/notes/openmath/HE7_passPE1_report.md:F-1` — count **4**.

**TEETH:** `.37`, `.38`, `.39`.

---

### EFF.HE7.96  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 1664–1727 — **ANNEX-LEMMA HE7-13′ (mixed residual nodes: the block split, and the per-class effect of one α-refine)**, clauses (a)–(e). Kept as ONE unit: five clauses, one hypothesis set, one proof (boundary audit §6 item 8).

> “**ANNEX-LEMMA HE7-13′ (mixed residual nodes: the block split, and the
> per-class effect of one α-refine).** Let Ψ̃ = Ψ − W with W = 0 or as in
> LEMMA HE7-12(d), and let f_S satisfy the standing convention at Ψ̃
> (Ψ̃ ∤ f_S), all roots level-2 points. Write P₂ for the polygon of f_S
> with respect to Ψ̃, and for each side of slope λ = u₂/ℓ₂ and each
> distinct monic irreducible r | R_λ let
>
>     C_{λ,r} := { ρ : f_S(ρ) = 0, dv₂(Ψ̃(ρ)) = λ,
>                  ι_ρ^{(2)}(r)(β_{2,ρ}) = 0 }
>
> (the level-2 label classes of COROLLARY HE7-7″; they partition the
> roots of f_S, since the label's factor is the minimal polynomial of
> β_{2,ρ} over ι^{(2)}(K₂)). Then:
>
> (a) *(the block split: a mixed node is a bouquet of PURE nodes)* each
> C_{λ,r} is nonempty (LEMMA HE7-10), Galois-stable (LEMMA HE7-11), and
> is the root set of a monic block factor f_{λ,r} ∈ O[x] with
> f_S = Π_{(λ,r)} f_{λ,r} and D″ℓ₂·deg r | deg f_{λ,r} (LEMMA HE7-6's
> argument with LEMMA HE7-5's forcing); the polygon of f_{λ,r} with
> respect to Ψ̃ is the SINGLE side of slope λ, of length
> L_{λ,r} := deg f_{λ,r}/D″, with Σ_{r | R_λ} L_{λ,r} = L_λ; and the
> residual of f_{λ,r} is c·r^{k} with c ∈ K₂^× and
> k = L_{λ,r}/(ℓ₂·deg r) ∈ ℤ_{≥1} — a single irreducible power. In
> particular THEOREM HE7.A's trichotomy applies to each block at its own
> (pure) node: at k = 1 the block's residual is separable (K₂ is a
> finite field) and HE7.A(2) decides the class, |C_{λ,r}| = D″ℓ₂ deg r,
> one irreducible factor of f with e = e₁ℓℓ₂, f = f₁d_r·deg r; at k ≥ 2
> with ℓ₂·deg r = 1 the block is the α-refine configuration and LEMMAS
> HE7-12/HE7-13/HE7-8 apply to it AS DISPLAYED; at k ≥ 2 with
> ℓ₂·deg r ≥ 2 the block passes to level 3, and the μ₂ ≥ 4 gate is
> unchanged: L_{λ,r} = k·ℓ₂ deg r ≥ 4, so μ₂ ≥ L_λ ≥ L_{λ,r} ≥ 4.
>
> Now fix a side of INTEGER slope λ₂ (ℓ₂ = 1) whose residual factors as
> R_{λ₂} = (Z − s₂)^{m₂}·R̂₂ with m₂ ≥ 2 and R̂₂(s₂) ≠ 0; s₂ ∈ K₂^×
> (s₂ ∈ K₂ since the factor is linear; s₂ ≠ 0 because the side's left
> endpoint is a vertex of P₂, so it attains and R_{λ₂}(0) ≠ 0 — the same
> mechanism as LEMMA HE7-13's "the endpoint j = 0 attains"). Let w be a
> (LIFT₂) polynomial at height λ₂ with residue s₂ (it exists: λ₂ > T₂
> satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w (covered by LEMMA
> HE7-12 with W + w, per (d)). Then, per class:
>
> (b) *(the refined class jumps — LEMMA HE7-13's conclusion, held by the
> refined class alone)* every ρ ∈ C_{λ₂, Z−s₂} has
> dv₂(Ψ̃^{(1)}(ρ)) > λ₂ (possibly = ∞);
>
> (c) *(companion classes on the same side persist EXACTLY, labels
> translated)* every ρ ∈ C_{λ₂,r₂} with r₂ ≠ Z − s₂ has
> dv₂(Ψ̃^{(1)}(ρ)) = λ₂ exactly, with residue
> β^{(1)}_{2,ρ} = β_{2,ρ} − ι_ρ^{(2)}(s₂) ≠ 0; its label at Ψ̃^{(1)} is
> (λ₂, r₂^τ) with r₂^τ(Z) := r₂(Z + s₂), monic irreducible of the SAME
> degree — so the λ₂ side SURVIVES the refine (this is exactly PE3's
> counter-instance to the pure-node conclusion), carrying the same
> companion classes;
>
> (d) *(strictly lower sides are untouched exactly)* every root with
> dv₂(Ψ̃(ρ)) = λ < λ₂ has dv₂(Ψ̃^{(1)}(ρ)) = λ exactly with the SAME
> residue, hence the same label;
>
> (e) *(steeper sides collapse onto λ₂)* every root with
> dv₂(Ψ̃(ρ)) = λ > λ₂ has dv₂(Ψ̃^{(1)}(ρ)) = λ₂ exactly with residue
> −ι_ρ^{(2)}(s₂), i.e. label (λ₂, Z + s₂) at Ψ̃^{(1)}. (The per-block
> wiring below never fires this clause — a block's refine happens at its
> own single side, with nothing steeper in the block; (e) is what
> governs, and refutes, the naive whole-f_S continuation.)”

**CONDITIONALITY:** **Annex grade — never hostile-passed as written** (`.93`), though the annex stack was later accepted 2/2 (shard 3). Rests on the standing convention at Ψ̃ (`EFF.HE7.09`, licensed by ANNEX-LEMMA R2-a, shard 3 — whose statement is explicitly extended to “any block factor f_C of ANNEX-LEMMA HE7-13′(a)”, and whose consumption rider (ii) supplies exactly the `Ψ̃ ∤ f_C` step this lemma's proof needs). Clause (a) transfers level-i by §S6's substitution table (`.32`). **Clause (e) is a refutation, not a tool**: the wiring never fires it.

**DERIVATION:** [ASSEMBLED — lines 1729–1816, verbatim]

> “*Proof.* Throughout, the §S5 package holds at Ψ̃ (LEMMA HE7-12(c); §S5
> itself when W = 0), so COROLLARY HE7-7″ gives every root of f_S its
> label, and — the one evaluation fact all four refine clauses share — by
> (LIFT₂)'s defining clause, at EVERY level-2 point ρ,
>
>     dv₂(w(ρ)) = λ₂  exactly, with res(w(ρ)/n₂(λ₂)(ρ)) = ι_ρ^{(2)}(s₂).
>
> (The PE3 charge asked that "the simple class's slots are untouched by w"
> be checked against LEMMA HE7-12's off-disk clause (a). Checked, and the
> mechanism is NOT slot disjointness: w moves the value landscape at every
> level-2 point equally — clause (a) governs only NON-level-2 points ξ,
> where it keeps dv₂(Ψ̃^{(1)}(ξ)) = dv₂(Ψ̃(ξ)) and hence the disk
> criterion. What protects the companion classes on-disk is RESIDUE
> SEPARATION, clause (c)'s calculation below: same value, different
> residue.)
>
> **(a).** The classes partition the roots (each root has exactly one
> label: its label factor is the minimal polynomial over K₂ of its residue
> root, via the field embedding ι_ρ^{(2)}). Each C = C_{λ,r} is
> Galois-stable by LEMMA HE7-11 — whose proof (an equivariance computation
> on Ψ̃, n₂ and ι) nowhere uses separability of R_λ — so
> f_C := Π_{ρ∈C}(x − ρ) has K₀-coefficients, integral over O, hence lies
> in O[x] and divides the separable f_S: LEMMA HE7-6's argument verbatim.
> Each Galois orbit in C has size e(L_ρ)f(L_ρ) with e₁ℓℓ₂ | e and
> f₁d_r·deg r | f (LEMMA HE7-5, whose proof consumes only the value group
> and the unit residue at ρ — no separability), so D″ℓ₂·deg r divides
> deg f_C. The reduction of §S5.5 applies to f_C exactly as to f_S (monic
> O-factor of f, every root a level-2 point, Ψ̃ ∤ f_C since Ψ̃ ∤ f_S), so
> LEMMAS HE7-9/HE7-10 and COROLLARY HE7-7″ run on f_C: every root of f_C
> has dv₂(Ψ̃(ρ)) = λ, and by LEMMA HE7-9(b) every slope of f_C's polygon
> carries D″·(its length) > 0 roots — so λ is the ONLY slope: the single
> side, of length L_C = deg f_C/D″ (LEMMA HE7-9(a) + THEOREM HE7.A(1)'s
> arithmetic on f_C give λ > T₂ and Σ_{slopes} L = L_C). Side lengths add:
> n_λ(f_S) = Σ_{r | R_λ}|C_{λ,r}| (the partition) with n_λ(f_S) = D″L_λ
> and |C_{λ,r}| = n_λ(f_{λ,r}) = D″L_{λ,r} (LEMMA HE7-9(b) on each), so
> Σ_r L_{λ,r} = L_λ. The residual: let R^{(C)} be the residual of f_C at
> its side. By LEMMA HE7-10 on f_C, every monic irreducible r′ | R^{(C)}
> has a nonempty class among f_C's roots, i.e. some ρ ∈ C has
> ι_ρ^{(2)}(r′)(β_{2,ρ}) = 0; but ι_ρ^{(2)}(r)(β_{2,ρ}) = 0 too, and both
> r, r′ are monic irreducible over K₂, i.e. both map to THE minimal
> polynomial of β_{2,ρ} over ι_ρ^{(2)}(K₂) — so r′ = r. Hence
> R^{(C)} = c·r^{k}; its degree is L_C/ℓ₂ (side of length L_C, slope
> denominator ℓ₂), so k = L_C/(ℓ₂·deg r) ∈ ℤ_{≥1}; c ≠ 0 is the top
> coefficient (the side's right endpoint is a vertex, so it attains). For
> the trichotomy sentence: at k = 1, R^{(C)} = c·r is separable
> (irreducible over the perfect field K₂) and THEOREM HE7.A(2) applies to
> f_C at Ψ̃ verbatim, giving the class size and the letters (LEMMA HE7-13's
> proof already notes its own hypothesis is insensitive to the
> normalization constant c, consuming only the residual's root set — the
> same is true of HE7.A(2)'s proof, which consumes r through its roots and
> degree); at k ≥ 2, ℓ₂ deg r = 1, the block's node is single-side,
> integer-slope, residual a pure power of Z − s with s ∈ K₂^× — LEMMA
> HE7-13's hypothesis EXACTLY (with the block's own μ₂ = L_C = k); at
> k ≥ 2, ℓ₂ deg r ≥ 2, the displayed level-3 branch of THEOREM HE7.A(3)
> applies to the block, and its gate is the displayed arithmetic:
> L_{λ,r} = k·ℓ₂ deg r ≥ 4 forces μ₂ = Σ_λ L_λ ≥ L_λ ≥ L_{λ,r} ≥ 4, so
> the μ₂ ≤ 3 non-propagation of HE7.A(3) — hence COROLLARY HE7.B(i)'s
> n ≤ 15 coverage — is unchanged by the block reduction.
>
> **(b).** ρ ∈ C_{λ₂,Z−s₂} means dv₂(Ψ̃(ρ)) = λ₂ with residue
> β_{2,ρ} = ι_ρ^{(2)}(s₂) (the minimal-polynomial reading of the label).
> So Ψ̃^{(1)}(ρ) = Ψ̃(ρ) − w(ρ) is a difference of two elements of the same
> dv₂ and the SAME residue — LEMMA HE7-13's own mechanism, per root —
> whence dv₂(Ψ̃^{(1)}(ρ)) > λ₂. ∎(b)
>
> **(c).** Here dv₂(Ψ̃(ρ)) = λ₂ with β_{2,ρ} ≠ ι_ρ^{(2)}(s₂) (the labels
> Z − s₂ and r₂ are distinct irreducibles, so their root sets are
> disjoint). Residues at a fixed height are additive (they are reductions
> of the n₂(λ₂)(ρ)-quotients), so Ψ̃^{(1)}(ρ)/n₂(λ₂)(ρ) has residue
> β_{2,ρ} − ι_ρ^{(2)}(s₂) ≠ 0, which forces dv₂(Ψ̃^{(1)}(ρ)) = λ₂ EXACTLY
> with that residue. The new label factor: ι_ρ^{(2)}(r₂)(β_{2,ρ}) = 0
> gives ι_ρ^{(2)}(r₂^τ)(β_{2,ρ} − ι_ρ^{(2)}(s₂)) =
> ι_ρ^{(2)}(r₂)(β_{2,ρ}) = 0 with r₂^τ(Z) = r₂(Z + s₂) monic irreducible
> of degree deg r₂ (translation is a K₂[Z]-automorphism), i.e. r₂^τ is the
> minimal polynomial of the new residue root: the label at Ψ̃^{(1)} is
> (λ₂, r₂^τ). Since these roots keep dv₂ = λ₂ and the package holds at
> Ψ̃^{(1)} (LEMMA HE7-12(c)(d) with W + w), LEMMA HE7-9(b) at Ψ̃^{(1)} puts
> them on a λ₂ side of the new polygon — the side survives. ∎(c)
>
> **(d).** dv₂(Ψ̃(ρ)) = λ < λ₂ = dv₂(w(ρ)): the ultrametric min is
> uniquely attained, so dv₂(Ψ̃^{(1)}(ρ)) = λ exactly; and w(ρ)/n₂(λ)(ρ)
> has strictly positive value, residue 0, so the residue at height λ is
> unchanged: β^{(1)}_{2,ρ} = β_{2,ρ}, same label. ∎(d)
>
> **(e).** dv₂(Ψ̃(ρ)) = λ > λ₂ = dv₂(w(ρ)): now Ψ̃(ρ)/n₂(λ₂)(ρ) has
> residue 0 and w(ρ)/n₂(λ₂)(ρ) has residue ι_ρ^{(2)}(s₂) ≠ 0, so
> dv₂(Ψ̃^{(1)}(ρ)) = λ₂ exactly with residue −ι_ρ^{(2)}(s₂), whose minimal
> polynomial is Z + s₂. ∎”

Justification tags: package at Ψ̃ `by EFF.HE7.44`(c); labels `by EFF.HE7.35`; the shared evaluation fact `by EFF.HE7.12`; (a)'s Galois/descent leg `by EFF.HE7.42` + `.36`; its forcing `by .29`; its single-slope and length arithmetic `by .41` + `.13`(1); its residual-uniqueness step `by .41` (HE7-10) + `definitional` (minimal polynomial); its trichotomy `by .13`(2), `by .45`, `by .14`; (b) `by .45`'s mechanism per root; (c) `computation` (residue additivity + translation automorphism) + `by .41`; (d)/(e) `computation` (ultrametric).

**RESOLUTION TRACE:** Base lines 1664–1816. Its `Ψ̃ ∤ f_C` step is licensed at 2380–2383 (ANNEX-LEMMA R2-a rider (ii), shard 3): “if gcd(Ψ̃, f_C) ≠ 1 then R2-a at F = f_C gives Ψ̃ | f_C | f_S, contradicting Ψ̃ ∤ f_S — one line, as predicted.”

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.

**TEETH:** `he7_pe3_probe12.py` (144/144, clause (c)'s surviving side observed) · `he7annex_supp.py` P2 (128/128 thread-entry parked residuals EXACT, i.e. clause (c) verified as an equality of polynomials), P3 (clause (b), 0 floor violations across 148 refines), P4 (clause (e)'s cycle exhibited as a tooth, 48/48), P5 (the mixed/pure boundary, 16/16).

---

### EFF.HE7.97  [fence]

**CANONICAL STATEMENT:** verbatim, lines 1818–1855 — **the wiring, and its three inherited consequences**.

> “**The wiring (how HE7.A(3)'s continuation reads at a mixed node).** At
> any node whose polygon has several sides or whose side residual has
> several distinct factors, split per clause (a) and continue PER BLOCK;
> each block's node is pure, so every displayed lemma applies verbatim
> there — HE7.A(2) at exponent 1; the α-refine with LEMMAS
> HE7-12/HE7-13/HE7-8 at a repeated K₂-rational linear power (the refine
> being an operation on the BLOCK's read: the block's next node is again
> read, split if mixed, and so on); the level-3 branch at
> ℓ₂·deg r ≥ 2. Three consequences, each inherited rather than new:
>
> * *Termination.* Along any path of this recursion the moves are: SPLIT
>   (≥ 2 blocks, so each block's degree strictly drops), PEEL (degree
>   drops by D″; at most μ₂ − 1 ever fire, the [r3] pigeonhole at LEMMA
>   HE7-8), REFINE (degree fixed; the refined-at slope strictly increases
>   — LEMMA HE7-13 at the pure node gives every next-polygon slope > λ₂,
>   and a subsequent block's single side IS one of those slopes), DECIDE /
>   LEVEL-3 (terminal for this ladder; level 3 is THEOREM HE7.D's problem,
>   gated at μ₂ ≥ 4 as shown in (a)). An infinite path therefore has an
>   infinite all-refine tail on a fixed polynomial at pure single-side
>   nodes with strictly increasing integer slopes — LEMMA HE7-8's
>   hypothesis set, derived, and refuted by LEMMA HE7-8 as displayed. So
>   the [r2] box on LEMMA HE7-8 ("the hypothesis set is the read's ACTUAL
>   configuration") now holds at mixed nodes too, THROUGH the block route.
> * *W ≠ 0 (LEMMA HE7-12(d) [r3]).* Along any path the increments'
>   values dv₂(w_i) are the refined-at slopes of THAT path, strictly
>   increasing by the previous bullet — pairwise distinct, so the [r3]
>   ultrametric-equality argument applies verbatim. (Distinct blocks'
>   chains live at DIFFERENT keys and never mix increments.)
> * *The naive whole-f_S continuation is REFUTED, not merely unproved.*
>   Clause (e) shows a refine drags every steeper class down to λ₂ with
>   residue −ι(s₂). At ONE repeated class per side (all 144 PE3-probe
>   members) the sequential whole-key route never revisits λ₂ and
>   coincides with the block route; at TWO repeated classes on one side
>   (R_{λ₂} = (Z−a)²(Z−b)², first live at μ₂ = 4) the sequential route
>   oscillates FOREVER between the two classes at the same slope λ₂ (each
>   class's decided position is dragged back by the other's refine — the
>   annex leg's T4 tooth exhibits the cycle). The per-class discipline is
>   load-bearing, not stylistic.”

**CONDITIONALITY:** Annex grade. **The Termination bullet is the discharge of `EFF.HE7.54`** and the W ≠ 0 bullet the discharge of `.44`(d) at mixed nodes. **The third bullet is a REFUTATION with a machine witness**: the naive whole-key continuation cycles forever at two repeated classes on one side, first live at μ₂ = 4 (n = 16), and the annex leg's P4 tooth exhibits it 48/48.

**DERIVATION:** A four-move termination argument (SPLIT / PEEL / REFINE / DECIDE-or-LEVEL-3) with a degree or slope monovariant on each, reducing an infinite path to LEMMA HE7-8's own hypothesis set. `by EFF.HE7.96`(a)(b)(e) + `by EFF.HE7.53`/`.55` (the pigeonhole) + `by EFF.HE7.45`.

**RESOLUTION TRACE:** Base lines 1818–1855; the refutation's witness at 1935–1937 (`.39`, P4).

**TEETH:** `he7annex_supp.py` P4 (**48/48 — the naive single-key route CYCLES on every two-repeated-class member**, cap 24 hit with every refine stuck at λ₂) · P3 (0 floor violations across 148 refines).

---

### EFF.HE7.98  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1857–1865 — **Remark R-a's disposition**.

> “**Remark R-a's disposition (folded per the PE3 report).** A SIMPLE
> factor r₂′ of an inseparable R_{λ₂} — decided by neither HE7.A(2)
> (whole-residual separability hypothesis) nor HE7.A(3) (which speaks of
> the repeated factor) — is decided at its own block by clause (a): the
> block's residual is c·r₂′^{k}, and at k = 1 (every machine-observed
> case) THEOREM HE7.A(2) applies to the block AT THE CURRENT KEY, no
> refine needed — "the simple class's side persists" is clause (c), and
> its persistence is bookkeeping, not a prerequisite: the block never sees
> w at all.”

**CONDITIONALITY:** **This closes a genuine gap between THEOREM HE7.A's clauses (2) and (3)** — a simple factor sitting on an inseparable residual's side is decided by neither as written. The disposition is unconditional at `k = 1`; at `k ≥ 2` the block falls into clause (a)'s trichotomy like any other. **“(every machine-observed case)” is an observation, not a hypothesis** — `.99`'s honesty box declines the `k = m` link that would make `k = 1` predictable from the multiplicity.

**DERIVATION:** `by EFF.HE7.96`(a) (the block's residual is `c·r₂′^k`) + `by EFF.HE7.13`(2) at the block's own pure node.

**RESOLUTION TRACE:** Base lines 1857–1865; witnessed at 1939–1941 (`.39`: “The R-a route fired 32× (config B's simple class decided at the ORIGINAL key, before any refine — "the block never sees w")”).

XREF: `lean/notes/openmath/HE7_passPE3_report.md:R-a` — count **2**.

**TEETH:** `he7annex_supp.py` — the R-a route fired **32×** on config B.

---

### EFF.HE7.99  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1867–1881 — **the annex's honesty box**.

> “**Honesty box (BOX-4-adjacent; what this annex does NOT claim).** The
> link between the multiplicity m of r in R_{λ₂}(f_S) and the block
> exponent k (equivalently the block length L_{λ,r} = k·ℓ₂ deg r) is NOT
> claimed — it is HE7-BOX-4's declined product link one step over
> (residual multiplicativity over the block factorization would give
> k = m; the note declines the family). The read never consults m: it
> computes each block's own node and applies the trichotomy THERE, and
> every emitted letter is unconditionally correct (an HE7.A(2) instance at
> its own key, licensed by LEMMA HE7-12(c)); the exponent question affects
> only WHICH branch fires. Machine: k = m at every observed member (the
> 144 PE3-probe members and the annex leg below; e.g. the parked
> (Z−(b−a))² side at the annex configurations — exponent 2 = multiplicity
> 2). Likewise not claimed: L_{C_{λ₂,Z−s₂}} ≥ 2 — if the repeated class's
> block has length 1 it is separable-decided and no refine fires there,
> harmlessly.”

**CONDITIONALITY:** Standing. **This is HE7-BOX-4 (`.73`) restated one level over**, and it is the DAG's density-side boundary at the block level. The mitigating argument — “the exponent question affects only WHICH branch fires”, every emitted letter being an HE7.A(2) instance at its own key — is what keeps the declined link from being load-bearing for σ. The `k = m` observation is machine-universal on 240 members and is explicitly **not** promoted to a claim.

**DERIVATION:** Declined-claim record with a correctness argument for why the declension is harmless: `by EFF.HE7.96`(a) (each block's own node is computed, not inferred from m) + `by EFF.HE7.13`(2) + `.44`(c).

**RESOLUTION TRACE:** Base lines 1867–1881; the parent box at 1327–1341 (`.10`, `.11`); the observation witnessed at 1946 (`.39`).

**TEETH:** Observation only: `k = m` at every observed member (144 + 96 = 240). **No tooth tests the link as a claim, because it is not claimed.** Disposition: **signed non-applicability.**

---

### EFF.HE7.100  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1885–1896 — machine record 1, the PE3 probe.

> “1. *The PE3 probe (committed at b574f25, cited as this annex's primary
>    machine record):* `verification/openmath/he7_pe3_probe12.py` — 144
>    members (96 mixed (Z−a)²(Z−b) nodes at μ₂ = 3, n = 12, plus 48 pure
>    cubes), derived top-first continuation, **σ == PARI 144/144, 0
>    violations**, first machine contact of any μ₂ ≥ 3 refine, 2-step
>    chains included; the counter-instance to the pure-node conclusion
>    recorded. Re-run for this annex in an isolated sandbox
>    (`/tmp/he7_annex_sandbox`, committed artifacts untouched):
>    **bit-identical GREEN — 144/144, results-JSON leaf-diff vs the
>    committed artifact EMPTY (even the 5.3 s timing leaf reproduced);
>    artifact md5s at annex time: runner 61d9f81cea79…, results
>    dfd9fe2342b8…, output 710a31d1ca28… — all byte-frozen.**”

**CONDITIONALITY:** **This is the verifier's own instrument, not the author's** — the strongest decorrelation available inside HE7's stack short of a foreign model. The bit-identical re-run (including the timing leaf) is a reproducibility claim of unusual strength. `git cat-file -t b574f25` = commit ✓; all three artifacts exist on disk.

**DERIVATION:** Machine record.

**RESOLUTION TRACE:** Base lines 1885–1896; the oracle's identity later qualified at 2490 (M-A, shard 3): the deg-16 legs' `factorpadic` is the shared `pari_sigma16`. **M-A names “the three stack legs (ANNEX F-1's, R1.3's, annex-pass #1's fresh leg)”, so THIS leg's oracle is covered by that qualification.**

**TEETH:** One row: 144/144 at μ₂ = 3, n = 12, with 2-step chains — the first machine contact of any μ₂ ≥ 3 refine.

---

### EFF.HE7.101  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1897–1923 — machine record 2, the annex leg and its preregistered predictions.

> “2. *The annex leg (additive, new file; every sealed artifact
>    byte-frozen):* `verification/openmath/he7annex_supp.py`, the first
>    machine contact of TWO repeated classes at one side and of any
>    μ₂ = 4 (n = 16) refine. Frame = the sealed battery's (2,1,1),
>    Φ′ = x² − p, u = 5, T₂ = 10; deg f = 16, μ₂ = 4; p ∈ {5,7},
>    s ∈ {1,2}, λ₂ ∈ {11,12}. Configurations: (A) R₂ = (Z−a)²(Z−b)²
>    (two repeated classes), read by the PER-CLASS route — each class
>    refined from the node's OWN key Ψ̃ (thread a: Ψ̃ − w_a; thread b:
>    Ψ̃ − w_b), each thread continued on its own > λ₂ sides (the block's
>    data read off f_S itself: the parked classes sit at dv₂ = λ₂
>    exactly, contributing a constant to h_{F₂} above λ₂ — LEMMA
>    HE6R1-2's translation mechanism); (B) R₂ = (Z−a)³(Z−b) (repeated
>    class of multiplicity 3 + parked simple, one-thread sequential —
>    the probe's mechanism at μ₂ = 4); (C) pure controls (Z−a)⁴.
>    Preregistered predictions: **P1** σ == PARI member-by-member, both
>    configurations + controls; **P2** at each thread's entry refine the
>    λ₂ side persists with the translated residual EXACTLY (clause (c):
>    config A: c(Z−(b−a))² of length 2 at thread a, symmetrically at
>    thread b; config B: c(Z−(b−a)) of length 1 at the final chain key);
>    **P3** per-thread refined-at slopes strictly increase (clause (b) +
>    LEMMA HE7-13 at the pure sub-nodes); **P4 (tooth)** the naive
>    single-key sequential route (the probe's own selection rule) FAILS
>    on every config-A member — refine-cap hit with the λ₂ slope
>    revisited (the cycle of clause (e)); **P5 (tooth)** on pure controls
>    the λ₂ side does NOT survive (LEMMA HE7-13 as displayed) — the
>    mixed/pure boundary is real. Verdict to be appended below from the
>    committed artifacts after the sealed run.”

**CONDITIONALITY:** **Preregistered** — the five predictions were written before the run, and the run record (`.102`) reports against them. **The block-data mechanism it uses (“the parked classes sit at dv₂ = λ₂ exactly, contributing a constant to h_{F₂} above λ₂ — LEMMA HE6R1-2's translation mechanism”) is exactly the mechanism whose scalar clause is corrected twice from shard 3** (`EFF.HE7.39`); the corrections are scale-only and the leg reads degrees/roots, so nothing moves. **Note the frame: p ∈ {5,7}, no characteristic 2, no char-p rows at all.**

**DERIVATION:** Preregistration; each prediction names the clause of `.33` it tests.

**RESOLUTION TRACE:** Base lines 1897–1923; verdict at 1925–1946.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — count **8**.

**TEETH:** P1–P5; P4 and P5 are planted mutants. Rows in §5.

---

### EFF.HE7.102  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 1925–1946 — the annex leg's run record.

> “**[run record, 2026-08-09, from the committed artifacts] GREEN — 96
>    members, σ == PARI 96/96, 0 violations, 0 level-3 skips, 3.5 s**
>    (`he7annex_supp_output.txt`, `he7annex_supp_results.json`): 48
>    config A + 32 config B + 16 pure controls over the 8 rows; 148
>    refines; the first machine σ at n = 16 (letters include {(16,1)},
>    {(4,1),(12,1)}, {(8,1),(8,1)}, {(4,2),(4,2)}). Predictions: **P1 ✓**
>    96/96 with Σef = 16; **P2 ✓** 128/128 thread-entry parked residuals
>    EXACT (config A: the monic (Z−(b−a))² of length 2 at BOTH threads;
>    config B: (Z−(b−a)) of length 1), plus 132 persistent clause-(c)
>    checks green along the chains; **P3 ✓** 0 floor violations across
>    all 148 refines; **P4 ✓ 48/48 — the naive single-key route CYCLES
>    on every two-repeated-class member** (cap 24 hit with every refine
>    stuck at λ₂; the disclosed smoke member: 24 of 24 refines at λ₂);
>    **P5 ✓** 16/16 pure controls lose the λ₂ side (LEMMA HE7-13 as
>    displayed) while every mixed member RETAINS it. The R-a route fired
>    32× (config B's simple class decided at the ORIGINAL key, before
>    any refine — "the block never sees w"). Disclosures: the sealed
>    smoke found no logic defect; ONE pre-run instrument change is
>    disclosed in the runner docstring (the σ oracle's nfinit p-maximal
>    hint for deg-16 tractability; both oracles cross-checked identical
>    on the smoke member); the exponent observation k = m held on every
>    member (the honesty box's disclosure line).”

**CONDITIONALITY:** All five predictions confirmed. **Compiler arithmetic check:** 48 + 32 + 16 = **96** ✓; the R-a route's 32 firings equal config B's member count ✓. **“0 level-3 skips”** is the sentence ANNEX R R1.3 later cites as evidence that this leg never reached level 3 — “its nodes never carried ℓ₂·deg r₂ ≥ 2 repeated factors” — motivating the constructed level-3 family (shard 3). **The disclosed pre-run instrument change** (the nfinit p-maximal hint) is the first appearance of the oracle whose identity M-A later corrects to `pari_sigma16`.

**DERIVATION:** Machine record against preregistered predictions.

**RESOLUTION TRACE:** Base lines 1925–1946; the “0 level-3 skips” consumed at 2264–2267 (shard 3); the oracle identity corrected at 2490 (M-A, shard 3).

**TEETH:** Five rows (P1–P5) in §5.

---

### EFF.HE7.103  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1948–1959 — **HE7-BOX-1 (arc record) — dated APPEND (2026-08-09)**.

> “**HE7-BOX-1 (arc record) — dated APPEND (2026-08-09).** This line
> continues the [r1]/[r2]/[r3] record inside HE7-BOX-1 (§S9); under the
> acceptance freeze it cannot be inserted there, so it lives here:
> **PE3 HAS NOW RUN (report `HE7_passPE3_report.md`, 111ac7f): CLEAN — 0
> CRITICAL, 0 GAP, 1 MINOR (F-1, this annex's subject; R-a folded);
> machine leg bit-identical GREEN plus two fresh legs (780/780 f₁ = 2
> unramified family; 144/144 mixed-residual probe). The 2-clean count
> completed 1/2 → 2/2: HE7 IS ACCEPTED — the first stage-one note through
> the hostile-arc bar. The text is frozen at the accepted body; this
> dated annex discharges the owed F-1 rider (ANNEX-LEMMA HE7-13′ +
> the block reading of HE7.A(3)/§S6(iii) + the R-a disposition), edits
> nothing above, and moves no sealed number.**”

**CONDITIONALITY:** **This is the acceptance of record for the body**, and it is subsequently **ANNOTATED (not revoked)** by ANNEX R's BOX-1 append (shard 3, ratification CHALLENGE, 5 findings), then closed by the final dated line (annex stack ACCEPTED 2/2, CHALLENGE discharged, note FULLY FROZEN). **Note the fresh leg not otherwise inventoried in this note: “780/780 f₁ = 2 unramified family” — this is the ONLY appearance of an f₁ = 2 machine family anywhere in HE7's record, and it is reported without a runner filename.** HE7-BOX-2's coverage list (`.70`, `.71`) still says “f₁ ≥ 2 stage genres” are unexercised. Recorded as OPEN-CALL 2.

**DERIVATION:** Arc record. `git cat-file -t 111ac7f` = commit ✓.

**RESOLUTION TRACE:** Base lines 1948–1959; continued at 2442–2462 and 2493–2497 (shard 3).

XREF: `lean/notes/openmath/HE7_passPE3_report.md:F-1` — count **8**.
XREF: `lean/notes/openmath/HE7_passPE3_report.md:R-a` — count **2**.

**TEETH:** PE3's own legs (780/780 f₁ = 2 unramified; 144/144 mixed-residual probe = `.100`).

---

### EFF.HE7.104  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 1961–1969 — ANNEX F-1's closing **What does not move**.

> “**What does not move.** Every displayed statement and proof of the
> frozen body; every sealed artifact and pin of §S10/§S11 (byte-frozen
> md5s re-verified above); THEOREM HE7.A at pure nodes and everywhere at
> μ₂ ≤ 2 (mixed nodes need μ₂ ≥ 3); the n = 8 closure §S8 (μ₂ = 2, all
> nodes pure — the dictionary is untouched); COROLLARY HE7.B's grade
> sentences; THEOREM HE7.C/HE7.D and the μ₂ ≥ 4 level-3 gate (re-derived
> per block in clause (a) with the same arithmetic); every box HE7-BOX-1…5
> as written, HE7-BOX-4 in particular (this annex leans on its declined
> link NOWHERE, per the honesty box).”

**CONDITIONALITY:** None; this is the annex's own blast-radius declaration and the compiler's warrant for leaving `EFF.HE7.13`, `.15`, `.57`–`.62` unriddered. **One item on the list is later contradicted in part**: “THEOREM HE7.C/HE7.D … re-derived per block in clause (a) with the same arithmetic” holds for the μ₂ ≥ 4 GATE, but THEOREM HE7.D itself is later found unproved as displayed at level ≥ 3 (Codex F1) and re-proved only at ANNEX R. **The two statements are compatible** — ANNEX F-1's claim is that IT does not move HE7.D, not that HE7.D is sound — but a chapter cut reading this list alone would draw the wrong conclusion. Flagged.

**DERIVATION:** Blast-radius declaration, item by item.

**RESOLUTION TRACE:** Base lines 1961–1969; the HE7.D item overtaken at 1990–2253 (ANNEX R R1, shard 3).

**TEETH:** NONE (a negative declaration).

---

### EFF.HE7.105  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the ANNEX R heading (line 1973) and its Provenance-and-scope paragraph (1975–1988), both verbatim]

> “## ANNEX R (2026-08-09, post-ratification; CODEX F1-F5)”

> “**Provenance and scope.** The ratification sweep's Codex leg
> (`CODEX_HE7RAT_2026-08-09.md`, session 019fe4c6-4ae2-7053-95f9-d5c5cc0d58d1,
> gpt-5.6-sol at HIGH, fresh context) returned **5 findings, all 5 CONFIRMED
> at adjudication — RATIFICATION OUTCOME: CHALLENGE**: F1 (CRITICAL as stated,
> scoped to §S6/DEFINITION HE7-2/THEOREM HE7.D/COROLLARY HE7.B(ii)), F2 (GAP
> as stated at the §S1 CONVENTION; grade flagged for Asvin), F3 (regraded
> wording-MINOR), F4/F5 (MINOR). This annex executes the fold note's repair
> queue R1–R5 in order. The accepted body above (through ANNEX F-1) is
> BYTE-FROZEN — md5 verified identical before and after this append — and
> per the annex pattern nothing above is edited: each repair is stated as a
> dated annex definition/lemma/rider naming its exact target. Honesty of
> grade: this annex is a post-ratification append and has NOT itself been
> through a hostile pass; R1's re-proof is at annex grade (the core displays
> are full proofs; the package step is a transfer audit of §S6's own kind).”

**CONDITIONALITY:** **This is the terminal effective-text rule for the whole note** (header (i)). Its own honesty clause — “has NOT itself been through a hostile pass” — became false at `.127` (annex-pass #1 and #2, both CLEAN, annex stack ACCEPTED 2/2), and the sentence is not edited because of the freeze. **The five findings were produced by a DECORRELATED MODEL in a fresh context** (gpt-5.6-sol at HIGH), which is the campaign's standing decorrelation instrument and is the reason F1 — a CRITICAL that four in-house hostile passes had missed — was found at all.

**DERIVATION:** Provenance record.

**RESOLUTION TRACE:** Base lines 1973–1988. The honesty clause overtaken at 2480–2487 (`.127`). The five findings' repairs: F1 at `.106`–`.117`, F2 at `.118`–`.121`, F3 at `.122`, F4 at `.123`, F5 at `.124`.

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F1` — grep-verified count **4**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F2` — grep-verified count **7**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F3` — grep-verified count **3**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F4` — grep-verified count **5**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F5` — grep-verified count **3**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:019fe4c6-4ae2-7053-95f9-d5c5cc0d58d1` — grep-verified count **2** (the session pin).

**TEETH:** The Codex pass IS the tooth — a decorrelated model on a fresh context, five findings, five confirmed at adjudication. Its own machine leg is `.116`/`.117`.

---

### EFF.HE7.106  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 1992–2011 — **R1.0, the defect, exactly**.

> “**R1.0 The defect, exactly.** DEFINITION HE7-2 displays the normalizer
> recursion `n_{i+1}(k) := n_i(m)·Φ_i^s (ℓ_i m + s u_i = k, 0 ≤ s < ℓ_i)`
> AND lists "n₁ = ϖ-powers" among the level-0 datum's outputs. The two are
> incompatible. At i = 0 the recursion (from any base n₀ — the level-0 datum
> declares none) gives n₁(k) = n₀(m)·x^{s(k)} with x-degree s(k) < e₁, while
> ϖ^k = x^{i₀k}π^{a₀k} has x-degree i₀k ≥ e₁ for k ≥ e₁ whenever i₀ ≥ 1 —
> equality is impossible regardless of n₀. Codex's witness: (e₁,h) = (2,3),
> k = 3, so i₀ = 1, a₀ = −1, ϖ = xπ^{−1}; the recursion's 2m + 3s = 3 with
> 0 ≤ s < 2 gives (m,s) = (0,1), hence n₁(3) = x, while ϖ³ = x³π^{−3}; the
> quotient ϖ³/n₁(3) = x²π^{−3} has dv = 0 and residue η_ξ ≠ 0 — generically
> ≠ 1 (the RIDER twist of §S4.1). So the recursive system and the claimed
> ϖ-power base are two DIFFERENT normalizer systems differing by a live
> twist, and §S6's "with the SAME proofs" had no coherent normalizer/cocycle
> convention: THEOREM HE7.D's proof was unproved as displayed. Because
> 𝒫_{i+1}'s defining letter β_{i,ξ} = res(Φ_i(ξ)^{ℓ_i}/n_i(u_i)(ξ)) is read
> THROUGH the normalizer system, the incoherence also left the level-(i+1)
> letters coordinate-ambiguous for i ≥ 2. Scope (adjudicated): the level-2
> core §S1–S5, §S7, §S8, THEOREM HE7.A/HE7.A′/HE7.C, COROLLARY HE7.B(i) and
> the whole machine record do NOT consume DEFINITION HE7-2 (§S1 defines n₂
> directly); first live at level 3, i.e. n ≥ 16.”

**CONDITIONALITY:** None — this is a refutation with a displayed witness. **It is the strongest honesty item in the entire note: an ACCEPTED 2/2 note recording that one of its four headline theorems “was unproved as displayed”.** The scope sentence is what confines the damage, and it is the compiler's warrant for leaving the level-2 core unriddered everywhere.

**DERIVATION:** A displayed incompatibility argument plus an explicit numeric witness. The general argument is a degree count in `x`: the recursion's `n₁(k)` has `x`-degree `s(k) < e₁` while `ϖ^k` has `x`-degree `i₀k ≥ e₁` for `k ≥ e₁` when `i₀ ≥ 1` — `computation`. The witness `(e₁,h) = (2,3)`, `k = 3` is verified inline: `i₀ = 1`, `a₀ = −1` (so `i₀h + e₁a₀ = 3 − 2 = 1` ✓), `2m + 3s = 3` with `0 ≤ s < 2` gives `(m,s) = (0,1)` ✓, `n₁(3) = x`, `ϖ³ = x³π^{−3}`, quotient `x²π^{−3}` with `dv = e₁v` giving `2·(−3) + 2·3 = 0` ✓ — **compiler-recomputed, all four steps check.**

**RESOLUTION TRACE:** Base lines 1992–2011. Targets `EFF.HE7.47` (DEFINITION HE7-2), `.17`/`.48` (THEOREM HE7.D), `.16`(ii) (COROLLARY HE7.B(ii)), `.14` (HE7.A(3)'s level-3 branch). Repaired at 2013–2253.

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F1` — count **4**.

**TEETH:** No tooth found this defect and none could have: it is a coherence defect in a definition, invisible to a σ-agreement battery. **Found by a decorrelated model.** The repaired system is exercised at `.13`.

---

### EFF.HE7.107  [definition]

**CANONICAL STATEMENT:** verbatim, lines 2013–2037 — **ANNEX-DEF HE7-2′ (the corrected level recursion)**.

> “**ANNEX-DEF HE7-2′ (the corrected level recursion; replaces DEFINITION
> HE7-2's normalizer line and base sentence, everything else unchanged).**
> The normalizer system of a level ladder is defined by
>
>     BASE (level 1):   n₁(k) := ϖ^k   (k ∈ ℤ),
>     RECURSION (i ≥ 1): n_{i+1}(k) := n_i(m_i(k))·Φ_i^{s_i(k)},
>                        ℓ_i·m_i(k) + s_i(k)·u_i = k,  0 ≤ s_i(k) < ℓ_i
>
> (possible and unique because gcd(u_i, ℓ_i) = 1). Attached objects, for
> i ≥ 1:
>
> * **the level-(i+1) letter** Λ_i := Φ_i^{ℓ_i}/n_i(u_i), with
>   β_{i,ξ} := res(Λ_i(ξ)) at every level-(i+1) point ξ (well defined by
>   ANNEX-LEMMA R1-a(i) below); at i = 1, Λ₁ = Φ′^ℓ/ϖ^u — §S1's letter;
> * **the level-i cocycle** τ_i(a,b) := n_i(a)·n_i(b)/n_i(a+b), a Laurent
>   monomial in ϖ, Φ₁, …, Φ_{i−1} with O-coefficients;
> * **the transport tower** ι_ξ^{(1)} := ι_ξ and ι_ξ^{(i+1)} := the
>   ι_ξ^{(i)}-semilinear embedding K_{i+1} → k̄ with β_i ↦ β_{i,ξ}
>   (well defined because β_{i,ξ} is a root of the irreducible
>   ι_ξ^{(i)}(r_i)); in particular ι_ξ^{(i+1)}|_{K_i} = ι_ξ^{(i)}.
>
> At i = 1 the recursion reproduces §S1's n₂(k) = ϖ^{m(k)}Φ′^{s(k)}
> verbatim, and the transport tower reproduces DEFINITION HE7-1's ι^{(2)}:
> **levels 1 and 2 are byte-unchanged.** The base is a DEFINITION, not a
> recursion output — this is the whole correction.”

**CONDITIONALITY:** **SUPERSESSION KIND: replacement**, scoped exactly — “replaces DEFINITION HE7-2's normalizer line and base sentence, everything else unchanged”. Target: `EFF.HE7.47`. **Annex grade** (`.01`, `.11`). Its self-consistency claim (“levels 1 and 2 are byte-unchanged”) is what protects `EFF.HE7.06`, `.08`, `.11` and the whole machine record; it is discharged by R1-a(iv) (`.04`).

**DERIVATION:** Definition. The existence/uniqueness clause is Bézout at `gcd(u_i, ℓ_i) = 1`; the well-definedness of `β_{i,ξ}` and of the transport tower is deferred to R1-a(i) and to irreducibility of `ι_ξ^{(i)}(r_i)`; the level-1/2 reproduction claim is verified at R1-a(iv). **Compiler check of the i = 1 instance:** `n₂(k) = n₁(m₁(k))·Φ₁^{s₁(k)} = ϖ^{m(k)}Φ′^{s(k)}` with `ℓm(k) + s(k)u = k`, `0 ≤ s(k) < ℓ` — byte-identical to DEFINITION HE7-1's display ✓.

**RESOLUTION TRACE:** Base lines 2013–2037. Coherence proved at 2039–2091 (`.04`); consumed by `.06`, `.07`, `.09`, `.10`, `.12`. Targets `EFF.HE7.47`.

**TEETH:** `he7rannex_supp.py` runs “the CORRECTED HE7-2′ chain — n₃(k) = n₂(m₂(k))·Ψ^{s₂(k)} with the τ₂-cocycle carried per R1-a”, 79/79 (`.13`).

---

### EFF.HE7.108  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 2039–2065 — **ANNEX-LEMMA R1-a (the cocycle is a letter monomial — the level-i twist group)**.

> “**ANNEX-LEMMA R1-a (the cocycle is a letter monomial — the level-i
> twist group).** For every i ≥ 1 and all a, b, k ∈ ℤ:
>
> (i) n_i(0) = 1, and at every level-i point ξ, w_i(n_i(k)(ξ)) = k
> EXACTLY; consequently Λ_i(ξ) has w-value 0 at every level-(i+1) point
> and β_{i,ξ} ≠ 0 is well defined.
>
> (ii) τ₁ ≡ 1, and for i ≥ 1, with c := c_i(a,b) :=
> (s_i(a) + s_i(b) − s_i(a+b))/ℓ_i ∈ {0, 1},
>
>     τ_{i+1}(a,b) = Λ_i^{c} · τ_i(m_i(a), m_i(b))
>                          · τ_i(m_i(a) + m_i(b), c·u_i) .        (R1.1)
>
> (iii) Hence τ_i(a,b) = Π_{1≤j<i} Λ_j^{e_j(a,b)} with explicit integer
> exponents e_j determined by the s-bookkeeping alone (independent of any
> polynomial being read); at every level-i point ξ, τ_i(a,b)(ξ) has
> w-value 0 and residue
>
>     res( τ_i(a,b)(ξ) ) = ι_ξ^{(i)}( Π_{1≤j<i} β_j^{e_j(a,b)} )
>                        ∈ ι_ξ^{(i)}(K_i^×) ,
>
> the transport of a FIXED nonzero element of K_i, independent of ξ.
>
> (iv) At i = 2, (R1.1) gives τ₂(a,b) = Λ₁^{c₁(a,b)} — exactly §S1's
> CONVENTION display with its integer c. The twist is trivial at level 1,
> a single-letter power at level 2, and a genuine multi-letter monomial
> first at level 3 — which is why nothing at n ≤ 15 moves.”

**CONDITIONALITY:** Annex grade, but a **full displayed proof** (`.115`: “R1-a/R1-b/R1-c are full displayed proofs”). **Clause (iv) is the load-bearing compatibility statement**: it identifies τ₂ with §S1's CONVENTION display, sharpening that display's `c ∈ ℤ` to `c ∈ {0,1}` without contradicting it, and it is the reason “nothing at n ≤ 15 moves”. Clause (iii) is the twist-blindness engine consumed throughout R1.2. **Consumed out of range** by the dated line at `.136`/`.137`, which uses R1-a(iii)(iv) to compute the corrected §S5.5 scalar.

**DERIVATION:** [ASSEMBLED — lines 2067–2091, verbatim]

> “*Proof.* **(i)** n₁(0) = ϖ⁰ = 1 and m_i(0) = s_i(0) = 0 give n_i(0) = 1
> by induction. Values: dv(ϖ(ξ)) = 1 exactly at every (T1)/(T2) point (§S1),
> so w₁(n₁(k)(ξ)) = k; inductively, at ξ ∈ 𝒫_{i+1} ⊆ 𝒫_i,
> w_{i+1}(n_{i+1}(k)(ξ)) = ℓ_i·w_i(n_i(m_i(k))(ξ)) + s_i(k)·w_{i+1}(Φ_i(ξ))
> = ℓ_i·m_i(k) + s_i(k)·u_i = k, using w_{i+1} = ℓ_i·w_i and 𝒫_{i+1}'s
> defining clause w_{i+1}(Φ_i(ξ)) = u_i. For Λ_i: w_{i+1}(Φ_i^{ℓ_i}(ξ)) =
> ℓ_i u_i = w_{i+1}(n_i(u_i)(ξ)) (the latter = ℓ_i·w_i(n_i(u_i)(ξ)) =
> ℓ_i·u_i), difference 0.
> **(ii)** τ₁ ≡ 1 because k ↦ ϖ^k is a homomorphism — THE point of the
> re-based system. For i ≥ 1: s_i(a) + s_i(b) − s_i(a+b) lies in
> (−ℓ_i, 2ℓ_i) and is ≡ 0 mod ℓ_i, so it is 0 or ℓ_i, i.e. c ∈ {0,1};
> applying ℓ_i·(·) + u_i·(s-identity) = 0 gives
> m_i(a) + m_i(b) = m_i(a+b) − c·u_i. Expand, writing A := m_i(a),
> B := m_i(b):
> τ_{i+1}(a,b) = [n_i(A)n_i(B)/n_i(m_i(a+b))]·Φ_i^{cℓ_i}
> = τ_i(A,B)·[n_i(A+B)/n_i(A+B+cu_i)]·Φ_i^{cℓ_i}
> = τ_i(A,B)·τ_i(A+B, cu_i)·Φ_i^{cℓ_i}/n_i(cu_i),
> and Φ_i^{cℓ_i}/n_i(cu_i) = Λ_i^c for c ∈ {0,1} (at c = 0 both sides are
> 1 by (i); at c = 1 it is the definition of Λ_i).
> **(iii)** Induction on i via (R1.1), base τ₁ ≡ 1. The w-value is 0 by (i)
> (w_i(τ_i(a,b)(ξ)) = a + b − (a+b) = 0). The residue: each letter Λ_j,
> j < i, has residue β_{j,ξ} = ι_ξ^{(j+1)}(β_j) at every level-(j+1) point,
> hence at every level-i point (𝒫_i ⊆ 𝒫_{j+1}), and
> ι_ξ^{(j+1)} = ι_ξ^{(i)}|_{K_{j+1}} by the transport tower; multiply.
> **(iv)** τ₂(a,b) = Λ₁^{c}·τ₁(·,·)·τ₁(·,·) = Λ₁^{c}. ∎”

Justification tags: (i) `by EFF.HE7.05` (`dv(ϖ(ξ)) = 1` at (T1)/(T2) points) + induction on the recursion of `.03`; (ii) `computation` (the `c ∈ {0,1}` range argument, then a monomial expansion) — **the key structural fact is `τ₁ ≡ 1`, i.e. the re-based level-1 system is a homomorphism, which is precisely what DEFINITION HE7-2's broken base destroyed**; (iii) induction via (R1.1) + `by EFF.HE7.06`'s transport (extended to the tower by `.03`); (iv) `computation` from (ii) at `i = 1`.

**RESOLUTION TRACE:** Base lines 2039–2091; consumed at `.06`, `.07`, `.09`, `.10`, `.12`, and out of range at 2604–2611 and 2632–2641 (`.32`, `.33`).

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — grep-verified count **25** (the twist-blindness principle clause (iii) supplies at every level).

**TEETH:** `he7rannex_supp.py`: “The Λ₂Λ₁-monomial twist arithmetic fired on 102 slot instances (a₁ ≠ 0), and the exponent-vector value identity 4α + 10σ + u₂s₂ = k held on every n₃-monomial computed” — i.e. clause (iii)'s letter-monomial form and clause (i)'s exactness are both machine-exercised at level 3. **The counter “102” is re-read by M-1 (`.24`).**

---

### EFF.HE7.109  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2093–2099 — **R1.1's preamble: the two §S6 sentences the annex replaces**.

> “**R1.1 The core displays, re-proved with the cocycle carried.** These
> two replace §S6's "(SLOT). §S3 verbatim … Nothing else enters" and
> "(LIFT). §S4.2 verbatim" — the sentences F1 falsified at level ≥ 3 —
> by the actual arguments. §S3 Step 3's factorization
> ϖ^{m₀} = ϖ^{m₀−tu}·ϖ^{tu} is a TRIVIAL-cocycle identity; one level up it
> becomes n_i(m₀) vs n_i(m₀−tu_i)·n_i(u_i)^t, off by the nontrivial twist
> θ_t below, and the residue formula must carry it.”

**CONDITIONALITY:** **SUPERSESSION KIND: replacement**, two named target sentences inside `EFF.HE7.48`'s DERIVATION. **The diagnostic sentence is the clearest statement of what F1 actually broke**: §S3 Step 3's `ϖ^{m₀} = ϖ^{m₀−tu}·ϖ^{tu}` is a *trivial-cocycle* identity, valid at level 1 because `k ↦ ϖ^k` is a homomorphism, and the level-i analogue is off by `θ_t`.

**DERIVATION:** Diagnostic; discharged by `.06` and `.07`.

**RESOLUTION TRACE:** Base lines 2093–2099. Targets `EFF.HE7.48` (both sentences) and, via M-B (`.26`), the twin clauses at `EFF.HE7.17` and `.16`(ii).

**TEETH:** `.13`'s P3 tooth (18/79 flip when the deep letter is dropped) is the machine form of “the residue formula must carry it”.

---

### EFF.HE7.110  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 2101–2126 — **ANNEX-THEOREM R1-b ((SLOT_i) under HE7-2′, every i ≥ 1)**.

> “**ANNEX-THEOREM R1-b ((SLOT_i) under HE7-2′, every i ≥ 1).** Let 𝔇_i
> be a level-i datum with the normalizers of ANNEX-DEF HE7-2′, and
> assume (SLOT_{i−1}) at level i (the inductive hypothesis; at i = 1 it
> is GENHN-2 with the transport identity of HE6-1 Step 2). Let ξ be a
> level-(i+1) point, C ∈ O[x] with 0 ≠ deg-bound C < D_{i+1}, and
> C = Σ_{s<L_i} c_s·Φ_i^{s} (deg c_s < D_i) its Φ_i-development. Define
> the **twist units**
>
>     θ_t := n_i(m₀ − t·u_i)·n_i(u_i)^{t} / n_i(m₀)   (t < g_i),  θ₀ = 1,
>
> where k := min_{s<L_i}(ℓ_i·w_i(c_s) + s·u_i), s₀ := s_i(k),
> m₀ := m_i(k). Then w_{i+1}(C(ξ)) = k EXACTLY; the minimising s lie in
> the single class s₀ + ℓ_i·{0,…,g_i−1} mod ℓ_i; and
>
>     res( C(ξ)/n_{i+1}(k)(ξ) )
>         = ι_ξ^{(i+1)}( Σ_{t<g_i} γ_t·ϑ_t·β_i^{t} ) ≠ 0 ,
>
> where γ_t ∈ K_i is the level-i residue symbol of c_{s₀+ℓ_i t} at
> height m₀ − t·u_i ((SLOT_{i−1}); γ_t ≠ 0 exactly at the attaining t)
> and ϑ_t ∈ K_i^× is the fixed residue symbol of the letter monomial θ_t
> (ANNEX-LEMMA R1-a(iii)) — depending on (k, t) and the s-bookkeeping
> only, NOT on C or ξ. At i = 1 every θ_t = 1 (ϖ-powers multiply) and
> the display is (SLOT₂) byte-for-byte. **(SLOT_i)'s clauses as consumed
> by THEOREM HE7.D — exactness, nonzero residue, residue in K_{i+1},
> ξ-independence — are unchanged; what the correction moves is the
> residue's COORDINATES (γ_t ↦ γ_t·ϑ_t).**”

**CONDITIONALITY:** Annex grade, full displayed proof. **The closing sentence is the compatibility guarantee** that keeps every downstream consumer of (SLOT_i) intact — only the residue's coordinates move, and every consumed clause (exactness, nonzero, membership, ξ-independence) is unchanged. **At i = 1 it degenerates to (SLOT₂) byte-for-byte**, so `EFF.HE7.11` is untouched. **One machine gap, disclosed at `.13`(ii): `g₂ = 1` throughout the level-3 family, so “the within-class deep twist ϑ_t (t ≥ 1) is structurally invisible at this family” — R1-b's ϑ_t for t ≥ 1 is exercised nowhere.**

**DERIVATION:** [ASSEMBLED — lines 2128–2163, verbatim]

> “*Proof.* **Step 1 (values, twist-free).** (SLOT_{i−1}) at ξ ∈ 𝒫_{i+1} ⊆
> 𝒫_i gives w_i(c_s(ξ)) = w_i(c_s) exactly, so w_{i+1}(c_s(ξ)) =
> ℓ_i·w_i(c_s); and w_{i+1}(Φ_i(ξ)) = u_i by 𝒫_{i+1}'s defining clause.
> Hence w_{i+1}(c_s(ξ)Φ_i(ξ)^s) = ℓ_i·w_i(c_s) + s·u_i exactly — §S3
> Step 1 with the substitution table.
> **Step 2 (class separation, twist-free).** ℓ_i·w_i(c_s) + s·u_i ≡ s·u_i
> (mod ℓ_i) and s ↦ s·u_i is a bijection of ℤ/ℓ_i (gcd(u_i, ℓ_i) = 1):
> cross-class ties are impossible; the min sits in one class of g_i slots
> — §S3 Step 2 verbatim.
> **Step 3 (within-class, the twist carried).** A class slot s₀ + ℓ_i t
> attains iff w_i(c_{s₀+ℓ_i t}) = m₀ − t·u_i (from ℓ_i m₀ + s₀u_i = k).
> The exact monomial identity (expand n_{i+1}(k) = n_i(m₀)Φ_i^{s₀} and
> Λ_i^t = Φ_i^{ℓ_i t}/n_i(u_i)^t):
>
>     c_{s₀+ℓ_i t}·Φ_i^{s₀+ℓ_i t} / n_{i+1}(k)
>         = [ c_{s₀+ℓ_i t} / n_i(m₀ − tu_i) ] · Λ_i^{t} · θ_t ,      (R1.2)
>
> and θ_t telescopes into cocycle values:
> θ_t = Π_{j=0}^{t−1} τ_i(m₀ − (j+1)u_i, u_i) (each factor is
> n_i(m₀−(j+1)u_i)n_i(u_i)/n_i(m₀−ju_i); the product collapses to the
> displayed θ_t). Evaluate (R1.2) at ξ. The first bracket has w_i-value
> w_i(c_{s₀+ℓ_i t}) − (m₀ − tu_i) ≥ 0, equal to 0 iff attaining, with
> residue ι_ξ^{(i)}(γ_t) by (SLOT_{i−1})'s residue-and-transport clause.
> Λ_i(ξ)^t has value 0 and residue β_{i,ξ}^t (R1-a(i)). θ_t(ξ) has value 0
> and residue ι_ξ^{(i)}(ϑ_t), ϑ_t ∈ K_i^× fixed (R1-a(iii)). Summing the
> class and reading residues:
>
>     res( C(ξ)/n_{i+1}(k)(ξ) ) = Σ_{t<g_i} ι_ξ^{(i)}(γ_t·ϑ_t)·β_{i,ξ}^{t}
>         = ι_ξ^{(i+1)}( Σ_{t<g_i} γ_t·ϑ_t·β_i^{t} ) ,
>
> using ι_ξ^{(i+1)}|_{K_i} = ι_ξ^{(i)} and ι_ξ^{(i+1)}(β_i) = β_{i,ξ}.
> Since r_i is irreducible over K_i of degree g_i, {1, β_i, …,
> β_i^{g_i−1}} is a K_i-basis of K_{i+1}; the coefficients γ_t·ϑ_t lie in
> K_i and vanish iff γ_t does (ϑ_t is a unit), and at least one attaining
> γ_t ≠ 0 — so the sum is NONZERO: no cancellation, w_{i+1}(C(ξ)) = k
> exactly, residue as displayed. ∎”

Justification tags: Steps 1–2 are `EFF.HE7.11`'s Steps 1–2 under `.07`'s substitution, and are declared **twist-free**; Step 3 is the genuinely new content — the monomial identity (R1.2) `computation` from `.03`, the telescoping of `θ_t` into cocycle values `by EFF.HE7.108`(ii), the residue readout `by .04`(i)(iii) + `by (SLOT_{i−1})`, and the non-vanishing `by` the `K_i`-basis argument with `ϑ_t` a unit.

**RESOLUTION TRACE:** Base lines 2101–2163. Replaces the “(SLOT). §S3 verbatim” sentence inside `EFF.HE7.48`'s DERIVATION, per `.05`; carried onto `EFF.HE7.17`'s display by M-B (`.26`).

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` — grep-verified count **2** (the i = 1 base case).
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1` — grep-verified count **15** (Step 2's transport identity).

**TEETH:** `he7rannex_supp.py` at level 3 (`.13`) — but **only the `t = 0` twist**: disclosure (ii) records `g₂ = 1`, so `ϑ_t` for `t ≥ 1` is structurally invisible there.

---

### EFF.HE7.111  [theorem]

**CANONICAL STATEMENT:** verbatim, lines 2165–2169 — **ANNEX-THEOREM R1-c ((LIFT_i) under HE7-2′)**.

> “**ANNEX-THEOREM R1-c ((LIFT_i) under HE7-2′).** Statement verbatim as
> THEOREM HE7.D's: for k with m₀ := m_i(k) ≥ (g_i − 1)u_i + bound_i —
> k-uniformly, k ≥ bound_{i+1} := (L_i − 1)u_i + ℓ_i·bound_i — the
> residue map at height k is onto ι_ξ^{(i+1)}(K_{i+1}), realised by
> C ∈ O[x] with deg-bound < D_{i+1} and slot value exactly k (c ≠ 0).”

**CONDITIONALITY:** Annex grade, full displayed proof. **The bound recursion is UNCHANGED** — the proof's closing sentence says “values never see the twist” — so `EFF.HE7.23` stands as written. The repair is one added line: the lift targets the **inverse-twisted** residue `γ_t·ϑ_t^{−1}`.

**DERIVATION:** [ASSEMBLED — lines 2171–2182, verbatim]

> “*Proof.* §S4.2 one level up, with ONE pre-twist line added. Given
> c = Σ_{t<g_i} γ_t β_i^t ∈ K_{i+1} (unique in the K_i-basis), for each t
> with γ_t ≠ 0 invoke (LIFT_{i−1}) at level-i height m_t := m₀ − tu_i ≥
> m₀ − (g_i−1)u_i ≥ bound_i for the residue **γ_t·ϑ_t^{−1} ∈ K_i^×** —
> the INVERSE twist, exactly DEFINITION HE7-3's inverse-twisted mechanism
> (§S5.3 Step 2, machine-load-bearing per tooth HE7-T-BADTWIST) applied
> one step deeper. Set the other slots to 0 and C := Σ c_sΦ_i^s. All
> occupied slots sit at value k; by ANNEX-THEOREM R1-b the residue is
> Σ_t (γ_tϑ_t^{−1})·ϑ_t·β_i^t = c. The bound recursion is unchanged —
> values never see the twist: m₀ = (k − s₀u_i)/ℓ_i ≥ (k − (ℓ_i−1)u_i)/ℓ_i
> ≥ (g_i−1)u_i + bound_i when k ≥ bound_{i+1}, the same arithmetic as
> §S4.2's (‡₂) step. ∎”

Justification tags: the K_i-basis expansion `by .03`; the per-slot lift `by (LIFT_{i−1})` at the inverse-twisted residue — **the mechanism is `EFF.HE7.27`'s, one level deeper**, and its load-bearingness is HE7-T-BADTWIST's; the readout `by EFF.HE7.110`; the bound arithmetic `computation`, identical to `EFF.HE7.12`'s (‡₂) step.

**RESOLUTION TRACE:** Base lines 2165–2182. Replaces the “(LIFT). §S4.2 verbatim” sentence inside `EFF.HE7.48`'s DERIVATION, per `.05`.

**TEETH:** `he7rannex_supp.py` kind **K2R** — “forced (Z−c)² by INVERSE-twisting the target — **R1-c's mechanism used constructively**”, 15 members, of which 13 land {(16,1)}. This is the only place R1-c's inverse-twist is exercised, and it is used as a *construction*, not as a check.

---

### EFF.HE7.112  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2184–2193 — **R1.2's preamble: the composite twist unit**.

> “**R1.2 The rest of the level-i package: where the twist cancels, item
> by item (the twist-blindness audit).** The one enlargement HE7-2′
> forces on §S6's transfer step: every residue read at level i+1 carries,
> per slot, a FIXED unit of K_{i+1}^× — a monomial in β₁, …, β_i
> composing the n_{i+1}-cocycle's Λ_i-powers (already displayed at level
> 2 as §S5.3 Step 2's τ_t, res(τ_t) = β^{c_t}) with the deeper ϑ-units of
> R1-b. Call it the **composite twist unit** of the slot; by R1-a(iii) it
> is a fixed element of K_{i+1}^×, independent of ξ and of the polynomial
> read.”

**CONDITIONALITY:** Annex grade. **This paragraph defines the object the whole audit turns on** and identifies it with the level-2 twist already displayed in §S5.3 Step 2 — i.e. the enlargement is a generalisation of something the note already carried, not a new mechanism.

**DERIVATION:** Definition, discharged by `.108`(iii) (fixedness, ξ-independence).

**RESOLUTION TRACE:** Base lines 2184–2193; consumed by `.113`.

**TEETH:** `.117`'s P3 tooth.

---

### EFF.HE7.113  [fence]

**CANONICAL STATEMENT:** verbatim, lines 2195–2235 — **R1.2 items 1–7, the twist-blindness audit**. Kept as ONE unit: seven items, one audit, one conclusion (boundary audit §6 item 5).

> “The audit of every consumer (§S6's list, LEMMA HE7-12(c)'s
> architecture):
>
> 1. *Values, polygons, counts, degrees, bounds* — the disk criterion,
>    (S6.1)–(S6.3), LEMMA HE7-9's identities, TERMINATION's arithmetic,
>    the class-size sandwich's counting — never see residues at all:
>    twist-free, §S6 verbatim.
> 2. *DEFINITION HE7-3 one level up (the test family):* its prescription
>    is ALREADY inverse-twisted; under HE7-2′ "inverse-twisted" means by
>    the composite unit (available by R1-c, which absorbs any fixed
>    K_{i+1}^×-unit into the lift). Same construction, same degrees.
> 3. *LEMMA HE7-7 one level up (the ξ-side):* Step 1 is values only
>    (item 1). Step 2's residual-assembly display already carries the
>    cocycle bracket τ_t; under HE7-2′ res(τ_t) enlarges from β^{c_t} to
>    the composite unit — still fixed, still nonzero — and DEFINITION
>    HE7-3's inverse prescription is defined with the SAME composite
>    unit, so the middle step of the display cancels exactly as at level
>    2: 0 = ι(unit)·ι(r_{i+1})(β_{i+1,ξ}), unit ≠ 0, hence the label
>    vanishing. COHERENCE — one fixed normalizer system on both sides of
>    the assembly — is what the correction restores; no invariance under
>    CHANGING systems is consumed anywhere (that stronger claim is false,
>    which is HE7-T-BADTWIST's very tooth).
> 4. *LEMMA HE7-7′/COROLLARY HE7-7″ one level up:* assembled by the same
>    Step-2 mechanism; their consumed clauses are of the form "excess > 0
>    ⟺ ι(R)(β) = 0" — vanishing predicates against the FIXED system's
>    residual, twist-coherent by item 3.
> 5. *Galois equivariance (LEMMA HE7-11 one level up):* n_{i+1}(k) is
>    now a well-defined Laurent monomial in ϖ, Φ₁, …, Φ_i with O-
>    coefficients — g-fixed (under the broken display this premise was
>    not even well posed at i ≥ 2). The fixed symbols ϑ_t ∈ K_i live in
>    the abstract field and transport through ι^{(i+1)}; HE7-11's proof
>    pattern (ι^{(i+1)}_{gρ} = ḡ∘ι^{(i+1)}_ρ) is verbatim.
> 6. *The α-refine branch and HE6R1-1/2/3 one level up:* the refine
>    consumes (LIFT_{i−1})'s surjectivity onto K_i (R1-c, twist
>    absorbed); the peel and block lemmas consume values, degrees, Galois
>    stability and vanishing predicates only (items 1, 4, 5).
> 7. *Every count consumed downstream* — class sizes, e/f letters, the
>    μ ≥ 4 jump gate, J ≤ log₂μ − 1 — quantifies over the labels of the
>    fixed system ("for every monic irreducible r | R") and consumes only
>    degree/count/vanishing data. This is GENHN's J-D0 ("counts are
>    twist-blind, letters are twisted"), which §S1's CONVENTION installed
>    at level 2 and R1-a(iii) now supplies at every level: re-coordinating
>    residues by fixed units moves WHICH element of K_{i+1} a label names,
>    never how many roots carry it, its degree, or its (non)vanishing.”

**CONDITIONALITY:** **Annex grade, and explicitly NOT a full proof** — `.115` classifies it: “R1.2 is a transfer audit of exactly §S6's and LEMMA HE7-12(c)'s kind”. **Item 3's parenthetical is a NON-IMPORT of the first importance**: what is restored is COHERENCE of one fixed system, and “no invariance under CHANGING systems is consumed anywhere (that stronger claim is false, which is HE7-T-BADTWIST's very tooth)”. **Item 5 records that under the broken display, LEMMA HE7-11's premise “was not even well posed at i ≥ 2”** — a second casualty of F1 beyond (SLOT)/(LIFT).

**DERIVATION:** A seven-item transfer audit. Item 1 `by` twist-freeness of values; items 2–4 `by EFF.HE7.108`(iii) + `.110` + `.111`; item 5 `by .03` (well-definedness) + `EFF.HE7.42`'s proof pattern; item 6 `by .07` + items 1/4/5; item 7 `by XREF J-D0` + `.04`(iii).

**RESOLUTION TRACE:** Base lines 2195–2235; concluded at 2237–2253 (`.10`); graded at 2255–2261 (`.11`).

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.

**TEETH:** `.13`'s P3 tooth is item 3's machine form at level 3 (18/79 flip). **Items 1, 4, 5, 6, 7 have no tooth** — they are transfer claims about proofs. Disposition: **signed transfer audit, proof-only.**

---

### EFF.HE7.114  [corollary]

**CANONICAL STATEMENT:** verbatim, lines 2237–2253 — **ANNEX-COROLLARY R1-d (THEOREM HE7.D and COROLLARY HE7.B(ii), re-proved)**.

> “**ANNEX-COROLLARY R1-d (THEOREM HE7.D and COROLLARY HE7.B(ii),
> re-proved).** THEOREM HE7.D holds as stated with DEFINITION HE7-2
> read through ANNEX-DEF HE7-2′: the induction of §S6 with (SLOT) :=
> ANNEX-THEOREM R1-b, (LIFT) := ANNEX-THEOREM R1-c, and the §S5
> transfer step audited per R1.2 items 1–7. Levels 1 and 2 are
> byte-unchanged (HE7-2′ reproduces §S1's n₂ and DEFINITION HE7-1's
> ι^{(2)}; τ₂ = Λ₁^c is §S1's CONVENTION display — R1-a(iv)); the first
> level at which any new symbol (a ϑ_t ≠ 1, i.e. a nontrivial deep
> cocycle) can appear is level 3, unreachable below n = 16 (THEOREM
> HE7.C). COROLLARY HE7.B(ii) consumes THEOREM HE7.D as a package and
> is re-proved with it, with its OWN conditionality sentence ("modulo
> the arc grade of this note", §S9) unchanged. THEOREM HE7.A(3)'s
> level-3 branch inherits the repair the same way. **No hole developed
> in the re-derivation** — the fold note's predicted repair (re-base +
> carry the cocycle through the τ mechanism) closed at every audited
> site; had any site failed, this corollary would instead be an OPEN
> box, per the honesty invariant.”

**CONDITIONALITY:** **Annex grade** (`.115`), never hostile-passed as written but subsequently covered by the annex stack's 2/2 (`.127`). **Its strength is exactly the strength of R1.2's audit** — R1-b and R1-c are full proofs, the seven-item transfer is not. The closing honesty sentence (“had any site failed, this corollary would instead be an OPEN box”) is the note's declaration that the audit's outcome was not assumed. **Targets:** `EFF.HE7.17`, `.48` (THEOREM HE7.D), `.16`(ii) (COROLLARY HE7.B(ii)), `.14` (HE7.A(3)'s level-3 branch).

**DERIVATION:** Composition: `.03` + `.06` + `.07` + `.09`, with the level-1/2 compatibility `by .04`(iv) and the level-3 unreachability `by EFF.HE7.15`.

**RESOLUTION TRACE:** Base lines 2237–2253; graded at 2255–2261; the “SAME proofs” clauses at the two frozen displays riddered at 2491 (M-B, `.26`).

**TEETH:** `he7rannex_supp.py` (`.13`) is the only machine contact with the re-proved region, and its disclosure (ii) says it covers “the τ-cocycle substance of F1, not every letter of R1-b”.

---

### EFF.HE7.115  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 2255–2261 — **the Honest grade paragraph**.

> “**Honest grade.** The ratification annotation on THEOREM HE7.D /
> COROLLARY HE7.B(ii) / HE7.A(3)-level-3 is DISCHARGED BY THIS ANNEX at
> annex grade: R1-a/R1-b/R1-c are full displayed proofs; R1.2 is a
> transfer audit of exactly §S6's and LEMMA HE7-12(c)'s kind; none of it
> has been through a hostile pass. Asvin adjudicates the ratification
> outcome (fold note §S1); the acceptance annotation and its lifting are
> recorded in the BOX-1 append below.”

**CONDITIONALITY:** **This unit IS the grade attached to `.107`–`.114`.** Its “none of it has been through a hostile pass” became false at `.127`; the sentence is frozen. **“Asvin adjudicates the ratification outcome” is a live decision item** — carried as OPEN-CALL 1 together with F2's grade.

**DERIVATION:** Grade record with an explicit three-way classification of the annex's evidence (full proofs / transfer audit / unpassed).

**RESOLUTION TRACE:** Base lines 2255–2261; overtaken in the pass count at 2480–2487.

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F1` — count **4**.

**TEETH:** NONE (a grade record).

---

### EFF.HE7.116  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 2263–2292 — **R1.3's machine leg and its preregistered predictions**.

> “**R1.3 The machine leg (additive; the FIRST machine coverage of the
> level ≥ 3 region).** The adjudication records ZERO machine exercise at
> level 3 anywhere in the program (the ANNEX F-1 leg's n = 16 family
> reports 0 level-3 skips — its nodes never carried ℓ₂·deg r₂ ≥ 2
> repeated factors). New additive leg
> `verification/openmath/he7rannex_supp.py`: ONE constructed n = 16
> family where level 3 actually FIRES — built inside-out at the sealed
> battery's frame ((e₁,f₁,h) = (2,1,1), Φ′ = x² − p, λ = 5/2, u = 5,
> d_r = 1, T₂ = 10, D″ = 4): level-3 key Ψ₂ := Ψ² − S·n₂(u₂) (DEFINITION
> HE7-3's family at the level-2 node (λ₂ = u₂/ℓ₂, ℓ₂ = 2, r₂ = Z − s₂),
> degree 8), members f := Ψ₂² + A·Ψ₂ + B of degree 16 with A, B
> prescribed n₃-monomial perturbations so that the ladder is FORCED:
> μ = 8 (level-1 residual (Z−s)⁴), μ₂ = 4 (level-2 polygon a single side
> λ₂ with residual (Z−s₂)², ℓ₂·deg r₂ = 2 ≥ 2 — the JUMP gate of THEOREM
> HE7.A(3), first live at μ₂ ≥ 4), μ₃ = 2 (the level-3 problem, decided
> by the μ₂ = 2 dictionary one level up). The σ read runs the CORRECTED
> HE7-2′ chain — n₃(k) = n₂(m₂(k))·Ψ^{s₂(k)} with the τ₂-cocycle carried
> per R1-a — and every member is scored against PARI `factorpadic` on
> the actual degree-16 polynomial (the ANNEX F-1 leg's deg-16 oracle
> with the p-maximal hint). Preregistered predictions: **P1** the ladder
> fires as constructed (μ, μ₂, μ₃) = (8, 4, 2) member-by-member, read
> forward from f, not assumed; **P2** σ (level-3 read) == PARI on every
> char-0 member; **P3 (tooth)** dropping the τ₂-cocycle from the level-3
> residual assembly (the level-3 analogue of HE7-T-BADTWIST) changes at
> least one read at a live-twist letter s ≠ 1 — the corrected chain is
> load-bearing, not decorative. Budget discipline: 10-member smoke
> first; if PARI at degree 16 is too slow, scale down and disclose; if
> infeasible, the region stays machine-uncovered and this section says
> so. **Verdict appended below from the committed artifacts after the
> sealed run.**”

**CONDITIONALITY:** **Preregistered**, with an explicit falsifier and an explicit failure protocol (“if infeasible, the region stays machine-uncovered and this section says so”). **The oracle name is SUPERSEDED by M-A** (`.129`): “scored against PARI `factorpadic`” must be read as the shared `pari_sigma16` (`factor` + `nfinit([F,[p]])` p-maximal hint + `idealprimedec`, “factorpadic-EQUIVALENT” per the runner's own docstring). **This is a constructed family, built inside-out to force the ladder** — its σ agreement therefore tests the READ, not the reachability of the configuration in nature.

**DERIVATION:** Preregistration. The construction instantiates `EFF.HE7.27` (the test family) at the level-2 node to build `Ψ₂`, then perturbs by `n₃`-monomials; the forced ladder `(μ, μ₂, μ₃) = (8, 4, 2)` is designed against the gate of `EFF.HE7.14` (jump at `ℓ₂·deg r₂ ≥ 2`, live at `μ₂ ≥ 4` by `.15`).

**RESOLUTION TRACE:** Base lines 2263–2292; verdict at 2294–2334; oracle name corrected at 2490 (`.25`); the “102 slot instances” counter re-read at 2489 (`.24`).

**TEETH:** P1–P4; four rows in §5.

---

### EFF.HE7.117  [regression-record]

**CANONICAL STATEMENT:** verbatim, lines 2294–2334 — **R1.3's run record**.

> “**[run record, 2026-08-09, from the committed artifacts] GREEN — 79
> members, σ == PARI 79/79, 0 violations, 2.6 s**
> (`he7rannex_supp_output.txt` 6b320011429b…,
> `he7rannex_supp_results.json` aca0edc15f16…, runner-as-run
> `he7rannex_supp.py` de5ba60c08b2…; pins: `he7_pe3_probe12.py`
> 61d9f81cea79…, `he7annex_supp.py` a5d00403c282…). Grid: p ∈ {5,7},
> s ∈ {2,3} (live level-1 twist on EVERY member), u₂ ∈ {21,23},
> s₂ ∈ {1,2}; kinds K1 (ℓ₃ = 2) 16, K2 (ℓ₃ = 1 random) 32, K2R (forced
> (Z−c)² by INVERSE-twisting the target — R1-c's mechanism used
> constructively) 15, K3 (two sides) 16; 1 disc-zero discard. **P1 ✓**
> 79/79 ladders fire read-forward: level-1 single side 5/2 with
> residual == (Z−s)⁴, level-2 single side u₂/2 with residual == (Z−s₂)²
> (ℓ₂·deg r₂ = 2 — the JUMP, not a refine), level-3 reached at μ₃ = 2,
> all slopes > T₃. **P2 ✓** 79/79 σ agreement, Σef = 16 every member;
> σ genres {(16,1)} × 32, {(8,1),(8,1)} × 31, {(8,2)} × 16 — the μ₂ = 2
> dictionary one level up, no fourth value. **P3 ✓ TOOTH: 18/79 members
> FLIP when the deep letter is dropped** (multiplier s₂^{a₂} only —
> the single-letter reading the broken DEF HE7-2 suggests), flips on
> all four (p,s) frames, concentrated in the kinds whose residual has
> ≥ 3 slots (K2 10, K2R 8; K1/K3's shorter residuals are monic-
> normalization-blind to a global unit): **the τ₃-cocycle's Λ₁
> component is machine-load-bearing** — HE7-T-BADTWIST one level up.
> **P4 ✓** 19 members fire the level-3 α-refine (all 15 K2R + 4 K2),
> every chain terminates in ONE step with the refined-at slope strictly
> above the floor; 0 level-4 nodes (as forced at μ₃ = 2); 13 of 15 K2R
> land {(16,1)} — the ALPHA2 pattern one level up. The Λ₂Λ₁-monomial
> twist arithmetic fired on 102 slot instances (a₁ ≠ 0), and the
> exponent-vector value identity 4α + 10σ + u₂s₂ = k held on every
> n₃-monomial computed. DISCLOSURES: (i) members are ℤ_p only (no
> deg-16 char-p oracle); (ii) g₂ = 1 throughout — the within-class deep
> twist ϑ_t (t ≥ 1) is structurally invisible at this family
> (exercising it needs d_{r₂} ≥ 2, K₃ = F_{p²}, not constructed here):
> the leg covers the τ-cocycle substance of F1, not every letter of
> R1-b; (iii) the smoke record is disclosed in the runner docstring
> (smoke 1 GREEN with 0 refines → K2R + u₂ = 23 ADDED so P4 is
> exercised → smoke 2 GREEN; no reader/twist logic changed between the
> smokes and the sealed run, and the sealed re-run after the docstring
> disclosure was bit-identical on both artifacts — output and
> results-JSON md5s unchanged). **This is the first machine σ at a fired
> level-3 node anywhere in the program**, and — see R3 — each of the
> 79 members is a degree-16 TWO-JUMP witness within the ladder's read.”

**CONDITIONALITY:** **Three disclosures, all landed inline, plus two out-of-range corrections.** (i) ℤ_p only — no char-p at level 3, and combined with `p ∈ {5,7}` this family also has no characteristic 2. (ii) **`g₂ = 1` throughout — R1-b's within-class deep twist `ϑ_t (t ≥ 1)` is exercised NOWHERE**; the leg covers the τ-cocycle substance of F1, not every letter of R1-b. (iii) the smoke history discloses that **K2R and `u₂ = 23` were ADDED after smoke 1 so that P4 would be exercised** — a post-hoc grid extension, disclosed, with the reader logic unchanged and the sealed re-run bit-identical. **Out of range:** M-1 (`.128`) re-reads the “102 slot instances” counter as 47 + 55 on a shared counter; M-A (`.129`) corrects the oracle's identity.

**Compiler arithmetic audit (all recomputed):** kinds 16 + 32 + 15 + 16 = **79** ✓ (matching the member count, with the 1 disc-zero discard already excluded); σ genres 32 + 31 + 16 = **79** ✓; P4's refines 15 + 4 = **19** ✓; P3's flip concentration K2 10 + K2R 8 = **18** ✓ matching the 18/79 headline. **Every number in the run record cross-checks.**

**DERIVATION:** Machine record against preregistered predictions.

**RESOLUTION TRACE:** Base lines 2294–2334; “102” re-read at 2489; oracle name corrected at 2490; the two-jump-witness clause consumed by R3 at 2407–2412 (`.122`).

**TEETH:** Four rows (P1–P4) in §5, of which P3 is a planted mutant. **All five artifacts/pins named exist on disk**: `he7rannex_supp.py`, `he7rannex_supp_output.txt`, `he7rannex_supp_results.json`, `he7_pe3_probe12.py`, `he7annex_supp.py`.

---

### EFF.HE7.118  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the R2 heading (line 2336) and its defect paragraph (2338–2346), both verbatim]

> “### R2 (CODEX F2): the gcd dichotomy — the §S1 CONVENTION's equivalence chain made formal at a REDUCIBLE key”

> “**The defect.** The §S1 CONVENTION [r1] displays "Ψ ∤ f_S —
> equivalently A₀^{(2)} ≠ 0, equivalently dv₂(Ψ(ρ)) < ∞ at every root ρ
> of f_S". The first equivalence is polynomial division (Ψ | f_S ⟺
> Ψ | A₀^{(2)} ⟺ A₀^{(2)} = 0, since deg A₀^{(2)} < deg Ψ). The second
> needs Ψ ∤ f_S ⟹ gcd(Ψ, f_S) = 1 — NOT formal, because Ψ is never
> assumed irreducible (Codex's abstract scenario: Ψ = ab, f_S = ac with
> Ψ ∤ f_S yet common roots). LEMMA HE6R1-3 as displayed assumes the
> stronger Ψ | f_S. The lemma below closes the chain by transplanting
> HE6R1-3's own orbit argument, launched from g₀ ≠ 1 instead of Ψ | f_S.”

**CONDITIONALITY:** None — this is a defect report against `EFF.HE7.09`, the note's standing level-2 convention, **consumed at level 2 everywhere**. **The defect is a direct consequence of the note's own NON-IMPORT** “never assumed irreducible” (`EFF.HE7.06`): the convention's chain silently used irreducibility it had explicitly declined. Graded **GAP as stated**, with the grade flagged for Asvin (`.17`).

**DERIVATION:** The first equivalence is verified inline (`deg A₀^{(2)} < deg Ψ`); the second is refuted by an abstract scenario (`Ψ = ab`, `f_S = ac`) that R2-a then shows cannot occur *in context*.

**RESOLUTION TRACE:** Base lines 2336–2346. Targets `EFF.HE7.09`, and through it `EFF.HE7.35`, `.41`, and `EFF.HE7.96`. Repaired at 2348–2387.

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F2` — count **7**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — grep-verified count **8**.

**TEETH:** None found it; the sealed battery's frame has `Ψ` irreducible or the stratum isolated, so the reducible-key scenario never arises there. **Found by a decorrelated model.**

---

### EFF.HE7.119  [lemma]

**CANONICAL STATEMENT:** verbatim, lines 2348–2359 — **ANNEX-LEMMA R2-a (the gcd dichotomy)**.

> “**ANNEX-LEMMA R2-a (the gcd dichotomy).** Let (λ, r) be a level-2
> datum with key Ψ = Ψ_{λ,r} (DEFINITION HE7-1 — reducible allowed),
> and let F ∈ O[x] be monic with every root a (T1)/(T2) point of
> Galois-stable root set (e.g. F = f_S, or any block factor f_C of
> ANNEX-LEMMA HE7-13′(a)). Then
>
>     gcd(F, Ψ) ∈ { 1, Ψ } .
>
> Consequently Ψ ∤ F ⟹ gcd(F, Ψ) = 1 ⟹ Ψ(ρ) ≠ 0 at every root ρ of F
> ⟹ dv₂(Ψ(ρ)) < ∞ at every root — the CONVENTION's chain, closed. The
> same holds at every refined key Ψ̃ = Ψ − W of LEMMA HE7-12 (with
> LEMMA HE7-12(b)'s disk criterion supplying the level-2-point step).”

**CONDITIONALITY:** **Annex grade, full displayed proof.** Its hypothesis set is deliberately wide (`F` any monic O-polynomial with Galois-stable (T1)/(T2) root set), covering both `f_S` and every block factor of ANNEX-LEMMA HE7-13′(a) — which is what makes rider (ii) at `.120` a one-liner. **The refined-key clause is what licenses the convention at every iterate of a refine chain**, closing the same gap at `EFF.HE7.44`(c) item (11) and `EFF.HE7.96`.

**DERIVATION:** [ASSEMBLED — lines 2361–2375, verbatim]

> “*Proof (LEMMA HE6R1-3's proof, with "g₀ ≠ 1" replacing "Ψ | f_S").*
> Suppose g₀ := gcd(F, Ψ) ≠ 1, taken monic. Every root ξ of g₀ is a root
> of Ψ = Ψ_{λ,r}, hence a level-2 point with level-1 label (λ, r) (LEMMA
> HE6-1; at a refined key Ψ̃, LEMMA HE7-12(b): dv₂(Ψ̃(ξ)) = ∞ > T₂ forces
> ξ into the disk — item (11)'s mechanism), so LEMMA HE6-0′/HE7-5 gives
> [L_ξ : K₀] ≥ (e₁ℓ)(f₁d_r) = D″. The root set of g₀ is the intersection
> of two Galois-stable sets (F's by hypothesis; Ψ's since Ψ ∈ O[x]),
> hence Galois-stable, and its roots are integral over O; so g₀ ∈ O[x]
> with K₀-coefficients and g₀ contains ξ's full orbit:
> deg g₀ ≥ [L_ξ : K₀] ≥ D″. But g₀ | Ψ gives deg g₀ ≤ D″. Hence
> deg g₀ = D″ and g₀ = Ψ (both monic). So gcd ≠ 1 forces Ψ | F —
> Codex's abstract Ψ = ab / F = ac scenario is IMPOSSIBLE in context: a
> proper common factor would be a Galois-stable factor of Ψ of degree
> ≥ deg Ψ. The chain: gcd = 1 ⟺ no common root in K̄₀ ⟺ Ψ(ρ) ≠ 0 for
> every root ρ of F ⟺ dv₂(Ψ(ρ)) = e₁ℓ·v(Ψ(ρ)) < ∞. ∎”

Justification tags: every root of the key is a level-2 point `by XREF LEMMA HE6-1` (or, at a refined key, `by EFF.HE7.44`(b)); the local forcing `by XREF LEMMA HE6-0′` + `by EFF.HE7.29`; the descent of `g₀` to `O[x]` `by` Galois stability of an intersection + integral closedness (classical); the degree squeeze `computation`; the chain `definitional` (`dv₂ = e₁ℓ·v`).

**RESOLUTION TRACE:** Base lines 2348–2375. Targets `EFF.HE7.09` (licenses its chain), and through the riders `EFF.HE7.35`, `.41` and `EFF.HE7.96`.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1` — count **15**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0′` — grep-verified count **5**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** **NONE — proof-only.** The scenario it excludes is one the battery's frame cannot produce.

---

### EFF.HE7.120  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2377–2387 — **R2's two consumption riders, and the optional source-side erratum**.

> “**The two consumption riders.** (i) *At the CONVENTION:* the displayed
> equivalence chain is licensed by ANNEX-LEMMA R2-a with F = f_S — so
> COROLLARY HE7-7″, LEMMA HE7-9 and the label partition are licensed on
> the stated stratum exactly as consumed. (ii) *At ANNEX-LEMMA
> HE7-13′(a)'s f_C inference* (the recurrence Codex named): if
> gcd(Ψ̃, f_C) ≠ 1 then R2-a at F = f_C gives Ψ̃ | f_C | f_S,
> contradicting Ψ̃ ∤ f_S — one line, as predicted. *(Optional HE6R1-side
> erratum, recorded here, executed there or not at Asvin's discretion:
> LEMMA HE6R1-3's hypothesis can be widened from "Ψ | f_S" to
> "gcd(f_S, Ψ) ≠ 1" with its proof byte-near-verbatim, which is exactly
> R2-a.)*”

**CONDITIONALITY:** **SUPERSESSION KIND: license** (neither a replacement nor a wording rider — it supplies a missing justification for a display that stays as written). Targets: `EFF.HE7.09` (rider (i), and through it `.35`, `.41`) and `EFF.HE7.96`(a) (rider (ii)). **The parenthetical is the note's single most explicit statement of the append/consumption protocol**: an erratum owed to a supplier is *recorded here*, and whether it is executed at the source is Asvin's call, not HE7's.

**DERIVATION:** Rider (i) is `by .15` at `F = f_S`; rider (ii) is `by .15` at `F = f_C` plus `f_C | f_S`.

**RESOLUTION TRACE:** Base lines 2377–2387; the optional erratum has **no landed append on HE6R1** anywhere in this repo's HE7 record — recorded, not executed (OPEN-CALL 2).

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` — count **8**.

**TEETH:** NONE (a license record).

---

### EFF.HE7.121  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 2389–2395 — **R2's grade flag**.

> “**Grade flag (per the fold note, for Asvin).** As stated the finding
> is a GAP (an underived equivalence at a standing convention consumed
> at level 2 everywhere); by arc precedent (PE2 F-1's W ≠ 0, PE3 F-1 —
> verified-true, in-toolkit, display-scale) this exact shape was twice
> graded MINOR. The repair above is identical under either grade; the
> grade decides only whether the ratification CHALLENGE cites one heavy
> finding or two.”

**CONDITIONALITY:** **A live, explicitly-deferred decision.** It is echoed at the BOX-1 append (`.125`: “Asvin adjudicates: the CHALLENGE's final disposition and F2's grade”) and is still open in the note's own terms — the final dated line (`.131`) records the CHALLENGE as “discharged” but never records the grade. **OPEN-CALL 1.**

**DERIVATION:** Grade argument by arc precedent, with two named precedents (PE2 F-1's `W ≠ 0`; PE3 F-1) both graded MINOR on the same shape: verified-true, in-toolkit, display-scale.

**RESOLUTION TRACE:** Base lines 2389–2395; echoed at 2458–2459; never resolved in the note.

XREF: `lean/notes/openmath/HE7_passPE2_report.md:F-1` — grep-verified count **5**.
XREF: `lean/notes/openmath/HE7_passPE3_report.md:F-1` — grep-verified count **8**.

**TEETH:** NONE (a grade question).

---

### EFF.HE7.122  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the R3 heading (2397) and its rider (2399–2412), both verbatim]

> “### R3 (CODEX F3, wording-MINOR): the n = 16 sentences restated to the proved direction”

> “Two body sentences claim an existential their displays do not prove:
> THEOREM HE7.C's "The first n at which a level-3 object can be needed
> is n = 16" and §S7's "The first degree at which J = 2 is possible is
> n = D′μ with μ ≥ 8, i.e. n = 16". The displays prove the NECESSARY
> direction only: J ≥ 2 ⟹ μ ≥ 8 ⟹ n ≥ 16. **Rider: read both sentences
> as "level 3 / J = 2 is unreachable below n = 16; n = 16 is the first
> degree NOT EXCLUDED by the bound."** No consumer uses more (THEOREM
> HE7.C's gate, COROLLARY HE7.B(i)'s n ≤ 15 clause and §S8's "level 3 is
> degenerate" all consume the necessary direction). Post-script from
> R1.3's leg: the constructed family, if GREEN, supplies degree-16
> two-jump WITNESSES within the ladder's own read (machine-instance
> grade) — the existential direction would then hold as an exhibited
> instance, though the body's sentences still claim only what they
> proved; see the run record below.”

**CONDITIONALITY:** **SUPERSESSION KIND: wording-rider.** Targets both sentences of `EFF.HE7.15` (the statement's closing sentence and its proof's closing sentence). **The post-script's condition was met**: R1.3's leg ran GREEN 79/79 (`.13`), so the existential direction now holds as an exhibited machine instance — **but the note is explicit that “the body's sentences still claim only what they proved”**, i.e. the rider is NOT lifted by the machine witness. The blast-radius check is displayed: no consumer uses more than the necessary direction.

**DERIVATION:** A direction audit: the displays prove `J ≥ 2 ⟹ μ ≥ 8 ⟹ n ≥ 16`, which is the contrapositive-style necessary condition, not the existential.

**RESOLUTION TRACE:** Base lines 2397–2412. Targets `EFF.HE7.15`. Post-script discharged at 2294–2334 (`.13`) and re-asserted at 2332–2334 (“each of the 79 members is a degree-16 TWO-JUMP witness within the ladder's read”).

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F3` — count **3**.

**TEETH:** `he7rannex_supp.py` — 79 degree-16 two-jump witnesses, machine-instance grade.

---

### EFF.HE7.123  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the R4 heading (2414) and its completed inventory (2416–2426), both verbatim]

> “### R4 (CODEX F4, MINOR): LEMMA HE7-12(c) item (7)'s dependency inventory completed”

> “Item (7)'s sentence "LEMMA HE6R1-2's read consumes only the HE7-7/7′
> analogues, items (5)–(6)" is inaccurate. The full inventory (Codex F4
> = the orchestrator's pre-verdict key P-1 item 7, exact match): clause
> (a) also consumes **LEMMA HE6-4 and LEMMA HE6-2′** — LEVEL-1 lemmas,
> key-free, unchanged under Ψ ↦ Ψ^{(w)}; clause (b) also consumes
> **(LIFT₂), DEFINITION HE7-3's test family, LEMMA HE7-9(a), and THEOREM
> HE7.A(1)**; clause (c) again the test family and HE7-7/7′. All of
> these transfer to the refined key through items **(1), (2), (5), (6),
> (8)** of the same audit, so LEMMA HE7-12(c)'s CONCLUSION is unaffected
> — the erratum is citation-completeness on one sentence, no transfer
> breaks.”

**CONDITIONALITY:** **SUPERSESSION KIND: inventory completion.** Target: `EFF.HE7.44`(c) item (7). **The conclusion is explicitly unaffected.** Note the decorrelation datum embedded here: “Codex F4 = the orchestrator's pre-verdict key P-1 item 7, **exact match**” — the finding had been independently predicted before the pass ran. **R4 does NOT name §S6(iii)'s parallel sentence** about the same lemma (`EFF.HE7.51`), whose inventory differs; carried as shard 1's OPEN-CALL 4.

**DERIVATION:** A dependency re-inventory of LEMMA HE6R1-2's three clauses, each item then routed through a named item of HE7-12(c)'s own audit.

**RESOLUTION TRACE:** Base lines 2414–2426. Targets `EFF.HE7.44`.

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F4` — count **5**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-4` — grep-verified count **8**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-2′` — grep-verified count **4**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` — grep-verified count **8**.

**TEETH:** NONE (a citation-completeness erratum).

---

### EFF.HE7.124  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the R5 heading (2428) and its rider (2430–2440), both verbatim]

> “### R5 (CODEX F5, MINOR): §S4.2's "subgroup-coset" mislabel”

> “§S4.2's sharpness sentence "below them the failure is genuine (a
> proper subgroup-coset of K₂ is reached, or the height is not attained
> at all)" mislabels the reachable set. **Rider: read "a proper
> subgroup-coset of K₂" as "the nonzero elements of a proper F_Q-linear
> subspace (a punctured proper subspace)"** — LEMMA HE7-L1's own display
> already gives the correct object ({Σ_{t∈T(k)} c_t·η_θ^t : c_t ∈ F_Q,
> not all 0}). Codex's witness checks: in K₂ = F₈ with reachable slots
> {1, β}, the set {1, β, 1+β} has size 3 — no additive subgroup/coset
> (sizes are powers of 2) and no multiplicative one (F₈^× has order 7).
> Nothing consumes the group structure; tooth HE7-T-LIFT2SHARP verifies
> the exact sets by enumeration.”

**CONDITIONALITY:** **SUPERSESSION KIND: wording-rider.** Target: `EFF.HE7.22`. **It collides with the HE6-side dated append's item (ii)** (`.29`), which calls the very same phrase “coset-correct as written” — the two are true of different objects (the shape inside the braces vs the external `η_θ^{−q(k)}` multiplier). Carried as shard 1's OPEN-CALL 2 and restated at `.29` here. Blast radius nil: “Nothing consumes the group structure.”

**DERIVATION:** A counting witness: in `K₂ = F₈` with reachable slots `{1, β}`, the realized set `{1, β, 1+β}` has size 3, which is neither a power of 2 (so not an additive subgroup/coset) nor a divisor of 7 (so not a multiplicative one) — `computation`, compiler-verified: `|F₈| = 8`, additive subgroup orders ∈ {1,2,4,8}; `|F₈^×| = 7`, multiplicative subgroup orders ∈ {1,7}; 3 is in neither list ✓.

**RESOLUTION TRACE:** Base lines 2428–2440. Targets `EFF.HE7.22`; cross-read against 2538–2541 (`.29` item (ii)).

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F5` — count **3**.

**TEETH:** HE7-T-LIFT2SHARP verifies the exact sets by enumeration — **but with the blind spot disclosed at `.29`(iii): its frames sat at `q(k) = 0` on every proper-`T` height, so it never saw the coset factor.**

---

### EFF.HE7.125  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2442–2462 — **HE7-BOX-1 (arc record) — dated APPEND (2026-08-09, post-ANNEX F-1)**.

> “**HE7-BOX-1 (arc record) — dated APPEND (2026-08-09, post-ANNEX F-1).**
> Continues the [r1]/[r2]/[r3]/PE3 record under the acceptance freeze:
> **THE RATIFICATION SWEEP'S CODEX LEG HAS NOW RUN**
> (`CODEX_HE7RAT_2026-08-09.md`; decorrelated model, fresh context, the
> four charged attack surfaces all CLEAN, both heavy findings from the
> free hunt): **OUTCOME CHALLENGE — 5 findings, 5 confirmed (F1 CRITICAL
> as stated, scoped to §S6/DEF HE7-2/THEOREM HE7.D/COROLLARY HE7.B(ii);
> F2 GAP-as-stated with grade flagged; F3–F5 MINOR).** The 2/2 acceptance
> is ANNOTATED, not revoked: the level-2 core (§S1–S5, §S7, §S8, THEOREM
> HE7.A/HE7.A′/HE7.C, COROLLARY HE7.B(i), the whole machine record) is
> untouched by all five findings; THEOREM HE7.D, COROLLARY HE7.B(ii) and
> HE7.A(3)'s level-3 branch carried the annotation. **ANNEX R (this
> annex) discharges the repair queue: F1 by ANNEX-DEF HE7-2′ +
> ANNEX-LEMMA R1-a + ANNEX-THEOREMS R1-b/R1-c + the R1.2 audit
> (ANNEX-COROLLARY R1-d re-proves HE7.D and HE7.B(ii)); F2 by
> ANNEX-LEMMA R2-a; F3/F5 by riders; F4 by the completed inventory.**
> No sealed number, battery verdict, or n ≤ 15 σ-claim moved. Asvin
> adjudicates: the CHALLENGE's final disposition and F2's grade. The
> annex itself is unpassed (post-ratification append); the next fresh
> hostile pass on this note attacks the post-ANNEX-R text, ANNEX R
> included.”

**CONDITIONALITY:** **This is the fifth entry in the HE7-BOX-1 arc series** (after `EFF.HE7.67`/`.68`/`.69`/`.103`) and is itself continued by `.90`. **The decorrelation datum is load-bearing**: “the four charged attack surfaces all CLEAN, **both heavy findings from the free hunt**” — i.e. the two serious findings came from the model's unconstrained search, not from the orchestrator's charge. **“Asvin adjudicates” is live** (OPEN-CALL 1). The closing sentence (“the annex itself is unpassed”) became false at `.86`.

**DERIVATION:** Arc record. **The untouched-list is the compiler's warrant** for leaving the level-2 core and the whole machine record unriddered: shard 1's `.74`–`.79`, `.120`–`.126`, and all of shard 2's `.76`–`.92`.

**RESOLUTION TRACE:** Base lines 2442–2462. Continues the series homed at 1275–1304 and 1948–1959 (shard 2); continued at 2493–2497 (`.90`). Annotates `EFF.HE7.103`'s acceptance.

XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F1` — count **4**.
XREF: `lean/notes/openmath/CODEX_HE7RAT_2026-08-09.md:F2` — count **7**.

**TEETH:** The Codex leg itself (a decorrelated model, fresh context) plus `.76`'s level-3 machine leg.

---

### EFF.HE7.126  [scope-record]

**CANONICAL STATEMENT:** verbatim, lines 2464–2474 — ANNEX R's **What does not move**.

> “**What does not move (ANNEX R).** Every displayed statement and proof
> of the frozen body and of ANNEX F-1 (byte-frozen, md5-verified across
> this append); every sealed artifact and pin of §S10/§S11; the level-2
> frame §S1 (ANNEX-DEF HE7-2′ REPRODUCES its n₂, letter, transport and
> CONVENTION display — R1-a(iv)); every n ≤ 15 conclusion; the n = 8
> closure; COROLLARY HE7.B's grade sentences. What moves, all additive:
> the level ≥ 3 normalizer system now has one coherent definition
> (HE7-2′), THEOREM HE7.D's proof carries the displayed cocycle instead
> of a false verbatim-transfer sentence, the §S1 CONVENTION's chain is
> formal at reducible keys (R2-a), and the level-3 region gains its
> first machine leg (R1.3; verdict below).”

**CONDITIONALITY:** **The “what moves” half is the authoritative four-item summary of this shard's outbound effect** and matches the twelve supersessions §7 enumerates. **One tension with the “does not move” half:** “Every displayed statement and proof of the frozen body” does not move *as text*, but THEOREM HE7.D's *proof* is precisely what R1.1 replaces two sentences of — the two halves are reconciled by reading “does not move” as “is not edited”, which is the annex pattern's own meaning. Flagged because a chapter cut could read it as “is not superseded”.

**DERIVATION:** Blast-radius declaration, item by item.

**RESOLUTION TRACE:** Base lines 2464–2474; the four moving items are `.107`, `.109`–`.114`, `.119`, `.116`/`.117`.

**TEETH:** NONE (a negative declaration).

---

### EFF.HE7.127  [changes-record]

**CANONICAL STATEMENT:** [ASSEMBLED — the heading (line 2478) and the provenance paragraph (2480–2487), both verbatim]

> “### Dated corrections (2026-08-09, post-annex-acceptance)”

> “*Provenance.* The annex stack was ACCEPTED 2/2 — annex-pass #1
> (`HE7_annexpass_report.md`, commit 4a613d8: CLEAN, 1 MINOR) and
> annex-pass #2 (`HE7_annexpass2_report.md`, commit a472155: CLEAN,
> 2 MINOR, fresh route GREEN) — and the Codex CHALLENGE is thereby
> DISCHARGED. The three MINOR one-liners those reports owe land here,
> riders only: no statement, sealed number, or verdict moves, and
> everything above this heading is byte-frozen (prefix md5 732af1e1
> verified across this append).”

**CONDITIONALITY:** **This retroactively falsifies three frozen self-descriptions** — ANNEX F-1's “has NOT been through a hostile pass” (`EFF.HE7.93`), ANNEX R's identical clause (`.64`), and `.74`'s “none of it has been through a hostile pass” — none of which is edited. **“the Codex CHALLENGE is thereby DISCHARGED” closes the ratification, but does NOT resolve F2's grade**, which `.80` and `.84` both flag for Asvin and which no later line settles. Both annex-pass commits verified: `git cat-file -t 4a613d8` = commit ✓, `a472155` = commit ✓; both report files exist on disk.

**DERIVATION:** Provenance record.

**RESOLUTION TRACE:** Base lines 2478–2487; the three owed one-liners are `.87`, `.88`, `.89`; closed at 2493–2497 (`.90`).

XREF: `lean/notes/openmath/HE7_annexpass_report.md:M-1` — grep-verified count **3**.
XREF: `lean/notes/openmath/HE7_annexpass2_report.md:M-A` — grep-verified count **5**.
XREF: `lean/notes/openmath/HE7_annexpass2_report.md:M-B` — grep-verified count **7**.

**TEETH:** annex-pass #2's “fresh route GREEN” — detailed at `.88` as the triple-oracle leg W1 (`factorpadic` ROUND4 + a non-PARI sympy disc-parity check, 96/96 + 79/79 + 48/48 on a new n = 24 family).

---

### EFF.HE7.128  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 2489 — **M-1**.

> “- **M-1 (ANNEX R R1.3 run record — the "102 slot instances" counter).** Read "The Λ₂Λ₁-monomial twist arithmetic fired on 102 slot instances" as **47 corrected-chain slot instances + 55 naive-tooth-reader re-reads on a shared counter** (`sides3`'s `deep-letter-fired` counts under both readers): recounted isolated at annex-pass #1 (report M-1, 4a613d8) and machine re-confirmed on the re-generated members at annex-pass #2 (leg W1_R, a472155) — the two recounts agree exactly (47 + 55 = 102); the deep letter's load-bearing evidence, the 18/79 flip tooth, is unaffected.”

**CONDITIONALITY:** **SUPERSESSION KIND: counter re-reading.** Target: `.117`'s “102 slot instances” sentence. **This is a genuine over-count of the corrected chain's exercise**: the headline number conflated the corrected reader's instances with the *tooth reader's* re-reads on a shared counter, so the corrected-chain figure is **47, not 102** — a 2.2× reduction in the claimed level-3 twist exercise. The load-bearing tooth (18/79) is unaffected. **Compiler check: 47 + 55 = 102 ✓.** Twice recounted, on two independent passes, agreeing exactly.

**DERIVATION:** A counter audit: the shared `sides3` `deep-letter-fired` counter increments under both readers.

**RESOLUTION TRACE:** Base line 2489. Targets `.117`.

XREF: `lean/notes/openmath/HE7_annexpass_report.md:M-1` — count **3**.
XREF: `lean/notes/openmath/HE7_annexpass2_report.md:W1` — grep-verified count **3**.

**TEETH:** annex-pass #1's isolated recount + annex-pass #2's leg W1_R re-run on regenerated members — **two independent recounts agreeing exactly**.

---

### EFF.HE7.129  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 2490 — **M-A**.

> “- **M-A (ANNEX R R1.3 — the oracle name).** Read R1.3's "scored against PARI `factorpadic`" as **the stack's shared oracle `pari_sigma16`** (PARI global `factor` + `nfinit([F,[p]])` p-maximal hint + `idealprimedec`; "factorpadic-EQUIVALENT" per the committed runner's own docstring) — the three stack legs (ANNEX F-1's, R1.3's, annex-pass #1's fresh leg) import that single shared implementation, and actual `factorpadic` entered the record only at annex-pass #2's triple-oracle leg W1 (`factorpadic` ROUND4 + a non-PARI sympy disc-parity check on every re-generated committed member: 96/96 + 79/79 agreement, plus 48/48 on the pass's new n = 24 family; a472155).”

**CONDITIONALITY:** **SUPERSESSION KIND: provenance-rider.** Targets: `.116`, `.117` (R1.3) and — cross-shard — `EFF.HE7.100`, `.102` (ANNEX F-1's legs). **This corrects an ORACLE-IDENTITY claim, the strongest kind of decorrelation claim a machine record can make**: three deg-16 legs were scored not against `factorpadic` but against a shared re-implementation, i.e. they shared an oracle and were less decorrelated than their text implied. **The repair is real evidence, not a re-labelling**: annex-pass #2's W1 leg re-scored every committed member with actual `factorpadic` **plus a non-PARI sympy disc-parity check**, agreeing 96/96 + 79/79, and added 48/48 at n = 24. **HE7-BOX-3 (`EFF.HE7.72`, the oracle-asymmetry box) is not updated for this.**

**DERIVATION:** An implementation audit of the three legs' oracle import, plus a re-scoring with two independent oracles.

**RESOLUTION TRACE:** Base line 2490. Targets `.75`, `.76`, `EFF.HE7.100`, `.102`.

XREF: `lean/notes/openmath/HE7_annexpass2_report.md:M-A` — count **5**.
XREF: `lean/notes/openmath/HE7_annexpass2_report.md:W1` — count **3**.

**TEETH:** annex-pass #2 leg **W1**: `factorpadic` ROUND4 + non-PARI sympy disc-parity, **96/96 + 79/79 + 48/48 (new n = 24 family)** — the stack's only genuinely triple-oracle leg, and the only n = 24 contact anywhere in the HE7 record.

---

### EFF.HE7.130  [changes-record]

**CANONICAL STATEMENT:** verbatim, line 2491 — **M-B**.

> “- **M-B (THEOREM HE7.D / COROLLARY HE7.B(ii) — proof-provenance riders).** Read THEOREM HE7.D's clause "all hold, with the SAME proofs" (§S2) and COROLLARY HE7.B(ii)'s "whose inductive step is exactly §S3–S5" as **"with (SLOT) := ANNEX-THEOREM R1-b, (LIFT) := ANNEX-THEOREM R1-c, and the §S5 transfer audited per R1.2 (ANNEX-COROLLARY R1-d)"** — the operative displays; this is the same rider ANNEX R R1.1's preamble already attaches to §S6's twin sentences ("(SLOT). §S3 verbatim …" / "(LIFT). §S4.2 verbatim"), now attached at the two frozen statement displays that carry the same F1-falsified transfer clause (annex-pass #2 M-B, a472155).”

**CONDITIONALITY:** **SUPERSESSION KIND: provenance-rider.** Targets: `EFF.HE7.17` (THEOREM HE7.D's §S2 display) and `EFF.HE7.16`(ii) (COROLLARY HE7.B(ii)). **This is the item that forced shard 1 to emit THEOREM HE7.D TWICE** (§S2 display and §S6 display as separate units): R1.1's preamble riders §S6's two sentences, and M-B riders §S2's twin clause — two different riders naming two different displays of one theorem. Without the split, one CONDITIONALITY field would have to attach both to one text (shard 1 §6.1 item 21).

**DERIVATION:** Rider by parity with R1.1's preamble: the same F1-falsified transfer clause appears at two frozen statement displays, so the same substitution applies there.

**RESOLUTION TRACE:** Base line 2491. Targets `EFF.HE7.17`, `.16`(ii). Parallel to `.05` (which targets `EFF.HE7.48`).

XREF: `lean/notes/openmath/HE7_annexpass2_report.md:M-B` — count **7**.

**TEETH:** NONE (a provenance rider); the operative displays' evidence is `.13`.

---

### EFF.HE7.131  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2493–2497 — **HE7-BOX-1's final dated line**.

> “**HE7-BOX-1 (arc record) — final dated line (2026-08-09).** With the
> annex stack accepted 2/2 (4a613d8, a472155), the CHALLENGE discharged,
> and the three owed one-liners landed above, this note — body + ANNEX
> F-1 + ANNEX R + this micro-annex — is **FULLY FROZEN**: dated appends
> only.”

**CONDITIONALITY:** **This is the sixth and final entry of the HE7-BOX-1 arc series and the note's terminal status.** It closes the CHALLENGE but **does not resolve F2's grade** (OPEN-CALL 1). Note that four further dated corrections/lines follow it in the file (`.132`–`.137`) — consistent with “dated appends only”, and each carries its own prefix-md5 pin.

**DERIVATION:** Arc record.

**RESOLUTION TRACE:** Base lines 2493–2497. Closes the series `EFF.HE7.67`/`.68`/`.69`/`.103` → `.84` → here. **After it, four supplier-sourced dated items still land** (2501–2652).

**TEETH:** The two annex-pass legs (`.86`, `.88`).

---

### EFF.HE7.132  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2501–2529 — the **dated correction from HE6 PE2 F-1: LEMMA HE7-L1's realized set is a COSET**.

> “### Dated correction (2026-08-09, from HE6 PE2 F-1)
>
> *Landing verified at this append.* HE6's PE2 finding F-1
> (`HE6_passPE2_report.md` @ 404dae1, GAP, PARI-confirmed; report md5
> 62d76f854d738f48e9e09d59dc3da4a7, byte-frozen) lands on LEMMA
> HE7-L1's exact display (§S4.1): the two display lines (the realized
> set and T(k)) are byte-identical between HE6-1L (HE6 §S1 L118–119)
> and HE7-L1 (this note L383–384) — diff re-run empty at this append —
> so the defect found at HE6-1L is this note's display too. The display
> omits the normalizer twist: read after division by ϖ^k (not by the
> canonical height-k attaining monomial n(k) = x^iπ^a), the realized
> set is the COSET
>
>     { η_θ^{−q(k)} · Σ_{t ∈ T(k)} c_t·η_θ^{t} : c_t ∈ F_Q, not all 0 },
>     T(k) := { t < f₁ : k ≥ (i₀ + e₁t)·h },
>     η_θ^{q(k)} := ϖ(θ)^k/n(k)(θ)   (HE6-1L's own RIDER identity),
>
> since C(θ)/ϖ(θ)^k = [C(θ)/n(k)(θ)]·[n(k)(θ)/ϖ(θ)^k] =
> γ·η_θ^{−q(k)} — division by ϖ^k MULTIPLIES the n(k)-read residue by
> η_θ^{−q(k)} (the −q direction is HE6 PE2 F-3; the fold rider (a)'s
> "differing by η_θ^{q}" identity is correct as an identity). Both
> boundary clauses are twist-invariant: at full T(k) the coset is still
> ALL of K^× (η^{−q}·K^× = K^×), and T(k) = ∅ is untouched. Witness
> (source pin, F-1 + PE2 fresh leg B): (e₁, f₁, h) = (2, 2, 3), O = ℤ₃,
> Φ′ = x⁴ + 729, ϖ = xπ^{−1}, k = 3 (i₀(3) = 1, T(3) = {0} proper,
> q(3) = 1): over the 162 enumerated members C with dv(C) = 3 the
> realized ϖ-read set is {η, 2η} = η^{−1}·F₃^× — disjoint from the
> displayed {1, 2} = F₃^×; and at k = 9 = (D′−1)h the realized set is
> 8/8 of F₉^× (fullness survives the twist). Exact PARI.”

**CONDITIONALITY:** **SUPERSESSION KIND: replacement of a display**, with its own further correction at `.135` (the `res(·)` form and the factor placed outside the braces). Target: `EFF.HE7.19`. **This is an INBOUND supplier correction**: the defect was found at HE6's own PE2 pass, and HE7's display is byte-identical to HE6's, so the same defect. **The two boundary clauses survive**, which is why the non-propagation at `.29` is total. **Compiler checks on the witness:** `(e₁,f₁,h) = (2,2,3)` gives `D′ = 4`, `(D′−1)h = 9` ✓ matching the second half; `i₀(3)`: need `i₀·3 ≡ 3 (mod 2)`, `0 ≤ i₀ < 2` → `i₀ = 1` ✓; `T(3) = {t < 2 : 3 ≥ (1 + 2t)·3}` = `{t : 3 ≥ 3 + 6t}` = `{0}` ✓ proper.

**DERIVATION:** The identity `C(θ)/ϖ(θ)^k = [C(θ)/n(k)(θ)]·[n(k)(θ)/ϖ(θ)^k] = γ·η_θ^{−q(k)}` is displayed; the direction (`−q`, not `+q`) is HE6 PE2 F-3; the twist-invariance of both boundary clauses is `computation` (`η^{−q}·K^× = K^×`); the witness is exact PARI enumeration over 162 members.

**RESOLUTION TRACE:** Base lines 2501–2529. Targets `EFF.HE7.19`. Corrected in form at 2571–2591 (`.31`); its fold-box interaction scoped at 2555–2569 (`.30`); non-propagation at 2531–2553 (`.29`).

XREF: `lean/notes/openmath/HE6_passPE2_report.md:F-1` — grep-verified count **6**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` — grep-verified count **4**. (The note's citation form `HE6-1L [r2]` has fixed-string count **0** in the target — source defect 1.)

**TEETH:** HE6's PE2 fresh leg B — 162 enumerated members at `(2,2,3)/ℤ₃`, realized ϖ-read set `{η, 2η}` **disjoint** from the displayed `{1,2}`; and 8/8 of `F₉^×` at the full-`T` height. **Exact PARI. A foreign-arc tooth that HE7's own battery structurally could not fire** (its frames sat at `q(k) = 0`).

---

### EFF.HE7.133  [fence]

**CANONICAL STATEMENT:** verbatim, lines 2531–2553 — the **NON-PROPAGATION enumeration** for the coset correction.

> “**NON-PROPAGATION for this note's own consumptions (enumerated).**
> HE7's arc verified the twist-invariant fullness/emptiness clauses of
> HE7-L1 only; no HE7 pass adjudicated the sub-threshold exact-set
> clause (F-1's landing-site paragraph). Site by site: (i) the (LIFT₂)
> proof (§S4.2, L436–437) calls HE7-L1 only at m_t ≥ (D′−1)h — full-T
> heights, the surjectivity clause — so its exact-residue choices γ_t
> stand, and the fold rider (b)'s "the γ_t of (SLOT₂)(b) are exactly
> HE6-1L's residues" survives; (ii) the W₁/W₂ sharpness display
> (§S4.2, L449–450) is keyed to the fullness threshold, and its
> sub-threshold sentence already reads "a proper subgroup-coset of K₂
> is reached" — coset-correct as written; (iii) tooth HE7-T-LIFT2SHARP
> (§S4.2 L454–456; machine leg Q3, §S10) checks the two fullness
> halves (above-threshold surjective / below-threshold not), both
> twist-invariant — and per F-1, its frames sat at q(k) = 0 on each
> proper-T height tested ((2, 2, 1): q(0) = q(1) = 0; (3, 1, 2):
> T(1) = ∅), where the coset factor is 1; (iv) the level-i induction
> (§S6, L1012) consumes (LIFT_{i−1}) at full-residue heights only.
> None of THEOREM HE7.A/HE7.A′/HE7.C/HE7.D, COROLLARY HE7.B, the annex
> stack, or a sealed number moves. The exact-set display correction is
> owned at the source by HE6's owed repair round (HE6-BOX-2 queue,
> PE2 report §S4); this append is the note-to-owner on the frozen copy.
> Append-only: everything above this heading is byte-untouched
> (pre-append file md5 0698155b22508c0871e4ce830bdab8b6 is the prefix).”

**CONDITIONALITY:** **This is a four-site blast-radius audit and it is exhaustive by construction** — it enumerates every consumption of HE7-L1 in the note. **Item (iii) is the honest disclosure that HE7's own tooth could not have caught the defect** (its frames sat at `q(k) = 0`). **Item (ii) is the sentence that collides with ANNEX R R5** (`.124`): R5 calls “a proper subgroup-coset of K₂” a mislabel; this item calls it “coset-correct as written”. Both are true of different objects — shard 1's OPEN-CALL 2. **The closing sentence is the note's clearest append-protocol statement**: the correction is owned at the source, and this append is the note-to-owner.

**DERIVATION:** A site-by-site audit against the note's own call sites, each identified by line number. Site (i) `by EFF.HE7.25` (the use-site margin check proving `T(m_t)` full); (ii) `by EFF.HE7.22`; (iii) `by` the tooth's own frame data; (iv) `by EFF.HE7.48`.

**RESOLUTION TRACE:** Base lines 2531–2553. Its item (ii) cross-reads against 2428–2440 (`.20`).

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:HE6-BOX-2` — grep-verified count **2**.
XREF: `lean/notes/openmath/HE6_passPE2_report.md:F-1` — count **6**.

**TEETH:** Item (iii) is a **signed tooth blind-spot disclosure** — the only one of its kind in the note: a tooth that appears to guard a clause and provably could not have seen its defect.

---

### EFF.HE7.134  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2555–2569 — the **fold-box as-of scoping**.

> “**Dated line (2026-08-09, same wave — fold-box as-of scoping).** The
> §S4.1 fold-box sentence "HE6's repair R3 struck §S1's (LIFT) and
> adopted LEMMA HE7-L1 **verbatim** as **LEMMA HE6-1L [r1]**" is to be
> read **as-of the r1 landing**: at that landing the two display lines
> (the realized set and T(k)) were byte-identical and the surrounding
> prose differed by the 5 cosmetic byte-diffs enumerated at
> HE6R1_RECON's R3 row (cec49ba: `^k` vs `^{k}`; "which is ALL" vs
> "and it is ALL"; `{0,…,f₁−1}` vs `{0, …, f₁−1}`; `))h` vs `))·h`;
> ";" vs "." before the T(k) = ∅ clause) — display-identical, not
> verbatim. Post-r2 the two texts diverge by exactly the η_θ^{−q(k)}
> coset correction, which BOTH notes now carry: HE6-1L [r2] in its own
> display (8797a34), this note via the dated append above (5da0552).
> The frozen fold-box sentence itself is byte-untouched; this line is
> its as-of scoping. Append-only: the pre-append file md5
> 4c817dfba0afcd0959b2324c3c4da65a is the prefix.”

**CONDITIONALITY:** **SUPERSESSION KIND: as-of scoping** — the fifth distinct kind in this note (see shard 1 §6.3 item 8). Target: `EFF.HE7.20`. The word “verbatim” is not withdrawn; it is time-indexed, and the five cosmetic diffs are enumerated exactly. **The post-r2 divergence claim is the useful part for the DAG**: both notes now carry the coset correction, HE6 in its own display and HE7 by append — so a consumer must NOT assume the two displays are still byte-identical.

**DERIVATION:** A byte-diff record, enumerated, pinned to HE6R1_RECON's R3 row at commit `cec49ba` (verified commit ✓).

**RESOLUTION TRACE:** Base lines 2555–2569. Targets `EFF.HE7.20`.

XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:R3` — grep-verified count **7**.

**TEETH:** A diff, twice run (“diff re-run empty at this append” at `.28`; the five diffs enumerated here).

---

### EFF.HE7.135  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2571–2591 — the **res(·)-correct form, from HE6 PE3 obs-1**.

> “**Dated line (2026-08-09, from HE6 PE3 obs-1 — the res(·) form of
> the appended display).** HE6's PE3 pass (`HE6_passPE3_report.md` @
> 9f02ad4, md5 298b3c973e31648c65b405532b2e28eb; target-CLEAN, obs-1
> recorded out-of-scope for this note's queue) observes of the dated
> append above ("from HE6 PE2 F-1", 5da0552): its definition line
> reads `η_θ^{q(k)} := ϖ(θ)^k/n(k)(θ)` without `res(·)` — an
> element/residue conflation (the two sides live in K(θ) and K
> respectively) — and its coset display places the factor η_θ^{−q(k)}
> INSIDE the braces where LEMMA HE6-1L [r2] (HE6 §S1) places it
> OUTSIDE, mathematically identical and byte-different. The
> res(·)-correct form, stated once:
>
>     η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ)),
>     realized set = η_θ^{−q(k)} · { Σ_{t ∈ T(k)} c_t·η_θ^{t} :
>                                    c_t ∈ F_Q, not all 0 }
>
> — HE6-1L [r2]'s display form (its own line carries the `res`). No
> sealed number, statement, or verdict moves; the appended text above
> is byte-untouched and this line is its res(·)-corrected reading.
> Append-only: the pre-append file md5
> e7a0d95b24e256c81397b779d3ea9c97 is the prefix.”

**CONDITIONALITY:** **SUPERSESSION KIND: replacement of a display**, superseding `.132`'s own display — a correction of a correction, one wave later. Target: `EFF.HE7.19`, via `.28`. **The defect corrected is a type error** (element vs residue: `ϖ(θ)^k/n(k)(θ) ∈ K(θ)` while `η_θ^{q(k)} ∈ K`), found not by HE7's arc nor by HE6's F-1 but by HE6's PE3 as an out-of-scope observation. **This is the display the merged spec should carry** — it is the last word on LEMMA HE7-L1's realized set anywhere in the file.

**DERIVATION:** A typing audit of the previous append's definition line, plus a bracket-placement alignment with HE6-1L [r2]'s own display form.

**RESOLUTION TRACE:** Base lines 2571–2591. Supersedes 2510–2517 (`.28`'s display); targets `EFF.HE7.19`.

XREF: `lean/notes/openmath/HE6_passPE3_report.md:obs-1` — grep-verified count **1**.
XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:q(k)` — grep-verified count **12** (the object HE6-1L [r2]'s own display carries with `res`).

**TEETH:** NONE — a typing/format correction with no numeric content. Disposition: **signed non-applicability** (“No sealed number, statement, or verdict moves”).

---

### EFF.HE7.136  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2593–2622 — the **§S5.5 scalar clause, from HE6R1 PE2 F-1**.

> “**Dated line (2026-08-09, from HE6R1 PE2 F-1 — the §S5.5 scalar
> clause).** HE6R1's passPE2 (`HE6R1_passPE2_report.md` @ 2118e59,
> CLEAN, finding F-1) lands on the §S5.5 [r1] addition (b) parenthesis
> (L730–731): "with R_{λ₂}^{f} and R_{λ₂}^{f_S} of equal degree and
> equal radical **(equal outright when separable)**". The parenthesis
> carries verbatim the clause HE6R1's PE1 F-3 falsified — nothing pins
> the scalar to 1; HE6R1's [r1′] corrected its own copy (LEMMA
> HE6R1-2(c)) and left this frozen copy unflagged. The corrected
> reading, re-derived at this append from this note's own annex:
> residues multiply along f = f_S·g, and at a side λ₂ the height
> normalizers compose through the cocycle,
> n₂(h_{F₂,f_S}(λ₂))·n₂(c_g) = τ₂(h_{F₂,f_S}(λ₂), c_g)·n₂(h_{F₂,f}(λ₂))
> with h_{F₂,f}(λ₂) = h_{F₂,f_S}(λ₂) + c_g; ANNEX-LEMMA R1-a(iv) gives
> τ₂(a,b) = Λ₁^{c₁(a,b)}, c₁ ∈ {0,1}, whose residue at a level-2 point
> is the transport of the FIXED unit β^{c₁} ∈ K₂^× (R1-a(iii)); with
> LEMMA HE6R1-2(a)'s no-excess display res(g(ξ)/n₂(c_g)(ξ)) = ι_ξ(γ_g)
> the assembly gives, per side,
>
>     R_{λ₂}^{f} = γ_g · β^{c₁(h_{F₂,f_S}(λ₂), c_g)} · R_{λ₂}^{f_S} ,
>
> **equal up to a fixed K₂^× scalar per side when separable** — not
> equal outright. At ℓ = 1, s(·) ≡ 0 makes n₂(k) = ϖ^k a homomorphism
> (τ₂ ≡ 1), c₁ ≡ 0, and the scalar is γ_g alone. The consumers below
> the §S5.5 sentence are scale-invariant per the PE2 site check (report
> F-1: THEOREM HE7.A(2) consumes the monic irreducible factors, the
> α-refine consumes residual roots, separability checks are
> scale-invariant). No sealed number, statement, or verdict moves; the
> source-side cure is HE6R1's post-PE2 micro-annex, same wave.
> Append-only: the pre-append file md5
> 0ac7d1f86cd918df6d66499fbe4c215a is the prefix.”

**CONDITIONALITY:** **SUPERSESSION KIND: replacement of a parenthesis, itself SUPERSEDED IN ITS EXPONENT ARGUMENT by `.137`.** Target: `EFF.HE7.39`. **The provenance is notable: HE7's copy carried a clause its own supplier had already falsified (HE6R1 PE1 F-3) and corrected in its own copy (LEMMA HE6R1-2(c)), “and left this frozen copy unflagged”** — a corpus-level staleness mode that only cross-note review catches. **The repair is derived HERE, from this note's own annex** (R1-a(iii)(iv)), not imported. Consumers are scale-invariant, checked at the source pass.

**DERIVATION:** Displayed: residues multiply along `f = f_S·g`; the height normalizers compose through the cocycle with `h_{F₂,f} = h_{F₂,f_S} + c_g`; `by .04`(iv) `τ₂ = Λ₁^{c₁}` with `c₁ ∈ {0,1}`; `by .04`(iii) its residue is the transport of the fixed unit `β^{c₁}`; `by XREF LEMMA HE6R1-2(a)`'s no-excess display for `γ_g`. The `ℓ = 1` specialisation is `computation` (`s(·) ≡ 0 ⟹ τ₂ ≡ 1`).

**RESOLUTION TRACE:** Base lines 2593–2622. Targets `EFF.HE7.39`. **Its displayed exponent argument is superseded at 2624–2652 (`.33`)**; its `ℓ = 1` sentences are explicitly preserved there.

XREF: `lean/notes/openmath/HE6R1_passPE2_report.md:F-1` — grep-verified count **3**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2(c)` — grep-verified count **1**.
XREF: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md:F-3` — grep-verified count **8**.

**TEETH:** NONE — proof-only. The scale-invariance of the consumers was checked textually at the source pass, not by machine.

---

### EFF.HE7.137  [changes-record]

**CANONICAL STATEMENT:** verbatim, lines 2624–2652 — the **pin-height correction of the cocycle exponent, from HE6R1 PE3 F-1**. This is the note's LAST line.

> “**Dated line (2026-08-09, from HE6R1 PE3 F-1 — the cocycle
> exponent's argument is the PIN height).** HE6R1's passPE3
> (`HE6R1_passPE3_report.md` @ 9aa0cc6, CLEAN; HE6R1 ACCEPTED 2/2)
> lands on the dated line above (263cef0): its display's exponent
> c₁(h_{F₂,f_S}(λ₂), c_g) takes the side's LINE VALUE, which off the
> first side of a multi-side level-2 polygon at ℓ₂ ≥ 2 need not lie in
> ℤ — h(λ₂) = m₁ + j₁λ₂ ∈ ℤ requires ℓ₂ | j₁ (e.g. pins (3,0), (1,13),
> (0,21): the 13/2-side gives h = 39/2 ∉ ℤ) — while s(·) and hence c₁
> are defined on ℤ (ANNEX-LEMMA R1-a: a, b, k ∈ ℤ), so the display is
> ill-formed there. The corrected argument is the **PIN height**
> m₁ := dv₂(A^{(2)}_{j₁}) at the side's starting index j₁, an integer:
> normalizing each side by n₂(m₁)·Ψ(ξ)^{j₁} — the normalization
> HE7-7′(b)'s own proof uses — the Ψ(ξ)^{j₁} factor is COMMON to f and
> f_S (same sides by (b)) and CANCELS in the ratio, the vertex pins
> shift by c_g (m₁^f = m₁^{f_S} + c_g), and the cocycle composition
> runs entirely over ℤ:
>
>     R_{λ₂}^{f} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R_{λ₂}^{f_S} .
>
> Scope of the line-value form above: it agrees with the pin-height
> form exactly when j₁ = 0 (a single-side level-2 polygon, or the
> first side); at ℓ = 1, s(·) ≡ 0 gives c₁ ≡ 0 and the scalar is γ_g
> alone — the dated line's ℓ = 1 sentences stand as written. No sealed
> number, statement, or verdict moves; the consumed content (a fixed
> nonzero K₂^× scalar per side, consumers scale-invariant) is
> unchanged, and PE3's blast-radius check found no consumer of the
> exponent at HEAD. The source-side cure is HE6R1's dated acceptance
> record (post-PE3), same wave. Append-only: the pre-append file md5
> 501b92eaf2824ac8eb78d9d468d8c9cc is the prefix.”

**CONDITIONALITY:** **SUPERSESSION KIND: replacement of an exponent argument**, superseding `.136`'s display. Target (through `.136`): `EFF.HE7.39`. **This is a correction of a correction of a correction** — the third layer on §S5.5(b)'s parenthesis — and it is the terminal reading. **The defect is a well-formedness failure, not an arithmetic one**: `c₁` is defined only on ℤ, and the line value `h(λ₂) = m₁ + j₁λ₂` need not be an integer off the first side at `ℓ₂ ≥ 2`. **Compiler check of the witness pins `(3,0), (1,13), (0,21)`:** the segment from `(1,13)` to `(3,0)` has slope `−13/2`, i.e. `λ₂ = 13/2` with `ℓ₂ = 2`; taking `j₁ = 1`, `m₁ = 13`, the line value at `j = 0` is `13 + 1·(13/2) = 39/2 ∉ ℤ` ✓ — exactly as displayed. **Both earlier forms are explicitly scoped, not withdrawn**: the line-value form agrees at `j₁ = 0`, and the `ℓ = 1` sentences stand.

**DERIVATION:** A well-formedness audit plus a re-derivation at the pin height: normalize each side by `n₂(m₁)·Ψ(ξ)^{j₁}` (the normalization HE7-7′(b)'s own proof uses, `by EFF.HE7.34`), observe `Ψ(ξ)^{j₁}` is common to `f` and `f_S` and cancels, note `m₁^f = m₁^{f_S} + c_g`, and run the cocycle composition over ℤ `by .04`.

**RESOLUTION TRACE:** Base lines 2624–2652 — **the last lines of the file**. Supersedes 2604–2611 (`.32`'s display); targets `EFF.HE7.39` through it.

XREF: `lean/notes/openmath/HE6R1_passPE3_report.md:F-1` — grep-verified count **12**.

**TEETH:** NONE — proof-only. “PE3's blast-radius check found no consumer of the exponent at HEAD” is a signed non-applicability disposition.

---

## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`)
against the target note or artifact; counts shown are each shard's own recorded count.
**110 raw XREF citations across the three shards reduce to 78 distinct `target:designation`
pairs; 32 duplicate instances (28 distinct designations cited by more than one shard,
of which 4 are cited by all three) are marked `**DEDUP**` and removed as separate rows.**
Every duplicate's count agrees exactly across every shard that cited it — **zero count
mismatches found** (a fixed-string grep against an unchanged file must return the same
count regardless of who runs it; a mismatch would have meant a shard mis-copied its own
grep output, and none did). No zero-count or purely descriptive string is emitted as an
XREF anywhere below; no designation was invented at merge time.

`[TABLE — compiler ledger]`

| # | Target : designation | Count | Role | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|
| 1 | `HE6_PROOF_2026-08-08.md:DEFINITION HE6-1` | 7 | The order-2 key family Ψ_{λ,r}; supplies λ > D′h and the key's slot heights | s1 | — |
| 2 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-0` | 17 | Off-disk level-1 value δ = D′·min(dv ξ, h) | s1 | — |
| 3 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-0′` | 5 | s1: Level-1 local forcing (e₁ℓ \| e, f₁d_r \| f) / s3: R2-a's local forcing | s1+s3 | **DEDUP** |
| 4 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-1` | 15 | s1: The level-1 ξ-side; Step 1's estimate and Step 2's transport identity / s3: R2-a's "every root of the key is a level-2 point" step | s1+s3 | **DEDUP** |
| 5 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` | 4 | s1: The corrected level-1 (LIFT); = LEMMA HE7-L1 as of the r1 landing / s3: The level-1 lift whose display carries the coset defect | s1+s3 | **DEDUP** |
| 6 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-2` | 10 | Level-1 evaluation display (× ℓ gives the level-2 disk criterion) | s1 | — |
| 7 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-2′` | 4 | s1: Second level-1 evaluation display (added to HE7-12(c)(7) by ANNEX R R4) / s3: Added to HE7-12(c) item (7) by R4 | s1+s3 | **DEDUP** |
| 8 | `HE6_PROOF_2026-08-08.md:COROLLARY HE6-2″` | 1 | Level-1 label of a root; the datum (λ, r) "arises as a label of f" | s1 | — |
| 9 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-3` | 12 | Level-1 slope counts (SEP)-free; supplies n_λ = D′L_λ for THEOREM HE7.C | s1 | — |
| 10 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-4` | 8 | s1: Level-1 nonemptiness (added to HE7-12(c)(7) by R4; named in §S6(iii)) / s3: Added to HE7-12(c) item (7) by R4 | s1+s3 | **DEDUP** |
| 11 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-5` | 5 | Level-1 Galois equivariance | s1 | — |
| 12 | `HE6_PROOF_2026-08-08.md:THEOREM HE6.A` | 19 | The level-1 class-size theorem HE7.A is "one level up"; its sandwich slack | s1 | — |
| 13 | `HE6_PROOF_2026-08-08.md:COROLLARY HE6.B` | 6 | The four-case jump enumeration, in its WIDENED [r1] form | s1 | — |
| 14 | `HE6_PROOF_2026-08-08.md:HE6.B` | 6 | The pre-r1 enumeration error HE7.A(3) repeats one level up | s1 | — |
| 15 | `HE6_PROOF_2026-08-08.md:HE6-BOX-1` | 9 | s1: This unit's problem statement; the n = 8 bite / s2: The box HE7 closes; the ALPHA2 node the battery runs | s1+s2 | **DEDUP** |
| 16 | `HE6_PROOF_2026-08-08.md:HE6-T-CASEB` | 4 | HE6's own tooth; the observed three-σ alphabet | s1 | — |
| 17 | `HE6_PROOF_2026-08-08.md:S1` | 7 (§-anchor) | The inherited frame + ϖ-convention (see `.05`'s caveat) | s1 | — |
| 18 | `HE6_PROOF_2026-08-08.md:S3.3` | 2 | The disk-criterion transfer's source step | s1 | — |
| 19 | `HE6_PROOF_2026-08-08.md:S6.2` | 3 | The class-size sandwich transferred verbatim at HE7.A(2) | s1 | — |
| 20 | `HE6_PROOF_2026-08-08.md:S6.4` | 1 | HE6's own two-route decorrelation at μ ≤ 3 | s1 | — |
| 21 | `HE6_PROOF_2026-08-08.md:S7.2` | 5 | s1: HE6's stated exact residue = HE7's problem statement / s2: HE6's stated exact residue, whose under-count `.02` audits | s1+s2 | **DEDUP** |
| 22 | `HE6_PROOF_2026-08-08.md:S7.3` | 1 | The FGMN citation targets HE7 declares NOT consumed | s1 | — |
| 23 | `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-1` | 9 | s1: The widened jump condition with identical bounds / s2: The widened jump condition among the never-attacked consumed lemmas | s1+s2 | **DEDUP** |
| 24 | `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` | 8 | s1: The proper-block read off f (μ₂, sides, residual radical) / s2: Supplies `.03`(d), `.11`, and the annex leg's translation mechanism / s3: The proper-block read whose clause (c) carries the scalar defect | s1+s2+s3 | **DEDUP** |
| 25 | `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` | 8 | s1: The level-2 peel at Ψ \| f_S (irreducibility half NOT reproved here) / s2: Supplies `.03`(e), `.12`, `.17`, `.20` / s3: The peel whose proof R2-a transplants | s1+s2+s3 | **DEDUP** |
| 26 | `HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F1` | 4 | The enumeration error found against HE7.A(3)/HE7.C | s1 | — |
| 27 | `HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` | 4 | s1: The missing Ψ ∤ f_S hypothesis / s2: The finding whose stratum `.19` re-scopes and `.20` decides | s1+s2 | **DEDUP** |
| 28 | `HE6R1_RECON_2026-08-08.md:S3.2` | 6 | The ten-item literal-instance check; the item-2 ℓ = 1 verification | s1 | — |
| 29 | `GENHN_PROOF_2026-08-08.md:LEMMA GENHN-2` | 2 | s1: THE SLOT LEMMA — the ladder's base case / s3: R1-b's i = 1 base case | s1+s3 | **DEDUP** |
| 30 | `GENHN_PROOF_2026-08-08.md:GENHN-4` | 6 | Refine transfer — declared NOT consumed | s1 | — |
| 31 | `GENHN_PROOF_2026-08-08.md:GENHN.A(iv)` | 3 | The "binomial kill" LEMMA HE7-8 declares it does not need | s1 | — |
| 32 | `GENHN_PROOF_2026-08-08.md:GENHN.C` | 19 | §S7 trichotomy — argument template only, at §S8 only | s1 | — |
| 33 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ)]` | 1 | The program predicate COROLLARY HE7.B discharges | s1 | — |
| 34 | `GENHN_PROOF_2026-08-08.md:W-9` | 13 | The graded weld face declared NOT consumed | s1 | — |
| 35 | `HE3_PROOF_2026-08-08.md:HE3-3` | 15 | The elementary convex duality (★) of step 1 | s1 | — |
| 36 | `HE3_PROOF_2026-08-08.md:HE3-BOX-6` | 12 | s1: The original defect §S5.5's reduction repairs / s2: The original defect §S5.5's reduction repairs | s1+s2 | **DEDUP** |
| 37 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | s1: "counts are twist-blind, letters are twisted" / s3: The twist-blindness principle R1-a(iii) supplies at every level | s1+s3 | **DEDUP** |
| 38 | `W12_PROOF_2026-08-08.md:W-12.D` | 19 | The conditional-stack consumer named in COROLLARY HE7.B | s1 | — |
| 39 | `W12_PROOF_2026-08-08.md:r4` | 59 | The Artin–Schreier trap round (descriptive; see source defect 5) | s1 | — |
| 40 | `GENIND_PROOF_2026-08-08.md:GENIND.B` | 19 | s1: The conditional-stack consumer named in COROLLARY HE7.B / s2: A supplier in HE7-BOX-1's minimum | s1+s2 | **DEDUP** |
| 41 | `CODEX_HE6PE1_2026-08-08.md:F2` | 4 | The Φ′ \| f stratum finding whose level-2 analogue is HE6R1-F2 | s1 | — |
| 42 | `CODEX_HE6PE1_2026-08-08.md:finding 4` | 1 | The (LIFT) over-reach found twice (= FINDING HE7-F1) | s1 | — |
| 43 | `CODEX_HE7RAT_2026-08-09.md:F1` | 4 | s1: The CRITICAL on DEFINITION HE7-2 / THEOREM HE7.D / s3: The CRITICAL on DEFINITION HE7-2 / THEOREM HE7.D | s1+s3 | **DEDUP** |
| 44 | `CODEX_HE7RAT_2026-08-09.md:F4` | 5 | s1: HE7-12(c) item (7)'s incomplete inventory / s3: HE7-12(c) item (7)'s inventory | s1+s3 | **DEDUP** |
| 45 | `CODEX_HE7RAT_2026-08-09.md:F5` | 3 | s1: §S4.2's "subgroup-coset" mislabel / s3: The "subgroup-coset" mislabel | s1+s3 | **DEDUP** |
| 46 | `HE6_passPE2_report.md:F-1` | 6 | s1: The η_θ^{−q(k)} coset defect landing on LEMMA HE7-L1 / s3: The inbound coset correction | s1+s3 | **DEDUP** |
| 47 | `HE6_passPE3_report.md:obs-1` | 1 | s1: The res(·) form of the appended coset display / s3: The inbound res(·) correction | s1+s3 | **DEDUP** |
| 48 | `HE6R1_passPE2_report.md:F-1` | 3 | s1: The §S5.5 "(equal outright when separable)" scalar defect / s3: The inbound scalar correction | s1+s3 | **DEDUP** |
| 49 | `HE7_passPE1_report.md:F-1` | 4 | s1: The refined-key read GAP closed by LEMMAS HE7-12/HE7-13 / s2: The refined-key GAP | s1+s2 | **DEDUP** |
| 50 | `HE7_passPE1_report.md:F-2` | 2 | s1: The false (S5.2) middle-band dichotomy / s2: The false (S5.2) dichotomy | s1+s2 | **DEDUP** |
| 51 | `HE7_passPE1_report.md:F-4` | 2 | s1: The (LIFT_i) vs (LIFT_{i−1}) off-by-one citation / s2: The (LIFT_i)/(LIFT_{i−1}) off-by-one | s1+s2 | **DEDUP** |
| 52 | `HE7_passPE2_report.md:F-1` | 5 | s1: LEMMA HE7-12(d)'s W ≠ 0 hypothesis / s2: LEMMA HE7-12(d)'s W ≠ 0 / s3: An arc precedent cited in F2's grade argument | s1+s2+s3 | **DEDUP** |
| 53 | `HE7_passPE2_report.md:F-2` | 7 | s1: Mid-chain peels interleaving the refine chain / s2: Mid-chain peels | s1+s2 | **DEDUP** |
| 54 | `HE7_passPE3_report.md:F-1` | 8 | s1: The mixed-residual defect (ANNEX F-1's subject) / s2: The mixed-residual defect — ANNEX F-1's whole subject / s3: The second arc precedent in F2's grade argument | s1+s2+s3 | **DEDUP** |
| 55 | `HE6R1_passPE3_report.md:F-1` | 12 | s1: The pin-height correction of the cocycle exponent (`.39`) / s3: The inbound pin-height correction | s1+s3 | **DEDUP** |
| 56 | `HE6_PROOF_2026-08-08.md:HE6-BOX-4` | 2 | The oracle asymmetry HE7-BOX-3 inherits | s2 | — |
| 57 | `HE6R1_RECON_2026-08-08.md:he6r1_checks.py` | 2 | The sibling battery discharging the `d_r ≥ 2` hole | s2 | — |
| 58 | `W12_PROOF_2026-08-08.md:W-12` | 100 | A supplier in HE7-BOX-1's minimum (note-wide tag; addressable form is `W-12.D`, 19) | s2 | — |
| 59 | `HMENU3_PROOF_2026-08-08.md:ANNEX A` | 5 | The minors-only / dated-annex precedent (HE7's shorthand fails grep — defect 1) | s2 | — |
| 60 | `HE7_passPE1_report.md:F-3` | 2 | The missing integer floor | s2 | — |
| 61 | `HE7_passPE1_report.md:R-a` | 2 | The stale `WIP = False` self-comment | s2 | — |
| 62 | `HE7_passPE1_report.md:R-b` | 2 | The silent PARI-drop guard | s2 | — |
| 63 | `HE7_passPE1_report.md:R-c` | 2 | The redundant degenerate test | s2 | — |
| 64 | `HE7_passPE2_report.md:R-a` | 2 | B3's peel-guard skip | s2 | — |
| 65 | `HE7_passPE2_report.md:R-b` | 1 | B1's same-instrument coupling | s2 | — |
| 66 | `HE7_passPE3_report.md:R-a` | 2 | The simple-factor-of-an-inseparable-residual remark | s2 | — |
| 67 | `CODEX_HE7RAT_2026-08-09.md:F2` | 7 | The gcd-dichotomy GAP at the §S1 CONVENTION | s3 | — |
| 68 | `CODEX_HE7RAT_2026-08-09.md:F3` | 3 | The n = 16 existential | s3 | — |
| 69 | `CODEX_HE7RAT_2026-08-09.md:019fe4c6-4ae2-7053-95f9-d5c5cc0d58d1` | 2 | The Codex session pin (decorrelation provenance) | s3 | — |
| 70 | `HE6_PROOF_2026-08-08.md:HE6-BOX-2` | 2 | The queue that owns the exact-set correction at the source | s3 | — |
| 71 | `HE6_PROOF_2026-08-08.md:q(k)` | 12 | The twist exponent HE6-1L [r2]'s own display carries with `res` | s3 | — |
| 72 | `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2(c)` | 1 | The clause HE6R1 corrected in its own copy | s3 | — |
| 73 | `HE6R1_RECON_2026-08-08.md:R3` | 7 | The row enumerating the five cosmetic byte-diffs | s3 | — |
| 74 | `HE6R1_RECON_2026-08-08.md:F-3` | 8 | The PE1 finding that falsified the "equal outright" clause | s3 | — |
| 75 | `HE7_annexpass_report.md:M-1` | 3 | The "102" counter recount | s3 | — |
| 76 | `HE7_annexpass2_report.md:M-A` | 5 | The oracle-name correction | s3 | — |
| 77 | `HE7_annexpass2_report.md:M-B` | 7 | The proof-provenance rider | s3 | — |
| 78 | `HE7_annexpass2_report.md:W1` | 3 | The triple-oracle leg | s3 | — |
**Designations counted but NOT emitted as XREFs (5 distinct, after dedup of one cross-shard
mention):**

- **`twist (letters only)`** — count **0** in `GENHN_PROOF_2026-08-08.md`; the target's own
  heading (line 729) is `**The twist (letters only).**` with the closing period inside the
  bold. Referent unique and verified; carried descriptively at `.03`. (Shard 1.)
- **`stage-α recentering` / `stage-CS`** — HE7-local method names for HE3's route, not HE3
  designations; the parent designations `HE3-3` (15) and `HE3-BOX-6` (12) are separately
  verified and emitted above. Carried descriptively at `.15`, `.18`, `.37`. (Shard 1.)
- **`HMENU3-ANNEX-A`** **[DEDUP — cited identically by shard 1 (as a cross-reference,
  explicitly disclaiming ownership: "the row belongs to shard 2's ledger") and shard 2 (as
  primary)]** — count **0** in `HMENU3_PROOF_2026-08-08.md`; the target's own heading is
  `## ANNEX A` (count **5**, emitted above as row 59). Cited by ANNEX F-1 and §S9's `[r3]`
  box, both shard 2. Homed at shard 2's ledger per shard 1's own disclaimer.
- **`HE6-1L [r2]`** — count **0** in `HE6_PROOF_2026-08-08.md`; the `[r2]` round suffix is
  HE7-local. Parent `LEMMA HE6-1L` verified (row 5, count 4). Carried at `.135`. (Shard 3.)
- **`LEMMA HE6R1-2(a)`** — count **0**; the sibling clause-letter `LEMMA HE6R1-2(c)` DOES
  occur in the target (count **1**, row 72) — the clause-letter form is used inconsistently
  in `HE6R1_RECON` itself. Parent `LEMMA HE6R1-2` verified (row 24, count 8). Carried
  descriptively at `.136`. (Shard 3.)

**Commit hashes resolved with `git cat-file -t` — 15 distinct, all real commits in this
repository** (shard 3's §3.1 gives the whole-note total; shard 2 independently verified
the 9-hash subset it cites, all present in shard 3's list — cross-check clean):
`1956151` (the §S10/§S11 instrument seal), `111ac7f` (PE3), `4a613d8` / `a472155` (the two
ANNEX R acceptance passes), `b574f25` (the PE3 probe artifacts), `b3c05be` (the minors-only
ledger fold), `5da0552`, `263cef0`, `cec49ba` (the five cosmetic byte-diffs row),
`404dae1` (HE6 PE2), `9f02ad4` (HE6 PE3), `2118e59` (HE6R1 PE2), `9aa0cc6` (HE6R1 PE3),
`8797a34` (HE6-1L `[r2]`'s landing), `4c42f9d` (the sealed verdict).

**Battery artifacts and report files verified present on disk (`verification/openmath/`
and `lean/notes/openmath/`), consolidated across all three shards' independent checks:**
`he7_checks.py` (+2 artifacts), `he7r1_supp.py` (+2), `he7r2_supp.py` (+2),
`he7_pe2_fresh.py` (+2), `he7_pe3_probe12.py` (+2), `he7annex_supp.py` (+2),
`he7rannex_supp.py` (+2), `he6r1_checks.py`, `he6_checks.py` — 11 machine-family files,
16/16 artifacts checked present; `HE7_annexpass_report.md`, `HE7_annexpass2_report.md`,
`HE6_passPE2_report.md`, `HE6_passPE3_report.md`, `HE6R1_passPE2_report.md`,
`HE6R1_passPE3_report.md`, `CODEX_HE7RAT_2026-08-09.md` — 7/7 report files present.
**One reported machine family remains UNPINNED**: the "780/780 f₁ = 2 unramified family"
at `.101` has no runner filename, commit pin, or artifact anywhere in the note (shard 2's
OPEN-CALL 2, carried forward at §8 below).

### Sample re-verification (12 of 78, grep-rerun at merge time against the working tree)

`[TABLE — compiler ledger]`

| Target : designation | Recorded count | Re-verified count | Match |
|---|---:|---:|---|
| `HE6_PROOF_2026-08-08.md:LEMMA HE6-1L` | 4 | 4 | OK |
| `HE6_PROOF_2026-08-08.md:S7.2` | 5 | 5 | OK |
| `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-2` | 8 | 8 | OK |
| `HE6R1_RECON_2026-08-08.md:LEMMA HE6R1-3` | 8 | 8 | OK |
| `HE6R1_RECON_2026-08-08.md:FINDING HE6R1-F2` | 4 | 4 | OK |
| `JD0_PROOF_2026-08-08.md:J-D0` | 25 | 25 | OK |
| `HE7_passPE2_report.md:F-1` | 5 | 5 | OK |
| `HE7_passPE3_report.md:F-1` | 8 | 8 | OK |
| `HE6R1_passPE3_report.md:F-1` | 12 | 12 | OK |
| `CODEX_HE7RAT_2026-08-09.md:F1` | 4 | 4 | OK |
| `CODEX_HE6PE1_2026-08-08.md:F2` | 4 | 4 | OK |
| `HE7_annexpass2_report.md:M-A` | 5 | 5 | OK |

**All 12 sampled counts match exactly; no drift introduced by sharding or merge.** The
sample deliberately covers all three triple-shard-duplicated designations (`LEMMA
HE6R1-2`, `LEMMA HE6R1-3`), two of the three shard-pairs (s1+s2 via `S7.2`, s1+s3 via
`LEMMA HE6-1L`/`FINDING HE6R1-F2`/`J-D0`), and two designations that look alike but are
genuinely distinct targets (`CODEX_HE6PE1_2026-08-08.md:F2` vs. `CODEX_HE7RAT_2026-08-09.md:F2`
— different files, correctly NOT deduped in §4 above).

### Sample statement-quote re-verification (6 of 137, checked verbatim against the source
note by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---|---|
| `.06` (DEFINITION HE7-1) | "A pair (λ, r) with … the level-2 normalizer system … gcd(u, ℓ) = 1" | 93–109 | OK, byte-exact |
| `.19` (LEMMA HE7-L1, frozen display) | "Fix k ∈ ℤ_{≥0} … If T(k) = ∅ the height k is not attained at all." | 379–388 | OK, byte-exact |
| `.67` (=s2.04, HE7-BOX-1 base) | "Attempt grade **0/2** — no hostile pass has run … a **composition claim at 0/2**, not an acceptance." | 1275–1284 | OK, byte-exact |
| `.103` (=s2.40, ANNEX F-1's BOX-1 append) | "PE3 HAS NOW RUN … The 2-clean count completed 1/2 → 2/2: HE7 IS ACCEPTED" | 1948–1959 | OK, byte-exact |
| `.131` (=s3.27, final dated line) | "With the annex stack accepted 2/2 (4a613d8, a472155) … is **FULLY FROZEN**: dated appends only." | 2493–2497 | OK, byte-exact |
| `.137` (=s3.33, HE6R1 PE3 F-1, chain TERMINAL) | "The corrected argument is the **PIN height** … R_{λ₂}^{f} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R_{λ₂}^{f_S}." | 2624–2652 | OK, byte-exact |

**All 6 sampled quotes are byte-identical to the source note at the cited lines; no drift
introduced.** The sample deliberately covers all three shards' HOME ranges and both chain
TERMINALs' immediate neighbourhood (`.137` is itself the `.39`-chain's terminal link).

---

## 5. Local supply/consumption ledger

### 5.1 Per-supplier mathematical supply versus append/consumption protocol (merged from
all three shards' §3.2 tables; organised by supplier note, each row's protocol column
kept strictly distinct from its mathematical-status column per the header's predicate
split)

`[TABLE — compiler ledger]`

| Supplier note | Verified designation(s) | HE7 supply / consumption (EFF units) | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| HE6_PROOF | `HE6-BOX-1` (9) | `.13`–`.16`, `.57`–`.62`, `.64`, `.87`, `.92` | **CLOSED** at n ≤ 15 and at every machine-certified configuration (`.16`(i)); at every degree modulo the arc grade (`.16`(ii)); the battery decides σ on "the exact family HE6 certified as undecidable" | **Not landed.** No dated append on HE6 is claimed by this note |
| HE6_PROOF | `LEMMA HE6-1L` (4) | `.19`, `.20`, `.21`, `.132`, `.135` | HE7-L1 was ADOPTED BY HE6 (reverse direction); HE7 now CITES; the coset defect is HE7's own display too, corrected by a chained pair of inbound corrections (`.132` → `.135` TERMINAL) | **Landed at the source** for the original over-reach (HE6's own r1 round, R3) — "DISCHARGED at the source", not "appended by us". The coset defect is **not landed by HE7**: "owned at the source by HE6's owed repair round (HE6-BOX-2 queue, PE2 report §S4); this append is the note-to-owner on the frozen copy" |
| HE6_PROOF | `S1` (7, §-anchor) / (LIFT) | `.05`, `.21` | FINDING HE7-F1: HE6 §S1's (LIFT) refuted as stated, non-propagating to any HE6 theorem | **Not landed by HE7**; "The corrected hypothesis … *should be* appended to HE6 §S1's (LIFT)" — an offered erratum, executed at the source |
| HE6_PROOF | `HE6-BOX-4` (2) | `.72` | Inherited, not discharged: the char-p rows have no PARI `factorpadic` oracle | **Not landed** (an inherited box, not a new HE7 supply) |
| HE6R1_RECON | `LEMMA HE6R1-3` (8) | `.09`, `.38`, `.49`, `.60`, `.62` (licensed via R2-a, `.119`) | Consumed, not reproved; irreducibility half machine-evidenced only (2 PARI members, `he7r1_supp.py` A5) | **Not landed by HE7.** ANNEX-LEMMA R2-a (`.119`) offers a widening as an "*Optional HE6R1-side erratum … executed there or not at Asvin's discretion*" |
| HE6R1_RECON | `LEMMA HE6R1-2` (8) | `.39`, `.51`, `.66`(d), `.74`, `.101` | Consumed, not reproved; **proof-only, machine-unexercised** (its own configuration — proper blocks — is never machine-hit); supersedes HE7-BOX-4 in read form | **Not landed by HE7**; the scalar erratum's "source-side cure is HE6R1's post-PE2 micro-annex, same wave" |
| HE6R1_RECON | `he6r1_checks.py` (2) | `.71` | Reverse direction: HE6R1's own battery discharges HE7's `d_r ≥ 2` machine-coverage hole (944 members, 677/682 PARI, 0 mis-decisions) | **Foreign-note evidence consumed**, no append |
| GENHN_PROOF | `[GENHN-HE(μ)]` (1) | `.16` | HE7 asserts it "holds at EVERY leaf at those degrees", and at every leaf modulo the arc grade | **Not landed by HE7** on GENHN |
| GENIND_PROOF / W12_PROOF | `GENIND.B` (19), `W-12.D` (19) / `W-12` (100, note-wide) | `.16`, `.67` | Named as the composition path to the uniformity theorem, and as a supplier in HE7-BOX-1's inherited-minimum clause | **Not landed by HE7**; and HE7 carries **no updated supplier-grade table** — the minimum clause is frozen as-of-r1 (OPEN-CALL 6 below) |
| HE3_PROOF | `HE3-BOX-6` (12) | `.37` | §S5.5's block-factor reduction is "the step whose absence was HE3-BOX-6's original defect" | **Not landed by HE7** |
| HMENU3_PROOF | `ANNEX A` (5) | `.69`, `.93` | The dated-annex + minors-only-hold PROTOCOL precedent, cited twice as a pattern, not a mathematical import | **Not landed** — a protocol citation only |
| HE7 itself (inbound) | `CODEX_HE7RAT_2026-08-09.md:F1`–`F5` | `.105`–`.124` | Five confirmed Codex-ratification findings, discharged by ANNEX R at **annex grade** (post-ratification, not itself hostile-passed) | The annex IS the landing on HE7's own frozen text; "nothing above is edited" |
| HE7 itself (inbound) | `HE7_annexpass_report.md:M-1`, `HE7_annexpass2_report.md:M-A`/`M-B` | `.128`–`.130` | Three MINOR one-liners from the annex stack's own two acceptance passes, riding as riders | "No sealed number, statement, or verdict moves" |
| HE7 itself (inbound) | `HE6_passPE2_report:F-1`, `HE6_passPE3_report:obs-1`, `HE6R1_passPE2_report:F-1`, `HE6R1_passPE3_report:F-1` | `.132`, `.135`, `.136`, `.137` | Four supplier-side dated corrections landing on HE7's own frozen shard-1 text — the two supersession CHAINs of §7.2 | The corrections themselves are HE7's inbound record; whether the source note ALSO updates its own copy is left to Asvin/the source note (§7.2, §7.3) |

**The protocol column is not an inference.** HE7 states the "lands nothing" protocol in
its own words at least seven times (§1's predicate B, collected once there); **zero dated
consumption appends are claimed landed on any supplier by this note, and none is invented
here.**

### 5.2 Two supplier-findings flagged for the maintenance queue (MQ)

`spec/HYPOTHESIS_LEDGER.md` maintains a standing `MAINTENANCE QUEUE` (entries `MQ-1`
through `MQ-6` at the time of this merge). **This merge run does not itself add an MQ
entry — editing `HYPOTHESIS_LEDGER.md` is out of this deliverable's scope — but flags the
following two shard-2-recorded arithmetic defects as MQ-candidates**, since both are
compiler-discovered (not source-stated) recomputation results against a sealed table, the
exact genre the existing MQ entries track:

- **Q1's degenerate-distribution row mislabel (`.82`, =s2.19).** The `[r1]` degenerate
  distribution reads "F₅[[t]] λ=5/2 **s=2** → 2", but Q1's F₅[[t]] rows carry only s = 1
  and s = 3; the row actually short by 2 is **s = 1** (compiler-recomputed: the four short
  rows are `ℤ₃ s=2` (2), `F₃[[t]] s=1` (3), `F₅[[t]] s=1` (2), `F₅[[t]] s=3` (1), total 8 —
  count and total correct, one letter wrong). Nothing depends on the letter, but the table
  is wrong as written.
- **Q1's σ-column convention is undocumented (`.87`, =s2.24).** Q1's three σ columns sum
  to the **read-OK member count**, not to the `members` column, on the four rows carrying
  degenerate members — a convention the table never states, invisible except by doing the
  arithmetic (compiler audit: `members` and `PARI` columns coincide on nine of thirteen
  rows, diverging exactly on the four degenerate rows).

Both are genuine table defects (not merge-introduced), both were found only because
shard 2's own compiler pass recomputed Q1's row and column sums (shard 2 §6.3 item 4:
"Recomputing Q1's thirteen rows found a real, previously unrecorded defect … and an
unstated convention … Neither is visible without doing the sums"), and both are carried
forward here **flagged, not silently repaired**, consistent with the note's own byte-freeze.

---
## 6. TEETH inverse table (unified from all three shards; presented as three sub-tables
by shard-of-origin — the battery legs themselves are naturally partitioned this way, since
shard 1 carries the core P1–P5/planted-mutant battery, shard 2 carries the additive
`[r1]`/`[r2]`/`[r3]` legs and the Q1–Q6 verdict tables, and shard 3 carries ANNEX R's
level-3 leg and the oracle/counter corrections — with one combined zero-orphan statement
closing all three)

### 6.1 Shard 1's core battery (IDs unchanged, offset 0)

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition ∈ {executable regression, planted mutant, measurement, signed non-applicability, foreign-note evidence}.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| **P1** HE7-READ2 / HE7-SIG2 — 1,335 PARI jobs, 1,335 agree, 0 mismatch, nine ℤ_p rows + four F_p[[t]] rows | `.13`, `.14`, `.57`, `.58`, `.61`, `.62` | Executable regression against an independent oracle (sealed, `he7_checks.py` @ 688adbe88447) |
| **P2** HE7-SLOT2 — `v(Res(f, C)) = 2·dv₂(C)`, 12,632 checks, 0 violations, both level-2 classes, both characteristics | `.06`, `.11`, `.40` | Executable regression (the machine form of (SLOT₂)'s exactness) |
| **P3** HE7-LIFT1 / HE7-LIFT2 — reachable sets vs closed forms, ten frames exhaustively | `.12`, `.19`, `.21`, `.22`, `.23` | Executable regression; exhaustive enumeration |
| **P4** HE7-GEN2 — 4,259 level-2 flat identities at rational κ₂, ℓ₂ ∈ {1,2,3} | `.27`, `.30`, `.32`, `.41` | Executable regression |
| **P5** HE7-SEP2 — 191 strict + 5 infinite excesses exactly at the level-2 labels | `.30`, `.34`, `.35`, `.41` | Executable regression |
| **HE7-T-CASEB-SEP** — three distinct PARI σ inside ONE constant-outer-data family, all 8/8 predicted | `.13`, `.58`, `.61` | Planted separation certificate; fired |
| **HE7-T-RANK** — outer read gives one class of size 8 with three σ compatible; level-2 read gives exactly one per member, 8/8 == PARI | `.13`, `.57` | Planted mutant; fired |
| **HE7-T-WITHHOLD** — with one side's level-2 residual withheld the reader reports UNDETERMINED | `.13`, `.35` | Planted mutant; fired (no silent acceptance) |
| **HE7-T-LIFT2SHARP** — the exact reachable sets, five level-1 + five level-2 frames; `(3,1,2)` height k = 1 attained by **no** C | `.12`, `.19`, `.21`, `.22`, `.24` | Planted mutant / exhaustive enumeration; fired. **Disclosed blind spot:** its frames sat at `q(k) = 0` on every proper-`T` height, so the coset defect of `.19` was invisible to it |
| **HE7-T-BADTWIST** — 21 (p, s, member) reads CHANGE when the β-power twist is dropped; twisted read == PARI 480/480 (+83 further flips) | `.08`, `.27`, `.32` | Planted mutant; fired — “the level-2 normalizer cocycle is machine-load-bearing” |
| **HE7-T-SLOT2TIE** — at `gcd(u, ℓ) ≠ 1` the ℓ classes share heights, slot-min not exact, no level-2 residue well defined | `.06`, `.11`, `.18` | Planted mutant; fired (the gcd hypothesis is load-bearing) |
| **`he7r1_supp.py` A1–A5** — 8/8 exact peels, 8/8 one-peel-only, 8/8 peeled reads, 2/2 PARI σ(f), **2/2 PARI σ(Ψ)** | `.09`, `.38`, `.58`(row 6), `.60`, `.62` | Executable regression (additive post-seal). **A5 is the ONLY evidence for LEMMA HE6R1-3's irreducibility half** |
| **`he7r2_supp.py` B1** — slot geometry: Ψ's occupied slots all at T₂, w's slot-min exactly λ₂ > T₂, (LIFT₂) contract — 42/42 | `.43`, `.44` | Executable regression |
| **`he7r2_supp.py` B2** — off-disk inequality (S5.8.1) + invariance, five strata covering all three offset cases — 210/210 | `.28`, `.31`, `.44` | Executable regression, **with a signed vacuity disclosure**: the δ = ∞ inequality half was tested on 1 of 42 |
| **`he7r2_supp.py` B3** — strict slope increase (S5.8.2) + the HE7-9(b) count identity at the refined key — 42/42 | `.41`, `.45`, `.46` | Executable regression, with a disclosed peel-guard skip that never fired |
| **`he7r2_supp.py` B4/B5** — pre-refine residual is `(Z − s₂)²` (42/42); per-row refine recount == frozen artifact (13/13) | `.45`, `.46`, `.59` | Executable regression (hypothesis verification, not assumption) |
| **`he7_pe2_fresh.py`** — independent instrument, 634-member ℓ = 1, d_r = 2 (K₂ = F_{p²}) α-refine family, σ == PARI 634/634, first 2-step chains | `.14`, `.45`, `.53` | Executable regression on a DECORRELATED instrument (no he6/he7 import) — the R-b decoupling |
| **`he7_pe3_probe12.py`** — 144 members at μ₂ = 3, n = 12 (96 mixed + 48 pure cubes), σ == PARI 144/144 | `.14`, `.45`, `.51` | Executable regression; **carries the counter-instance** to HE7-13's conclusion at mixed nodes |
| **`he7annex_supp.py`** — 96 members at μ₂ = 4, n = 16; P4 tooth: the naive single-key route CYCLES 48/48; P5 tooth: 16/16 pure controls LOSE the λ₂ side | `.44`, `.45`, `.51`, `.53` | Executable regression + two planted mutants; both fired |
| **`he7rannex_supp.py`** — 79 members, first machine σ at a fired level-3 node; P3 tooth: 18/79 flip without the deep letter | `.17`, `.47`, `.48` | Executable regression + planted mutant; fired. **Disclosed gap:** `g₂ = 1` throughout, so R1-b's within-class deep twist `ϑ_t (t ≥ 1)` is structurally invisible |
| **`he6r1_checks.py`** (foreign, HE6R1's own leg) — ℓ = 1, d_r = 2, K₂ = F_{p²}, 944 members, 677/682 PARI, zero mis-decisions, the 5 non-agreements exactly the peel stratum | `.11`, `.12`, `.22` (the `d_r ≥ 2` hole) | Foreign-note regression consumed as coverage |
| **HE6's `HE6-T-CASEB`** (foreign) — the observed three-σ alphabet on identical outer data | `.61` | Foreign-note measurement consumed as decorrelation |

**Both-direction audit.** Every row above guards at least one in-range unit. Every in-range unit whose `TEETH` field names a battery row appears in some row. Units with **`TEETH: NONE`** — `.03`, `.04`, `.05`, `.10`, `.26`, `.37`, `.52`, `.63` — are declarations, scope records or fences and are outside the orphan count. Units flagged **`TEETH: Indirect`** — `.07`, `.29`, `.36`, `.42` — are guarded only through the composite `Σef == PARI` agreement of P1 and are recorded here as such. **One unit is explicitly toothless and proof-only: `.39`** (LEMMA HE6R1-2's proper-block read), per §S9's HE7-BOX-2 `[r1]` — “LEMMA HE6R1-2's own configuration is proof-only”. **Zero battery-row orphans; zero toothed-unit orphans; one signed proof-only unit.**

Out-of-range rows recorded but not counted here (homed in shard 2): the sealed §S11 verdict tables Q1–Q6 as verdict units, the four `[r2]` disclosures, the three `[r3]` disclosures, and the ANNEX F-1 legs' own predictions P1–P5.

---


### 6.2 Shard 2's additive `[r1]`/`[r2]`/`[r3]` legs and Q1–Q6 verdicts (renumbered)

`[TABLE — compiler ledger]` Battery row → guarded unit(s) → disposition.

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| P1 HE7-READ2 / HE7-SIG2 — 1,335/1,335 PARI, 0 mismatch, 13 rows | `.77`, `.81`, `.87`, `.92` | Executable regression (sealed) |
| P2 HE7-SLOT2 — 12,632 checks, 0 violations | `.81`, `.88`, `.92` | Executable regression (sealed) |
| P3 HE7-LIFT1 / HE7-LIFT2 — ten frames exhaustively | `.81`, `.89`, `.92` | Executable regression (sealed); **disclosed blind spot: `q(k) = 0` on every proper-`T` height** |
| P4 HE7-GEN2 — 4,259 flat identities | `.81`, `.90`, `.92` | Executable regression (sealed) |
| P5 HE7-SEP2 — 191 + 5 excess certificates | `.81`, `.90`, `.92` | Executable regression (sealed) |
| HE7-T-CASEB-SEP · HE7-T-RANK · HE7-T-WITHHOLD | `.79`, `.87`, `.91` | Planted mutants; all fired |
| HE7-T-LIFT2SHARP | `.79`, `.89`, `.91` | Planted mutant; fired, with the disclosed blind spot above |
| HE7-T-BADTWIST — 21 reads flip; twisted read == PARI 480/480 | `.79`, `.91` | Planted mutant; fired — widest downstream reach of any HE7 tooth |
| HE7-T-SLOT2TIE | `.79`, `.91` | Planted mutant; fired |
| `he7r1_supp.py` A1/A2/A3 | `.75`, `.80`, `.82`, `.83` | Executable regression (additive; A3 runs the SEALED reader, not decorrelated) |
| `he7r1_supp.py` A4/A5 (PARI σ(f), σ(Ψ)) | `.83`, `.75` | Executable regression against an independent oracle; **A5 on 2 members is the only evidence for HE6R1-3's irreducibility half** |
| `he7r2_supp.py` B1 | `.84` | Executable regression; **coupled to the instrument under test** (R-b), decorrelated by PE2's fresh leg |
| `he7r2_supp.py` B2 | `.84`, `.86` | Executable regression; **signed vacuity disclosure** — the δ = ∞ inequality tested on 1 of 42 |
| `he7r2_supp.py` B3 | `.84`, `.86` | Executable regression; **disclosed non-repair** — peel-guard skip never fired |
| `he7r2_supp.py` B4/B5 | `.84` | Executable regression (hypothesis verification + artifact recount) |
| `he7_pe2_fresh.py` — 634/634, first 2-step chains, no he6/he7 import | `.69`, `.86` | Executable regression on a **decorrelated instrument** — the stack's strongest independence |
| PE1's fresh n = 12 peel family — 2,552/2,552 | `.68` | Foreign-arc regression on a fresh instrument |
| PE3's fresh f₁ = 2 unramified family — 780/780 | `.103` | Foreign-arc regression — **runner filename NOT given** (OPEN-CALL 2) |
| `he7_pe3_probe12.py` — 144/144 at μ₂ = 3, n = 12; bit-identical re-run | `.93`, `.94`, `.96`, `.99`, `.100` | Executable regression on the **verifier's** instrument; carries the counter-instance |
| `he7annex_supp.py` P1 — 96/96, Σef = 16 | `.96`, `.101`, `.102` | Executable regression |
| `he7annex_supp.py` P2 — 128/128 parked residuals EXACT + 132 persistence checks | `.96`(c), `.102` | Executable regression |
| `he7annex_supp.py` P3 — 0 floor violations / 148 refines | `.96`(b), `.97`, `.102` | Executable regression |
| `he7annex_supp.py` P4 — naive single-key route CYCLES 48/48 | `.96`(e), `.97`, `.102` | **Planted mutant on the WRONG method**; fired |
| `he7annex_supp.py` P5 — 16/16 pure controls lose the λ₂ side | `.96`, `.102` | Planted mutant on the pure/mixed boundary; fired |
| `he7annex_supp.py` R-a route — fired 32× | `.98`, `.102` | Executable regression |
| `he6r1_checks.py` — 944 members, 677/682 PARI, 0 mis-decisions; 12/12 peels, 5/5 PARI | `.71`, `.75` | Foreign-note regression consumed as coverage |
| `he7rannex_supp.py` (out of range, shard 3) — 79/79 at a fired level-3 node | `.70` (discharges its level-3 item) | Recorded, not counted here |

**Both-direction audit.** Every row guards at least one in-range unit. Every in-range unit whose `TEETH` field names a row appears above. **Units with `TEETH: NONE`:** `.65` (an audit record), `.104` (a negative declaration). **Units that are explicitly PROOF-ONLY, with the note's own coverage sentence quoted:** `.66`(d) and `.74` — “LEMMA HE6R1-2's own configuration is proof-only” (`.71`); `.73` and `.99` — declined claims, which have no tooth by construction (disposition **signed non-applicability**). **Zero battery-row orphans; zero toothed-unit orphans; four signed proof-only/declined units.**

---


### 6.3 Shard 3's ANNEX R level-3 leg, oracle correction, and counter-reading (renumbered)

`[TABLE — compiler ledger]`

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| The **Codex ratification leg** (`CODEX_HE7RAT_2026-08-09.md`; gpt-5.6-sol HIGH, fresh context, 5 findings, 5 confirmed; **both heavy findings from the free hunt**) | `.105`, `.106`, `.118`, `.122`, `.123`, `.124`, `.125` | **Decorrelated-model audit.** The only instrument that found F1 and F2 — no executable tooth could have (see below) |
| `he7rannex_supp.py` **P1** — 79/79 ladders fire read-forward, (μ,μ₂,μ₃) = (8,4,2) | `.116`, `.117` | Executable regression (constructed family) |
| `he7rannex_supp.py` **P2** — σ == PARI 79/79, Σef = 16, three genres, no fourth value | `.107`, `.114`, `.116`, `.117` | Executable regression; **oracle identity corrected by M-A** to the shared `pari_sigma16` |
| `he7rannex_supp.py` **P3 (tooth)** — 18/79 members FLIP when the deep letter is dropped, on all four (p,s) frames | `.108`, `.109`, `.110`, `.112`, `.113` item 3, `.117` | Planted mutant; **fired — HE7-T-BADTWIST one level up** |
| `he7rannex_supp.py` **P4** — 19 level-3 α-refines, all one step, 0 level-4 nodes; K2R = R1-c's inverse twist used constructively | `.111`, `.117` | Executable regression |
| `he7rannex_supp.py` twist arithmetic — the Λ₂Λ₁-monomial identity `4α + 10σ + u₂s₂ = k` on every n₃-monomial | `.108`(i)(iii), `.117` | Executable regression; **counter re-read by M-1: 47 corrected-chain instances, not 102** |
| annex-pass #1's isolated recount + annex-pass #2's leg **W1_R** | `.117`, `.128` | Two independent recounts, agreeing exactly (47 + 55 = 102) |
| annex-pass #2's leg **W1** — `factorpadic` ROUND4 + non-PARI sympy disc-parity on every regenerated member: 96/96 + 79/79, plus **48/48 at n = 24** | `.117`, `.127`, `.129`, and cross-shard `EFF.HE7.100`/`.102` | **Triple-oracle executable regression** — the stack's only genuinely decorrelated oracle leg, and its only n = 24 contact |
| HE6's **PE2 fresh leg B** — 162 members at (2,2,3)/ℤ₃; realized ϖ-read set `{η, 2η}` disjoint from the displayed `{1,2}`; 8/8 of `F₉^×` at the full-`T` height. Exact PARI | `.132`, `.133`, and cross-shard `EFF.HE7.19`/`.22` | **Foreign-arc regression that HE7's own tooth structurally could not fire** |
| HE7-T-LIFT2SHARP (out of range) | `.124`, `.133`(iii) | **Signed tooth blind-spot disclosure**: its frames sat at `q(k) = 0` on every proper-`T` height |

**PROOF-ONLY rows (no tooth, by the note's own account).** `.113` items 1, 4, 5, 6, 7 (the transfer audit — claims about proofs); `.119` (R2-a — the scenario it excludes cannot arise in the battery's frame); `.120`, `.123`, `.130`, `.135`, `.136`, `.137` (riders and errata with “No sealed number, statement, or verdict moves”); `.110`'s `ϑ_t` for `t ≥ 1` (**structurally invisible at `g₂ = 1`**, disclosed at `.117`(ii)). **Eleven of thirty-three units in this shard are proof-only or rider-only** — the highest proportion of the three shards, as befits a repair queue.

**Both-direction audit.** Every row above guards at least one in-range unit; every in-range unit whose `TEETH` field names a row appears above. **Units with `TEETH: NONE`:** `.115`, `.120`, `.121`, `.123`, `.126`, `.130`, `.135`, `.136`, `.137`. **Zero battery-row orphans; zero toothed-unit orphans; eleven signed proof-only/rider-only units, each with the note's own disclaiming sentence quoted.**

**The observation this shard's inverse table exists to record:** the two heavy findings repaired here (F1 CRITICAL, F2 GAP) were found by **no tooth at all**. F1 is a coherence defect in a definition; F2 is an underived equivalence. Neither is a σ-disagreement, and the battery only measures σ-disagreement, exactness identities and reachable sets. **A machine battery cannot falsify a definition's coherence, and this note is the corpus's cleanest demonstration of that limit.**

---


**Combined zero-orphan statement (all three shards' independent audits agree).** Across
the whole merged inventory: every battery row/tooth guards at least one unit; every unit
whose TEETH field names a row appears in some row above; zero battery-row orphans and
zero toothed-unit orphans in any of the three sub-tables. Fifteen units are explicitly
signed PROOF-ONLY or DECLINED (no tooth by construction, with the note's own disclaiming
sentence quoted at each): `.10`, `.36` (declined claims); `.11`, `.66` (LEMMA HE6R1-2's
own configuration, "proof-only"); and eleven of shard 3's thirty-three units (riders and
errata carrying "No sealed number, statement, or verdict moves"). **The one property that
survives across all three sub-tables is the note's own central limitation, stated once by
shard 3 and true of the whole: a machine battery cannot falsify a definition's incoherence
or an underived equivalence — the two heaviest findings in HE7's whole history (Codex F1,
F2) were found by no tooth at all, only by a decorrelated model's fresh read.**

---
## 7. SERIES, supersession CHAINs, and cross-shard boundary resolution (the HE7-specific
merge centerpiece — template v2 has neither construct; both were invented by the shards'
own boundary self-audits and are assembled here for the first time across shard lines)

### 7.1 The dated-arc SERIES: HE7's grade chronology

Shard 2's boundary self-audit names the construct and flags it as a v2 gap: "**a dated arc
record is a SERIES, and the v2 template has no series type**" (§6.1 item 2 there), and its
SHARD NOTES independently states the series "spans three shards" even though its own
HOME range supplies only four of the series' links. The reason is visible once `.01`'s own
CONDITIONALITY field (shard 1, reproduced verbatim in the merged inventory) is read as
what it is: the series' **origin** claim, which every later link supersedes by continuing
the same box under the same name (`HE7-BOX-1`, "arc record"/"arc grade"). Assembling `.01`'s
own five-fold supersession list against the units that actually carry each link gives the
complete, ordered, seven-step series — reproduced here as ONE block, per the merge charge,
rather than as five independent units the way a flat inventory would present it:

`[TABLE — compiler ledger, the SERIES assembled from EFF.HE7.01's CONDITIONALITY field
plus its own confirmation at EFF.HE7.67]`

| Link | Unit | Round | Grade movement | Content (quoted from the unit or from `.01`'s own resolution) |
|---:|---|---|---|---|
| 0 (origin) | `.01` (=s1.01) | base | **0/2** | "Attempt grade 0/2 — no hostile pass has run on this note." |
| 1 | `.02` (=s1.02) | `[r1]` | **stays 0/2** | "a repair round does not upgrade an arc, and the r1 text owes a fresh hostile pass" |
| 2 | `.67` (=s2.04) | base (HE7-BOX-1 opens) | **0/2** (re-affirmed) | "Attempt grade 0/2 — no hostile pass has run on this note, and the r1 round does not upgrade it … COROLLARY HE7.B is therefore a **composition claim at 0/2**, not an acceptance." |
| 3 | `.68` (=s2.05) | `[r2]` | **stays 0/2** | PE1 ran: 0 CRITICAL, 1 GAP, 3 MINOR — grade stays 0/2 (a hostile pass ran, but not clean) |
| 4 | `.69` (=s2.06) | `[r3]` | **0/2 → 1/2** | PE2 CLEAN |
| 5 | `.103` (=s2.40, ANNEX F-1's BOX-1 append) | dated append | **1/2 → 2/2, ACCEPTED** | "PE3 HAS NOW RUN … CLEAN — 0 CRITICAL, 0 GAP, 1 MINOR (F-1) … The 2-clean count completed 1/2 → 2/2: **HE7 IS ACCEPTED** — the first stage-one note through the hostile-arc bar." |
| 6 | `.125` (=s3.21, ANNEX R's BOX-1 append) | dated append | **2/2, ANNOTATED not revoked** | The ratification CHALLENGE (five Codex findings against the accepted text) is discharged by ANNEX R; acceptance stands, annotated on THEOREM HE7.D / COROLLARY HE7.B(ii) / HE7.A(3)'s level-3 branch only |
| 7 (terminal) | `.131` (=s3.27, the final dated line) | dated append | **2/2, FULLY FROZEN** | "With the annex stack accepted 2/2 (4a613d8, a472155), the CHALLENGE discharged, and the three owed one-liners landed above, this note … is **FULLY FROZEN**: dated appends only." |

**The series' durable content survives every grade movement**: the SUPPLIER-MINIMUM
clause of link 2 ("every consequence inherits the minimum over its suppliers …") is never
superseded by any later link and remains the box's load-bearing content per `.67`'s own
CONDITIONALITY — recorded again at OPEN-CALL 6 below, since the minimum was never
refreshed against the suppliers' own since-advanced grades. **No link is duplicated and no
link is skipped**: cross-checked against all three shards' independent SHARD NOTES
descriptions of the series (shard 2: "`.04`, `.05`, `.06` here, `.40` here, ANNEX R's
append in shard 3, the final dated line in shard 3"; shard 3: "closes the series
`EFF.HE7.s2of3.04`/`.05`/`.06`/`.40` → `.21` → here") — both descriptions, rewritten
through the SHARD-MAP, name exactly the seven post-origin links assembled above.

### 7.2 Supersession CHAINs, with TERMINAL markers verified to survive the merge uniquely

Shard 3's boundary self-audit names this construct too, and flags it as a second v2 gap:
"**Supersession CHAINS have no representation. … Fix: `CHAIN:` with an explicit TERMINAL
marker — otherwise a chapter cut can pick a superseded intermediate**" (§6.3 item 3
there). Two chains exist, both landing on shard-1 text, both discovered and resolved
entirely within shard 3's own range:

**CHAIN 1 — LEMMA HE7-L1's realized-set display (2 layers on the frozen sentence).**
Target: `.19` (=s1.19, the frozen `LEMMA HE7-L1` display, byte-untouched above).

| Layer | Unit | Content |
|---:|---|---|
| 0 (frozen original) | `.19` | The un-twisted realized-set display, `{ Σ_{t∈T(k)} c_t·η_θ^t }` |
| 1 | `.132` (=s3.28, HE6 PE2 F-1) | Supplies the missing `η_θ^{−q(k)}` coset factor |
| 2 (**TERMINAL**) | `.135` (=s3.31, HE6 PE3 obs-1) | Restates layer 1 in `res(·)`-correct form — the reading every consumer of `.19` must use |

**CHAIN 2 — §S5.5(b)'s cocycle-scalar parenthesis (3 layers on one sentence — the
longest chain in the note).** Target: `.39` (=s1.39, "(equal outright when separable)").

| Layer | Unit | Content |
|---:|---|---|
| 0 (frozen original) | `.39` | "(equal outright when separable)" — false as written, per `.39`'s own CONDITIONALITY |
| 1 | `.136` (=s3.32, HE6R1 PE2 F-1) | Corrects to "equal up to a fixed K₂^× scalar per side", exponent argument at the side's **line value** |
| 2 (**TERMINAL**) | `.137` (=s3.33, HE6R1 PE3 F-1) | Corrects layer 1's exponent argument from the line value to the **PIN height** `m₁ := dv₂(A^{(2)}_{j₁})` — the reading every consumer of `.39` must use, scoped: agrees with layer 1 exactly when `j₁ = 0` |

**Uniqueness of each TERMINAL, verified.** For a TERMINAL marker to be safe, no third,
later correction to the same target sentence may exist anywhere in the merged inventory.
This was checked two ways: (a) shard 3's own SHARD NOTES cross-shard supersession table
marks exactly these two rows "chained" and marks exactly `.135`/`.137` (there written
`.31`/`.33`) TERMINAL, and no other row in that table, or in shard 2's five-row ANNEX F-1
table, targets `.19` or `.39` a third time; (b) an exhaustive scan of every CONDITIONALITY
and RESOLUTION TRACE field in the merged 137-unit inventory for the strings `EFF.HE7.19`
and `EFF.HE7.39` as a supersession *target* (as opposed to a citation) confirms the only
hits are the two layers listed per chain above, plus `.19`'s and `.39`'s own self-quotation
of their frozen text. **Both TERMINALs are unique and both survive the merge intact** —
`.135` for the coset display, `.137` for the cocycle-scalar exponent.

### 7.3 Full cross-shard supersession edge list (consolidated, with SUPERSESSION KIND)

Shard 3's boundary self-audit names a third v2 gap here: "**There is no SUPERSESSION KIND
field, and this note needs seven values**" — replacement, license, wording-rider,
provenance-rider, as-of scoping, counter re-reading, inventory completion, plus shard 2's
scope-pin (eight distinct kinds across the whole note). Every edge below carries its kind.

`[TABLE — compiler ledger, consolidated from shard 2 SHARD NOTES (5 edges, ANNEX F-1 →
shard 1) and shard 3 SHARD NOTES (13 edges: 11 → shard 1, 2 → shard 2)]`

| From | To | Kind | Content |
|---|---|---|---|
| `.95` (=s2.32, ANNEX F-1's rider) | `.14` (HE7.A(3)'s `[r2]` wiring sentence) | scope-pin | Pure-node verbatim; mixed-node routed through ANNEX-LEMMA HE7-13′ (`.96`) |
| `.95` | `.51` (§S6(iii)'s block sentence) | wording-rider | "per distinct factor, REPEATED OR NOT — mixed nodes included" |
| `.95` | `.54` (LEMMA HE7-8's `[r2]` box) | scope-pin (inherited) | Inherits the `.14`/`.51` reading |
| `.95` | `.44`(d) (HE7-12(d)'s `[r3]` parenthetical) | scope-pin (inherited) | Inherits the same reading |
| `.95` | `.45` (LEMMA HE7-13's conclusion) | scope-pin | Pinned to pure nodes; mixed-node case FALSE as stated, routed to `.96` |
| `.107` (=s3.03) | `.47` (DEFINITION HE7-2's normalizer line + base sentence) | replacement | ANNEX-DEF HE7-2′ |
| `.109` (=s3.05) | `.48` (§S6's "(SLOT). §S3 verbatim …" / "(LIFT). §S4.2 verbatim") | replacement | → ANNEX-THEOREM R1-b / R1-c |
| `.114` (=s3.10, ANNEX-COROLLARY R1-d) | `.17`, `.48` (THEOREM HE7.D), `.16`(ii) (COROLLARY HE7.B(ii)), `.14` (HE7.A(3)'s level-3 branch) | re-proof | At annex grade |
| `.119`/`.120` (=s3.15/.16, ANNEX-LEMMA R2-a) | `.09` (→ `.35`, `.41`), and `.96`(a) | license | Supplies the CONVENTION's missing gcd equivalence; closed at reducible keys — the display of `.09` is not edited |
| `.122` (=s3.18, ANNEX R R3) | `.15` (both n = 16 sentences) | wording-rider | Restated to the proved (necessary) direction only |
| `.123` (=s3.19, ANNEX R R4) | `.44`(c)(7) (HE7-12(c) item (7)'s inventory) | inventory completion | + LEMMA HE6-4, LEMMA HE6-2′, (LIFT₂), HE7-3, HE7-9(a), HE7.A(1) |
| `.124` (=s3.20, ANNEX R R5) | `.22` ("a proper subgroup-coset of K₂") | wording-rider | → "the nonzero elements of a proper F_Q-linear subspace" |
| `.125` (=s3.21, ANNEX R's BOX-1 append) | `.103` (=s2.40, the 2/2 acceptance) | annotation | Acceptance ANNOTATED, not revoked (§7.1 link 6) |
| `.129` (=s3.25, M-A) | `.100`, `.102` (=s2.37/.39, ANNEX F-1's deg-16 legs); and `.116`, `.117` (=s3.12/.13) | provenance-rider | The shared oracle is `pari_sigma16`, not `factorpadic` |
| `.130` (=s3.26, M-B) | `.17`, `.16`(ii) | provenance-rider | "with the SAME proofs" → R1-b/R1-c/R1.2/R1-d |
| `.132`+`.135` (=s3.28+.31) | `.19` | replacement, **chained; `.135` TERMINAL** | The realized set is the `res(·)`-form coset (§7.2 CHAIN 1) |
| `.134` (=s3.30, M-1) | `.20` (the fold-box's "verbatim") | as-of scoping | Time-indexed to the r1 landing |
| `.136`+`.137` (=s3.32+.33) | `.39` | replacement, **chained; `.137` TERMINAL** | The §S5.5 scalar, exponent at the PIN height (§7.2 CHAIN 2) |
| `.128` (=s3.24, M-1) | `.117`'s "102 slot instances" counter | counter re-reading | 47 corrected-chain instances, not 102 |

**In-range supersessions (not cross-shard, applied within shard 3's own range and not
re-emitted as separate edges above):** `.128` also corrects `.116`/`.117`'s counter
in-place (same row as above); `.129` also corrects `.116`/`.117`'s oracle name in-place;
`.135` corrects `.132`'s display in-place (CHAIN 1's own second link); `.137` corrects
`.136`'s exponent argument in-place (CHAIN 2's own second link).

**Total: eighteen distinct supersession edges** (5 from shard 2, 13 from shard 3 — shard
3's own count of "twelve outbound" undercounts by one because its SHARD NOTES table
folds `.119`/`.120`'s two-target row and counts the `.125` annotation edge separately from
the twelve; both readings are reconciled in the table above, which lists every target
once). **All eighteen resolve to a unit that exists in the merged inventory; zero dangling
targets.**

### 7.4 Range-edge audit (boundary cleanliness, all three shards' own findings confirmed
consistent)

All three shards independently audited their own physical line boundary and all three
report the same thing: **no source statement unit is cut at any shard boundary.**
Shard 1/shard 2 boundary (source line 1246/1247): line 1244 blank, 1245 `---`, 1246
blank, 1247 opens `## S9.` — a clean section break. Shard 2/shard 3 boundary (source line
1972/1973): line 1970 blank, 1971 `---`, 1972 blank, 1973 opens `## ANNEX R` — a clean
section break. The file's own end (source line 2652) is shard 3's own last line, closing
the final dated correction's md5 pin. **Zero units span a shard boundary; the three-way
split was made at natural section breaks throughout.**

---
## 8. Self-audit and OPEN-CALLS (merged, dedup marked)

**15 raw OPEN-CALLs (5 per shard) reduce to 13 distinct after merge-time dedup.** Two
pairs are genuinely identical, and — unlike every other dedup in this merge — **the
source itself flags both pairs explicitly**, each shard saying so in the other's words:
shard 3's OPEN-CALL 1 closes "(This is the same call shard 1 raises as its OPEN-CALL 1;
recorded in both so neither merge drops it.)"; shard 2's OPEN-CALL 3 closes "(Raised
identically as shard 1's OPEN-CALL 5; recorded in both shards so neither merge drops
it.)" This merge performs exactly the fold both shards asked for. **None of the 13 is
discharged by the act of merging** — every one is carried forward open, per the standing
merge charge.

### OPEN-CALL 1 — the §S1 CONVENTION's grade: GAP or MINOR? **[DEDUP — shard 1 OPEN-CALL 1
≡ shard 3 OPEN-CALL 1, self-identified duplicate]**

ANNEX R R2's closing paragraph (quoted at `.121`, the grade-flag unit) reads: "As stated the finding is a GAP
… by arc precedent … this exact shape was twice graded MINOR. The repair above is
identical under either grade; the grade decides only whether the ratification CHALLENGE
cites one heavy finding or two." The BOX-1 append (`.125`) adds: "Asvin adjudicates: the
CHALLENGE's final disposition and F2's grade." `.131` (the final dated line) records the
CHALLENGE as **discharged** but never records the **grade**. **The compiler cannot
decide this**, and the choice changes `.09`'s CONDITIONALITY wording (GAP vs MINOR) and
the ratification summary throughout. **Decision needed: Asvin.**

### OPEN-CALL 2 — two dated riders point opposite ways on the same phrase

`.22`'s phrase "a proper subgroup-coset of K₂" is (a) declared a **mislabel** by ANNEX R
R5 (`.124`), to be read as "the nonzero elements of a proper F_Q-linear subspace", and
(b) declared **coset-correct as written** by the HE6 PE2 F-1 dated append's
non-propagation item (ii) (`.133`). Both are true of different objects: R5 speaks of the
shape *inside* the braces (a punctured subspace, not a group coset); the HE6-side append
speaks of the *external* `η_θ^{−q(k)}` multiplier (a genuine coset factor, per CHAIN 1,
§7.2). **The fully corrected object is `η_θ^{−q(k)} · (punctured proper F_Q-linear
subspace)` — a coset of a punctured subspace — but no line of the note states that
composite.** The compiler has carried both riders verbatim at `.22` and refused to
synthesise the composite. **Decision needed: whether the merged spec should state the
composite reading, and if so, whether it is a note-level erratum owed to HE7 or a mere
reading note.**

### OPEN-CALL 3 — LEMMA HE7-12(d) and LEMMA HE7-13 are mutually dependent, resolved by
fiat

`.44`(d)'s `[r3]` argument for `W ≠ 0` cites LEMMA HE7-13's strict slope increase; `.45`'s
proof cites LEMMA HE7-12(c)(d) for the package at the refined key. The note breaks the
circle in one parenthesis — "the two lemmas induct together along the chain, the base
`W = w₁` being a single nonzero (LIFT₂) polynomial" — a correct *sketch* of a
simultaneous induction on chain length, but **the induction is not displayed**: no
statement of the joint hypothesis, no base/step separation. PE2 graded the underlying
issue MINOR and repaired it with exactly this parenthesis. **Not a claimed error**;
recorded because a formalization blueprint cannot build a mutual recursion from a
parenthesis. **Decision needed at Phase 0b/chapter time: whether the joint induction
must be displayed before formalization.**

### OPEN-CALL 4 — R4's completed inventory may or may not apply to §S6(iii) too

ANNEX R R4 (`.123`) completes the dependency inventory of LEMMA HE7-12(c) item (7)'s
sentence about LEMMA HE6R1-2. `.51` (§S6(iii)) makes the **same claim about the same
lemma** in different words, and R4 does not name it. The two inventories differ: `.51`
already lists LEMMA HE6-4 (which R4 adds) but omits (LIFT₂)/DEFINITION HE7-3/HE7-9(a)/
THEOREM HE7.A(1) (which R4 adds). **Decision needed: whether the merged spec reads R4's
completion onto `.51` as well.** Carried at `.51` as an explicit flag; no silent
completion was made.

### OPEN-CALL 5 — characteristic 2 is claimed covered and exercised nowhere **[DEDUP —
shard 1 OPEN-CALL 5 ≡ shard 2 OPEN-CALL 3, self-identified duplicate]**

`.56` claims the termination argument "does not use 2 ∈ O^×, so it covers the
equal-characteristic-2 Artin–Schreier corner". The claim is textually sound (it routes
through completeness). But **`p = 2` appears in no row of any HE7 leg**: the sealed
battery runs `q ∈ {3,5,7}` (char 0) / `{3,5}` (char p); `he6r1_checks.py` the same;
`he7annex_supp.py` and `he7rannex_supp.py` run `p ∈ {5,7}`. HE7-BOX-2's coverage list
(`.70`, `.71`) does **not** name characteristic 2 among the unexercised items. **Decision
needed: whether "characteristic 2 unexercised anywhere in the HE7 stack" is a
coverage-hole row the merged spec must add to HE7-BOX-2.**

### OPEN-CALL 6 — HE7-BOX-1's inherited-supplier minimum is never refreshed

`.67` states the SERIES' durable clause (§7.1): "Every consequence inherits the minimum
over its suppliers {GENHN 0/2 post-r1 erratum (battery GREEN), HE6 0/2 post-r1 (battery
GREEN), HE6R1 0/2 (battery GREEN), HE3 1/2 at μ ≤ 3, GENIND 0/2, W-12 0/2, classical}."
**Four dated arc entries later, HE7 itself is ACCEPTED 2/2 and the ANNEX R stack is
ACCEPTED 2/2 — and the supplier list is never restated.** From this note's own text HE6R1
is known to have reached at least PE3 (`.137` cites `HE6R1_passPE3_report.md`, and its
text records "HE6R1 ACCEPTED 2/2"), so at least one entry in the minimum is stale. **The
compiler will not update a frozen grade table from outside evidence.** Decision needed:
whether the merged spec carries `.67`'s minimum as-of-r1 (with a staleness flag) or
resolves it against the suppliers' own EFF specs at Phase 0c.

### OPEN-CALL 7 — the 780/780 f₁ = 2 family is unpinned and contradicts the coverage box

`.101` reports PE3's "two fresh legs (780/780 f₁ = 2 unramified family; 144/144
mixed-residual probe)". The second is pinned (`he7_pe3_probe12.py`, committed at
`b574f25`, artifacts on disk). **The first has no runner filename, no commit pin, and no
artifact anywhere in the note.** Meanwhile HE7-BOX-2's `[r1]` list (`.71`) still says
"what stays unexercised anywhere is … f₁ ≥ 2 stage genres". **Either the box is stale or
the leg is not an HE7-frame σ family.** Decision needed: locate the leg (it should exist
in `HE7_passPE3_report.md`) and either pin it or mark it UNPINNED; correspondingly,
whether HE7-BOX-2's `f₁ ≥ 2` item survives.

### OPEN-CALL 8 — ANNEX F-1's "what does not move" list names THEOREM HE7.D, which later
did move

`.104` lists "THEOREM HE7.C/HE7.D and the μ₂ ≥ 4 level-3 gate … " among what does not
move. **Read literally this is true** — ANNEX F-1 does not move HE7.D — but three
sections later Codex F1 finds HE7.D **unproved as displayed** at level ≥ 3 (`.105`), and
ANNEX R re-proves it at annex grade (`.114`). A chapter cut reading `.104` in isolation
would conclude HE7.D is settled. **Decision needed: whether the merged spec attaches a
forward-pointer from `.104`'s HE7.D item to `.114`.** No silent edit was made; the
tension is recorded at `.104`'s own CONDITIONALITY.

### OPEN-CALL 9 — three coverage ledgers, one region, jointly inconsistent about level 3
**[related to OPEN-CALL 11 below — a relation, not a dedup: the two shards say so
explicitly and keep them separate]**

Machine coverage is stated three times with three different scopes and freeze dates:
`.70` (base), `.71` (`[r1]`), and ANNEX R R1.3's disclosures (`.117`), which discharge the
level-3 item and simultaneously add a NEW hole (`g₂ = 1` throughout, so R1-b's
within-class deep twist is structurally invisible — OPEN-CALL 11). **The three lists are
individually frozen and jointly inconsistent about level 3.** Decision needed: whether
the merge emits a single reconciled coverage ledger (with each row's provenance) or
carries the three frozen lists side by side. The compiler declines to synthesise one,
because doing so would create a coverage claim no line of the note makes.

### OPEN-CALL 10 — the offered HE6R1-side erratum is recorded, not executed

`.120`: "*(Optional HE6R1-side erratum, recorded here, executed there or not at Asvin's
discretion: LEMMA HE6R1-3's hypothesis can be widened from "Ψ | f_S" to "gcd(f_S, Ψ) ≠
1" with its proof byte-near-verbatim, which is exactly R2-a.)*" **No landed append on
`HE6R1_RECON_2026-08-08.md` corresponding to this is visible from HE7's record.** The
mathematical content exists here as R2-a (`.119`), so nothing is unproved; what is open
is whether HE6R1's own display should be widened, and by whom. **Decision needed: Asvin
/ orchestrator — an action item, not a spec question.**

### OPEN-CALL 11 — R1-b's within-class deep twist is exercised nowhere **[related to
OPEN-CALL 9]**

`.117` disclosure (ii): "**g₂ = 1 throughout** — the within-class deep twist ϑ_t (t ≥ 1)
is structurally invisible at this family … the leg covers the τ-cocycle substance of F1,
**not every letter of R1-b**." The level-3 machine leg exercises the *cocycle* (18/79
flips) but not the *within-class* twist units R1-b's residue display introduces. **This
is a new coverage hole created by the repair itself, named in no box** — HE7-BOX-2's list
(`.70`, `.71`) predates ANNEX R and is frozen. **Decision needed: whether the merged
coverage ledger gains a row "R1-b's ϑ_t (t ≥ 1) at g_i ≥ 2: unexercised".**

### OPEN-CALL 12 — M-A's oracle correction is not reflected in HE7-BOX-3

`.129` (M-A) establishes that three deg-16 legs (ANNEX F-1's, R1.3's, annex-pass #1's
fresh leg) were scored against a shared re-implementation `pari_sigma16`, not against
`factorpadic`, and that actual `factorpadic` entered only at annex-pass #2's W1 leg
(`.127`). **HE7-BOX-3 (`.72`, the oracle-asymmetry box) is frozen and says only that PARI
exists on the ℤ_p side.** The oracle-*identity* limitation is a second, different
asymmetry. **Decision needed: whether the merged spec adds it to the oracle box, or
carries it only at `.129`.** No silent merge was made.

### OPEN-CALL 13 — does any claim depend on the pre-M-1 "102" figure?

`.128` (M-1) reduces the corrected-chain twist exercise from **102 slot instances to
47** (the other 55 were the naive tooth-reader's re-reads on a shared counter). M-1
states the load-bearing tooth (18/79) is unaffected, and the compiler's own audit of
`.117` finds no other number depending on 102. **But the sentence "the Λ₂Λ₁-monomial
twist arithmetic fired on 102 slot instances (a₁ ≠ 0)" is the note's ONLY quantification
of how much of R1-a(iii)'s letter-monomial machinery was exercised at level 3**, and
halving it halves that evidence. **Decision needed: whether the merged spec reports the
level-3 twist exercise as 47 (the corrected figure) in every downstream summary.** The
compiler has quoted both and marked M-1's reading terminal.

### Recorded source defects (flagged, not silently repaired; 19 raw → 18 distinct, 1
dedup marked)

1. **`.03`:** the GENHN paragraph is cited as "its 'twist (letters only)' paragraph";
   fixed-string `twist (letters only)` has count **0** because the target's heading has
   a period inside the bold. Referent unique and verified; carried descriptively.
2. **`.15`, `.18`, `.37`:** "HE3's stage-α recentering" / "HE3's stage-CS route" are
   HE7-local method names, not HE3 designations. Parent designations `HE3-3` (15) and
   `HE3-BOX-6` (12) verified; names carried descriptively.
3. **`.26`:** "Exactly one item is in the third class (§S5.3)" is falsified by the
   note's own `.64` under-count list and by `.68`'s `[r2]` addition. True of §S5.1–S5.7
   as originally scoped; false of the section's final content. Not edited.
4. **`.09`:** the note writes "Codex PE1 finding 2"; the target report numbers it `F2`
   and writes `Finding 2` (capital). Fixed-string `finding 2` count **0**. XREF emitted
   at `F2` (count 4).
5. **`.56`:** "W-12's r4 repair" — `r4` has count **59** in `W12_PROOF_2026-08-08.md`, a
   bare round tag matching every `[r4]` bracket, not an addressable statement. Carried
   descriptively; a precise designation would need W-12's own EFF spec.
6. **`.59`/`.60`/`.62`:** "the fifth row" denotes two different rows across three
   sentences (the α-refine row vs. the peel row); all three referents are unambiguous
   from their own content; no statement moves. Recorded because a grep for "fifth row"
   will collide.
7. **`.101` and `.85` [DEDUP — shard 1 defect 7 and shard 2 defect 4, self-identified:
   shard 1 flags its own copy "(shard-2 homed, quoted here)"]:** the `[r2]` disclosure
   (`.85`) reads "not the 41 stated in Q1's sentence below", but Q1's sentence (`.87`)
   in the frozen text already reads **42** with the recount folded in. The two sentences
   point at each other and neither now contains "41". Harmless; the number is right in
   both places. `.46` and `.59` quote the corrected figure, 42.
8. **`.132`:** the citation `HE6-1L [r2]` has fixed-string count **0** — the `[r2]`
   round suffix is HE7-local. Parent `LEMMA HE6-1L` verified (count 4).
9. **`.136`:** `LEMMA HE6R1-2(a)` has count **0** in the target, while its sibling
   `LEMMA HE6R1-2(c)` has count **1** — the clause-letter form is used inconsistently in
   `HE6R1_RECON` itself. Carried descriptively under the verified parent (8).
10. **Four frozen self-descriptions became false and are not edited (correctly, under
    the freeze):** ANNEX F-1's "has NOT been through a hostile pass" (`.93`), ANNEX R's
    identical clause (`.105`), `.115`'s "none of it has been through a hostile pass",
    and `.125`'s "the annex itself is unpassed". All four falsified by `.127`'s ACCEPTED
    2/2. **A systematic mode, not four accidents** (§6.3's `STALE-SELF-DESCRIPTION`
    format proposal).
11. **`.126` vs `.109`:** ANNEX R's "What does not move" opens "Every displayed
    statement and **proof** of the frozen body", yet R1.1 (`.109`) explicitly replaces
    two sentences of §S6's proof. Reconciled by reading "does not move" as "is not
    edited" (the annex pattern's own meaning); a chapter cut could misread it as "is not
    superseded". Flagged at `.126`.
12. **`.117`'s "102"** is an over-count of the corrected chain's exercise, recorded by
    the note itself at `.128` (=OPEN-CALL 13's own subject). Listed here because the
    corrected figure (47) is the one a downstream summary must carry.
13. **`.106`'s witness uses `n₀`** ("the recursion from any base n₀ — the level-0
    datum declares none") — an object DEFINITION HE7-2 does not define, which is
    precisely the defect the argument exploits (it is correct *because* it quantifies
    over all possible `n₀`). Noted so a reader does not take `n₀` for a defined symbol.
14. **`.75` vs `.116`:** HE7-BOX-5 (`.75`) says a peel at μ₂ ≥ 3 is "Not exercised". The
    PE3 probe (`.116`) runs 144 members at μ₂ = 3 — but as a *refine* probe, no peel
    reported there. The box still stands, but the two facts sit ~550 lines apart in the
    source. Flagged, not repaired.
15. **`.72` vs `.129`:** HE7-BOX-3's oracle-asymmetry claim (ℤ_p-only PARI) is narrower
    than M-A's oracle-*identity* finding (shared `pari_sigma16` vs. true `factorpadic`,
    OPEN-CALL 12) — the two are compatible but describe different asymmetries under one
    box name.
16. **Compiler arithmetic audits (shard 3), all checked correct:** `.106`'s four-step
    Codex witness, `.117`'s five cross-sums, `.124`'s subgroup-order witness, `.128`'s
    `47 + 55 = 102`, `.132`'s three arithmetic checks, `.137`'s pin-height witness — six
    independent recomputations, **zero arithmetic errors found**.
17. **Q1's row-label defect and Q1's σ-column convention** — the two findings flagged
    for the maintenance queue (§5.2 above); listed here for completeness of the source
    defect inventory, not double-flagged as a new item.
18. **HMENU3-ANNEX-A** — the near-miss XREF whose home ledger is shard 2's, cross-cited
    by shard 1 (§4 above); listed here for completeness, not double-flagged.

### Fidelity audit (merge-level, in addition to each shard's own three independent audits)

- All 137 canonical statement units carry mandatory CANONICAL STATEMENT, CONDITIONALITY,
  DERIVATION, RESOLUTION TRACE, and TEETH fields, verbatim-or-`[ASSEMBLED]` per template
  v2. No inverse, sign, quantifier, index, level, inequality direction, or implication
  direction was altered anywhere in the renumbering pass.
- Every source table is marked `[TABLE]`; the note's three ASCII tables are each emitted
  twice (verbatim display + Markdown transcription), per shard 2's rule extension; no
  source table was prosified at merge time.
- All 78 unique external XREF designations have fixed-string counts ≥ 1; a 12-designation
  sample was re-grepped at merge time against the working tree and matched exactly (§4);
  a 6-quote sample was re-checked verbatim against the source note by line number and
  matched byte-exact (§4). Fifteen cited commit hashes were independently confirmed real
  commits via `git cat-file -t`.
- **The ID-renumbering rewrite was performed mechanically** (a context-tracking
  left-to-right script, not hand-transcription) precisely because HE7's ~1,400 internal
  cross-references at 137 units made hand-renumbering an unacceptable error surface;
  the script's disambiguation rule (§1's SHARD-MAP note) was verified against every
  sampled cross-shard citation chain in §7.3 and found to resolve exactly as the source
  shards' own prose intended. An exhaustive regex sweep confirms **zero leftover
  `sKof3` substrings within the merged statement inventory (§3)** and **zero
  out-of-range IDs anywhere in the file** (every renumbered ID lies in 1–137).
- The SERIES (§7.1) is assembled from all seven of its links with no duplication and no
  gap, cross-checked against both shard 2's and shard 3's independent descriptions of its
  span. Both supersession CHAINs (§7.2) have their TERMINAL member verified unique by an
  exhaustive scan of every supersession-target citation in the merged inventory.
- Absorption status (§1's predicate A), the append/consumption protocol (§1's predicate
  B), and the inbound-corrections predicate unique to this note (§1's predicate C) are
  kept distinct everywhere below, matching all three source shards' own discipline — and
  matching the discipline template v2 asks for two of the three, this merge supplying the
  third by construction rather than by template guidance.
- **Two dedup pairs among the fifteen raw OPEN-CALLs were folded, both self-flagged by
  the source shards themselves** (§8); no OPEN-CALL was discharged, narrowed, or silently
  resolved by the act of merging. Two Q1 table defects are flagged for the maintenance
  queue (§5.2) without editing `spec/HYPOTHESIS_LEDGER.md`, which is out of this
  deliverable's scope.
- **Honest limitation of this merge, stated once rather than three times:** the
  forty-plus individual BOUNDARY SELF-AUDIT arguments (which unit-boundary candidate was
  chosen and why, per shard 1 §6, shard 2 §6, shard 3 §6) are not reproduced in this
  merged file — only their format-level conclusions (the SERIES and CHAIN constructs,
  the SUPERSESSION KIND vocabulary, the six other v2-gap proposals catalogued across the
  three shards' own §6.3 sections) survive here. A reader who needs the per-boundary
  reasoning for a specific unit should consult that unit's home shard file directly; the
  shard files are retained for exactly this purpose (§1).

---

EFF-HE7 MERGED: 137 statements / 78 xrefs verified / 13 open calls
