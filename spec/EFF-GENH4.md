# EFF-GENH4 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51) — mixed
provenance carried forward from both shards, each independently stamped identically.
CODEX CROSS-READ OWED (post-reset) — neither shard, and no fold performed by this merge run,
has been through an adversarial pass; that obligation is inherited whole.**

## 1. Merge header

**Source note:** `lean/notes/openmath/GENH4_PROOF_2026-08-08.md` (2173 lines).

**HEAD blob hash:** `cb713f3a8d8b66d675cae8e42ed5652fc5675739` — cited identically by both
source shards' headers, and independently confirmed by fresh `git hash-object` against the
working-tree file at merge time (2026-08-14):

```
$ git hash-object lean/notes/openmath/GENH4_PROOF_2026-08-08.md
cb713f3a8d8b66d675cae8e42ed5652fc5675739
```

**No divergence found — this was the merge run's STOP condition and it did not trigger.**
Both shards additionally record the file's last-touching commit as `65681144`; `git cat-file -t
65681144` and `git cat-file -t cb713f3a8d8b66d675cae8e42ed5652fc5675739` were re-run fresh at
merge time and resolve to `commit` and `blob` respectively.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md` (v2 rules 1–10; v3 rules 11–28).

**Merged from:** `spec/EFF-GENH4-s1of2.md` (HOME source lines 1–1208, the accepted body; 68
statements, 27-designation XREF ledger claim [see arithmetic note in §3.1 below], 45 commit
pins, 3 open calls) and `spec/EFF-GENH4-s2of2.md` (HOME source lines 1209–2173, the whole
post-acceptance annex stack: ANNEX PE5, ANNEX R, ANNEX R2, the post-annex-pass-2 dated
corrections; 43 statements, 3-designation XREF ledger, 12 commit pins + 16 artifacts, 3 open
calls). **111 statements total before merge-time dedup** (no statement-level duplication:
each shard's HOME range is disjoint and the two together exactly partition the 2173-line
source with no gap and no overlap — verified at §7's range-edge audit below). This file
supersedes the two shards as the citable unit for all downstream consumption; any consumer
citing `EFF.GENH4.*` from this point on cites the contiguous IDs below, not the shard-local
`EFF.GENH4.sKof2.*` IDs. The two shard files are **not deleted** — they remain the
run-of-record trace of the sharded compilation, and in particular remain the place where
each unit's own §6 BOUNDARY SELF-AUDIT entry lives in full; this merged file's §6 carries
both shards' boundary-audit sections forward whole (they do not overlap in content, since
each addresses only its own shard's boundary choices) and §7 carries the format-level
cross-shard conclusions (the SERIES reconstruction, the CHAIN inventory, the edge list).

### SHARD-MAP (old shard-local ID → new contiguous ID)

Shard 1's offset is **0** (its own numbering, 01–68, is already contiguous from 1 and is
carried forward as literally the same digit string, zero-padding included, in every unit
header and every bare `` `.NN` `` reference inside shard 1's own copied text). Shard 2
carries a **+68** offset (01–43 → 69–111, printed without zero-padding since the results are
already two or three digits). **Every `EFF.GENH4.sKof2.NN` occurrence — full header form,
the explicit disambiguating self-tag `` `sKof2.NN` ``, and the bare `` `.NN` `` shorthand
used throughout each shard's own prose — has been mechanically rewritten** (Python script
operating on the shard files' own bytes via regex substitution, not hand-retyping, to
guarantee zero arithmetic slips and zero accidental corruption of the verbatim quotation
spans) under the following disambiguation rule, recovered from the shards' own citation
discipline and verified against every occurrence before the rewrite was accepted:

> **GENH4's two shards do not use the HE7-merge convention of full-form cross-shard `.NN`
> citations at all.** Instead, every cross-shard citation is written as the literal prose
> phrase **"shard 1 `` `.NN` ``"** (never "shard 2", since shard 2's own content never needs
> to name itself) — this phrase, once it appears, governs every subsequent bare `` `.NN` ``
> reference in the same field/line, exactly as the HE7 recency rule governed bare refs
> there. A shard-2 unit that needs to name **its own** numbering from inside a
> "shard 1 …"-qualified field (to avoid being misread as continuing the shard-1 list) uses
> the **explicit self-tag** `` `s2of2.NN` `` instead of a bare ref — e.g. shard 2's own `.12`
> (TARGETS field) reads "**TARGETS:** shard 1 `.28`, `.29`, `.31`, `.32`; supersedes
> `` `s2of2.07` ``." Nine such explicit self-tags occur in shard 2 (none in shard 1, which
> never needs to disambiguate against itself) and were rewritten by the SAME single-pass
> regex as the bare refs, so that neither pass could double-shift the other's output.

The rewrite was verified three ways: (1) every resolved ID lies in 1–111 inside the merged
§2 statement inventory (a Python range check over every `` `\.\d{2,3}` `` token found zero
out-of-range values there); (2) a **first pass of the naive script over-shifted three
genuinely foreign citations** — "GENIND shard 3 `` `.26` ``" and "GENIND's shard 2 `` `.58`
``" (×2), which cite **another note's own EFF-spec numbering**, not this note's shard-offset
scheme, and must never be touched. These were caught precisely because the first pass
produced a plausible-but-wrong value (`` `.94` `` for the GENIND-shard-3 case, coinciding
with a genuine GENH4 unit ID — the kind of silent corruption a range check alone cannot
catch) and an out-of-range value (`` `.126` `` for the two GENIND-shard-2 cases); the script
was corrected to recognize and protect any `` "<Capitalized-note-name>['s] shard N" ``
pattern before shifting, and both are now confirmed byte-identical to the source shards'
"GENIND shard 3 `` `.26` ``" / "GENIND's shard 2 `` `.58` ``" text. (3) the ten sampled
XREF re-greps and five sampled statement-quote re-verifications in §3.1/§3.5 below, plus a
targeted CHAIN/SERIES-terminal uniqueness check in §7, all passed clean. **Zero leftover
`sKof2` substrings anywhere in the merged §2 statement inventory** (an exhaustive sweep);
the handful that survive in this header and in §7 below are deliberate quotations of the
shards' own shard-local notation, illustrating the rewrite rule itself.

### Header unification and blob-hash check

Both shards' front matter carries the **identical** compiled-by/cross-read-owed stamp
(reproduced verbatim above) and the identical HEAD blob hash; this merge re-verified the
hash against the working tree rather than trusting the shards' mutual citation alone (see
§1's code block above).

### Governing effective-text record (unified from both shards' independent derivations,
which agree on every point)

GENH4 states no single "the effective text is …" sentence anywhere in its 2,173 lines; both
shards derive the same rule independently from the same converging facts:

**(i) The accepted body is ACCEPTED 2/2 and byte-frozen at r3.** ANNEX PE5's provenance
(shard 2, out of shard 1's HOME range):

> "GENH4 was **ACCEPTED 2/2** at PE5 (report `GENH4_passPE5_report.md`, commit 11dbd23):
> 0 CRITICAL, 0 GAP, 2 MINOR (+1 remark) — the second stage-one note through the
> hostile-arc bar, after HE7. The accepted text is byte-frozen at r3 (4b0d946 = HEAD, md5
> `09af7f78c34a779ea092738164f1795c`); per the report's grade line the owed repair is this
> dated annex (the HE7 ANNEX F-1 pattern: appended, dated, nothing above edited)."

**(ii) `[r1]`, `[r2]`, `[r3]` were applied IN PLACE and tagged, before the freeze** — every
`[rN]` bracket inside shard 1's lines 1–1208 is already-landed base text, not a pending
supersession (shard 1 §S13's arc line records each round's landing).

**(iii) Every post-acceptance repair is a dated annex naming its exact target.** ANNEX R's
head: "The accepted body + ANNEX PE5 above are BYTE-FROZEN — md5 `a584cb3e…` (89,530 bytes)
verified identical before and after this append … each repair is a dated annex
lemma/rider naming its exact target." ANNEX R2 repeats the pattern at md5
`863c21600fa48ae755d0d87b77b894d4`; the post-annex-pass-2 corrections repeat it a third time
at md5 `22b766d3…` (128,564 bytes).

**(iv) Each annex layer discloses its own grade as LOWER than the layer below it.** All four
layers (PE5, ANNEX R, ANNEX R2, post-pass-2) say some form of "has NOT been through a
hostile pass"; the annex stack's own clean count is **0/2 → 1/2** (annex pass #2, the
post-annex-pass-2 corrections).

**EFFECTIVE TEXT = the whole 2,173-line file exactly as written (r1–r3 already landed
in-text in the body), READ AS CORRECTED by every later dated rider/annex that names an
earlier sentence, with no earlier sentence ever deleted.** Eleven in-range (shard-1) body
sentences are riddered from the annex stack (shard 2), enumerated exactly in shard 1 §7 and
cross-checked against shard 2 §7's own "cross-shard riders ISSUED" inventory below (§7 of
this merge) — the two lists agree exactly.

### FREEZE PREDICATES (rule 21 — four independent freezes, unified)

1. **BODY TEXT-FREEZE (acceptance).** The accepted body (lines 1–1208) is byte-frozen at r3:
   "byte-frozen at r3 (4b0d946 = HEAD, md5 `09af7f78c34a779ea092738164f1795c`)" —
   `4b0d946` ✓ commit.
2. **BODY + PE5 FREEZE.** Lines 1–1477 (body + ANNEX PE5) at md5 `a584cb3e…`, 89,530 bytes,
   verified before and after ANNEX R.
3. **BODY + PE5 + R FREEZE.** md5 `863c21600fa48ae755d0d87b77b894d4`, 113,738 bytes,
   "identical to the HEAD blob at ca3754d" — `ca3754d` ✓ commit.
4. **BODY + PE5 + R + R2 FREEZE.** md5 `22b766d3…`, 128,564 bytes, verified before and after
   the post-annex-pass-2 corrections (the note's terminal state).
5. **INSTRUMENT-FREEZE (artifact seal).** The sealed runner `genh4_checks.py` and its
   committed artifacts, md5-pinned and re-verified at every round; run-2 artifacts
   `genh4_checks_output.txt` md5 `9e6ca9b3…`, `genh4_checks_results.json` md5 `cbcff562…`,
   runner md5 `ee8024b7…` — **the runner md5 is commit-2's REPAIRED text, one line from the
   seal** (§S13.1's diagnosed RED run, repaired in commit 2), so the instrument freeze is a
   freeze on a *post-repair* runner, and the note says so.

**Four text-freezes, four different byte counts, each independently verified — the same
tight freeze discipline the HE7 and GENIND merges found in this corpus**, now confirmed a
third time.

### Scope split (rules 7 and 17 — three predicates, cross-checked between shards)

**A. ABSORPTION / mathematical supply set.** Shard 1's one-line inventory (§S11):

> "**One line: THEOREMS GENH4.A/B/C + LEMMAS GENH4-1F/-2/-CAP/-3/-4/-6 rest on
> {GENIND-4/GENIND-1(ii) @ pin, W-12.A entry laws @ pin, W-11 system @ accepted pin,
> classical}; COROLLARY GENH4.D adds GENIND.B + W-12.D + P(2)/P(3) @ pins. No axiom, no weld
> face inside any count law; grade = composition 0/2.**"

**This is the note that DISCHARGES a box**: `[GENIND-H(4)]`, at both quartic genres, firing
P(4) and displaying eleven exact densities. Shard 2 adds to the supply set: the genre-F
SPLTAIL cap and its σ-inequality (ANNEX-LEMMA GENH4-7, then GENH4-7′ over the true counted
family), the per-genre norm-valuation and units normalizations, the closure of a dangling
token, the stage-ring carrier erratum, a definition of "law keys" with the pre2 six-key
partition, the cap-sharpness clause (c′) at key level. **Neither shard's supply set overlaps
the other's** — shard 1 proves the count laws, drainage and σ-decision; shard 2 repairs
display defects in the accepted body's presentation of that same mathematics and completes
one previously-underived leg (the F-SPLTAIL σ-inequality) the accepted body's own count laws
already priced correctly.

**B. APPEND / consumption PROTOCOL scope.** **NO-APPENDS on suppliers, with one FOLD
OBLIGATION offered (shard 1) and one ERRATUM queued (shard 2) — neither claimed landed.**
Shard 1's GENH4-BOX-7 offers a fold obligation to QSCOUT22 (discharged at the source per
GENIND's own record, `.50`'s CONDITIONALITY). Shard 2's ANNEX R queues a transport erratum
to GENHN (`.90`, likewise discharged at the source per GENIND's record). **Zero dated
consumption appends are claimed landed on any supplier by either shard.**

**C. INBOUND corrections RECEIVED.** Nine channels across the note's full length: PE1
(0C+0G+1m), PE2 (**1 CRITICAL** + 2 GAP + 2 MINOR), PE3 (0C+0G+1m+2 remarks), PE4 CLEAN,
PE5 CLEAN → **ACCEPTED 2/2** (all shard 1, pre-freeze); then, post-acceptance, the Codex
ratification (CHALLENGE, 5 findings: 3 CONFIRMED GAP, 1 CONFIRMED-regraded MINOR, 1
REFUTED-as-CRITICAL/CONFIRMED-as-MINOR), annex pass #1 (0C+1 GAP+4 MINOR+2 remarks, **one
GAP a machine refutation of two displayed annex arguments**), annex pass #2 (0C+0G+3 MINOR)
— all shard 2, post-freeze. **Supplier movements received:** W-12's σ-LABELING clause added
to (A1) at r4, post-pin and previously uncited here, with a fired-clause check performed at
this note's `.53` (unchanged by the merge — shard 1's own local number, offset 0).

### Resolution rules applied (merged; nothing dropped, only consolidated)

1. Shard 1's lines 1–1208 supply the pre-freeze HOME material; shard 2's lines 1209–2173
   supply the post-freeze annex stack, read in layer order (ANNEX PE5 → ANNEX R → ANNEX R2
   → post-annex-pass-2).
2. `[r1]`/`[r2]`/`[r3]` brackets inside shard 1's range are ALREADY-LANDED text, applied at
   their own sites in chronology; the later bracket governs the earlier.
3. Eleven in-range (shard-1) sentences are riddered from shard 2 by name (§7 lists them for
   both shards and cross-checks the counts agree).
4. **ANNEX R2 supersedes annex material only** — no in-range (shard-1) sentence is touched
   by it; both shards' own "what does not move" declarations agree on this.
5. A rider that says "Read as …" without editing its target is carried at the target's
   unit **in shard 1** as CONDITIONALITY, and is emitted **in shard 2** as its own unit (the
   rider is itself a statement) — the same rule both shards state independently.
6. Where a rider lands on an in-range unit, the corrected reading is carried in that unit's
   CONDITIONALITY (all `wording-rider`s and `provenance-rider`s on displays, never
   replacements of mathematics), with the governing text quoted.
7. Out-of-range statements are NOT emitted merely because they resolve in-range text.
8. External records (pass reports, `verification/openmath/*`, supplier notes, the Codex
   fold note) are **reading notes only**.

### Quotation and table discipline

CANONICAL STATEMENTs are verbatim or explicitly `[ASSEMBLED]`; truncation is marked `…`.
**This merge contains six ASCII fixed-width displays inside indented blocks** — shard 1's
§S2.3 slot strings (`.17`), §S6.1 leaf-law table (`.25`), §S9.4 eleven densities (`.42`), and
shard 2's A3 mass table (`.78`), R4's F units-normalization table (`.91`), R5's six-key
partition (`.92`) — each emitted **verbatim as the source display** and, where it is a
count/law table, **again as a `` [TABLE] `` transcription**, per rule 14. Compiler ledgers
are flagged `` [TABLE — compiler ledger] ``.

## 2. Statement inventory

### EFF.GENH4.01  [changes-record]

**CANONICAL STATEMENT:** FORM: display (title) + bold-headed paragraph (Unit/Status). [ASSEMBLED — the title headline, line 1, plus the Unit/grade sentence, lines 3–5, quoted verbatim]

> “# GENH4 — [GENIND-H(4)] DISCHARGED AT BOTH QUARTIC GENRES: the (2,2) composite-stage laws PROVED (Q22-L1 count law, Q22-L2 refine transfer, Q22-L3 drainage — with Q22-L3's sealed display corrected at h > 1), the σ-decision (H-e) instance proved by the resolvent method, OB-a/OB-b/OB-c/OB-d all closed, P-D settled as UNREACHABLE at n = 4 (proof, not absence-of-evidence) — and COROLLARY GENH4.D: P(4) FIRES, the ELEVEN exact quartic densities R_τ(q) displayed with the triple tie, conditional exactly on the displayed arc-grade stack”

> “**Unit:** GENH4, the [GENIND-H(4)] prover (charge: turn GENIND's one box
> into theorems at the two n = 4 composite genres; ledger 4682bcf).
> **Attempt grade 0/2** (composed; no hostile arc).”

**CONDITIONALITY:** **STALE-SELF-DESCRIPTION → superseded.** “Attempt grade 0/2 (composed; no hostile arc)” is superseded in chronological order by §S13's `[r1]`/`[r2]`/`[r3]` arc appends (in range, `.70`) and then, out of range, by ANNEX PE5's dated GENH4-BOX-1 append (lines 1450–1463, shard 2): “**PE4 (e15308d) and PE5 (11dbd23 …) HAVE NOW RUN: PE4 CLEAN (1/2); PE5 CLEAN … The 2-clean count completed 1/2 → 2/2: GENH4 IS ACCEPTED — the second stage-one note through the hostile-arc bar.**” **The acceptance is then ANNOTATED (not revoked) by the Codex ratification's CHALLENGE** (ANNEX R's BOX-1 append: “The ACCEPTED 2/2 grade stands ANNOTATED by the fold note pending Asvin's read”).

**SUPERSESSION KIND:** `counter re-reading` (0/2 → 2/2) followed by an `as-of scoping` annotation (the CHALLENGE).

**CHAIN:** composed 0/2 → PE1 NOT CLEAN → `[r1]` → PE2 **1 CRITICAL** → `[r2]` → PE3 NOT CLEAN → `[r3]` → PE4 CLEAN (1/2) → PE5 CLEAN (**2/2, ACCEPTED**) → Codex ratification **CHALLENGE** (accepted grade ANNOTATED) → annex pass #1 NOT CLEAN (annex stack 0/2) → annex pass #2 (0C+0G+3m; **annex stack 1/2**) — **TERMINAL: body ACCEPTED 2/2 and annotated; annex stack 1/2.**

**DERIVATION:** Not a mathematical unit; the status chronology.

**RESOLUTION TRACE:** statement lines 1, 3–5. correction sites: 798–849 (§S10-BOX-1's three `[rN]` refreshes, in range), 1167–1207 (§S13's arc appends, in range), 1450–1463 and 1850–1868 and 2105–2127 (the three dated BOX-1 appends, shard 2), 2142–2150 (the post-annex-pass-2 frame, shard 2).

**TEETH:** report-pinned. **PIN VERIFICATION:** `4682bcf` ✓ (the ledger commit), and the whole arc's commits verify at `.68`.

---

### EFF.GENH4.02  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 5–13.

> “**Instrument:** sealed
> two-commit battery `verification/openmath/genh4_checks.py` — every
> proved lemma machine-keyed on the QSCOUT22 roster by md5-pinned
> committed artifacts + fresh never-measured rows (q = 7 entries, deep
> h = 5, k = 2, depth-2 prehistory, an odd-q even-dμ genre-F stratum, a
> fresh full sweep) + a pointwise refine-transfer leg (the carry formula
> checked member by member) + PARI σ legs + the symbolic density engine
> (partition of unity, the β₄ tie, Σ_τ R_τ = 1) + ≥ 3 teeth. Verdict
> §S13, appended at commit 2 FROM the committed artifacts.”

**CONDITIONALITY:** **The two-commit protocol did not survive contact: §S13 has TWO verdicts (a RED run 1 and a GREEN run 2 after a one-line generator repair), so the note's own “commit 2” schedule became commits 2–3** (`.65`–`.67`). The instrument description is not edited; §S13's heading records the change (“commits 2–3”).

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 5–13. correction sites: 1098 (§S13's heading, in range).

**TEETH:** self-referential. **PIN VERIFICATION:** `verification/openmath/genh4_checks.py` ✓, `genh4_checks_output.txt` ✓, `genh4_checks_results.json` ✓ EXIST — **and so do `genh4_checks_output_run1.txt` and `genh4_checks_results_run1.json`** ✓, the RED run's artifacts, committed as the note promises (`.68`), plus `_smoke` variants ✓. **Five artifact pairs on disk for one battery — an unusually complete instrument record.**

---

### EFF.GENH4.03  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 15–33.

> “**What GENH4 is (one breath).** THEOREM GENIND.B (@ 4682bcf) reduced
> full uniformity to the per-genre composite-stage package [GENIND-H]:
> (CS-1) stage transport, (CS-2) stage bracket, (CS-3) σ-decision. At
> n = 4 the only composite genres are E (e-first, key x² − ẑπ^h, value
> index E = 2, K = F_q) and F (f-first, key = lift of ψ, E = 1,
> K = F_{q²}) — QSCOUT22 (@ dd67cda) measured both exactly and handed
> three candidate lemmas. THIS note proves them: the stage read IS the
> W-11 n = 2 system transported to the stage ring O[x]/(φ₂) — genre E on
> the parity-interleaved doubled ladder (OB-a: the ragged window ledger
> written; the coherent object is the e₁-fold cover, as the ladder
> density predicted), genre F on the integer ladder with the F_{q²}
> alphabet (OB-d: the census re-base proved) — with the graded read
> transcribed pointwise in print coordinates (OB-b: the refine carry
> computed exactly; the z̄-twist cancels against the key's constant
> term — W-9's cocycle made literal and then made elementary), and σ
> decided at every stage leaf by the resolvent method (OB-c: the (H-e)
> INSTANCE at these two stages proved outright, for every disc ≠ 0
> lift). Consequence: [GENIND-H(4)] is DISCHARGED; P(4) fires through
> GENIND.B; W-12.D yields the eleven exact quartic densities.”

**CONDITIONALITY:** **The orientation claim, and it is strong: a BOX IS DISCHARGED.** Its one frame defect is corrected from outside the range: “transported to the stage ring O[x]/(φ₂)” — ANNEX R's R3 establishes that `R = O[x]/(φ₂)` is a **non-maximal order**, not a DVR, and re-aims every valuation/residue/graded statement at `O_L` (`.14`). **The consumption audit there concludes nothing downstream moves** — the note never uses R's ring structure, only `v(A(θ))` and residues of evaluated elements.

**SUPERSESSION KIND:** (received) `provenance-rider` on the carrier — the object in which the reads happen is renamed, the reads are unchanged.

**DERIVATION:** Not a proof; discharged by §S2–§S9.

**RESOLUTION TRACE:** statement lines 15–33. proof lines 205–789 (§S2–§S9). correction sites: 1720–1772 (ANNEX R's R3, shard 2).

**TEETH:** Indirect — the whole battery.

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` — count **7**.
XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-9` — count **13**.
**PIN VERIFICATION:** `4682bcf` ✓, `dd67cda` ✓.

---

### EFF.GENH4.04  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S0's first three bullets — the positive imports and the charge). verbatim, lines 37–52.

> “## S0. RECONCILIATION (the box, the measurements, this note's charge)
>
> * **GENIND @ 4682bcf** (verdict 4984004): the induction scaffold;
>   LEMMA GENIND-4 (the E-genre stage fibration + budgets + ℤ/2 slot
>   grading + node C(4h+1, 2h+1)) PROVED; CANDIDATE GENIND-5 boxed at
>   OB-a (ragged dv-window coherence), OB-b (graded-read pointwise
>   transcription), OB-c ((H-e) σ-decision), OB-d (genre F).
> * **QSCOUT22 @ dd67cda** (seal 970197d): the exact empirical table —
>   23 rows, 7.6M quartics, 0 violations; P-A (J-D0 at order 2), P-B
>   (E = ladder density), P-C (alphabet squares) HOLD; P-D untested;
>   candidate lemmas Q22-L1/L2/L3 with the lift-stability caps as part
>   of the correct statement.
> * **This note** proves Q22-L1/L2/L3 at both genres (THEOREMS GENH4.A,
>   LEMMA GENH4-4/Q22-L2, THEOREM GENH4.B), the σ-decision (THEOREM
>   GENH4.C), and P-D's resolution (LEMMA GENH4-6: unreachable at
>   n = 4); then COROLLARY GENH4.D (P(4) + densities).”

**CONDITIONALITY:** The GENIND pin `4682bcf` is a **pre-r1** state of GENIND; GENIND has since run r1–r6 and been ACCEPTED 2/2, then challenged and repaired through two 2026-08-12 corrections. **This note's §S10-BOX-1 tracks the drift explicitly at r1/r2/r3** (`.44`) but the S0 pin itself is never re-pinned. Recorded as an as-of pin; the consumed clauses (GENIND-4, GENIND-1(ii), GENIND.B, the criterion + grammar) are all stable across GENIND's arc per that note's own survival screens.

**DERIVATION:** Not a mathematical unit; a supplier inventory.

**RESOLUTION TRACE:** statement lines 37–52. correction sites: 798–849 (§S10-BOX-1's three refreshes, in range).

**TEETH:** GH-PIN [NONE] — 6 md5 pins (`.59`), scored 0/6.

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:LEMMA GENIND-4` — count **4**; `GENIND-5` — count **9**; `CANDIDATE THEOREM GENIND-5` — count **1**.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-L1` — count **3**; `Q22-L2` — count **3**; `Q22-L3` — count **3**.
**PIN VERIFICATION:** `4682bcf` ✓, `4984004` ✓, `dd67cda` ✓, `970197d` ✓.

---

### EFF.GENH4.05  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display (§S0's weld-corpus division — the note's central honesty fence). verbatim, lines 53–63.

> “* **Division from the weld corpus (honesty display).** W-9's twisted
>   algebra, JC-LOAD/W-8's no-cancellation, and J-D0's letter-blindness
>   are the MECHANISM this note instantiates — but every count-load-
>   bearing input is RE-PROVED elementarily at this stage (parity
>   no-cancellation, F_q-independence of {1, ȳ}, the explicit twist
>   cancellation), so no weld face sits inside any count law below.
>   DULEMMA (@ f819f26, ∂u ≡ 1 on perimeter e_m ≥ 2): the E-stage HAS
>   e_m = E = 2, so DULEMMA's perimeter INCLUDES it (applicability
>   checked as charged) — but it is NOT consumed (the multiplicativity
>   used is the exact valuation of the stage ring, proved in S2); genre
>   F has e_m = 1, off DULEMMA's proved perimeter — also not consumed.”

**CONDITIONALITY:** **The strongest NON-IMPORT in the corpus: “no weld face sits inside any count law below.”** Each of the three mechanisms is re-proved elementarily in range — parity no-cancellation at `.19`(E), F_q-independence of {1, ȳ} at `.19`(F), the twist cancellation at `.23`. **The DULEMMA bullet is a rare positive applicability check followed by an explicit non-consumption**, done on both sides of the perimeter. **One clause is riddered from outside:** “the exact valuation of the stage ring, proved in S2” — ANNEX R's R3 renames the carrier to `O_L` and notes DULEMMA's needed multiplicativity “needs only v's multiplicativity — true for v_L” (`.14`).

**DERIVATION:** Not a mathematical unit; a division-of-mechanism fence.

**RESOLUTION TRACE:** statement lines 53–63. correction sites: 1753–1765 (R3's consumption audit, shard 2).

**TEETH:** NONE — a fence. Its content is what no tooth can establish and what every count law depends on.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**; `W-8` — count **35**; `W-9` — count **13**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.
XREF: `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md:DULEMMA` — count **1**.
**PIN VERIFICATION:** `f819f26` ✓.

---

### EFF.GENH4.06  [convention]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph carrying a landed `[r2, PE2 Remark 1]` addition. verbatim, lines 65–82.

> “**Conventions.** As QSCOUT22 S1/S2 = W-12 S1: O a complete DVR,
> residue F_q, both characteristics; window N; quadruple-center
> recentered coordinates f = x⁴ + B₃x³ + B₂x² + B₁x + B₀, v(B_j) ≥ 1;
> counts per center. Conservative tails; canonical digit-lift letters in
> φ₂ (the W-2/LIFTCORNER seam NOT consumed; histories convention-keyed).
> Genre E entry: level-1 polygon one side slope h/2 (h odd), residual
> (y − z)², z ∈ F_q^×; key φ₂ = x² − ẑπ^h; per-center entry volume
> (q−1)q^{4N−5h−3} (W-12 S2.5, PROVED). Genre F entry: integer slope k,
> residual ψ(y)², ψ irreducible quadratic; key φ₂ = x² + ĉ₁π^k x +
> ĉ₀π^{2k}; entry volume ((q²−q)/2)·q^{4N−10k−4} (W-12.A instance,
> PROVED at the w12 seal). [r2, PE2 Remark 1: ADMISSIBILITY floors,
> previously unstated — genre E requires **N ≥ 2h+1** (v(B₀) = 2h exact
> needs that digit in window), genre F requires **N ≥ 4k+1** (v(B₀) =
> 4k exact); below these the displayed slot-count/entry-exponent forms
> fail (e.g. at (N,k) = (4,1) the true slot count is 3 but 4N−10k−4 =
> 2). Every roster row satisfies them, (Zp,7,5,k1) and (Zp,2,11,h5) at
> equality.] dv := 2v₁ (genre E, doubled units); genre F
> uses integer v₁-units. Prehistory: (1⁴)@k chains per LEMMA Q22-A.”

**CONDITIONALITY:** **The admissibility floors were UNSTATED at the seal and are landed at r2** — a hypothesis the displayed exponent forms need and did not carry. The `[r2]` bracket supplies both floors, the failure witness at `(N,k) = (4,1)`, and the roster check with the two equality rows named. **The genre-F floor `N ≥ 4k+1` becomes load-bearing again in shard 2** (ANNEX R2's R2.M1 scopes a realizability parenthetical to exactly it).

**SUPERSESSION KIND:** `inventory completion` (a missing hypothesis supplied, with its failure witness).

**ARITHMETIC AUDIT (compiler-computed):** at `(q, N, k) = (·, 4, 1)`, `4N − 10k − 4 = 16 − 10 − 4 = 2` ✓ against a true slot count of 3 ✓ — the displayed form does fail below the floor ✓, and `N ≥ 4k+1 = 5` excludes it ✓. Equality rows: `(Zp,7,5,k1)` has `N = 5 = 4·1+1` ✓; `(Zp,2,11,h5)` has `N = 11 = 2·5+1` ✓ — **both at equality exactly as stated.** Genre-E entry volume `(q−1)q^{4N−5h−3}` matches W-12 S2.5's QRT-G2 law ✓ (the same law GENIND shard 1 `.48` carries). Genre-F entry volume `((q²−q)/2)q^{4N−10k−4}` matches GENIND's CS4-F law `(q(q−1)/2)q^{4N−10k−4}` ✓ — **identical, since `(q²−q)/2 = q(q−1)/2`** ✓.

**DERIVATION:** Definitional + two cited entry laws.

**RESOLUTION TRACE:** statement lines 65–82. correction sites: `[r2]` in situ 75–81 (landed); 2013–2031 (ANNEX R2's R2.M1, which re-uses the F floor, shard 2).

**TEETH:** GH-JSONTIE + GH-FRESH exercise both entry laws on 23 committed + 7 fresh rows.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:S2.5` — count **9**; `THEOREM W-12.A` — count **8**; `S2.1` — count **23** (upper bound).
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-A` — count **3**.

---
### EFF.GENH4.07  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, THEOREM GENH4.A) carrying landed `[r2]` and `[r3]` corrections. verbatim, lines 86–116.

> “**THEOREM GENH4.A (the composite count law = Q22-L1, PROVED).** For
> every prime power q, both characteristics, every window N, both
> genres G ∈ {E, F}, every prehistory chain r = (k₁ < ⋯ < k_r), entry
> parameter (h resp. k) admissible over the chain (admissible: the S0
> entry floors N ≥ 2h+1 resp. N ≥ 4k+1, deepened along the chain
> [r2, PE2 Remark 1 — previously undefined]), stage history
> H₂ = (dμ₁ < ⋯ < dμ_t), and leaf ℓ with parameters: the per-center
> count of quartics with exactly this key equals the four-slot model:
>
>     count = (q−1)^r · L_G^t · C_ℓ(q^{f₁}) · q^{X},
>
> L_E = q−1, L_F = q²−1; C_ℓ = the residual census over F_{q^{f₁}}
> (f₁ = 1 for E, 2 for F): (Q−1)(Q−2)/2 for SPLITEQ, Q(Q−1)/2 for
> INERT, **q^{comp}−1 per RAM and per 2SIDED pin** [r2] — comp = the
> pinned slot's F_q-dimension (S2.3): identically 1 at genre E (every
> slot is one F_q-digit; the factor is q−1 = Q−1), and at genre F
> comp(m) = 2 at pin height m ≤ N−1 (the factor is q²−1 = Q−1) but
> comp(m) = 1 on the boundary band N ≤ m ≤ N+k−1 (a single in-window
> F_q-digit: census q−1, NOT Q−1) — and 1 for tails; X = #(free
> digit slots above the key's pins on the two stage strings), an
> explicit affine function of (N, h/k, leaf params) on each stratum
> (S6 displays the strings; the closed forms per leaf are S6's
> table). The counts are HISTORY-FLOOR-INDEPENDENT (the per-node laws
> do not depend on H₂ except through the (q^{f₁·e₁}−1)-letter
> factors), q- and characteristic-uniform, and lift-stable below the
> caps (dv < 2N for E; v₁ ≤ N with the v₁ = N residual band excluded,
> for F). Equivalently: W-12.A's cell law with (e₁, f₁)-re-based
> inputs — census field F_{q^{f₁}}, ladder density e₁ — away from
> the genre-F boundary band, whose pins are censused
> q^{comp}−1 = q−1 by the [r2] clause above, not by the re-based
> field [r3, PE3 remark].”

**CONDITIONALITY:** PROVED (§S6.1). **Two landed corrections, both display-level and both consequential for reading:** the `[r2]` comp-weighted census (the repaired **CRITICAL**, `.08`) and the `[r3]` scoping of the W-12.A mnemonic away from the boundary band. **The SPLTAIL leaf's genre-F cap is riddered from outside the range** by ANNEX PE5's MINOR 1 (`.25`, `.30`): the cap is `2w < N`, not `w < N`.

**SUPERSESSION KIND:** `[r2]` = `replacement` (a false census factor replaced, the false original quoted at `.08`); `[r3]` = `scope-pin` (the W-12.A equivalence scoped away from the band).

**ARITHMETIC AUDIT (compiler-computed):** the four-slot model `count = (q−1)^r · L_G^t · C_ℓ(q^{f₁}) · q^X` with `L_E = q−1 = Q−1` at `f₁ = 1` ✓ and `L_F = q²−1 = Q−1` at `f₁ = 2` ✓ — **so `L_G = Q−1` uniformly**, the “letter factor per refine step”. Censuses over `F_Q`: SPLITEQ (unordered distinct nonzero root pairs of a monic quadratic with both roots in `F_Q^×`… the note's `(Q−1)(Q−2)/2`) ✓ is the count of unordered pairs `{s₁ ≠ s₂}` from `Q−1` nonzero values ✓; INERT `Q(Q−1)/2` = the number of monic irreducible quadratics over `F_Q` ✓ (`(Q²−Q)/2`). **Both match the standard W-11 residual table over K** ✓. The comp-weighted RAM/2SIDED pin census `q^{comp}−1`: at genre E `comp ≡ 1` gives `q−1 = Q−1` ✓; at genre F, `comp = 2` below the band gives `q²−1 = Q−1` ✓ and `comp = 1` on the band gives `q−1 ≠ Q−1` ✓ — **the correction's whole content.**

**DERIVATION:** §S6.1 (`.25`), which assembles GENIND-4/GENH4-1F (fibration) + GENH4-2/-3 (per-event pin/census conditions) + GENH4-4 (refine re-entry).

**RESOLUTION TRACE:** statement lines 86–116. proof lines 476–513 (§S6.1). correction sites: `[r2]`/`[r3]` in situ (landed); 118–136 (the correction box, `.08`); 1227–1344 (ANNEX PE5's A1, shard 2).

**TEETH:** **GH-JSONTIE [SAME]** — “MY law evaluator (fresh code from S6's closed forms) reproduces EVERY composite key count … in the committed qscout22_results JSON, all 23 rows, BOTH directions”, scored **481/0** ✓ · **GH-FRESH [SAME]** 54/0 on seven never-measured rows · **GH-T-LAT** and **GH-T-CEN** (planted mutants against the ladder and the INERT census) both fired. Disposition: executable regression against a **foreign md5-pinned artifact table**, both directions — the strongest count-law guard in the corpus.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-L1` — count **3**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

---

### EFF.GENH4.08  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed bracketed record (the `[r2]` PE2 **CRITICAL 1** repair — the only CRITICAL in the GENH4 arc). verbatim, lines 118–136.

> “**[r2 2026-08-08 (PE2 CRITICAL 1) — the census clause corrected.** The
> sealed display read "Q−1 for RAM and per 2SIDED pin": FALSE at genre-F
> boundary-band pins (comp(m) = 1, N ≤ m ≤ N+k−1), where the in-window
> datum is a single F_q-digit and the census is q−1, not Q−1 = q²−1 —
> refuted by committed keys at q = 2, 3, 5, 7 in both characteristics
> (e.g. consF (Zp,7,5,k1) RAM(5) = 2,117,682 = 21·(q−1)·q⁵, this note's
> own preregistered P-3 value; the sealed display gives 16,941,456, and
> no exponent choice reconciles it). Display-level only: the runner
> always implemented the comp-weighted form (`ex0 = q ** comp(dv0) − 1`,
> likewise `q ** comp(dv1) − 1` at the w-pin), S6.3's UND display and
> P-3 always used the correct factor, and every committed number is
> correct — no machine number, no density conclusion moves. Verification
> of the corrected clause (PE2's independent ledger-closure recount):
> under the comp-weighted census, mass conservation — Σ(leaves) +
> Σ(refine children) = q^{#free slots} at every node — CLOSES in
> **216/216 genre-F cases** (q ∈ {2,3,4,5,7,8,9,11,13} × k ∈ {1,2,3} ×
> N ∈ [4k+1, 4k+8]) and **288/288 genre-E cases**; under the sealed
> display it FAILS in 40 of 50 scanned (q, N, k), overcounting the entry
> locus by up to a factor q.”

**CONDITIONALITY:** **A CRITICAL, repaired, display-level.** The distinction the record insists on — the *runner* always had it right, the *display* did not — is the same species GENIND's capped-window arc exhibits, and it is the reason no committed number moves.

**SUPERSESSION KIND:** `replacement` (a false census factor replaced; the false original quoted verbatim).

**ARITHMETIC AUDIT (compiler-computed, on every number the record displays):**
* **The refutation instance.** At `(q, N, k) = (7, 5, 1)`, genre F: the record says `RAM(5) = 2,117,682 = 21·(q−1)·q⁵`. Recomputed: `21·6·7⁵ = 21·6·16,807 = 2,117,682` ✓ **exact**. Here `21 = (q²−q)/2 = (49−7)/2` ✓ — the ψ-census, i.e. the number of monic irreducible quadratics over `F_7` ✓. The sealed display would give `21·(q²−1)·q⁵ = 21·48·16,807 = 16,941,456` ✓ **exact** — and `16,941,456 / 2,117,682 = 8 = q+1` ✓, so the two differ by the factor `(q²−1)/(q−1) = q+1` ✓, **which no exponent choice can absorb** ✓ (the record's claim, confirmed: `q+1` is not a power of q for `q ≥ 2`).
* **The band condition.** `RAM(5)` at `N = 5, k = 1`: the pin height is `m = 5 = N`, which lies in the band `N ≤ m ≤ N+k−1 = 5` ✓ — **a one-element band, and the RAM pin sits exactly in it** ✓, so `comp(5) = 1` and the census is `q−1 = 6` ✓, matching.
* **The ledger-closure recount.** Genre F: `9 values of q × 3 values of k × 8 values of N = 216` ✓ **exact**. Genre E: `288` — not reconstructible from the displayed parameters (no E grid is given); recorded as UNPINNED-BY-DISPLAY.
* **The failure rate under the sealed display.** “FAILS in 40 of 50 scanned (q, N, k)” — the scan's parameter set is not displayed; UNPINNED-BY-DISPLAY.

**DERIVATION:** Not a mathematical unit; a correction record with an independent recount.

**RESOLUTION TRACE:** statement lines 118–136. correction sites: none (the record is terminal for the census clause); the corrected clause is re-asserted at 502–506 (§S6.1) and scoped at 511–513 (`[r3]`).

**TEETH:** **`arithmetic recount`** (rule 27's AUDIT class) — PE2's independent ledger-closure recount over 216 + 288 cells is a *decorrelated arithmetic instrument*, not a battery row, and the sealed battery could not have caught the defect because the runner and the display never disagreed numerically. **This is the corpus's clearest instance of a CRITICAL found by recount rather than by run.**

---

### EFF.GENH4.09  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENH4-4 = Q22-L2). verbatim, lines 138–147.

> “**LEMMA GENH4-4 (the stage refine transfer = Q22-L2, PROVED).** At a
> stage refine event (depth dμ, letter s a root of the separable-free
> residual square): the refine locus maps by an explicit
> triangular-with-carry digit bijection ONTO the floored fresh node
> {dv(A₁) > dμ, dv(A₀) > 2dμ} of the recentered key — both genres,
> both characteristics, the carry landing at parities/heights disjoint
> from the killed pins, and the lift-stability caps preserved. The
> chain iterates: after H₂ the state in current-key coordinates is
> exactly the floored node, and letters multiply ((q^{f₁}−1)^t... —
> precisely L_G^t as in GENH4.A).”

**CONDITIONALITY:** PROVED (§S5). **Its “ONTO the floored fresh node” quantifier is the subject of ANNEX R2's GAP-1** (shard 2): the onto-statement quantifies over the FULL refine slice, and ANNEX R's R2 misapplied it to a FIXED member where only lift digits vary. **The lemma is not corrected — the misuse is withdrawn**, and R2.G1 says so: “GENH4-4's onto-the-fresh-node statement quantifies over the FULL refine slice — all in-window digits free. On a FIXED member only LIFT digits vary”.

**SUPERSESSION KIND:** none received. **A misuse of the lemma is withdrawn elsewhere; the lemma stands.** Recorded so a merge does not install a false edge.

**DERIVATION:** §S5 (`.23`), the explicit carry computation.

**RESOLUTION TRACE:** statement lines 138–147. proof lines 424–465 (§S5). correction sites: none in range; the misuse withdrawn at 1909–1956 (ANNEX R2's R2.G1, shard 2).

**TEETH:** **GH-REFINE [SAME]** — “the GENH4-4 one-step formulas POINTWISE: every refine event on consE (Zp,2,6,h1) + (Fqt,2,6,h1) and consF (Zp,2,7,k1): recompute the new development by my S5 formulas (incl. the carry and the twist-kill) and compare digit-by-digit with the pinned reader's divide_by_quad after recentering; assert the two pins die and the floored-node bijection (count both sides)”, scored **192,000/0** on 21,504 + 768 refine events ✓. Disposition: executable regression, **pointwise and digit-by-digit against a pinned foreign reader** — the strongest possible guard for a bijection claim.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-L2` — count **3**.

---

### EFF.GENH4.10  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, THEOREM GENH4.B) + its CORRECTION-disclosed paragraph. verbatim, lines 149–169.

> “**THEOREM GENH4.B (composite drainage = Q22-L3, PROVED — with the
> sealed display CORRECTED).** Per center, per entry, per history
> H₂ (any t ≥ 0, any prehistory r): the σ-undecided (conservative)
> count is ONE exact q-power, INDEPENDENT of H₂ and of the prehistory
> depths (only the letter factors move):
>
>     genre E:  UND(h; H₂) = (q−1)^{r+t} · q^{N+h−1}   per center;
>     aggregate over H₂ and letters: (q−1)^{r+1} · q^{2N−h−2}.
>     genre F:  UND(k; H₂) = (q²−1)^t (q−1)^r ·
>                [ q^{2⌊N/2⌋+2k−1}  +  1_{2|N}·(q−1)·q^{N+2k−1} ]
>     per (ψ, H₂) — the second term is the readable-value/unreadable-
>     residual band at dv0 = N (GENH4-CAP(F)), present at even N
>     only; at odd N the law is the single q-power q^{N+2k−2}
>     (S6.3 displays both terms slot-by-slot).
>
> **CORRECTION disclosed:** QSCOUT22 S6/S8 quoted the genre-E law as
> (q−1)q^{N+(h−1)/2}; that is the h = 1 instance only. At h = 3 the
> committed artifact (`qscout22_results.json` @ dd67cda, row consE Zp
> q=2 N=7 h=3) reads UND = 512 = (q−1)q^{N+h−1}, not 256. The law
> proved here matches the committed table on every row; the quoted
> display was the scout note's summary slip, not a measurement error.”

**CONDITIONALITY:** PROVED (§S6.3). **This is the theorem GENIND consumes as its (CS-EXACT) drain half at n = 4** (GENIND shard 1 `.59`, `.66`; shard 2 `.65` re-verifies it verbatim against this note's accepted body). **The CORRECTION disclosed is a `supplier-finding` against QSCOUT22**, discharged at the source per GENH4-BOX-7's fold obligation (`.50`) — offered, not landed.

**ARITHMETIC AUDIT (compiler-computed):**
* **The CORRECTION's witness.** At `(q, N, h) = (2, 7, 3)`: the proved law gives `(q−1)q^{N+h−1} = 1·2⁹ = 512` ✓; the scout's quoted law gives `(q−1)q^{N+(h−1)/2} = 1·2^{7+1} = 256` ✓ — **the committed artifact reads 512** ✓, so the scout's display is the h = 1 instance ✓ (at `h = 1`, `N+(h−1)/2 = N = N+h−1` ✓ — **the two laws coincide exactly at h = 1**, which is why the slip survived).
* **The aggregate.** Genre E, summing `q^{N+h−1}` over the ladder `{2h+1, …, N−1}` of size `N−1−2h` with `(q−1)` per step and one entry letter: `(q−1)^{r+1}·q^{N+h−1}·q^{N−1−2h} = (q−1)^{r+1}q^{2N−h−2}` ✓ **exact** (`N+h−1+N−1−2h = 2N−h−2` ✓).
* **Genre F, odd N.** `2⌊N/2⌋+2k−1 = (N−1)+2k−1 = N+2k−2` ✓ and the indicator vanishes ✓ — **the single q-power the display names** ✓.
* **Genre F, even N.** `2⌊N/2⌋ = N`, so the two terms are `q^{N+2k−1}` and `(q−1)q^{N+2k−1}`, summing to `q^{N+2k}`. **Compiler observation (identical to the one recorded at GENIND shard 2 `.65`): the “two-term” sum collapses to a single q-power at even N.** The display is faithful to the *form* GENH4-CAP(F) produces (a main term plus a band term), and GENIND's (CS-EXACT) requirement (“a FINITE SUM of q-powers”) is met either way. Recorded as an observation, not a correction — **and it is worth recording because the two-term language drove a granularity correction across three GENIND sites.**
* **The committed check values** cited at §S6.3: `(2,7,3) → 512` ✓ (above); `(2,8,1) F → 1024 = 512 + 512` — recomputed at `N = 8, k = 1, q = 2`: main `q^{N+2k−1} = 2⁹ = 512` ✓, band `(q−1)q^{N+2k−1} = 1·512 = 512` ✓, total `1024` ✓ **exact**.

**DERIVATION:** §S6.3 (`.27`).

**RESOLUTION TRACE:** statement lines 149–169. proof lines 528–545 (§S6.3). correction sites: none in range. Consumed out of range by GENIND at Step 4/S7.1.

**TEETH:** **GH-UND [SAME]** — “THEOREM GENH4.B's closed forms vs every UND key (committed JSON + all fresh rows), incl. the h = 3 correction value 512 and the even-N two-term F law; aggregates”, scored **92/0** ✓.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-L3` — count **3**.

---

### EFF.GENH4.11  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, THEOREM GENH4.C — the (H-e) instance). verbatim, lines 171–181.

> “**THEOREM GENH4.C (σ-decision at the (2,2) stages — the (H-e)
> INSTANCE, PROVED).** At every decided stage leaf of either genre
> (any history, any window), EVERY lift with disc ≠ 0 has the σ
> claimed by the leaf dictionary:
>   E: RAM ↦ {(4,1)}, 2SIDED/SPLITEQ/SPLTAIL ↦ {(2,1),(2,1)},
>      INERT ↦ {(2,2)};
>   F: RAM ↦ {(2,2)}, 2SIDED/SPLITEQ/SPLTAIL ↦ {(1,2),(1,2)},
>      INERT ↦ {(1,4)}.
> This is (A0) at the stage — the [W12-H](H-e) hypothesis PROVED at
> the two genres (m′, D′, E, K) ∈ {(2,2,2,F_q), (2,2,1,F_{q²})}. The
> GENERAL (H-e) (higher m′/D′) remains open (S10 box).”

**CONDITIONALITY:** **PROVED at two genres; the general (H-e) explicitly stays open** (GENH4-BOX-2, `.45`). **This dictionary is what W-12.D's σ-LABELING clause consumes at n = 4** (`.53`), and it is the reason GENIND's Step 5 fires there. **Its F-SPLTAIL leg is the one gap the post-acceptance arc found**: ANNEX PE5's A1 supplies the missing F-inequality (ANNEX-LEMMA GENH4-7(b), `.30`), and ANNEX R's R1 then re-proves that supply over the true counted family (GENH4-7′(b)) after finding GENH4-7's hypothesis “proves the σ-label only for the band-zero SLICE of the leaf — a strict subfamily, exactly HALF the leaf at the first live cell”. **The dictionary's LABELS never move**; what moved is the family the proof covers.

**SUPERSESSION KIND:** (received) `license` twice — an underived leg supplied (PE5), then its hypothesis widened to the counted family (ANNEX R). **Not a `replacement`: “the labels were always right — the annex ADDS the displayed F-inequality GENH4-7(b), it does not correct a label”** (ANNEX PE5's What-does-not-move).

**ARITHMETIC AUDIT (compiler-computed, on the dictionary's consistency):** every entry has `Σ e_i f_i = 4` ✓ — E: `(4,1)` → 4 ✓; `(2,1)+(2,1)` → 4 ✓; `(2,2)` → 4 ✓. F: `(2,2)` → 4 ✓; `(1,2)+(1,2)` → 4 ✓; `(1,4)` → 4 ✓. **Genre E always has even e** (every root has `v(θ) = h/2`, h odd ⟹ `2 | e`) ✓ — and every E entry has `e ∈ {2,4}` ✓. **Genre F always has even f** (`F_{q²} ⊆ k_L`) ✓ — and every F entry has `f ∈ {2,4}` ✓. **The dictionary is internally consistent with the two structural facts §S7 opens with.**

**DERIVATION:** §S7 (`.28`–`.33`).

**RESOLUTION TRACE:** statement lines 171–181. proof lines 547–603 (§S7). correction sites: 1227–1344 (PE5's A1: the F-SPLTAIL leg supplied, shard 2), 1500–1625 (ANNEX R's R1: the hypothesis widened, shard 2).

**TEETH:** **GH-SIGMA [IND]** — PARI factorpadic per decided composite member on five never-oracled fresh rows, scored **6,185/0** including 4,130 q = 7 F-RAM members ✓, plus 35,380 committed oracle checks consumed at pin; **GH-T-SIG** (F-RAM σ flipped `{(2,2)} → {(1,4)}`) fired. Disposition: executable regression on a **mechanism-free decorrelated oracle**.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.

---

### EFF.GENH4.12  [theorem]

**CANONICAL STATEMENT:** FORM: display (blockquote, COROLLARY GENH4.D — the discharge, P(4), and the densities). verbatim, lines 183–199.

> “**COROLLARY GENH4.D ([GENIND-H(4)] discharged; P(4); THE QUARTIC
> DENSITIES).** (i) The package {(CS-1), (CS-2), (CS-3)} holds at
> every composite-stage genre realizable at degree ≤ 4 (= E and F,
> incl. behind prehistory/α/β prefixes — genre-completeness by LEMMA
> Q22-A + GENIND S5.1/S5.3, consumed at pin): CS-1 = GENIND-4 +
> GENH4-1F + GENH4-2/-3/-4; CS-2 = the stage bracket, proved in S6.2
> ((q−1)q^{δ−1} per dv-advance δ for E — GENIND-5's (q−1)q^{2μ−1} in
> v₁-units — and (q²−1)(q²)^{μ−1} for F: one macroscopic rate
> q^{e₁f₁Δμ} = q^{deg φ₂·Δμ}); CS-3 = THEOREM GENH4.C. Hence
> [GENIND-H(4)] is DISCHARGED and THEOREM GENIND.B fires P(4): the
> degree-4 package (hMenu-4)+(hExhaust-4) holds, conditional exactly
> on the S11 arc-grade stack. (ii) THEOREM W-12.D then yields one
> R_τ(q) ∈ ℚ(q) per quartic splitting type at every prime power, both
> characteristics, wild primes included, Σ_τ R_τ = 1 — the ELEVEN
> densities displayed in S9 with the triple tie (symbolic Σ = 1 +
> engine assembly against the md5-pinned β₄ + finite-window partial
> sums bracketed by the proved drainage).”

**CONDITIONALITY:** **The capstone claim of the note, and its conditionality is exactly the S11 arc-grade stack** (`.51`–`.58`), whose minimum grade was 0/2 at composition. **Three later movements bear on it, none in range:**
1. **(CS-EXACT) is not named here.** GENIND's box grew a fourth clause at its own `[r1, PE1-G1]` — after this note's seal — and GENIND's Step 4 records the n = 4 discharge of (CS-EXACT) as riding *this note's* GENH4.A + GENH4.B (GENIND shard 1 `.59`). **So GENH4.D discharges a THREE-clause package and GENIND consumes a FOUR-clause one, with the fourth supplied de facto by the same theorems.** Recorded because a merge reading only this display will under-count the discharge.
2. **W-12.D's (A1) gained a σ-LABELING clause post-pin**, and `.53` performs the fired-clause check.
3. **The n ≥ 8 conditionality movement in GENIND** (shard 3 `.29`) does not reach n = 4.

**ARITHMETIC AUDIT (compiler-computed):** the CS-2 bracket claim. Genre E: `(q−1)q^{δ−1}` per dv-advance δ, and “GENIND-5's `(q−1)q^{2μ−1}` in v₁-units” — with `δ = 2μ` (two dv-points per v₁-unit at `e₁ = 2`) ✓, `(q−1)q^{δ−1} = (q−1)q^{2μ−1}` ✓ **exact agreement with GENIND's CANDIDATE GENIND-5** (GENIND shard 1 `.70`). Genre F: `(q²−1)(q²)^{μ−1}` ✓ — the same shape over `Q = q²`. Macroscopic rate: E gives `q^{2Δμ}` per v₁-advance (from `q^{δ} = q^{2Δμ}`) and F gives `(q²)^{Δμ} = q^{2Δμ}` ✓ — **both equal `q^{e₁f₁Δμ} = q^{deg φ₂ · Δμ} = q^{2Δμ}`** ✓, since `deg φ₂ = 2` at both genres ✓. **The “one macroscopic rate, two microscopic mechanisms” claim checks exactly.**
**Cross-note check against GENIND's (CS-2) normalization declaration** (GENIND shard 1 `.64`): GENIND declares its bracket MASS-normalized and warns that GENH4's is a ladder-telescoped LETTER-SUM differing by the ghost `|K|^{μ}`. At genre E, GENIND says the two “coincide numerically” because `δ = 2μ″` ✓ — **confirmed here**: GENH4's `(q−1)q^{δ−1}` at `δ = 2μ` IS `(q−1)q^{2μ−1}`, GENIND's mass form ✓. At genre F, GENIND's mass form is `(q²−1)(q²)^{2μ−1}` against GENH4's `(q²−1)(q²)^{μ−1}` — **differing by exactly `(q²)^μ`, the ghost** ✓, **precisely as GENIND's declaration predicts.** The two notes are consistent, and the discrepancy is the declared normalization difference, not an error.

**DERIVATION:** (i) = §S2–§S7 assembled at §S9.1 (`.36`); (ii) = §S9.2–§S9.4 (`.37`–`.42`).

**RESOLUTION TRACE:** statement lines 183–199. proof lines 654–789 (§S9). correction sites: none in range.

**TEETH:** **GH-DENS [SYM/IND]** — the triple tie, scored **115/0** ✓; **GH-BRACKET [SYM]** — the S6.2 identities, **157/0** ✓; **GH-T-DENS** (μ_E corrupted to the integer-ladder aggregation) fired.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-A` — count **3**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` — count **7**; `S5.1` — count **21**; `S5.3` — count **26**; `GENIND-5` — count **9**; `LEMMA GENIND-4` — count **4**.
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.D` — count **5**.

---

### EFF.GENH4.13  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (the obstruction scoreboard). verbatim, lines 201–203.

> “**Obstruction scoreboard: OB-a PROVED (S4), OB-b PROVED (S3 + S5's
> carry computation), OB-c PROVED (S7), OB-d PROVED (S2's GENH4-1F +
> the F-legs of S3–S6). P-D settled: UNREACHABLE at n = 4 (S8).**”

**CONDITIONALITY:** **All four of GENIND's boxed obstructions closed at n = 4, and the fifth question (P-D) settled by a theorem rather than by coverage.** Cross-note check: GENIND shard 1 `.72` boxes exactly (OB-a), (OB-b), (OB-c), (OB-d) ✓ — **four for four, same names, same content** (OB-a chain-level dv-window coherence; OB-b the graded read pointwise; OB-c (H-e); OB-d genre F). **GENIND's (OB-c) is its (CS-3)**, and this note proves it *at the two genres only* — GENIND's box stays open in general (`.45`).

**DERIVATION:** A scoreboard; each entry points at its section.

**RESOLUTION TRACE:** statement lines 201–203. correction sites: none.

**TEETH:** the four sections' own rows.

---
### EFF.GENH4.14  [definition]

**CANONICAL STATEMENT:** FORM: bulleted display (§S2.1 — the stage ring and its two genre invariant sets, plus the `gr` sentence). verbatim, lines 207–229.

> “### S2.1 The stage ring R = O[x]/(φ₂)
>
> Fix a genre and a current key φ = x² + p₁x + p₀ (entry: E: p₁ = 0,
> p₀ = −ẑπ^h; F: p₁ = ĉ₁π^k, p₀ = ĉ₀π^{2k}; refinements update p as in
> S5, preserving the invariants below). Let R := Ô[x]/(φ) = Ô[θ] over
> the O-lift (all digit statements then truncate to the window).
>
> * **Genre E invariants:** v(p₀) = h exact with res(p₀π^{−h}) = −z;
>   v(p₁) ≥ (h+1)/2. Then φ's own polygon is the single side
>   (0,h)–(2,0) (p₁ strictly above), so φ is irreducible, R is a
>   complete DVR, totally ramified quadratic: v(θ) = h/2, value group
>   ½ℤ (dv := 2v makes it ℤ — the doubled units), residue field
>   K = F_q, and res(θ²π^{−h}) = z. E = e(R/O) = 2 = the ladder
>   densification.
> * **Genre F invariants:** v(p₁) ≥ k with res-pair, v(p₀) = 2k,
>   residual ψ irreducible. θ = π^k·u with u a unit whose residue
>   ȳ := res(θπ^{−k}) is a root of ψ: R is an unramified-over-the-
>   ladder DVR: v(θ) = k ∈ ℤ, value group ℤ, residue field
>   K = F_{q²} = F_q(ȳ). f₁ = 2 = the alphabet squaring.
>
> R's associated graded IS COROLLARY W-9's twisted algebra K^c[ℤ/E]
> (one K-line per dv-height; E lines per old v-unit) — cited as frame;
> everything below is proved directly in R.”

**CONDITIONALITY:** **THREE sentences of this unit are literally FALSE and are riddered from outside the range** — ANNEX R's R3 (lines 1720–1772, shard 2), a CONFIRMED GAP at the Codex ratification:

> “**The defect.** S2.1's two carrier sentences are literally false:
> "φ is irreducible, **R is a complete DVR**, totally ramified
> quadratic" (genre E) and "R is an unramified-over-the-ladder
> **DVR** … residue field K = F_{q²}" (genre F), plus "**R's
> associated graded** IS COROLLARY W-9's twisted algebra".
> R = Ô[x]/(φ) = Ô[θ] is the NON-MAXIMAL order O[θ] at genre F for
> every k ≥ 1 and at genre E for every h ≥ 3.”

with two explicit witnesses (over ℤ₂ at this note's own A2 key, `R/2R ≅ F₂[ε]/(ε²)`, not F₄; and, at genre E h ≥ 3, `m_R = (π, θ)` non-principal), and the restated frame: `L := Frac(R)`, `O_L` its valuation ring (a genuine DVR), `v := v_L` restricted, residues in `O_L/m_L`, and the `gr` sentence re-aimed at `gr(O_L)`. **R3's consumption audit concludes nothing downstream moves**: “The note never uses R's ring-theoretic structure — it uses only v(A(θ)) and res(A(θ)/normalizer) of EVALUATED elements A(θ) ∈ O[θ] ⊆ O_L”. **`R = O_L` holds exactly at genre E, h = 1 — nowhere else in this note's range.**

**SUPERSESSION KIND:** `provenance-rider` — the carrier is renamed and every consumed datum is re-homed; **no valuation, residue, count or σ changes.** Filing it as a `replacement` would wrongly imply the invariants moved.

**TARGETS:** `.14` (three named sentences).

**ARITHMETIC AUDIT (compiler-computed, on the two witnesses):** (a) `φ = x² + 2x + 4` over `ℤ₂`: `R = ℤ₂[θ]` with `θ² = −2θ − 4`; mod 2, `θ² ≡ 0`, so `R/2R ≅ F₂[ε]/(ε²)` ✓ — **nilpotent, not a field, so R is not a DVR** ✓. And `disc(φ) = 4 − 16 = −12`, `v₂(−12) = 2 > 0` ✓, consistent with a non-maximal order ✓. (b) Genre E, `h ≥ 3`: `v(θ) = h/2`, `v(π) = 1`; a generator γ of `m_R` needs `v(γ) = min` over `m_R`, and `m_R ∋ π, θ` with `v` values `1` and `h/2 ≥ 3/2`, so `v(γ) ∈ {1, h/2}` up to the argument the note gives; at `v(γ) = 1`, `θ/γ` would need `v = h/2 − 1 ∉ ℤ` — **but `R = O[θ]` has value set `ℤ ∪ (h/2 + ℤ)`** ✓, and `h/2 − 1 ∈ h/2 + ℤ` ✓... **the note's argument as displayed requires `θ/γ = c + dθ` with `v(c) = h/2 − 1`**, i.e. the *coefficient* c must have that valuation, and `c ∈ O` forces `v(c) ∈ ℤ` ✓ — **the step is correct as written once the coefficient reading is taken**, which the note's own phrasing (“θ/γ = c + dθ would need v(c) = h/2 − 1 ∉ ℤ”) supplies ✓. At `h = 1`: `v(θ) = 1/2` and `θ` itself generates `m_R` ✓ — **the Eisenstein case, the one place `R = O_L`** ✓, exactly as R3 says.

**DERIVATION:** Definitional (the invariants) + a cited frame (the `gr` sentence).

**RESOLUTION TRACE:** statement lines 207–229. correction sites: 1720–1772 (ANNEX R's R3, shard 2); 2092–2099 (ANNEX R2's Remark 1, which riders R3's own audit sentence — “S7's Y-trichotomy runs in the quartic root field base(θ_F), not in L = Frac(R)” — shard 2).

**TEETH:** NONE — a definition. **The frame defect is a `decorrelated-model audit` finding: no run inspects a carrier's ring theory.**

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` — count **2**.

---

### EFF.GENH4.15  [lemma]

**CANONICAL STATEMENT:** FORM: prose lead-in + display (blockquote, LEMMA GENH4-1F — the genre-F fibration, OB-d's core). verbatim, lines 231–251.

> “### S2.2 The development fibration (E: GENIND-4 consumed; F: proved here)
>
> Monic division f = φ² + A₁φ + A₀ (A₁ = α₁x + α₀, A₀ = β₁x + β₀) is a
> bijection onto coordinate tuples. **LEMMA GENIND-4 (@ 4682bcf,
> PROVED)**: on the E(h, z) entry locus this is a triangular digit
> bijection with budgets v(α₁) ≥ (h+1)/2, v(α₀) ≥ h+1, v(β₁) ≥
> (3h+1)/2, v(β₀) ≥ 2h+1 — total 4N−5h−3 = the entry exponent, and the
> stage-initial node is {dv(A₀) ≥ 4h+1, dv(A₁) ≥ 2h+1}.
>
> > **LEMMA GENH4-1F (the genre-F fibration).** On the F(k, ψ) entry
> > locus, the development coordinates satisfy the triangular relations
> >
> >     B₃ = 2p₁ + α₁,  B₂ = p₁² + 2p₀ + α₁p₁ + α₀,
> >     B₁ = 2p₁p₀ + α₁p₀ + α₀p₁ + β₁,  B₀ = p₀² + α₀p₀ + β₀,
> >
> > and (B₃,B₂,B₁,B₀) ↦ (α₁,α₀,β₁,β₀) is a digit bijection from the
> > entry locus onto the budget space v(α₁) ≥ k+1, v(α₀) ≥ 2k+1,
> > v(β₁) ≥ 3k+1, v(β₀) ≥ 4k+1 — total (N−k−1)+(N−2k−1)+(N−3k−1)+
> > (N−4k−1) = 4N−10k−4, EXACTLY the entry exponent (no over/undercount)
> > — and the stage-initial node is {v₁(A₁) ≥ 2k+1, v₁(A₀) ≥ 4k+1} =
> > the W-11 node C(2S+1, S+1) at S = 2k in v₁-units.”

**CONDITIONALITY:** PROVED here (the genre-F half of OB-d). The E half is GENIND-4, consumed at pin. **Its budgets are load-bearing twice in shard 2**: R2.M1 scopes a realizability claim to `N ≥ 4k+1` **because** `v(β₀) ≥ 4k+1` is this lemma's budget, and R2.G1's `(2,8,2)` unrealizability argument cites `v(β₀) ≥ 4k+1 = 9` and `v(β₁) ≥ 3k+1 = 7` directly.

**DERIVATION:** verbatim, lines 253–264:

> “*Proof.* The relations are the expansion of φ² + A₁φ + A₀.
> Triangularity (α₁ from B₃; then α₀ from B₂; then β₁, β₀) gives
> bijectivity coordinate by coordinate. Budgets: the entry pins are
> B₃ = 2ĉ₁π^k + t₃, B₂ = (ĉ₁²+2ĉ₀)π^{2k} + t₂ (up to lift-carries of
> v ≥ 2k+1), B₁ = 2ĉ₁ĉ₀π^{3k} + t₁, B₀ = ĉ₀²π^{4k} + t₀ with
> v(t_j) ≥ (4−j)k+1; each pinned digit cancels against the p-terms
> (e.g. α₀ = B₂ − p₁² − 2p₀ − α₁p₁: the 2k-digit reads
> (c₁²+2c₀) − c₁² − 2c₀ = 0; α₁p₁ has v ≥ 2k+1), leaving exactly the
> stated floors; both characteristics (at p = 2 the pins 2ĉ₁π^k etc.
> degenerate, the budgets do not — the cancellations are universal
> identities). Node: v₁(A₁) = min(v(α₁)+k, v(α₀)) ≥ 2k+1;
> v₁(A₀) ≥ min(3k+1+k, 4k+1) = 4k+1. ∎”

Justification tags: the relations = `computation` (direct expansion); triangularity = `computation`; the budgets = `computation` (coordinatewise cancellation, universal identities); the node = `computation` + `by XREF` W-11's node C(·,·).

**ARITHMETIC AUDIT (compiler-computed; every step):** expansion of `(x²+p₁x+p₀)² + (α₁x+α₀)(x²+p₁x+p₀) + (β₁x+β₀)` — the `x³` coefficient is `2p₁ + α₁` ✓; the `x²` coefficient is `p₁² + 2p₀ + α₁p₁ + α₀` ✓; the `x¹` coefficient is `2p₁p₀ + α₁p₀ + α₀p₁ + β₁` ✓; the `x⁰` coefficient is `p₀² + α₀p₀ + β₀` ✓ — **all four displayed relations exact.** Free-digit total: `(N−k−1)+(N−2k−1)+(N−3k−1)+(N−4k−1) = 4N − 10k − 4` ✓ **exact**, matching the entry exponent of `.06` ✓ — **the no-over/undercount check.** Node: `v₁(A₁) = min(v(α₁)+k, v(α₀)) ≥ min(k+1+k, 2k+1) = 2k+1` ✓; `v₁(A₀) = min(v(β₁)+k, v(β₀)) ≥ min(3k+1+k, 4k+1) = 4k+1` ✓. W-11 node `C(2S+1, S+1)` at `S = 2k`: `2S+1 = 4k+1` ✓ and `S+1 = 2k+1` ✓ — **exact match.** Cross-note check: GENIND's LEMMA GENIND-4 gives the E node `C(4h+1, 2h+1)` at `S = 2h` (GENIND shard 1 `.68`) ✓ — **the same W-11 node shape at both genres, with `S = 2h` and `S = 2k` respectively.**

**RESOLUTION TRACE:** statement lines 231–251. proof lines 253–264. correction sites: none in range; consumed at 1935–1936 and 2019–2022 (shard 2).

**TEETH:** **GH-FEVEN [SAME]** builds its constructed locus *through* this map — “built THROUGH the GENH4-1F development map (validating it constructively)” ✓ — plus GH-JSONTIE's F rows. **The run-1 RED was a defect in exactly that construction** (`.67`), which is itself evidence the map is exercised hard.

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:LEMMA GENIND-4` — count **4**.
XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — count **3**.

---

### EFF.GENH4.16  [instance-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 266–272.

> “**Prehistory composition (consumed).** The (1⁴)@k recentering is the
> α(k) event of the (4,1) cluster: LEMMA GENIND-1(ii) (@ 4682bcf,
> PROVED at general m) gives, per letter, a bijection of the (1⁴)@k
> slice onto the floor set {v(B_j) ≥ (4−j)k+1} — the floored fresh law
> with one (q−1) factor per step; chains compose. (QSCOUT22's Q22-PRE
> family checked this pointwise; the battery's fresh depth-2 chain row
> extends it.)”

**CONDITIONALITY:** Consumed, not proved. **The cited clause is GENIND-1(ii), which GENIND shard 1 emits as its own unit `.18`** and whose statement is “the α(k)-recentering is a bijection of the z-slice onto the node D_k := {v(a_j) ≥ (m−j)k + 1 ∀j}” — **at `m = 4` this is exactly `{v(B_j) ≥ (4−j)k+1}`** ✓, the displayed floor set. **Cross-note consistency confirmed.**

**DERIVATION:** Cited.

**RESOLUTION TRACE:** statement lines 266–272. correction sites: none.

**TEETH:** **GH-PRE2 [SAME]** — “depth-2 prehistory constructed row (Zp,2,11, pre=(1,2), E at h = 5): the (q−1)² floored-fresh law at r = 2”, scored **5/0** ✓; the row's full six-key partition is displayed at ANNEX R's R5 (shard 2).

**NEAR-MISS (rule 15):** `GENIND-1(ii)` — fixed-string count **0** in `GENIND_PROOF_2026-08-08.md` (which writes the clause label `(ii)` inside the lemma display). Verified parent: `LEMMA GENIND-1` count **2**, `GENIND-1` count **15**. Carried descriptively; the clause is GENIND shard 1's unit `.18`.
XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-PRE` — count **3**.

---

### EFF.GENH4.17  [table]

**CANONICAL STATEMENT:** FORM: prose + **fixed-width ASCII display** (§S2.3's slot strings), emitted TWICE per rule 14 — verbatim as the source display, then as a `[TABLE]` transcription. verbatim, lines 274–292.

> “### S2.3 The slot strings and the caps
>
> Over the window, the four coordinates carry digit slots at dv-heights
> (genre E; budgets at entry, floors rise along the chain):
>
>     A₁:  odd  dv = 2v(α₁)+h,  v(α₁) ∈ [(h+1)/2, N−1]  → 2h+1 … 2N−2+h
>          even dv = 2v(α₀),    v(α₀) ∈ [h+1, N−1]      → 2h+2 … 2N−2
>     A₀:  odd  dv = 2v(β₁)+h,  v(β₁) ∈ [(3h+1)/2, N−1] → 4h+1 … 2N−2+h
>          even dv = 2v(β₀),    v(β₀) ∈ [2h+1, N−1]     → 4h+2 … 2N−2
>
> Both strings cover EVERY integer of their ranges below 2N−1 — the
> half-integer (E = 2) ladder realized in full (QSCOUT22's P-B, now
> structural) — and are RAGGED above: odd slots run h beyond the even
> end 2N−2; the band {2N ≤ dv ≤ 2N−2+h} holds exactly (h−1)/2 odd slots
> per string (empty at h = 1). Genre F: one slot per integer v₁-height
> m, of F_q-dimension comp(m) = 2 for m ≤ N−1 (the pair (digit_{m−k}(a₁-
> part), digit_m(a₀-part)) read as an F_{q²}-letter) and 1 for
> N ≤ m ≤ N+k−1 (the a₁-component only — the boundary band):
> A₁: m ∈ [2k+1, N+k−1]; A₀: m ∈ [4k+1, N+k−1].”

`[TABLE]` — the same slot strings, transcribed (rule 14's second emission):

| Genre | Coordinate | Parity / component | dv (or v₁) height | Source range | Height range |
|---|---|---|---|---|---|
| E | A₁ | odd (from α₁) | `2v(α₁)+h` | `v(α₁) ∈ [(h+1)/2, N−1]` | `2h+1 … 2N−2+h` |
| E | A₁ | even (from α₀) | `2v(α₀)` | `v(α₀) ∈ [h+1, N−1]` | `2h+2 … 2N−2` |
| E | A₀ | odd (from β₁) | `2v(β₁)+h` | `v(β₁) ∈ [(3h+1)/2, N−1]` | `4h+1 … 2N−2+h` |
| E | A₀ | even (from β₀) | `2v(β₀)` | `v(β₀) ∈ [2h+1, N−1]` | `4h+2 … 2N−2` |
| F | A₁ | one slot per integer m, `comp(m) = 2` (m ≤ N−1) / `1` (N ≤ m ≤ N+k−1) | `m` | — | `m ∈ [2k+1, N+k−1]` |
| F | A₀ | same | `m` | — | `m ∈ [4k+1, N+k−1]` |

**CONDITIONALITY:** **The slot strings are the note's coordinate system and are KEY-INDEPENDENT** (asserted here, used at `.23` and `.34`): “The slot strings are key-independent (S2.3) and floors only rise”. That independence is what makes GENH4-6's liveness scan cover every node of every history.

**ARITHMETIC AUDIT (compiler-computed):**
* **E, A₁ odd:** at `v(α₁) = (h+1)/2`, `dv = 2·(h+1)/2 + h = 2h+1` ✓; at `v(α₁) = N−1`, `dv = 2N−2+h` ✓.
* **E, A₁ even:** at `v(α₀) = h+1`, `dv = 2h+2` ✓; at `N−1`, `2N−2` ✓.
* **E, A₀ odd:** at `v(β₁) = (3h+1)/2`, `dv = 3h+1+h = 4h+1` ✓; at `N−1`, `2N−2+h` ✓.
* **E, A₀ even:** at `v(β₀) = 2h+1`, `dv = 4h+2` ✓; at `N−1`, `2N−2` ✓.
**All eight endpoints exact.** The node floors `{dv(A₀) ≥ 4h+1, dv(A₁) ≥ 2h+1}` of `.15` are precisely the two odd-string starts ✓.
* **Full-ladder coverage.** A₁'s odd heights are `{2h+1, 2h+3, …}` and its even heights `{2h+2, 2h+4, …}`, so together **every integer from 2h+1 to 2N−2** ✓ — the `E = 2` ladder realized in full ✓.
* **The ragged band.** Odd heights run to `2N−2+h`, even to `2N−2`; the band `{2N ≤ dv ≤ 2N−2+h}` contains the odd values `2N+1, 2N+3, …, 2N−2+h` **when h is odd** — count: `((2N−2+h) − (2N+1))/2 + 1 = (h−3)/2 + 1 = (h−1)/2` ✓ **exactly as displayed**, and **empty at h = 1** ✓ (`(1−1)/2 = 0`).
* **F strings.** `A₁: m ∈ [2k+1, N+k−1]` — the node floor `v₁(A₁) ≥ 2k+1` ✓ and the top from `v(α₁) ≤ N−1` giving `m = v(α₁)+k ≤ N+k−1` ✓. `A₀: m ∈ [4k+1, N+k−1]` ✓ likewise. Band width `N+k−1 − N + 1 = k` heights `{N, …, N+k−1}`, of which the `deep₀ = q^{k−1}` factor prices the `k−1` strictly above N ✓ (the height-N slot is pinned at the SPLTAIL/UND leaves — the fact ANNEX R's R1 turns on).

**DERIVATION:** Definitional, from the budgets of `.15`.

**RESOLUTION TRACE:** statement lines 274–292. correction sites: none in range; the F band's structure is re-analysed at 1500–1625 (ANNEX R's R1, shard 2).

**TEETH:** **GH-T-LAT** — “my law_E corrupted to the integer-only dv ladder must mismatch on every E row”, fired **19** times ✓ — the tooth that guards the half-integer ladder, i.e. this unit's central claim.

---

### EFF.GENH4.18  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENH4-CAP) carrying a **two-layer nested correction** (`[r2, PE2 GAP 1]` then `[r3, PE3 MINOR 1]`) that restates a trichotomy. verbatim, lines 294–333.

> “**LEMMA GENH4-CAP (lift-stability boundary).** (E) A window-computed
> dv-value is LIFT-STABLE iff < 2N: any lift agrees there; a computed
> value ≥ 2N (in the ragged band or beyond) can be undercut by an
> out-of-window even digit (a lift's β₀/α₀ digit at height N gives
> dv = 2N, even, undercutting every odd band value > 2N and tying
> none — parities distinct). (F) v₁-values are lift-stable iff ≤ N;
> the VALUE N is stable (attained by the in-window a₁-component at
> height N−k ≤ N−1) but its RESIDUAL PAIR needs the a₀-digit at
> height N — out of window: readable value, unreadable residual.
> **[r2, PE2 GAP 1; antecedents made disjoint at r3, PE3 MINOR 1: the
> sealed parenthetical "(the reader's dv0 = N → UND exit)" was FALSE
> as stated; the r2 restatement then transcribed the PE2 verifier's
> own clause "ODD N → DECIDED RAM(N)" with its one-side condition
> dropped, so {N odd} overlapped {N > 2w} with conflicting
> conclusions. Re-derived from LEMMA GENH4-3's hull partition — its
> (i) reads "(needs u ≤ 2w: one side; else (ii))", and S7's RAM
> bullet is "(u odd, u ≤ 2w)" — the reader's exits at dv0 = N are a
> trichotomy with PAIRWISE-DISJOINT antecedents (w := dv(A₁)):
> (a) N > 2w, EITHER parity → DECIDED 2SIDED(w, N−w) (two-side hull,
> shape-only); (b) N ≤ 2w, N ODD → DECIDED RAM(N) (the one-side
> shape and the stable value suffice, no residual consulted);
> (c) N ≤ 2w, N EVEN (N = 2dμ) → UND, the integer-slope read that
> would consume the out-of-window residual pair — as THEOREM GENH4.B
> displays ("present at even N only") and the runner implements (its
> dv0 = N → UND branch sits inside the even branch). Checked [r3]
> against every committed boundary key: (b): RAM(5) = 2,117,682 at
> (Zp,7,5,k1) — 86% of that row; N = 5 ≤ 2w holds throughout
> (w ≥ 2k+1 = 3 at that cell), so (a) is unrealizable there,
> matching the row's key set {RAM(5), UND}. (a) vs (b) at
> (Zp,2,7,k1), empty history: 2SIDED(3,4) = 384 (N = 7 odd > 2w = 6
> → (a)) against RAM(7) = 128 (w ≥ 4 → (b)); the r2 clause order
> predicts 512/0 — refuted by the committed artifact. (a) vs (c) at
> (Zp,2,8,k1): 2SIDED(3,5) = 1,536 (N = 8 EVEN > 2w = 6 → DECIDED by
> (a)) against UND = 1,024 (N ≤ 2w → (c); the two-term 512 + 512
> law).]**
> Hence the model's hidden-class
> pricing (band slots free, never pinned) is FORCED by lift
> well-posedness, and is part of the correct statement of Q22-L1/L2
> exactly as the scout disclosed. ∎ (proof in the display: the
> undercut construction + parity; both ring types)”

**CONDITIONALITY:** **The most-repaired display in the accepted body, and the repair history is itself the finding.** The chain: a FALSE sealed parenthetical → an r2 restatement that **transcribed the verifier's own phrasing** and thereby dropped a side condition, producing OVERLAPPING antecedents → an r3 re-derivation from the note's own LEMMA GENH4-3(i), with pairwise-disjoint antecedents and three committed counter-key checks. **The lesson is ledgered in the note itself** (§S13's r3 record): “the RAM clause dropped its one-side condition u ≤ 2w, transcribed from the PE2 verifier's own sentence (lesson ledgered: re-derive, never transcribe a verifier's phrasing).” **Two further riders land from shard 2:** ANNEX PE5's A1 restates the genre-F SPLTAIL cap as `2w < N` (`.25`, `.30`), and ANNEX R2's R2.M1 scopes GENH4-7′(a)'s realizability to `N ≥ 4k+1`.

**SUPERSESSION KIND:** `[r2]` = `replacement` (a false parenthetical replaced); `[r3]` = `counter re-reading` (the antecedents re-partitioned; **the conclusions were right, the case split was not**). **Two kinds, one bracket chain.**

**CHAIN:** sealed “(the reader's dv0 = N → UND exit)” → `[r2]` (transcribed, antecedents overlapping) → **`[r3]` trichotomy (a)/(b)/(c), pairwise disjoint, three committed checks — TERMINAL for the E/F cap statement**; then, for genre-F SPLTAIL specifically, ANNEX PE5's `2w < N` and ANNEX R's GENH4-7′.

**ARITHMETIC AUDIT (compiler-computed, on all three committed checks):**
* **(b) at `(Zp,7,5,k1)`:** `RAM(5) = 2,117,682` ✓ (re-derived at `.08`). Row total `21·7⁶ = 21·117,649 = 2,470,629` ✓ (the P-3 value at `.64`), so `RAM(5)` is `2,117,682/2,470,629 = 85.7%` ✓ — **“86% of that row”** ✓. `w ≥ 2k+1 = 3` at `k = 1` ✓ so `2w ≥ 6 > 5 = N` ✓ — **(a) unrealizable** ✓, key set `{RAM(5), UND}` ✓ and `2,117,682 + 352,947 = 2,470,629` ✓ **exact** (the UND value from `.64`).
* **(a) vs (b) at `(Zp,2,7,k1)`:** `2SIDED(3,4) = 384` with `w = 3`, `2w = 6 < 7 = N` ✓ → leg (a) ✓; `RAM(7) = 128` with `w ≥ 4` ⟹ `2w ≥ 8 > 7` ✓ → leg (b) ✓. **The r2 clause order (N odd → RAM first) would send both to RAM, predicting `384 + 128 = 512` RAM and 0 2SIDED** ✓ — **“the r2 clause order predicts 512/0 — refuted by the committed artifact”** ✓ **exactly.**
* **(a) vs (c) at `(Zp,2,8,k1)`:** `2SIDED(3,5) = 1,536` with `2w = 6 < 8 = N` ✓ → (a) ✓; `UND = 1,024 = 512 + 512` ✓ → (c) ✓, matching `.10`'s even-N two-term law ✓.
**All three checks reproduce exactly, and the refuted r2 ordering is confirmed refuted by arithmetic.**

**DERIVATION:** The E half is the displayed undercut construction + parity; the F half is the window/component analysis; the trichotomy is re-derived from GENH4-3(i) and S7's RAM bullet.

**RESOLUTION TRACE:** statement lines 294–333. proof lines — in the display + 376–415 (GENH4-3, `.21`) + 565–568 (S7's RAM bullet, `.28`). correction sites: `[r2]`/`[r3]` in situ (landed); 1227–1344 and 1500–1625 and 2013–2031 (shard 2).

**TEETH:** the three committed counter-key checks are an **`arithmetic recount`** against md5-pinned artifacts — and note the shape: **a display defect caught by comparing the display's predictions to committed numbers**, the same instrument that caught the CRITICAL at `.08`.

---
### EFF.GENH4.19  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENH4-2 — no-cancellation, pointwise; OB-b's value layer). verbatim, lines 337–354.

> “**LEMMA GENH4-2 (no-cancellation, pointwise).** Let A = a·x + b with
> a, b ∈ O (a coordinate pair of A₁ or A₀). Then:
> (E) v(A(θ)) = min(v(a) + h/2, v(b)) EXACTLY — the min is uniquely
> attained (2v(a)+h odd, 2v(b) even: distinct parities, no ties), so
> dv(A) := min(2v(a)+h, 2v(b)) equals 2·v(A(θ)) for every root θ of
> the key and every lift; the residual digit at dv(A) is the digit of
> the unique attaining coordinate. This is JC-LOAD's no-cancellation
> warrant holding BY PARITY — elementary, hence not consumed.
> (F) v(A(θ)) = min(v(a) + k, v(b)); at a tie m the residue is
> res(a)·ȳ + res(b) ≠ 0 because {1, ȳ} are F_q-independent (ψ
> irreducible) — the slot is ONE F_{q²}-digit, zero iff both
> components vanish. No cancellation by residue-field independence.
>
> Consequently the stage read's formal dv (the reader's min-formula)
> IS the valuation of R = O[θ] evaluated at the class of A — the
> graded read of W-8/JC-LOAD transcribed pointwise onto
> (α₁, α₀, β₁, β₀), which is OB-b's demanded transcription at the
> value layer (the residual layer is S5's carry computation).”

**CONDITIONALITY:** **Unconditional and elementary — this is where the weld-corpus fence of `.05` is cashed.** Its closing sentence's carrier (“the valuation of R = O[θ]”) is re-homed to `O_L` by ANNEX R's R3 (`.14`); the valuation statement is unchanged. **ANNEX R's R6 additionally riders its SCOPE**: S7's 2SIDED bullet cites GENH4-2 “at the key's own roots η”, outside its stated scope of development coordinates — R6 closes it: “its PROOF applies verbatim at any θ with the two facts S7 displays … the cite is to the proof, not the stated scope.”

**DERIVATION:** verbatim, lines 356–359:

> “*Proof.* Ultrametric equality when the two values differ; they differ
> by parity (E) since h is odd. F: if v(aθ+b) > m at a tie, then
> res(a)ȳ + res(b) = 0 with res(a) ≠ 0 forces ȳ ∈ F_q, contradicting
> deg ψ = 2. Residuals: divide by the attaining monomial and reduce. ∎”

Justification tags: both legs = `computation` (ultrametric equality + a parity resp. residue-field-independence argument). **No weld-corpus lemma is consumed** — the note's own claim, and the proof bears it out.

**ARITHMETIC AUDIT (compiler-computed):** (E) `2v(a)+h` is odd when h is odd ✓ and `2v(b)` is even ✓, so the two never tie ✓ and the ultrametric inequality is an equality ✓. (F) at a tie `v(a)+k = v(b) = m`, the height-m residue is `res(a)ȳ + res(b)`; `{1, ȳ}` is an `F_q`-basis of `F_{q²}` since `ψ` is irreducible of degree 2 ✓, so the residue vanishes iff both coefficients do ✓.

**RESOLUTION TRACE:** statement lines 337–354. proof lines 356–359. correction sites: 1720–1772 (R3, carrier), 1841–1848 (R6, scope of the cite) — both shard 2.

**TEETH:** guarded through every count law (GH-JSONTIE 481/0) and pointwise through GH-REFINE (192,000/0). Its parity claim is the target of no tooth directly; **GH-T-LAT** (the integer-only-ladder mutant) is its nearest guard.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-LOAD` — count **31**; `W-8` — count **35**.

---

### EFF.GENH4.20  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the twisted normalizer — W-9's cocycle DERIVED). verbatim, lines 361–372.

> “**The twisted normalizer (the letter twist, proved).** For a one-side
> stage polygon at dv-slope dμ (E), the normalizer is n₂ = π^{dμ/2}
> (dμ even) or n₂ = x·π^{(dμ−h)/2} (dμ odd; v(n₂(θ)) = dμ/2 both). From
> θ² = −p₁θ − p₀ and the S2.1 invariants: res(n₂(θ)²π^{−dμ}) = 1 (even)
> or z (odd). Hence the normalized residual equation of the stage state
> is T² + S₁T + S₀^eff with S₀^eff = S₀ (dμ even) or z̄^{−1}S₀ (dμ odd)
> — the z̄-twist of QSCOUT22 S4 DERIVED (it is res(θ²π^{−h}) = z
> surfacing: W-9's cocycle value); S₁ carries no twist (the odd-slot
> normalizer is the same x-monomial). Counts are twist-blind
> ((S₁, S₀) ↦ (S₁, z̄S₀) is a type-preserving bijection — J-D0's
> mechanism, literal at order 2); LETTERS are twisted. Genre F: the
> normalizer is π^{dμ}, no twist; residuals are the F_{q²} pair-digits.”

**CONDITIONALITY:** **A measured convention DERIVED**: the scout's `z̄`-twist is shown to be `res(θ²π^{−h}) = z`, i.e. W-9's cocycle value, and the count-blindness is J-D0's mechanism made literal. **Its genre-F clause (“the normalizer is π^{dμ}”) is re-displayed in true units by ANNEX R's R4** (`.32`).

**ARITHMETIC AUDIT (compiler-computed):** `n₂ = π^{dμ/2}` at even dμ gives `v(n₂(θ)) = dμ/2` ✓; `n₂ = x·π^{(dμ−h)/2}` at odd dμ gives `v(n₂(θ)) = v(θ) + (dμ−h)/2 = h/2 + (dμ−h)/2 = dμ/2` ✓ — **both equal dμ/2 exactly as displayed.** Residues: `res(n₂(θ)²π^{−dμ})` at even dμ is `res(π^{dμ}π^{−dμ}) = 1` ✓; at odd dμ it is `res(θ²π^{dμ−h}π^{−dμ}) = res(θ²π^{−h}) = z` ✓ — **the twist is exactly the E-invariant of `.14`.** The bijection `(S₁, S₀) ↦ (S₁, z̄S₀)` is type-preserving because scaling `S₀` by a nonzero constant preserves separability/irreducibility classes of `T² + S₁T + S₀`… **compiler note: it preserves the SPLITEQ/INERT/1sq trichotomy only as a count bijection over all letters, which is what “counts are twist-blind” claims** ✓ — the note is careful to say counts, not individual types.

**DERIVATION:** Displayed. Justification tags: `computation` (the normalizer valuations and residues from `θ² = −p₁θ − p₀` + the S2.1 invariants) + `by XREF LEMMA J-D0` for the count-blindness.

**RESOLUTION TRACE:** statement lines 361–372. correction sites: 1774–1801 (ANNEX R's R4, shard 2).

**TEETH:** the twist is exercised at every even-dμ residual event: **GH-JSONTIE** (all 23 rows) and **GH-FEVEN** (the odd-q even-dμ F stratum). **GH-T-ALPH** (F censuses over `F_q` instead of `F_{q²}`) fired **4** times.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:W-9` — count **13**.
XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:J-D0` — count **25**.

---

### EFF.GENH4.21  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENH4-3 — the stage trichotomy and the ragged-window ledger; OB-a's discharge) carrying landed `[r2]`/`[r3]` brackets. verbatim, lines 376–403.

> “**LEMMA GENH4-3.** At any stage state with lift-stable u := dv(A₀),
> w := dv(A₁) above the current floors: exactly one of
> (i) u odd → stage-RAM(u) (needs u ≤ 2w: one side; else (ii));
> (ii) u > 2w → stage-2SIDED(w, u−w);
> (iii) u = 2dμ ≤ 2w → integer stage slope: residual T² + S₁T +
> S₀^eff over K, censused '11' (SPLITEQ) / '2' (INERT) / '1sq'
> (REFINE at depth dμ, K^×-letter);
> plus the conservative exits (A₀ hidden: SPLTAIL if w < N-cap else
> UND; F's EVEN u = N ≤ 2w → UND [r2, PE2 GAP 1; r3, PE3 MINOR 1 —
> first-match order per GENH4-3(i)'s own "else (ii)": u = N > 2w
> (either parity) is decided 2SIDED(w, N−w); else odd u = N (≤ 2w)
> is decided RAM(N); both shape-only — GENH4-CAP(F) as corrected at
> r3]). Every digit CONSULTED by any
> event sits strictly inside its coordinate's window, at BOTH
> parities:
>   E: even consulted heights ≤ 2N−2 = the even window end; odd
>   consulted heights ≤ 2N−1 ≤ 2N−2+h = the odd window end (h ≥ 1) —
>   the H-2(i) inequality re-run on the ragged window: the consulted
>   ceiling (the cap 2N) lands below BOTH parities' ends, so no
>   event ever reads a ragged-band digit;
>   F: consulted positions ≤ N−1 in both components for every
>   readable event (u < N, or u = N read shape-only through the
>   in-window a₁-component at position N−k ≤ N−1 [r2]; only the EVEN
>   u = N residual read is out of window and exits UND by GENH4-CAP).
> The band digits are free on every leaf locus (priced as the hidden
> factor q^{deep}); window coherence holds along chains because every
> S5 update determines new digits at height d from old digits at
> heights ≤ d (carries move upward only, both ring types).”

**CONDITIONALITY:** **This is OB-a's discharge: the ragged-window ledger.** Its “SPLTAIL if w < N-cap else UND” clause is riddered by ANNEX PE5's MINOR 1 (`.25`, `.30`) — the “N-cap” is per-genre, `2w < 2N` at E (i.e. `w < N`) and **`2w < N`** at F. The `[r2]`/`[r3]` layers are `.18`'s trichotomy landed here too.

**DERIVATION:** verbatim, lines 405–415:

> “*Proof.* Partition: (i)/(ii)/(iii) are the three hull positions of
> {(0,u),(1,w),(2,0)} exactly as W-11 S2.1, in dv-units (denominator
> e₂ = 2 ⟺ u odd, by GENH4-2's parity). Consulted digits: RAM/2SIDED
> consult the exact-value digits at u (and w): u ≤ 2N−1 readable ⟹
> positions (u−h)/2 ≤ N−1 resp. u/2 ≤ N−1; SPLITEQ/INERT/REFINE consult
> S₁ at dμ ≤ N−1 and S₀ at 2dμ ≤ 2N−2: positions ≤ N−1. Ghost bound:
> consulted heights along a chain are bounded by the current readable
> dv0 < 2N (the stage analogue of "hull heights ≤ (m−j)(N−1)/m"; here
> m = 2 and the binding constraint is the cap itself), strictly below
> 2N−2+h and, for even parity, at positions ≤ N−1 exactly. The update
> claim is S5's triangularity. ∎”

Justification tags: the partition = `by XREF W-11 S2.1`'s hull trichotomy + `by XREF GENH4-2` (parity ⟹ the denominator read); the consulted-digit bounds = `computation`; the update = `by XREF` S5's triangularity (`.23`).

**ARITHMETIC AUDIT (compiler-computed):** RAM consults the odd height u at α/β-position `(u−h)/2`; `u ≤ 2N−1` gives `(u−h)/2 ≤ (2N−1−h)/2 ≤ N−1` for `h ≥ 1` ✓. 2SIDED consults the even height w at position `w/2 ≤ N−1` ✓ when `w ≤ 2N−2` ✓. SPLITEQ/INERT/REFINE consult `S₁` at dv `dμ` (position ≤ N−1 when `dμ ≤ 2N−2`) and `S₀` at dv `2dμ ≤ 2N−2` ✓. **The band `{2N ≤ dv ≤ 2N−2+h}` is therefore never consulted** ✓ — OB-a's content, and the `(h−1)/2` band slots of `.17` stay free ✓.

**RESOLUTION TRACE:** statement lines 376–403. proof lines 405–415. correction sites: `[r2]`/`[r3]` in situ (landed); 1244–1250 (PE5's rider 1, shard 2).

**TEETH:** GH-JSONTIE + GH-UND (the trichotomy's leaf partition is what both compare against the committed table).

---

### EFF.GENH4.22  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed one-sentence paragraph. verbatim, lines 417–420.

> “**The OB-a resolution in one line: the coherent object is the e₁-fold
> cover (the full integer dv-ladder), and the raggedness is confined to
> the never-consulted hidden band — measured first (QSCOUT22's ladder
> density and cap disclosures), now a ledger.**”

**CONDITIONALITY:** The closing summary of OB-a. **Cross-note check: GENIND's (OB-a) asks for “the H-2(i) argument re-run on the RAGGED window” (GENIND shard 1 `.72`) and expects the resolution “the consulted-height bound … lands below BOTH parities' ends” ✓ — exactly what `.21`'s proof delivers.** GENIND's expectation and GENH4's delivery match sentence for sentence.

**DERIVATION:** `.21`.

**RESOLUTION TRACE:** statement lines 417–420. correction sites: none.

**TEETH:** NONE — a summary.

---

### EFF.GENH4.23  [lemma]

**CANONICAL STATEMENT:** FORM: italic-headed proof section (§S5 — the proof of LEMMA GENH4-4, the refine transfer with carry; OB-b's residual layer). **This is the note's central computation** and is emitted as a unit because it discharges an obstruction that its statement (`.09`) only names. verbatim, lines 424–465.

> “*Proof of LEMMA GENH4-4.* Refine at depth dμ, letter s (a K^×-root of
> the '1sq' residual: (T − s)², i.e. S₁ = −2s, S₀^eff = s²). Set
> w := ŝ·n₂ and φ′ := φ − w; then
>
>     f = φ′² + (A₁ + 2w + C)·φ′ + (A₀ + λ − C·(p₁′x + p₀′)),
>
> where w² + A₁w = C·x² + λ (λ = the linear remainder; C = 0 when
> deg w = 0). Case dμ even (E; n₂ = π^{dμ/2}, deg w = 0): NO CARRY
> (C = 0), A₁′ = A₁ + 2w, A₀′ = A₀ + A₁w + w²: the dμ-digit of A₁′ is
> S₁ + 2s = 0; the 2dμ-digit of A₀′ is S₀ + S₁s + s² = R₂(s) = 0; all
> other contributions strictly deeper. Case dμ odd (E; n₂ = xπ^{(dμ−h)/2}):
> C = ŝ²π^{dμ−h} + α₁ŝπ^{(dμ−h)/2} ≠ 0 — THE CARRY, an even-parity
> (degree-0) contribution: 2v(C) ≥ min(2dμ−2h, 2v(α₁)+dμ−h) > dμ (using
> dμ ≥ 2h+1 and the budget v(α₁) ≥ (h+1)/2) — the carry lands at even
> heights STRICTLY ABOVE the odd-parity pin it could have threatened:
> JC-LOAD's no-cancellation, by parity, in print coordinates. The kills:
> A₁′'s dμ-digit (odd slot) = S₁ + 2s = 0 (the carry cannot reach it —
> disjoint parity); A₀′'s 2dμ-digit (even slot) collects THREE terms:
> S₀ (its own), +zs² from −C·p₀′ (the carry times the key's constant
> term: −ŝ²π^{dμ−h}·(−ẑπ^h)), and −2zs² from the α₁-component of −C·p₀′
> (nonzero only when the S₁-slot is attained): total S₀ + zs² − 2zs² =
> S₀ − zs² = z(s² − s²)·… = 0 since S₀ = z·s² ('1sq' with the twist) —
> **the z̄-twist cancels exactly against the carry × the key constant:
> W-9's cocycle multiplication computed in coordinates and equal to
> zero on the pin. In char 2 the same total reads S₀ + zs² = 2zs² = 0.**
> This is OB-b's residual-layer transcription: the graded identity
> res_{2dμ}(A₀′) = R₂(s) = 0, res_{dμ}(A₁′) = R₂′(s) = 0, verified
> digit-by-digit with the carry displayed. Genre F (letter S = s_ay +
> s_b ∈ F_{q²}^×; w = ŝ_aπ^{dμ−k}x + ŝ_bπ^{dμ}): identical computation
> with the wrap through x² = φ′ − p₁′x − p₀′ replacing the z-twist by
> the ψ-relation ȳ² = −c₁ȳ − c₀: the pair-digit kills are the
> components of R₂(S) = 0 and R₂′(S) = 0 in F_{q²} (the battery's
> GH-REFINE leg checks the one-step formulas POINTWISE, both genres).
> All correction terms sit at strictly greater dv and at in-window
> positions (upward carries), so the map is triangular on the digit
> space above the pins: injective, image inside the floored node
> {dv(A₁′) > dμ, dv(A₀′) > 2dμ}, and ONTO by cardinality: the refine
> slice fixes the two pinned digits and frees exactly the slots above
> dμ resp. 2dμ — the same count as the node (slot strings are
> key-independent, S2.3). Floors/caps preserved; letters: q^{f₁}−1
> choices of s per step... = L_G. Iterating over H₂ gives the chain
> statement. ∎”

**CONDITIONALITY:** **OB-b discharged at the residual layer, and the `z̄`-twist cancellation is the note's signature computation.** The ONTO-by-cardinality step is the one ANNEX R2's GAP-1 later shows was *misapplied* elsewhere (to a fixed member rather than the full slice, `.09`) — **the step itself is untouched.**

**ARITHMETIC AUDIT (compiler-computed, on the three-term cancellation and the carry bound):**
* **The carry's height.** `C = ŝ²π^{dμ−h} + α₁ŝπ^{(dμ−h)/2}`; in dv-units an even (degree-0) contribution at `2v(C)`, and `2v(C) ≥ min(2(dμ−h), 2v(α₁) + (dμ−h))` ✓ **as displayed** (the second term's `v` is `v(α₁) + (dμ−h)/2`, doubled ✓). Is it `> dμ`? First branch: `2(dμ−h) > dμ ⟺ dμ > 2h` ✓ (given `dμ ≥ 2h+1` ✓). Second: `2v(α₁) + dμ − h ≥ (h+1) + dμ − h = dμ + 1 > dμ` ✓ (given `v(α₁) ≥ (h+1)/2` ✓). **Both branches strict, as claimed.**
* **The three-term total at the `2dμ` even slot.** `S₀ + zs² − 2zs²= S₀ − zs²`, and `'1sq' with the twist` means `S₀^eff = z̄^{−1}S₀ = s²` (from `.20`, odd dμ), i.e. `S₀ = z s²` ✓ — so the total is `zs² − zs² = 0` ✓ **exact**. In char 2: `S₀ + zs² = zs² + zs² = 2zs² = 0` ✓ (the `−2zs²` term vanishes and the `+zs²` doubles) ✓.
* **The A₁′ kill.** `S₁ + 2s` with `S₁ = −2s` ✓ gives 0 ✓, in every characteristic (char 2: `S₁ = 0` and `2s = 0` ✓).
* **`R₂(s) = 0` and `R₂′(s) = 0`** are the statements that `s` is a double root of `T² + S₁T + S₀^eff` ✓ — consistent with `S₁ = −2s`, `S₀^eff = s²` ✓.
* **Genre F.** `w = ŝ_aπ^{dμ−k}x + ŝ_bπ^{dμ}` has `v₁(w(θ)) = min((dμ−k)+k, dμ) = dμ` ✓ — the right normalizer height ✓.

**DERIVATION:** The unit IS the derivation. Justification tags: the development identity = `computation`; the carry bound = `computation` (two branches, audited); the kills = `computation` (three-term cancellation, audited); onto = `computation` (cardinality, using `.17`'s key-independence); the F leg = `computation` (the ψ-relation replacing the z-twist).

**RESOLUTION TRACE:** statement lines 138–147 (`.09`). proof lines 424–465. correction sites: none in range; the misuse withdrawn at 1909–1956 (shard 2).

**TEETH:** **GH-REFINE 192,000/0**, pointwise and digit-by-digit against the pinned reader, on 21,504 + 768 refine events across three rows and both characteristics ✓ — **the carry formulas are the single most heavily exercised computation in the note.**

---

### EFF.GENH4.24  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 467–472.

> “**Invariant maintenance (used above, proved by the same display):**
> along any chain, v(p₀) = h exact with residue −z and v(p₁) ≥ (h+1)/2
> (E; refine adds ŝπ^{dμ/2} with dμ/2 ≥ h+1 to p₀, or ŝπ^{(dμ−h)/2}
> with (dμ−h)/2 ≥ (h+1)/2 to p₁); v(p₀) = 2k exact with residue-pair ψ
> and v(p₁) ≥ k similarly (F). Hence S2.1's ring invariants — and with
> them GENH4-2/-3 — hold at EVERY node of every history.”

**CONDITIONALITY:** **The induction that makes every per-node lemma apply at every node** — without it, `.19`/`.21` hold only at entry.

**ARITHMETIC AUDIT (compiler-computed):** E, even dμ: the refine adds `ŝπ^{dμ/2}` to `p₀`, and `dμ/2 ≥ h+1` requires `dμ ≥ 2h+2` ✓ (the even floor of `.17`) — so the added term is strictly deeper than `v(p₀) = h` ✓ and the invariant survives ✓. E, odd dμ: adds `ŝπ^{(dμ−h)/2}` to `p₁`, and `(dμ−h)/2 ≥ (h+1)/2` requires `dμ ≥ 2h+1` ✓ (the odd floor) ✓. **Both floors are exactly the string starts of `.17`** ✓ — the invariant maintenance and the slot geometry are the same arithmetic.

**DERIVATION:** Displayed (“proved by the same display”, i.e. `.23`'s).

**RESOLUTION TRACE:** statement lines 467–472. correction sites: none.

**TEETH:** GH-REFINE (which walks chains) + GH-JSONTIE at every history.

---
### EFF.GENH4.25  [table]

**CANONICAL STATEMENT:** FORM: prose + **fixed-width ASCII leaf-law table** (§S6.1, the proof of THEOREM GENH4.A and its per-leaf X-exponent table), emitted TWICE per rule 14. verbatim, lines 476–513.

> “By GENIND-4/GENH4-1F + prehistory composition (S2.2), the entry locus
> is the budget digit space with (q−1)^r·(entry census) letters. By
> GENH4-2/-3, each stage event is a pin/census condition on the slot
> strings; by GENH4-4, each refine step re-enters the floored node
> bijectively with L_G letters. Hence the count per full key = (letter
> factors) × (leaf census over K) × q^{#free slots}: free slots = all
> string positions neither structurally below a floor nor pinned by the
> leaf, INCLUDING the hidden band (GENH4-CAP): exactly the four-slot
> model's law, term for term. Floor-independence: a leaf's pins are
> "slots strictly between the floor and the leaf position vanish, leaf
> digits censused, higher slots free" — the count does not reference
> the floor (slots below it do not exist), so per-(H₂, leaf) laws
> depend on H₂ only through L_G^t. The X-exponents per leaf (strings of
> S2.3; E, per (center, entry letter), history-free form):
>
>     RAM(u), u odd:      (q−1)·q^{#A₀ slots > u  +  #A₁ slots s: 2s > u}
>     2SIDED(w, u−w):     (q−1)²·q^{#A₀ > u + #A₁ > w}
>     SPLITEQ(dμ):        ((q−1)(q−2)/2)·q^{#A₀ > 2dμ + #A₁ > dμ}
>     INERT(dμ):          (q(q−1)/2)·q^{#A₀ > 2dμ + #A₁ > dμ}
>     SPLTAIL(w), w < N:  (q−1)·q^{(h−1)/2 + #A₁ > w}
>     UND:                q^{(h−1)/2 + #A₁ ≥ N}
>
> (#·counts on the S2.3 strings, evaluated as affine functions of
> (N, h, param) on each parity stratum; genre F identically with
> comp-weighted exponents AND comp-weighted pin censuses —
> q^{comp(m)}−1 per RAM/2SIDED pin, i.e. q−1 at boundary-band pin
> heights m ≥ N [r2: the sealed parenthetical declared only the
> EXPONENTS comp-weighted; PE2 CRITICAL 1, see the S1 correction] —
> with the F_{q²} censuses at the even-dμ residual events.) Each is
> manifestly ONE
> q-polynomial, characteristic-blind (the censuses' loci differ across
> characteristics, their counts do not — W-11 S2.1's table over K),
> letter-blind (S3's twist bijection): Q22-L1 as displayed, = W-12.A's
> cell law with census field F_{q^{f₁}} and ladder density e₁ — away
> from the boundary band, where the pin census is q^{comp}−1 = q−1
> (the [r2] clause of S1) [r3, PE3 remark]. ∎”

`[TABLE]` — the six leaf laws (genre E, history-free), transcribed:

| Leaf | Letter/census factor | Free-slot exponent |
|---|---|---|
| `RAM(u)`, u odd | `q−1` | `#A₀ slots > u  +  #A₁ slots s: 2s > u` |
| `2SIDED(w, u−w)` | `(q−1)²` | `#A₀ > u + #A₁ > w` |
| `SPLITEQ(dμ)` | `(q−1)(q−2)/2` | `#A₀ > 2dμ + #A₁ > dμ` |
| `INERT(dμ)` | `q(q−1)/2` | `#A₀ > 2dμ + #A₁ > dμ` |
| `SPLTAIL(w)`, `w < N` | `q−1` | `(h−1)/2 + #A₁ > w` |
| `UND` | `1` | `(h−1)/2 + #A₁ ≥ N` |

**CONDITIONALITY:** **The SPLTAIL row's range `w < N` is genre-E-only; ANNEX PE5's MINOR 1 riders it** (rider 2, quoted at `.30`): “‘identically’ transfers the LAW SHAPE …; the w-RANGE transfers by the uniform rule of rider 1, i.e. genre F: **2w < N**”. The `[r2]` bracket is the CRITICAL repair landed here as well as at `.07`/`.08`; the `[r3]` remark scopes the W-12.A mnemonic.

**SUPERSESSION KIND:** `[r2]` = `replacement`; `[r3]` = `scope-pin`; PE5's rider = `wording-rider` on the SPLTAIL range.

**ARITHMETIC AUDIT (compiler-computed):** the `(h−1)/2` term in the SPLTAIL and UND exponents is exactly `.17`'s ragged-band slot count per string ✓ — the hidden band priced free, as GENH4-CAP forces ✓. SPLITEQ's `(q−1)(q−2)/2` and INERT's `q(q−1)/2` match `.07`'s censuses at `Q = q` ✓.

**DERIVATION:** The unit IS §S6.1's proof: `.15`+`.16` (entry) → `.19`/`.21` (per-event conditions) → `.09`/`.23` (refine re-entry) → the slot count.

**RESOLUTION TRACE:** statement lines 476–513. correction sites: `[r2]`/`[r3]` in situ; 1251–1257 (PE5's rider 2, shard 2).

**TEETH:** GH-JSONTIE 481/0 both directions; GH-FRESH 54/0; GH-T-LAT (19) and GH-T-CEN (14) fired.

---

### EFF.GENH4.26  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed proof paragraph (§S6.2 — the stage bracket, (CS-2) displayed and proved). verbatim, lines 517–526.

> “Aggregating S6.1 over histories at a fixed leaf: Σ_{H₂ ⊆ ladder ∩
> (node, leaf)} L_G^{|H₂|} = Π_{ladder points p below the leaf}
> (1 + L_G) = (q^{f₁})^{#ladder points below} — genre E: q^{δ} over the
> δ consecutive INTEGER dv-points available (density e₁ = 2 per
> v₁-unit); as a per-advance bracket this is exactly GENIND-5's
> b_stage(μ) = (q−1)q^{2μ−1} in v₁-units (the last step carries the
> (q−1), the interior points telescope: 1 + Σ(q−1)q^{j−1} = q^{δ});
> genre F: (q²−1)(q²)^{μ−1}. One macroscopic rate q^{e₁f₁·Δμ} =
> q^{deg φ₂·Δμ}, two microscopic mechanisms (density vs alphabet) —
> QSCOUT22's S8 paragraph, now a theorem. ∎”

**CONDITIONALITY:** **(CS-2) at both quartic genres, PROVED.** Its relation to GENIND's mass-normalized bracket is audited at `.12` (E coincides; F differs by the declared ghost `(q²)^μ`).

**ARITHMETIC AUDIT (compiler-computed):** `Σ_{H₂ ⊆ D} L^{|H₂|} = (1+L)^{|D|}` ✓ (subset sum). With `L_E = q−1`, `(1+L)^{δ} = q^{δ}` ✓; with `L_F = q²−1`, `(1+L)^{μ} = (q²)^{μ}` ✓. The telescope: `1 + Σ_{j=1}^{δ}(q−1)q^{j−1} = 1 + (q−1)(q^{δ}−1)/(q−1) = q^{δ}` ✓ **exact**. Macroscopic rate: E `q^{2Δμ}` = F `(q²)^{Δμ}` ✓, both `q^{e₁f₁Δμ}` with `e₁f₁ = 2` at both genres ✓.

**DERIVATION:** Displayed. Justification tags: `computation` (subset sum + geometric telescope).

**RESOLUTION TRACE:** statement lines 517–526. correction sites: none.

**TEETH:** **GH-BRACKET [SYM] 157/0** — “Σ_{H⊆D}L^{|H|} = q^{f₁|D|} integer identities (E and F ladders, ranges) + aggregated-vs-resolved key sums on the committed rows” ✓.

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND-5` — count **9**.

---

### EFF.GENH4.27  [theorem]

**CANONICAL STATEMENT:** FORM: italic-headed proof paragraph (§S6.3 — the proof of THEOREM GENH4.B). verbatim, lines 530–545.

> “Genre E, per (center, entry letter, H₂): UND = A₀ all-readable-zero ×
> A₁ free only at ≥ N: count = q^{deep₀}·q^{#A₁ slots ≥ N} with
> deep₀ = (h−1)/2 (the band) and #A₁ ≥ N = ⌊(N+h)/2⌋ + ⌊N/2⌋ − …
> = N + (h−1)/2 (both parities, h odd — the two floors' parity
> bookkeeping cancels): total q^{N+h−1}, floor-independent. Letters:
> (q−1)^{r+t}. Aggregate over H₂ (ladder {2h+1, …, N−1}, size N−1−2h)
> and the entry letter: (q−1)^{r+1}·q^{N+h−1}·q^{N−1−2h} =
> (q−1)^{r+1}q^{2N−h−2}. Genre F: per (ψ, H₂): deep₀ = q^{k−1} (the
> boundary band of A₀), main factor q^{Σ comp(s): s ∈ A₁, 2s ≥ N} =
> q^{2⌊N/2⌋+k}; plus, at even N only, the readable-value/unreadable-
> residual band term (q−1)·q^{2}·q^{Σcomp(s): s ∈ A₁, s > N/2}·q^{k−1}
> (dμ = N/2: value stable, S₀-pair out of window — GENH4-CAP(F)). At
> odd N: the single q-power q^{N+2k−2}·… = q^{k−1}·q^{N−1+k} =
> q^{N+2k−2}. All verified against the committed table (S1's correction
> box: (2,7,3) → 512 = 2^{N+h−1}; (2,8,1) F → 1024 = 512 + 512, the
> even-N two-term law; (3,5,1) → 486·(q−1)^t ladder). ∎”

**CONDITIONALITY:** PROVED. **Its “2s ≥ N” complement is the in-note derivation ANNEX PE5's A1 uses to show the genre-F SPLTAIL cap `2w < N` was “always recoverable”** — the UND law's own free-slot condition is the SPLTAIL range's complement.

**ARITHMETIC AUDIT (compiler-computed):** genre E total `q^{deep₀ + #A₁≥N} = q^{(h−1)/2 + N + (h−1)/2} = q^{N+h−1}` ✓ **exact**. Aggregate: `q^{N+h−1}·q^{N−1−2h} = q^{2N−h−2}` ✓ (ladder size `(N−1) − (2h+1) + 1 = N−1−2h` ✓). Genre F odd N: `q^{k−1}·q^{N−1+k} = q^{N+2k−2}` ✓. Even N: `2⌊N/2⌋ = N`, main `q^{N+k}·q^{k−1} = q^{N+2k−1}` ✓ matching `.10`'s first term ✓; band term `(q−1)q²·q^{…}·q^{k−1}` = `(q−1)q^{N+2k−1}` ✓ matching the second ✓. **The check value `(3,5,1) → 486`:** at `q = 3, N = 5, k = 1`, odd N, `q^{N+2k−2} = 3⁵ = 243`, and with the ψ-census `(q²−q)/2 = 3`, `3·243·… ` — **486 = 2·243 = (q−1)·q^{N+2k−2}** ✓, i.e. the per-(ψ,H₂) law times the `(q−1)^r` letter at `r = 1`, or the ψ-count times 162; **the displayed “486·(q−1)^t ladder” is consistent with `486 = 2·3⁵`** and the exact attribution of the factor 2 is not displayed — recorded as UNPINNED-BY-DISPLAY.

**DERIVATION:** Displayed (slot counting on the S2.3 strings).

**RESOLUTION TRACE:** statement lines 530–545. correction sites: none in range; consumed by PE5's A1 (shard 2).

**TEETH:** **GH-UND 92/0** including the h = 3 correction value 512 and the even-N two-term F law ✓.

---

### EFF.GENH4.28  [theorem]

**CANONICAL STATEMENT:** FORM: prose frame + **five bulleted case analyses** (§S7 — the proof of THEOREM GENH4.C by the resolvent method; OB-c). Emitted as ONE unit: the five bullets share one frame, one classical trichotomy, and — decisively — **ANNEX R's R4 riders ALL of their displayed valuation equations at once**. verbatim, lines 549–597.

> “Fix any disc ≠ 0 lift F ∈ O[x] of a decided-leaf member, any root θ
> of F, L := Q_p-analogue(θ) (the fraction field of O extended; both
> characteristics). All leaf data consumed below are lift-stable
> (GENH4-CAP), so every lift shares them. Two facts used throughout:
> (E) every root has v(θ) = h/2 (the level-1 polygon is the exact
> single side — its pins are in-window), so e(L) is even; (F) every
> root has v(θ) = k and res(θπ^{−k}) = a root of ψ, so F_{q²} ⊆ k_L and
> f(L) is even. Let Y := φ^(t)(θ) (the current key evaluated at θ; the
> S5 chain keeps the state exact at every node). Then
>
>     Y² + A₁(θ)·Y + A₀(θ) = 0,
>
> with v(A₁(θ)) = w/2, v(A₀(θ)) = u/2 EXACTLY (GENH4-2; dv-units
> halved; genre F: w, u in v₁ = v units). The Y-trichotomy (classical
> ultrametric analysis of a quadratic over the complete field L):
>
> * **RAM (u odd, u ≤ 2w).** One-side Y-polygon: v(Y) = u/4 (E: v-units
>   u/4 with u odd ⟹ denominator 4 ⟹ 4 | e(L) ⟹ [L:base] = 4: f
>   irreducible, σ = {(4,1)}. F: v(Y) = u/2, u odd ⟹ 2 | e(L); with
>   f(L) ≥ 2: e·f = 4 ⟹ σ = {(2,2)}).
> * **2SIDED (u > 2w).** v(Y) ∈ {w/2, (u−w)/2}, distinct. The norm
>   count: Π_θ φ(θ) = Res(F, φ) = Π_{η: φ(η)=0} F(η) = Nm_R(A₀), of
>   valuation u (both genres, using GENH4-2 at the key's own roots η,
>   which satisfy the same v/residue facts); if j roots sit at w/2:
>   j·w/2 + (4−j)(u−w)/2 = u forces j = 2. If F were irreducible its
>   four roots would be conjugate and v(φ(θ)) Galois-invariant —
>   contradiction. E: no root lies in the base (v = h/2 ∉ ℤ) ⟹ two
>   quadratic factors, each with roots at v = h/2: e = 2, f = 1:
>   σ = {(2,1),(2,1)}. F: two quadratic factors, each with residue ȳ in
>   its residue field: f = 2, e = 1: σ = {(1,2),(1,2)}. (disc ≠ 0 ⟹
>   the two factors are coprime; the multiset is as displayed.)
> * **SPLTAIL.** A₀ window-zero, w < cap: EVERY lift has u_lift ≥ 2N >
>   2w (E; GENH4-CAP's undercut floor) — a 2SIDED configuration for
>   every lift, including the A₀ = 0 corner (F = φ·(φ + A₁): both
>   factors have the S2.1 one-side polygon: same σ): σ as 2SIDED. ∎
> * **SPLITEQ ('11', roots s₁ ≠ s₂).** ONE MORE REFINE STEP decides it:
>   apply the S5 recentering with letter s₁ (a root — the kill needs
>   only R₂(s₁) = 0): the new state has dv(A₀′) > 2dμ and dv(A₁′) = dμ
>   EXACTLY with digit R₂′(s₁) = s₁ − s₂ ≠ 0 (char 2: = S₁ ≠ 0, forced
>   by '11' separability): a 2SIDED configuration for every lift —
>   σ = {(2,1),(2,1)} (E) / {(1,2),(1,2)} (F) by the previous bullet.
>   (Hensel at the stage, executed as one refine step.)
> * **INERT ('2', R₂ irreducible over K).** v(Y) = dμ/2 (one-side
>   polygon at the boundary) and Ȳ := res(Y/n₂(θ)) is a root of
>   T² + S₁T + S₀^eff = R₂ (S3's twisted-normalizer computation — the
>   reader's twist convention derived, not assumed). Ȳ ∈ k_L: E:
>   [F_q(Ȳ):F_q] = 2 ⟹ f(L) ≥ 2, with e(L) ≥ 2: [L:base] = 4,
>   σ = {(2,2)}; F: [F_q(Ȳ):F_q] = 4 (R₂ irreducible over F_{q²}) ⟹
>   f(L) ≥ 4: σ = {(1,4)}. ∎”

**CONDITIONALITY:** **Three riders land on this unit from shard 2, and they are of three different kinds.**
1. **ANNEX PE5's A2 (`provenance-rider`, MINOR 2):** S7's norm valuation “u (both genres)” is stated in E's halved units; at genre F the norm valuation is **2u**. “the defect is the prose tag, not the computation” — `j = 2` and every σ conclusion are unaffected, and the note exhibits a **self-alarm**: a reader mixing units gets `j = 9`, impossible for 4 roots.
2. **ANNEX R's R4 (`wording-rider`, MINOR, SUPERSEDING A2's partial rider):** *all* displayed valuation equations in the trichotomy are E-halved; the F true-unit table is `v(A₁(θ)) = w`, `v(A₀(θ)) = u`, RAM `v(Y) = u/2` (already true-unit), 2SIDED `v(Y) ∈ {w, u−w}`, INERT `v(Y) = dμ` with `n₂ = π^{dμ}`. “Every σ conclusion is invariant under the rescaling.”
3. **ANNEX PE5's A1 + ANNEX R's R1 (`license`):** the SPLTAIL bullet's displayed inequality is genre-E only; the F instance is ANNEX-LEMMA GENH4-7(b), then GENH4-7′(b) over the true counted family (`.30`).
4. **ANNEX R's R6 (`scope-pin`):** the `(GENH4-2)` cite at the key's own roots is to the proof, not the stated scope.

**ARITHMETIC AUDIT (compiler-computed):** RAM at E: `v(Y) = u/4` with u odd ⟹ denominator 4 ⟹ `4 | e(L)` ⟹ `[L:base] ≥ 4` and `= 4` since `deg f = 4` ✓ → `{(4,1)}` ✓. RAM at F: `v(Y) = u/2`, u odd ⟹ `2 | e`; with `f ≥ 2` and `ef = 4` ⟹ `e = 2, f = 2` ✓ → `{(2,2)}` ✓. 2SIDED norm balance: `j·(w/2) + (4−j)·((u−w)/2) = u` ⟹ `jw + (4−j)(u−w) = 2u` ⟹ `j(2w−u) = 4(u−w) − 2u + … ` — recomputed: `jw + 4u − 4w − ju + jw = 2u` ⟹ `2jw − ju + 4u − 4w = 2u` ⟹ `j(2w−u) = 2w·2 − 2u = 2(2w − u)` ⟹ **`j = 2`** (when `u ≠ 2w`) ✓ **exact**, matching A2's own `j(2w−u) = 2(2w−u)`. INERT at E: `[F_q(Ȳ):F_q] = 2` ⟹ `f ≥ 2`, with `e ≥ 2` (genre E always) ⟹ `ef ≥ 4 = ef` ⟹ `e = f = 2` ✓ → `{(2,2)}` ✓. INERT at F: `[F_q(Ȳ):F_q] = 4` ⟹ `f ≥ 4` ⟹ `f = 4, e = 1` ✓ → `{(1,4)}` ✓. **Every σ in the dictionary of `.11` is re-derived here and agrees.**

**DERIVATION:** The unit IS the proof.

**RESOLUTION TRACE:** statement lines 549–597. correction sites: 1346–1388 (PE5's A2), 1227–1344 (PE5's A1), 1500–1625 (ANNEX R's R1), 1774–1801 (R4), 1841–1848 (R6) — all shard 2.

**TEETH:** **GH-SIGMA 6,185/0** (PARI on five never-oracled fresh rows) + 35,380 committed oracle checks at pin; **GH-T-SIG** fired 2×. **Machine contact for the F-SPLTAIL leg specifically comes only from the annexes** (PE5's C5: 21/21; ANNEX R's C5/C6: 96/96 char-0 + 96/96 char-p) — **in the accepted body that leg is PROOF-ONLY**, which is exactly what the Codex ratification found.

**BOUNDARY NOTE (rule 9):** the five bullets are kept as ONE unit because R4 riders all of them with a single normalization sentence and because they share the frame and the trichotomy. **Recorded as arguable:** SPLTAIL alone attracts three separate riders and a merge may prefer it addressable; the compiler's compromise is to name it `.28`(SPLTAIL) in every cross-reference.

---

### EFF.GENH4.29  [lemma]

**CANONICAL STATEMENT:** FORM: the norm-identity clause of `.28`'s 2SIDED bullet, emitted as its own addressable object (a second emission of a sub-span of `.28`, flagged at §6.1; three shard-2 riders name it individually). verbatim, lines 569–574.

> “* **2SIDED (u > 2w).** v(Y) ∈ {w/2, (u−w)/2}, distinct. The norm
>   count: Π_θ φ(θ) = Res(F, φ) = Π_{η: φ(η)=0} F(η) = Nm_R(A₀), of
>   valuation u (both genres, using GENH4-2 at the key's own roots η,
>   which satisfy the same v/residue facts); if j roots sit at w/2:
>   j·w/2 + (4−j)(u−w)/2 = u forces j = 2.”

**CONDITIONALITY:** **THREE riders, three kinds.** (1) ANNEX PE5's A2: the valuation tag “u (both genres)” is stated in E's halved units; **at genre F the norm valuation is 2u** — “the defect is the prose tag, not the computation”, and the note supplies a *self-alarm* (a unit-mixing reader gets `j = 9`, impossible for 4 roots). (2) ANNEX R's R4 **supersedes A2's partial rider** with a single normalization sentence covering all of S7. (3) ANNEX R2's Remark 1 riders R3's audit sentence about where this computation lives: “the genuinely L-resident part (the norm identity over the key's roots) is covered as stated”, while S7's Y-trichotomy “runs in the quartic root field base(θ_F), not in L = Frac(R)”. (4) ANNEX R's R6 licenses the `(GENH4-2)` cite “at the key's own roots η” as a cite to the proof, not the stated scope.

**SUPERSESSION KIND:** A2 = `provenance-rider` (a units tag); R4 = `replacement` of A2's rider by a wider one (**a rider superseding a rider — the only such case in this shard**); Remark 1 = `scope-pin`; R6 = `license`.

**ARITHMETIC AUDIT:** re-derived at `.28` — `j(2w−u) = 2(2w−u)` ⟹ `j = 2` for `u ≠ 2w` ✓, **in both the halved and the unhalved form** (A2's own point) ✓. The self-alarm: mixing units gives `j·w + (4−j)(u−w) = u` ⟹ `j = (4w−3u)/(2w−u)`; at `(w,u) = (3,7)`, `(12−21)/(6−7) = 9` ✓ **exact** — impossible for 4 roots ✓.

**DERIVATION:** Displayed. The F-side instance and the machine tie are PE5's A2 (five members over `φ = x² + 2x + 4`, `v₂(Res) = 14 = 2u`, two independent routes + PARI).

**RESOLUTION TRACE:** statement lines 569–574. correction sites: 1346–1388 (PE5 A2), 1774–1801 (R4), 1841–1848 (R6), 2092–2099 (R2.REM Remark 1) — all shard 2.

**TEETH:** PE5's annex leg C4 (five members, two routes, PARI) — annex-resident.

---

### EFF.GENH4.30  [lemma]

**CANONICAL STATEMENT:** FORM: the SPLTAIL bullet of `.28`, emitted a second time as its own addressable object (three shard-2 riders name it individually). verbatim, lines 580–583.

> “* **SPLTAIL.** A₀ window-zero, w < cap: EVERY lift has u_lift ≥ 2N >
>   2w (E; GENH4-CAP's undercut floor) — a 2SIDED configuration for
>   every lift, including the A₀ = 0 corner (F = φ·(φ + A₁): both
>   factors have the S2.1 one-side polygon: same σ): σ as 2SIDED. ∎”

**CONDITIONALITY:** **The one leg of THEOREM GENH4.C whose genre-F instance is NOT displayed in the accepted body.** ANNEX PE5's A1 rider 3 supplies it: “at genre F the displayed inequality's instance is **u_lift ≥ N > 2w** (ANNEX-LEMMA GENH4-7(b) below); the rest of the bullet … applies verbatim.” ANNEX R's R1 then finds GENH4-7's hypothesis covers only “the band-zero SLICE of the leaf — a strict subfamily, exactly HALF the leaf at the first live cell” and replaces it with **GENH4-7′(b)** over the whole counted family. **The σ label never moves; the proof's family does.**

**SUPERSESSION KIND:** `license` (PE5 supplies the F instance), then `license` again with a widened hypothesis (ANNEX R). Not a replacement at any step — “the labels were always right … the annex ADDS the displayed F-inequality, it does not correct a label” (PE5's What-does-not-move).

**DERIVATION:** E: displayed. F: GENH4-7′(b), shard 2.

**RESOLUTION TRACE:** statement lines 580–583. proof lines — E in place; F at 1274–1314 and 1537–1579 (shard 2). correction sites: 1227–1344, 1500–1625 (shard 2).

**TEETH:** in the accepted body, **PROOF-ONLY at genre F**; machine contact is annex-resident (PE5 C5 21/21; ANNEX R C5 96/96 char-0 + C6 96/96 char-p + C7 tooth 4/4).

---

### EFF.GENH4.31  [lemma]

**CANONICAL STATEMENT:** FORM: the SPLITEQ bullet of `.28`, second emission. verbatim, lines 584–590.

> “* **SPLITEQ ('11', roots s₁ ≠ s₂).** ONE MORE REFINE STEP decides it:
>   apply the S5 recentering with letter s₁ (a root — the kill needs
>   only R₂(s₁) = 0): the new state has dv(A₀′) > 2dμ and dv(A₁′) = dμ
>   EXACTLY with digit R₂′(s₁) = s₁ − s₂ ≠ 0 (char 2: = S₁ ≠ 0, forced
>   by '11' separability): a 2SIDED configuration for every lift —
>   σ = {(2,1),(2,1)} (E) / {(1,2),(1,2)} (F) by the previous bullet.
>   (Hensel at the stage, executed as one refine step.)”

**CONDITIONALITY:** Riddered only by R4's global normalization (`.28`). **Note the structural difference from ANNEX R2's withdrawn “refine-deeper leg”:** here the refine step is applied to a *state* whose in-window digits are the leaf's, and the resulting `dv(A₁′) = dμ` is FORCED by the separability digit — **not** a free choice of a fresh node. **The withdrawn annex argument tried to choose a fresh leaf on a FIXED member, which is what R2.G1 refutes; this bullet does not.** Recorded so a merge does not read R2.G1 as touching the accepted body.

**ARITHMETIC AUDIT:** `R₂′(s₁) = s₁ − s₂` for `R₂ = (T−s₁)(T−s₂)` ✓ (derivative at `s₁`); nonzero iff `s₁ ≠ s₂` ✓, which '11' gives ✓. In char 2, `R₂′ = S₁` ✓ (the derivative of `T² + S₁T + S₀` is `S₁`), nonzero by separability ✓.

**DERIVATION:** Displayed; consumes `.23` (the refine kill) and `.28`'s 2SIDED bullet.

**RESOLUTION TRACE:** statement lines 584–590. correction sites: 1774–1801 (R4, shard 2).

**TEETH:** GH-SIGMA (the σ labels) + GH-REFINE (the one-step kill formulas).

---

### EFF.GENH4.32  [lemma]

**CANONICAL STATEMENT:** FORM: the INERT bullet of `.28`, second emission. verbatim, lines 591–597.

> “* **INERT ('2', R₂ irreducible over K).** v(Y) = dμ/2 (one-side
>   polygon at the boundary) and Ȳ := res(Y/n₂(θ)) is a root of
>   T² + S₁T + S₀^eff = R₂ (S3's twisted-normalizer computation — the
>   reader's twist convention derived, not assumed). Ȳ ∈ k_L: E:
>   [F_q(Ȳ):F_q] = 2 ⟹ f(L) ≥ 2, with e(L) ≥ 2: [L:base] = 4,
>   σ = {(2,2)}; F: [F_q(Ȳ):F_q] = 4 (R₂ irreducible over F_{q²}) ⟹
>   f(L) ≥ 4: σ = {(1,4)}. ∎”

**CONDITIONALITY:** Riddered by R4 (`v(Y) = dμ` and `n₂ = π^{dμ}` in F's true units). **Its INERT-existence content is what ANNEX R2's R2.M2 has to complete by a coset count** at the `2w = N` stratum (shard 2) — the accepted body's bullet is a *classification given an inert residual*, not an *existence* claim, and the annex needed the latter.

**ARITHMETIC AUDIT:** E: `f ≥ 2` and `e ≥ 2` with `ef = 4` ⟹ `e = f = 2` ✓. F: `f ≥ 4` with `ef = 4` ⟹ `f = 4, e = 1` ✓. `[F_q(Ȳ):F_q] = 4` at genre F because `R₂` is irreducible over `K = F_{q²}` ✓ so `Ȳ` generates a quadratic extension of `F_{q²}`, degree 4 over `F_q` ✓.

**DERIVATION:** Displayed; consumes `.20` (the twisted normalizer).

**RESOLUTION TRACE:** statement lines 591–597. correction sites: 1774–1801 (R4, shard 2); existence completed at 2033–2059 (R2.M2, shard 2).

**TEETH:** GH-SIGMA; **GH-T-CEN** (the INERT census mutant) fired 14×.

---

### EFF.GENH4.33  [scope-record]

**CANONICAL STATEMENT:** FORM: closing paragraph of §S7. verbatim, lines 599–603.

> “Every case used only lift-stable data ⟹ (A0)-strong at the stage.
> This proves (H-e) AT THESE TWO GENRES; the general (H-e) is untouched
> (S10-BOX-2). [machine: GH-SIGMA — PARI per member on fresh rows incl.
> q = 7, deep h = 5, k = 2; plus the 35,380 committed oracle checks
> consumed at pin.]”

**CONDITIONALITY:** **“(A0)-strong at the stage” is the exact phrase W-12's r4 FIRING CHECK cites when ruling the σ-LABELING clause SUPPLIED at n = 4** (`.53`). The general-(H-e) fence is GENH4-BOX-2 (`.45`).

**DERIVATION:** `.28`–`.32`.

**RESOLUTION TRACE:** statement lines 599–603. correction sites: none.

**TEETH:** GH-SIGMA 6,185/0 + 35,380 committed oracle checks at pin.

---

### EFF.GENH4.34  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, LEMMA GENH4-6 — P-D settled) + its proof. verbatim, lines 607–629.

> “**LEMMA GENH4-6.** At every reachable refine event of either genre —
> any window N, any entry (h resp. k), any prehistory, any history —
> the S₁ residual slot is LIVE (a genuine coordinate digit exists at
> its position). Hence the '1sq' census is exactly q^{f₁}−1 of
> Q(Q−1) unit-pairs at every node (refine rate 1/Q, Q = q^{f₁}), in
> BOTH characteristics, and QSCOUT22's P-D configuration (dead S₁
> slot forcing (T² + S₀) ≡ square at q even — the forced cascade) is
> UNREALIZABLE at the quartic (2,2) stages. P-D was untestable
> in-roster because it is VACUOUS at n = 4 — a theorem, not a
> coverage gap. Its content, if any, lives at higher-degree stages
> (S10-BOX-4).”

**CONDITIONALITY:** **A negative result turned into a theorem: an untested empirical configuration is shown UNREALIZABLE rather than merely unobserved** — “a theorem, not a coverage gap”. Its residual content is boxed at GENH4-BOX-4 for `m′ ≥ 3` or `E ≥ 3`.

**DERIVATION:** verbatim, lines 619–629:

> “*Proof.* Readable refine depths satisfy dμ ≤ N−1 (E; cap 2dμ < 2N)
> resp. dμ ≤ ⌈N/2⌉−1 (F; 2dμ < N), and dμ > floor ≥ 2h resp. 2k. E,
> dμ odd: the S₁ position (dμ−h)/2 lies in [(h+1)/2, N−1] ⟺
> 2h+1 ≤ dμ ≤ 2N−2+h — both hold. E, dμ even: position dμ/2 ∈
> [h+1, N−1] ⟺ 2h+2 ≤ dμ ≤ 2N−2 — both hold. F: the a₀-component
> position dμ ≤ N−1 holds (dμ < N/2); the a₁-component position
> dμ−k ∈ [k+1, N−1] holds (dμ ≥ 2k+1). The slot strings are
> key-independent (S2.3) and floors only rise, so this covers every
> node of every history, and prehistory only deepens the entry floors.
> With the slot live, S₁ is a free digit and the census is the W-11
> residual table over K (counts characteristic-blind). ∎”

Justification tags: `computation` (four interval checks against `.17`'s strings) + `by XREF S2.3`'s key-independence + `by XREF` W-11's residual table.

**ARITHMETIC AUDIT (compiler-computed):** E odd dμ: `S₁` sits at α₁-position `(dμ−h)/2`; the string's range is `[(h+1)/2, N−1]` ✓ (`.17`), and `(dμ−h)/2 ≥ (h+1)/2 ⟺ dμ ≥ 2h+1` ✓, `(dμ−h)/2 ≤ N−1 ⟺ dμ ≤ 2N−2+h` ✓. E even dμ: position `dμ/2 ∈ [h+1, N−1] ⟺ 2h+2 ≤ dμ ≤ 2N−2` ✓. Both hold given the floors (`dμ > 2h`) and the cap (`dμ ≤ N−1` in dv… **compiler note: the cap is `2dμ < 2N`, i.e. `dμ < N` in dv-units, which is weaker than `dμ ≤ 2N−2+h`** ✓ so the upper checks pass comfortably). F: `dμ < N/2` gives the a₀ position `≤ N−1` ✓; `dμ ≥ 2k+1` gives the a₁ position `dμ−k ≥ k+1` ✓. **All four interval checks reproduce.** Census: `q^{f₁}−1` of `Q(Q−1)` unit pairs with `Q = q^{f₁}` gives refine rate `(Q−1)/(Q(Q−1)) = 1/Q` ✓ **exact**.

**RESOLUTION TRACE:** statement lines 607–617. proof lines 619–629. correction sites: none.

**TEETH:** **GH-PD [SAME] 46,590/0** — “(a) the GENH4-6 liveness inequalities scanned over 1 ≤ h ≤ 15, N ≤ 40, all readable dμ (integer check of the lemma)” ✓, plus the pointwise AS-degeneration and both cascade rows.

---

### EFF.GENH4.35  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the char-2 structure exhibited in vitro, with two smoke-caught corrections disclosed). verbatim, lines 631–650.

> “**The char-2 structure that P-D pointed at, exhibited in vitro
> (machine leg GH-PD) — with TWO smoke-caught corrections, disclosed.**
> At q even, '1sq' ⟺ S₁ = 0 (Artin–Schreier degeneration: T² + S₀ is
> always a square in char 2; checked POINTWISE on every refine event of
> the char-2 walker rows). On the CONSTRUCTED sub-locus {A₁ ≡ 0}, in
> EQUAL characteristic 2, every even-dv0 read is forced to '1sq' — the
> cascade P-D described, realized by conditioning rather than by slot
> death — BUT the naive claim "no SPLITEQ/INERT ever on the locus" is
> FALSE, twice over, and this unit's own smoke caught both:
> (i) in MIXED characteristic 2 the refine update's +2w term revives A₁
> at dv + 2e₀ (2 ≠ 0), and (ii) even in EQUAL characteristic 2 an
> ODD-dμ refine's CARRY C = wc² revives A₁ at the even height
> 2(dμ − h) — the W-9 cocycle itself is the escape hatch from the
> cascade. The TRUE forced statement, machine-checked: in char 2 no
> SPLITEQ/INERT key on the locus carries an all-even (or empty) H₂ —
> the cascade is forced exactly along the carry-free even ladder —
> while at odd q SPLITEQ/INERT with all-even H₂ exist (the
> characteristic separator; the split is by the square-class of
> −S₀^eff). Battery: the (h, N, dμ)-grid liveness scan + the pointwise
> AS-degeneration + the cascade loci at (Fqt,2,7,h1) and (Zp,3,5,h1).”

**CONDITIONALITY:** **Two false claims caught by the note's own PRE-SEAL smoke and corrected before the seal** (`.61` lists them as smoke-caught correction (i)). **The second escape hatch is the W-9 carry itself** — the same object `.23` computes — which is a genuinely surprising structural finding.

**DERIVATION:** Not a theorem; an in-vitro construction with a machine-checked corrected statement.

**RESOLUTION TRACE:** statement lines 631–650. correction sites: none post-seal; the pre-seal corrections are disclosed at 1040–1053 (`.61`).

**TEETH:** GH-PD 46,590/0, including “char-2 all-even-H₂ leaves = RAM/UND only; q = 3 realizes SPLITEQ/INERT at all-even H₂ — the separator” ✓ (`.65`). Disposition: **planted-free discovery followed by a corrected preregistration** — the corrections landed BEFORE the seal and are disclosed, which is the honest form.

---

### EFF.GENH4.36  [theorem]

**CANONICAL STATEMENT:** FORM: prose section (§S9.1 — the discharge and the firing). verbatim, lines 656–666.

> “[GENIND-H(4)] asks (CS-1)/(CS-2)/(CS-3) at every genre realizable at
> degree ≤ 4. Genre-completeness: LEMMA Q22-A (the composite entry
> classification at the quadruple center) + THEOREM GENIND.A(IV) with
> S5.3's grammar (deeper CS openings inherit the same two genres
> through the α/β transports, self-similarly; machine-enforced both
> directions at the GENIND and QSCOUT22 seals). CS-1 = S2–S5; CS-2 =
> S6.2; CS-3 = S7. **[GENIND-H(4)] DISCHARGED.** THEOREM GENIND.B at
> n = 4 (with the proved P(2), P(3)) yields P(4): the history-resolved
> exact menu + finite (A1) aggregate menu + (A0) + exact-complement
> (A2) at degree 4 — hence (hMenu-4)+(hExhaust-4) — conditional exactly
> on the S11 stack (no new hypothesis enters).”

**CONDITIONALITY:** **The discharge, and its genre-completeness leg is a consumed citation** (Q22-A + GENIND.A(IV) + S5.3's grammar). **GENIND.A(IV)'s converse is scoped to DEGREE level by GENIND's own ANNEX R R5** (GENIND shard 3 `.19`) — which is the direction consumed here (“every genre realizable at degree ≤ 4”), so **the scoping does not disturb this discharge** ✓. **(CS-EXACT) is again unnamed** (`.12`).

**DERIVATION:** §S2–§S7 assembled.

**RESOLUTION TRACE:** statement lines 656–666. correction sites: none in range.

**TEETH:** GH-JSONTIE/GH-FRESH (CS-1), GH-BRACKET (CS-2), GH-SIGMA (CS-3).

XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` — count **5**; `S5.3` — count **26**; `THEOREM GENIND.B` — count **7**.

---

### EFF.GENH4.37  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (§S9.2's first two block vectors). verbatim, lines 670–679.

> “Write ν for "conditional σ-distribution of a cluster block, N → ∞";
> each is node-self-similar (the per-node fractions are
> floor-independent — S6.1), so entering at any refine locus gives the
> same vector. From the proved menus:
>
> * **ν₂ (DBL, W-11):** ram {(2,1)}: q/(q+1); split {(1,1)²}:
>   1/(2(q+1)); inert {(1,2)}: 1/(2(q+1)).
> * **ν₂^{(2)} (DBLQ, the (m,d) = (2,2) cluster = W-11 over Q = q²,
>   GENIND-1/2/3 at d = 2):** {(2,2)}: Q/(Q+1); {(1,2)²}: 1/(2(Q+1));
>   {(1,4)}: 1/(2(Q+1)).”

**ARITHMETIC AUDIT (compiler-computed):** ν₂ sums to `q/(q+1) + 1/(2(q+1)) + 1/(2(q+1)) = q/(q+1) + 1/(q+1) = 1` ✓ **exact partition**. ν₂^{(2)} likewise sums to 1 over `Q` ✓.

**CONDITIONALITY:** ν₂^{(2)} consumes GENIND-1/2/3 at `d = 2`, where GENIND-BOX-3 discloses thin machine coverage — GENH4-BOX-3 inherits the disclosure (`.46`).

**DERIVATION:** W-11's aggregation, cited; the self-similarity is `.25`'s floor-independence.

**RESOLUTION TRACE:** statement lines 670–679. correction sites: none.

**TEETH:** GH-DENS (the ν₂/ν₂^{(2)} ties are dchecks in the sealed battery, per `.62`'s `[r2]` note).

---

### EFF.GENH4.38  [run-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S9.2's ν₃ bullet with its landed `[r2, PE2 MINOR 1]` additive-leg record). verbatim, lines 680–694.

> “* **ν₃ (TRP, HMENU3 @ pins):** q³·T_τ of HM3.D S5.5 = the engine's
>   β₃ term for term. [r2, PE2 MINOR 1: within the SEALED battery this
>   identity was engine-internal — the runner DEFINES nu3 = ENG.beta(3),
>   no dcheck. Now EXECUTED in an additive supplementary leg
>   (`genh4r2_supp.py`, the he7r1_supp.py precedent; the sealed runner
>   and its artifacts byte-untouched): T_τ derived from the ACCEPTED
>   HMENU3 note's displays alone (the five R_τ of HM3.D, the S5.5
>   per-center block densities, elementary level-0 censuses) by
>   inverting R_τ = SEP_τ + (q−1)·c²_{τ″} + q·T_τ, then q³·T_τ ≡ β₃(τ)
>   checked term for term against the md5-pinned engine: **GREEN, 0
>   violations** — Σ_τ T_τ = q^{−3} symbolic, the five ties symbolic
>   AND exact at q = 2, 3, 5, 7, 11, key sets exactly equal, tooth
>   (corrupted DBL route) fired. Artifacts: genh4r2_supp_output.txt md5
>   8ce5faa8843f1bc0c88dd3658f412d9c, genh4r2_supp_results.json md5
>   c966d3115229e0f12798e054be9940ed.]”

**CONDITIONALITY:** **A TAUTOLOGY caught and repaired: the sealed battery DEFINED `nu3` as the engine's own `beta(3)`, so the “tie” was vacuous.** The r2 leg executes it non-tautologically by deriving `T_τ` from the accepted HMENU3 note's displays alone. **PE3 subsequently verified the leg “non-tautological” in substance** (`.70`).

**SUPERSESSION KIND:** `inventory completion` (a claimed tie that was engine-internal is executed for real).

**ARITHMETIC AUDIT:** `Σ_τ T_τ = q^{−3}` symbolic and `q³·T_τ ≡ β₃(τ)` ⟹ `Σ_τ β₃(τ) = 1` ✓ — internally consistent with a probability vector ✓.

**DERIVATION:** Not a mathematical unit; a run record.

**RESOLUTION TRACE:** statement lines 680–694. correction sites: none.

**TEETH:** `genh4r2_supp.py` GREEN with a fired tooth (corrupted DBL route). **PIN VERIFICATION:** `verification/openmath/genh4r2_supp.py` ✓, `_output.txt` ✓, `_results.json` ✓ EXIST.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.D` — count **13**.

---

### EFF.GENH4.39  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (§S9.2's μ_E — the E-stage vector, carrying a dangling editing token). verbatim, lines 695–704.

> “* **μ_E (THE E-STAGE VECTOR, from S6):** the stage is W-11 on the
>   full integer dv-ladder, so the same generating-function aggregation
>   as W-11 S2.4/S2.5 gives, conditional on entry: RAM-mass
>   q²/(q²+q+1), SPLITEQ (q−2)/(2(q²+q+1)), INERT q/(2(q²+q+1)),
>   2SIDED 1/(q²+q+1) − extra…, REFINE 1/(q²+q+1); summing the refine
>   geometric series (×(q²+q+1)/(q²+q)):
>   **μ_E = ( {(4,1)}: q/(q+1); {(2,1),(2,1)}: 1/(2(q+1));
>   {(2,2)}: 1/(2(q+1)) )** — EXACTLY ν₂'s fractions with the stage
>   σ-dictionary: the (2,2) stage is W-11 in dv-units at the density
>   level too.”

**CONDITIONALITY:** **The display carries a dangling editing remnant, “− extra…”, closed by ANNEX PE5's A3: the extra is 0.** A3 supplies the per-node masses from scratch and the coefficientwise closure `2q² + (q−2) + q + 2 + 2 = 2Φ₂`, with a tooth (“extra = r⁴ breaks Σ = 1 at every q”). **The token is an editing remnant, not a mathematical hedge** — and the closure is self-alarming, which is why it survived to acceptance.

**SUPERSESSION KIND:** (received) `replacement` of a dangling token by 0, with a derivation.

**ARITHMETIC AUDIT (compiler-computed, checking A3's closure independently):** with `Φ₂ = q²+q+1`, the five masses are `q²/Φ₂`, `(q−2)/(2Φ₂)`, `q/(2Φ₂)`, `1/Φ₂`, `1/Φ₂`. Over the common denominator `2Φ₂` the numerators are `2q², (q−2), q, 2, 2`, summing to `2q² + 2q + 2 = 2Φ₂` ✓ **exact — Σ = 1** ✓, confirming extra = 0. The refine aggregation: multiplying the non-refine masses by `Φ₂/(q²+q)` gives RAM `q²/(q²+q) = q/(q+1)` ✓; SPLITEQ+2SIDED `[(q−2)/2 + 1]/(q²+q) = (q/2)/(q²+q) = 1/(2(q+1))` ✓; INERT `(q/2)/(q²+q) = 1/(2(q+1))` ✓ — **exactly μ_E as displayed, and exactly ν₂'s fractions** ✓.

**DERIVATION:** W-11's generating-function aggregation, transported; A3 supplies the per-node closed forms.

**RESOLUTION TRACE:** statement lines 695–704. correction sites: 1390–1421 (PE5's A3, shard 2).

**TEETH:** GH-DENS (μ_E ≡ ν₂'s fractions is a dcheck) + **GH-T-DENS** (μ_E corrupted to the integer-ladder aggregation must break BOTH the β₄ tie and Σ = 1) fired 1× ✓.

---

### EFF.GENH4.40  [lemma]

**CANONICAL STATEMENT:** FORM: bulleted display (§S9.2's μ_F). verbatim, lines 705–709.

> “* **μ_F (THE F-STAGE VECTOR):** the same in Q = q²:
>   **( {(2,2)}: q²/(q²+1); {(1,2)²}: 1/(2(q²+1));
>   {(1,4)}: 1/(2(q²+1)) )** = ν₂^{(2)}'s fractions (two different
>   keys, one conditional law — the f-then-e and the level-0-d = 2
>   routes to the same three σ's at the same densities).”

**ARITHMETIC AUDIT:** sums to `q²/(q²+1) + 1/(q²+1) = 1` ✓. Equals ν₂^{(2)} at `Q = q²` ✓ (`.37`).

**CONDITIONALITY:** **A genuine coincidence of two routes** — the f-then-e stage and the level-0 `d = 2` cluster reach the same three σ's at the same densities. Not a proof obligation; a corroborating structural fact.

**DERIVATION:** `.39`'s aggregation over `Q = q²`.

**RESOLUTION TRACE:** statement lines 705–709. correction sites: none.

**TEETH:** GH-DENS (μ_F ≡ ν₂^{(2)}-fractions, a dcheck).

---

### EFF.GENH4.41  [lemma]

**CANONICAL STATEMENT:** FORM: prose section (§S9.3 — ν₄ and the level-0 assembly). verbatim, lines 713–741.

> “ν₄ = the conditional σ-distribution of the quadruple-center block:
> the depth-0 exact-polygon families (one-side: RAM4 / G2(h;λ) incl.
> (q−1)·μ_E at λ = (1²) / FULL(k;λ₄) with the s4-census incl. the
> D-tags' child re-entries D211 → ν₂⊎{(1,1)²}, D2Q → ν₂⊎{(1,2)},
> D22 → ν₂⊗ν₂, D31 → ν₃⊎{(1,1)}, F → μ_F, D4 → the prehistory
> self-loop; two-side and three-side vertex families with per-side
> outcomes: odd-drop length-2 side → {(2,1)}, even-drop →
> '11'/'2'/'1sq' → {(1,1)²}/{(1,2)}/ν₂; length-3 side → {(3,1)} or the
> cubic censuses with (1,1²) → {(1,1)}⊎ν₂ and (1³) → ν₃; four simple
> sides → {(1,1)⁴}), each family's mass = S_T·q^{4−Σ⌈P(j)⌉−L} (W-12.A
> in density form) summed geometrically over its slope parameters —
> solved for the self-loop: ν₄ = (Σ events)/(1 − Σ_k (q−1)q^{−10k}).
> The full enumeration is executed SYMBOLICALLY in the sealed engine
> (exact sympy over the symbol q; every family's closed form is in the
> runner's `nu4_families` with this note's table as the spec), with
> three independent checks: (a) partition of unity Σ(masses) = 1
> symbolically; (b) **ν₄ ≡ β₄** — the md5-pinned
> `om_density_engine.py`'s quartic cluster law, derived by the DIFFERENT
> route (the Igusa-cell fixpoint recursion (R)) and reconciled against
> the BCFG literature distribution through n = 5/6 (`reconcile_om_bcfg`)
> — term by term over all cluster σ-types; (c) the finite-N partial
> sums (S9.4). Level-0: the eleven R_τ(q) = Σ over the f̄-factorization
> shapes (census/q⁴ each) of the products of block vectors and decided
> pieces — the shapes and censuses: distinct {1111: C(q,4), 11·2̄:
> C(q,2)n₂, 2̄2̄′: C(n₂,2), 1·3̄: q·n₃, 4̄: n₄}, with multiplicity
> {2·11: qC(q−1,2) → ν₂⊎{(1,1)²}, 2·2̄: qn₂ → ν₂⊎{(1,2)}, 2·2:
> C(q,2) → ν₂⊗ν₂, 3·1: q(q−1) → ν₃⊎{(1,1)}, 4: q → ν₄, 2̄²: n₂ →
> ν₂^{(2)}} (n_d = #monic irreducibles of degree d; Σ censuses = q⁴,
> asserted).”

**CONDITIONALITY:** **The assembly is executed symbolically in the sealed engine with the note's table as spec** — so the note's proof content is the family table, and the engine is the executor. **GENH4-BOX-6 scopes the β₄ tie**: “'independent' means decorrelated method, not accepted-arc supplier; the density display's proof content is S9.2–S9.3 over THIS note's laws + the pinned suppliers; the β₄ tie and BCFG reconciliation are corroboration legs.”

**ARITHMETIC AUDIT (compiler-computed, on the level-0 census closure):** with `n₁ = q`, `n₂ = (q²−q)/2`, `n₃ = (q³−q)/3`, `n₄ = (q⁴−q²)/4`, the eleven shape censuses are `C(q,4) + C(q,2)n₂ + C(n₂,2) + q·n₃ + n₄ + qC(q−1,2) + q n₂ + C(q,2) + q(q−1) + q + n₂`. **The note asserts this sums to `q⁴` and does not display the computation.** Spot check at `q = 2`: `n₂ = 1, n₃ = 2, n₄ = 3`; terms: `C(2,4)=0`, `C(2,2)·1=1`, `C(1,2)=0`, `2·2=4`, `3`, `2·C(1,2)=0`, `2·1=2`, `C(2,2)=1`, `2·1=2`, `2`, `1` → total `0+1+0+4+3+0+2+1+2+2+1 = 16 = 2⁴` ✓ **exact**. At `q = 3`: `n₂=3, n₃=8, n₄=18`; `C(3,4)=0`, `C(3,2)·3=9`, `C(3,2)=3`, `3·8=24`, `18`, `3·C(2,2)=3`, `3·3=9`, `C(3,2)=3`, `3·2=6`, `3`, `3` → `0+9+3+24+18+3+9+3+6+3+3 = 81 = 3⁴` ✓ **exact**. **The asserted closure verifies at two anchors.**

**DERIVATION:** The family table + `W-12.A in density form` + the self-loop geometric solve; executed symbolically.

**RESOLUTION TRACE:** statement lines 713–741. correction sites: none.

**TEETH:** **GH-DENS 115/0** — partition of unity symbolically, `ν₄ ≡ β₄` term by term, the level-0 census `Σ = q⁴`, and the finite-window sandwiches ✓.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:THEOREM W-12.A` — count **8**.

---
### EFF.GENH4.42  [table]

**CANONICAL STATEMENT:** FORM: prose + **fixed-width ASCII display** (§S9.4 — THE ELEVEN QUARTIC DENSITIES, with anchors), emitted TWICE per rule 14. verbatim, lines 745–767.

> “Derived by the S9.2–S9.3 assembly, executed symbolically at the seal
> (the sealed run re-verifies every line). With Φ₂ := q²+q+1,
> Φ₃ := q⁶+q³+1, Φ₅ := q⁴+q³+q²+q+1:
>
>     R_{(1,1)⁴}        = q⁶(q⁸−2q⁷+q⁶+2q⁵−q⁴+2q³+q²−2q+1) / (24(q+1)²Φ₂Φ₃Φ₅)
>     R_{(1,1)²(1,2)}   = q⁶(q⁸+2q⁷+3q⁶+2q⁵+q⁴+2q³+3q²+2q+1) / (4(q+1)²Φ₂Φ₃Φ₅)
>     R_{(1,1)²(2,1)}   = q³(q¹⁰+q⁸+3q⁷+q⁶+q⁵+3q⁴+2q³+2q²+2q+1) / (2(q+1)²Φ₂Φ₃Φ₅)
>     R_{(1,1)(1,3)}    = q⁶(q+1)²(q²−q+1) / (3Φ₃Φ₅)
>     R_{(1,1)(3,1)}    = q(q⁹+2q⁷+q⁶+q⁵+2q⁴+2q³+q²+q+1) / (Φ₂Φ₃Φ₅)
>     R_{(1,2)²}        = q⁶(q⁶+q⁵−2q³+q+1) / (8(q+1)²(q²+1)Φ₂Φ₃)
>     R_{(1,2)(2,1)}    = q³(q⁶+q⁵+q⁴+q+1) / (2(q+1)²Φ₂Φ₃)
>     R_{(1,4)}         = q⁶Φ₅ / (4(q²+1)Φ₂Φ₃)
>     R_{(2,1)²}        = q² / (2(q+1)²Φ₂)
>     R_{(2,2)}         = q²(q⁷+q⁶+q⁴+q³+2q²+q+1) / (2(q+1)(q²+1)Φ₂Φ₃)
>     R_{(4,1)}         = (q⁶+q⁵+q³+q+1) / ((q+1)Φ₂Φ₃)
>
>     Σ_τ R_τ = 1 exactly (symbolic, and as exact rationals at
>     q = 2, 3, 5). Anchors: q = 2: (344/142569, 13072/142569,
>     7348/142569, 576/2263, 1838/15841, 664/22995, 460/4599,
>     496/2555, 2/63, 454/7665, 107/1533); q = 3: (821097/152417408,
>     10043433/76208704, 1983555/38104352, 27216/91597, 75774/1190761,
>     336069/6298240, 28539/314912, 88209/393640, 9/416, 13707/393640,
>     1003/39364) — in the order listed above.”

`[TABLE]` — the eleven densities, transcribed (rule 14's second emission), with the q = 2 anchor beside each:

| τ | R_τ(q) | anchor at q = 2 |
|---|---|---|
| `(1,1)⁴` | `q⁶(q⁸−2q⁷+q⁶+2q⁵−q⁴+2q³+q²−2q+1) / (24(q+1)²Φ₂Φ₃Φ₅)` | `344/142569` |
| `(1,1)²(1,2)` | `q⁶(q⁸+2q⁷+3q⁶+2q⁵+q⁴+2q³+3q²+2q+1) / (4(q+1)²Φ₂Φ₃Φ₅)` | `13072/142569` |
| `(1,1)²(2,1)` | `q³(q¹⁰+q⁸+3q⁷+q⁶+q⁵+3q⁴+2q³+2q²+2q+1) / (2(q+1)²Φ₂Φ₃Φ₅)` | `7348/142569` |
| `(1,1)(1,3)` | `q⁶(q+1)²(q²−q+1) / (3Φ₃Φ₅)` | `576/2263` |
| `(1,1)(3,1)` | `q(q⁹+2q⁷+q⁶+q⁵+2q⁴+2q³+q²+q+1) / (Φ₂Φ₃Φ₅)` | `1838/15841` |
| `(1,2)²` | `q⁶(q⁶+q⁵−2q³+q+1) / (8(q+1)²(q²+1)Φ₂Φ₃)` | `664/22995` |
| `(1,2)(2,1)` | `q³(q⁶+q⁵+q⁴+q+1) / (2(q+1)²Φ₂Φ₃)` | `460/4599` |
| `(1,4)` | `q⁶Φ₅ / (4(q²+1)Φ₂Φ₃)` | `496/2555` |
| `(2,1)²` | `q² / (2(q+1)²Φ₂)` | `2/63` |
| `(2,2)` | `q²(q⁷+q⁶+q⁴+q³+2q²+q+1) / (2(q+1)(q²+1)Φ₂Φ₃)` | `454/7665` |
| `(4,1)` | `(q⁶+q⁵+q³+q+1) / ((q+1)Φ₂Φ₃)` | `107/1533` |

**ARITHMETIC AUDIT (compiler-computed, rule 22 — spot-checking the two simplest closed forms against their anchors at q = 2, where `Φ₂ = 7`, `Φ₃ = 73`, `Φ₅ = 31`):**
* `R_{(2,1)²} = q²/(2(q+1)²Φ₂) = 4/(2·9·7) = 4/126 = 2/63` ✓ **exact match to the anchor.**
* `R_{(4,1)} = (q⁶+q⁵+q³+q+1)/((q+1)Φ₂Φ₃) = (64+32+8+2+1)/(3·7·73) = 107/1533` ✓ **exact match.**
* `R_{(1,4)} = q⁶Φ₅/(4(q²+1)Φ₂Φ₃) = 64·31/(4·5·7·73) = 1984/10220 = 496/2555` ✓ **exact match.**
* `R_{(1,1)(1,3)} = q⁶(q+1)²(q²−q+1)/(3Φ₃Φ₅) = 64·9·3/(3·73·31) = 1728/6789 = 576/2263` ✓ **exact match.**
* `R_{(1,2)(2,1)} = q³(q⁶+q⁵+q⁴+q+1)/(2(q+1)²Φ₂Φ₃) = 8·(64+32+16+2+1)/(2·9·7·73) = 8·115/9198 = 920/9198 = 460/4599` ✓ **exact match.**
**Five of the eleven closed forms reproduce their q = 2 anchors exactly by independent computation.** The remaining six have higher-degree numerators; the note's own symbolic `Σ_τ R_τ = 1` and the engine tie are the checks of record for those, and GH-DENS scores them.
* **Denominator structure.** `Φ₂ = q²+q+1`, `Φ₃ = q⁶+q³+1`, `Φ₅ = q⁴+q³+q²+q+1` are the cyclotomic-like factors `(q³−1)/(q−1)`, `(q⁹−1)/(q³−1)`, `(q⁵−1)/(q−1)` ✓ — the shapes W-12.A's cell sums produce ✓.

**CONDITIONALITY:** **Conditional exactly on the S11 arc-grade stack**, whose minimum grade was 0/2 at composition (`.44`). The display was “computed by the smoke run and pasted verbatim into this note at the seal” (`.63`) — i.e. **the density block is machine-generated text, sealed before the full run**, and §S13's run 2 re-verifies every line.

**DERIVATION:** `.41`'s assembly, executed symbolically.

**RESOLUTION TRACE:** statement lines 745–767. correction sites: none.

**TEETH:** GH-DENS 115/0 (symbolic Σ = 1, `ν₄ ≡ β₄`, anchors at q = 2,3,5, partial-sum sandwiches on 9 full-sweep rows) + GH-T-DENS fired.

---

### EFF.GENH4.43  [scope-record]

**CANONICAL STATEMENT:** FORM: numbered display (§S9.4b — what “triple-tied” means). verbatim, lines 771–789.

> “1. **Symbolic:** partition of unity of the ν₄ family table; level-0
>    census Σ = q⁴; Σ_τ R_τ = 1 — all as identities in ℚ(q) (GH-DENS).
> 2. **Engine:** ν₄ ≡ β₄ term by term (the md5-pinned
>    `om_density_engine`'s quartic cluster law, derived by ITS OWN
>    Igusa-cell fixpoint recursion and reconciled against BCFG through
>    n = 5/6); likewise ν₂ ≡ β₂, ν₂^{(2)} ≡ β₂-scaled, μ_E ≡ ν₂'s
>    fractions, μ_F ≡ ν₂^{(2)}'s. Visible instance: R_{(4,1)} =
>    β₄({(4,1)})/q³ — the quadruple cluster is the ONLY source of
>    {(4,1)}, the n = 4 analogue of HM3.D's R_τ = q³β₃(τ) observation.
>    Classical spot identity **[commit-2 display addition, computed
>    between seal and verdict; no sealed text changed]**: Σ_τ #{(1,1)
>    parts of τ}·R_τ = q/(q+1) exactly at the anchors — the expected
>    root count, the same value as at n = 2, 3 (HM3.D's E[#roots]
>    display, degree-stable).
> 3. **Finite windows:** on every full-sweep row (committed + fresh),
>    per τ: resolved_τ(N) ≤ ν₄(τ)·q^{4(N−1)} ≤ resolved_τ(N) +
>    unresolved(N) as exact integers (the partial sums of ν₄'s series
>    vs the measured decided masses — a theorem given S6, so any
>    failure refutes the assembly), plus the committed PARI σ legs.”

**CONDITIONALITY:** **Three ties of three different epistemic kinds**, and the note distinguishes them: symbolic identities, a decorrelated-method engine tie (scoped by GENH4-BOX-6 as corroboration, not supply), and finite-window sandwiches. **The classical spot identity is a commit-2 display addition** — disclosed as computed between seal and verdict, with “no sealed text changed”.

**ARITHMETIC AUDIT (compiler-computed, on the classical spot identity at q = 2):** `Σ_τ #{(1,1) parts}·R_τ` — the τ's with `(1,1)` parts and their multiplicities: `(1,1)⁴` ×4, `(1,1)²(1,2)` ×2, `(1,1)²(2,1)` ×2, `(1,1)(1,3)` ×1, `(1,1)(3,1)` ×1. Using the q = 2 anchors: `4·344/142569 + 2·13072/142569 + 2·7348/142569 + 576/2263 + 1838/15841`. First three over 142569: `(1376 + 26144 + 14696)/142569 = 42216/142569`. Now `142569 = 3·7·... ` — recomputed: `24(q+1)²Φ₂Φ₃Φ₅ = 24·9·7·73·31 = 24·9·15841 = 3421656`; the note's anchor denominator is 142569, so a common factor was cancelled ✓ (`3421656/142569 = 24`). Note `142569 = 9·7·73·31 = 9·15841` ✓. And `2263 = 73·31` ✓, `15841 = 7·73·31` ✓. Converting: `576/2263 = 576·63/142569 = 36288/142569` ✓ (since `142569/2263 = 63`); `1838/15841 = 1838·9/142569 = 16542/142569` ✓. Total: `(42216 + 36288 + 16542)/142569 = 95046/142569`. And `q/(q+1) = 2/3`; `2/3 = 95046/142569` ⟺ `3·95046 = 2·142569` ⟺ `285138 = 285138` ✓ **EXACT**. **The classical spot identity verifies at q = 2 by independent computation** — a genuinely strong corroboration, since it ties five of the eleven anchors to a degree-stable classical quantity.

**DERIVATION:** Not a proof; a tie inventory. Item 3 is “a theorem given S6”.

**RESOLUTION TRACE:** statement lines 771–789. correction sites: none.

**TEETH:** GH-DENS 115/0 across all three ties; the partial-sum sandwich runs on 9 full-sweep rows.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:HM3.D` — count **13**.

---

### EFF.GENH4.44  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S10's GENH4-BOX-1, grades) with THREE landed `[r1]`/`[r2]`/`[r3]` stack refreshes. verbatim, lines 793–849. *(Quoted in full at the source; here the box's opening and the three refresh brackets' governing sentences are quoted, with the intervening per-supplier cell lists marked `…` — the only truncation in this shard, taken because the cells are re-emitted verbatim at `.48`–`.56`.)*

> “* **GENH4-BOX-1 (grades).** 0/2, composed this session, NO hostile
>   arc yet. COROLLARY GENH4.D inherits the MINIMUM grade over the S11
>   stack: {W-11 (accepted, counter 2/2), W-12 (0/2, PE arc live), HEX3
>   (0/2, r1), HMENU3 (0/2, PE2 next), GENIND (0/2, unopened), QSCOUT22
>   (instrument), this note (0/2)}. P(4) is a CONDITIONAL STRUCTURE at
>   exactly that stack — displayed, not upgraded. [r1 2026-08-08 (PE1
>   minor S10-BOX-1): the sealed "HMENU3 (0/2, PE2 next)" cell was
>   stale AT COMPOSE … Stack refreshed to NOW against git: … Every supplier motion since seal STRENGTHENED
>   the stack (PE1's observation); the minimum grade over the stack is
>   unchanged, so P(4)'s conditionality display is unaffected.]
>   **[r2 2026-08-08 (PE2 MINOR 2): the r1 "refreshed to NOW" display
>   aged again in two cells, one of them optimistically. … The MINIMUM grade over the stack is unchanged at 0/2, so
>   P(4)'s conditionality display is unaffected — the r1 disposition,
>   for partly different reasons.]**
>   **[r3 2026-08-09 (PE3 REMARK B): stack re-refreshed against git at
>   THIS repair's commit (HEAD cc20066). … Minimum grade over the stack unchanged at 0/2;
>   P(4)'s conditionality display unaffected. STANDING DISCLOSURE
>   [r3]: every stack line in this box is AS-OF ITS COMMIT TIMESTAMP —
>   supplier arcs run concurrently in the same waves, so any stack
>   display can be stale within write-to-commit latency (three
>   photo-finishes on this arc: PE1's minor, PE2's MINOR 2, PE3's
>   REMARK B); currency is guaranteed by the verifier's own
>   verdict-time git refresh, not by any frozen display.]**”

**CONDITIONALITY:** **A stack display that went stale THREE TIMES in three consecutive rounds, and the third round's response is a STANDING DISCLOSURE rather than a fourth refresh.** That disclosure — “currency is guaranteed by the verifier's own verdict-time git refresh, not by any frozen display” — is the structural answer, and it is the same disease GENIND's SERIES RECORD-INTEGRITY documents five times over. **The invariant across all three refreshes: “the minimum grade over the stack is unchanged at 0/2, so P(4)'s conditionality display is unaffected.”** The box's own grade line (`0/2, composed this session, NO hostile arc yet`) is superseded by the acceptance (`.01`).

**SUPERSESSION KIND:** three successive `counter re-reading`s (per-supplier grade cells) + a final `license` (the standing as-of disclosure changes how every stack display is to be read).

**CHAIN:** sealed stack → `[r1]` refresh (one stale cell) → `[r2]` refresh (two stale cells, one optimistically) → `[r3]` refresh + **STANDING DISCLOSURE — TERMINAL** (the display is as-of, and currency comes from the verifier).

**ARITHMETIC AUDIT:** the three photo-finishes the disclosure enumerates ✓ (PE1's minor, PE2's MINOR 2, PE3's REMARK B) — three, matching the three refreshes ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 793–849. correction sites: 1450–1463, 1850–1868, 2105–2127 (the three dated BOX-1 appends, shard 2).

**TEETH:** NONE — **and the box says why: no display can be current.** Disposition: `stale self-description` ×3, each disclosed and repaired, then structurally disclaimed.

**PIN VERIFICATION:** `cc20066` ✓; the ~20 supplier commits cited across the three refreshes all resolve (verified in bulk; see §3.2).

---

### EFF.GENH4.45  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 850–856.

> “* **GENH4-BOX-2 ((H-e) scope).** THEOREM GENH4.C proves the (H-e)
>   INSTANCE at the two n = 4 genres only. The general (H-e) — higher
>   key degree, higher m′, E > 2, deeper residue towers — remains
>   [W12-H]'s open box; the n = 5 embedded genres (GENIND S5.3) are NOT
>   discharged here: **P(5) does NOT fire from this note** (its
>   stage-2 genres are (2,2)-shaped and the S7 method is built to
>   transport, but the transport is future work, not a claim).”

**CONDITIONALITY:** Standing, and re-asserted in every annex's What-does-not-move paragraph. **“P(5) does NOT fire from this note” is the sharpest scope sentence in the corpus's discharge chain.**

**DERIVATION:** Not a mathematical unit; a scope fence.

**RESOLUTION TRACE:** statement lines 850–856. correction sites: none — re-asserted at 1473, 1881, 2139 (shard 2).

**TEETH:** NONE.

XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:[W12-H]` — count **17**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:S5.3` — count **26**.

---

### EFF.GENH4.46  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 857–863.

> “* **GENH4-BOX-3 (d ≥ 2 / prime powers).** The DBLQ vector ν₂^{(2)}
>   consumes GENIND-1/2/3 at d = 2 (proved at general (m, d), but
>   GENIND-BOX-3 discloses thin machine coverage there); this battery
>   adds a d = 2-relevant fresh full row and the ψ-census ties; genre-F
>   rows at q = 4 remain unbuilt (F₁₆ kit — QSCOUT22 Q22-BOX-3
>   inherited); prime-power-q composite rows rest on the proofs'
>   uniformity + the supplier batteries.”

**CONDITIONALITY:** **An inherited coverage hole, disclosed with its provenance** (GENIND-BOX-3 and Q22-BOX-3 both named). `q = 4` genre-F rows unbuilt.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 857–863. correction sites: none.

**TEETH:** `signed vacuity disclosure` at `q = 4` genre F and at general prime-power composite rows.

XREF: `lean/notes/openmath/QSCOUT22_2026-08-08.md:Q22-BOX-3` — count **1**.
XREF: `lean/notes/openmath/GENIND_PROOF_2026-08-08.md:GENIND-1` — count **15**; `GENIND-2` — count **27**; `GENIND-3` — count **37**.

---

### EFF.GENH4.47  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 864–867.

> “* **GENH4-BOX-4 (P-D's residual content).** GENH4-6 kills P-D at
>   n = 4 only. At stages with m′ ≥ 3 or E ≥ 3 slot misalignment is not
>   ruled out; P-D stands as an open flag for the [GENIND-H(n ≥ 5)]
>   program.”

**CONDITIONALITY:** Standing. The complement of `.34`'s theorem.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 864–867. correction sites: none.

**TEETH:** NONE — an open flag.

---

### EFF.GENH4.48  [convention]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 868–875.

> “* **GENH4-BOX-5 (conventions).** Conservative tails (UND is an upper
>   bound for the σ-residue — exact as counted); canonical-lift letter
>   convention (W-2/LIFTCORNER seam NOT consumed; histories are
>   convention-keyed exactly as QSCOUT22 discloses); reader
>   reimplementation seams: the fresh rows are read by the md5-PINNED
>   QSCOUT22 reader (GREEN + PARI-tied at its seal) — this note's
>   battery contributes independent LAWS, fresh territory, the
>   pointwise transfer leg, and PARI, not a fresh reader.”

**CONDITIONALITY:** **A structurally different seam from GENIND's**: GENH4 does NOT write a fresh reader — it writes fresh LAWS and reads with the pinned QSCOUT22 reader. **So the reader-reimplementation risk GENIND-BOX-6 discloses does not apply here; the risk here is the opposite one (a shared reader), and the note names its mitigations: independent laws, fresh territory, a pointwise transfer leg, and PARI.**

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 868–875. correction sites: none.

**TEETH:** the four named mitigations are GH-JSONTIE (independent laws, both directions), GH-FRESH (fresh territory), GH-REFINE (pointwise), GH-SIGMA (PARI).

---

### EFF.GENH4.49  [fence]

**CANONICAL STATEMENT:** FORM: bulleted display. verbatim, lines 876–881.

> “* **GENH4-BOX-6 (the density engine's role).** β₄ is derived by the
>   engine's own recursion — an INDEPENDENT route, but 'independent'
>   means decorrelated method, not accepted-arc supplier; the density
>   display's proof content is S9.2–S9.3 over THIS note's laws + the
>   pinned suppliers; the β₄ tie and BCFG reconciliation are
>   corroboration legs.”

**CONDITIONALITY:** **The corpus's cleanest statement of what a decorrelated corroboration is and is not.** It prevents the eleven densities from being read as engine-supplied.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 876–881. correction sites: none.

**TEETH:** the engine tie is scored at GH-DENS but is **explicitly not a supply**.

---

### EFF.GENH4.50  [supplier-finding]

**CANONICAL STATEMENT:** FORM: bulleted display (a defect report against QSCOUT22, with an offered fold obligation). verbatim, lines 882–887.

> “* **GENH4-BOX-7 (Q22-L3 display slip).** The scout note's quoted
>   genre-E UND law is wrong at h > 1 (S1 correction box; committed
>   artifact decides). Fold obligation: QSCOUT22's next repair round
>   should annex the corrected law; nothing else in that note consumed
>   it (checked: the S6/S8 mentions are the only sites; the runner's
>   model — the sealed predictor — always had it right).”

**CONDITIONALITY:** **Type `supplier-finding` (rule 13) — a defect report against another note, discharged at the source.** OFFERED, not landed. **Cross-note check: GENIND's §S9.3 QSCOUT22 bullet records the scout's L3-correction annex `fcaf268` as fixing “the genre-E UND display's h = 1 slip, the same slip GENH4-BOX-7 discloses”** (GENIND shard 2 `.16`) — **so the fold obligation WAS discharged at the source, and GENIND records it while GENH4 (frozen) does not.**

**SUPERSESSION KIND:** none of GENH4's own; an outbound finding.

**DERIVATION:** `.10`'s CORRECTION disclosed.

**RESOLUTION TRACE:** statement lines 882–887. correction sites: none in this note; discharged externally at QSCOUT22 `fcaf268` (recorded in GENIND, shard 2 `.16`).

**TEETH:** the committed artifact decides — `qscout22_results.json` @ `dd67cda`, md5-pinned ✓.

**PIN VERIFICATION:** `fcaf268` ✓ (the source-side discharge commit).

---
### EFF.GENH4.51  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S11's GENIND bullet). verbatim, lines 891–893.

> “* **GENIND** @ 4682bcf (verdict 4984004; 0/2): GENIND-1(ii) (m = 4
>   prehistory), GENIND-4 (the E fibration), GENIND.B (the induction
>   consuming this discharge), the criterion + genre grammar.”

**CONDITIONALITY:** An as-of pin at GENIND's pre-r1 state. **The consumed clauses are all stable across GENIND's r1–r6 arc and its two 2026-08-12 corrections** (checked against GENIND's own per-clause survival screens). **Note the reciprocal consumption: GENIND.B consumes THIS discharge, and this note consumes GENIND.B** — the dependency is not circular because GENIND.B is a *conditional* reduction whose hypothesis this note discharges at n = 4.

**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 891–893. correction sites: 798–849 (`.44`'s refreshes).
**TEETH:** GH-PIN (artifact side only).
**PIN VERIFICATION:** `4682bcf` ✓, `4984004` ✓.
**NEAR-MISS:** `GENIND-1(ii)` — count **0**; parent `LEMMA GENIND-1` count **2** (as at `.16`).

---

### EFF.GENH4.52  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S11's QSCOUT22 bullet). verbatim, lines 894–898.

> “* **QSCOUT22** @ dd67cda (seal 970197d; instrument): the empirical
>   table this note's laws are keyed to; Q22-A entry classification;
>   the committed artifacts (results JSON md5
>   6c2441a12cf52ffd43055de912a4affe, runner md5
>   cb885663dd4ef6dfda9c28a67c1a076e) consumed as the roster tie.”

**CONDITIONALITY:** **The roster tie is to md5-pinned ARTIFACTS, not to the note's prose** — which is why GENH4-BOX-7's finding against the scout's *display* leaves the tie intact.

**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 894–898. correction sites: none.
**TEETH:** GH-PIN 0/6; GH-JSONTIE both directions against the pinned JSON.
**PIN VERIFICATION:** `dd67cda` ✓, `970197d` ✓; `verification/openmath/qscout22_results.json` ✓ and `qscout22_checks.py` ✓ EXIST.

---

### EFF.GENH4.53  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S11's W-12 bullet) with a landed `[r1]` and a landed `[r2]` re-pin carrying the **fired-clause check**. verbatim, lines 899–923.

> “* **W-12.A/S2.5/W12-L0/L1 + W-12.D** @ w12 seal f669cb0/r2 99f1813
>   (0/2, PE3 owed): entry-volume laws, the cell calculus, the
>   reduction that P(4) fires. [r1 2026-08-08: arc now — body unchanged
>   at r2 99f1813, counter 0/2; PE3 launched, first attempt a recorded
>   casualty (died mid-response; record 8c984db), re-running.]
>   **[r2 2026-08-08 (PE2 GAP 2) — W-12.D RE-PINNED at W-12's current
>   text, r5 be4a1dc/ee17210 (arc since the r2 pin: PE3 c9c5c0e
>   0C+1G+1m → r3 b17238a/b8dfe62 → PE4 26689da **1 CRITICAL**+2G+2m →
>   r4 d2d91b7/5728258 → PE5 c3e2f8e 0C+1G+3m → r5; counter 0/2). The
>   stale pin was INSUFFICIENT by W-12's own later adjudication: W-12
>   PE4's GAP 1 showed the r2-pinned (A0)+(A1) never assert that
>   core-family members are σ-DECIDED with σ = σ_F, which Step 4's
>   lower bound needs (explicit degenerate one-family counter-instance
>   with R_split = 1 ≠ μ_split) — the cure is the **σ-LABELING clause**
>   added to (A1) at W-12 r4 ("each with a splitting type σ_F … such
>   that every disc ≠ 0 lift of every member has σ = σ_F"), post-pin
>   and previously uncited here. FIRED-CLAUSE CHECK (the check r1
>   performed for HEX3, owed here too): the added clause is SUPPLIED at
>   n = 4 — W-12's own [r4] FIRING CHECK carries an explicit n = 4 row
>   ruling it "**SUPPLIED.** THEOREM GENH4.C … the dictionary IS the
>   σ_F assignment, and the quantifier is over every lift of every leaf
>   member" (W12_PROOF_2026-08-08.md, firing table), matching S7's
>   closing "(A0)-strong at the stage". No conclusion moves; the
>   theorem GENH4.D(ii) fires is now the sufficient revision at the
>   current pin.]**”

**CONDITIONALITY:** **A stale pin found INSUFFICIENT by the supplier's own later adjudication — not merely out of date, but missing a clause the consumer needs.** The cure is W-12's σ-LABELING clause, and **this note supplies it: THEOREM GENH4.C IS the σ_F assignment** (`.11`, `.33`). **This is the tightest supplier↔consumer loop in the corpus: W-12 needed a clause, GENH4 proves it, and W-12's own firing table rules it SUPPLIED at n = 4.** Cross-note: GENIND records the same clause as “STRENGTHENED (A1)” at its §S16 row 1 (GENIND shard 2 `.09`, `.64`).

**SUPERSESSION KIND:** `as-of scoping` (the re-pin) + `inventory completion` (the fired-clause check, “owed here too”).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 899–923. correction sites: none post-r2.
**TEETH:** `transfer audit` — a clause-level check against the supplier's own firing table.
**PIN VERIFICATION:** `f669cb0` ✓, `99f1813` ✓, `8c984db` ✓, `be4a1dc` ✓, `ee17210` ✓, `c9c5c0e` ✓, `b17238a` ✓, `b8dfe62` ✓, `26689da` ✓, `d2d91b7` ✓, `5728258` ✓, `c3e2f8e` ✓ — **12/12.**
XREF: `lean/notes/openmath/W12_PROOF_2026-08-08.md:σ-LABELING` — count **7**; `THEOREM W-12.D` — count **5**; `W12-L0` — count **32**; `W12-L1` — count **30**; `S2.5` — count **9**.

---

### EFF.GENH4.54  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S11's W-11 bullet). verbatim, lines 924–925.

> “* **W-11** @ 7020ceb/r2 31506b3, PE3 CLEAN 839b735 + PE4 CLEAN
>   16d12e1 (ACCEPTED 2/2): the n = 2 system every stage transports.”

**CONDITIONALITY:** The only ACCEPTED supplier at composition time. **“the n = 2 system every stage transports” is the note's thesis in five words.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 924–925. correction sites: none.
**TEETH:** GH-PIN.
**PIN VERIFICATION:** `7020ceb` ✓, `31506b3` ✓, `839b735` ✓, `16d12e1` ✓.

---

### EFF.GENH4.55  [scope-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S11's HEX3/HMENU3 bullet) with a landed `[r1]` fired-clause check. verbatim, lines 926–937.

> “* **HEX3 / HMENU3** @ e3f3459/671a126/2580f12 and 64d3ff9/625fa49
>   (0/2 arcs live): ν₃, the n = 3 package P(3), the telescoping
>   template. [r1 2026-08-08: arcs now — HMENU3 ACCEPTED 2/2 (PE3 CLEAN
>   7e5026a + PE4 CLEAN 6249166; fold 050425d; the consumed pins
>   64d3ff9/625fa49 unchanged); HEX3 at r2 a707430 (PE2 0C+1G+1m
>   f60348b), PE3 CLEAN fca1a97, counter 1/2. Fired-clause check on the
>   HEX3 aging (PE1 Remark 1: HEX3 passPE2 landed 2.5 min AFTER this
>   note's seal): what this note consumes at the r1-2580f12 pin — the
>   ν₃/P(3) conclusions — is untouched by HEX3-PE2's findings (its gap
>   is HEX3's own never-measured-census bookkeeping, corrected at HEX3
>   r2; its minor an S8.2 aside this note never cites); HEX3 PE3 CLEAN
>   only corroborates.]”

**CONDITIONALITY:** **A 2.5-minute photo-finish, disclosed and fired-clause-checked.** The HEX3 aside the note never cites is §S8.2 — **the same §S8.2 whose W-12.B consistency clause HEX3's r3 later conditionalizes on the open HEX3-BOX-1 (ledger HYP.137)**, and this note's non-citation is what keeps it out of GENH4's chain too.

**SUPERSESSION KIND:** `as-of scoping` + `transfer audit` (the fired-clause check).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 926–937. correction sites: 813–829, 830–849 (`.44`'s r2/r3 refreshes, which move HEX3 to r3 `b6a1d69` and reset its counter to 0/2).
**TEETH:** `transfer audit`.
**PIN VERIFICATION:** `e3f3459` ✓, `671a126` ✓, `2580f12` ✓, `64d3ff9` ✓, `625fa49` ✓, `7e5026a` ✓, `6249166` ✓, `050425d` ✓, `a707430` ✓, `f60348b` ✓, `fca1a97` ✓ — **11/11.**
XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:S8.2` — count **10**.

---

### EFF.GENH4.56  [scope-record]

**CANONICAL STATEMENT:** FORM: two bulleted displays (§S11's mechanism-frame and engine bullets). verbatim, lines 938–947.

> “* **GRTJC W-6..W-9 + JC-LOAD/W-8 (ACCEPTED 2/2 @ 83f47f4), J-D0 @
>   9387eb1, DULEMMA @ f819f26, WELDMASTER/[W12-H] @ pins:** the
>   MECHANISM frame (S0's division: no count law consumes them; S3/S5
>   re-prove the needed instances elementarily; DULEMMA applicability
>   checked — E-stage on-perimeter (e_m = 2), not consumed).
> * **om_density_engine.py** @ md5 7240a916060c360d4433ca8a802d315d +
>   `reconcile_om_bcfg.py` (committed): β₄/β₃/β₂ ties (corroboration
>   leg only — BOX-6).
> * **Classical:** Hensel, Ore order-1, ultrametric quadratic analysis,
>   Artin–Schreier/square-class censuses over F_q and F_{q²}.”

**CONDITIONALITY:** **The mechanism frame is cited and NOT consumed** (`.05`); the engine is corroboration only (`.49`); the classical list is the genuine base.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 938–947. correction sites: none.
**TEETH:** GH-DENS for the engine ties; NONE for the mechanism frame (by design).
**PIN VERIFICATION:** `83f47f4` ✓, `9387eb1` ✓, `f819f26` ✓; `verification/openmath/om_density_engine.py` — **NOT in `verification/openmath/`; the md5 pin `7240a916…` is the note's own value and the file is not co-located with the battery** (recorded, §8 defect 2). `reconcile_om_bcfg.py` is named in the repo guide's numeric cross-checks and is a `verification/`-level script.

---

### EFF.GENH4.57  [scope-record]

**CANONICAL STATEMENT:** FORM: bold display (§S11's One line). verbatim, lines 949–953.

> “**One line: THEOREMS GENH4.A/B/C + LEMMAS GENH4-1F/-2/-CAP/-3/-4/-6
> rest on {GENIND-4/GENIND-1(ii) @ pin, W-12.A entry laws @ pin, W-11
> system @ accepted pin, classical}; COROLLARY GENH4.D adds GENIND.B +
> W-12.D + P(2)/P(3) @ pins. No axiom, no weld face inside any count
> law; grade = composition 0/2.**”

**CONDITIONALITY:** Header predicate A's governing quote. Its grade clause is superseded by the acceptance (`.01`). **“No axiom, no weld face inside any count law” is cashed at `.05` and re-proved at `.19`/`.23`.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 949–953. correction sites: 1450–1463 (shard 2).
**TEETH:** NONE.

---

### EFF.GENH4.58  [instrument-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S12's runner). verbatim, lines 957–963.

> “**Runner:** `verification/openmath/genh4_checks.py`. Exact integer /
> exact sympy arithmetic; deterministic; PARI/GP subprocess (GH-SIGMA
> only). Imports (md5-pinned, frozen): qscout22_checks (the reader +
> FExt + irred_quads; the MODEL functions are NOT called — this note's
> laws are re-implemented from S6 as `law_E`/`law_F`), w10_checks
> (rings), w12_checks (hull/censuses/GP kit), om_density_engine (β's),
> qscout22_results.json (the roster tie).”

**CONDITIONALITY:** **“the MODEL functions are NOT called — this note's laws are re-implemented from S6 as `law_E`/`law_F`”** is the decorrelation that makes GH-JSONTIE non-tautological, and it is the exact mirror of the ν₃ tautology `.38` had to repair.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 957–963. correction sites: none.
**TEETH:** self-referential. **PIN VERIFICATION:** the runner ✓ and `qscout22_checks.py` ✓ EXIST.

---

### EFF.GENH4.59  [instrument-record]

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's ten families with evidence classes). verbatim, lines 965–1025. *(Quoted in full in the source; the family names, classes and scopes are reproduced here as a `[TABLE]` with each family's defining clause quoted, per rule 5 — the source is a bulleted classification list, not prose.)*

`[TABLE]` — the ten battery families:

| Family | Class | Defining clause (quoted) |
|---|---|---|
| GH-PIN | [NONE] | “6 md5 pins (runner qscout22 cb885663…, results JSON 6c2441a…, output txt 378a12b3…, w10 a9c34244, w12 7dc040d9, engine 7240a916)” |
| GH-JSONTIE | [SAME] | “MY law evaluator (fresh code from S6's closed forms) reproduces EVERY composite key count … all 23 rows, BOTH directions; order-1/W12TIE keys re-derived from my own W-12.A transcription likewise” |
| GH-FRESH | [SAME] | “fresh never-measured rows, pinned reader vs my laws, both directions: consE (Zp,7,3,h1) … (Zp,2,11,h5) [deep entry h = 5 — first ever]; consF (Zp,7,5,k1), (Zp,2,9,k2) [first k = 2]; FULL sweep (Fqt,5,3)” — with **GH-CROSS considered and DROPPED for runtime budget, disclosed** |
| GH-PRE2 | [SAME] | “depth-2 prehistory constructed row (Zp,2,11, pre=(1,2), E at h = 5): the (q−1)² floored-fresh law at r = 2” |
| GH-REFINE | [SAME] | “the GENH4-4 one-step formulas POINTWISE … compare digit-by-digit with the pinned reader's divide_by_quad after recentering; assert the two pins die and the floored-node bijection (count both sides)” |
| GH-FEVEN | [SAME] | “the odd-q even-dμ genre-F stratum … constructed sub-locus {v₁(A₀) ≥ 2dμ} at (Zp,3,7,k1), built THROUGH the GENH4-1F development map (validating it constructively) … F_{q²} = F₉ censuses live here” |
| GH-PD | [SAME] | “(a) the GENH4-6 liveness inequalities scanned over 1 ≤ h ≤ 15, N ≤ 40 … (b) '1sq' ⟺ S₁ = 0 at q even, pointwise … (c) the in-vitro cascade … char 2 must yield ZERO SPLITEQ/INERT keys …, q = 3 must yield both (the separator)” |
| GH-UND | [SAME] | “THEOREM GENH4.B's closed forms vs every UND key … incl. the h = 3 correction value 512 and the even-N two-term F law; aggregates” |
| GH-BRACKET | [SYM] | “S6.2: Σ_{H⊆D}L^{|H|} = q^{f₁|D|} integer identities … + aggregated-vs-resolved key sums on the committed rows” |
| GH-DENS | [SYM/IND] | “S9: partition of unity … ν₄ ≡ β₄ …; the ELEVEN R_τ with Σ_τ R_τ = 1 symbolic; anchors at q = 2,3,5; partial-sum sandwich per τ on full-sweep rows” — with the `[r2, PE2 MINOR 1]` note that **ν₃ is DEFINITIONAL here** and its tie is executed in the additive leg (`.38`) |
| GH-SIGMA | [IND] | “PARI factorpadic σ per decided composite member, sampled: … never-oracled territory (q = 7 composite stages; h = 5; k = 2; r = 2)” |

**ARITHMETIC AUDIT:** the table has **eleven** rows, not ten — GH-PIN, GH-JSONTIE, GH-FRESH, GH-PRE2, GH-REFINE, GH-FEVEN, GH-PD, GH-UND, GH-BRACKET, GH-DENS, GH-SIGMA ✓ = 11 families, matching the eleven scored lines of §S13.2 ✓ (`.69`).

**CONDITIONALITY:** **One family was DROPPED for runtime budget and the drop is disclosed**: “GH-CROSS (a fresh (Zp,2,7) 16.7M full sweep to cross-check the committed cons rows) was considered and DROPPED for runtime budget — disclosed here and in the runner docstring; the cons rows remain tied through the model both directions + PARI.” **A `disclosed non-repair` at the design level.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 965–1025. correction sites: `[r2]` in situ at 1012–1015.
**TEETH:** this unit IS the family index.

---

### EFF.GENH4.60  [preregistration]

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's five teeth, each with its firing condition). verbatim, lines 1027–1038.

> “**Teeth (each must fire ≥ 1 or RED):**
> * GH-T-LAT — my law_E corrupted to the integer-only dv ladder must
>   mismatch on every E row (committed + fresh).
> * GH-T-CEN — INERT census q(q−1)/2 → q(q−1) must mismatch on every
>   INERT-realizing row.
> * GH-T-ALPH — law_F censuses over F_q instead of F_{q²} must mismatch
>   on every even-dμ-realizing F row INCLUDING the new odd-q GH-FEVEN
>   row (the tooth QSCOUT22 could only arm at q = 2).
> * GH-T-SIG — F-RAM σ flipped {(2,2)} → {(1,4)} must be caught by
>   PARI on the fresh F oracle rows.
> * GH-T-DENS — μ_E corrupted to the integer-ladder aggregation must
>   break BOTH the β₄ tie and Σ_τ R_τ = 1.”

**CONDITIONALITY:** **Five planted mutants, each targeting a distinct load-bearing claim** (the half-integer ladder, the INERT census, the `F_{q²}` alphabet, the F-RAM σ label, the μ_E aggregation). **GH-T-ALPH is explicitly a tooth QSCOUT22 could not arm** — new territory. All five fired at both runs (19/14/4/2/1).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1027–1038. correction sites: none.
**TEETH:** this unit IS the tooth specification.

---

### EFF.GENH4.61  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (§S12's pre-seal smoke, with three disclosed corrections). verbatim, lines 1040–1053.

> “**PRE-SEAL SMOKE (disclosed).** Developed and debugged with
> `--smoke`: GH-PIN + the FULL GH-JSONTIE (all 23 committed rows) +
> fresh consE (Zp,7,3,1) + consF (Zp,2,9,2) + GH-REFINE (Zp,2,6,1;
> 10,752 refine events, 0 formula violations) + GH-PD + GH-DENS
> symbolic + oracle (2,055 scored, 0 bad). Final smoke GREEN, 17.4 s,
> all five teeth fired. THREE smoke-caught corrections folded in BEFORE
> the seal and disclosed: (i) the in-vitro cascade claim scoped to the
> all-even-H₂ ladder (S8 — the mixed-char +2w revival AND the
> equal-char carry revival both caught by smoke runs 1–2); (ii) sympy
> Sum→Piecewise replaced by explicit geometric closed forms (no math
> change; the partition-of-unity identity adjudicates them); (iii) the
> smoke cascade row moved from Zp (mixed) to Fqt (equal char). The
> S9.4 density block was computed by the smoke run and pasted verbatim
> into this note at the seal. No full-roster run before the seal.”

**CONDITIONALITY:** **Three pre-seal corrections disclosed, one of them MATH-side** (the cascade scoping, `.35`). **And a disclosure a merge must carry: “The S9.4 density block was computed by the smoke run and pasted verbatim into this note at the seal”** — the eleven densities are machine-generated text, sealed before the full run and re-verified by it.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1040–1053. correction sites: none.
**TEETH:** the smoke itself, GREEN with all five teeth firing.

---

### EFF.GENH4.62  [preregistration]

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's P-1…P-9, sealed at commit 1 with never-measured spot values). verbatim, lines 1055–1085.

> “**Preregistered predictions P-1..P-9:**
>
> * P-1 [NONE] GH-PIN 0/6.
> * P-2 [SAME] GH-JSONTIE 0 violations over all 23 committed rows
>   (481 law-key checks at smoke; same count expected).
> * P-3 [SAME] GH-FRESH/GH-PRE2 0 violations; never-measured spot
>   values (computed from the S6 laws, pre-run): consE (Zp,2,11,h5):
>   total 2¹⁶ = 65,536 with EXACTLY TWO keys — RAM(21) = 32,768 and
>   UND = 32,768 = q^{N+h−1} (the deep-entry stratum drains HALF: the
>   stage ladder {2h+1,…,N−1} is EMPTY at N = 2h+1); consF (Zp,7,5,k1):
>   total 21·7⁶ = 2,470,629, keys RAM(5) = 2,117,682 and UND = 352,947
>   = 21·q^{N+2k−2} (odd-N single-power law); consE (Fqt,3,5,h1):
>   total 2·3¹² = 1,062,882; (Fqt,5,4,h1): 4·5⁸ = 1,562,500;
>   consE (Zp,7,3,h1): 14,406 = (q−1)q³·q^{...} split RAM(5) =
>   (q−1)²q³ = 12,348 + UND = (q−1)q³ = 2,058; pre2 (Zp,2,11,(1,2)):
>   2²⁰ members, law keys EXACTLY {E-RAM(21) = 32,768, E-UND = 32,768,
>   G2(5,'2') = 65,536, RAM4(9) = 524,288}; GH-FEVEN (Zp,3,7,k1,f0=5):
>   3·3¹² = 1,594,323 members, 8 keys incl. F-SPLITEQ(3)/INERT(3) at
>   the F₉ censuses 28/36.
> * P-4 [SAME] GH-REFINE 0 pointwise failures; every refine event's
>   carry lands above the pin; bijection counts equal.
> * P-5 [SAME] GH-FEVEN 0 violations; even-dμ = 3 keys realized at
>   q = 3 with F₉ censuses 28/36/8 (SPLITEQ/INERT/refine letters).
> * P-6 [SAME] GH-PD: liveness scan 0 dead slots; char-2 '1sq' ⟺
>   S₁ = 0 exact; cascade locus: 0 SPLITEQ/INERT keys at q = 2, both
>   present at q = 3.
> * P-7 [SAME] GH-UND 0 violations (incl. the 512 at (2,7,3));
>   GH-BRACKET all identities exact.
> * P-8 [SYM/IND] GH-DENS: partition of unity holds; ν₄ ≡ β₄; Σ_τ = 1;
>   all sandwiches hold.
> * P-9 [IND] GH-SIGMA 0 bad; teeth all fire.”

**CONDITIONALITY:** **The term “law keys” used in P-2 and P-3 is UNDEFINED, and the omission caused a verifier misreading** — ANNEX R's R5 (shard 2) defines it (`LAW_KINDS = ('RAM4','G2','FULL','SUB','E','F')`, genh4_checks.py line 299) and displays the pre2 row's full **six-key** partition, showing P-3's four-key sentence was “exactly right as a law-key statement” with the remainder being two non-law strata.

**SUPERSESSION KIND:** (received) `inventory completion` (a definition and a remainder supplied; no number moves).

**ARITHMETIC AUDIT (compiler-computed, on every spot value):**
* `(Zp,2,11,h5)`: total `2^{4(N−1)}`? — no: the displayed total is `2¹⁶ = 65,536`, a per-centre ENTRY locus, `(q−1)q^{4N−5h−3} = 1·2^{44−25−3} = 2^{16}` ✓ **exact**. `UND = q^{N+h−1} = 2^{15} = 32,768` ✓, and `RAM(21) = 32,768` = the remainder ✓ — **half each** ✓. The ladder `{2h+1,…,N−1} = {11,…,10}` is EMPTY at `N = 11 = 2h+1` ✓.
* `(Zp,7,5,k1)`: total `((q²−q)/2)q^{4N−10k−4} = 21·7^{20−10−4} = 21·7⁶ = 21·117,649 = 2,470,629` ✓. `UND = 21·q^{N+2k−2} = 21·7⁵ = 21·16,807 = 352,947` ✓. `RAM(5) = 2,470,629 − 352,947 = 2,117,682` ✓ **exact** (and independently `21·6·7⁵` at `.08`) ✓.
* `(Fqt,3,5,h1)`: `(q−1)q^{4N−5h−3} = 2·3^{20−5−3} = 2·3^{12} = 2·531,441 = 1,062,882` ✓.
* `(Fqt,5,4,h1)`: `4·5^{16−5−3} = 4·5^8 = 4·390,625 = 1,562,500` ✓.
* `(Zp,7,3,h1)`: `6·7^{12−5−3} = 6·7^4 = 6·2401 = 14,406` ✓. `RAM(5) = (q−1)²q³ = 36·343 = 12,348` ✓; `UND = (q−1)q³ = 6·343 = 2,058` ✓; `12,348 + 2,058 = 14,406` ✓ **exact partition**.
* `pre2 (Zp,2,11,(1,2))`: `2²⁰` members ✓ (the floored box `v(B_j) ≥ 9,7,5,3` frees `2+4+6+8 = 20` digits ✓, per R5). The four law keys sum to `32,768 + 32,768 + 65,536 + 524,288 = 655,360`, and `2²⁰ = 1,048,576`; the remainder `393,216 = 2^{17} + 2^{18}` ✓ = R5's two non-law strata ✓ **exact**.
* `GH-FEVEN (Zp,3,7,k1,f0=5)`: `3·3^{12} = 1,594,323` ✓ (= `3^{13}`) ✓.
* **F₉ censuses:** SPLITEQ `(Q−1)(Q−2)/2 = 8·7/2 = 28` ✓; INERT `Q(Q−1)/2 = 9·8/2 = 36` ✓; refine letters `Q−1 = 8` ✓ — **28/36/8 exactly as preregistered.**
**Every one of the eleven preregistered spot values re-derives from the displayed laws.**

**RESOLUTION TRACE:** statement lines 1055–1085. correction sites: 1803–1839 (ANNEX R's R5, shard 2).
**TEETH:** this unit IS the prediction set; `.69` is its scoring.

---

### EFF.GENH4.63  [preregistration]

**CANONICAL STATEMENT:** FORM: bulleted display (§S12's falsifiers). verbatim, lines 1086–1092.

> “* Falsifiers: a GH-JSONTIE mismatch with the committed table refutes
>   THEOREM GENH4.A as stated (diagnose the slot strings first); a
>   GH-REFINE pointwise failure refutes LEMMA GENH4-4 (the carry
>   computation — OB-b reopens); a GH-UND mismatch refutes GENH4.B; a
>   PARI σ mismatch refutes GENH4.C (OB-c reopens); a ν₄/β₄ or Σ ≠ 1
>   failure refutes the S9 assembly (P(4)'s density display, not the
>   stage laws); a dead tooth voids the battery, not the theorems.”

**CONDITIONALITY:** **Six falsifiers with explicit localization**, including two that name which obstruction REOPENS. **The last clause — “a dead tooth voids the battery, not the theorems” — is what licenses §S13.1's RED verdict to be a row defect rather than a refutation** (`.67`), and the note invokes it by name there (“per P-11's own falsifier grammar”).

**COMPILER NOTE:** §S13.1 cites “**P-11**'s own falsifier grammar”, but this note's preregistration runs **P-1…P-9** and the falsifiers are an unnumbered bullet. **`P-11` does not exist in GENH4** — it is GENIND's numbering (whose falsifier bullet IS P-11). Recorded as source defect 1 (§8): a cross-note numbering slip in the RED verdict's own justification. **The invoked clause exists here verbatim; only its label is wrong.**

**RESOLUTION TRACE:** statement lines 1086–1092. correction sites: none.
**TEETH:** none fired.

---

### EFF.GENH4.64  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S12's closing verdict placeholder). verbatim, lines 1094–1096.

> “**VERDICT: PENDING — commit 1 seals this note + the runner; commit 2
> appends §S13 from `genh4_checks_output.txt` / `genh4_checks_results
> .json`.**”

**CONDITIONALITY:** **SUPERSEDED, and by more than it scheduled: §S13 is appended over commits 2–3, not commit 2, because run 1 was RED.**
**SUPERSESSION KIND:** `replacement` (the placeholder by the verdicts), with the schedule itself corrected.
**CHAIN:** `VERDICT: PENDING` (commit 1, seal `121d9ab`) → §S13.1 RED (commit 2, `3eb1667`) → §S13.2 GREEN (commit 3, `4b5c085`) — **TERMINAL.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1094–1096. correction sites: 1098 (§S13's heading “commits 2–3”).
**TEETH:** the two-commit protocol. **PIN VERIFICATION:** `121d9ab` ✓, `3eb1667` ✓, `4b5c085` ✓.

---

### EFF.GENH4.65  [run-record]

**CANONICAL STATEMENT:** FORM: §-headed paragraph (§S13.1 — run 1, RED, with the defect diagnosed). verbatim, lines 1100–1137.

> “### S13.1 Run 1 (the sealed runner, single fresh run): RED — ONE
> violation, INSTRUMENT-SIDE, diagnosed exactly
>
> **RED, 1,102.2 s, exactly ONE violation in 245,694 checks** — and it
> is a defect of THIS battery's fresh-row GENERATOR, not of any law:
> the GH-FEVEN constructed row enumerated β₁ at floor f0−k = 4 instead
> of f0−k+1 = 5 (a v₁-floor needs BOTH components of the pair-slot
> above the same v₁-height), so the built locus was the asymmetric box
> {v(β₁) ≥ 4, v(β₀) ≥ 6} (3^{14} members — 3× the SEALED P-3
> prediction 1,594,323, which was computed from the correct floor and
> was right) rather than {v₁(A₀) > 5}. Quantitative closure of the
> diagnosis (from the committed run-1 artifacts): the single
> mismatching key is F-RAM(5), obs = 3,188,646 = 3ψ·(q−1)·q³·q⁹
> [r1 2026-08-08, notation (PE1 Remark 2): "3ψ" = the 3 CHOICES of ψ
> (the F₉ irreducible-quadratic census (q²−q)/2 = 3 at q = 3) — a
> count multiplicity, not a factor named ψ; i.e. obs = 3·(q−1)·q¹²] —
> EXACTLY the β₁-component-only attainment of value 5 that the
> mis-floored box admits ((q−1) = the freed β₁ digit at position 4;
> q³ = the A₀ slots above 5; q⁹ = the A₁ slots with 2s > 5) — and ALL
> EIGHT other keys of the row match the sealed f0 = 5 law exactly
> (they also match the f0 = 4 law: dv0 ≥ 6 keys are floor-insensitive
> there, closing the consistency check). Everything else in the
> battery: **ZERO violations** — GH-PIN 6/0, GH-JSONTIE 481/0 (all 23
> committed rows), GH-FRESH 54/0 (every never-measured spot at its
> preregistered value incl. the (2,11,h5) two-key half-drained
> stratum, the q = 7 rows, k = 2), GH-PRE2 5/0 (the (q−1)² depth-2
> law), GH-REFINE 192,000/0 (21,504 + 768 refine events, the carry
> formulas pointwise, walker ≡ pinned reader on every member),
> GH-PD 46,590/0 (liveness scan + AS-degeneration + both cascade rows:
> char-2 all-even-H₂ leaves = RAM/UND only; q = 3 realizes
> SPLITEQ/INERT at all-even H₂ — the separator), GH-UND 92/0,
> GH-BRACKET 157/0, GH-DENS 115/0 (partition of unity, ν₄ ≡ β₄,
> μ_E/μ_F identities, Σ_τ R_τ = 1 symbolic + anchors, all sandwiches),
> GH-SIGMA 6,185/0 (PARI, incl. 4,130 q = 7 F-RAM members). Teeth:
> LAT 19, CEN 14, ALPH 4, SIG 2, DENS 1 — all fired. Artifacts of run
> 1 committed at commit 2; per P-11's own falsifier grammar a
> generator defect voids the ROW, not the theorems — but the battery
> verdict is honestly RED as run.”

**CONDITIONALITY:** **A RED verdict published, diagnosed, and kept.** The defect is instrument-side (a fresh-row generator's floor), the diagnosis is closed quantitatively against the committed artifacts, and **the note refuses to reclassify the verdict**: “the battery verdict is honestly RED as run.”

**ARITHMETIC AUDIT (compiler-computed, on the diagnosis):** the mis-floored box `{v(β₁) ≥ 4, v(β₀) ≥ 6}` at `(q,N,k) = (3,7,1)` has `(N−4) + (N−6) = 3 + 1`… **recomputed properly**: free digits are `(N − 4) = 3` for β₁ and `(N − 6) = 1` for β₀ — that gives `3^4`, not `3^{14}`. The note says `3^{14}` members and “3× the SEALED P-3 prediction 1,594,323 = 3^{13}` ✓ — `3^{14} = 3·3^{13}` ✓ **internally consistent**, and the correct locus `{v₁(A₀) > 5}` has `3^{13}` ✓. **So the factor-3 overcount is exactly one freed digit** ✓, matching “(q−1) = the freed β₁ digit at position 4” — **compiler note: a freed digit contributes a factor `q = 3`, and the note attributes the excess to `(q−1) = 2` in the key formula while the locus grows by `q = 3`; both are consistent because the excess key `F-RAM(5)` collects the `q−1` nonzero values of the freed digit and the zero value stays in the correct-floor keys** ✓. Check: `obs = 3·(q−1)·q^{12} = 3·2·531,441 = 3,188,646` ✓ **exact**. And `3ψ = (q²−q)/2 = 3` at `q = 3` ✓.
**Total check count:** 245,694 = the sum of the eleven family scores plus the one violation? `6+481+54+5+192,000+46,590+92+157+115+6,185 = 245,685`, plus GH-FEVEN's 8 matching keys + 1 violation = 245,694 ✓ **exact** — **the totals reconcile.**

**DERIVATION:** Not a mathematical unit; an executed run with a diagnosis.
**RESOLUTION TRACE:** statement lines 1100–1137. correction sites: `[r1]` in situ (the “3ψ” notation clarification); 1139–1142 (`.66`).
**TEETH:** all five fired; the RED is a generator defect, not a tooth failure. **PIN VERIFICATION:** `genh4_checks_output_run1.txt` ✓ and `genh4_checks_results_run1.json` ✓ EXIST — **the RED run's artifacts are committed, as promised.**

---

### EFF.GENH4.66  [changes-record]

**CANONICAL STATEMENT:** FORM: bold display (§S13.1's repair line). verbatim, lines 1139–1142.

> “**Repair (commit 2, one line + this section):** the β₁ floor
> corrected to f0−k+1 in `run_feven` (comment marks the site); no law
> code, no note statement, no other row touched. Commit 3 = the full
> fresh re-run's verdict below.”

**CONDITIONALITY:** **A one-line instrument repair with an explicit scope claim** — no law code, no note statement, no other row. **Consequence for freeze predicate 4: the pinned runner md5 `ee8024b7…` is the REPAIRED text, “one line from the seal”** (`.69`), so the instrument freeze is on a post-repair runner and the note says so.
**SUPERSESSION KIND:** `replacement` (one line of the generator).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1139–1142. correction sites: none.
**TEETH:** the re-run (`.69`) is the check.

---

### EFF.GENH4.67  [run-record]

**CANONICAL STATEMENT:** FORM: §-headed paragraph (§S13.2 — run 2, GREEN). verbatim, lines 1144–1157.

> “### S13.2 Run 2 (repaired runner, full fresh run): GREEN
>
> **GREEN. 947.5 s, exit 0, single fresh run, ZERO violations in every
> family, all five teeth fired.** GH-PIN 6/0 · GH-JSONTIE 481/0 ·
> GH-FRESH 54/0 · GH-PRE2 5/0 · GH-REFINE 192,000/0 · GH-FEVEN 8/0
> (the repaired row: 1,594,323 members = EXACTLY the sealed P-3
> prediction, 8 keys, F₉ censuses live at odd q) · GH-PD 46,590/0 ·
> GH-UND 92/0 · GH-BRACKET 157/0 · GH-DENS 115/0 · GH-SIGMA 6,185/0.
> Teeth: LAT 19 · CEN 14 · ALPH 4 · SIG 2 · DENS 1. Artifacts:
> `genh4_checks_output.txt` (md5 9e6ca9b3b83aa9902ddef379f72db741),
> `genh4_checks_results.json` (md5 cbcff562132f82e302d95a017318075c);
> runner md5 ee8024b7a500220a6408dab373d7432f = commit-2's repaired
> text (one line from the seal). All non-FEVEN results byte-agree with
> run 1's committed artifacts (same counts every family; timing only).”

**CONDITIONALITY:** **GREEN, with the repaired row hitting the sealed prediction exactly** — “1,594,323 members = EXACTLY the sealed P-3 prediction”, i.e. **the preregistration was right and the generator was wrong**, which is the strongest possible vindication of the two-commit protocol.

**ARITHMETIC AUDIT:** the eleven family scores sum to `6+481+54+5+192,000+8+46,590+92+157+115+6,185 = 245,693` ✓ — and PE2's isolated re-run reports exactly “GREEN, 245,693/0” (`.70`) ✓ **exact match.** Against run 1's 245,694 (which included the one violation) ✓ — the difference of 1 is the violation ✓. **The two runs' totals reconcile to the digit.**
**PIN VERIFICATION:** `genh4_checks_output.txt` ✓, `genh4_checks_results.json` ✓ EXIST. The runner md5 `ee8024b7…` is the value GENIND's ANNEX R — r1 leg also pins when importing this battery read-only (GENIND shard 3 `.38`) ✓ — **cross-note pin agreement.**

**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1144–1157. correction sites: none.
**TEETH:** all eleven families and all five teeth.

---

### EFF.GENH4.68  [changes-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph + the three landed arc appends (§S13.2's consequence and the `[r1]`/`[r2]`/`[r3]` records). verbatim, lines 1159–1207. *(The three arc brackets are quoted in full; they are the note's own repair chronology and the source of `.01`'s CHAIN.)*

> “**Consequence for the grade box.** THEOREMS GENH4.A/B/C and LEMMAS
> GENH4-1F/-2/-CAP/-3/-4/-6 stand as composed, machine-corroborated:
> Q22-L1/L2/L3 PROVED at both genres, OB-a/OB-b/OB-c/OB-d closed, P-D
> settled unreachable at n = 4. **[GENIND-H(4)] is DISCHARGED**;
> THEOREM GENIND.B fires P(4); COROLLARY GENH4.D's eleven quartic
> densities stand with the triple tie (Σ_τ R_τ = 1 symbolic; ν₄ ≡ β₄;
> finite-window sandwiches on 9 full-sweep rows), conditional exactly
> on the S11 arc-grade stack. n = 5's embedded CS genres remain OPEN
> (GENH4-BOX-2). Attempt 0/2; the hostile arc has not begun. [r1
> 2026-08-08: the arc has now begun — PE1 NOT CLEAN 0C+0G+1m (263a36f;
> the minor = the S10-BOX-1 stale HMENU3 cell, repaired at this r1; the
> two remarks addressed at S11/S13.1); arc: composed → seal 121d9ab →
> RED 3eb1667 → GREEN 4b5c085 → PE1 263a36f → r1 (this, note-only);
> counter 0/2; PE2 next.] [r2 2026-08-08: PE2 NOT CLEAN 1C+2G+2m
> (2618e9b). The CRITICAL — S1's census clause at genre-F boundary-band
> pins — is DISPLAY-level: the runner and every frozen number were
> correct (PE2's isolated full re-run: GREEN, 245,693/0, results-JSON
> leaf-diff vs committed = the elapsed-time leaf only). r2 = this
> repair, note-only plus ONE additive machine leg: … Arc: … → PE1 263a36f → r1 dff23f8 → PE2
> 2618e9b → r2 (this). Counter 0/2; PE3 next.] [r3 2026-08-09: PE3
> NOT CLEAN 0C+0G+1m +2 remarks (a011533/3b88321) — every r2 repair
> verified in SUBSTANCE (census concordant at all four sites, no
> silent Q−1 consumer; trichotomy CONTENT right; W-12.D re-pin sound;
> supp leg non-tautological; two fresh-territory instruments:
> equal-characteristic walkers at (Fqt,2,8,1)/(Fqt,5,5,1) key-for-key
> with the committed Zp rows, and mechanism-free wild-prime σ-density
> at p = 2, 3). The MINOR: the r2 trichotomy DISPLAY's antecedents
> overlapped — the RAM clause dropped its one-side condition u ≤ 2w,
> transcribed from the PE2 verifier's own sentence (lesson ledgered:
> re-derive, never transcribe a verifier's phrasing). r3 = this
> repair, note-only, three items: … Sealed runner +
> artifacts byte-untouched; no frozen number moves. Arc: … → PE2
> 2618e9b → r2 fd35416/5279a11 → PE3 a011533/3b88321 → r3 (this).
> Counter 0/2; PE4 attempts the clean count.]”

**CONDITIONALITY:** **“Attempt 0/2; the hostile arc has not begun” is superseded three times in place and then by the acceptance** (`.01`). **The r3 record contains the corpus's most transferable lesson, ledgered: “re-derive, never transcribe a verifier's phrasing.”** PE3's substance verification of every r2 repair — including “supp leg non-tautological” — is the check that the `.38` repair actually repaired something.

**SUPERSESSION KIND:** three successive `counter re-reading`s + the acceptance's fourth (shard 2).
**ARITHMETIC AUDIT:** PE2's isolated re-run “GREEN, 245,693/0” ✓ matches `.67`'s total exactly ✓ — **an independent reproduction of the sealed battery by a hostile verifier.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1159–1207. correction sites: 1450–1463, 1850–1868, 2105–2127 (the three dated BOX-1 appends, shard 2).
**TEETH:** `in-house hostile pass` ×5 (PE1–PE5), two of them CLEAN.
**PIN VERIFICATION:** `263a36f` ✓, `121d9ab` ✓, `3eb1667` ✓, `4b5c085` ✓, `dff23f8` ✓, `2618e9b` ✓, `a011533` ✓, `3b88321` ✓, `fd35416` ✓, `5279a11` ✓ — **10/10.**

---

### EFF.GENH4.69  [changes-record] · **SERIES GENH4-BOX-1, entry 1 of 3 (post-acceptance)**

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX PE5's provenance and scope). verbatim, lines 1209–1225.

> “## ANNEX PE5 (2026-08-09, post-acceptance) — the two display MINORs and the S9.2 remark: the genre-F SPLTAIL cap 2w < N with its σ-inequality (MINOR 1), the per-genre norm valuation at S7's 2SIDED bullet (MINOR 2), and the closure of the dangling "− extra…" token (REMARK). The frozen accepted body above is NOT edited.
>
> **Provenance and scope.** GENH4 was **ACCEPTED 2/2** at PE5 (report
> `GENH4_passPE5_report.md`, commit 11dbd23): 0 CRITICAL, 0 GAP, 2 MINOR
> (+1 remark) — the second stage-one note through the hostile-arc bar,
> after HE7. The accepted text is byte-frozen at r3 (4b0d946 = HEAD, md5
> `09af7f78c34a779ea092738164f1795c`); per the report's grade line the
> owed repair is this dated annex (the HE7 ANNEX F-1 pattern: appended,
> dated, nothing above edited). It covers exactly PE5 MINOR 1 + MINOR 2
> plus the S9.2 remark and NOTHING else. Honesty of grade: the annex
> text itself is a post-acceptance append and has NOT been through a
> hostile pass; what it displays is content every pass verified in
> substance (PE2 ruled the SPLTAIL/UND boundary right in note and
> runner; PE5 re-derived both items and the closure), verified here
> against the committed artifacts plus one additive machine leg
> (`genh4annex_supp.py`, GREEN, record below). No statement, frozen
> number, or conclusion moves.”

**CONDITIONALITY:** **The acceptance record; and the annex's own grade is disclosed as ungraded.** “ACCEPTED 2/2 … the second stage-one note through the hostile-arc bar, after HE7” supersedes shard 1 `.01`'s and `.68`'s grade lines. **The scope claim “covers exactly PE5 MINOR 1 + MINOR 2 plus the S9.2 remark and NOTHING else” is checkable and checks** (§6.1 item 1).

**SUPERSESSION KIND:** `counter re-reading` (the clean counter 1/2 → 2/2) + `license` (the append-only protocol begins).

**SERIES:** GENH4-BOX-1 entry **1 of 3**; the full arc is `.80`'s dated append.

**DERIVATION:** Not a mathematical unit. **PIN VERIFICATION:** `11dbd23` ✓, `4b0d946` ✓; `verification/openmath/genh4annex_supp.py` ✓, `_output.txt` ✓, `_results.json` ✓ EXIST; `lean/notes/openmath/GENH4_passPE5_report.md` — **verified to EXIST ✓.**

**RESOLUTION TRACE:** statement lines 1209–1225. correction sites: 1850–1868 (the ratification's annotation of this acceptance, `.94`).

**TEETH:** `in-house hostile pass` ×2 CLEAN (PE4, PE5) + the additive leg (`.79`).

---

### EFF.GENH4.70  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (A1's defect statement — a self-finding against the frozen body). verbatim, lines 1227–1239.

> “### A1. MINOR 1 — the genre-F SPLTAIL cap is 2w < N, not w < N
>
> **The defect (as found at PE5).** The true and implemented genre-F
> SPLTAIL cap is **2w < N** (w = dv(A₁) in v₁ = v units; sealed runner
> `law_F`: `if 2 * dv1 < N`; sealed fresh-row reader:
> `if dv1 is not None and 2 * dv1 < N`) — but it is DISPLAYED nowhere:
> the two display sentences below read naturally as w < N at genre F,
> which is refuted by the committed rows. Additionally, S7's SPLTAIL
> bullet displays the σ-decision inequality for genre E only; the F
> instance is derived here (ANNEX-LEMMA GENH4-7(b)) — it is the
> one-line step on which the F-SPLTAIL σ-label {(1,2),(1,2)} rests,
> a committed key class consumed by W-12.D's σ-labelling clause at
> n = 4.”

**CONDITIONALITY:** **The same defect species as shard 1's CRITICAL: the runner had it right and the display did not.** Two distinct sub-defects: an undisplayed cap and an underived σ-inequality — **and the second is on a clause W-12.D consumes**, which is why the Codex ratification later graded the residue a GAP.

**DERIVATION:** Not a mathematical unit; a defect report with source-code witnesses.

**RESOLUTION TRACE:** statement lines 1227–1239. correction sites: 1500–1625 (R1, which finds this annex's own repair insufficient).

**TEETH:** the sealed runner's two quoted conditionals are the witnesses; the committed rows refute the misread cap (`.73`).

---

### EFF.GENH4.71  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed numbered display (A1's three named rider targets). verbatim, lines 1241–1264.

> “**The three display sentences this annex riders (named exactly;
> none is edited).**
>
> 1. **LEMMA GENH4-3 (S4):** "plus the conservative exits (A₀ hidden:
>    SPLTAIL if **w < N-cap** else UND; …)". **Read as:** the "N-cap"
>    is the genre's hidden-A₀ lift-stability floor u_floor measured
>    against 2w — SPLTAIL iff **2w < u_floor**, with u_floor = 2N
>    (genre E, dv-units: GENH4-CAP(E)'s undercut floor) and u_floor = N
>    (genre F, v₁-units: GENH4-CAP(F)'s window floor). At E this is
>    w < N as S6.1 displays; at F it is **2w < N** — NOT w < N.
> 2. **S6.1's leaf row + gloss:** "SPLTAIL(w), w < N:
>    (q−1)·q^{(h−1)/2 + #A₁ > w}" with "genre F identically with
>    comp-weighted exponents AND comp-weighted pin censuses". **Read
>    as:** "identically" transfers the LAW SHAPE (pin census ×
>    free-slot power × band factor); the w-RANGE transfers by the
>    uniform rule of rider 1, i.e. genre F: 2w < N, with the UND
>    complement freeing A₁ exactly at the slots 2s ≥ N.
> 3. **S7's SPLTAIL bullet:** "A₀ window-zero, w < cap: EVERY lift has
>    u_lift ≥ 2N > 2w (E; GENH4-CAP's undercut floor) — a 2SIDED
>    configuration for every lift, including the A₀ = 0 corner …: σ as
>    2SIDED. ∎". **Read as:** at genre F the displayed inequality's
>    instance is **u_lift ≥ N > 2w** (ANNEX-LEMMA GENH4-7(b) below);
>    the rest of the bullet (the 2SIDED reduction, the A₀ = 0 corner
>    via F = φ·(φ + A₁)) applies verbatim.”

**CONDITIONALITY:** **A uniform rule (`2w < u_floor`) supplied for a per-genre constant that the body displayed only in its E instance.** All three riders preserve the displays byte-intact.

**SUPERSESSION KIND:** `wording-rider` ×3 (“Read as …”), each naming its target exactly. **TARGETS:** shard 1 `.21`, `.25`, `.30`.

**ARITHMETIC AUDIT:** the uniform rule `SPLTAIL iff 2w < u_floor` with `u_floor = 2N` (E) gives `w < N` ✓ = the displayed E range; with `u_floor = N` (F) gives `2w < N` ✓ = the implemented F range ✓ — **one rule, two instances, both matching the runner.**

**DERIVATION:** The floors are GENH4-CAP(E)/(F) (shard 1 `.18`).

**RESOLUTION TRACE:** statement lines 1241–1264. correction sites: none.

**TEETH:** `.73`'s committed refutation of the wrong reading.

---

### EFF.GENH4.72  [lemma]

**CANONICAL STATEMENT:** FORM: prose derivation + display (blockquote, ANNEX-LEMMA GENH4-7) + proof. verbatim, lines 1266–1314.

> “**In-note derivation of the cap (why 2w < N was always recoverable).**
> S6.3's genre-F UND law carries the complement explicitly: "main
> factor q^{Σ comp(s): s ∈ A₁, **2s ≥ N**}" — UND frees A₁ exactly at
> the slots with 2s ≥ N, so the SPLTAIL range is its complement
> 2w < N; THEOREM GENH4.B's committed verification box ((2,8,1) F →
> 1024 = 512 + 512) prices exactly this partition. The reason the cap
> is 2w < N and nothing else:
>
> > **ANNEX-LEMMA GENH4-7 (the genre-F SPLTAIL cap and σ-inequality).**
> > At a genre-F stage state with A₀ hidden (every in-window A₀ digit
> > zero: a₀-positions ≤ N−1 and a₁-positions ≤ N−1 all vanish) and
> > pin dv(A₁) = w:
> > (a) every lift has u_lift := v₁(A₀^lift) ≥ N, and u_lift = N is
> > realizable (the a₀-component digit at position N, the first
> > out-of-window position; for k ≥ 2 also the free boundary-band
> > a₁ digits);
> > (b) if 2w < N then EVERY disc ≠ 0 lift has u_lift ≥ N > 2w, hence
> > sits in GENH4-3(ii)'s 2SIDED(w, u_lift − w) position — including
> > the A₀ = 0 corner via F = φ·(φ + A₁) — and by S7's 2SIDED bullet
> > (F leg) has σ = {(1,2),(1,2)}: the S1 dictionary's F-SPLTAIL label,
> > (A0)-strong;
> > (c) if 2w ≥ N, NO single label is lift-sound: the u_lift = N lift
> > of (a) has u_lift ≤ 2w and lands in the r3 trichotomy's decided
> > legs (odd N → RAM(N): σ = {(2,2)}) or the out-of-window residual
> > read (even N), while any lift with u_lift > 2w is 2SIDED:
> > σ = {(1,2),(1,2)} — two lifts of the SAME state with DIFFERENT σ.
> > Hence 2w < N is the UNIQUE lift-sound cap, and the reader's UND
> > exit at 2w ≥ N is forced, not conservative slack.
>
> *Proof.* (a) A₀ = a₁x + a₀ has v₁(A₀) = min(v(a₀), v(a₁) + k) with
> the ψ-genericity of GENH4-2 preventing cancellation (S2.1's ring
> invariants, maintained along chains by S5). Hidden means every
> in-window position vanishes: v(a₀) ≥ N (a₀-positions ≤ N−1) and
> v(a₁) + k ≥ N + 1 (a₁-positions ≤ N−1); lift digits at the
> out-of-window positions are free, so u_lift ≥ N with equality
> realizable through a₀ at position N (and, for k ≥ 2, through the
> free band digits the deep₀ factor prices). (b) u_lift ≥ N > 2w is
> GENH4-3(ii)'s antecedent u > 2w at every lift; all data consumed are
> lift-stable (GENH4-CAP(F)), so S7's 2SIDED bullet applies to every
> lift; at A₀ = 0 both factors of φ·(φ + A₁) carry the S2.1 one-side
> polygon — the bullet's own corner sentence. (c) The two lifts are
> exhibited: u_lift = N ≤ 2w falls to GENH4-CAP(F)'s r3 trichotomy —
> at odd N the RAM(N) leg (σ = {(2,2)} by S7's F-RAM bullet), at even
> N the dv0 = N residual read that GENH4-CAP(F) rules out of window
> (different deep lifts realize different residual classes, hence
> different σ); a lift with u_lift > 2w — realizable, the
> out-of-window digits are free — is 2SIDED. {(2,2)} ≠
> {(1,2),(1,2)} and the even-N residual σ's vary, so no constant label
> covers all lifts. ∎”

**CONDITIONALITY:** **SUPERSEDED IN ITS HYPOTHESIS by GENH4-7′** (`.84`) and **IN ITS CLAUSE (c) by (c′)** (`.99`). The Codex ratification found the two bold clauses of the hypothesis contradictory (“a₁-positions ≤ N−1 all vanishing gives v(a₁) ≥ N … the floor v(a₁) + k ≥ N + 1 is the strictly weaker condition”), and **the weaker condition is the counted leaf** — so GENH4-7 proves the σ-label “only for the band-zero SLICE of the leaf — a strict subfamily, exactly HALF the leaf at the first live cell”. Then annex pass #1 machine-refuted clause (c)'s witnesses at band-pinned strata.

**SUPERSESSION KIND:** received `replacement` at the hypothesis (R1) and at clause (c) (R2.G1) + `inventory completion` at clause (a) (the band-nonzero cap `u_lift ≤ m`) + `scope-pin` at (a)'s realizability (R2.M1). **Four kinds on one lemma; the header's own inventory of them was itself under-counted and is corrected at R2.M4** (`.104`).

**CHAIN:** GENH4-7 → **GENH4-7′** (hypothesis widened to the counted family; (a) gains the band cap) → **(c′)** (clause (c) re-proved at key level, band-zero witnessed) → R2.M1 (realizability scoped to `N ≥ 4k+1`) → post-pass-2 MINOR-2 ((c′)(i)'s disc parenthetical corrected for equal characteristic 2) — **TERMINAL: GENH4-7′(a)-with-cap, (b) unchanged, (c′) as corrected.**

**ARITHMETIC AUDIT:** the in-note recoverability argument checks — S6.3's UND main factor frees A₁ at slots with `2s ≥ N` ✓ (shard 1 `.27`), so the SPLTAIL complement is `2w < N` ✓; and the `(2,8,1)` F verification `1024 = 512 + 512` ✓ (shard 1 `.10`) prices exactly that partition ✓. **Clause (b)'s inequality chain `u_lift ≥ N > 2w`** requires `2w < N` ✓ — the cap ✓.

**DERIVATION:** Displayed.

**RESOLUTION TRACE:** statement lines 1266–1314. correction sites: 1500–1625 (R1), 1909–2011 (R2.G1), 2013–2031 (R2.M1), 2079–2088 (R2.M4), 2159–2167 (post-pass-2 MINOR-2).

**TEETH:** `.73` (committed refutation of the wrong cap) + `.74` (21/21 PARI lifts + the `2w ≥ N` two-lift tooth) — **both annex-resident.**

---

### EFF.GENH4.73  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A1's committed refutation of the wrong reading). verbatim, lines 1316–1331.

> “**The committed refutation of the wrong reading (machine, C1–C3 of
> the annex leg).** At the committed (Zp,2,8,k1) row (qscout22 row 16,
> artifact md5 6c2441a1…, pin-verified): the misread cap w < N
> predicts SPLTAIL(4) = 384, SPLTAIL(5) = 96, SPLTAIL(6) = 24,
> SPLTAIL(7) = 6 and UND = 514 — against the committed
> **SPLTAIL(3)-only = 1,536 and UND = 1,024** (the wrong cap
> redistributes the committed UND: 514 + 510 = 1,024). Same at
> (Zp,2,7,k1) (row 15: wrong SPLTAIL(4..6) = 96/24/6, UND = 2 vs
> committed 128) and at the equal-characteristic (Fqt,2,7,k1) (row 19
> ≡ row 15). The annex leg re-derived the full law fresh from
> S6.1/S6.3 (tie: key-for-key on all three rows) and found the wrong
> cap ALSO corrupts the refined (3,)-histories (row 16 @(3,):
> SPLTAIL(4..7) = 1,152/288/72/18, UND 3,072 → 1,542 — hand-derived,
> then machine-confirmed; disclosed as a widening of the sealed
> prereg's mismatch scope). Every mismatching key is a SPLTAIL/UND
> key; NO decided RAM/2SIDED/SPLITEQ/INERT count moves.”

**ARITHMETIC AUDIT (compiler-computed):** the wrong-cap redistribution at row 16: `384 + 96 + 24 + 6 = 510` ✓, and `514 + 510 = 1,024` ✓ = the committed UND ✓ — **mass conserved exactly**, which is what makes the misread cap a *redistribution* rather than a miscount. Row 15: wrong `96 + 24 + 6 = 126` and `2 + 126 = 128` ✓ = the committed UND ✓. Refined history: `1,152 + 288 + 72 + 18 = 1,530` and `1,542 + 1,530 = 3,072` ✓ = the committed UND ✓. **All three closures exact.**

**CONDITIONALITY:** **A disclosed widening of the sealed preregistration's mismatch scope**, hand-derived first and then machine-confirmed — the honest order.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1316–1331. correction sites: none.

**TEETH:** `genh4annex_supp.py` C1–C3 (`.79`), against md5-pinned committed rows.

---

### EFF.GENH4.74  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A1's σ-labelling consequence and its machine contact). verbatim, lines 1333–1344.

> “**The σ-labelling consequence (what W-12.D consumes).** S7's proof
> of THEOREM GENH4.C is total at genre E and at five of the six F
> bullets as displayed; the F-SPLTAIL leg is ANNEX-LEMMA GENH4-7(b)
> above. With it, the committed F-SPLTAIL key class (SPLTAIL(3) =
> 384/1,536/384 at rows 15/16/19) carries the σ_F = {(1,2),(1,2)}
> label the S11 firing-table row supplies to W-12.D's σ-labelling
> clause at n = 4 — every disc ≠ 0 lift of every member, both ring
> types. Machine contact (annex leg C5, fresh): 21/21 constructed
> lifts of (Zp,2,7,k1) SPLTAIL(3) states (three A₁ shapes × seven
> lifts, A₀ = 0 corner included) scored σ = {(1,2),(1,2)} by PARI;
> the 2w ≥ N tooth fired (GENH4-7(c)'s two lifts exhibited: w = 4
> hidden state, u_lift = 7 → {(2,2)} vs u_lift = 9 → {(1,2),(1,2)}).”

**CONDITIONALITY:** **“five of the six F bullets as displayed” is the exact accounting of what the frozen body proves** — and the sixth is the one W-12.D consumes. **R1 then finds this supply covers only half the leaf** (`.83`) and widens it.

**ARITHMETIC AUDIT:** `3 A₁ shapes × 7 lifts = 21` ✓. The tooth's two lifts at `w = 4`: `u_lift = 7 ≤ 2w = 8` → odd → RAM(7) → `{(2,2)}` ✓; `u_lift = 9 > 8` → 2SIDED → `{(1,2),(1,2)}` ✓ — **the two-lift contrast is exactly clause (c)'s** ✓.

**DERIVATION:** Not a mathematical unit.

**RESOLUTION TRACE:** statement lines 1333–1344. correction sites: 1581–1592 (R1.1, which restores the supply over the true family).

**TEETH:** annex leg C5, PARI, 21/21 + a fired tooth.

---

### EFF.GENH4.75  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (A2 — the per-genre norm valuation). verbatim, lines 1346–1363.

> “### A2. MINOR 2 — the norm valuation at S7's 2SIDED bullet is per-genre: u in E's halved units, 2u in F's declared v-units
>
> **The display sentence this annex riders (named exactly; not
> edited).** S7's 2SIDED bullet: "The norm count: Π_θ φ(θ) =
> Res(F, φ) = Π_{η: φ(η)=0} F(η) = Nm_R(A₀), **of valuation u (both
> genres**, using GENH4-2 at the key's own roots η, which satisfy the
> same v/residue facts); if j roots sit at w/2: j·w/2 + (4−j)(u−w)/2 =
> u forces j = 2." **Read as:** the norm identity chain is exact as
> displayed (F ≡ A₀ mod φ, so F(η) = A₀(η) at the key's two roots η);
> the VALUATION tag "u (both genres)" is stated in E's halved units
> throughout. Per genre, in each genre's own declared units (S7
> declares "genre F: w, u in v₁ = v units"):
>
> * **Genre E:** v(A₀(η)) = u/2 at each of the two roots (GENH4-2,
>   dv-units halved) ⟹ v(Nm_R(A₀)) = u. The display is exact.
> * **Genre F:** v(A₀(η)) = u at each of the two roots (v₁ = v units)
>   ⟹ v(Nm_R(A₀)) = **2u** — the display's "u" is false at F in the
>   declared units, by exactly the factor 2.”

**CONDITIONALITY:** **SUPERSEDED by ANNEX R's R4**, which covers all three of S7's mixed-unit sentences at once: “this rider covers all three sentences at once and supersedes A2's partial one.” **A rider superseded by a wider rider — the only such case in the queue.**

**SUPERSESSION KIND:** `provenance-rider` (a units tag), itself later `replacement`-ed by R4.
**TARGETS:** shard 1 `.29`.
**ARITHMETIC AUDIT:** `Nm_R(A₀) = Π_η A₀(η)` over the key's two roots ✓, so `v(Nm) = 2·v(A₀(η))` ✓; at E that is `2·(u/2) = u` ✓ and at F `2·u = 2u` ✓ — **the factor-2 discrepancy is exactly the halving convention** ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1346–1363. correction sites: 1774–1801 (R4).
**TEETH:** `.77` (the committed instance).

---

### EFF.GENH4.76  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A2's self-consistency analysis and self-alarm). verbatim, lines 1365–1377.

> “**Why the displayed balance was self-consistent (no number moved).**
> The displayed equation j·w/2 + (4−j)(u−w)/2 = u is the consistently
> HALVED form: halved root-values (v(Y) ∈ {w/2, (u−w)/2}, the bullet's
> own list) balanced against the halved norm valuation u. In F's
> declared units the equation is j·w + (4−j)(u−w) = 2u — the same
> equation multiplied by 2 — and both give j(2w−u) = 2(2w−u), j = 2
> (u ≠ 2w). So j = 2, the Galois-invariance step, and the σ
> conclusion {(2,1),(2,1)}/{(1,2),(1,2)} are all unaffected: the
> defect is the prose tag, not the computation. Self-alarm: a reader
> mixing the units (unhalved values, unhalved-but-u norm) solves
> j·w + (4−j)(u−w) = u and gets j = (4w−3u)/(2w−u) = 9 at
> (w,u) = (3,7) — impossible for 4 roots, so the misreading announces
> itself rather than mislabeling silently.”

**CONDITIONALITY:** **A defect that cannot propagate silently, and the note proves it** — the self-alarm is a genuine structural property, not a reassurance.
**ARITHMETIC AUDIT:** both forms give `j(2w−u) = 2(2w−u)` ✓ ⟹ `j = 2` ✓. The mixed form at `(3,7)`: `(12−21)/(6−7) = (−9)/(−1) = 9` ✓ **exact** — impossible for a quartic ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1365–1377. correction sites: none.
**TEETH:** the self-alarm is itself a structural tooth.

---

### EFF.GENH4.77  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (A2's committed instance). verbatim, lines 1379–1388.

> “**The committed instance (machine, annex leg C4).** At the committed
> 2SIDED(3,4) of (Zp,2,7,k1) (row 15, count 384): w = 3, u = 7, and
> v(Res(F,φ)) = j·w + (4−j)(u−w) = 2·3 + 2·4 = **14 = 2u**. Exhibited
> on five explicit members over the key φ = x² + 2x + 4 (v(p₁) = 1 ≥
> k, v(p₀) = 2 = 2k exact, residue pair ψ = y² + y + 1 — S2.1's
> invariants): v₂(Res(F,φ)) = 14 on all five, by two independent
> routes (6×6 Sylvester determinant; reduction mod φ + the quadratic
> norm α²p₀ − αβp₁ + β²), and PARI scores σ = {(1,2),(1,2)} on every
> member. The balance display's j = 2 is machine-tied at the same
> members.”

**ARITHMETIC AUDIT:** `2·3 + 2·4 = 14` ✓ and `2u = 14` ✓. The key `φ = x² + 2x + 4` over `ℤ₂`: `v(p₁) = v(2) = 1 ≥ k = 1` ✓, `v(p₀) = v(4) = 2 = 2k` ✓, and the residual `ψ = y² + y + 1` is the unique irreducible quadratic over `F₂` ✓ — **all three S2.1 invariants check.** (This is the same key R3 uses for its non-maximality witness, `.89`.)
**CONDITIONALITY:** **Two independent computational routes plus PARI** — a strong tie for a prose-tag correction.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1379–1388. correction sites: none.
**TEETH:** annex leg C4, two routes + PARI, five members.

---

### EFF.GENH4.78  [table]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with a **fixed-width ASCII mass table** (A3 — the closure of the dangling token), emitted TWICE per rule 14. verbatim, lines 1390–1421.

> “### A3. REMARK — S9.2's dangling "− extra…" token: the 2SIDED mass is EXACTLY 1/(q²+q+1)
>
> **The display token (named exactly; not edited).** S9.2's μ_E
> bullet: "RAM-mass q²/(q²+q+1), SPLITEQ (q−2)/(2(q²+q+1)), INERT
> q/(2(q²+q+1)), **2SIDED 1/(q²+q+1) − extra…**, REFINE 1/(q²+q+1)".
> **Closure:** the token "− extra…" is an editing remnant; the extra
> is **0**. Write Φ₂ := q² + q + 1 and r := 1/q. The per-node masses
> on the full integer dv-ladder (u = dv(A₀), w = dv(A₁), digits
> uniform, self-similar node):
>
>     RAM     = Σ_{i≥1} (1−r)r^{2i−2}·r^{i−1} = (1−r)/(1−r³)   = q²/Φ₂
>     2SIDED  = Σ_{j≥1} (1−r)r^{j−1}·r^{2j}   = (1−r)r²/(1−r³) = 1/Φ₂
>     even-dμ = (1−r)r/(1−r³) = q/Φ₂, split by the K-census over the
>               q(q−1) unit pairs: SPLITEQ (q−2)/(2q) → (q−2)/(2Φ₂),
>               INERT 1/2 → q/(2Φ₂), REFINE 1/q → 1/Φ₂
>
> and the closure is coefficientwise over the common denominator 2Φ₂:
>
>     2q² + (q−2) + q + 2 + 2 = 2q² + 2q + 2 = 2Φ₂  ⟹  Σ = 1.
>
> Any positive "extra" subtracted from the 2SIDED mass would break
> the partition of unity — self-alarming (the annex leg's tooth:
> extra = r⁴ breaks Σ = 1 at every q). Downstream is untouched: the
> refine aggregation × Φ₂/(q² + q) gives exactly the displayed
> μ_E = ( {(4,1)}: q/(q+1); {(2,1),(2,1)}: 1/(2(q+1));
> {(2,2)}: 1/(2(q+1)) ) = ν₂'s fractions — machine-tied at GH-DENS in
> the sealed battery, re-derived from scratch by PE5's charge 2, and
> re-checked in the annex leg (C6: closed forms + aggregation exact at
> 7 points q, all numerator degrees < 7, so 7 points decide each
> identity). SPLTAIL and UND are window-boundary leaves (they vanish
> in the N → ∞ per-node limit) and correctly do not appear in the
> vector.”

`[TABLE]` — the per-node masses, transcribed:

| Event | Series | Closed form |
|---|---|---|
| RAM | `Σ_{i≥1} (1−r)r^{2i−2}·r^{i−1}` | `(1−r)/(1−r³) = q²/Φ₂` |
| 2SIDED | `Σ_{j≥1} (1−r)r^{j−1}·r^{2j}` | `(1−r)r²/(1−r³) = 1/Φ₂` |
| even-dμ (total) | — | `(1−r)r/(1−r³) = q/Φ₂` |
| → SPLITEQ | `(q−2)/(2q)` of even-dμ | `(q−2)/(2Φ₂)` |
| → INERT | `1/2` of even-dμ | `q/(2Φ₂)` |
| → REFINE | `1/q` of even-dμ | `1/Φ₂` |

**ARITHMETIC AUDIT (compiler-computed, every line):** with `r = 1/q`, `1 − r³ = (q³−1)/q³` and `1 − r = (q−1)/q`, so `(1−r)/(1−r³) = q²(q−1)/(q³−1) = q²/(q²+q+1) = q²/Φ₂` ✓ (since `q³−1 = (q−1)Φ₂`). `(1−r)r²/(1−r³) = q²/Φ₂ · r² = 1/Φ₂` ✓. `(1−r)r/(1−r³) = q²/Φ₂ · r = q/Φ₂` ✓. Splits: `(q/Φ₂)·(q−2)/(2q) = (q−2)/(2Φ₂)` ✓; `(q/Φ₂)·(1/2) = q/(2Φ₂)` ✓; `(q/Φ₂)·(1/q) = 1/Φ₂` ✓. Closure over `2Φ₂`: numerators `2q², (q−2), q, 2, 2` sum to `2q² + 2q + 2 = 2Φ₂` ✓ **⟹ Σ = 1, extra = 0** ✓. **Every displayed identity reproduces.** The C6 degree argument: all numerator degrees `< 7`, so agreement at 7 points decides ✓ (a polynomial of degree < 7 vanishing at 7 points is zero ✓).

**CONDITIONALITY:** **An editing remnant closed by derivation, with a tooth.** Downstream is untouched, and the μ_E aggregation is re-derived independently by PE5's charge 2 and by the annex leg.

**SUPERSESSION KIND:** `replacement` of a dangling token by 0.
**TARGETS:** shard 1 `.39`.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1390–1421. correction sites: none.
**TEETH:** annex leg C6 + the extra-token tooth, FIRED.

---

### EFF.GENH4.79  [run-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (A4 — the additive machine leg). verbatim, lines 1423–1448.

> “### A4. Machine record (additive leg; every sealed artifact byte-frozen)
>
> `verification/openmath/genh4annex_supp.py` — sealed with
> preregistered predictions P1–P6 at cceca77 (BEFORE the run), run
> fresh, repaired once with disclosure, re-run fresh: **GREEN, 0
> violations, 0.1 s + PARI** (`genh4annex_supp_output.txt` md5
> 713a0a3b…, `genh4annex_supp_results.json` md5 37d0650e…, committed
> e945734). C0: 5/5 md5 pins verified (sealed runner + both sealed
> GENH4 artifacts + qscout22 runner/results). C1 (P1): the committed
> rows 15/16/19 read exactly as this annex states. C2 (P2): a fresh
> typing of the S6.1/S6.3 genre-F recursion ties all three rows
> key-for-key. C3 (P3): the wrong-cap table equals PE5's
> failure-scenario numbers exactly, masses conserved, mismatch set =
> SPLTAIL/UND keys only. **Disclosed smoke catch:** the sealed prereg
> scoped C3's mismatch set to the empty history; the first run (RED,
> 2 instrument-side violations) caught the wrong cap propagating into
> the refined (3,)-history keys as well — values hand-derived before
> the one-line repair (row 16 @(3,): 1,152/288/72/18 + UND 1,542,
> closing to the committed 3,072; row 15 @(3,): 288/72/18 + UND 6,
> closing to 384), then machine-confirmed; the refutation of the
> misread cap is thereby STRENGTHENED, and no decided key moves under
> it. C4 (P4) and C5 (P5): as displayed in A2/A1 (five 2SIDED members
> two-route exact; 21/21 SPLTAIL lifts + the 2w ≥ N two-lift tooth
> FIRED). C6 (P6): the closure, the aggregation, and the extra-token
> tooth FIRED. σ-oracle: the same GP sig routine as the sealed
> battery's GH-SIGMA (nfinit/idealprimedec per p-adic factor).”

**CONDITIONALITY:** **A second published RED-then-repair cycle in this note** (after shard 1's `.65`) — this one at the annex leg, with the widened refutation disclosed as a STRENGTHENING.
**ARITHMETIC AUDIT:** row 15 @(3,): `288 + 72 + 18 = 378` and `378 + 6 = 384` ✓ **exact**; row 16 @(3,) audited at `.73` ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1423–1448. correction sites: 2152–2158 (the post-pass-2 MINOR-1 corrects a *different* leg's pin, not this one).
**TEETH:** P1–P6, GREEN after a disclosed repair; two teeth fired. **PIN VERIFICATION:** `cceca77` ✓, `e945734` ✓; the three leg files EXIST ✓.

---

### EFF.GENH4.80  [changes-record] · **SERIES GENH4-BOX-1, the acceptance entry**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (the dated GENH4-BOX-1 append recording the acceptance). verbatim, lines 1450–1463.

> “**GENH4-BOX-1 (arc record) — dated APPEND (2026-08-09).** This line
> continues the [r1]/[r2]/[r3] record of S10-BOX-1/S13; under the
> acceptance freeze it cannot be inserted there, so it lives here:
> **PE4 (e15308d) and PE5 (11dbd23, `GENH4_passPE5_report.md`) HAVE
> NOW RUN: PE4 CLEAN (1/2); PE5 CLEAN — 0 CRITICAL, 0 GAP, 2 MINOR
> (+1 remark), machine leg bit-identical GREEN (isolated re-run
> 245,693/0, leaf-diff = elapsed only) plus a fresh q = 9 route. The
> 2-clean count completed 1/2 → 2/2: GENH4 IS ACCEPTED — the second
> stage-one note through the hostile-arc bar. The text is frozen at
> r3 4b0d946; this dated annex discharges the owed MINOR 1 + MINOR 2
> riders and closes the S9.2 remark, edits nothing above, and moves
> no sealed number. Conditionality is unchanged: exactly the S11
> arc-grade stack (minimum grade 0/2 at verdict time: W-12, HEX3,
> GENIND live — PE5 charge 4).**”

**CONDITIONALITY:** **The acceptance, with its conditionality explicitly UNCHANGED: “minimum grade 0/2 at verdict time”.** So GENH4 is 2/2 and P(4) is conditional on a stack whose minimum is 0/2 — **the two grades must never be conflated**, and the note is careful.
**SUPERSESSION KIND:** `counter re-reading`, executed by append because the target is frozen.
**TARGETS:** shard 1 `.01`, `.44`, `.68`.
**ARITHMETIC AUDIT:** the isolated re-run `245,693/0` ✓ matches shard 1 `.67`'s run-2 total exactly ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1450–1463. correction sites: 1850–1868 (the ratification annotation).
**TEETH:** `in-house hostile pass` ×2 CLEAN + an independent bit-identical re-run + a fresh q = 9 route.
**PIN VERIFICATION:** `e15308d` ✓, `11dbd23` ✓, `4b0d946` ✓.

---

### EFF.GENH4.81  [fence] · **SERIES WHAT-DOES-NOT-MOVE, entry 1 of 3**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1465–1476.

> “**What does not move.** Every displayed statement, proof, and frozen
> number of the accepted body; the sealed runner and artifacts (md5
> pins re-verified, C0); the committed key tables (the annex leg reads
> them, never writes); THEOREM GENH4.A/B and the count laws (the cap
> was always 2w < N in every committed number and in S6.3's
> complement); THEOREM GENH4.C's dictionary and the W-12.D supply (the
> labels were always right — the annex ADDS the displayed F-inequality
> GENH4-7(b), it does not correct a label); the eleven densities, the
> triple tie, and the S11 conditionality stack; GENH4-BOX-2 (n = 5's
> embedded CS genres stay OPEN). The E-side displays (w < N at S6.1,
> u_lift ≥ 2N at S7) are exact as written — MINOR 1 is the genre-F
> transfer only.”

**CONDITIONALITY:** **An enumerated non-movement declaration — the annex layer's own scope check.** Its claim “the annex ADDS the displayed F-inequality …, it does not correct a label” is the sentence that keeps GENH4.C's dictionary intact through both later layers.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1465–1476. correction sites: none.
**TEETH:** NONE — a scope fence.

---
### EFF.GENH4.82  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R's provenance; the Codex ratification's CHALLENGE). verbatim, lines 1478–1498.

> “## ANNEX R (2026-08-09, post-ratification; CODEX F1-F5)
>
> **Provenance and scope.** The ratification sweep's Codex leg
> (`CODEX_GENH4RAT_2026-08-09.md`, session 019fe500-0ddc-7b52-9e32-c4dff01e560c,
> gpt-5.6-sol at HIGH, fresh context, read-only) returned **5 findings —
> RATIFICATION OUTCOME: CHALLENGE** at adjudication: F2 (CONFIRMED, GAP as
> stated with the CRITICAL flag disclosed both ways — the consumed-clause
> gap on ANNEX-LEMMA GENH4-7), F3 (CONFIRMED GAP, display/frame scope —
> the stage-ring "DVR" sentences), F4 (CONFIRMED GAP, scoped to
> GENH4-7(c), unconsumed), F5 (CONFIRMED, regraded MINOR — S7 units),
> F1 (REFUTED as CRITICAL against the committed artifact; CONFIRMED as
> MINOR display — "law keys" undefined). This annex executes the fold
> note's repair queue R1–R5 in order. The accepted body + ANNEX PE5
> above are BYTE-FROZEN — md5 `a584cb3e8985775ee6f1c9f09b7cf9e5`
> (89,530 bytes) verified identical before and after this append; the
> freeze boundary is the PE5 annex's last line, and nothing above it is
> edited: each repair is a dated annex lemma/rider naming its exact
> target. Honesty of grade: this annex is a post-ratification append and
> has NOT itself been through a hostile pass; R1's machine leg is sealed
> and GREEN (record in R1.2), R2's clause-(c) re-proof is at annex grade
> (two displayed existence arguments + transfer steps citing GENH4-4).”

**CONDITIONALITY:** **A decorrelated model, reading an ACCEPTED 2/2 note, returned five findings — three GAPs, one of them on the post-acceptance annex, and one CRITICAL flag REFUTED against the committed artifact.** The refutation of F1-as-CRITICAL is as important as the confirmations: **the committed artifact decided against the verifier**, and the finding survived only as a MINOR display defect (an undefined term).

**ARITHMETIC AUDIT:** five findings, dispositions: 3 CONFIRMED GAP (F2, F3, F4) + 1 CONFIRMED-regraded MINOR (F5) + 1 REFUTED-as-CRITICAL / CONFIRMED-as-MINOR (F1) = 5 ✓. Queue R1–R5 maps to F2, F4, F3, F5, F1 ✓ — **ordered by severity, not by number**, with R6 added as a noted extra.

**SUPERSESSION KIND:** none of its own (a provenance record); it establishes freeze predicate 2.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1478–1498. correction sites: 1886–1907 (annex pass #1's provenance, which finds a GAP in this layer).
**TEETH:** **`decorrelated-model audit`** — three of the five findings could not have been produced by any run (a hypothesis contradiction, a ring-theoretic frame error, an undefined term).
**PIN VERIFICATION:** `lean/notes/openmath/CODEX_GENH4RAT_2026-08-09.md` ✓ EXISTS.

---

### EFF.GENH4.83  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with two nested quotations (R1.0 — the consumed-clause gap, stated exactly). verbatim, lines 1500–1535.

> “### R1 (CODEX F2, the consumed-clause gap): ANNEX-LEMMA GENH4-7' — the F-SPLTAIL supply argument re-proved over the FREE boundary band
>
> **R1.0 The defect, exactly.** ANNEX-LEMMA GENH4-7 (ANNEX PE5, A1)
> states its hypothesis as
>
> > "At a genre-F stage state with A₀ hidden (every in-window A₀ digit
> > zero: a₀-positions ≤ N−1 and **a₁-positions ≤ N−1** all vanish)"
>
> and its proof glosses
>
> > "Hidden means every in-window position vanishes: v(a₀) ≥ N
> > (a₀-positions ≤ N−1) and **v(a₁) + k ≥ N + 1 (a₁-positions ≤ N−1)**".
>
> The two bold clauses contradict each other: a₁-positions ≤ N−1 all
> vanishing gives v(a₁) ≥ N, i.e. v(a₁) + k ≥ N + k — the floor
> v(a₁) + k ≥ N + 1 is the strictly weaker condition "a₁-positions
> ≤ N−k all vanish". And the WEAKER condition is the counted leaf: the
> sealed runner's `law_F` prices SPLTAIL as
> (q^{comp(w)}−1) · wf(A1, w) · deep0 with
> **deep0 = q^{Σ comp(s): s ∈ A₀, s > N} = q^{k−1}** — the boundary-band
> digits at heights N+1 … N+k−1, carried by the IN-WINDOW a₁-positions
> N−k+1 … N−1 (S2.3's comp-1 band slots), are FREE in the counted
> family; the height-N band slot (a₁-position N−k) is pinned zero
> (deep0 sums s > N strictly). So GENH4-7 as stated proves the σ-label
> only for the band-zero SLICE of the leaf — a strict subfamily,
> exactly HALF the leaf at the first live cell (machine, R1.2). The
> slice is first live at **k ≥ 2 AND N ≥ 4k+3** (SPLTAIL needs
> 2w < N with w ≥ 2k+1, so N ≥ 4k+3; the band is empty at k = 1, where
> GENH4-7 and GENH4-7' coincide verbatim): every committed F-SPLTAIL
> key is k = 1 (rows 15/16/19 + feven — machine C2), and the fresh
> k = 2 row (Zp,2,9,k2) has NO SPLTAIL leaf, so the gapped slice had
> ZERO machine exercise before this annex. CONSUMPTION: S7's F-SPLTAIL
> bullet = GENH4-7(b) = the W-12.D σ-labelling supply row (S11 firing
> table) — a consumed clause was textually gapped on a nonempty menu
> slice; hence the CHALLENGE outcome. The conclusion was TRUE all
> along, by the proof's own floor inequality; the corrected lemma:”

**CONDITIONALITY:** **A hypothesis that contradicts its own proof's gloss, on a clause W-12.D consumes, over a slice with ZERO machine exercise.** Every element of that sentence is load-bearing: the contradiction is textual, the consumption is real, and the untested slice is half the leaf at the first live cell.

**ARITHMETIC AUDIT (compiler-computed):** `a₁-positions ≤ N−1 all vanish` ⟹ `v(a₁) ≥ N` ⟹ `v(a₁) + k ≥ N + k` ✓, strictly stronger than `≥ N+1` for `k ≥ 2` ✓ — **the two clauses genuinely differ, and only at `k ≥ 2`** ✓, exactly matching “the band is empty at k = 1, where GENH4-7 and GENH4-7' coincide verbatim” ✓. First-live condition: SPLTAIL needs `2w < N` and `w ≥ 2k+1` (shard 1 `.17`'s A₁ string floor), so `N > 2(2k+1) = 4k+2`, i.e. `N ≥ 4k+3` ✓ **exact**; at `k = 2` that is `N ≥ 11` ✓ — matching R1.2's cell `(2,11,2)` ✓. `deep0 = q^{k−1}` counts the band heights `N+1 … N+k−1`, i.e. `k−1` of them ✓ — **and the height-N slot is pinned zero because deep0 sums `s > N` strictly** ✓.

**DERIVATION:** Not a mathematical unit; a defect report.
**RESOLUTION TRACE:** statement lines 1500–1535. correction sites: none.
**TEETH:** **`decorrelated-model audit`**; the “ZERO machine exercise before this annex” is the disclosure that makes the finding sharp.

---

### EFF.GENH4.84  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, ANNEX-LEMMA GENH4-7′) + proof of (a) and (b). verbatim, lines 1537–1579.

> “> **ANNEX-LEMMA GENH4-7' (GENH4-7 with the leaf's true floor — the
> > free boundary band quantified; replaces GENH4-7's hypothesis
> > sentence and clause (a)'s parenthetical, everything else
> > unchanged).** At a genre-F stage state with A₀ hidden IN THE LEAF
> > SENSE — every A₀ slot at v₁-height ≤ N vanishes, i.e. v(a₀) ≥ N
> > (a₀-positions ≤ N−1 all vanish) and v(a₁) + k ≥ N + 1
> > (a₁-positions ≤ N−k all vanish) — while the k−1 boundary-band
> > a₁-positions N−k+1, …, N−1 (v₁-heights N+1, …, N+k−1: exactly
> > S6.3's deep₀ = q^{k−1} factor) remain FREE, and pin dv(A₁) = w:
> > (a) for EVERY value of the free band digits and EVERY lift,
> > u_lift := v₁(A₀^lift) ≥ N, with u_lift = N realizable (the a₀
> > lift digit at position N), and at a band-nonzero member
> > u_lift ≤ m := the lowest nonzero band height ≤ N+k−1;
> > (b) if 2w < N then EVERY disc ≠ 0 lift of EVERY member — all
> > q^{k−1} band completions, both characteristics — has
> > u_lift ≥ N > 2w, hence sits in GENH4-3(ii)'s
> > 2SIDED(w, u_lift − w) position — including the A₀ = 0 corner via
> > F = φ·(φ + A₁) — and by S7's 2SIDED bullet (F leg) has
> > σ = {(1,2),(1,2)}: the S1 dictionary's F-SPLTAIL label,
> > (A0)-strong, lift-sound on the WHOLE counted family;
> > (c) if 2w ≥ N, NO single label is lift-sound for the leaf key
> > (re-proved per band stratum in R2 below).
> > At k = 1 the band is empty and GENH4-7' ≡ GENH4-7.
>
> *Proof of (a) and (b).* v₁(A₀) = min(v(a₀), v(a₁) + k), with
> cancellation prevented by ψ-genericity (GENH4-2; S2.1's invariants,
> maintained along chains by S5): the height-m contribution is the
> F_{q²}-letter d₁ȳ + d₀ read from (a₁-digit at m−k, a₀-digit at m),
> and ȳ ∉ F_q makes it vanish iff both digits do — both
> characteristics. Every contributing height is ≥ N: on the a₀ side
> the in-window digits (positions ≤ N−1) are state-zero and lift
> digits sit at positions ≥ N; on the a₁ side the floor is N+1, and
> the FREE band digits sit at heights N+1 … N+k−1 ≥ N+1 — so
> u_lift ≥ N REGARDLESS of the band values; equality realizable via
> a₀ at position N; a nonzero band digit at height m caps
> u_lift ≤ m by the no-cancellation letter (d₁ ≠ 0). (b)
> u_lift ≥ N > 2w is GENH4-3(ii)'s antecedent u > 2w at every lift
> and every band completion; the data consumed (w and its pin letter)
> are lift-stable (GENH4-CAP(F): w ≤ (N−1)/2 < N); S7's 2SIDED bullet
> (F leg) consumes only v(A₁(θ)) = w and v(A₀(θ)) = u_lift > 2w, so
> it applies verbatim; at A₀^lift = 0 both factors of φ·(φ + A₁)
> carry the S2.1 one-side polygon — the bullet's own corner sentence.
> ∎ (Clause (c): R2 below.)”

**CONDITIONALITY:** **(b) — the consumed clause — is now proved on the WHOLE counted family and is untouched by everything that follows.** (a) gains a band cap; (c) is deferred to R2 and later WITHDRAWN-and-replaced by (c′) (`.99`). **The header's supersession inventory is itself under-counted and is corrected at R2.M4** (`.104`). (a)'s realizability parenthetical is scoped to `N ≥ 4k+1` at R2.M1 (`.101`); **(b) is unaffected because SPLTAIL forces `N ≥ 4k+3`** ✓.

**SUPERSESSION KIND:** `replacement` of GENH4-7's hypothesis sentence and (a)'s parenthetical; `inventory completion` for (a)'s band cap. **NOT a replacement of (b)'s conclusion — “same conclusion, hypothesis now COVERING the counted family”** (`.85`).

**ARITHMETIC AUDIT:** the band has `k−1` free positions (`N−k+1 … N−1`, i.e. v₁-heights `N+1 … N+k−1`) ✓ = `deep₀ = q^{k−1}` ✓. Lift-stability of w: `2w < N` ⟹ `w ≤ (N−1)/2 < N` ✓ — inside GENH4-CAP(F)'s stable range ✓.

**DERIVATION:** Displayed. Justification tags: `by XREF GENH4-2` (no-cancellation by ψ-genericity) + `by XREF` S2.1/S5 (invariant maintenance) + `computation` (the height analysis) + `by XREF GENH4-3(ii)` + `by XREF` S7's 2SIDED F leg.

**RESOLUTION TRACE:** statement lines 1537–1579. correction sites: 1957–1999 ((c) → (c′)), 2013–2031 (M1), 2079–2088 (M4), 2159–2167 (post-pass-2 MINOR-2 on (c′)'s proof).

**TEETH:** R1.2's leg (`.86`) — **the k ≥ 2 slice's FIRST exercise**, 24,576 members enumerated, 96/96 char-0 PARI + 96/96 char-p, teeth 4/4.

---

### EFF.GENH4.85  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.1 — the W-12.D supply restored). verbatim, lines 1581–1592.

> “**R1.1 The W-12.D supply, restored.** THEOREM GENH4.C's F-SPLTAIL
> leg now reads ANNEX-LEMMA GENH4-7'(b) in place of GENH4-7(b) —
> same conclusion, hypothesis now COVERING the counted family. With
> it, the committed F-SPLTAIL key class (SPLTAIL(3) = 384/1,536/384
> at rows 15/16/19, all k = 1 — where the two lemmas coincide) AND
> the k ≥ 2 slice (first exercised in R1.2) carry the
> σ_F = {(1,2),(1,2)} label that the S11 firing-table row supplies to
> W-12.D's σ-labelling clause at n = 4 — every disc ≠ 0 lift of every
> member, both ring types. No committed key count, no density, and no
> k = 1 σ-claim moves: the sealed counts always priced the free band
> (deep0 was in `law_F` and S6.3's display from the seal); the defect
> was the post-acceptance annex's hypothesis gloss only.”

**CONDITIONALITY:** **The install instruction for R1, and the sentence a chapter cut of THEOREM GENH4.C must carry: its F-SPLTAIL leg reads GENH4-7′(b).**
**SUPERSESSION KIND:** `replacement` (which lemma the leg reads).
**TARGETS:** shard 1 `.11`, `.30`, `.33`.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1581–1592. correction sites: none.
**TEETH:** `.86`.

---

### EFF.GENH4.86  [run-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R1.2 — the k ≥ 2 slice's first machine exercise). verbatim, lines 1594–1625.

> “**R1.2 Machine record (the k ≥ 2 slice's FIRST exercise).**
> `verification/openmath/genh4annexr_supp.py` — sealed with
> preregistered predictions R1–R7 at commit 6272cd4 (BEFORE the run;
> one full design dry-run disclosed in the docstring: it caught a
> branch explosion in the first BFS root counter, replaced by the
> exact Panayi recursion; all other checks GREEN on the dry-run), run
> fresh: **GREEN, 0 violations, 0.4 s + PARI** (output md5
> `c1ed4a7f…`, results md5 `f26186fd…`, bit-identical to the
> dry-run's artifacts). The cell: (q,N,k) = (2,11,2), SPLTAIL(5),
> 2w = 10 < N = 11 — the first live k ≥ 2 cell (N = 4k+3). Checks:
> C0 5/5 md5 pins (sealed runner + artifacts + qscout22 pair).
> C2: the fresh S6-typed law has NO SPLTAIL at (2,9,2)/(2,10,2) and
> first realizes SPLTAIL(5) at N = 11; all 4 committed F-SPLTAIL keys
> are k = 1. C3: the SEALED runner's own `law_F(2,11,2)` gives
> SPLTAIL(5) = 24,576 = 3·2¹²·2 (deep0 = 2 = q^{k−1}), tying the
> fresh typing key-for-key (9 keys), node mass 2²⁰ exact; the
> OLD-gloss (band-pinned) family = 12,288 = HALF — count-refuted as a
> description of the leaf. C4: all 24,576 leaf members enumerated:
> the GENH4-7' floor holds on ALL; the band-nonzero half (12,288)
> violates the old hypothesis, 0 violate the new (characteristic-
> blind digit layer). C5: 96 constructed lifts (24 states = 3 pin
> letters × 2 band values × 4 A₁-completions; 4 lifts each, incl. the
> A₀ = 0 corner and u_lift = N = 11 lifts) over φ = x² + 4x + 16:
> PARI σ = {(1,2),(1,2)} on 96/96 — constant across BOTH band values
> (48 members on the previously unexercised band-nonzero slice).
> C6 (FIRST char-p σ contact for F-SPLTAIL): the same 96 members over
> F₂[[t]] (φ = x² + t²x + t⁴): disc ≠ 0 (exact gcd over F₂[t]) and
> EXACTLY 4 roots in F₄[[t]], 0 in F₂[[t]] on 96/96 — two unramified
> conjugate quadratic pairs, the {(1,2),(1,2)} read. C7 TOOTH: 2
> wrong-floor mutants (a₀-digit at position 9 < N: u = 9 odd ≤ 2w →
> RAM(9)): char-0 PARI σ = {(2,2)} and char-p 0 roots in F₄[[t]] —
> FIRED 4/4: the GENH4-7' floor is load-bearing, not decorative.”

**CONDITIONALITY:** **The gapped slice's first exercise, and it confirms the repair count-for-count.** The old gloss's family is exactly HALF ✓ — the finding's own quantitative claim, machine-confirmed.

**ARITHMETIC AUDIT (compiler-computed):** `SPLTAIL(5) = 24,576 = 3·2^{12}·2` ✓ (`3·4096·2 = 24,576`) ✓, with `deep0 = 2 = q^{k−1} = 2^1` ✓. Old-gloss family `12,288 = 24,576/2` ✓ **exactly HALF** ✓. Node mass `2²⁰ = 1,048,576` ✓. Cell: `N = 4k+3 = 11` at `k = 2` ✓; `w = 5` gives `2w = 10 < 11` ✓ and `w ≥ 2k+1 = 5` ✓ — **the minimal live cell**. Lifts: `3 × 2 × 4 = 24` states ✓ × 4 lifts = **96** ✓, of which the band-nonzero half is 48 ✓. Char-p read: 4 roots in `F₄[[t]]`, 0 in `F₂[[t]]` ⟹ two conjugate unramified quadratic pairs ⟹ `{(1,2),(1,2)}` ✓ **exact**. Tooth: `u = 9` odd `≤ 2w = 10` → RAM(9) → `{(2,2)}` ✓ ≠ `{(1,2),(1,2)}` ✓ — the mutant fires ✓.

**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1594–1625. correction sites: none.
**TEETH:** seven checks, GREEN; **C6 is the FIRST char-p σ contact for F-SPLTAIL in the corpus**; C7's two wrong-floor mutants fired 4/4.
**PIN VERIFICATION:** `6272cd4` ✓; `verification/openmath/genh4annexr_supp.py` ✓, `_output.txt` ✓, `_results.json` ✓ EXIST.

---

### EFF.GENH4.87  [lemma]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph + three bulleted per-stratum witnesses (R2 — clause (c) re-displayed). verbatim, lines 1627–1701. *(The three stratum bullets are quoted; the section's scope paragraph opens it.)*

> “### R2 (CODEX F4): GENH4-7'(c) re-displayed per band stratum — the cap-sharpness witnesses that actually exist
>
> **Scope.** Clause (c) is CAP SHARPNESS only: W-12.D's supply consumes
> (b), and the reader's UND exit at 2w ≥ N is conservative-sound
> regardless — F4 is unconsumed. But the old display's two witnesses
> were wrong exactly where Codex pointed: at a band-pinned state
> (k ≥ 2, lowest nonzero band digit at height m) with m ≤ 2w, NO lift
> has u_lift > 2w (GENH4-7'(a): u_lift ≤ m — Codex's (k,N,w) =
> (2,9,5), m = 10 = 2w instance), so "a lift with u_lift > 2w —
> realizable" is false there; and at even N the sentence "different
> deep lifts realize different residual classes, hence different σ"
> is unjustified in char 2 (dμ < w forces the S₁-slot to 0 and
> T² + S₀ is always a square over F_{q²}: the read is REFINE, not a
> decided σ). The corrected per-stratum witnesses (2w ≥ N throughout;
> u-geography from GENH4-7'(a): u_lift sweeps {N, N+1, …} at a
> band-zero state and {N, …, m} at a band-pinned state; legs per
> GENH4-3 + GENH4-CAP(F): u odd ≤ 2w → RAM(u), σ = {(2,2)}; u even
> = 2dμ ≤ 2w → residual read at depth dμ; u > 2w → 2SIDED,
> σ = {(1,2),(1,2)}): …”

*(The three bullets — N odd; N even with dμ < w; N even with dμ = w — are reproduced verbatim in the source at lines 1647–1701 and are carried here by reference to their own targets: the first two are WITHDRAWN at `.97`, and the third survives with its existence input completed at `.102`.)*

**CONDITIONALITY:** **TWO of the three per-stratum witnesses are later MACHINE-REFUTED and WITHDRAWN** (`.97`); the third (`2w = N`) survives, with its char-odd existence completed by a coset count (`.102`) and its char-2 trace argument re-derived SOUND by the annex pass (`.105`). **The scope sentence is what keeps the damage contained: “Clause (c) is CAP SHARPNESS only: W-12.D's supply consumes (b) … F4 is unconsumed.”**

**SUPERSESSION KIND:** received `replacement` with **WITHDRAWAL** — two displayed legs are withdrawn, not re-worded.
**CHAIN:** GENH4-7's (c) → **R2's per-stratum witnesses** → **R2.G1: two legs WITHDRAWN, (c′) at key level — TERMINAL** (with M2/M3 completing (c′)'s inputs and post-pass-2 MINOR-2 fixing its disc parenthetical).
**ARITHMETIC AUDIT:** Codex's instance `(k,N,w) = (2,9,5)`: `m = 10 = 2w` ✓, and GENH4-7′(a)'s cap gives `u_lift ≤ m = 10 = 2w` ✓ — so **no lift has `u_lift > 2w`** ✓, the old witness is unrealizable ✓. The char-2 objection: at `dμ < w` the S₁-slot is 0 ✓ and `T² + S₀` is always a square over `F_{q²}` in char 2 ✓ (Frobenius is bijective) — so the read is `'1sq'` (REFINE), not decided ✓.
**DERIVATION:** Displayed per stratum; two legs later withdrawn.
**RESOLUTION TRACE:** statement lines 1627–1701. correction sites: 1909–2011 (R2.G1), 2033–2059 (M2), 2061–2077 (M3).
**TEETH:** annex pass #1's FR4/FR5 legs — **which refuted two of the three** (`.97`).

---

### EFF.GENH4.88  [lemma]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2's char-2 refine-deeper leg). verbatim, lines 1703–1718.

> “**The char-2 refine-deeper leg (cited where used above).** A '1sq'
> read at depth dμ₁ refines with letter s₁ = the square root (S5, one
> step); LEMMA GENH4-4 maps the refine locus ONTO the floored fresh
> node {dv(A₁′) > dμ₁, dv(A₀′) > 2dμ₁}, whose digits are free lift
> digits; realize the fresh leaf dv(A₁′) = dμ₁+1 =: w′,
> dv(A₀′) = 2dμ₁+3 = 2w′+1 > 2w′ (nonempty: S6.1's census
> (q^{comp}−1)·q^{…} > 0, slots live by GENH4-6): a fresh
> 2SIDED′(w′, w′+1) for every such lift, σ = {(1,2),(1,2)} by S7's
> 2SIDED bullet — which differs from the {(2,2)} of the paired RAM
> lift. This is the old display's "different deep lifts" sentence
> made into an actual construction; it is an annex-grade transfer
> (GENH4-4 + census nonemptiness, both PROVED in the body, composed
> here without a fresh hostile pass).”

**CONDITIONALITY:** **WITHDRAWN — machine-refuted at annex pass #1** (`.97`). The transport error is named there: GENH4-4's onto-statement quantifies over the FULL refine slice, and on a FIXED member only lift digits vary, so **neither fresh coordinate is free**.
**SUPERSESSION KIND:** received **`replacement` with WITHDRAWAL**.
**ARITHMETIC AUDIT:** the claimed fresh leaf `dv(A₀′) = 2dμ₁+3` with `w′ = dμ₁+1` gives `2w′+1 = 2dμ₁+3` ✓ internally consistent — **the arithmetic is fine; the availability is not**, which is precisely the withdrawal's ground.
**DERIVATION:** Displayed; withdrawn.
**RESOLUTION TRACE:** statement lines 1703–1718. correction sites: 1917–1956 (R2.G1's refutation).
**TEETH:** FR4 refuted it 6/6.

---

### EFF.GENH4.89  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraphs (R3 — the stage-ring frame erratum). verbatim, lines 1720–1765.

> “### R3 (CODEX F3): the stage-ring frame erratum — v and res live in L/O_L, and R is an order, not a DVR
>
> **The defect.** S2.1's two carrier sentences are literally false:
> "φ is irreducible, **R is a complete DVR**, totally ramified
> quadratic" (genre E) and "R is an unramified-over-the-ladder
> **DVR** … residue field K = F_{q²}" (genre F), plus "**R's
> associated graded** IS COROLLARY W-9's twisted algebra".
> R = Ô[x]/(φ) = Ô[θ] is the NON-MAXIMAL order O[θ] at genre F for
> every k ≥ 1 and at genre E for every h ≥ 3. Witnesses: (Codex's, at
> this note's own A2 key φ = x² + 2x + 4 over ℤ₂) R/2R ≅ F₂[ε]/(ε²),
> not F₄ — R has nilpotents mod 2, its maximal-ideal residue field is
> F₂, and θ/2 (which generates the integral closure) is not in R;
> (the fold note's, genre E h ≥ 3) m_R = (π, θ) is non-principal: a
> generator γ would have v(γ) ∈ ℤ ∪ (h/2 + ℤ); at v(γ) = 1,
> θ/γ = c + dθ would need v(c) = h/2 − 1 ∉ ℤ, impossible, and at
> v(γ) = h/2, π/γ has v = 1 − h/2 < 0. R = O_L holds exactly at
> genre E, h = 1 (the Eisenstein case) — nowhere else in this note's
> range (F entries have k ≥ 1).
>
> **The restated frame (where every consumed fact is true).** Let
> L := Frac(R) = base(θ) — φ is irreducible over the base in both
> genres (E: the one-side polygon; F: the residual ψ irreducible) —
> and O_L its valuation ring, which IS a complete DVR. Define
> **v := v_L restricted** (normalized on the base) and read every
> residue in O_L/m_L. Then, exactly as S2.1's bullets display:
> genre E: e(L/base) = 2, f = 1, v(θ) = h/2, value group ½ℤ,
> O_L/m_L = F_q, res(θ²π^{−h}) = z; genre F: e = 1, f = 2, v(θ) = k,
> value group ℤ, O_L/m_L = F_{q²} = F_q(ȳ), res(θπ^{−k}) = ȳ a root
> of ψ. The gr sentence re-aims at **gr(O_L)** (one K-line per
> dv-height — W-9's twisted algebra); R ⊆ O_L, and every graded READ
> the note performs (the leading digit of an evaluated element at its
> v-height) happens in gr(O_L).
>
> **Consumption audit (why nothing downstream moves).** The note never
> uses R's ring-theoretic structure — it uses only v(A(θ)) and
> res(A(θ)/normalizer) of EVALUATED elements A(θ) ∈ O[θ] ⊆ O_L:
> GENH4-2's ultrametric/parity proof, S3's twisted-normalizer
> residues, S5's carry computation, S7's resolvent chain, and S0's
> DULEMMA disclosure (which needs only v's multiplicativity — true
> for v_L) all run in L/O_L verbatim; the censuses and count laws are
> digit-coordinate counts on O[x]-coefficients and never touch R at
> all. No count, no σ conclusion, no density moves. RIDERED (named
> exactly, not edited): S2.1's E bullet's "R is a complete DVR",
> S2.1's F bullet's "R is an unramified-over-the-ladder DVR", and
> S2.1's "R's associated graded IS …" sentence — each read with
> R's v/residue/graded data interpreted as O_L's, per this erratum.”

**CONDITIONALITY:** **A literally false carrier claim, with two explicit witnesses, and a consumption audit showing nothing downstream moves.** Its audit sentence is itself riddered at R2.REM (`.105`): S7's Y-trichotomy “runs in the quartic root field base(θ_F), not in L = Frac(R)”.
**SUPERSESSION KIND:** `provenance-rider` on three named sentences (the carrier is re-homed; no datum changes).
**TARGETS:** shard 1 `.14` (three sentences), and by audit `.19`, `.20`, `.23`, `.28`, `.05`.
**ARITHMETIC AUDIT:** both witnesses re-derived at shard 1 `.14` ✓ (`R/2R ≅ F₂[ε]/(ε²)` from `θ² ≡ 0 mod 2`; the non-principality valuation argument). `R = O_L` exactly at genre E `h = 1` ✓ (Eisenstein).
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1720–1765. correction sites: 2092–2099 (R2.REM Remark 1).
**TEETH:** NONE — a frame erratum; **`decorrelated-model audit`** is the finding's disposition.

---

### EFF.GENH4.90  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R3's queued transport obligation). verbatim, lines 1767–1772.

> “**Transport obligation, QUEUED (not executed here).** GENHN.A(i)
> states the same "stage ring is a DVR with residue field F_{q^{f₁}}"
> sentence at general (e₁, f₁); the same carrier-rename erratum is
> OWED TO THE LIVE GENHN ARC and is hereby queued for GENHN's own
> ratification round — one rider of exactly this R3 form at
> GENHN.A(i), with the non-maximality witnesses transported.”

**CONDITIONALITY:** **An outbound erratum, QUEUED and not landed** — header predicate B's second governing quote. **Cross-note check: GENIND's §S9.3 GENHN bullet records exactly this as one of three queued GENHN errata (“A(i) transport ← Codex-GENH4 F3”), and GENIND's dated supplier-movement record then reports E3 EXECUTED @ `46bf675`** (GENIND shard 3 `.26`) — **so the queued obligation WAS discharged at the source, and GENH4 (frozen) does not record it.**
**SUPERSESSION KIND:** none of GENH4's own; an outbound queued erratum.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1767–1772. correction sites: none here; discharged externally at GENHN `46bf675` (recorded in GENIND shard 3).
**TEETH:** NONE.
XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN.A(i)` — count **11**.

---

### EFF.GENH4.91  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraphs with an ASCII table (R4 — the S7 units-normalization rider). verbatim, lines 1774–1801.

> “### R4 (CODEX F5): the S7 units-normalization rider (supersedes ANNEX A2's partial rider)
>
> **The defect.** S7 mixes valuation conventions inside one section:
> the opening display "v(A₁(θ)) = w/2, v(A₀(θ)) = u/2 EXACTLY" and
> the 2SIDED/INERT bullets ("v(Y) ∈ {w/2, (u−w)/2}"; "v(Y) = dμ/2")
> are E-halved forms, flatly contradicting the section's own
> declaration "genre F: w, u in v₁ = v units" — while the RAM
> bullet's F-leg "v(Y) = u/2" is ALREADY a true-unit statement
> (u odd, so u/2 half-integral: that is the ramification read).
> ANNEX A2 repaired only the norm tag between them.
>
> **The rider (one normalization sentence + the F table).** ALL
> displayed valuation equations in S7's trichotomy bullets are stated
> in genre E's halved (dv/2) units; their genre-F true-unit
> (v₁ = v) instances are:
>
>     opening:  v(A₁(θ)) = w,  v(A₀(θ)) = u
>     RAM:      v(Y) = u/2            (as displayed -- already true-unit)
>     2SIDED:   v(Y) ∈ {w, u−w}
>     INERT:    v(Y) = dμ, normalizer n₂ = π^{dμ}
>
> Every σ conclusion is invariant under the rescaling: polygon shapes,
> parities, and denominator reads are scale-blind; the INERT residue
> step is computed against n₂ = π^{dμ} (S3), correct in true units;
> the 2SIDED norm balance is A2's analysis, whose halved and unhalved
> forms give the same j = 2. Same defect species as A2's norm tag,
> which PE5 graded MINOR; this rider covers all three sentences at
> once and supersedes A2's partial one.”

`[TABLE]` — the genre-F true-unit instances (rule 14's second emission):

| S7 display | E-halved form (as displayed) | Genre-F true-unit instance |
|---|---|---|
| opening | `v(A₁(θ)) = w/2`, `v(A₀(θ)) = u/2` | `v(A₁(θ)) = w`, `v(A₀(θ)) = u` |
| RAM | `v(Y) = u/2` | `v(Y) = u/2` (already true-unit) |
| 2SIDED | `v(Y) ∈ {w/2, (u−w)/2}` | `v(Y) ∈ {w, u−w}` |
| INERT | `v(Y) = dμ/2` | `v(Y) = dμ`, `n₂ = π^{dμ}` |

**CONDITIONALITY:** **A rider that supersedes an earlier rider** — the only such case in this queue. Its scope-invariance claim (“Every σ conclusion is invariant under the rescaling”) is what keeps `.79`'s dictionary intact.
**SUPERSESSION KIND:** `replacement` (of A2's partial rider) + `wording-rider` (on all of S7's displays).
**TARGETS:** shard 1 `.28`, `.29`, `.31`, `.32`; supersedes `.75`.
**ARITHMETIC AUDIT:** the RAM F-leg `v(Y) = u/2` is already true-unit because `u` odd makes `u/2` half-integral, which IS the ramification read ✓ — **the one bullet that needed no rescaling, correctly identified.** Scale-invariance: multiplying all valuations by 2 preserves polygon shapes, denominators and parities ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1774–1801. correction sites: none.
**TEETH:** NONE — a normalization rider; `.77`'s committed instance is its nearest tie.

---

### EFF.GENH4.92  [table]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraphs with a **fixed-width six-key partition table** (R5 — “law keys” defined and the pre2 remainder displayed), emitted TWICE per rule 14. verbatim, lines 1803–1839.

> “### R5 (CODEX F1): "law keys" defined + the pre2 row's full six-key partition displayed
>
> **The defect.** P-2 ("481 law-key checks") and P-3 ("law keys
> EXACTLY {…}") use the term "law keys" WITHOUT DEFINITION and
> display no remainder, inviting the partition misreading the
> verifier made (summing the four displayed keys to 655,360 ≠ 2²⁰ and
> filing a census contradiction).
>
> **The definition.** "Law keys" = the keys of kind in the sealed
> runner's `LAW_KINDS = ('RAM4', 'G2', 'FULL', 'SUB', 'E', 'F')`
> (genh4_checks.py line 299) — the kinds whose counts this note's S6
> laws predict and `cmp_tables` compares. Non-law kinds (the order-1
> strata: vertices and order-1 tails, tied instead through the W-12.A
> transcription in GH-JSONTIE) are counted in the same tables but are
> not "law keys".
>
> **The full pre2 partition (committed row, machine C1).** The
> committed `genh4_checks_results.json` pre2 row (Zp,2,11,pre=(1,2))
> partitions its 2²⁰ = 1,048,576 members EXACTLY into SIX keys:
>
>     RAM4(9)                    = 524,288   (law kind)
>     G2(5,'2')                  =  65,536   (law kind)
>     E-RAM(21)                  =  32,768   (law kind)
>     E-UND                      =  32,768   (law kind)
>     VTX((0,10),(1,7),(4,0))    = 131,072   = 2^17  (non-law: vertex)
>     L1TAIL                     = 262,144   = 2^18  (non-law: order-1
>                                                     B0-hidden tail)
>     Σ                          = 1,048,576 = 2^20  EXACT
>
> P-3's sentence displayed the four law-kind keys, exactly right as a
> law-key statement; the remainder 393,216 is the two non-law strata,
> both FORCED by the pre2 floored box (chain (1,2): floors
> v(B_j) ≥ 9, 7, 5, 3; free digits 2+4+6+8 = 20): the two-side vertex
> v(B₀) = 10 exact ∧ v(B₁) = 7 exact prices 1·2³·2⁶·2⁸ = 2¹⁷, and
> the B₀-hidden level-1 tail v(B₀) ≥ 11 prices 2^{4+6+8} = 2¹⁸ —
> hand-derived in the fold note and machine-tied here (C1). No census
> contradiction; no machine number was ever wrong.”

`[TABLE]` — the pre2 six-key partition (rule 14's second emission):

| Key | Count | Kind |
|---|---|---|
| `RAM4(9)` | 524,288 = 2¹⁹ | law |
| `G2(5,'2')` | 65,536 = 2¹⁶ | law |
| `E-RAM(21)` | 32,768 = 2¹⁵ | law |
| `E-UND` | 32,768 = 2¹⁵ | law |
| `VTX((0,10),(1,7),(4,0))` | 131,072 = 2¹⁷ | non-law (vertex) |
| `L1TAIL` | 262,144 = 2¹⁸ | non-law (order-1 B₀-hidden tail) |
| **Σ** | **1,048,576 = 2²⁰** | **EXACT** |

**ARITHMETIC AUDIT (compiler-computed, rule 22):** `524,288 + 65,536 + 32,768 + 32,768 + 131,072 + 262,144 = 1,048,576 = 2²⁰` ✓ **exact.** The four law keys sum to `655,360` ✓ = the verifier's figure ✓, and the remainder `1,048,576 − 655,360 = 393,216 = 2¹⁷ + 2¹⁸` ✓ **exact.** The floored box: chain `(1,2)` gives floors `v(B_j) ≥ 9, 7, 5, 3` for `j = 0,1,2,3`, so free digits `(11−9) + (11−7) + (11−5) + (11−3) = 2+4+6+8 = 20` ✓ **exact.** The vertex pricing `1·2³·2⁶·2⁸ = 2¹⁷` ✓ (B₀ and B₁ pinned exact, B₂ and B₃ free at 6 and 8, plus 3 from B₁'s freedom above 7 — consistent with the displayed factors) ✓. The tail pricing `2^{4+6+8} = 2¹⁸` ✓. **Every number in the partition reproduces.**

**CONDITIONALITY:** **A CRITICAL flag REFUTED against the committed artifact, surviving only as an undefined term.** The definition is pinned to a source line (`genh4_checks.py line 299`).
**SUPERSESSION KIND:** `inventory completion` (a definition and a remainder supplied; no number moves).
**TARGETS:** shard 1 `.62`.
**DERIVATION:** Displayed + machine-tied at C1.
**RESOLUTION TRACE:** statement lines 1803–1839. correction sites: none.
**TEETH:** the annex-R leg's C1, tying the committed row.

---

### EFF.GENH4.93  [scope-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R6 — the `(GENH4-2)` cite's scope). verbatim, lines 1841–1848.

> “### R6 (noted, the fold queue's R5): the "(GENH4-2)" cite at the key's own roots
>
> S7's 2SIDED bullet cites "(GENH4-2) at the key's own roots η".
> GENH4-2 is stated for development coordinates; its PROOF applies
> verbatim at any θ with the two facts S7 displays ((E) v(η) = h/2;
> (F) v(η) = k with res(ηπ^{−k}) a root of ψ) — the cite is to the
> proof, not the stated scope. Half-line closure of the
> orchestrator's own noted nit; no consumer moves.”

**CONDITIONALITY:** A scope license. **Note the provenance: “the orchestrator's own noted nit”, i.e. a finding neither the verifier nor a run produced.**
**SUPERSESSION KIND:** `license` (a cite is licensed beyond a lemma's stated scope, with the reason).
**TARGETS:** shard 1 `.19`, `.29`.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1841–1848. correction sites: 2092–2099 (R2.REM Remark 1 cites it).
**TEETH:** NONE.

---

### EFF.GENH4.94  [changes-record] · **SERIES GENH4-BOX-1, entry 2 of 3 (post-ratification)**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1850–1868.

> “**GENH4-BOX-1 (arc record) — dated APPEND (2026-08-09, post-
> ratification).** Continuing the [r1]/[r2]/[r3]/PE4/PE5 record under
> the acceptance freeze: **the Codex ratification pass HAS NOW RUN
> (CODEX_GENH4RAT_2026-08-09.md, gpt-5.6-sol at HIGH, fresh context) —
> outcome CHALLENGE: 5 findings, adjudicated 1 REFUTED-as-classified
> (F1 → MINOR display), 2 GAP (F2 consumed-clause on the
> post-acceptance ANNEX PE5's GENH4-7; F3 frame), 1 GAP scoped to the
> unconsumed clause (c) (F4), 1 MINOR (F5). The ACCEPTED 2/2 grade
> stands ANNOTATED by the fold note pending Asvin's read; THIS ANNEX R
> applies the full repair queue R1–R5 (+ the noted R6): GENH4-7'
> re-proves the W-12.D F-SPLTAIL supply over the true leaf (the free
> boundary band), with the k ≥ 2 slice machine-exercised for the
> FIRST time (genh4annexr_supp.py: GREEN, 0 violations; 96/96 char-0
> PARI σ + 96/96 char-p root-count σ + 24,576 members enumerated +
> teeth 4/4). Any future hostile pass on this note attacks the
> post-ANNEX-R text; ANNEX R itself has NOT been through a hostile
> pass. Conditionality is otherwise unchanged: exactly the S11
> arc-grade stack, plus the GENHN.A(i) transport erratum QUEUED to
> the live GENHN arc (R3).**”

**CONDITIONALITY:** **“The ACCEPTED 2/2 grade stands ANNOTATED by the fold note pending Asvin's read”** — an acceptance neither revoked nor clean, awaiting an owner decision. **This is OPEN-CALL 1's object.**
**SUPERSESSION KIND:** `as-of scoping` on the acceptance (annotated, not revoked).
**TARGETS:** shard 1 `.01`; `.80`.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1850–1868. correction sites: 2105–2127 (entry 3).
**TEETH:** `.86`.

---

### EFF.GENH4.95  [fence] · **SERIES WHAT-DOES-NOT-MOVE, entry 2 of 3**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 1870–1884.

> “**What does not move (ANNEX R).** Every displayed statement, proof,
> and frozen number of the accepted body and of ANNEX PE5's A1–A4
> except the three rider targets named in R3/R4 and GENH4-7's
> hypothesis sentence (superseded by GENH4-7', conclusion identical);
> the sealed runner and all committed artifacts (md5 pins re-verified,
> C0); every committed key count incl. the pre2 six-key partition (R5
> displays it, C1 machine-ties it); THEOREM GENH4.A/B and the count
> laws (the free band was always priced — deep0 in `law_F` and S6.3
> from the seal); THEOREM GENH4.C's dictionary and the W-12.D supply
> (the label was always right; R1 widens the PROOF's stated family to
> the counted one); the eleven densities, the triple tie, and the S11
> conditionality stack; GENH4-BOX-2 (n = 5's embedded CS genres stay
> OPEN). The E-side displays are exact as written throughout — every
> ANNEX R item is genre-F (R1/R2), frame (R3), units (R4), or display
> (R5/R6) scope.”

**CONDITIONALITY:** **An enumerated non-movement declaration with an exception list of exactly four items.** Its closing taxonomy — every item is genre-F, frame, units or display — is the layer's own scope proof.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1870–1884. correction sites: none.
**TEETH:** NONE.

---
### EFF.GENH4.96  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph (ANNEX R2's provenance — the first annex hostile pass). verbatim, lines 1886–1907.

> “## ANNEX R2 (2026-08-09, post-annex-pass-1)
>
> **Provenance and scope.** The first hostile annex pass
> (`GENH4_annexpass_report.md`, commits 6cb147b → fed3cff → a8dec16,
> fresh context, quote-and-classify) returned **NOT CLEAN at annex
> scope: 0 CRITICAL + 1 GAP + 4 MINOR + 2 remarks** — the
> annex-acceptance count stays 0/2. The GAP (GAP-1) machine-refutes
> ANNEX R's R2 clause-(c) witnesses at band-pinned strata; the
> consumed surface (GENH4-7'(b), the W-12.D F-SPLTAIL supply) survived
> the pass's full hostile re-derivation plus two fresh cells. This
> annex lands the owed repairs. The body + ANNEX PE5 + ANNEX R above
> are BYTE-FROZEN: md5 `863c21600fa48ae755d0d87b77b894d4`
> (113,738 bytes, identical to the HEAD blob at ca3754d) verified
> before and after this append; nothing above this section's first
> line is edited — every repair names its exact target. Machine
> support: the annex-pass fresh leg
> `verification/openmath/genh4annexpass_fresh.py` (md5 `f044c491…`,
> output `bf8f94f5…`, results `71535780…`, committed at fed3cff;
> GREEN, 0 violations) — its FR4/FR5 checks are the adjudication legs
> cited below; no new computation was needed. Honesty of grade: ANNEX
> R2 itself has NOT been through a hostile pass; annex pass #2 attacks
> the post-R2 text and attempts the stack's first clean mark.”

**CONDITIONALITY:** **The consumed surface SURVIVED a full hostile re-derivation plus two fresh cells; what fell was the unconsumed cap-sharpness clause.** That separation — consumed survives, unconsumed falls — is the pass's most important structural result. **The results md5 `71535780…` is corrected to `7153578c…` by the post-annex-pass-2 MINOR-1** (`.109`).

**SUPERSESSION KIND:** none of its own (a provenance record); establishes freeze predicate 3.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 1886–1907. correction sites: 2152–2158 (MINOR-1, the pin transcription).
**TEETH:** `in-house hostile pass` at annex scope, with a committed fresh leg.
**PIN VERIFICATION:** `6cb147b` ✓, `fed3cff` ✓, `a8dec16` ✓, `ca3754d` ✓; `verification/openmath/genh4annexpass_fresh.py` ✓ (+ output ✓, results ✓) EXIST; `lean/notes/openmath/GENH4_annexpass_report.md` — **verified to EXIST ✓.**

---

### EFF.GENH4.97  [supplier-finding]

**CANONICAL STATEMENT:** FORM: heading + bold-headed paragraph with two quoted refuted displays and the machine refutation (R2.G1's finding half). verbatim, lines 1909–1936.

> “### R2.G1 (GAP-1): the N-even band-pinned leg and the refine-deeper leg of R2 are WITHDRAWN — machine-refuted; clause (c) restated at the key level
>
> **The refuted displays, quoted.** R2's N-even dμ < w bullet claimed,
> at band-pinned strata with m ≤ 2w:
>
> > "u = N residual read at depth dμ < w (S₁-slot 0): char ≠ 2 decided
> > ≠ {(2,2)} as above; char 2: '1sq' → one refine step."
>
> and the refine-deeper leg claimed:
>
> > "LEMMA GENH4-4 maps the refine locus ONTO the floored fresh node
> > {dv(A₁′) > dμ₁, dv(A₀′) > 2dμ₁}, whose digits are free lift
> > digits; realize the fresh leaf dv(A₁′) = dμ₁+1 =: w′,
> > dv(A₀′) = 2dμ₁+3 = 2w′+1 > 2w′ …: a fresh 2SIDED′(w′, w′+1) for
> > every such lift, σ = {(1,2),(1,2)} … Clause (c) is thereby
> > re-established at the key level in every stratum."
>
> Both are FALSE as within-stratum claims. Machine (FR4): at
> (q,N,k) = (2,10,2), UND key, band-pinned stratum m = 11, w = 7,
> dμ = 5 < w — squarely inside the quoted bullet — the 6 refine-path
> u = 10 lifts read PARI σ = {(2,2)} on 6/6 against the displayed
> fresh 2SIDED′(6,7) σ = {(1,2),(1,2)}; all 24 band-pinned lifts
> across (2,8,2) and (2,10,2) read {(2,2)} — those two strata are
> σ-CONSTANT, with no within-stratum differing pair at all. At
> (2,8,2) (N = 8 ≤ 4k) the quoted "u = N residual read" does not even
> exist: both height-8 components sit below the GENH4-1F entry
> budgets (b₀@8 < v(β₀) ≥ 4k+1 = 9; b₁@6 < v(β₁) ≥ 3k+1 = 7), so
> every in-family lift has u = 9 = m → RAM(9) → {(2,2)}.”

**CONDITIONALITY:** **A MACHINE REFUTATION of a displayed annex argument, with PARI σ on 6/6 and 24/24.** The two strata are σ-CONSTANT — not merely un-witnessed but provably without a within-stratum differing pair.

**ARITHMETIC AUDIT (compiler-computed):** at `(2,8,2)`: `v(β₀) ≥ 4k+1 = 9` ✓ and `v(β₁) ≥ 3k+1 = 7` ✓ (shard 1 `.15`'s budgets), so the height-8 letter's components sit at a₀-position 8 `< 9` ✓ and a₁-position `8−k = 6 < 7` ✓ — **both below budget, so the height-8 slot is structurally zero** ✓ and `u = 9 = m` ✓ → odd, `≤ 2w` → RAM(9) → `{(2,2)}` ✓. At `(2,10,2)`: `m = 11`, `w = 7`, `2w = 14 ≥ m` ✓ so GENH4-7′(a)'s cap `u_lift ≤ m = 11 < 14` holds ✓ — **no lift reaches `u > 2w`** ✓, exactly the refutation.

**DERIVATION:** Not a mathematical unit; a refutation with machine legs.
**RESOLUTION TRACE:** statement lines 1909–1936. correction sites: none.
**TEETH:** **FR4** — PARI σ 6/6 and 24/24; a **`decorrelated-model audit` executed as a machine refutation**, the strongest combination in the queue.

---

### EFF.GENH4.98  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed bulleted display (R2.G1's transport-error diagnosis). verbatim, lines 1938–1956.

> “**Why the within-stratum route cannot work (the transport error,
> displayed).** GENH4-4's onto-the-fresh-node statement quantifies
> over the FULL refine slice — all in-window digits free. On a FIXED
> member only LIFT digits vary, and neither fresh coordinate is free:
>
> * **dv(A₁′) is FORCED, not free.** In equal characteristic the
>   '1sq' root s₁ = √S₀ lies in F_q, the refine carry C = 0 and the
>   2w_re term dies: dv(A₁′) = w. In mixed characteristic the +2w_re
>   revival forces dv(A₁′) = dμ+1. Either way the A₁′ string is
>   key-pinned, never at the display's free disposal.
> * **dv(A₀′) is CAPPED by the surviving band letter.** The height-m
>   band letter's ȳ-component d₁ ≠ 0 survives the refine
>   substitution: at (2,10,2), λ = ŝ²π¹⁰ + ŝπ⁵A₁ contributes the
>   height-10 kill plus terms at heights ≥ 12 only — no correction
>   reaches height 11 — so dv(A₀′) = 11 is forced; 11 odd ≤ 2w →
>   RAM(11) → σ = {(2,2)}, exactly the FR4 read. Wherever the band
>   caps u′ ≤ m < 2dμ+3, the displayed fresh leaf dv(A₀′) = 2dμ+3 is
>   unrealizable in both characteristics.”

**CONDITIONALITY:** **A quantifier-transport error named precisely: a full-slice ONTO statement applied to a fixed member.** This is the same species of error the corpus has now seen three times (GENIND's `M★ < N` from a lower bound; GENIND's ONTO-without-unit-pivots; here). **LEMMA GENH4-4 itself is untouched** (shard 1 `.09`).
**ARITHMETIC AUDIT:** at `(2,10,2)`, `dμ = 5`, so the displayed fresh leaf would need `dv(A₀′) = 2dμ+3 = 13`, but the band caps `u′ ≤ m = 11 < 13` ✓ — **unrealizable** ✓. And `11` odd `≤ 2w = 14` → RAM(11) → `{(2,2)}` ✓ matching FR4 ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 1938–1956. correction sites: none.
**TEETH:** FR4.

---

### EFF.GENH4.99  [lemma]

**CANONICAL STATEMENT:** FORM: display (blockquote, GENH4-7′(c′)) + proof. verbatim, lines 1957–1999.

> “> **(c′)** If 2w ≥ N, NO single label is lift-sound for the leaf
> > KEY. Witnesses live at the key's band-zero members — which every
> > leaf key contains (deep0's band sweep includes the zero value; at
> > k = 1 the whole key is band-zero) — and are shape-only where
> > 2w > N:
> > (i) if 2w > N: let u₀ := the least odd height ≥ max(N, 4k+1);
> > then u₀ ≤ 2w (N odd ≥ 4k+1: u₀ = N ≤ 2w; N even ≥ 4k+2:
> > u₀ = N+1 ≤ 2w since 2w > N with both even; N ≤ 4k: u₀ = 4k+1
> > ≤ 2w−1 since w ≥ 2k+1, S2.3), and the two lifts of one band-zero
> > member — the a₀ digit at height u₀ alone (u = u₀ odd ≤ 2w →
> > RAM(u₀) → σ = {(2,2)}) and the a₀ digit at height 2w+1 alone
> > (u = 2w+1 > 2w → 2SIDED(w, w+1) → σ = {(1,2),(1,2)}) — differ,
> > both characteristics, no residual read consulted;
> > (ii) if 2w = N: a u > 2w lift (2SIDED, σ = {(1,2),(1,2)}) against
> > an inert continuation at the separable u = 2w read (σ = {(1,4)})
> > at SOME member of the key — existence by the completed coset
> > count (R2.M2 below) in char odd and by R2's trace argument
> > (pass-verified sound, R2.REM) in char 2.
> > NO within-stratum pair is claimed at band-pinned strata with
> > m ≤ 2w: such strata can be σ-constant (the FR4 pair of strata
> > read {(2,2)} on 24/24), and the key-level conclusion rides the
> > band-zero stratum of the same key — cross-stratum contrast, which
> > is what cap-uniqueness consumes.”

**CONDITIONALITY:** **The repaired clause, at KEY level with band-zero witnesses and an explicit non-claim at band-pinned strata.** Its `(i)` leg is **shape-only** (“no residual read consulted”), which is what makes it characteristic-blind; its `(ii)` leg needs an existence input supplied by M2 (char odd) and R2's trace argument (char 2, pass-verified). **UNCONSUMED — see `.100`.** Its proof's disc parenthetical is corrected by the post-annex-pass-2 MINOR-2 (`.110`).

**SUPERSESSION KIND:** `replacement` of clause (c) and of R2's per-stratum witness display.
**TARGETS:** `.72`(c), `.87`.

**ARITHMETIC AUDIT (compiler-computed, on (i)'s three cases):** `N odd ≥ 4k+1`: `u₀ = N` and `2w ≥ N` gives `u₀ ≤ 2w` ✓. `N even ≥ 4k+2`: `u₀ = N+1`; with `2w > N` and both `2w, N` even, `2w ≥ N+2 > N+1 = u₀` ✓. `N ≤ 4k`: `u₀ = 4k+1`, and `w ≥ 2k+1` gives `2w ≥ 4k+2 = u₀+1`, so `u₀ ≤ 2w−1` ✓. **All three sub-cases exact.** The two lifts: `u = u₀` odd `≤ 2w` → RAM → `{(2,2)}` ✓; `u = 2w+1 > 2w` → 2SIDED(w, w+1) → `{(1,2),(1,2)}` ✓ — **and `2w+1` is realizable at a band-zero member because the a₀ lift digits are free above N** ✓.

**DERIVATION:** verbatim, lines 1985–1999 (quoted in the source; its key steps: band-zero existence from deep0's sweep, u-geography from GENH4-7′(a) with M1's correction, the two legs from S7's RAM and 2SIDED bullets, and disc ≠ 0 at both witnesses).

**RESOLUTION TRACE:** statement lines 1957–1999. correction sites: 2033–2059 (M2 supplies (ii)'s char-odd input), 2100–2103 (R2.REM verifies (ii)'s char-2 input), 2159–2167 (MINOR-2 corrects the disc parenthetical).
**TEETH:** FR4 (24/24 band-pinned σ-constant) + FR5 at `(2,9,2)` (9/9, both sides at one band-pinned stratum with `m = 2w`) — **the machine-confirmed instance pattern is displayed at `.100`.**

---

### EFF.GENH4.100  [scope-record]

**CANONICAL STATEMENT:** FORM: bold-headed paragraph (R2.G1's consumption status). verbatim, lines 2001–2011.

> “**Consumption status (unchanged).** Clause (c)/(c′) is UNCONSUMED:
> W-12.D's supply row consumes clause (b) only (S11 firing table;
> re-verified by the annex pass's charge 4), and the reader's UND
> exit at 2w ≥ N is conservative-sound regardless — no consumer moves
> under this correction. The honest-scope sentence of R2's 2w = N leg
> (τ-degenerate members; key granularity) carries over to (c′)
> verbatim. The machine-confirmed instance pattern of (c′): at the
> two FR4 cells the {(2,2)} side is carried by the band-pinned strata
> (24/24) and the {(1,2),(1,2)} side by band-zero members of the same
> keys (6/6 at each cell); at the FR5 cell (2,9,2) both sides live at
> one band-pinned stratum with m = 2w (9/9).”

**CONDITIONALITY:** **The containment sentence: a machine-refuted annex argument moves no consumer, because the consumed clause is (b) and the refuted one was (c).** Re-verified independently by the pass's charge 4. **The “(6/6 at each cell)” figure is corrected by the post-annex-pass-2 MINOR-3 to “6/6 TOTAL, 3 per cell”** (`.111`).
**SUPERSESSION KIND:** none of its own; a status declaration. Receives a `provenance-rider` at MINOR-3.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2001–2011. correction sites: 2168–2173 (MINOR-3).
**TEETH:** FR4 + FR5.

---

### EFF.GENH4.101  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M1 — realizability scoped). verbatim, lines 2013–2031.

> “### R2.M1 (MINOR-1): GENH4-7'(a)'s realizability parenthetical scoped to N ≥ 4k+1
>
> Quoted targets: "u_lift = N realizable (the a₀ lift digit at
> position N)" (7'(a)) and "u_lift sweeps {N, N+1, …} at a band-zero
> state" (R2). Corrected: **u_lift = N is realizable WHEN
> N ≥ 4k+1** (the a₀ lift digit at position N is then inside
> GENH4-1F's entry budget v(β₀) ≥ 4k+1); at hidden states with
> N ≤ 4k (nonempty: the UND leaves at (2,8,2)) the height-N letter is
> structurally zero — both components sit below the budgets (the a₀
> component at N < 4k+1, the a₁ component at N−k < 3k+1) — and the
> sweep starts at max(N, 4k+1). R2's u-geography sentences read
> correspondingly: {max(N, 4k+1), max(N, 4k+1)+1, …} at a band-zero
> state and {max(N, 4k+1), …, m} at a band-pinned state. The FLOOR
> half of (a) (u_lift ≥ N, every band completion, every lift) is
> untouched. **Clause (b) is unaffected**: SPLTAIL forces N ≥ 4k+3
> (2w < N with w ≥ 2k+1, S2.3), so position N is in budget throughout
> (b)'s geography — realizability there is exercised at the committed
> and annex-pass cells (u = N lifts at (2,11,2), (2,15,3), (3,11,2):
> C5/FR2A/FR2B).”

**CONDITIONALITY:** **A realizability claim scoped to the entry budget, with (b) explicitly unaffected because SPLTAIL forces a stronger floor.** The floor half of (a) — the one (b) uses — is untouched.
**SUPERSESSION KIND:** `scope-pin`.
**TARGETS:** `.72`(a), `.84`(a), `.87`.
**ARITHMETIC AUDIT:** SPLTAIL forces `2w < N` with `w ≥ 2k+1` ⟹ `N > 4k+2` ⟹ `N ≥ 4k+3 > 4k+1` ✓ — **(b)'s geography is always in budget** ✓. At `(2,8,2)`: `N = 8 ≤ 4k = 8` ✓ so the height-N letter is structurally zero ✓ (a₀ at `8 < 9` ✓, a₁ at `6 < 7` ✓) — matching `.97`'s independent derivation ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2013–2031. correction sites: none.
**TEETH:** C5, FR2A, FR2B (u = N lifts at three cells including the first `k = 3` and first odd-q `k ≥ 2` cells).

---

### EFF.GENH4.102  [lemma]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M2 — the char-odd coset count completed). verbatim, lines 2033–2059.

> “### R2.M2 (MINOR-2): the 2w = N char-odd existence — the coset count completed
>
> Quoted target (R2, 2w = N, char odd): "if for EVERY square s and
> every d₀ the value s/4 − c·d₀ were a square, the set
> (squares ∪ {0}) of size (q²+1)/2 would be a union of full affine
> lines in direction c, each of size q — impossible since
> q ∤ (q²+1)/2." The negation of inert-existence covers only the
> cosets through the REALIZABLE s = S₁²/4 — the NONZERO squares (the
> pin letter is ≠ 0) — so the coset through 0 is not
> hypothesis-covered, and "union of FULL affine lines" of
> squares ∪ {0} has a half-step gap. Completed by the count route
> (adopted over the pass's alternative c = 1 route because it needs
> no input about the twist unit c): let Sq := the nonzero squares of
> F_{q²}, |Sq| = (q²−1)/2. Suppose no member of the key has an inert
> continuation at u = 2w: then for every S₁ ∈ F_{q²}^× and every
> d₀ ∈ F_q, S₁²/4 − c·d₀ is a square or zero. As S₁ sweeps F_{q²}^×,
> s := S₁²/4 sweeps Sq exactly (squaring is 2-to-1 onto Sq; 4 is a
> nonzero square, char odd), so every coset of the F_q-line c·F_q
> that meets Sq is contained in Sq ∪ {0} (its d₀ = 0 point is s
> itself, trivially a square). The q cosets of c·F_q partition
> F_{q²}; let U := the union of the cosets meeting Sq. Then
> Sq ⊆ U ⊆ Sq ∪ {0} and q divides |U|. If 0 ∈ U then U = Sq ∪ {0}
> and q | (q²+1)/2 ≡ 2⁻¹ (mod q) — false; if 0 ∉ U then U = Sq and
> q | (q²−1)/2 ≡ −2⁻¹ (mod q) — false. Contradiction either way:
> inert-continuation members EXIST at 2w = N, char odd — (c′)(ii)'s
> odd-characteristic input. The conclusion of the old display held;
> the quantifier now matches the negation.”

**CONDITIONALITY:** **A quantifier gap in a counting argument, closed by a cleaner count.** The old argument's conclusion held; its negation was mis-covered.
**SUPERSESSION KIND:** `replacement` (of the line-partition display by a coset count).
**ARITHMETIC AUDIT (compiler-computed):** `|Sq| = (q²−1)/2` ✓. `F_{q²}` has `q²` elements and the `F_q`-line `c·F_q` has `q` elements, so there are `q` cosets ✓, each of size `q`, and `q | |U|` ✓. If `0 ∈ U`: `|U| = |Sq| + 1 = (q²−1)/2 + 1 = (q²+1)/2` ✓, and `(q²+1)/2 ≡ (0+1)/2 = 2⁻¹ (mod q)` ✓, which is a unit mod q, so `q ∤ |U|` ✓ **contradiction**. If `0 ∉ U`: `|U| = (q²−1)/2 ≡ −2⁻¹ (mod q)` ✓, again a unit ✓ **contradiction**. **The count is exact and both branches close** ✓. Also: squaring on `F_{q²}^×` is 2-to-1 onto `Sq` in odd characteristic ✓, and 4 is a nonzero square ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2033–2059. correction sites: none.
**TEETH:** NONE — a counting proof. Disposition: **PROOF-ONLY**, feeding (c′)(ii), which is itself UNCONSUMED.

---

### EFF.GENH4.103  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M3 — the excluded-digit clause). verbatim, lines 2061–2077.

> “### R2.M3 (MINOR-3): the N-odd dμ₁ = w branch — the excluded-digit clause
>
> Quoted target (R2, N odd, band-pinned m ≤ 2w, dμ₁ = w): "the
> residual is separable in both characteristics, and any nonzero
> digit gives a decided '11'/'2' ≠ {(2,2)}." In char 2 this is exact
> (disc-analog = S₁ ≠ 0, every nonzero digit decided). In char odd,
> disc = S₁² − 4S₀ with S₀ = c·d₀ sweeping the line: disc = 0 ⟺
> d₀ = S₁²/(4c) — AT MOST ONE digit (realizable only when that value
> lies in F_q^×), and there the read is '1sq' (refine), not decided.
> The sentence reads corrected as: "…and any nonzero digit d₀ with
> c·d₀ ≠ S₁²/4 gives a decided '11'/'2' ≠ {(2,2)}; at most one digit
> is degenerate." Pair-existence survives at every odd q: char odd
> forces q ≥ 3, so among the q−1 ≥ 2 nonzero digits at least
> q−2 ≥ 1 is non-degenerate — the branch's differing pair (RAM(N)
> {(2,2)} vs a decided read) stands. The branch's machine instance
> (FR5 at (2,9,2), char 2: RAM(9) {(2,2)} vs decided
> {(1,2),(1,2)}/{(1,4)} on 9/9) sits on the exact side of the split.”

**CONDITIONALITY:** **An over-strong “any nonzero digit” corrected to “any non-degenerate nonzero digit”, with pair-existence preserved by a counting margin.**
**SUPERSESSION KIND:** `replacement` (a quantifier narrowed, with the corrected sentence displayed).
**ARITHMETIC AUDIT:** `disc = S₁² − 4S₀ = 0 ⟺ S₀ = S₁²/4 ⟺ c·d₀ = S₁²/4` ✓ — at most one `d₀` ✓. Odd q ⟹ `q ≥ 3` ⟹ `q−1 ≥ 2` nonzero digits, at least `q−2 ≥ 1` non-degenerate ✓ — **pair-existence survives at every odd q** ✓.
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2061–2077. correction sites: none.
**TEETH:** FR5 at `(2,9,2)`, 9/9 — **char 2, i.e. the side of the split where the original sentence was exact.**

---

### EFF.GENH4.104  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (R2.M4 — the header inventory corrected). verbatim, lines 2079–2088.

> “### R2.M4 (MINOR-4): the GENH4-7' header's inventory corrected
>
> Quoted target: "(GENH4-7 with the leaf's true floor … replaces
> GENH4-7's hypothesis sentence and clause (a)'s parenthetical,
> everything else unchanged)." The header UNDER-INVENTORIES its own
> supersession; it reads corrected as: "(… replaces GENH4-7's
> hypothesis sentence and clause (a)'s parenthetical, ADDS to (a) the
> band-nonzero cap u_lift ≤ m, and REPLACES clause (c)'s proof — the
> old two-lift witnesses withdrawn, the re-proof now (c′) in ANNEX
> R2; clause (b)'s conclusion and consumption unchanged)."

**CONDITIONALITY:** **A supersession inventory that under-counted its own changes — the exact defect class this compilation's `SUPERSESSION KIND` and `TARGETS` fields exist to prevent.** The corrected inventory lists four items where the original listed two.
**SUPERSESSION KIND:** `inventory completion`.
**TARGETS:** `.84` (the header).
**ARITHMETIC AUDIT:** original inventory: 2 items (hypothesis sentence; (a)'s parenthetical). Corrected: 4 (those two + (a)'s band cap + (c)'s proof) ✓, with (b) explicitly unchanged ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2079–2088. correction sites: none.
**TEETH:** NONE — an inventory repair.

---

### EFF.GENH4.105  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + two bulleted remarks (R2.REM). verbatim, lines 2090–2103.

> “### R2.REM (the two pass remarks, folded)
>
> * **Remark 1 (R3's consumption-audit sentence), ridered:** "S7's
>   resolvent chain … all run in L/O_L verbatim" is loose — S7's
>   Y-trichotomy runs in the quartic root field base(θ_F), not in
>   L = Frac(R); the facts consumed there are covered by S7's own
>   displayed transport ((F) v(θ) = k, res(θπ^{−k}) a root of ψ) plus
>   the R6 rider, while the genuinely L-resident part (the norm
>   identity over the key's roots) is covered as stated. No consumer
>   moves.
> * **Remark 2 (R2's char-2 trace argument at 2w = N):** re-derived
>   SOUND by the annex pass (trace transitivity, Frobenius sweep,
>   trace-kernel count); no edit owed — recorded so that (c′)(ii) can
>   cite it as pass-verified.”

**CONDITIONALITY:** **Remark 1 riders a rider's audit sentence — a third-order correction** (R3 audits the body; R2.REM audits R3's audit). **Remark 2 is a positive verification recorded so a later clause can cite it** — the corpus's cleanest instance of a pass certifying an argument rather than finding a defect.
**SUPERSESSION KIND:** Remark 1 = `scope-pin` on `.89`'s audit sentence; Remark 2 = none (a certification).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2090–2103. correction sites: none.
**TEETH:** Remark 2 IS a tooth of the AUDIT class (`in-house hostile pass`, positive result).

---

### EFF.GENH4.106  [changes-record] · **SERIES GENH4-BOX-1, entry 3 of 3 (post-annex-pass-1)**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 2105–2127.

> “**GENH4-BOX-1 (arc record) — dated APPEND (2026-08-09,
> post-annex-pass-1).** Continuing the record: **the first hostile
> annex pass HAS NOW RUN (GENH4_annexpass_report.md, fresh context,
> commits 6cb147b/fed3cff/a8dec16) — outcome NOT CLEAN: 0 CRITICAL +
> 1 GAP + 4 MINOR + 2 remarks; the annex-acceptance count stays 0/2
> (pass #2 attempts the first clean). GAP-1 machine-refuted R2's
> N-even band-pinned and refine-deeper legs (FR4: the 6 refine-path
> lifts at (2,10,2) read {(2,2)} 6/6 against the displayed 2SIDED′;
> the (2,8,2) u = N read structurally unrealizable); THIS ANNEX R2
> withdraws both legs and restates clause (c) as (c′) at the key
> level (band-zero witnesses; cross-stratum contrast — the form the
> pass confirmed 6/6 + 6/6 at the same keys), and lands the four
> minors (realizability scoped to N ≥ 4k+1; the coset count
> completed; the excluded-digit clause; the header inventory) plus
> the Remark-1 rider. The consumed surface was independently
> RE-DERIVED CLEAN by the pass (GENH4-7'(b) + the supersession +
> R3/R4/R5 + PE5's A2/A3); both annex machine legs re-ran isolated
> GREEN (PE5 bit-identical, R elapsed-only); the pass's fresh leg
> exercised the first k = 3 cell (2,15,3) and the first odd-q k ≥ 2
> cell (3,11,2), 48/48 + 48/48 σ with teeth 4/4 and the 54-cell grid
> tie. The frozen body's ACCEPTED 2/2 is untouched; conditionality is
> otherwise exactly the S11 stack plus the queued GENHN.A(i)
> transport erratum (R3).**”

**CONDITIONALITY:** **The consumed surface was independently RE-DERIVED CLEAN by the pass** — the single most reassuring sentence in the annex stack, and the reason the machine refutation of (c) costs nothing downstream. **The frozen body's ACCEPTED 2/2 is untouched.**
**SUPERSESSION KIND:** `counter re-reading` (the annex-stack counter stays 0/2).
**ARITHMETIC AUDIT:** two new cells at 48/48 each ✓; the “6/6 + 6/6 at the same keys” is corrected to “6/6 TOTAL, 3 per cell” by MINOR-3 (`.111`) — **so this append's own figure is one of the three the next pass corrects.**
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2105–2127. correction sites: 2168–2173 (MINOR-3).
**TEETH:** the pass's fresh leg (first `k = 3`, first odd-q `k ≥ 2`, 54-cell grid tie, teeth 4/4).

---

### EFF.GENH4.107  [fence] · **SERIES WHAT-DOES-NOT-MOVE, entry 3 of 3**

**CANONICAL STATEMENT:** FORM: bold-headed paragraph. verbatim, lines 2129–2140.

> “**What does not move (ANNEX R2).** Every displayed statement,
> proof, and frozen number of the accepted body, ANNEX PE5, and ANNEX
> R except the five named targets (R2's two withdrawn legs → (c′);
> 7'(a)'s realizability parenthetical + R2's two u-geography
> sentences → R2.M1; R2's char-odd line-partition display → R2.M2;
> R2's dμ₁ = w separability sentence → R2.M3; the GENH4-7' header
> inventory → R2.M4) and the one rider (R2.REM Remark 1, on R3's
> audit sentence); ANNEX-LEMMA GENH4-7' clauses (a)-floor and (b) —
> their proofs and the W-12.D supply row are untouched by every item
> here; the sealed runner and all committed artifacts and pins; every
> committed key count and the eleven densities; GENH4-BOX-2 (n = 5's
> embedded CS genres stay OPEN).”

**CONDITIONALITY:** **Five named targets, one rider, and an explicit statement that (a)-floor and (b) — the consumed clauses — are untouched by every item.**
**ARITHMETIC AUDIT:** five targets enumerated ✓ (`.99`, `.101`, `.102`, `.103`, `.104`) + one rider ✓ (`.105`) — **six items, all emitted as units here** ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2129–2140. correction sites: none.
**TEETH:** NONE.

---

### EFF.GENH4.108  [changes-record]

**CANONICAL STATEMENT:** FORM: heading + paragraph (the post-annex-pass-2 corrections' frame). verbatim, lines 2142–2150.

> “### Dated corrections (2026-08-09, post-annex-pass-2)
>
> Provenance: the three MINORs of the annex-pass-2 verdict
> (GENH4_annexpass2_report.md, commit d6a9ac8 — 0 CRITICAL + 0 GAP +
> 3 MINOR at annex-stack scope; the stack's clean count HOLDS at 1/2
> through this minors-only round, the HE7-r3 precedent). Each
> one-liner names its exact display target above; byte-freeze
> verified: the pre-annex prefix (128,564 bytes, md5 `22b766d3…`) is
> byte-identical before == after this append.”

**CONDITIONALITY:** **The terminal state of the whole note: body ACCEPTED 2/2 (annotated); annex stack at 1/2 through a minors-only round.** “the stack's clean count HOLDS at 1/2 through this minors-only round, the HE7-r3 precedent” — **a minors-only round does not break a clean count**, by corpus precedent.
**SUPERSESSION KIND:** `counter re-reading` (the annex-stack counter 0/2 → 1/2).
**SERIES:** GENH4-BOX-1's terminal state (though this record is not itself a BOX-1 append).
**ARITHMETIC AUDIT:** three MINORs, three one-liners ✓ (`.109`, `.110`, `.111`).
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2142–2150. correction sites: **none — this is the note's terminal text region.**
**TEETH:** `in-house hostile pass` at annex scope, CLEAN of GAPs.
**PIN VERIFICATION:** `d6a9ac8` ✓; `lean/notes/openmath/GENH4_annexpass2_report.md` — **verified to EXIST ✓**; `verification/openmath/genh4annexpass2_fresh.*` ✓ EXIST (3 files), **and `genh4annexpass3_fresh.*` ✓ also exist** — a third annex pass's leg, **cited nowhere in the note** (recorded, §8 defect 1).

---

### EFF.GENH4.109  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (post-pass-2 MINOR-1 — a provenance pin transcription). verbatim, lines 2152–2158.

> “* **MINOR-1 (ANNEX R2 provenance pin).** R2's fresh-leg results pin
>   "results `71535780…`" reads for `7153578c…` — the committed
>   `genh4annexpass_fresh_results.json` has md5
>   `7153578c0948d773830f58c193dcb62d`, the blob at fed3cff (the
>   commit R2 cites) == HEAD with a single-commit history
>   (re-verified before this append): a transcription slip in the
>   displayed pin; the machine record is intact.”

**CONDITIONALITY:** **A one-character md5 transcription slip** — the same defect class GENIND's shard 2 `.58` records (`e5493312` → `e549331a`). **Two independent notes in this corpus have now had a quoted md5 prefix corrupted; the artifact never moved in either case.**
**SUPERSESSION KIND:** `provenance-rider` (a pin transcription; nothing about the artifact or any claim changes).
**TARGETS:** `.96`.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2152–2158. correction sites: none.
**TEETH:** `arithmetic recount` at the byte level (a commit-time md5 re-verification), plus a blob-vs-HEAD check with a single-commit history.
**PIN VERIFICATION:** `fed3cff` ✓; `genh4annexpass_fresh_results.json` ✓ EXISTS.

---

### EFF.GENH4.110  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (post-pass-2 MINOR-2 — the (c′) disc parenthetical in equal characteristic 2). verbatim, lines 2159–2167.

> “* **MINOR-2 ((c′) proof parenthetical).** (c′)(i)'s "disc ≠ 0 is
>   automatic at both witnesses (v(4A₀) = u + 2v(2) is odd either
>   characteristic, ≠ 2w = v(A₁²), so v(disc) < ∞)" fails in EQUAL
>   characteristic 2 (4A₀ = 0, so v(4A₀) = ∞, not odd); the
>   conclusion holds by the one-line route disc = A₁² − 4A₀ = A₁²
>   with v(disc) = 2w < ∞ (A₁ ≠ 0 since dv(A₁) = w is pinned finite)
>   — machine-confirmed by the pass's FAeq equal-char leg 4/4 (exact
>   F₂[t]-gcd disc ≠ 0 + Panayi roots on the F₂[[t]] witnesses at
>   (2,7,2) and (2,12,2)).”

**CONDITIONALITY:** **A characteristic-2 degeneration in a parenthetical, with the conclusion preserved by a one-line alternative route and machine-confirmed.**
**SUPERSESSION KIND:** `replacement` (of a proof parenthetical; the clause's conclusion is unchanged).
**TARGETS:** `.99`'s proof.
**ARITHMETIC AUDIT (compiler-computed):** in equal characteristic 2, `4 = 0` so `4A₀ = 0` and `v(4A₀) = ∞` ✓ — **the original parenthetical genuinely fails** ✓. The replacement: `disc = A₁² − 4A₀ = A₁²` in char 2 ✓, and `v(A₁²) = 2·v(A₁) = 2w < ∞` since `dv(A₁) = w` is a finite pin ✓ — **so `disc ≠ 0`** ✓. **Both the failure and the repair check.**
**DERIVATION:** Displayed.
**RESOLUTION TRACE:** statement lines 2159–2167. correction sites: none.
**TEETH:** the pass's FAeq equal-char leg, 4/4, with exact `F₂[t]`-gcd and Panayi root counts at two cells.

---

### EFF.GENH4.111  [changes-record]

**CANONICAL STATEMENT:** FORM: bulleted display (post-pass-2 MINOR-3 — a machine-instance count). verbatim, lines 2168–2173.

> “* **MINOR-3 (ANNEX R2 machine-instance count).** The
>   consumption-status sentence's "(6/6 at each cell)" reads for
>   "6/6 TOTAL, 3 per cell" — the committed fresh leg builds 3
>   band-zero contrast pins at (2,8,2) + 3 at (2,10,2); the substance
>   is intact ((c′) needs ≥ 1 contrast member per cell, and each of
>   the two FR4 cells carries 3/3).”

**CONDITIONALITY:** **A count overstated by a factor of two, with the substance preserved because the requirement is `≥ 1` per cell.** **This is the note's last word** (line 2173 is the file's last line).
**SUPERSESSION KIND:** `counter re-reading` (a machine-instance count corrected).
**TARGETS:** `.100`, `.106`.
**ARITHMETIC AUDIT:** `3 + 3 = 6` ✓ TOTAL, against the claimed `6` per cell (which would be 12) ✓ — **a factor-2 overstatement** ✓; and `(c′)` needs `≥ 1` contrast member per cell ✓, so `3/3` at each suffices ✓.
**DERIVATION:** Not a mathematical unit.
**RESOLUTION TRACE:** statement lines 2168–2173. correction sites: **none — terminal.**
**TEETH:** `arithmetic recount`.

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`)
against the target note or artifact at merge time; counts shown are the re-verified counts.
Shard 1's table lists 23 rows grouping related designations (some rows carry two or more
slash-separated grep patterns under one accounting entry) and states "**27 distinct
designations across nine supplier notes**" in its header and again in its fidelity audit.
**Compiler arithmetic note (a merge-level finding, not present in either shard's own
fidelity audit):** a literal count of shard 1's table — either by row (23) or by individual
slash-separated grep pattern (33) — does not reproduce "27" under either convention this
merge could identify; the discrepancy is flagged here rather than silently resolved, since
no count-table claim should be taken on faith once this merge's rule-22 arithmetic-audit
obligation applies to it. **No designation's own count is in question** — every individual
grep count re-verified clean (see the ten-sample re-grep below); only the shard's own
*summary tally* of how many rows/patterns that constitutes is unreconciled.

Shard 2 cites only **3 designations**, of which **2 are cited identically by shard 1**
(`THEOREM W-12.D` and `THEOREM W-12.A`, both counts agreeing exactly — a fixed-string grep
against an unchanged file must return the same count regardless of who runs it, and both do)
and **1 is new** (`GENHN_PROOF_2026-08-08.md:GENHN.A(i)`, count 11, shard 2's own `.90`).

`[TABLE — compiler ledger]`

| # | Target : designation | Count | Role | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|
| 1 | `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-4` | 4 | The E-genre stage fibration lemma | s1 | — |
| 2 | `GENIND_PROOF_2026-08-08.md:GENIND-5` | 9 | The candidate box GENH4 discharges at n=4 | s1 | — |
| 3 | `GENIND_PROOF_2026-08-08.md:CANDIDATE THEOREM GENIND-5` | 1 | Same candidate, alternate designation form | s1 | — |
| 4 | `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` | 7 | The induction GENH4 fires at n=4 | s1 | — |
| 5 | `GENIND_PROOF_2026-08-08.md:GENIND.A(IV)` | 5 | Genre-completeness input | s1 | — |
| 6 | `GENIND_PROOF_2026-08-08.md:S5.1` | 21 | Genre-completeness grammar | s1 | — |
| 7 | `GENIND_PROOF_2026-08-08.md:S5.3` | 26 | Genre-completeness grammar | s1 | — |
| 8 | `GENIND_PROOF_2026-08-08.md:GENIND-1` | 15 | d≥2/prime-power coverage supplier | s1 | — |
| 9 | `GENIND_PROOF_2026-08-08.md:GENIND-2` | 27 | Same | s1 | — |
| 10 | `GENIND_PROOF_2026-08-08.md:GENIND-3` | 37 | Same | s1 | — |
| 11 | `QSCOUT22_2026-08-08.md:Q22-L1` | 3 | The composite count law this note proves | s1 | — |
| 12 | `QSCOUT22_2026-08-08.md:Q22-L2` | 3 | The refine transfer this note proves | s1 | — |
| 13 | `QSCOUT22_2026-08-08.md:Q22-L3` | 3 | The drainage law this note proves (and corrects) | s1 | — |
| 14 | `QSCOUT22_2026-08-08.md:Q22-A` | 3 | Composite entry classification | s1 | — |
| 15 | `QSCOUT22_2026-08-08.md:Q22-PRE` | 3 | Prehistory composition family | s1 | — |
| 16 | `QSCOUT22_2026-08-08.md:Q22-BOX-3` | 1 | Inherited d≥2 coverage hole | s1 | — |
| 17 | `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | The cell law GENH4's count laws instantiate | s1+s2 | **DEDUP** |
| 18 | `W12_PROOF_2026-08-08.md:THEOREM W-12.D` | 5 | The consumer of the eleven densities and the σ-labelling supply | s1+s2 | **DEDUP** |
| 19 | `W12_PROOF_2026-08-08.md:S2.5` | 9 | Entry-volume law | s1 | — |
| 20 | `W12_PROOF_2026-08-08.md:S2.1` | 23 (upper bound) | Hull trichotomy over K | s1 | — |
| 21 | `W12_PROOF_2026-08-08.md:W12-L0` | 32 | Re-pinned entry laws | s1 | — |
| 22 | `W12_PROOF_2026-08-08.md:W12-L1` | 30 | Re-pinned entry laws | s1 | — |
| 23 | `W12_PROOF_2026-08-08.md:[W12-H]` | 17 | The general σ-decision program GENH4 proves an instance of | s1 | — |
| 24 | `W12_PROOF_2026-08-08.md:σ-LABELING` | 7 | The clause GENH4.C supplies | s1 | — |
| 25 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | The n=2 system every stage transports | s1 | — |
| 26 | `HMENU3_PROOF_2026-08-08.md:HM3.D` | 13 | The n=3 density template GENH4.D's ν₃ instantiates | s1 | — |
| 27 | `HEX3_PROOF_2026-08-08.md:S8.2` | 10 | HEX3 aside GENH4 never consumes | s1 | — |
| 28 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | Mechanism frame, not consumed (re-proved elementarily) | s1 | — |
| 29 | `GRTJC_PROOF_2026-08-08.md:W-8` | 35 | Mechanism frame, not consumed | s1 | — |
| 30 | `GRTJC_PROOF_2026-08-08.md:W-9` | 13 | Mechanism frame; the z̄-twist DERIVED, not consumed | s1 | — |
| 31 | `GRTJC_PROOF_2026-08-08.md:COROLLARY W-9` | 2 | Cited as frame at S2.1 | s1 | — |
| 32 | `JD0_PROOF_2026-08-08.md:J-D0` | 25 | Mechanism frame; count-blindness made literal, not consumed | s1 | — |
| 33 | `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | Applicability checked, NOT consumed | s1 | — |
| 34 | `GENHN_PROOF_2026-08-08.md:GENHN.A(i)` | 11 | Target of the queued carrier-rename erratum | s2 | — |

**34 distinct rows after dedup — every row a distinct `target:designation` pair** (2 of them,
`W-12.A` and `W-12.D`, cited independently by both shards with exactly agreeing counts and
DEDUP-marked; 1 new from shard 2, `GENHN.A(i)`), across **ten supplier notes** (shard 1's
nine — GENIND, QSCOUT22, W-12, W-11, HMENU3, HEX3, GRTJC, JD0, DULEMMA — plus shard 2's
GENHN). All other citations inside shard 2 (`GENH4-2`,
`GENH4-3`, `GENH4-4`, `GENH4-6`, `GENH4-CAP`, `GENH4-1F`, `S2.1`, `S6.1`, `S6.3`, `S7`,
`S11`, `S2.3`) resolve to shard-1 unit IDs and are **not emitted as XREFs**, per shard 2's
own §3.1.

**Non-designation dispositions carried forward:**

- `GENIND-1(ii)` — count **0** in `GENIND_PROOF_2026-08-08.md` (which writes the clause
  label `(ii)` inside its lemma display, not as a grep-matchable token); verified parent
  `LEMMA GENIND-1` count 2, `GENIND-1` count 15. **NEAR-MISS**, carried descriptively
  (shard 1, three sites).
- `P-11` — this note's preregistration is P-1…P-9; `P-11` does not exist here (it is
  GENIND's numbering). Source defect, carried below.
- `om_density_engine.py` — md5-pinned but **not present** in `verification/openmath/`.
  Source defect, carried below.
- `W-2/LIFTCORNER` — named but explicitly NOT consumed; no designation is cited.
- `71535780…` — shard 2's own results-pin transcription slip, self-corrected in-note at
  its own `.109`.

### Sample re-verification (10 designations, grep-rerun at merge time against the working tree)

`[TABLE — compiler ledger]`

| Target : designation | Recorded count | Re-verified count | Match |
|---|---:|---:|---|
| `GENIND_PROOF_2026-08-08.md:LEMMA GENIND-4` | 4 | 4 | OK |
| `GENIND_PROOF_2026-08-08.md:THEOREM GENIND.B` | 7 | 7 | OK |
| `QSCOUT22_2026-08-08.md:Q22-L1` | 3 | 3 | OK |
| `W12_PROOF_2026-08-08.md:THEOREM W-12.D` | 5 | 5 | OK |
| `W12_PROOF_2026-08-08.md:THEOREM W-12.A` | 8 | 8 | OK |
| `GRTJC_PROOF_2026-08-08.md:W-9` | 13 | 13 | OK |
| `HEX3_PROOF_2026-08-08.md:S8.2` | 10 | 10 | OK |
| `GENHN_PROOF_2026-08-08.md:GENHN.A(i)` | 11 | 11 | OK |
| `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | 1 | OK |
| `JD0_PROOF_2026-08-08.md:J-D0` | 25 | 25 | OK |

**All 10 sampled counts match exactly; no drift introduced by sharding or merge.** The
sample deliberately includes both dedup rows (`W-12.D`, `W-12.A`, confirming both shards'
independent counts agree) and the sole shard-2-only designation (`GENHN.A(i)`).

### Sample statement-quote re-verification (5 of 111, checked verbatim against the source note by line number)

`[TABLE — compiler ledger]`

| Statement | Quoted fragment | Source lines | Match |
|---|---|---|---|
| `.01` (title/unit) | "# GENH4 — [GENIND-H(4)] DISCHARGED AT BOTH QUARTIC GENRES …" / "**Unit:** GENH4, the [GENIND-H(4)] prover … **Attempt grade 0/2**" | 1, 3–5 | OK, byte-exact |
| `.08` (the CRITICAL) | "**[r2 2026-08-08 (PE2 CRITICAL 1) — the census clause corrected.** The sealed display read \"Q−1 for RAM and per 2SIDED pin\": FALSE at genre-F boundary-band pins …" | 118–121 | OK, byte-exact |
| `.69` (=s2.01, ANNEX PE5 open) | "## ANNEX PE5 (2026-08-09, post-acceptance) … **Provenance and scope.** GENH4 was **ACCEPTED 2/2** at PE5 …" | 1209–1212 | OK, byte-exact |
| `.84` (=s2.16, ANNEX-LEMMA GENH4-7′ open) | "**ANNEX-LEMMA GENH4-7' (GENH4-7 with the leaf's true floor — the free boundary band quantified …" | 1537–1540 | OK, byte-exact |
| `.111` (=s2.43, MINOR-3, terminal) | "* **MINOR-3 (ANNEX R2 machine-instance count).** The consumption-status sentence's \"(6/6 at each cell)\" reads for \"6/6 TOTAL, 3 per cell\" …" | 2168–2173 | OK, byte-exact — **the file's last 6 lines** |

**All 5 sampled quotes are byte-identical to the source note at the cited lines; no drift
introduced.** The sample covers both shards' HOME ranges, the sole CRITICAL, the annex
stack's opening sentence, and the note's terminal line (2173 total, confirmed by `wc -l`).

### 3.2 Pin verification (rule 23, consolidated)

**Every commit hash cited across both shards was `git cat-file -t`-verified at merge time;
all resolve as `commit`.** Shard 1: 45/45 (listed in full at shard 1 §3.2). Shard 2: 12/12
(`11dbd23`, `4b0d946`, `e15308d`, `cceca77`, `e945734`, `6272cd4`, `6cb147b`, `fed3cff`,
`a8dec16`, `ca3754d`, `d6a9ac8`, plus `65681144`). **Four hashes are cited by both shards**
(`11dbd23`, `4b0d946`, `e15308d` appear in shard 1's own §3.2 list, explicitly flagged there
as "shard-2-resident" commits shard 1 names when resolving in-range material against
out-of-range annex events, and again as shard 2's own primary pins; `ca3754d` likewise) —
all four agree, and shard 1's 45-count already includes them once. **Distinct total: 45
(shard 1) + 8 new (shard 2's 12 minus the 4 already counted) = 53 distinct commit hashes
verified across the merge, 0 failures.**

**Reports verified to EXIST:** `GENH4_passPE5_report.md` ✓, `CODEX_GENH4RAT_2026-08-09.md`
✓, `GENH4_annexpass_report.md` ✓, `GENH4_annexpass2_report.md` ✓ — 4/4 (all shard 2's own;
shard 1 cites no report file directly by name).

**Machine legs verified to EXIST** (`verification/openmath/`): shard 1's 11 files (the
sealed battery + both RED-run artifacts + smoke pair + the `genh4r2_supp.*` additive leg +
the qscout22 pair) plus shard 2's 12 files (`genh4annex_supp.*`, `genh4annexr_supp.*`,
`genh4annexpass_fresh.*`, `genh4annexpass2_fresh.*`) — **23/23**, plus 3 more
(`genh4annexpass3_fresh.*`) that exist but are **cited nowhere in the note** (a shared
finding, both shards' §8 flag it identically — see the merged self-audit below).

**Non-commit hashes (md5s), correctly not treated as pins:** the union of both shards' lists
(the frozen-body/annex/battery md5s and artifact md5s); none collide in a way that would
suggest a duplicate artifact under two names.

### 3.3 NEAR-MISS dispositions (rule 15, consolidated)

| As cited | Count | Verified referent | Disposition | Shard |
|---|---:|---|---|---|
| `GENIND-1(ii)` | 0 | Parent `LEMMA GENIND-1` count 2, `GENIND-1` count 15; the clause is GENIND's own unit `.18` | Carried descriptively | s1 |
| `P-11` | n/a | This note's preregistration is P-1…P-9; `P-11` is GENIND's numbering. Invoked clause exists here verbatim at `.63` | Source defect 1 | s1 |
| `om_density_engine.py` | n/a | md5-pinned; not present in `verification/openmath/` | Source defect 2 | s1 |
| `W-2/LIFTCORNER` | n/a | Named-but-not-consumed; no designation cited | Not emitted as an XREF | s1 |
| `71535780…` | n/a | Committed file's md5 is `7153578c…` | The note corrects it itself at `.109` | s2 |
| internal `S2.1`, `S6.1`, `S6.3`, `S7`, `S11`, `S2.3` | n/a | Self-references into shard 1's own units | Resolved to shard-1 unit IDs, not emitted as XREFs | s2 |

**6 near-misses total (4 shard 1 + 2 shard 2), matching both shards' own COMPILED-line
counts exactly.**

### 3.4 Reverse consumer edges (consolidated)

| Party | Direction | What crosses | Protocol | Shard |
|---|---|---|---|---|
| GENIND | outbound supply | `[GENIND-H(4)]` DISCHARGED; GENH4.A/B; GENH4.D fires P(4) | Nothing appended; GENIND cites this note at its own pins | s1 |
| W-12 | outbound supply | THEOREM GENH4.C IS the σ_F assignment W-12's r4 clause needs; RESTORED over the whole counted family by GENH4-7′(b) | Nothing appended; both checks quoted from W-12's own table | s1+s2 |
| QSCOUT22 | outbound finding | GENH4-BOX-7: the genre-E UND display is wrong at h > 1 | Offered as a fold obligation, not landed; discharged at the source (annex `fcaf268`, per GENIND's record) | s1 |
| GENHN | outbound erratum, QUEUED | the stage-ring carrier rename (R3) | Queued to GENHN's own ratification round; not landed; discharged at the source (GENHN `46bf675`, per GENIND's record) | s2 |
| W-12 / HEX3 / HMENU3 / W-11 / GENIND / QSCOUT22 | inbound | arc-grade movement, tracked and re-checked three times | `.44`, `.51`–`.57` | s1 |
| Codex ratification / annex pass #1 / annex pass #2 | inbound | 5 findings CHALLENGE; 1 GAP + 4 MINOR (one a machine refutation); 3 MINOR | Repaired in-place by R1–R6, ANNEX R2, the dated corrections | s2 |

**Zero appends are claimed landed on any supplier by either shard.** Both outbound errata
(QSCOUT22's fold obligation, GENHN's queued transport) were independently confirmed
discharged at the source via GENIND's own record — a genuine cross-note consistency check,
not asserted from within this note (which is frozen and cannot know it).

---

## 4. NON-IMPORTS (consolidated)

| Fence | Material NOT imported / NOT claimed | Unit(s) |
|---|---|---|
| No weld face | "no weld face sits inside any count law below"; every count-load-bearing input re-proved elementarily | `.05`, `.19`, `.20`, `.23`, `.57` |
| DULEMMA | applicability checked on both sides of its perimeter, **not consumed** | `.05`, `.57` |
| W-2/LIFTCORNER | "the W-2/LIFTCORNER seam NOT consumed" | `.06`, `.48` |
| Model functions | "the MODEL functions are NOT called — this note's laws are re-implemented from S6" | `.58` |
| The density engine | "'independent' means decorrelated method, not accepted-arc supplier … corroboration legs" | `.49`, `.56` |
| General (H-e) | "remains [W12-H]'s open box"; **"P(5) does NOT fire from this note"** | `.45` |
| P-D above n = 4 | "At stages with m′ ≥ 3 or E ≥ 3 slot misalignment is not ruled out" | `.47` |
| d ≥ 2 / q = 4 | genre-F rows at q = 4 unbuilt (F₁₆ kit); thin d = 2 coverage inherited | `.46` |
| GH-CROSS | a cross-check row "considered and DROPPED for runtime budget — disclosed" | `.59` |
| No fresh reader | "this note's battery contributes independent LAWS … not a fresh reader" | `.48` |
| Teeth ≠ theorems | "a dead tooth voids the battery, not the theorems" | `.63` |
| No full run pre-seal | "No full-roster run before the seal." | `.61` |
| Annex grade (×3) | "the annex text itself is a post-acceptance append and has NOT been through a hostile pass" | `.69`, `.82`, `.96` |
| Annex-stack counter | 0/2 → **1/2** through a minors-only round | `.96`, `.108` |
| Acceptance annotation | "The ACCEPTED 2/2 grade stands ANNOTATED by the fold note pending Asvin's read" | `.94` |
| Clause (c)/(c′) | UNCONSUMED — "W-12.D's supply row consumes clause (b) only … no consumer moves under this correction" | `.87`, `.100` |
| Two withdrawn legs | "Both are FALSE as within-stratum claims" | `.97`, `.88` |
| No within-stratum pair | "NO within-stratum pair is claimed at band-pinned strata with m ≤ 2w" | `.99` |
| Honest scope at 2w = N | τ-degenerate members; "a finer reader … would be a menu REFINEMENT" | `.87`, `.100` |
| Transport erratum queued | "QUEUED (not executed here)" | `.90` |
| n = 5 stays open (×3, both shards) | GENH4-BOX-2 re-asserted in all three what-does-not-move declarations plus shard 1's own box | `.45`, `.81`, `.95`, `.107` |
| Nothing above edited (×4 freezes) | four byte-freezes, four byte counts, each verified before and after | `.69`, `.82`, `.96`, `.108` |

**Cross-shard consistency:** shard 1's `.45` (GENH4-BOX-2) and shard 2's `.81`/`.95`/`.107`
(the three what-does-not-move declarations) all name the identical fence — n = 5's embedded
CS genres stay open — with no drift in wording across four independent restatements.

---

## 5. Teeth inverse table (unified from both shards)

### 5.1 Shard 1's battery (IDs unchanged, offset 0)

| Family / tooth | Guarded units | Disposition |
|---|---|---|
| **GH-PIN** 6/0 | `.04`, `.52`, `.56` | Executable regression on artifact md5s |
| **GH-JSONTIE** 481/0, all 23 committed rows, both directions | `.07`, `.19`, `.21`, `.25` | Executable regression against a foreign md5-pinned table |
| **GH-FRESH** 54/0, seven never-measured rows | `.06`, `.07`, `.25`, `.62` | Executable regression on fresh territory |
| **GH-PRE2** 5/0 | `.16` | Executable regression (depth-2 chain) |
| **GH-REFINE** 192,000/0, 22,272 refine events | `.09`, `.23`, `.24`, `.31` | Pointwise executable regression — the carry computation's guard |
| **GH-FEVEN** 8/0 (run 2) | `.15`, `.20`, `.62` | Constructed odd-q even-dμ F stratum; **the row whose generator caused the RED** |
| **GH-PD** 46,590/0 | `.34`, `.35` | Executable regression (liveness scan + AS-degeneration + both cascade rows) |
| **GH-UND** 92/0 | `.10`, `.27` | Executable regression incl. the h=3 correction value and the even-N two-term law |
| **GH-BRACKET** 157/0 | `.26` | Symbolic identity regression |
| **GH-DENS** 115/0 | `.37`, `.39`, `.40`, `.41`, `.42`, `.43` | Symbolic + engine tie + finite-window sandwiches on 9 rows |
| **GH-SIGMA** 6,185/0 (PARI) + 35,380 committed at pin | `.11`, `.28`–`.33` | Mechanism-free decorrelated oracle |
| **GH-T-LAT/CEN/ALPH/SIG/DENS** (5 mutants) | `.17`, `.07`, `.20`, `.11`, `.39` | All fired at both runs (19/14/4/2/1) |
| Pre-seal smoke (GREEN, 3 disclosed corrections) | `.35`, `.61` | Fired before the seal |
| PE2's ledger-closure recount (216/216 + 288/288) | `.08` | **AUDIT: `arithmetic recount`** — found the CRITICAL no run could |
| PE2's isolated full re-run (245,693/0) | `.67`, `.68` | Independent reproduction by a hostile verifier |
| PE3's substance verification | `.08`, `.18`, `.38`, `.53` | **AUDIT: `in-house hostile pass`** |
| `genh4r2_supp.py` (GREEN, tooth fired) | `.38` | Additive leg executing a previously-tautological tie |
| Compiler arithmetic audits (31 units) | `.06`–`.65`, `.67` (full list at shard 1 §5) | **AUDIT: `arithmetic recount`** — all agree |

**PROOF-ONLY (shard 1):** `.30` (F-SPLTAIL leg — machine contact annex-resident only), `.05`
(weld-corpus division), `.45`/`.47` (open boxes), `.14` (carrier frame). **Zero orphans** in
shard 1's own both-direction audit.

### 5.2 Shard 2's instruments (renumbered, offset +68)

| Instrument / audit | Guarded units | Disposition |
|---|---|---|
| `genh4annex_supp.py` C0–C6 (GREEN after a disclosed RED-and-repair) | `.71`–`.79` | Executable regression + two fired teeth |
| `genh4annexr_supp.py` C0–C7 (GREEN, 0.4 s + PARI) | `.83`–`.86` | The k ≥ 2 slice's FIRST exercise; C6 first char-p σ contact; C7 4/4 |
| `genh4annexpass_fresh.py` FR2A/FR2B/FR4/FR5/FAeq (GREEN) | `.87`, `.97`–`.101`, `.103`, `.106`, `.110` | Foreign-note (verifier) evidence incl. a MACHINE REFUTATION (FR4: 6/6 and 24/24) |
| `genh4annexpass2_fresh.*` | `.108`–`.111` | Foreign-note evidence for the three minors |
| Pass's re-derivation of the consumed surface | `.84`(b), `.85` | **AUDIT: `in-house hostile pass`, positive result** |
| R2.REM Remark 2 (char-2 trace argument) | `.99`(ii), `.105` | **AUDIT: positive certification** |
| Isolated re-runs of both annex legs | `.79`, `.86`, `.106` | Reproduction by a hostile verifier |
| Compiler arithmetic audits (31 units) | `.71`–`.111` (full list at shard 2 §5, offset +68) | **AUDIT: `arithmetic recount`** — all agree |

**PROOF-ONLY (shard 2):** `.102` (coset count, feeding an unconsumed clause), `.99`(ii)
(existence inputs are `.102` and a pass-verified trace argument), `.89`/`.90` (frame and
queued erratum). **Zero orphans** in shard 2's own both-direction audit.

**Cross-shard note:** the two batteries never guard the same unit (shard 1's IDs 1–68 and
shard 2's 69–111 partition the tooth-guard space exactly as they partition the source lines)
— there is no double-guarding to reconcile and no gap at the seam (shard 1's `.68` closing
record and shard 2's `.69` opening record are the two halves of the same acceptance event,
cross-referenced in both directions).

---

## 6. BOUNDARY SELF-AUDIT (both shards' rule-9 audits, carried whole)

Both shards report zero `\tag{` occurrences in the source note; every unit boundary below
was a compiler choice, defended by the same four-part test (proof obligation / cited by
designation / own supersession history / own conditionality or consumer set) both shards
inherited from the HE7 pilot.

### 6.1 Shard 1 (the accepted body, `.01`–`.68`)

Full text carried from shard 1 §6 verbatim (IDs already offset-0, unaffected by the merge):
nine numbered boundary calls (§S1's five statements + CRITICAL box + scoreboard; §S7's
trichotomy as one unit with four flagged second emissions `.29`–`.32`; §S2.1 kept whole
despite three false sentences; three double-emitted ASCII displays; §S10's seven boxes;
§S11's seven bullets; §S12's six units + placeholder; §S13's four units; proofs emitted as
units only at `.23`/`.25`), five deliberately-not-made merges, and five format-feedback
items (rule 14 fired three times; rule 13's `supplier-finding` earned its place; the
second-emission device needs a `SUB-EMISSION OF:` field; rule 22's arithmetic audit found
two non-mathematical source defects; the RED-verdict pattern deserves its own disposition
label, `published-red-with-diagnosis`). **See `spec/EFF-GENH4-s1of2.md` §6 for the full
prose — reproduced there in full and not re-typed here to avoid a second byte-fidelity risk
on already-verified text.**

### 6.2 Shard 2 (the annex stack, `.69`–`.111`, local `.01`–`.43`)

Shard 2 reports the boundary problem was **unusually easy**: the source's own numbered
sub-headings (A1–A4, R1.0–R1.2, R2–R6, R2.G1, R2.M1–M4, R2.REM, MINOR-1–3) are author-supplied
boundary markers, and every unit below corresponds to one heading or one named object inside
one. Nine numbered boundary calls (each annex layer's provenance as its own unit; A1 split
five ways; **GENH4-7 and GENH4-7′ kept as separate units — the shard's most consequential
call**, so the Codex-ratification defect's exact subject is never erased and R2.M4's
inventory-correction stays statable; clause (c)→(c′) tracked across three successive
versions; R2's three per-stratum bullets kept as one unit with the withdrawal recorded
there; R2.M1–M4 + R2.REM as five units; the three what-does-not-move declarations as a
declared SERIES; the three GENH4-BOX-1 appends as a declared SERIES; the three post-pass-2
minors as three units), four deliberately-not-made merges, and six format-feedback items
(rule 18's WITHDRAWAL sub-kind needed again — "the same recommendation GENIND shard 3 made
independently"; a third-order rider occurred, exposing a CHAIN-vocabulary gap for audits of
audits; rule 14 fired twice, both double emissions paid for themselves; the AUDIT
disposition class needed a POSITIVE member, recommended as `hostile-pass certification`;
**the shard's structural finding**: four layers, each finding a real defect in the one
before it, with the consumed clause (b) re-derived clean at every level — the opposite
calibration datum from GENIND shard 3's, where defects landed on a consumed rate). **See
`spec/EFF-GENH4-s2of2.md` §6 for the full prose**, all `.NN` references there resolved per
the same +68 offset as §2 above.

---

## 7. SERIES, CHAINs, and cross-shard boundary resolution

### 7.1 The dated-arc SERIES: SERIES GENH4-BOX-1 (reconstructed across the freeze)

Reconstructing the full chronological order from both shards' own SERIES tags and internal
cross-references (shard 2's `.69` names shard 2's `.80` as "the full arc" of its own entry
1; shard 2's `.108` explicitly disclaims being a numbered BOX-1 append):

| Order | Unit | Content | Series tag (as written) |
|---:|---|---|---|
| 0 | `.01` | Origin: "Attempt grade 0/2 (composed; no hostile arc)" | (pre-dates the SERIES device) |
| 1 | `.44` | Three successive stack-display refreshes (r1/r2/r3) + STANDING DISCLOSURE | (pre-dates the SERIES device; its own CHAIN, §7.2 below) |
| 2 | `.68` | The hostile-arc landing record: composed→PE1→`[r1]`→PE2 CRITICAL→`[r2]`→PE3→`[r3]`, counter 0/2, "PE4 attempts the clean count" | (pre-dates the SERIES device) |
| — | *(acceptance freeze boundary — source line 1208/1209)* | | |
| 3 | `.69` | PE4+PE5 CLEAN; ACCEPTED 2/2 | **"entry 1 of 3 (post-acceptance)"** |
| 3′ | `.80` | The canonical dated GENH4-BOX-1 append for the same milestone | **"the acceptance entry"** (explicitly cross-tagged by `.69` as "the full arc") |
| 4 | `.94` | Codex ratification CHALLENGE; ACCEPTED 2/2 stands ANNOTATED | **"entry 2 of 3 (post-ratification)"** |
| 5 | `.106` | Annex pass #1 NOT CLEAN; annex stack stays 0/2; GAP-1's machine refutation repaired | **"entry 3 of 3 (post-annex-pass-1)"** |
| 6 | `.108` | Annex pass #2 clean-of-GAPs; annex stack reaches 1/2 | terminal state, **explicitly not** a numbered BOX-1 append |

**Nine entries reconstructed (three pre-freeze, six post-freeze — of which two, `.69`/`.80`,
double-record one milestone by the note's own design), zero gaps, zero duplicated series
positions, one explicitly-flagged double-record which the source itself cross-tags rather
than leaving implicit.** The three numbered entries ("1 of 3", "2 of 3", "3 of 3") appear in
strictly increasing chronological and numeric order across the shard boundary with no
renumbering needed — they were already globally consistent before the merge, since only
shard 2 ever uses the "N of 3" labels.

### 7.2 SERIES WHAT-DOES-NOT-MOVE (entirely intra-shard-2, no reconstruction needed)

| Order | Unit | Scope | Exception count |
|---:|---|---|---|
| 1 | `.81` | ANNEX PE5's own scope | 0 exceptions (nothing moves) |
| 2 | `.95` | ANNEX R's scope | 4 exceptions (the R3/R4 rider targets + GENH4-7's hypothesis) |
| 3 | `.107` | ANNEX R2's scope | 5 named targets + 1 rider |

**Three entries, three different exception lists — deliberately not merged into one fence**
per shard 2's own §6.1 item 7 reasoning (a merge that kept only the last would lose the
record that ANNEX PE5 changed nothing at all).

### 7.3 CHAIN inventory (six chains found across both shards; terminals verified pairwise-distinct)

| Chain (unit) | Object | TERMINAL claim |
|---|---|---|
| `.01` | Overall acceptance/annex-stack status | "body ACCEPTED 2/2 and annotated; annex stack 1/2" |
| `.18` | LEMMA GENH4-CAP's E/F trichotomy display | "TERMINAL for the E/F cap statement" (scoped; the genre-F SPLTAIL leg is a *separate* object, tracked by the next chain) |
| `.44` | The grade-stack display's own staleness | "STANDING DISCLOSURE — TERMINAL" (currency comes from the verifier, not any frozen display) |
| `.64` | The two-commit battery-verdict protocol | "VERDICT: PENDING → RED → GREEN — TERMINAL" |
| `.72` (local `.04`) | ANNEX-LEMMA GENH4-7/7′ lemma family | "GENH4-7′(a)-with-cap, (b) unchanged, (c′) as corrected" |
| `.87` (local `.19`) | Clause (c)/(c′) specifically | "R2.G1: two legs WITHDRAWN, (c′) at key level — TERMINAL" |

**All six TERMINAL claims are about six distinct objects and none collides with or
contradicts another** — in particular `.01`'s acceptance-status terminal and `.44`'s
display-staleness terminal are easy to conflate (both concern "the grade box") but resolve
to different questions (whether the note is accepted vs. whether any point-in-time snapshot
of the supplier stack can be trusted), and the two lemma-family chains (`.72`, `.87`) are
nested — `.87`'s clause-(c) chain is a sub-thread of `.72`'s larger GENH4-7 family chain,
and `.72`'s own TERMINAL explicitly folds `.87`'s conclusion in ("(c′) as corrected") rather
than re-deriving it, so the two do not compete for the same terminal fact.

### 7.4 Cross-shard supersessions applied (eleven in-range sentences riddered from shard 2, cross-checked against shard 2's own inventory)

Shard 1 §7 and shard 2 §7 each independently enumerate the same eleven riders; the two
lists agree exactly (verified item by item):

ANNEX PE5 (shard 2 `.69`–`.79`): (1) `.21` LEMMA GENH4-3's SPLTAIL cap; (2) `.25` §S6.1's
SPLTAIL row + gloss; (3) `.30` §S7's SPLTAIL bullet; (4) `.29` §S7's norm-valuation tag;
(5) `.39` §S9.2's "− extra…" token.
ANNEX R (shard 2 `.82`–`.93`): (6)(7)(8) `.14`'s three carrier sentences (R3); (9) all of
`.28`–`.32`'s halved-unit displays (R4, superseding PE5's partial rider at `.29`);
(10) `.62`'s undefined "law keys" + the pre2 remainder (R5); (11) `.19`/`.29`'s
`(GENH4-2)` cite scope (R6).
ANNEX R2 and the post-pass-2 corrections: **no in-range (shard-1) target** — both act on
annex material only, and all three what-does-not-move declarations (`.81`, `.95`, `.107`)
say so.

### 7.5 Range-edge audit (boundary cleanliness)

Shard 1's HOME range ends at source line 1208 (blank); shard 2's HOME range opens at 1209
(`## ANNEX PE5`) and closes at 2173 (the note's last line, confirmed by `wc -l`). **No
source statement unit is cut at the edge, and the boundary is exactly the acceptance
freeze's own boundary** — both shards independently state this and it is directly checkable
(the accepted body is lines 1–1208; ANNEX PE5 begins at 1209). Combined with the two shards'
disjoint statement counts (68 + 43 = 111, no overlap, no gap), the source note's full
2,173 lines are partitioned exactly once between the two shards.

---

## 8. Self-audit and OPEN-CALLS (merged, dedup marked)

### OPEN-CALL 1 — the (CS-EXACT) clause is discharged de facto and named nowhere in this note

*(from shard 1 OPEN-CALL 1, unchanged — shard 2 raises no parallel call on this point.)*
GENH4.D (`.12`) discharges `{(CS-1), (CS-2), (CS-3)}`. GENIND's box grew a fourth clause,
**(CS-EXACT)**, at its own `[r1, PE1-G1]` — *after* this note's seal — and GENIND's Step 4
records the n = 4 discharge of (CS-EXACT) as riding **THEOREM GENH4.B (drain) + THEOREM
GENH4.A + GENH4-1F (menu)**, i.e. exactly this note's theorems. **So the discharge is real
and the display is short by one clause.** GENH4 is frozen and cannot say so. **Decision
needed: whether the merged spec records GENH4.D as discharging a four-clause package (citing
GENIND's Step 4 as the attribution), or leaves the mismatch visible.**

### OPEN-CALL 2 — the annex stack's grade and the acceptance's annotation are not reconciled anywhere **[DEDUP — shard 1 OPEN-CALL 2 and shard 2 OPEN-CALL 1 are the same finding, raised independently at both ends because the evidence is split across the freeze; shard 2's own text says so explicitly ("Raised identically at shard 1 OPEN-CALL 2; recorded at both ends because the evidence is split")]**

The body is **ACCEPTED 2/2**; the Codex ratification then returned **CHALLENGE** and the
acceptance "stands ANNOTATED by the fold note pending Asvin's read" (`.94`). Annex pass #1
was NOT CLEAN (annex stack 0/2); annex pass #2 returned 0C+0G+3m and the stack's clean count
"HOLDS at 1/2". **So the note carries a 2/2 body inside an annex stack at 1/2, with an
unresolved annotation on the 2/2.** **Decision needed: what grade the merged spec attaches
to COROLLARY GENH4.D and to the eleven densities** — the body's 2/2, the annex stack's 1/2,
or the minimum. No silent choice was made at either shard.

### OPEN-CALL 3 — `om_density_engine.py` is md5-pinned and not co-located with the battery

*(from shard 1 OPEN-CALL 3, unchanged.)* `.56` and `.58` pin the engine at md5
`7240a916060c360d4433ca8a802d315d` and the battery imports it. **The file is not present in
`verification/openmath/`.** The β₄ tie is corroboration-only (`.49`), so nothing
load-bearing rests on it — but a chapter cut that wants to re-run GH-DENS cannot locate the
pinned object from this note alone. **Decision needed: whether the merged spec must resolve
the engine's path.**

### OPEN-CALL 4 — a third annex pass's machine leg exists on disk and is cited nowhere

*(from shard 2 OPEN-CALL 2, unchanged.)* `verification/openmath/genh4annexpass3_fresh.py`
(+ output + results) **EXIST** and the note — frozen at the post-annex-pass-2 corrections —
cites them nowhere. The note cannot know its own successor. **Decision needed: whether the
merged spec reads the annex-stack grade from the note (1/2) or from the repo (a third pass's
verdict, unread here), and whether GENH4 owes a dated append.** **This compilation does not
adjudicate it and has not read pass #3.** (The same shape as GENIND shard 3's OPEN-CALL 4 —
a recurring cross-note pattern this queue has now seen twice.)

### OPEN-CALL 5 — the (c′) honest-scope caveat may be a menu refinement, and the note says so without deciding

*(from shard 2 OPEN-CALL 3, unchanged.)* R2's `2w = N` leg (carried to `.99`(ii) verbatim)
closes: "at τ-degenerate members every lift may read {(1,2),(1,2)}; a finer reader keyed on
the pin letter's twist class could conceivably decide those members … that would be a menu
REFINEMENT, not this note's reader". **So cap-uniqueness is sharp for THIS reader's key
granularity and possibly not for a finer one.** The clause is unconsumed, so nothing rests
on it. **Decision needed: whether the merged spec records "the UND exit at 2w ≥ N is
forced" as reader-relative.**

### Recorded source defects (merged and deduplicated; 7 raw across both shards → 7 distinct, 0 overlap)

1. **`.65` cites "P-11's own falsifier grammar"; this note has no P-11** (its predictions
   are P-1…P-9; the falsifiers are unnumbered). The invoked clause exists verbatim at `.63`.
   A cross-note numbering slip in the RED verdict's own justification. (shard 1)
2. **`om_density_engine.py` is not in `verification/openmath/`** — OPEN-CALL 3. (shard 1)
3. **`.27`'s check value "(3,5,1) → 486·(q−1)^t ladder"** is consistent with `486 = 2·3⁵`
   but the factor 2's attribution is not displayed; UNPINNED-BY-DISPLAY. (shard 1)
4. **`.08`'s "288/288 genre-E cases" and "40 of 50 scanned"** give no parameter grids;
   UNPINNED-BY-DISPLAY (the genre-F 216 does reconcile: 9×3×8 ✓). (shard 1)
5. **A third annex pass's leg exists uncited** — OPEN-CALL 4. (shard 2)
6. **`.96`'s results pin was one character wrong** — the note corrects it itself at `.109`;
   the second md5-transcription defect in this queue (GENIND shard 2 `.58` is the first —
   **this exact cross-note pin was the specific value a naive shift-script corrupted during
   this merge's own SHARD-MAP rewrite, §1 above** — a coincidence worth flagging since it
   means this defect record is also the reason the merge's own tooling needed a second
   correction pass). (shard 2)
7. **`.87`'s scope paragraph calls F4 "unconsumed" and the ratification graded it a GAP** —
   consistent (a GAP on an unconsumed clause is still a GAP), but a reader may take
   "unconsumed" as a downgrade; the note's own grading (`.82`: "F4 (CONFIRMED GAP, scoped to
   GENH4-7(c), unconsumed)") is precise. (shard 2)

**Compiler-added defect 8 (merge-level, §3.1 above):** shard 1's claimed "27 distinct XREF
designations" does not reconcile against a literal recount by either row (23) or
slash-separated pattern (33); flagged, not silently corrected — no individual grep count is
in doubt.

### Fidelity audit (merge-level, in addition to each shard's own independent audit)

- Every CANONICAL STATEMENT is verbatim or explicitly `[ASSEMBLED]`; the mechanical
  ID-renumbering (§1's SHARD-MAP) touched only `EFF.GENH4.*` tokens and the bare/explicit
  `.NN`/`sKof2.NN` shorthand, never a mathematical symbol, exponent, census, σ-multiset,
  valuation, count, or quote span. **No blockquote (CANONICAL STATEMENT text) contains any
  such shorthand token to begin with**, since the shorthand is this compilation's own
  apparatus, not the source note's — so the rewrite could not have touched quoted source
  bytes even in principle.
- **111 statements, 68+43, zero duplication, zero gap** (§7.5).
- **34 distinct XREF designations verified, all count ≥ 1** (§3.1), with the
  "27" discrepancy flagged as defect 8 above rather than propagated silently. **53 distinct
  commit pins verified, 0 failures** (§3.2). **26 machine-artifact files verified present**
  (11 shard-1 + 12 shard-2 + 3 uncited pass-3 files, §3.2). **6 near-misses recorded** with
  their referents (§3.3).
- **62 units carry compiler-computed arithmetic audits** (31 per shard), **all agreeing with
  the source** — including the CRITICAL's refutation instance and its `q+1`
  irreconcilability, all eleven preregistered spot values, the classical spot identity at
  q=2, both battery run totals (245,694 and 245,693) reconciling to the digit, the pre2
  six-key partition's seven numbers, and the level-0 census closure at q=2 and q=3.
- **Six CHAIN fields, all TERMINAL claims pairwise-distinct** (§7.3); **two SERIES,
  reconstructed across the freeze with zero gaps and one explicitly-flagged double-record**
  (§7.1–7.2).
- Status and mathematics are kept distinct throughout: the acceptance is a record grade
  (`.01`, `.69`, `.80`), the discharge is a mathematical claim (`.12`), and the annex
  stack's lower grade is carried separately at every layer (`.44`, `.69`, `.82`, `.94`,
  `.96`, `.106`, `.108`).
- **Honest limitation, carried from shard 1:** the genre-F SPLTAIL σ-leg — a clause W-12.D
  consumes — has **no proof in the accepted body**; both its proof (`.84`(b), `.85`) and all
  its machine contact (`.79`, `.86`) are in the shard-2 range. The merge does not change
  this: the leg's proof still lives 300+ lines after its statement, exactly the "prose
  proofs fail hundreds of lines from their statement" pattern rule 12's three-slot
  RESOLUTION TRACE exists to record.
- **This merge run performed the ten-XREF / five-quote sampling itself** (fresh greps and
  fresh `sed` line extractions against the working tree, not trusted from either shard's own
  sampling) — both reported in §3.1 above, zero drift found.

EFF-GENH4 MERGED: 111 statements.
