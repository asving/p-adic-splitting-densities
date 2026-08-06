# LIFTCORNER passPE5 — hostile verification report (fresh context, post-r4; THIRD ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD** (949b346
content), i.e. after repair rounds **r1** (b2dc120), **r2** (a3112dc + e5b3faf),
**r3** (feedaab) and **r4** (6170b09 + fixup 56997be).
**Arc read in full before the note:** `LIFTCORNER_passPE1_report.md` (30e570c,
1C + 3G), `LIFTCORNER_passPE2_report.md` (3367f3c, 0C + 5G),
`LIFTCORNER_passPE3_report.md` (39ea0db, 0C + 5G), `LIFTCORNER_passPE4_report.md`
(8b53efa, 0C + 6G), and both r4 diffs (`git show 6170b09`, `git show 56997be`).
**Cross-note read:** ITERLAWN_PROOF_2026-08-08.md (S0.1 Lifts clause, S0.3 L6
row + the errata-r4 attribution bracket, the S7 DEPENDENCY-CLAIM SWEEP TABLE
all 22 rows, S9, S10 DAG edge), ILNRES_2026-08-08.md (S1 [NR-1], S5.1, S6
census, S7, perimeter facts), ITERLAWLIFT_CORNER_2026-08-08.md S0.
**Machine legs (all three mandatory):** (a) sealed runner; (b) children
generator + A7; (c) an independently written probe of the r4 `K2["one"]`
claim. **Charge:** quote-and-classify, fix nothing; honesty defects graded;
fences and boxes read as part of the statement. As the fifth hostile reader I
was directed at: the r4 edits themselves (the 5-line S5 template line by line;
the ARCHIVE region's non-authority marking and byte-preservation), the renamed
cocycle `c^{Φ′}`, the F4-4 re-point against ITERLAWN's actual r4 erratum, the
F4-6 rewrite against ILNRES S1/S5.1/S7 verbatim, and one S2–S4 proof detail no
prior pass ever re-derived.

**VERDICT: 0 CRITICAL ERRORS / 5 JUSTIFICATION GAPS. NOT A CLEAN PASS — the
acceptance counter stays 0/2 and no acceptance slot opens.**

The mathematics is untouched again: my one genuinely unmined re-derivation
(the TAIL-STAB statement's own read-kill close — the "Hence w₂(X) ≥ ω(X), and
for any Γ < ω(X) every level-2 read contributes 0" sentence, which PE1 graded
"sound" without display and PE2–PE4 never re-derived) checks out exactly
(§3(e) below). All three machine legs reproduce: sealed runner byte-untouched
(md5 intact, 0-byte diff vs the seal dafc0b5), exit 0 at 25,409/0; children
table regenerates byte-identically with A7's four legs PASS; and my own
fresh probe reproduces the r4 F4-1 claim — `K2["one"]` is invariant across
both twist draws AND under a ψ₁ perturbation while the letter z₁ moves. The
ARCHIVE region is byte-identical to the r3-era status lines (verified against
`git show feedaab`, raw diff 0 after trimming the two framing blank lines),
its three flagged corrections are each accurate, and no live sentence consumes
an archived claim as authority. The F4-3 provenance correction verifies
against my own grep of PE2's report (3 unqualified sealed-runner sites at
lines 33/54/471, 1 qualified at line 67; lines 76/472 are generator sites,
correctly not counted). The F4-6 quotes all verify verbatim at source
(ILNRES S1's "at any level" clause, S5.1's spec sentence, S7's four-member
completeness sentence, perimeter fact (iii), wave-18 S0's Φ₁-only display).

The five gaps are all in the r4 edits — the only unaudited surface going in —
and all five are the arc's own recurring genre (status/pointer/description
stronger or falser than the text it summarizes): the regenerated 5-line
template's PROVED line lists **PROP's rung propagation** as proved-at-grade
when the note's own F4-4 declares its load-bearing census an argument the note
"does not make" and no read source supplies (F5-1); the assert-saga
terminator's parenthetical "(ψ₁ and K₂ enter no counted predicate of S3 and no
step of S4)" is refuted by S4.2's own first proof sentence (F5-2); the F4-5
renaming leaves the cocycle written as bare `c′` at two surviving sites, one
of them live r3-edited text that the new convention now makes parse as a false
formula (F5-3); the F4-4 re-point — the round's cite-location repair —
itself miscites the sweep table's location ("S9"; it sits in ITERLAWN **S7**,
and ITERLAWN's actual S9 is a table-free scope box) (F5-4); and the r4 header
mis-points the e₀ = 1 emptiness record to "(S4.3, COR 1)", where it does not
appear (F5-5). None touches the chain, the measurement, or the grade.

---

## 1. Machine legs (mandatory, three parts) — ALL RUN, ALL REPRODUCE

### (a) The SEALED runner — exit 0, seal intact, 0-byte diff, every counted figure matches

```
$ md5sum liftcorner_checks.py
ccb4351c92573f5f962cae4ae952d8dd          <- = the note's claim (header + S3)
$ git show dafc0b5:verification/openmath/liftcorner_checks.py | md5sum
ccb4351c92573f5f962cae4ae952d8dd          <- md5 at the seal == md5 at HEAD
$ git diff dafc0b5 HEAD -- verification/openmath/liftcorner_checks.py | wc -c
0                                         <- 0 bytes
$ python3 liftcorner_checks.py ; echo EXIT=$?
... TOTAL checks 25409  elapsed 4.3s ... VERDICT: ALL GREEN ... EXIT=0
```

My family table: GATE 0/56 · AV 0/656 · TLAW 0/4176 · PV 0/4176 · INT 0/4176 ·
LOC 0/0 · CHI 0/4176 · COV 0/0 · WRONGLET 0/3816 · TRS 0/4176 · ENGGATE 0/1 ·
CERT 0 (internal T1/T2(nf=4)+T5) · WRONGLET total fires **1576** · gate-passed
**56** · coverage min d1-pairs **6** · teeth min **6**. Sum
56+656+4176+4176+4176+0+4176+0+3816+4176+1 = **25,409** ✓. **Every S3 figure
matches.** My run's diff against the committed `liftcorner_checks_output.txt`
is **6 lines, all wall-clock** (five per-block stamps + `elapsed 4.3s` vs
`4.4s`), empty under timing normalisation. (The [r4] machine bracket records
PE4's run differing at exactly 4 such lines — a faithful transcription of
PE4's own record; wall-clock jitter varies per run, and the counted quantities
are identical in all recorded runs including mine.)

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe5_children_regen2.txt ; echo $?
0
$ diff /tmp/pe5_children_regen2.txt liftcorner_tailstab_children_table.txt
(empty)   -> BYTE-IDENTICAL TO COMMITTED
```

§7 of my regeneration: assertion failures 0; A1–A6 PASS; A7 PASS — 752 nodes
reconciled / 5,336 children enumerated; (i) sum-identity mismatches 0;
(ii) shape violations 0; (iii) digit-wise dev-linearity mismatches 0;
(iv) branching ≤ 2e₀+3 violations 0 with observed max {2:7, 3:9, 4:11, 5:13,
6:15} = 2e₀+3 at every e₀; "ANY CHILD DROPPING NEITHER COORDINATE: NO";
"OVERALL: ALL GREEN". Matches the note's [r2, G3] block and the [r4]
machine-leg bracket exactly.

### (c) The r4 `K2["one"]` claim — reproduced with MY OWN probe (not PE4's)

Fresh script (`/tmp/pe5_probe_k2one.py`, read-only imports of the committed
modules), on the note's own row CB over ℤ₂ (d₀ = 2, g₀ = g₁ = 1, K₀ = 𝔽₄):

```
base c0 = (0, 1); base z1 = ((0, 1),)
C0.K2['one'] = (((1, 0),),)
twist draws: [(1, 0), (1, 1)]
  c'=(1, 0): K2['one'] = (((1, 0),),)  == base? True   z1 = ((1, 0),)  z1 moved? True
  c'=(1, 1): K2['one'] = (((1, 0),),)  == base? True   z1 = ((1, 1),)  z1 moved? True
psi1 perturbed (psi1[0] += 1): K2['one'] = (((1, 0),),)  == base? True
```

i.e. exactly the note's [r4, F4-1] display: `K2["one"] = ((K0["one"],),)` on
the base tower, on both twist draws, and with ψ₁ perturbed — while z₁ moves.
Source legs re-verified independently: `mk_field_ext` (def at
`grb_order2_check.py:333`) sets `one = tuple([K["one"]] + [K["zero"]]*(g-1))`
(line 336) reading only `g = len(psi)−1` and K's one/zero — `psi`'s
coefficients enter only `red` (line 335), which `one` never touches; the
reduction loop `for k in range(len(out)-1, g-1, -1)` is at :345 and is empty
at g = 1; `T.psi1` assigned once at :515; `build_Phi2` only reads it (:651);
`self.K2 = mk_field_ext(T.K1, T.psi1)` at `strata_probe.py:389`; the runner's
cited lines :35/:36/:52/:144/:179 all verified verbatim. So BOTH asserts are
inert exactly as the r4 final description says. (One trivial cite slip, not
numbered: the note cites ":333–334" for the `one` assignment; `one` is at
:336. The quoted code is verbatim correct.)

Nothing in the repo was edited by this pass except this report.

---

## 2. FINDINGS (all in the r4 edits; ranked)

### F5-1 — JUSTIFICATION GAP: the regenerated STATUS BLOCK's PROVED line lists "PROP's rung propagation" as proved-at-grade, which the note's own F4-4 bracket contradicts — the surface rebuilt to stop producing findings produced one

Offending passage (S5, STATUS BLOCK [r4], third bullet):

> "* **PROVED (at that grade).** (TAIL-STAB) by S4.1 as repaired at r1,
> statement byte-unchanged, its argument re-derived independently by PE2, PE3
> and PE4; and on it READ-EQ, the THEOREM, **COR 1** (…), COR 2 on the harness
> orbit, **and PROP's rung propagation**."

Against the note's own body, in the same revision:

> (PROP) "VERIFY-TARGET for the arc: the clause-(ii) census at rungs ≥ 2 (no
> rung leg opens Φ₁'s bytes outside the level-1 package) is NOT re-proved
> here."

> ([r4, F4-4]) "So a rung-≥2 clause-(ii) census must show that
> S4.1/WELL-DEF-(n) and the S4.2 telescope read Φ₁ only through monicity,
> degree e₀d₀ and w₁Φ₁ = e₀g₀h₀ (plausible — …) — **an argument this note does
> not make, and which neither the two formerly cited tables nor ITERLAWN's own
> r4 erratum supplies**"

PROP's rung-≥2 leg therefore rests on an **absent** argument — an open lemma,
per r4's own words unsupplied by any source anyone has read — not on a present
argument awaiting audit credit. That distinction is exactly what separates
charge item (5) from items (1), (2), (7) (which are displayed in the note and
re-derived by three hostile passes), and the PROVED line flattens it: PROP is
put on the same list as COR 1, under the same "(at that grade)" qualifier,
when the grade language (attempt 0/2, W-2 cap) prices audit status, not
missing steps. The body's own verb for PROP has never been "proved" — the r0
compose called it a "propagation leg", PE1 verified it as "honest — the
rung-≥2 clause-(ii) census is explicitly a VERIFY-TARGET … cited not
re-proved", and every archived status line said only that PROP "stands exactly
as PE1 verified it GIVEN (TAIL-STAB)". The r4 template is the first text in
the arc to classify PROP's rung propagation as PROVED — an upgrade introduced
by the regeneration itself.

**Mitigation (why GAP, not CRITICAL):** the CONDITIONALITY bullet two lines
below says "(5) PROP's rung-≥2 clause-(ii) census is OWED", so the disclosure
exists on the same surface; no chain step consumes the PROVED line; and PROP
at rung 1 (= COR 1 + ITERLAW S7's own display) is genuinely carried by the
note. The defect is the classification: the honest PROVED-line entry was
"PROP's rung propagation CONDITIONAL on the owed census (5)" — one clause.

### F5-2 — JUSTIFICATION GAP: the assert-saga terminator's parenthetical "(ψ₁ and K₂ enter no counted predicate of S3 and no step of S4)" is false as written — S4.2's proof opens by consuming exactly ψ₁ and K₂

Offending passage (S2 disclosure (c), the [r4, F4-1] FINAL DESCRIPTION):

> "**NO CHAIN STEP CONSUMES EITHER**: the ψ₁-site walk below establishes it
> for (i), and the same walk gives it for (ii) verbatim **(ψ₁ and K₂ enter no
> counted predicate of S3 and no step of S4)**."

S4.2 READ-EQ's proof, first sentence, in the same note:

> "The towers share every read datum (**reads, ψ₁, K₂**, and the LETTER
> z₁′ = −c′ in ε₁) — only key bytes differ."

So ψ₁ and K₂ do enter a step of S4 — as the shared read data on which
READ-EQ's byte-comparison rests — and every value compared by S3's counted
predicates (TLAW/CHI/AV/…) is computed in K₂ arithmetic, so "enter no counted
predicate" holds only in the narrow sense that no predicate takes ψ₁/K₂
themselves as compared objects. The TRUE claim — that no S3 predicate and no
S4 step consumes the runner ASSERTS, S4.2's shared-datum sentence being
"proved from the S4 setting … with no dependence on any runner assert" — is
stated correctly in the r3 walk two paragraphs below; the r4 parenthetical is
an overcompression of it that, read as written, contradicts the note's own
S4.2. This is the same species as the three assert-saga misdescriptions the
bracket exists to terminate (r0 described / r1 promoted (i) / r3 promoted
(ii)): a fourth round of imprecise wording about the same pair, introduced by
the round that closed the saga. Also note the false half is load-bearing for
the bracket's own inference: "the same walk gives it for (ii) verbatim" is
justified BY the parenthetical, so the sentence's evidence for the (true)
conclusion is defective, while the conclusion itself I re-verified
independently (leg (c) + the r3 walk's site list).

### F5-3 — JUSTIFICATION GAP: the F4-5 renaming is incomplete — the cocycle survives as bare `c′` at S2's Q7 row and S3's Q7 bullet, and the new convention makes the live S3 line parse as a false formula

Offending passages. The convention and completeness claim ([r4, F4-5] and the
r4 header):

> "From here on **`c^{Φ′}(γ,γ′)`** denotes the 2-read COCYCLE on the Φ′-tower
> … while **`c′` (no arguments) stays the RESIDUE SCALAR** … **S1's CANDIDATE
> display is sealed pre-run text and is NOT edited**: it writes this cocycle
> as `c′(γ,γ′)`, and this bracket is the correction of record for it"

> (r4 header) "**F4-5** — the `c′` collision (residue scalar vs cocycle) in
> the headline display **is fixed** by renaming the COCYCLE to `c^{Φ′}`"

The two surviving cocycle-as-`c′` sites, from my grep of the whole note:

> (S2 sheet, Q7 row) "cross-tower χ-ratio: **c_base == c′·ξ^{D₁}**, measured
> vs MEASURED"

> (S3, Q7 bullet) "**Q7 CHI 4,176/0 — the χ-ratio law c_base = c′·ξ^{D₁}
> EXACT**, measured against measured"

Both write the Φ′-tower cocycle as `c′` **with no arguments** — which is
precisely the form the new convention reserves for the residue scalar; under
[r4, F4-5]'s own rule the S3 line now reads "c_base = (residue scalar)·ξ^{D₁}",
a false equation. The S2 row is sealed pre-run text (I verified the S1/S2
table region is byte-unchanged since dafc0b5 — the dafc0b5→HEAD diff's second
hunk starts at the disclosures), so it deserves exactly the correction-of-
record treatment the bracket gives S1's CANDIDATE — but the bracket names
S1's CANDIDATE **only**. The S3 bullet has no such excuse: S3 is live,
repairable text (r3's F-E struck and replaced wording inside S3 two bullets
up), and r4 left it untouched. A "From here on" positional scoping defends the
S3 line from formal contradiction but then concedes the r4 header's "is
fixed" overstates: the collision PE4 numbered is fixed at 2 of its sites,
excused at 1, and persists unmentioned at 2 more. One-line cures both ways
(rename the S3 occurrence; extend the correction-of-record clause to the S2
row).

### F5-4 — JUSTIFICATION GAP: the F4-4 cite-location repair itself miscites the sweep table's location — "S9" is wrong; the 22-row sweep is in ITERLAWN S7, and ITERLAWN's S9 contains no table

Offending passage ([r4, F4-4]):

> "That cite was false as to location: **ITERLAWN_PROOF's S9
> dependency/exemption sweep (22 rows)** and ILNRES S6's "consumption census"
> are both keyed to *accepted-package* consumption …"

Checked at source: the 22-row DEPENDENCY-CLAIM SWEEP TABLE sits inside
**"## S7. THE CONDITIONALITY LEDGER"** (ITERLAWN_PROOF line 1148; the sweep
bracket opens at line 1150, the table at 1164–1190). ITERLAWN's actual
**S9** is "## S9. Scope box — fences (what this note does NOT do)" (line
1429) — a bullet list, no table, no sweep. The mislabel originates in PE4's
own report header ("the S9 dependency-sweep table"), which r4 transcribed —
the same transcription mechanism F4-3 just documented for "bit-identically".
So the bracket whose content is "the cite was false as to location" carries a
false location in its first sentence.

**What is NOT wrong (checked row by row, and why this is minor):** everything
substantive in the F4-4 re-point verifies at source. The S0.3 clause-table L6
row is quoted **verbatim** including the full errata-r4 attribution bracket
(ITERLAWN line 278; ellipsis faithful); the erratum's companion facts check
(sweep rows 4/12/19 at status C-r4; the S4.1 → L6-(n) DAG edge added, sweep
row 22 + the S10 bracket at line 1464); the S0.1 Lifts clause is quoted
verbatim (line 163); ILNRES's census is correctly placed in S6 (line 255) and
correctly characterized (engine-freeness, not Φ₁-bytes); and I re-read all 22
sweep rows myself — none is about how much of Φ₁'s form a rung leg opens, the
nearest (rows 1 and 10) being level-scope claims, exactly as the fixup
56997be says. The plausibility gloss also checks: sweep row 10 lists the C_k
inputs as ψ_m, γ_{m+1}, ε_m, realize_m, Φ_m, and S0.1's construction display
gives Φ₂ = Σ C_k·Φ₁^{e₁k} — Φ₁ entering only as a power — verbatim
consistent with the bracket's parenthesis. Only the section pointer is false.

### F5-5 — JUSTIFICATION GAP (minor): the r4 header claims the e₀ = 1 emptiness fact is "record[ed] (S4.3, COR 1)"; no such record exists at S4.3 — it lives in the S5 STATUS BLOCK

Offending passage (r4 header round bracket):

> "it also established a POSITIVE fact this note now records **(S4.3,
> COR 1)**: **δ₁ = 1 is empty at e₀ = 1**, so S4's e₀ ≥ 2 Setting costs COR 1
> nothing and the corner is covered in full."

S4.3's COR 1 text at HEAD is byte-unchanged on this point and contains no
such record (its whole text: the ξ = 1 slice sentence, the ITERLAW S7 cite,
the machine line). The fact is recorded once, in S5's STATUS BLOCK PROVED
bullet ("COR 1 ((ITER-LAW-LIFT) at the corner — and δ₁ = 1 is EMPTY at
e₀ = 1 …"). The nearest S4 text is the r0 Setting line ("at e₀ = 1 no Case II
exists — COR-3's degeneration"), which is the same mathematical fact but is
not the r4 record the header points at. A false internal pointer in r4-new
text, in the same genre as F5-4 at lower stakes (the true site is one section
away and clearly labeled). The mathematical fact itself is correct — I
re-checked it: δ₁ = 1 needs s₁+s₁′ ≥ e₀ with s₁, s₁′ ≤ e₀−1, and at e₀ = 1
that forces s₁ = s₁′ = 0 < 1.

---

## 3. The directed veins — results

### (a) The r4 edits: the 5-line template line by line; the ARCHIVE region

**Template, line by line.** **ARC** — every hop verified against the four
reports and `git log` (PE1 1C+3G at 30e570c; PE2 0C+5G at 3367f3c; PE3 0C+5G
at 39ea0db, FIRST acceptance attempt per its own header; PE4 0C+6G at 8b53efa,
SECOND; r4 = F4-1…F4-6 + the regeneration, matching both r4 commits) ✓.
**COUNTER** — 0/2 with the correct reason; the W-2 cap current (GRTW2 still
0/2 in the repo state); the W-2-free decoupling of the COR 1 / ξ = 1 chain
matches PE1's dependency trace, which PE4 re-traced ✓. **PROVED** — the
TAIL-STAB clause is accurate (statement byte-unchanged was PE2's fence check;
"re-derived independently by PE2, PE3 and PE4" matches the three reports'
re-derivation lists); READ-EQ / THEOREM / COR 1 / COR 2 accurate; **the PROP
clause is finding F5-1**. **CONDITIONALITY** — all four clauses verified
((5) OWED matches F4-4; F3's (a)/(b) match the box; the Φ₁-corner-only
description matches F4-6; the MODULO-arc price-sheet clause consistent) ✓.
**NEXT/AUDIT** — unaudited = r4 edits ✓ (true when written; this pass now
reads them); r3 edits read once (PE4) ✓; r2 edits read twice (PE3, PE4 — PE4
§3(e) read every deleted r2 line) ✓; items (1)/(2)/(7) at three re-derivations
✓; the machine-legs clause re-confirmed by my own runs ✓.

**The ARCHIVE region.** Byte-preservation VERIFIED against git, not prose:
the region between the ARCHIVE-BEGIN/END markers is **byte-identical** to
lines 863–980 of the note at feedaab (the three r1/r2/r3 STATUS LINEs; raw
diff 0 after trimming the two framing blank lines). The header's non-authority
marking is explicit and repeated ("Nothing between the markers is live … NOT
live status"). The THREE flagged corrections are each accurate: (1) the r1 F4
clause is indeed refuted by r3's F-A + r4's F4-1 and indeed sits in the
archive un-bracketed (which is what F4-2 recorded); (2) the "dropped in the r2
paraphrase" provenance is indeed wrong and the archive text indeed carries it
(r2 STATUS LINE's [r3, F-C] bracket) — and the corrected provenance verifies
against my grep of PE2's report (unqualified "bit-identical(ly)" for the
sealed runner at lines 33, 54, 471; qualified at 67; the other two hits, 76
and 472, are children-generator sites, correctly excluded); (3) the r3 STATUS
LINE's F-A summary does carry the refuted (ii)-promotion verbatim. My own
sweep of the archive found **no additional refuted-and-unflagged claim**
(remaining superseded content is stale-but-true-at-its-round, e.g. "TWO
hostile passes" counts). **No live sentence consumes an archived claim as
authority**: every live reference to the STATUS LINEs is historical (the r4
header, the STATUS BLOCK preamble, the archive header). Two unnumbered
observations: the ARCHIVE-BEGIN/END markers are HTML comments and hence
invisible in rendered markdown — the bold [r4, ARCHIVE] paragraph above them
carries the marking for rendered readers, and the archive is the note's tail,
so the risk is low; and the STATUS BLOCK preamble's "the status surface
produced findings in three consecutive passes — PE2's G2 …" stretches G2
(whose offending passage was the S4.1 F1 box + the grade-box charge list)
into "the status surface" — defensible only on a broad reading of that term.

**The other r4 edits, checked:** the [r4, structural] restoration of
disclosure item (d) is faithful to the seal (dafc0b5's list was
semicolon-joined "… carries over verbatim; the runner asserts this (…) …;
(d) SP bug-detector counters recorded." — r1's F4 repair removed the middle
clause, quoted since in [r3, F-A]; rejoining (d) with a semicolon restores
the seal's list structure; no claim changes) ✓. The [r4, F4-1] strike of the
r3 bullet quotes it in full (words verbatim; emphasis marks altered — bold →
italic on the refuted fragments — acceptable under "quoted in full") ✓. The
assert-pair arc sentence ("r0 described it …, r1 promoted (i), r3 promoted
(ii), and r4 demotes both") is accurate at all four points ✓. The F4-3
correction is accurate at both its sites (header + archive-header (2)) ✓.

### (b) The renamed cocycle `c^{Φ′}`

Every occurrence located by grep: THEOREM (line 881), the F4-5 bracket
(889–894), COR 2 (910) — consistent with each other and with the convention;
COR 2's prose now says "residue scalar c′" ✓; no `c(γ,γ′)` remains anywhere;
S1's CANDIDATE (293–294) writes `c′(γ,γ′)` and is verified byte-unchanged
since dafc0b5, correctly exempted with this bracket as correction of record.
**Residual collision found at two further sites** — S2's Q7 sheet row (line
318, sealed) and S3's Q7 verdict bullet (line 472, live) — finding **F5-3**.

### (c) The F4-4 re-point vs ITERLAWN's r4 erratum

All quotes verified verbatim at source (the L6 row with its full attribution
bracket; the S0.1 Lifts clause; rows 4/12/19 C-r4; the S10 DAG edge; rows 1
and 10 as the nearest-and-still-not-it; ILNRES S6's census correctly
characterized as engine-freeness). The 56997be fixup's re-scope ("neither the
two formerly cited tables nor ITERLAWN's own r4 erratum supplies" the census,
scoped to what PE4 read) is accurate and I independently confirm it: none of
the 22 sweep rows is a Φ₁-bytes census. Charge item (5)'s OWED re-scope
matches between the F4-4 bracket and the CONDITIONALITY line ✓. Two defects
in the bracket's own frame: the sweep's section mislabel (**F5-4**), and — 
unnumbered observation — "the true site of record … is ITERLAWN's own r4
erratum" is loose for an argument the same bracket says exists nowhere: the
erratum records the CONSUMPTION the owed census must clear, not the census;
the fixup's next clause self-corrects this, so it is not numbered.

### (d) The F4-6 rewrite vs ILNRES S1 / S5.1 / S7

All four load-bearing quotes verified verbatim at source: NR-1's recorded
statement in ILNRES S1 (lines 25–32) does contain "nothing is claimed for any
non-canonical lawful lift at any level" AND the Φ₁-corner clause ("open
exactly at g₀ = 1 ∧ δ₁ = 1"); ILNRES S5.1's spec sentence matches word for
word ("Extend the [IL] L7 Case-II analysis to an arbitrary lawful lift
Φ₁′ = Φ₁ + (π-excess) at g₀ = 1 ∧ δ₁ = 1, then ride S0.1's verbatim
propagation"), and its deliverable clause ("one note + sealed battery in this
genre; no accepted text edited") is what the unit delivers; ILNRES S7's
completeness sentence matches ("S1's FOUR-MEMBER residual list is COMPLETE
relative to the sources of record — NO FIFTH RESIDUAL EXISTS"); perimeter
fact (iii) matches ("'orders ≥ 3 untouched' ([IL]) is subsumed by [ILN]
itself"); wave-18 S0's display matches ("the honest OPEN displayed lemma
(ITER-LAW-LIFT): ITER-LAW for every lawful monic lift Φ₁"). The three
replacement paragraphs are honest: the delivery description matches the spec;
the discrepancy paragraph states both readings without choosing; the
carve-out withdrawal is the right call (this unit cannot mint a residual
against S7's completeness sentence) and ILNRES is verified NOT edited (no
commit in 8b53efa..HEAD touches it — fences hold; the working tree's one
modification is another agent's GRTJB file, untouched by me). One unnumbered
observation: "The two readings live in different notes of record" glosses
that S5.1 — cited for the narrow reading — lives in ILNRES itself, the same
note whose S1 carries the wide reading; the discrepancy is thus partly
ILNRES-internal, which is in fact what the erratum-candidate flag implies.
Defensible as written (the residual's DISPLAY lives in wave-18, its RECORD in
ILNRES), so recorded here rather than numbered.

### (e) The never-re-derived proof detail: the TAIL-STAB statement's read-kill close — RE-DERIVED, SOUND

The target (S4.1 statement, second half): "Hence w₂(X) ≥ ω(X), and for any
read weight Γ < ω(X) every level-2 read of X at Γ contributes 0 at every grid
slot (on-line: strict-excess summands die in res; off-line: C_j = 0; digit
collisions: w₀ ultrametric, min bounds survive)." Audit history: PE1 marked
it "sound" without displaying a derivation; PE2 explicitly re-read it only
"for consistency"; PE3 and PE4's re-derivation lists never include it; it is
in no charge item ((4) is READ-EQ's close, a different step). My derivation:

* Setup: the double development X = Σ_{j,i} a_{ji}Φ₀^iΦ′^j has unique digits
  with deg a_{ji} < d₀; the level-2 weight of a nonzero digit at slot (i,j)
  is wt(i,j) = e₁(e₀·w₀(a_{ji}) + i·h₀) + j·γ₂; a level-2 read at Γ
  evaluates, at each slot on the Γ-line — those (i,j) with
  u_{ij} := (Γ − jγ₂ − e₁ih₀)/(e₁e₀) ∈ ℤ≥0 — the residue
  res(a_{ji}/π^{u_{ij}}). (The functional's form is the accepted 2-read
  frame, consumed not re-proved — consistent with the note's citation
  discipline; "res kills strict π-excess" is S4's displayed base-fact list.)
* w₂(X) ≥ ω(X): w₂ = min over nonzero digits of wt(i,j); (LEDGER) bounds
  every term by ω(X). Immediate. ✓
* On-line kill: a_{ji} ≠ 0 at an on-line slot gives, from (LEDGER),
  e₁(e₀w₀(a_{ji}) + ih₀) + jγ₂ ≥ ω(X) > Γ = e₁(e₀u_{ij} + ih₀) + jγ₂, hence
  e₁e₀(w₀(a_{ji}) − u_{ij}) > 0, hence by integrality w₀(a_{ji}) ≥ u_{ij}+1:
  a_{ji}/π^{u_{ij}} is strict π-excess and res kills it — contribution 0. ✓
* Off-line: slots off the Γ-line contribute nothing to the read at Γ (the
  note's shorthand "C_j = 0"), and zero digits contribute no summand. ✓
* Collisions: within the statement's unique double development no two digits
  share a slot; the collision clause's actual consumption site is (C)(i)'s
  assembly (children's digits summed per slot, w₀(Σ) ≥ min w₀ preserving
  every slot's ≥ ω(X) bound, cancellation only deleting digits), where it is
  the base ultrametric fact. Sound there; inside the statement it is surplus
  justification, harmless. (Observation only, not numbered.)

Verdict on the vein: the one load-bearing sentence five hostile readers had
left untouched **holds**, with its dependencies exactly where the note says
they are (the accepted read frame + the S4 base facts).

---

## 4. Verified perimeter (checked this pass, no findings)

- **Grade box [r4] update:** the PE4 verdict/commit citation (0C + 6G,
  8b53efa), the six-gap list, the three-pass audit counts for items
  (1)/(2)/(7), and "the r4 edits are UNAUDITED" all accurate ✓.
- **[r4] machine-leg bracket:** every clause matches PE4's report, and every
  reproducible clause re-confirmed by my own runs ✓.
- **r4 header dispositions list:** F4-1…F4-6 one-line summaries match the
  applied brackets one for one (F4-5's summary is where F5-3's "is fixed"
  lands; F4-4's is where F5-4's mislabel propagates from PE4) ✓.
- **Strike discipline at r4:** every r4-removed sentence located in the
  6170b09 diff is quoted inside the bracket that replaces it (the r3 assert
  bullet; the r3 docstring re-read instruction; PROP's old cite clause; S5's
  NR-1 bookkeeping sentence; the THEOREM/COR 2 renames disclosed in F4-5;
  item (d)'s move disclosed in the structural bracket; the three status
  lines archived byte-unchanged) — no silent deletion found ✓.
- **Fences:** no commit in 8b53efa..HEAD touches ILNRES / ITERLAWN /
  wave-18 artifacts / either machine leg; both r4 commits touch only the
  note; no Lean change ✓.
- **Q7 CHI semantics** (re-checked at source while auditing F5-3's sites):
  `base_cc` is measured on base towers via `measured_cocycle(T0, C0, ·)`;
  the base towers see only G.T1_T2/G.T5 — measured-vs-measured as claimed ✓.
- **S1/S2 seal integrity:** the dafc0b5→HEAD diff on the note has exactly
  two hunks (header-bracket insertions; disclosures-onward), so S1's
  CANDIDATE and the S2 sheet table are byte-unchanged since the seal ✓.

## 5. Bottom line

**Not a clean pass: 0 CRITICAL, 5 gaps. The acceptance counter stays 0/2; no
slot opens; PE6 would be the next acceptance attempt after an r5.**

The chain, the measurement, and the machine record are in the same state four
passes have confirmed — and the one proof sentence nobody had ever re-derived
(the statement-level read-kill close) re-derives cleanly, so after five
hostile readings every load-bearing step of S4.1 has now been independently
re-derived at least once. The r4 round's two big structural moves are genuine
improvements: the 5-line template is a real reduction of the surface that had
produced findings in consecutive passes, and the ARCHIVE region is
byte-faithful, correctly de-authorized, and correctly annotated.

But the r4 edits — the pass's designated unaudited surface — contain five
new defects of the arc's own recurring genre. The template's PROVED line
overclassifies PROP (F5-1: the one listed item whose supporting argument the
same revision declares unwritten anywhere). The assert-saga terminator
introduces a fourth-round misdescription of the same pair it closes (F5-2:
ψ₁/K₂ "enter no step of S4" while S4.2's first proof sentence consumes
exactly them). The c′-collision fix is incomplete (F5-3: two surviving bare-c′
cocycle sites, one live and now false-parsing under the fix's own
convention). The cite-location repair miscites a location (F5-4: "S9" for
ITERLAWN's S7 sweep). And the header mis-points the one positive fact PE4
contributed (F5-5). Each is one clause to cure; none touches the chain; and
the pattern — every round's own edits generating next pass's findings in the
description layer while the mathematics sits still — is now five rounds
deep.

— passPE5, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-06).
Machine legs: **(a)** sealed runner exit 0, `VERDICT: ALL GREEN`,
`TOTAL checks 25409`, 0 violations in every counted family, 1,576 WRONGLET
fires, coverage/teeth minima 6/6, md5 `ccb4351c92573f5f962cae4ae952d8dd` = the
seal-commit md5, `git diff dafc0b5 HEAD` = **0 bytes**; output differs from
the committed artifact at 6 wall-clock lines only, empty under timing
normalisation. **(b)** children generator exit 0, regenerated table
**byte-identical** (`diff` empty), A1–A6 PASS, A7 all four legs PASS
(752 nodes / 5,336 children; 0/0/0/0; observed max branching = 2e₀+3 at every
e₀). **(c)** the r4 `K2["one"]` probe reproduced with an independently
written script: `K2["one"] = (((1,0),),)` on the base tower, on both twist
draws, and under a ψ₁ perturbation, while z₁ moves — both runner asserts
confirmed inert, from source and empirically. Nothing in the repo was edited
by this pass except this report.
