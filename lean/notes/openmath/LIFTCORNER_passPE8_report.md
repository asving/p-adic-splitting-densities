# LIFTCORNER passPE8 — hostile verification report (fresh context, post-r7; SIXTH ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD** (post-r7,
commit 4898d32 — the ONE-CLAUSE round: the F7-1 census-unit fix at both census
sites + the r7 round block + the round-close bring-forward; 74 insertions /
13 deletions on the note by `git diff --numstat`, note byte-identical
4898d32 → HEAD, verified), i.e.
after repair rounds **r1** (b2dc120), **r2** (a3112dc + e5b3faf), **r3**
(feedaab), **r4** (6170b09 + 56997be), **r5** (46e6e88), **r6** (91f0cde),
**r7** (4898d32).
**Arc read before the note:** all seven prior reports
(`LIFTCORNER_passPE1..PE7_report.md` at 30e570c / 3367f3c / 39ea0db / 8b53efa /
a5212e8 / f2b48e7 / 58f7060) and the r7 diff (`git diff 91f0cde..4898d32`
restricted to the note: 74 insertions / 13 deletions, 144-line diff listing).
**Cross-checks at source this pass:** the sealed runner's block loop
(`liftcorner_checks.py:31–129`), the wave-18 library's split/closed-form
(`strata_probe.py:385–410` Composite/`split`, `grb_order2_check.py:455` eq12,
`iterlawlift_corner.py:224` closed_form), the committed JSON artifact
(fires/teeth/cov per block), PE6's F6-2 section + bottom line (for the
charge-3 adjudication), PE2 lines 33/54/67 and PE4 line 11 + PE5 F5-4 (the
transcription-recurrence provenance), GRTW2_PROOF's live counter.
**Machine legs (both mandatory):** (a) sealed runner; (b) children generator +
A7 regenerate + compare. **Charge:** (1) the r7 diff line by line, including
the deviation's correctness per the F6-1 precedent; (2) the full
arc-accounting system at HEAD; (3) PE7's two unnumbered observations (the
dropped hedge; the dated preamble rationale) — adjudicate both; (4) one proof
component of my own choosing, decorrelated from the seven reports' choices.
Quote-and-classify, fix nothing; honesty defects graded; fences and boxes read
as part of the statement.

**VERDICT: 0 CRITICAL ERRORS / 0 JUSTIFICATION GAPS — A CLEAN PASS, the
FIRST of the arc. Per the acceptance rule this STARTS the count (the
counter's advance to 1/2 is the orchestrator's ledger action, not this
report's); one more consecutive clean pass accepts.**

Every clause of the r7 diff verifies: the census figures reproduce at both
pinned commits under their stated units (46 occurrences / 42 lines at
46e6e88 with the four doubles all scalar pairs at its lines 301/527/892/930;
51 / 47 at 91f0cde), the superseded wording is quoted verbatim against the
actual deletion, the three transcription-recurrence provenance claims all
verify at their sources (PE2 L33/54/67; PE4 L11 + PE5 F5-4's own provenance
sentence; PE6 F6-2), the bring-forward deviation is CORRECT (every deviated
clause true at HEAD, §2e), and the arc-accounting system is consistent and
true at HEAD as a system (§3). Both of PE7's unnumbered observations are
adjudicated CONCUR — correctly not numbered (§4). My decorrelated component —
the CANDIDATE's integer-data lift-independence clause, the exact clause COR 2's
proof consumes — re-derives cleanly and is grounded at source (§5). Both
machine legs reproduce (§1). Four unnumbered observations are recorded (§6);
none is a defect under the arc's own truth standard.

---

## 1. Machine legs (mandatory, two parts) — BOTH RUN, BOTH REPRODUCE

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
CERT 0 (internal T1/T2(nf=4)+T5) · WRONGLET total fires **1,576** ·
gate-passed **56** · coverage min d1-pairs **6** · teeth min **6**. Sum
56 + 656 + 4176·5 + 3816 + 1 = **25,409** ✓ — every S3 figure matches. My
run's diff against the committed `liftcorner_checks_output.txt`: **5 lines of
the artifact differ, all wall-clock stamp fields** (four per-block `[  N.Ns]`
stamps + `elapsed 4.3s` vs the artifact's `4.4s`); the diff is EMPTY under
timing normalisation. (Stating the unit per the note's own new standing rule:
5 differing LINES per side, 10 lines in the two-sided `diff` listing. Jitter
history: PE4 4, PE5 6, PE6 7, PE7 2, this pass 5 — counted quantities
identical in every recorded run.)

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe8_children_regen.txt ; echo EXIT=$?
EXIT=0
$ diff /tmp/pe8_children_regen.txt liftcorner_tailstab_children_table.txt | wc -c
0        -> BYTE-IDENTICAL TO COMMITTED
```

Assertion failures 0; A1–A6 PASS; A7 PASS — 752 nodes reconciled / 5,336
children enumerated; (i) sum-identity 0; (ii) shape 0; (iii) digit-wise
dev-linearity 0; (iv) branching ≤ 2e₀+3 violations 0, observed max
{2:7, 3:9, 4:11, 5:13, 6:15} = 2e₀+3 at every e₀; "ANY CHILD DROPPING NEITHER
COORDINATE: NO"; "OVERALL: ALL GREEN". Matches the note's [r2, G3] block and
the [r4] machine-leg bracket exactly. Nothing in the repo was edited by this
pass except this report.

---

## 2. Charge (1): the r7 diff line by line — ALL SIX EDIT SITES TRUE AND CORRECTLY PLACED

Diff structure verified against `git diff 91f0cde..4898d32` (six edit sites
across eight unified-diff hunks): the [r7, F7-1] annotation inside the r6
round block; the r7 round block (30 lines); the [r4, F4-5] warrant
replacement; the [r7] grade-box entry; the STATUS BLOCK label + ARC +
NEXT/AUDIT edits; the footer r7 line. Note byte-identical 4898d32 → HEAD
(0-line diff).

**(a) The census figures — independently re-grepped at both pinned commits
by this pass, not transcribed.** At **46e6e88**: `grep -c 'c′'` = **42**
(lines), `grep -o | wc -l` = **46** (occurrences); the four double lines are
its 301 / 527 / 892 / 930 — S1's ξ-conjugate line, S4's setting line,
READ-EQ's b₀-difference line, COR 2's preamble — **all scalar pairs**,
exactly as the r7 text says, so "the four uncounted occurrences are scalar
second occurrences on already-classified lines, so no site was lost" is TRUE.
At **91f0cde**: **47 lines / 51 occurrences**, doubles at its 328 / 554 /
919 / 959 (the same four sentences), all scalar pairs. My own one-by-one
classification at 91f0cde: **33 residue-scalar + 4 covered-cocycle + 14
mention/quotation** — the same totals, the IDENTICAL covered-cocycle bucket
(S1 CANDIDATE display ×2 at its lines 340/341, Q7 row 365, Q9 row 367 — all
inside the correction of record ✓), and the same conclusion: **NO fourth
bare-`c′`-as-cocycle site**. My split differs from PE7's transcribed
34 + 13 at exactly ONE occurrence — see observation O-b (§6); the material
warrant is unaffected under either convention.

**(b) The r7 round block.** PE7 = 58f7060, **0 CRITICAL + 1 gap (minor)** ✓
(its verdict line, quoted: "0 CRITICAL ERRORS / 1 JUSTIFICATION GAP
(minor)"); "all four r6 hunks verified true and correctly placed except one
clause" ✓ (PE7 §2); "the record system judged CONSISTENT AND TRUE AT HEAD for
the first time in the arc" ✓ (PE7 bottom line: "for the first time in the arc
the status block, grade box and dating record are simultaneously true at
HEAD"); "r6's disclosed NEXT/AUDIT deviation judged CORRECT" ✓ (PE7 §3b);
"the mathematics clean on its SEVENTH hostile reading" ✓; "both machine legs
re-run clean" ✓ (PE7 §1). The F7-1 restatement is faithful (hit-LINE count,
46 on 42, four lines carrying two, all scalar pairs — re-verified, (a)).
"both census sites now carry PE7's occurrence-level warrant of record" ✓
(the F4-5 bracket restated in full; the r6 block clause annotated with the
dated [r7, F7-1] bracket carrying the same warrant + pointer). The
**superseded quote is VERBATIM** against the actual deletion: the deleted
F4-5 tail was exactly `census is COMPLETE — PE6's sweep of "all 42 'c′'
occurrences" at its HEAD (46e6e88) found NO fourth site.` and the round block
quotes the full original sentence (its head "with Q9 the census is COMPLETE —"
survives in the replacement — quoting the whole sentence for context is
faithful; the changed part is the tail).

**(c) The PROVENANCE clause — all three recurrence attributions verified at
source.** (1) PE2's "bit-identically": PE2's report carries the unqualified
form at line 33 ("The sealed runner re-runs bit-identically") and line 54
(section header), qualified at line 67 — matching [r3, F-C]/[r4, F4-3] ✓.
(2) PE4's "S9": PE4's report line 11 reads "ITERLAWN_PROOF_2026-08-08.md S0.1
+ the S9 dependency-sweep table", and PE5's F5-4 records "The mislabel
originates in PE4's own report header … which r4 transcribed" ✓. (3) PE6's
"42 occurrences": PE6's F6-2 reads "My own sweep of all 42 `c′` occurrences
at HEAD finds NO fourth site" — the figure and the unit word originate there,
r6 transcribed them in quotation marks ✓. THIRD recurrence of the mechanism ✓
(the count is of transcription-bred defects: r2←PE2, r4←PE4, r6←PE6). The
standing rule ("quote counts only WITH THEIR UNIT AND COMMIT") is applied by
the r7 text itself — every count it states carries both.

**(d) The [r4, F4-5] warrant at HEAD, and HEAD-truth of the completeness
claim.** The new warrant is commit-pinned ("counts, at its HEAD 91f0cde") so
it reproduces as stated (verified, (a)). The r7 edits themselves add `c′`
occurrences — at HEAD the raw census is **54 occurrences / 50 lines** — and I
classified all three net-new occurrences: every one is a mention/quotation
inside the correcting brackets themselves (the [r7, F7-1] annotation's two
quoted "all 42 `c′` occurrences" and the new warrant's own "51 `c′`
occurrences" / "bare-`c′`-as-cocycle" text). The four double lines at HEAD
(363/589/954/1002) are the same four scalar-pair sentences. **The census
remains materially COMPLETE at HEAD: no fourth bare-`c′`-as-cocycle site
exists.** The commit pin is what makes the warrant stable under its own
growth — the standing rule doing exactly its job (observation O-d records
the 54 ≠ 51 arithmetic so a future pass does not mistake it for drift).

**(e) The deviation — VERIFIED CORRECT per the F6-1 precedent.** r7 brought
the round-close record surfaces to HEAD truth rather than transcribing PE7's
literal cure-state (the r6 precedent, which PE7 §3 verified correct). Every
clause of every deviated surface is true at HEAD: ARC line — every hop
(seven passes + seven repair rounds + the PE8 pointer) re-verified against
the seven reports and git (1C+3G / 0C+5G / 0C+5G FIRST /
0C+6G SECOND / 0C+5G THIRD / 0C+3G FOURTH / 0C+1G-minor FIFTH; report commits
30e570c / 3367f3c / 39ea0db / 8b53efa / a5212e8 / f2b48e7 / 58f7060, each
verified to exist with the matching verdict line and date; on the "1 minor"
wording see O-a) ✓; NEXT/AUDIT — "PE8 next" ✓ (this pass), "r7 edits
unaudited going in" ✓ (no pass between 4898d32 and HEAD; note byte-identical),
"r6 line-audited by PE7 — all four hunks verified true except the one census
clause" ✓, "r5 by PE6, r4 by PE5" ✓, "earlier edit sets read twice or more" ✓
(under the bullet's established convention: r3 edits now at four passes, r2
at five, r1 at six), machine-leg clause ✓ (PE7 §1 + my §1); [r7] grade-box
entry — "SEVEN hostile passes have now run" ✓, PE7 = FIFTH acceptance
attempt ✓, all four content claims about PE7's findings ✓, audit-state
sentence ✓; footer r7 line — wallclock 2026-08-06 = commit date (10:15) ✓,
terminator punctuation cascade correct ✓ (r6's "." → ";", r7 ends ".").

---

## 3. Charge (2): the full arc-accounting system at HEAD — CONSISTENT AND TRUE NOW

The four status-of-record surfaces (STATUS BLOCK five-liner; S4.3 grade box
through [r7]; the seven round blocks; the footer dating record) agree with
each other and with the world at HEAD: seven passes run, r7 applied, r7 edits
unaudited, PE8 next, counter 0/2 pending this pass. Sentence-level checks:

* **Hashes and verdicts.** All seven report commits + all eight repair
  commits resolve; each report commit adds exactly its report (PE4's 856-line
  file = WIP checkpoint fa67ef2 + final 8b53efa — disclosed in its own commit
  message, benign); each round block's cited verdict matches its report's
  verdict line **verbatim in count and class** (PE1 1C+3G … PE7 0C + 1
  JUSTIFICATION GAP (minor)).
* **Footer wallclocks vs commit dates:** r1–r4 = 2026-08-05 (17:08 / 18:28 /
  19:42 / 21:12–21:19) ✓; r5–r7 = 2026-08-06 (08:23 / 09:21 / 10:15) ✓.
* **COUNTER bullet.** "no pass has been clean" ✓ TRUE THROUGH PE7 (all seven
  verdict lines checked; this pass is the first clean one, and the bullet is
  the pre-PE8 record). "GRTW2 itself 0/2" ✓ CURRENT (GRTW2_PROOF header line 5
  carries "acceptance counter 0/2" at HEAD; GRTW2 untouched since 46e6e88 per
  the fence sweep below).
* **PROVED / CONDITIONALITY bullets.** Unchanged at r7 except nothing;
  re-checked against the world: item (5) still OWED, the F3 box's (a)/(b)
  still owed, ILNRES NOT edited (fence sweep), the e₀ = 1 emptiness fact still
  attributed to PE4's positive record ✓.
* **"Items (1), (2), (7): re-derived by three hostile passes"** ✓ still
  accurate — PE5/PE6/PE7 added line-audits and fresh-eyes complements, no new
  full re-derivations of (1)/(2)/(7); the count stays PE2+PE3+PE4.
* **FENCES.** `git log 46e6e88..HEAD --name-only`: the LIFT arc touched only
  the note + its PE6/PE7 reports; all other touched files belong to the
  JB/JC/WM arcs and the ledger; `verification/openmath/liftcorner_*`
  untouched since the seal (0-byte diff re-verified at HEAD); ILNRES /
  ITERLAWN / ITERLAWLIFT_CORNER / GRTW2 bodies untouched ✓.
* **Dated text discipline.** Every stale close carries its date bracket
  ([r4]-close, [r6]-close in the grade box; r1–r6 round-block terminators);
  the archive region is untouched by r7 (no hunk inside ARCHIVE-BEGIN/END) ✓.

---

## 4. Charge (3): PE7's two unnumbered observations — BOTH ADJUDICATED: CONCUR, correctly not numbered

**(i) The dropped hedge** (r6 round block: "all three gaps in record surfaces
r5 did not touch" vs PE6's "in what r5 did NOT touch **(or touched one clause
short)**"). CONCUR with PE7 — not a defect. Grounds, from PE6's own report
re-read this pass: PE6's F6-2 formally indexes its offending passage at **the
sealed Q9 sheet row** ("Offending passage (S2 sheet, Q9 row, sealed pre-run
text)"), which r5 did not touch; its headline places the gap "**outside** the
correction of record even after the r5 extension"; and its §2 line-audit
separately certifies every r5 insertion true and correctly placed ("Coverage
one row short — finding F6-2" is recorded against the coverage, not against
any inserted line). Under the source's own formal site assignment the
unhedged sentence is TRUE; the fuller provenance (r5 inherited PE5's
undercount) is preserved verbatim in the note at the F6-2 clause itself ("r5
therefore inherited" survives via the round block's own history) and in PE6's
report of record. Unlike the arc's numbered transcription findings
(F-C/F4-3, F5-4, F7-1), no truth value flips and no figure fails to
reproduce. Correctly left unnumbered.

**(ii) The dated preamble rationale** (STATUS BLOCK preamble: "The status
surface produced findings in three consecutive passes — PE2's G2 …, PE3's
F-C/F-D, PE4's F4-2/F4-3 — so it is now five lines"; the streak reached five
with PE5's F5-1 and PE6's F6-1). CONCUR with PE7 — not a defect. The sentence
is the r4 regeneration's design rationale: past-tense history with named
findings, all TRUE as stated; it asserts nothing about later passes. The
block label "[r4; edited r5, r6, r7]" carries the dating; the two later
status-surface findings are recorded thirty lines away in the same grade box
([r6]/[r7] entries) and in the ARC line's verdict counts, so the system
discloses the full streak. The defect direction also matters: the stale count
UNDERSTATES the case for the minimal template (an understatement of the
note's own past defects, not an overclaim of its results). Correctly left
unnumbered. (If a future round touches the preamble anyway, "three
consecutive passes (five by PE6)" is the one-clause alignment.)

---

## 5. Charge (4): the decorrelated re-derivation — the CANDIDATE's integer-data lift-independence clause (consumed by COR 2) — HOLDS

**Choice and decorrelation.** The S1 CANDIDATE's closing clause — "with all
integer data (splits, D₁, δ₂, windows) lift-independent" — is sealed pre-run
text and is CONSUMED as a named input by COR 2's proof ("plus z₁ = ξ·z₁′ (S1)
and **the lift-independence of D₁** (S1/S2)"). Sweep of the seven reports:
PE7 checked the D₁ FORMULA's transcription against wave-18; PE4 instantiated
COR 2 on one concrete orbit member; PE3 derived the count arithmetic; none
derives the lift-independence claim in general. (My first-choice component,
the Q9 wrong-letter equivalence, turned out on the decorrelation sweep to be
partially covered — PE1's charge-(2) leg records the implication in one
sentence — so it is demoted to the secondary leg below, disclosed as such.)

**The derivation.** The split of γ is the unique solution of the two-level
division identities: s₂, u₂ from γ = e₁u₂ + s₂h₁ with 0 ≤ s₂ < e₁; then
γ₁ = u₂ − s₂·w₁Φ₁; then s₁, u₁ from γ₁ = e₀u₁ + s₁h₀ with 0 ≤ s₁ < e₀
(existence/uniqueness: gcd(e_i, h_i) = 1, Bézout). Its only inputs are the
ledger integers (e₀, h₀, e₁, h₁, w₁Φ₁). On the S1 orbit, w₁Φ₁ = e₀h₀ is part
of the ORBIT'S DEFINITION ("deg = e₀d₀, **w₁ = e₀h₀**, nonzero order-1
residual") and the remaining integers are level-0/2 data no lift byte enters
— so the splits are lift-independent. Hence so are δ₂ = ⌊(s₂+s₂′)/e₁⌋ and
D₁ = (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀ (functions of splits and the shared integers
ℓ₀, γ₂, e₀ alone), and the windows (Γ₀ is a rounded expression in
e₁, γ₂, e₀, h₀, E₂; W1/W3 are Γ₀-offsets). ∎

**Grounded at source (both legs of the claim).** (i) Code: `Composite.split`
(`strata_probe.py:403`) reads only `(e₁, h₁, w₁Φ₁, e₀, h₀)` via `eq12`
(`grb_order2_check.py:455` — deterministic Bézout solution of u·e + s·h = γ,
0 ≤ s < e); `closed_form` (`iterlawlift_corner.py:224`) computes d₂ and
num = s₁a+s₁b−s₁c+ℓ₀γ₂d₂ from splits + `T.l0, T.gamma2, T.e0` only; `Gamma0`
(`strata_probe.py:400–401`) from `(e₁, γ₂, e₀, h₀, E₂)` only. The single
lift-dependent input to the closed form is the LETTER `C.z1_2` — exactly the
CANDIDATE's content. (ii) Harness: the twisted tower and its base tower come
from the same `LC.make_tower(kind, p, d₀, r₀, r₁, ·)` parameters
(`liftcorner_checks.py:35/:144`), so their ledger integers agree by
construction, and Q1's gate certifies each orbit member lawful for its own
ψ₀′ (pinning w₁ = e₀h₀ on the abstract side). The clause COR 2 consumes is
therefore PROVED, not merely transcribed. **No finding.**

**Secondary leg (disclosed as partially correlated — PE1 recorded the
implication in one sentence; the following quantitative ties are new).**
The wrong-letter control's algebra: with cf = z̄^{δ₂}(z₁′)^{D₁} and
wrong = z̄^{δ₂}(z₁)^{D₁}, the identity z₁ = ξz₁′ gives **wrong = cf·ξ^{D₁}**
exactly, so at any pair where TLAW holds (c = cf) and K₂ is a field with
z̄, z₁′ = −c′, ξ all nonzero and D₁ ∈ ℤ (Q5): mism = (c ≠ wrong) ⟺
(ξ^{D₁} ≠ 1) = pred. Consequences verified against the artifacts: (α) the
fire set must EQUAL the teeth set per block — the committed JSON gives
fires == teeth on **all 48 twisted blocks** (totals 1,576 == 1,576, per-block
equality everywhere; min teeth 6 matching Q8) — the sharp prediction of the
equivalence, previously checked only as the runner's own per-pair assert;
(β) the count reconciliation TLAW − WRONGLET = 4,176 − 3,816 = **360** =
exactly the pair mass of the 8 ξ = 1 dense controls (rows CB/CF × 4 rings,
E₂ = 6/3, pairs per tower 2E₂²: 4·(72+18) = 360), quantifying the runner's
`if not xi1_is_one` skip-gate (line 109) against S2's roster. Both cohere;
**no finding.**

---

## 6. Unnumbered observations (recorded, not findings)

* **(O-a)** The ARC line's hop "PE7 (0C + 1 minor; the FIFTH acceptance
  attempt)" compresses PE7's verdict "0 CRITICAL / 1 JUSTIFICATION GAP
  (minor)" by dropping the class word: the note's two adjacent surfaces (r7
  round block "0 CRITICAL + 1 gap (minor)"; [r7] grade-box "0 CRITICAL + 1
  gap, minor") carry it, and this note has never used "minor" as a standalone
  class, so the literal reading ("one finding, graded minor") is true — but a
  reader importing the sibling arcs' vocabulary (where "minor" is a class
  BELOW gap, e.g. JB PE6's "0C + 2 gaps + 1 minor") could mis-parse the hop as
  zero-gap. One-word alignment available ("0C + 1G, minor"). Not numbered:
  no arc-accounting sentence is false, and the report of record is cited at
  both neighboring surfaces.
* **(O-b)** The transcribed sub-split "34 residue-scalar + 13
  mention/quotation" of PE7's 51-occurrence census is
  classification-convention-dependent at exactly ONE occurrence — 91f0cde
  line 941, the quoted display `ξ := c₀/c′` INSIDE the F4-5 bracket (a
  quotation whose `c′` denotes the scalar): my independent classification
  puts it in mention/quotation (giving 33 + 4 + 14), PE7's in scalar (34 + 4
  + 13). The totals (51/47), the whole covered-cocycle bucket (the same 4
  sites), and the NO-fourth-site conclusion reproduce identically under both
  conventions, and the note transcribes the split with attribution, unit and
  commit per its own standing rule. Not numbered — unlike F7-1, the stated
  universe DOES reproduce under its own unit; only a one-occurrence
  use/mention boundary inside the correcting bracket itself wobbles.
* **(O-c)** The r7 round block's bring-forward list ("the STATUS BLOCK
  ARC-line + NEXT/AUDIT bullet, a dated [r7] grade-box entry, and the footer
  r7 dating line — NOTHING else") omits the STATUS BLOCK label bump
  ("[r4; edited r5, r6]" → "[r4; edited r5, r6, r7]") — the same
  self-exclusion structure PE7's observation (iii) declined to number at
  r6/r5. The label edit is itself a dating record (self-evidencing, and
  REQUIRED by the block's own convention once ARC/NEXT-AUDIT are edited).
  Not numbered, consistent with two prior adjudications of the identical
  structure.
* **(O-d)** HEAD-census arithmetic, recorded against future drift-misreads:
  at HEAD (4898d32) the raw `c′` census is 54 occurrences / 50 lines — the
  warrant's 51/47 is commit-pinned to 91f0cde and the 3 net-new occurrences
  are all mention/quotation inside r7's own correcting brackets (no new bare
  site; same four scalar-pair double lines). The completeness claim is TRUE
  at HEAD; a PE9 grepping HEAD should expect 54/50, not 51/47.

## 7. Bottom line

**A CLEAN PASS: 0 CRITICAL, 0 JUSTIFICATION GAPS — the first of the arc,
on the SIXTH acceptance attempt.** The one-clause r7 round is exact: its
figures reproduce at both pinned commits under their stated units, its
provenance claims verify at all three sources, its deviation is the correct
bring-forward, and the record system remains true at HEAD as a system. The
mathematics is now eight readings deep with no defect ever found below the
description layer; my decorrelated component (the lift-independence clause
COR 2 consumes) proves out at both the abstract and the source level. Per
the acceptance rule, this pass STARTS the count: one more consecutive clean
hostile pass on THIS text (no repair round intervening, since there is
nothing to repair) closes the arc at 2/2. The four observations above are
alignment options, not owed repairs.

— passPE8, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-06).
Machine legs: **(a)** sealed runner exit 0, `VERDICT: ALL GREEN`,
`TOTAL checks 25409`, 0 violations in every counted family, 1,576 WRONGLET
fires, coverage/teeth minima 6/6, md5 `ccb4351c92573f5f962cae4ae952d8dd` =
the seal-commit md5, `git diff dafc0b5 HEAD` = **0 bytes**; output differs
from the committed artifact at 5 wall-clock-stamp lines only, empty under
timing normalisation. **(b)** children generator exit 0, regenerated table
**byte-identical** (`diff` empty, 0 bytes), A1–A6 PASS, A7 all four legs PASS
(752 nodes / 5,336 children; 0/0/0/0; observed max branching = 2e₀+3 at every
e₀ ∈ {2,…,6}). Nothing in the repo was edited by this pass except this
report.
