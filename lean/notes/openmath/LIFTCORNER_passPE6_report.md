# LIFTCORNER passPE6 — hostile verification report (fresh context, post-r5; FOURTH ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD** (post-r5,
commit 46e6e88 — the deliberately MINIMAL round: five one-line fixes + one
round block + the ARC line; 32 insertions / 9 deletions), i.e. after repair
rounds **r1** (b2dc120), **r2** (a3112dc + e5b3faf), **r3** (feedaab), **r4**
(6170b09 + 56997be) and **r5** (46e6e88).
**Arc read in full before the note:** all five prior reports
(`LIFTCORNER_passPE1..PE5_report.md` at 30e570c / 3367f3c / 39ea0db / 8b53efa /
a5212e8) and the r5 diff (`git show 46e6e88`).
**Cross-note read:** ITERLAWN_PROOF_2026-08-08.md (S7 sweep table in full, S9
scope box), BRIDGE_ADJUDICATIONS_2026-07-30.md (the r5 adjudication entry with
the arc-dynamics diagnosis).
**Machine legs (both mandatory):** (a) sealed runner; (b) children generator +
A7 regenerate + compare. **Charge:** (1) the r5 diff line by line — every
insertion true, every fix correctly placed; (2) the whole note once more with
fresh eyes on the complement (S1 setup, S3 family-table arithmetic, the COR
displays); (3) the arc-record arithmetic end to end. Quote-and-classify, fix
nothing; honesty defects graded; fences and boxes read as part of the
statement.

**VERDICT: 0 CRITICAL ERRORS / 3 JUSTIFICATION GAPS. NOT A CLEAN PASS — the
acceptance counter stays 0/2 and no acceptance slot opens.**

The r5 design goal — a round too small to breed defects in its own new
prose — is MET on the diff itself: **all 32 inserted lines verify true and
all five fixes land at exactly the sites PE5 named** (§2 below, line by
line). The mathematics is untouched for the sixth consecutive reading (my
fresh-eyes complement — the S1 orbit/applicability arithmetic, the S3 family
sums, the COR 1/COR 2 displays and COR 2's two-line algebra, the b₀-main
difference bound in S4.2, the δ₁ = 1 emptiness at e₀ = 1, and the
counter-instance's polynomial identities — all re-derived clean, §4). Both
machine legs reproduce: sealed runner byte-untouched (md5 intact, 0-byte diff
vs the seal dafc0b5), exit 0 at 25,409/0 with every family figure matching;
children table regenerates byte-identically with A7's four legs PASS.

The three gaps are all in what r5 did NOT touch (or touched one clause short),
and all three are arc-record / notation-record defects, not chain defects: the
minimal round updated the STATUS BLOCK's ARC line but left the same block's
NEXT/AUDIT line asserting "PE5 … next" / "unaudited going in: the r4 edits" —
the note's declared status of record now contradicts itself two bullets apart
(F6-1); the F5-3 renaming/correction-of-record extension stops one row short —
S2's sealed **Q9** row also writes the measured cocycle as bare `c′`, a third
collision site PE5's two-site census missed and r5 therefore inherited (F6-2);
and the note's closing dating record lists rounds r1–r4 applied but not r5
(F6-3). None touches the chain, the measurement, or the grade.

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
56+656+4176+4176+4176+0+4176+0+3816+4176+1 = **25,409** ✓ — **every S3 figure
matches.** My run's diff against the committed `liftcorner_checks_output.txt`
is **7 lines, all wall-clock** (six per-block stamps + `elapsed 4.3s` vs
`4.4s`), empty under timing normalisation (PE4 recorded 4 such lines, PE5
recorded 6 — jitter varies per run; every counted quantity identical in all
recorded runs including mine).

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe6_children_regen.txt ; echo $?
0
$ diff /tmp/pe6_children_regen.txt liftcorner_tailstab_children_table.txt | wc -c
0        -> BYTE-IDENTICAL TO COMMITTED
```

§7 of my regeneration: assertion failures 0; A1–A6 PASS; A7 PASS — 752 nodes
reconciled / 5,336 children enumerated; (i) sum-identity mismatches 0;
(ii) shape violations 0; (iii) digit-wise dev-linearity mismatches 0;
(iv) branching ≤ 2e₀+3 violations 0 with observed max {2:7, 3:9, 4:11, 5:13,
6:15} = 2e₀+3 at every e₀; "ANY CHILD DROPPING NEITHER COORDINATE: NO";
"OVERALL: ALL GREEN". Matches the note's [r2, G3] block and the [r4]
machine-leg bracket exactly. Nothing in the repo was edited by this pass
except this report.

---

## 2. Charge (1): the r5 diff, line by line — ALL 32 INSERTIONS TRUE, ALL FIVE FIXES CORRECTLY PLACED

Diff structure verified: exactly **8 hunks** = the five fixes (F5-3 at two
sites) + the r5 round block + the ARC-line update; insertions 1+20+3+1+2+1+3+1
= 32, deletions 1+2+1+1+1+2+1 = 9, matching the commit stat. Hunk by hunk:

* **F5-5 (hunk 1, r4 header):** "(S4.3, COR 1)" → "(S5 STATUS BLOCK, PROVED
  bullet)". TRUE — the δ₁ = 1-empty-at-e₀ = 1 record does sit in the PROVED
  bullet ("COR 1 (… — and δ₁ = 1 is EMPTY at e₀ = 1 …)"), and nowhere in
  S4.3. Correctly placed at the exact pointer PE5 quoted. I re-derived the
  fact itself: δ₁ = 1 needs s₁+s₁′ ≥ e₀ with s₁, s₁′ ≤ e₀−1; at e₀ = 1 that
  is 0 ≥ 1. ✓
* **The r5 round block (hunk 2, 20 lines):** every factual claim verified —
  PE5 = commit a5212e8 with 0 CRITICAL + 5 gaps, all five in the r4 edits ✓
  (PE5's own verdict line); "the ledgered arc-dynamics diagnosis (each
  round's new prose has bred ~5 defects)" ✓ verbatim in the ledger
  (BRIDGE_ADJUDICATIONS, r5 adjudication entry: "each repair round introduces
  ~5 defects in its own new prose; convergence requires a ZERO-NEW-DEFECT
  round ⟹ r5 = MINIMAL (five one-line fixes, nothing else, no
  restructuring)"); each of the five superseded wordings is quoted VERBATIM
  against the pre-r5 text (checked against the 46e6e88 diff's deletion
  lines); the CONDITIONALITY quote "(5) PROP's rung-≥2 clause-(ii) census is
  OWED" verbatim at its site ✓; "the 22-row sweep sits in ITERLAWN S7,
  verified at source; ITERLAWN's S9 is a table-free scope box" ✓ — I verified
  at source: the DEPENDENCY-CLAIM SWEEP TABLE (rows 1–22) sits inside "## S7.
  THE CONDITIONALITY LEDGER" and "## S9. Scope box — fences" is a bullet
  list, no table; "plus the STATUS BLOCK ARC-line update, NOTHING else" ✓
  accurate against the diff (the PROVED-line edit IS F5-1); "both machine
  legs BYTE-FROZEN and untouched" ✓ (§1); counter 0/2 ✓; PE6 next ✓.
* **F5-2 (hunk 3, S2 (c) [r4, F4-1] terminator):** the parenthetical now
  reads "(the ASSERTS enter no counted predicate of S3 and no proof step of
  S4; ψ₁ and K₂ themselves enter S4.2 as shared read data)". BOTH halves
  TRUE: no S3 predicate and no S4 proof step consumes either runner assert
  (the r3 ψ₁-site walk, re-confirmed by PE5's independent probe), and S4.2's
  first proof sentence does list ψ₁/K₂ among the shared read data. The
  repaired sentence's inference ("the same walk gives it for (ii) verbatim")
  is now supported by a true parenthetical. Correctly placed. ✓
* **F5-3a (hunk 4, S3 Q7 bullet):** "c_base = c^{Φ′}·ξ^{D₁}" — the live
  false-parsing site PE5 named, renamed exactly per the [r4, F4-5]
  convention. ✓
* **F5-3b (hunk 5, [r4, F4-5] bracket):** "…correction of record for it and
  for S2's sealed Q7 sheet row, whose `c′` is likewise this cocycle". TRUE —
  the runner's CHI check compares `base_cc[(ga,gb)] == c·ξ^{D₁}` with `c` the
  MEASURED cocycle on the twisted tower, so the Q7 row's bare `c′` is indeed
  this cocycle. Correctly placed. (Coverage one row short — finding F6-2.)
* **F5-4 (hunk 6, [r4, F4-4]):** "ITERLAWN_PROOF's S7" — TRUE at source
  (above). Grep confirms no other live "S9" site remains in the note (the
  only "S9" occurrences at HEAD are the r5 block's quotation of the corrected
  wording). ✓
* **ARC line (hunk 7):** "… → r4 → PE5 (0C + 5G; the THIRD acceptance
  attempt) → r5 (this round: the five one-line fixes F5-1…F5-5, nothing
  else) → PE6 = the next acceptance attempt." All hops verified against the
  five reports and git ✓ (PE5's header: THIRD acceptance attempt).
* **F5-1 (hunk 8, STATUS BLOCK PROVED line):** ", and PROP's rung
  propagation" dropped; the line now ends "…and COR 2 on the harness orbit."
  — grammatical, and the CONDITIONALITY bullet two lines below carries PROP's
  status of record ("(5) … OWED"). Correctly placed; exactly PE5's cure. ✓

---

## 3. FINDINGS (all in what r5 left untouched or under-extended; ranked)

### F6-1 — JUSTIFICATION GAP: the STATUS BLOCK — "the note's whole status of record" — is internally contradictory at HEAD: its ARC line (r5-updated) says PE6 is next, while its NEXT/AUDIT line still says "PE5 … next" and "Unaudited going in: the r4 edits"

Offending passage (S5, STATUS BLOCK, fifth bullet, NOT touched at r5):

> "* **NEXT / AUDIT STATE.** PE5, a fresh hostile pass on THIS text.
> Unaudited going in: **the r4 edits**. Read once: the r3 edits (PE4). Read
> twice: the r2 edits (PE3, PE4). … Both machine legs BYTE-FROZEN and re-run
> clean at PE4 (…)."

Against the same block's first bullet, two bullets up (r5-updated):

> "* **ARC.** … → r4 → PE5 (0C + 5G; the THIRD acceptance attempt) → **r5
> (this round: …)** → **PE6 = the next acceptance attempt.**"

Both sentences of the NEXT/AUDIT bullet's opening are FALSE at HEAD: PE5 has
run (its report is a5212e8, quoted by the r5 header 900 lines earlier), the
next pass is PE6, and the unaudited surface going in is **the r5 edits** —
the r4 edits were PE5's designated target and yielded all five of its
findings. The block cannot claim a snapshot defense: its own standing rule
("**Standing rule for future rounds: edit these five lines; do not grow a
sixth**") makes it the live status surface, and r5 DID edit two of the five
lines (ARC, PROVED) while leaving the other stale — so the block is neither
an r4 snapshot nor a current record but a mixture, with its two forward
pointers naming different passes. (The block's header label "STATUS BLOCK
[r4]" is likewise stale after an r5 edit; and the S4.3 grade box's most
recent entry — the dated [r4] bracket — also still closes "the r4 edits are
UNAUDITED … PE5 … is the next acceptance attempt", the first round since r2
that the grade box was not brought forward; those two carry a dated-bracket
defense and are recorded here as adjacent sites, not numbered separately.)
This is the arc's own recurring genre — PE3's F-D numbered exactly an
internal inconsistency in the status surface's audit accounting.
**Failure scenario:** a fresh auditor consulting the declared status of
record directs the next hostile pass at the r4 edits (already mined by PE5)
and the actually-unaudited r5 edits escape their audit; the r5 header's
disclosure ("plus the STATUS BLOCK ARC-line update, NOTHING else") makes the
omission deliberate but, by this arc's own precedent (F4-2: disclosure
elsewhere does not cure stale text standing bare), does not cure it.
**Mitigation (why GAP, not worse):** the true state is stated twice on the
same page (the r5 header block and the ARC line), no chain step consumes the
NEXT/AUDIT line, and the cure is one line.

### F6-2 — JUSTIFICATION GAP: a THIRD bare-`c′`-as-cocycle site survives — S2's sealed Q9 sheet row — outside the correction of record even after the r5 extension; PE5's "two surviving sites" census undercounted, and r5 inherited the undercount

Offending passage (S2 sheet, Q9 row, sealed pre-run text):

> "| Q9 WRONGLET | control: per-pair (**c′** ≠ wrong-letter form) ⟺
> (ξ^{D₁} ≠ 1), exact set equivalence; total fires > 0 | 0 / fires |"

Verified at source: the runner computes `mism = (c != wrong)` where `c` is
the MEASURED COCYCLE on the twisted tower (from `measured_cocycle(T, C, ga,
gb)`) and `wrong = z̄^{δ₂}·z₁_old^{D₁}` — the row's "c′" is the per-pair
measured cocycle, the very function [r4, F4-5] renames `c^{Φ′}` (a per-pair
comparison against the pair-dependent wrong-letter form cannot be the
pair-independent residue scalar). Under the convention's own rule ("**`c′`
(no arguments) stays the RESIDUE SCALAR**") the row now parses as "residue
scalar ≠ wrong-letter form" — not what the control tested. The row is sealed
pre-run text (byte-unchanged since dafc0b5), so it deserves exactly the
correction-of-record treatment the bracket now gives S1's CANDIDATE and S2's
Q7 row — but the r5-extended clause names the Q7 row **only**. Provenance of
the miss: PE5's F5-3 claimed "The two surviving cocycle-as-`c′` sites, from
my grep of the whole note" — an undercount (its grep evidently keyed on the
χ-ratio formula, which the Q9 row does not contain); r5 faithfully
implemented PE5's named cure and stopped where PE5 stopped. My own sweep of
all 42 `c′` occurrences at HEAD finds NO fourth site (every other occurrence
is the residue scalar, the S1 CANDIDATE's covered `c′(γ,γ′)`, or a
quotation). Consequence for the r4 header's summary: "the `c′` collision …
**is fixed** by renaming the COCYCLE to `c^{Φ′}`" retains one residual
counterexample. **Failure scenario:** a reader applying the convention to
the sealed sheet mis-reads what the 3,816-sample control compared.
**Mitigation:** sealed text, no consumer (S3's Q9 bullet describes the
control correctly without the symbol; no chain step reads the sheet row's
notation); one clause to cure.

### F6-3 — JUSTIFICATION GAP (minor): the note's closing dating record omits r5 — it lists "repair round rN applied" for r1–r4 only

Offending passage (the note's final lines):

> "— LIFT-CORNER unit, campaign date 2026-08-08 (wallclock 2026-08-04);
> repair round r1 applied … r2 applied … r3 applied … repair round r4
> applied 2026-08-08 campaign (wallclock 2026-08-05)."

Every prior round appended its line to this record; r5 (wallclock
2026-08-06) did not, so the closing tally of applied rounds reads FOUR
against the header's and the ARC line's FIVE. The r5 date exists only inside
the r5 round block. **Failure scenario:** a reader (or a future correction
bracket, in an arc that has already litigated provenance twice — F4-3,
F5-4) dates the note's last repair to 2026-08-05 from the record built for
exactly that purpose. One line to cure.

---

## 4. Charge (2): the fresh-eyes complement — S1 setup, S3 arithmetic, COR displays — ALL CLEAN

* **S1 orbit frame re-derived:** ψ₀^{(ξ)} = ξ^{−1}ψ₀(ξy) = y + c₀/ξ = y + c′
  at ξ = c₀/c′ ✓; z₁ = ξ·z₁′ from z₁ = −c₀, z₁′ = −c′ ✓; the amin bound
  w₀(b_k) ≥ ⌈(e₀−k)h₀/e₀⌉ is the Newton-polygon line, and "strict-above
  automatic" holds because gcd(e₀,h₀) = 1 makes (e₀−k)h₀/e₀ non-integral for
  1 ≤ k ≤ e₀−1 ✓; COR 2's algebra: c_base = z̄^{δ₂}(ξz₁′)^{D₁} =
  c^{Φ′}·ξ^{D₁} ✓.
* **S2 applicability arithmetic re-derived:** twistable instances = 2 d₀ = 2
  rows × 4 rings + 4 d₀ = 1 rows × 2 p = 3 rings = 16 ✓; twisted towers =
  8·2·2 (two draws in 𝔽₄) + 8·1·2 (one draw in 𝔽₃) = 48 ✓; + 8 ξ = 1 dense
  controls = 56 gate checks ✓; 24 base towers = 6 rows × 4 rings ✓.
* **S3 family-table arithmetic:** the eleven counted families sum to 25,409 ✓
  and every figure matches my §1(a) re-run, including LOC's `pred 0 obs 0
  (0)` and the nested-only `viol("LOC", …)` sites (verified in the runner's
  PV/INT/TLAW violation branches, exactly as the [r3, F-E] bullet says) ✓.
* **COR displays' wording:** COR 1's scope/machine cites (Q10 + wave-18) ✓;
  COR 2's display uses `c^{Φ′}` and "residue scalar c′" consistently
  post-rename ✓; the [r1, F3] box unchanged and accurate ✓; the THEOREM's
  display letter z₁′ = −c′ matches S1 and the runner's `C.z1_2` ✓.
* **Spot re-derivations while passing:** S4.2's b₀-main difference bound
  (w₀(ĉ′ − lift(c′)) ≥ 1 since both lift c′; ledger ≥ Γ + e₁e₀) ✓; the
  counter-instance's identities re-checked in exact arithmetic
  (Φ′ = x⁴+4x³+5x²+4x+3; xΦ₀² = (x−2)Φ′ + (6x+2)Φ₀ + (−2x+4) with digit
  weights 3/3/2 vs ω = 2, slacks 1/1/0) ✓; the CONTENT sub-lemma's division
  induction ✓.

**Charge (3): arc-record arithmetic end to end.** Round headers r1–r5:
pass verdicts and report commits all verified against the five reports and
git (PE1 1C+3G / PE2 0C+5G / PE3 0C+5G / PE4 0C+6G / PE5 0C+5G; acceptance
attempts FIRST = PE3, SECOND = PE4, THIRD = PE5, per the reports' own
headers) ✓. Naming discipline (r2's pass/round clarification) consistent
throughout ✓. Counter 0/2 with the correct reason at every occurrence ✓;
W-2 cap language consistent (GRTW2 still 0/2 in the repo) ✓. Machine-leg
brackets [r1]–[r4] accurate; r5's byte-frozen claim verified by my own runs
✓. The grade box's dated stack (r0 → r2 → r3 → r4) is internally consistent
per date; its missing r5 entry and the STATUS BLOCK's stale NEXT/AUDIT line
are finding F6-1; the footer's missing r5 line is F6-3. The ARCHIVE region
is untouched by r5 (diff) and PE5 verified it byte-identical to feedaab ✓.

**Unnumbered observations (recorded, not findings):** (i) r5's five fixes
were applied as in-place edits inside dated [r4, …] brackets and the r4
header, with the superseded wording quoted only in the r5 round block — no
site-local [r5] markers; nothing is false at HEAD and nothing was silently
deleted, but the bracket system's site-level dating is no longer
byte-faithful to its labels (the genre that produced F4-3 and F5-4 twice
suggests future provenance care). (ii) "exactly five one-line fixes" counts
findings, not edit sites — F5-3 is two one-line edits at two sites, both
disclosed in the block. (iii) S5's delivery sentence still lists "PROP's
rung propagation at [ILN]'s own conditionality" among deliverables; the tag
omits the owed clause-(ii) census, which is priced two paragraphs later and
in the CONDITIONALITY bullet — PE5 read and accepted this paragraph
(§3(d)), so it is recorded here, not numbered.

## 5. Bottom line

**Not a clean pass: 0 CRITICAL, 3 gaps. The acceptance counter stays 0/2; no
slot opens; PE7 would be the next acceptance attempt after an r6.**

The r5 experiment half-succeeded, and the half that succeeded is the
important half: for the first time in the arc, a repair round's own NEW
PROSE contains no defect this pass could find — all 32 insertions are true,
verbatim-quoted, and correctly placed, and the mathematics beneath them has
now survived six hostile readings with every load-bearing step re-derived at
least once. What the minimal round could not do is keep the note's RECORD
SURFACES mutually consistent while touching only seven lines: the status of
record now points two ways at once (F6-1), the collision census it executed
was one row short at inheritance (F6-2), and the closing date record lost a
round (F6-3). All three are one-line cures in the bookkeeping layer; none
has any bearing on TAIL-STAB, READ-EQ, the THEOREM, the corollaries, or the
25,409/0 measurement.

— passPE6, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-06).
Machine legs: **(a)** sealed runner exit 0, `VERDICT: ALL GREEN`,
`TOTAL checks 25409`, 0 violations in every counted family, 1,576 WRONGLET
fires, coverage/teeth minima 6/6, md5 `ccb4351c92573f5f962cae4ae952d8dd` =
the seal-commit md5, `git diff dafc0b5 HEAD` = **0 bytes**; output differs
from the committed artifact at 7 wall-clock lines only, empty under timing
normalisation. **(b)** children generator exit 0, regenerated table
**byte-identical** (`diff` empty, 0 bytes), A1–A6 PASS, A7 all four legs
PASS (752 nodes / 5,336 children; 0/0/0/0; observed max branching = 2e₀+3 at
every e₀ ∈ {2,…,6}). Nothing in the repo was edited by this pass except this
report.
