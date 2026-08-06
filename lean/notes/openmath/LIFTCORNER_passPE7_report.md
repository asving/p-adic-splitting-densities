# LIFTCORNER passPE7 — hostile verification report (fresh context, post-r6; FIFTH ACCEPTANCE ATTEMPT)

**Target:** `lean/notes/openmath/LIFTCORNER_2026-08-08.md` **at HEAD** (post-r6,
commit 91f0cde — the second MINIMAL round: three record-surface fixes
F6-1…F6-3 + the r6 round block + the ARC-line update; 61 insertions / 11
deletions), i.e. after repair rounds **r1** (b2dc120), **r2** (a3112dc +
e5b3faf), **r3** (feedaab), **r4** (6170b09 + 56997be), **r5** (46e6e88),
**r6** (91f0cde).
**Arc read in full before the note:** all six prior reports
(`LIFTCORNER_passPE1..PE6_report.md` at 30e570c / 3367f3c / 39ea0db / 8b53efa /
a5212e8 / f2b48e7) and the r6 diff (`git show 91f0cde`).
**Cross-checks at source this pass:** the sealed runner's Q7/Q9 pair-loop
(`liftcorner_checks.py:78–120`), ITERLAWLIFT_CORNER_2026-08-08.md (the D₁
display, the S7/Case-II claim), ITERLAWN_PROOF S0.2 (base facts),
GRTW2_PROOF (§3.4 remarks, §5.3 W2-OPEN-1, its own 0/2 counter), the
BRIDGE_ADJUDICATIONS wave-fold entry ("one disclosed correct deviation").
**Machine legs (both mandatory):** (a) sealed runner; (b) children generator +
A7 regenerate + compare. **Charge:** (1) the r6 diff line by line; (2) the
STATUS BLOCK + grade box + dating record as a SYSTEM at HEAD (the F6-1 genre —
every arc-accounting sentence true NOW), including the disclosed
unaudited-going-in deviation and whether the r6 unit judged it correctly;
(3) the correction-of-record clause vs the 42-occurrence census, re-executed
independently; (4) fresh eyes on what the six re-derivation lists do not
cover. Quote-and-classify, fix nothing; honesty defects graded; fences and
boxes read as part of the statement.

**VERDICT: 0 CRITICAL ERRORS / 1 JUSTIFICATION GAP (minor). NOT A CLEAN
PASS — the acceptance counter stays 0/2 and no acceptance slot opens.**

The r6 diff is true and correctly placed at every hunk except one clause: all
three fixes land exactly where PE6 pointed, every superseded wording is quoted
verbatim against the actual deletion lines, the brought-forward STATUS BLOCK /
grade box / dating record are mutually consistent and TRUE AT HEAD as a
system (the F6-1 disease is cured, §3), and the disclosed deviation on the
unaudited-going-in accounting was judged CORRECTLY by the r6 unit (§3b). The
mathematics is untouched for the seventh consecutive reading. Both machine
legs reproduce (§1). The one gap: the census-completeness warrant's figure —
PE6's "all 42 `c′` occurrences", transcribed twice at r6 — is a hit-LINE
count, not an occurrence count (raw occurrences at PE6's HEAD 46e6e88: **46**,
on 42 lines; four lines carry two each), so the note's stated sweep universe
does not reproduce under its own unit. The material claim survives my
independent re-execution: at HEAD the census is COMPLETE — 51 occurrences /
47 lines, every one a residue scalar, a covered site, or a mention/quotation;
NO fourth bare-`c′`-as-cocycle site (§4). So r6's new prose carries exactly
one inherited-unit defect: the zero-new-defect streak PE6 started does not
extend to r6, by one clause.

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
... TOTAL checks 25409  elapsed 4.4s ... VERDICT: ALL GREEN ... EXIT=0
```

My family table: GATE 0/56 · AV 0/656 · TLAW 0/4176 · PV 0/4176 · INT 0/4176 ·
LOC 0/0 · CHI 0/4176 · COV 0/0 · WRONGLET 0/3816 · TRS 0/4176 · ENGGATE 0/1 ·
CERT 0 (internal T1/T2(nf=4)+T5) · WRONGLET total fires **1,576** ·
gate-passed **56** · coverage min d1-pairs **6** · teeth min **6**. Sum
56+656+4176+4176+4176+0+4176+0+3816+4176+1 = **25,409** ✓ — every S3 figure
matches. My run's diff against the committed `liftcorner_checks_output.txt` is
**2 lines, both per-block wall-clock stamps** (my `elapsed 4.4s` matched the
artifact this time); the diff is EMPTY under timing normalisation. (Jitter
history: PE4 4 lines, PE5 6, PE6 7, this pass 2 — counted quantities identical
in every recorded run.)

### (b) The children generator — regenerates BYTE-IDENTICALLY; A7 all four legs PASS

```
$ python3 liftcorner_tailstab_children.py --table /tmp/pe7_children_regen.txt ; echo EXIT=$?
EXIT=0
$ diff /tmp/pe7_children_regen.txt liftcorner_tailstab_children_table.txt | wc -c
0        -> BYTE-IDENTICAL TO COMMITTED
```

§7 of my regeneration: assertion failures 0; A1–A6 PASS; A7 PASS — 752 nodes
reconciled / 5,336 children enumerated; (i) sum-identity 0; (ii) shape 0;
(iii) digit-wise dev-linearity 0; (iv) branching ≤ 2e₀+3 violations 0, observed
max {2:7, 3:9, 4:11, 5:13, 6:15} = 2e₀+3 at every e₀; "ANY CHILD DROPPING
NEITHER COORDINATE: NO"; "OVERALL: ALL GREEN". Matches the note's [r2, G3]
block and the [r4] machine-leg bracket exactly. Nothing in the repo was edited
by this pass except this report.

---

## 2. Charge (1): the r6 diff line by line — ALL HUNKS TRUE EXCEPT THE CENSUS-FIGURE CLAUSE (finding F7-1)

Diff structure verified: 4 hunks, 61 insertions / 11 deletions, matching the
commit stat — the r6 round block (27 lines); the F6-2 extension in [r4, F4-5];
the grade-box [r6] bracket (17 new lines) with the [r4]-close left as dated
text; the STATUS BLOCK label + ARC + NEXT/AUDIT edits; the footer r5/r6 lines.

* **The r6 round block:** PE6 = f2b48e7 with 0C + 3G ✓; "all 32 r5 insertions
  verified true, all five fixes correctly placed, the mathematics clean on its
  sixth hostile reading" ✓ (PE6 §2 + verdict); the three superseded wordings
  quoted VERBATIM against the actual deletion lines of the diff (the
  NEXT/AUDIT opening incl. both "Read once/Read twice" sentences ✓; the
  machine-leg clause "re-run clean at PE4" ✓; the label "STATUS BLOCK [r4]" ✓;
  the Q7-only clause "for S2's sealed Q7 sheet row, whose `c′` is likewise
  this cocycle" ✓; the footer terminator with its period ✓); the grade-box
  [r4]-close ellipsized quote faithful ✓; "the first bring-forward since r4" ✓
  (box updated r2, r3, r4, skipped at r5); "the sealed sheet text itself is
  NOT edited" ✓ (no r6 hunk touches S2; the sheet is byte-unchanged since
  dafc0b5, re-confirmed); "plus the STATUS BLOCK ARC-line update, NOTHING
  else" ✓ accurate against the diff; counter 0/2 ✓; PE7 next ✓. The census
  figure "all 42 `c′` occurrences" — finding **F7-1**.
* **F6-2 (the [r4, F4-5] extension):** "S2's sealed Q7 **and Q9** sheet rows,
  whose `c′` is likewise this cocycle **in each**" — TRUE, re-verified at
  source independently of PE5/PE6: the runner computes
  `c, d2, shape_bad, v = measured_cocycle(T, C, ga, gb)` and then Q7 CHI tests
  `base_cc[(ga,gb)] != K2["mul"](c, K2["pow"](xi2, D1))` and Q9 WRONGLET sets
  `wrong = z̄^{d2}·z1old^{D1}`, `mism = (c != wrong)`,
  `pred = (ξ^{D1} != K2["one"])`, violating iff `mism != pred`
  (`liftcorner_checks.py:81, 104–118`) — in both rows the sheet's `c′` is the
  per-pair MEASURED cocycle, the function [r4, F4-5] renames `c^{Φ′}`.
  Correctly placed at the exact clause PE6 named. The precedent cite
  ([r3/r4, F4-1] docstring) accurate ✓.
* **F6-1 (STATUS BLOCK + grade box):** every clause of the new NEXT/AUDIT
  bullet true at HEAD (§3); the [r6] grade-box bracket's arc facts all verify
  (SIX passes = PE1–PE6 ✓; PE5 = a5212e8, 0C+5G, THIRD attempt ✓; PE6 =
  f2b48e7, 0C+3G, FOURTH ✓; the F6-1/2/3 one-line summaries match PE6's
  findings, with the label+box folded into F6-1 exactly as PE6 recorded them —
  "adjacent sites, not numbered separately" ✓); "Audit state after r6: the r6
  edits are UNAUDITED; the r5 edits were read once (PE6)" ✓; label
  "[r4; edited r5, r6]" accurate (r5 edited ARC+PROVED; r6 edited
  label+ARC+NEXT/AUDIT) ✓.
* **F6-3 (footer):** r5 line + r6 line appended, terminator punctuation
  correct; both wallclocks 2026-08-06 match the commit dates (46e6e88 Aug 6
  08:23, 91f0cde Aug 6 09:21) ✓.
* **ARC line:** every hop re-verified against the six reports and git (1C+3G /
  0C+5G / 0C+5G FIRST / 0C+6G SECOND / 0C+5G THIRD / 0C+3G FOURTH; report
  commits 30e570c / 3367f3c / 39ea0db / 8b53efa / a5212e8 / f2b48e7) ✓.

---

## 3. Charge (2): the record system at HEAD — CONSISTENT AND TRUE NOW; the disclosed deviation JUDGED CORRECTLY

### (a) The system

For the first time since r4, the note's three status-of-record surfaces agree
with each other and with the world at HEAD: the STATUS BLOCK's ARC line, its
NEXT/AUDIT bullet, the S4.3 grade box's last entry ([r6]) and the footer
dating record all say the same thing — six passes run, r6 applied, r6 edits
unaudited, PE7 next, counter 0/2. Sentence-level checks: "SIX hostile passes
have now run" ✓; "no pass has been clean" ✓ (verified against all six
verdict lines); "GRTW2 itself 0/2" ✓ CURRENT (GRTW2_PROOF's own header still
carries acceptance counter 0/2 at this HEAD); "Items (1), (2), (7): re-derived
by three hostile passes, NO acceptance credit" ✓ still accurate (PE5/PE6 added
no full re-derivations of those items); the machine-leg clause ("re-run clean
at PE6 …") ✓ and independently re-confirmed by my own runs; the dated [r4]
grade-box close is now explicitly bracketed as dated text by the [r6] entry ✓.
Stale-but-dated round-block closes (r1's "round r2", r2's "PE3 next", …)
carry their dates; the archive is untouched by r6 (the diff's hunks all sit
outside ARCHIVE-BEGIN/END) ✓. FENCES: `git log 46e6e88..HEAD --name-only`
shows the LIFT arc touched only the note + the PE6 report; ILNRES / ITERLAWN /
wave-18 artifacts / both machine legs untouched ✓.

### (b) The disclosed deviation — VERIFIED CORRECT

The deviation (ledgered in the 2026-08-06 wave fold as "one disclosed correct
deviation"): PE6's F6-1 described the true state AS OF PE6 ("the next pass is
PE6, and the unaudited surface going in is **the r5 edits**"); r6 did NOT
transcribe that cure-state but brought the bullet forward to post-r6 truth
("PE7 … Unaudited going in: **the r6 edits** (the r5 edits were line-audited
by PE6 — all 32 insertions verified true — and the r4 edits by PE5; earlier
edit sets read twice or more)"). The judgment is CORRECT: transcribing PE6's
literal wording would have recreated the F6-1 defect one round later (false
"next" pointer, false unaudited surface — exactly the failure scenario PE6
displayed), while every clause of the deviated wording is true at HEAD:
PE7 next ✓; r6 edits unaudited going in ✓; r5 line-audited by PE6 (§2 of its
report, all 32 insertions) ✓; r4 line-audited by PE5 (its designated charge,
§3(a) "line by line") ✓; and "earlier edit sets read twice or more" ✓ under
the bullet's own established counting convention — the superseded bullet's
"Read once: the r3 edits (PE4). Read twice: the r2 edits (PE3, PE4)" counted
full hostile passes over text containing the edit set, and under that same
convention the r3 edits now stand at three (PE4, PE5, PE6), the r2 at four,
the r1 at five, while the stronger "line-audited" credit is correctly reserved
for the named single passes. No finding.

---

## 4. Charge (3): the correction-of-record clause vs the census — RE-EXECUTED INDEPENDENTLY; COMPLETE, but the cited figure's UNIT is wrong (F7-1)

My own census at HEAD (91f0cde): `grep -c` = **47 hit-lines**, raw occurrences
of the two-character string `c′` = **51** (four lines carry two: S1's
ξ-conjugate line, S4's setting line, READ-EQ's b₀-main difference line, COR 2's
preamble — all scalar pairs). Classification of all 51, one by one:

* **34 = the residue scalar** (S1 definition/stratification, S2 roster/rows
  Q1 and disclosure (c), the F4-1 bracket's draw mention, the r3 walk's ψ₁
  sentences, S3's TLAW letter, the S4 setting + b₀-split + counter-instance +
  READ-EQ + THEOREM/COR displays' scalar uses, the F3 box, COR 1's ξ = 1
  parenthesis);
* **4 = the measured cocycle, ALL inside the correction of record** (S1
  CANDIDATE display, both lines — `c′(γ,γ′)` and `c_base = c′(γ,γ′)·ξ^{D₁}`;
  S2's Q7 row; S2's Q9 row — the three sites the [r4, F4-5] bracket now
  names, the CANDIDATE covered as "it");
* **13 = mentions of the symbol or quotations of superseded/source wording**
  (the r4 header's and grade box's "the `c′` collision", the r5 block's
  quotation, the r6 block's three, the F4-5 bracket's convention/mention/
  quotation lines, the [r6] grade-box mention).

**NO fourth bare-`c′`-as-cocycle site exists at HEAD.** The census is
COMPLETE as the note claims, and the Q9 extension was exactly the missing
row. Same sweep re-run at 46e6e88 (PE6's HEAD): 42 hit-lines, **46**
occurrences (doubles at its lines 301/527/892/930) — which is the finding:

### F7-1 — JUSTIFICATION GAP (minor): the census-completeness warrant cites "all 42 `c′` occurrences"; 42 is a hit-LINE count — the occurrence count at 46e6e88 is 46 — so the note's stated sweep universe does not reproduce under its own unit

Offending passages (both r6-new; the same figure twice):

> ([r4, F4-5], r6 extension) "with Q9 the census is COMPLETE — PE6's sweep of
> "all 42 `c′` occurrences" at its HEAD (46e6e88) found NO fourth site."

> (r6 round block, F6-2 clause) "with Q9 the census is COMPLETE — PE6's sweep
> of "all 42 `c′` occurrences" at its HEAD (46e6e88) found NO fourth site;"

Verified: `grep -c 'c′'` at 46e6e88 = 42 (lines); `grep -o 'c′' | wc -l` = 46
(occurrences); four lines carry the string twice. So "42 occurrences" is true
only if "occurrence" is read as "occurrence-line". A hostile reader who
reproduces the note's own unit gets 46 and must conclude the quoted sweep
missed four — the census-completeness warrant, the exact thing the clause
exists to establish, fails to reproduce as stated. Provenance: the figure and
the word "occurrences" ORIGINATE in PE6's report (its F6-2: "My own sweep of
all 42 `c′` occurrences at HEAD finds NO fourth site"); r6 transcribed the
claim in quotation marks — the arc's documented transcription mechanism
(F-C/F4-3: PE2's "bit-identically"; F5-4: PE4's "S9"), now in its third
recurrence, and the first to be fenced by quotation marks at transcription.
**Mitigation (why minor):** the material claim is TRUE — my independent
occurrence-level census above finds the census COMPLETE at both commits (the
4 uncounted occurrences are scalar second-occurrences on already-classified
lines, so PE6's line-based sweep lost no information); the quotation marks
honestly attribute the figure; and the cure is one clause (either "42
occurrence-lines (46 occurrences, four lines carrying two)" or re-cite this
report's 51/47 HEAD count). **Failure scenario:** a future correction bracket
or census extension inherits "42" as the universe size (the F6-2 disease —
PE5's "two surviving sites" undercount — recurring one level up, at the
meta-census).

---

## 5. Charge (4): the fresh-eyes complement — cites and legs no prior list covers — ALL CLEAN

* **The CANDIDATE display's D₁ transcription** (sealed pre-run text, never
  checked against source by any pass): ITERLAWLIFT_CORNER's display is
  `c(γ,γ′) = z̄^{δ₂}·z₁^{(s₁(γ)+s₁(γ′)−s₁(γ+γ′)+ℓ₀γ₂δ₂)/e₀}` — the note's
  D₁ := (s₁+s₁′−s₁″+ℓ₀γ₂δ₂)/e₀ matches exactly (s₁″ = s₁(γ+γ′)), with the
  letter z₁ ↦ z₁′ being precisely the candidate's content ✓.
* **COR 1's parenthetical** "(ITERLAW S7: only PAIR-VAL Case II consumes Φ₁'s
  form; all other strata lift-form-free)" — matches wave-18 S0's own sourced
  claim ("only PAIR-VAL Case II consumes Φ₁'s explicit form", citing
  ITERLAW_2026-08-08.md S7 first bullet; "ITERLAW S7: L1–L6, EXP, Case I, S5,
  S6 are lift-form-free") ✓.
* **Sources-of-record pointers:** GRTW2 §3.4 exists = "THE (ξ, w) CLOSED FORM
  (the display of record)" with "Structural remarks" (the S4.1 bracket's
  "rem. 1" cite resolves) ✓; GRTW2 §5 = "CLAUSE 3 — ψ-transport threaded
  through the tower", and W2-OPEN-1 sits at §5.3 exactly as the [r1, F3] box
  cites, header "displayed open lemma, machine-confirmed" consistent with the
  box's characterization ✓.
* **S4's base-fact cite** "[IL S1]/[ILN] S0.2 (division algorithm by monic
  keys, w₀ a valuation, res additive + kills strict π-excess)" — ITERLAWN
  S0.2 lists verbatim "division algorithm in O[x] (Φ monic ⟹ unique
  developments), w₀ a valuation, res additive and vanishing on strict
  π-excess" ✓.
* **Q7/Q9 runner semantics** re-verified at source independently (§2, F6-2
  bullet) ✓. **W-2 cap currency** (GRTW2 0/2) ✓. **Fences** across
  46e6e88..HEAD ✓ (§3a).

**Unnumbered observations (recorded, not findings):** (i) the r6 round
block's "all three gaps in record surfaces r5 did not touch" drops PE6's own
hedge "(or touched one clause short)" — F6-2's one-row-short census was
executed BY r5 per PE6's bottom line; the sentence stands only under PE6's
offending-passage site assignments (the sealed Q9 row, untouched), which is
how PE6 indexed the finding, so it is defensible as written and not numbered.
(ii) The STATUS BLOCK preamble's "produced findings in three consecutive
passes" is r4-dated rationale; the status surface has now produced findings
in five consecutive passes (PE5's F5-1, PE6's F6-1) — the label's
"[r4; edited r5, r6]" carries the dating, so not numbered. (iii) The ARC
line's "r6 (this round: the three record-surface fixes F6-1…F6-3, nothing
else)" leaves its own update outside the count — same structure PE6 accepted
at r5, and the r6 header discloses "plus the STATUS BLOCK ARC-line update";
not numbered.

## 6. Bottom line

**Not a clean pass: 0 CRITICAL, 1 gap (minor). The acceptance counter stays
0/2; no slot opens; PE8 would be the next acceptance attempt after an r7.**

The record layer finally converged: for the first time in the arc the status
block, grade box and dating record are simultaneously true at HEAD, the
correction-of-record census is materially complete (independently re-executed
at occurrence level, both commits), the disclosed deviation was the right
call, and the mathematics is now seven readings deep with no defect ever
found below the description layer. What broke the zero-new-defect streak is
one transcribed clause: the completeness warrant quotes PE6's "42
occurrences" where the reproducible figure is 42 LINES / 46 occurrences — a
one-clause cure (r7), after which, on this pass's evidence, nothing in the
note is known to be false.

— passPE7, fresh hostile context, campaign 2026-08-08 (wallclock 2026-08-06).
Machine legs: **(a)** sealed runner exit 0, `VERDICT: ALL GREEN`,
`TOTAL checks 25409`, 0 violations in every counted family, 1,576 WRONGLET
fires, coverage/teeth minima 6/6, md5 `ccb4351c92573f5f962cae4ae952d8dd` =
the seal-commit md5, `git diff dafc0b5 HEAD` = **0 bytes**; output differs
from the committed artifact at 2 wall-clock lines only, empty under timing
normalisation. **(b)** children generator exit 0, regenerated table
**byte-identical** (`diff` empty, 0 bytes), A1–A6 PASS, A7 all four legs PASS
(752 nodes / 5,336 children; 0/0/0/0; observed max branching = 2e₀+3 at every
e₀ ∈ {2,…,6}). Nothing in the repo was edited by this pass except this
report.
