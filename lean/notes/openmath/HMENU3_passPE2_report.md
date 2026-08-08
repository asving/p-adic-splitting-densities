# HMENU3 passPE2 report — hostile verification of HMENU3_PROOF_2026-08-08.md (post-r1)

**Pass:** PE2 (second hostile pass on the (hMenu-3) discharge note; fresh
context; verifier fixes nothing, quotes and classifies; fences/boxes/annex
drafts are part of the statement). **Target:**
`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md` at HEAD after r1 (3235e1b;
seal 64d3ff9, verdict 625fa49, PE1 f4f7b03). **Date:** 2026-08-08.

## VERDICT LINE

**NOT CLEAN — 0 CRITICAL + 0 GAPS + 2 MINOR.** Both minors are
display-precision defects in [r1] repair brackets — no theorem, count, series,
or grade is touched; every substantive charge on this pass CONFIRMS the note.
The r1 G1 repair is verified against git at all four sites and W-12's arc has
NOT moved again since r1 (r2 @ 99f1813 is still the supplier HEAD state; no
W12 PE3 in the log at read time), so the corollary's W-12 conditionality
display is CURRENT. The machine leg is bit-clean (runner md5 = seal, fresh
full run GREEN 183,387/0, teeth 21/15/10/4, artifacts content-identical
ex-timing). The fresh route (DIFFERENT from PE1's independent reader — direct
block convolution + generating functions, no state enumeration, own
arithmetic) reproduces every aggregate family count including all 58
B-composite families at (2,9) on 6 rows in both characteristics, and
re-proves LEMMA HM3-4 by explicit composition enumeration. The 2-clean
acceptance counter for this note stays **0/2**.

---

## FINDINGS

### FINDING 1 — MINOR (the r1-m1 carry clause misassigns the 3/2 carry to the B-composite RAM families)

**Quote (THEOREM HM3.B, [r1] bracket).** "the odd RAM-type parameters u/u₁
carry 3/2 in RAW coordinates — the two consulted windows contribute
u + (u+1)/2, e.g. LINRAM2's ℓ term u₁ + (u₁+1)/2 = (3u₁+1)/2 — which becomes
integer carry 3 at the AP index u = 2i−1".

**Defect.** For the B1/B2/B3-RAM **aggregate** families — which are families
of THEOREM HM3.B, the theorem this clause lives in — the u carry is exactly
**1**, not 3/2: the interior W-11 bracket q^{(u−1)/2} cancels the half, giving
A_RAM(u) = (q−1)q^{2M−u−2} and e.g. ℓ(B2-RAM(m,k,w;u)) = 5m+6k+w+u+4 (m ≥ 1;
6k+w+u+3 at m = 0). Committed data pins it: B2-RAM(0,1,1;u=3) at (Zp,2,9) =
8,192+8,192 = 16,384 = 2^{27−13} (ℓ = 13 = 6+3+1+3, u-carry 1), while a
(3u+1)/2 reading gives 2,048. My finite-difference carry sweep over my own
closed forms (below): B1/B2/B3-RAM u → 1.0 per raw unit. The 3/2 raw carry is
real ONLY for the tier-I/II families RAM2LIN (ℓ = 2+6t+(3u+1)/2 in dictionary
coordinates, u = u₀−3t) and LINRAM2 (u₁ partial carry 3/2), and for THEOREM
HM3.A's history-resolved *instance* laws (where "the two consulted windows
contribute u+(u+1)/2" is true — e.g. the empty-history B2-RAM key alone is
2^{27−14} = 8,192, instance ℓ = 6k+w+(3u+1)/2+2). Note the pre-r1 sealed text
("w/j/u/k′ carry ≥ 1") was actually TRUE for the B-RAM u; the r1 bracket
inherited PE1 FINDING 2's own wrong example (PE1 displayed
"B2-RAM(m,k,w;u) has ℓ = 5m+6k+w+(3u+1)/2+4", refuted by the committed
16,384 above — PE1's conclusion stood via LINRAM2/RAM2LIN, its example did
not).

**Why minor.** The clause's load-bearing content survives on every reading:
strict positivity holds everywhere, and W-12.D Step 1's guard m_i·b_i ∈ ℤ_{>0}
holds a fortiori for B-RAM (2·1 = 2 vs 2·(3/2) = 3); ℓ(base) ∈ ℤ everywhere.
Admissibility and every geometric series are unaffected (my own convolution
and partial-sum legs below confirm the counts and densities). Repair shape:
scope the 3/2 sentence to "the tier-I/II RAM2LIN/LINRAM2 families and the
HM3.A instance laws; the B-composite A_RAM aggregates carry u with integer
coefficient 1".

### FINDING 2 — MINOR (no fired-clause check recorded for the HEX3 supplier findings)

**Quote (HM3-BOX-2, [r1]).** "…and HEX3's arc (PE1 NOT CLEAN 0C+2G+2m @
d177fd8, counter 0/2, r1 owed [r1])."

**Defect.** The r1 updated the HEX3 arc grade at BOX-2 and the S10 tail but —
unlike its own W-12 treatment, which records a gap-by-gap fired-clause check
at S9 bullet 1 — records no check of whether HEX3's PE1 findings touch clauses
this note fires. They graze one: HEX3 PE1's gap 1 is H-2(i)'s displayed
ghost-zone inequality (pairing backwards, false at j = 1), and §S3.1's proof
of LEMMA HM3-2 fires H-2(i) BY NAME ("HEX3 H-2(i) (window coherence) shows
every digit consulted by the chain of X lies strictly below the ghost
zones"). At the r1 timestamp the supplier's fix had not yet landed (HEX3 r1 =
2580f12, 09:36:32Z, six minutes after this r1). The conclusion consumed
(window coherence) survives — HEX3's PE1 re-derived the corrected pairing
(N−jk) on the whole range and the α-term is machine-tied — and HEX3's gap 2 /
minors touch nothing consumed here (u(2,7) value re-verified to 5,664 both
forms), so nothing propagates. But the note's conditionality record, the
exact thing HM3.D points at, leaves the reader unable to see this without
leaving the note. Repair shape: one sentence at BOX-2 ("HEX3 gap 1 hits
H-2(i), whose conclusion S3.1 consumes; conclusion re-derived intact by HEX3
PE1, display corrected at HEX3 r1; gaps/minors otherwise outside the fired
clauses").

**No further findings.** Everything else checked out; the records follow.

---

## CHARGE 1 — the r1 edits verified against git (the PE1-unmined vein)

* **G1's four sites** (S9 bullet 1 / HM3-BOX-2 / S10 tail / HM3.D header) all
  present in the r1 diff (f4f7b03→3235e1b), all [r1]-tagged with strikethrough
  of the sealed text; the diff touches ONLY the note (71+/15−), runner +
  artifacts byte-frozen (runner md5 65326f85c218087261f434f8b8cc8dda at HEAD =
  the r1-recorded value; `git diff 64d3ff9 HEAD -- …/hmenu3_checks.py` empty).
* **Arc facts re-verified from git:** W12 passPE2 @ 1be15d2 = 2026-08-08
  08:14:16Z, verdict "NOT CLEAN — 0 CRITICAL + 3 GAPS + 2 minor" ✓; HMENU3
  seal 64d3ff9 = 08:40:17Z (26m01s later — "26 minutes" ✓); W12 r2 @ 99f1813
  (09:02:59Z, "all five PE2 findings, note-only, [r2] tags" + "ANNEX 2
  (HMENU3 BOX-2, verbatim)") ✓; HEX3 PE1 @ d177fd8 0C+2G+2m ✓.
* **W-12's arc has NOT moved again since r1:** no W12 PE3 commit exists at my
  read time (log swept through HEAD a00cf97). The HM3.D header's "post-r2
  99f1813 as of this repair, PE3 next" is CURRENT. Suppliers that DID move
  after r1 (both favorably/neutrally, hence remarks not findings): HEX3 r1
  landed @ 2580f12 (09:36:32Z; all four PE1 findings repaired; so BOX-2's
  "r1 owed" was true when written and has aged); W-11 PE3 ran CLEAN @ 839b735
  (counter 1/2) — strengthens the "accepted pins" bullet.
* **Annex-verbatim check:** the S8.1 BOX-2 annex text and the copy applied in
  W12_PROOF Annex 2 are equal after normalizing block-quote markers (804
  chars, md5 22b5fa99… both sides) ✓.
* **Fired-clause arithmetic re-done:** W12-PE2 gap 2's DBL SPLIT-TAIL mass
  ⌊(N−1)/2⌋(q−1)²q^{2N−2} == S5.3's displayed q(q−1)q^{N−1}·⌊(N−1)/2⌋(q−1)q^{N−2}
  EXACTLY ✓; gap 3's guard (m_i·b_i ∈ ℤ_{>0}) holds at every family (carry
  sweep: increments 1, 2, 3, 5, 6 only) ✓; gap 1 (disc-0 a ≡ b oracle-warrant
  genre) is outside Steps 1–4 as consumed ✓.
* **The S0 de-misquote:** W12_PROOF §S1(iii) reads "ℓ_F affine with strictly
  positive parameter coefficients" (no "integer") — S0's restatement now
  matches ✓; and W-12.D Step 1's [r1 m1]/[r2 G3] guard text (quoted at W12
  lines 735–755) is exactly "m_ib_i ∈ ℤ_{>0} … and m₀+Σm_ia_i = ℓ_F(base
  point) ∈ ℤ", as the r1 brackets cite ✓.
* **AP-index carry arithmetic re-derived** (finite differences on my own
  closed forms at q = 5, N = 18, cross-checked by hand): m → 5 ✓; k/t → 6
  (claim "≥ 3" ✓); w → 1, j → 1, B-block k′ → 2, VERT2-leaf k′ → 3 (claim
  "≥ 1" ✓); II-RAM3 h → 2; I-RAM2LIN u → 3/2 ✓ (AP-index 3 ✓); I-LINRAM2
  u₁ → 3/2 partial ✓; B1/B2/B3-RAM u → **1** (FINDING 1). LINRAM2 in genuine
  product coordinates (i, v = u₀−(3u₁+1)/2): ℓ = 6i+v — all integer, all
  positive; every family passes the Step-1 guard.

## CHARGE 2 — B1-L/B2-L (and B3) transport laws re-derived from the W-11/W12-L0 block dictionary

**Own fiber derivation (raw digit counting, no supplier fiber cited).** At a
depth-0 TRP frame, window W, per center, my own count of each β-event locus:

* β1 (FULL side slope k, residual (y−z)²(y−z′)): ordered pairs (z, z′),
  z ≠ z′ ∈ F_q^× = (q−1)(q−2); three residual digits fixed; free digits
  q^{(W−1−k)+(W−1−2k)+(W−1−3k)} ⟹ total (q−1)(q−2)·q^{3W−3−6k}.
* β2 (vertex at 1, height 2k, right residual (y−z)², v(B₀) = 3k+w exact):
  (q−1)_z ×(q−1)_{B₀ digit} × q^{(W−1−k)+(W−1−2k)+(W−1−u₀)} ⟹
  (q−1)²q^{3W−3−6k−w}.
* β3 (vertex at 2 height t, left residual (y−z)², u₀ = 3t+2j): (q−1)_z ×
  (q−1)_{c₂} × q^{(W−1−t)+(W−1−2t−j)+(W−1−3t−2j)} ⟹ (q−1)²q^{3W−3−6t−3j}
  (in char 2/3 the forced middle digits are 0 — still forced; counts
  characteristic-free, J-D0).
* α (FULL, (y−z)³): (q−1)q^{3W−3−6k}.

Each equals the note's route prefactor × the target system's total mass:
β1: (q−1)(q−2)q^{3k+M−1}·q^{2(M−1)}; β2: (q−1)²q^{3k+M−1−w}·q^{2(M−1)};
β3: (q−1)q^{3t+M−1}·[(q−1)q^{2M−2−3j} = my own mass of block states entering
first refine at depth j]; α: (q−1)q^{3k}·q^{3(M−1)} — all four EXACT (M =
W−3k resp. W−3t). So the fibration constants are forced by dimension alone;
the per-key correspondence on top of them is HM3-1(iii) + W12-L1(b)
(unit-scaled residuals), which the machine checks per key (MENU/XREAD).
HM3-1(iii)'s vertex persistence re-walked: v(recentering shifts) > m keeps
v(center−r_split) = m; rightmost side length 1 ⟹ g = 1 ⟹ no repeat; the
dictionary's four lines re-derived from root-valuation sums (block refine k′:
u₀ = m+2(m+k′) = 3m+2k′; RAM(u): 3m+u; 2SIDED(w₁,w₂): 3LIN(m+w₂, m+w₁, m);
SPLITEQ/INERTDEEP(k′) ↦ VERT2(3m+2k′, m, λ)).

**Block aggregation re-derived from LEMMA W12-L0 as stated** (W12_PROOF S2.6
quoted directly): fixing each leaf, the admissible interior histories are the
subsets of {1..s_max} (s_max = (u−1)/2, w₁−1, k′−1), the instance laws are
s-independent on their ranges, so Σ(q−1)^{|hist|} = q^{s_max} and the four
A_L displays follow, incl. ranges; forcing hist to start at j gives
(q−1)q^{s_max−j} and the four A^{(j)}_L displays with their shifted ranges
(u ≥ 2j+1, w₁ ≥ j+1, k′ ≥ j+1) ✓ — all EIGHT displayed aggregate laws
re-derived. Composing bracket × prefactor × A_L reproduces the displayed
B1-L/B2-L/B3-L forms ✓.

## CHARGE 3 — the raw-key recursion's completeness (the 187-key question)

**What the note claims (quotes).** S1: "The read is deterministic, so the raw
keys PARTITION the state space (disjointness is structural)." HM3.A: "the
per-center count of every raw key is given exactly by the recursion pred3".
S3.3: "Induction on the window… Every state receives exactly one raw key".
Grade box: "HM3.A/B/C **composed at attempt 0/2**, machine-sealed on 41
rows". S10 P-2: "(Fqt,2,9): 150 decided keys (187 with drain-history keys)".

**Verdict: the claim is honestly graded.** Key-set completeness has two legs
and the note claims each at its true grade: (a) PROVABLE completeness ∀(q,N)
= the S3.3 induction, whose case split is HM3-1(i) ("B₀ = 0, one of the SEVEN
decided shapes, or one of the FOUR refine species — nothing else"), resting
by name on W-12 S2.4 depth-0 completeness + HEX3 H-1 at pins — i.e.
composition grade, exactly what the grade box says; (b)
ENUMERATION-completeness on the 41 rows, machine-checked BOTH directions (I
read the code: `for k in sorted(set(tally) | set(pred))` — a predicted-but-
unmeasured key violates exactly like a measured-but-unpredicted one), 1,031
key-checks 0 violations. The recursion's structure mirrors the induction
case-for-case (depth-0 laws / top DRAIN q^{2(Ne−1)} / α-recursion at Ne−3k /
three β-routes through W12-L0 with the dictionary; key prefixes make the
routes structurally disjoint; termination by window descent). Census
re-verified from the committed artifact: (Fqt,2,9) = 150 decided + 37
drain-history = 187 keys, decided 16,674,048, deep 523,008 — and the 150-key
census was a sealed PRE-RUN prediction on a never-measured row (the strongest
completeness evidence in the file). No overclaim found: nowhere does the note
assert machine-checked completeness beyond the roster or unconditional
provable completeness.

## CHARGE 4 — HM3-RTAU: what the 30 checks verify; conditionality at read time

From the runner's `rtau_leg()` (read line-by-line): 30 = 1 (Σ_τ R_τ = 1,
sympy-symbolic on the DISPLAYED five forms) + 5 (each displayed R_τ == the
monic level-0 assembly of om_density_engine's β(2)/β(3), symbolic; the
engine md5-pinned) + 4 q-values × [1 (per-center identity Σ_τ D_τ(24) ==
q^{69} − u(q,24) EXACT, integers) + 5 (whole-space partial sum SEP + DBL +
q·TRP at N = 24: remainder ∈ (0, q^{−20}), exact Fractions)]. So RTAU verifies
the displayed forms' internal consistency, the independent engine tie, and
that the aggregate menu's partial sums converge to the displayed values with
positive vanishing remainder — it does NOT itself derive R_τ symbolically
from the menu (that derivation is PE1's independent summation, and my own
partial-sum leg below reproduces it numerically-exactly at N = 20). This
matches the note's own description (S5.5 "Executed (machine: HM3-RTAU, exact
symbolic)" + P-8's list). **Conditionality sentence at MY read time:** the
W-12 element is current (no PE3 yet); the HEX3 element has aged (r1 landed
post-repair; PE2 next now); this note's element ("PE2 next") is discharged by
this pass. Accurate when written; see FINDING 2 for the one missing
propagation record.

## CHARGE 5 — the seal actually contains the preregistrations

`git show 64d3ff9` verified: commit 1 contains ONLY the note + runner (no
artifacts, no §S10 — "VERDICT: PENDING" present), and the note's S7 P-2 block
at the seal already carries ALL three never-measured rows' spot predictions —
(Fqt,2,9): 150 decided keys, decided 16,674,048, deep 523,008, 4 key spots
(131,072 / 65,536 / 32,768 / 32,768); (Fqt,3,6): 30 keys, deep 95,580, 4
spots (26,244 / 26,244 / 17,496 / 5,832); (Fqt,27,2): one decided key
('RAM3',1) = 18,954 + drain 729 — plus P-3's (Fqt,2,9) drain 103,168 and
P-9's teeth 21/15/10/4. The runner docstring at the seal carries the same
predictions (byte-identical file at HEAD). Artifacts landed only at 625fa49;
their committed md5s (7f754887…/daf077d0…) match the note's S10 and the files
at HEAD. Disclosure honest: predictions "computed from the sealed predictor
pre-run" = SAME-class, stated. Teeth thresholds re-derived from the roster:
N ≥ 4 rows = 21, N ≥ 5 = 15, N ≥ 6 = 10, oracle rows = 4 ✓; Σ states =
94,824,902 ✓ (18+23 rows ✓); XREAD-eligible rows (≤ 65,536 states) = 22 ✓.

## MACHINE LEG

* **Runner vs seal:** md5 65326f85c218087261f434f8b8cc8dda; `git diff 64d3ff9
  HEAD` on the runner EMPTY; all 7 PIN files intact at HEAD (md5s re-computed
  = the PINS table).
* **Fresh full run** (isolated `git archive` of the SEAL commit into /tmp;
  PYTHONPATH-only environment fix; single run): **GREEN, exit 0, 183,387
  checks / 0 violations, 447.8 s** (committed 443.8 s) — PIN 7, MENU 1,031,
  DRAIN 82, AGG 707, XREAD 171,444, HEX3TIE 38, W12TIE 69, DBLTIE 23,
  ORACLE 9,956 (= 9,952 σ + 4 member-count rows: 48/624/6,688/2,592 ✓),
  RTAU 30; teeth 21/15/10/4 all exactly preregistered; 41/41 rows. Output
  txt: 66 lines, ZERO non-timing diffs vs the committed artifact; results
  JSON identical ex `elapsed_s` (row dicts, tallies, families, teeth all
  equal — python structural compare). Verdict-section arithmetic re-audited:
  family total 183,387 ✓; never-measured rows reproduced (187/39/2 keys;
  deep 523,008 / 95,580 / 0; drain 103,168 / 80,109 / 729).
* **FRESH ROUTE (differs from PE1's independent reader — no state
  enumeration, no runner imports; `/tmp/hmenu3_pe2/fresh_conv.py`):**
  (i) LEMMA HM3-4 re-proved by EXPLICIT enumeration of all compositions of m
  (direct convolution) AND by my own truncated-power-series expansion of
  A₁/(1−A₁), == (q−1)q^{4m−1} at q ∈ {2,3,4,5,9,27}, m ≤ 7 (48 cells).
  (ii) A_L/A^{(j)} re-aggregated by EXPLICIT subset enumeration over interior
  histories from W12-L0-as-stated == my hand-derived closed forms (q ≤ 5,
  M ≤ 11, j ≤ 4). (iii) My own convolution assembly (bracket × my own fiber
  prefactors × A_L; tier I/II with my own shear-unshift classifier written
  from the S1 dictionary) compared FAMILY-BY-FAMILY against the committed
  enumeration tallies at 6 rows — (Zp,2,7), (Zp,2,9), (Fqt,2,9), (Zp,3,5),
  (Fqt,3,6), (Fqt,4,5): 116 aggregate families at (2,9) incl. all 58
  B-composite families, ZERO mismatches, B-composite masses tie exactly
  (270,592 at (2,9) both routes; Zp == Fqt). This is an independent
  derivation of every B-composite family count at those rows, not just ≥ 2.
  (iv) My own exact-Fraction partial-sum leg at N = 20, q ∈ {2,3}: all five
  displayed R_τ exceeded by the menu partial sums by remainders in
  (0, q^{−16}); Σ_τ R_τ = 1 exact.

## REMARKS (verified non-findings, for the record)

1. At read time the S9/BOX-2 HEX3 element reads "r1 owed" while HEX3 r1 has
   since landed (2580f12, six minutes after this note's r1) — accurate when
   written, ordinary aging of a dated [r1] bracket, NOT stale-at-birth like
   PE1's FINDING 1. W-11 has since strengthened to PE3 CLEAN (839b735,
   counter 1/2). Composer should refresh both at the next touch.
2. PE1's FINDING 2 text contains a wrong example formula (B2-RAM ℓ with
   (3u+1)/2 — refuted by committed data; see FINDING 1). The PE1 CONCLUSION
   (raw-coordinate non-integrality exists; the guard rescues it) is correct
   via LINRAM2/RAM2LIN. Recorded here because the r1 bracket inherited the
   framing.
3. The r1 fired-clause bracket for W-12 gap 1 says the disc-0 sub-genre is
   "outside HM3.C's level-0-type partition"; more precisely it is outside the
   clauses HM3.D fires (it concerns W-12's own oracle warrant on disc-0
   members); the level-0 partition itself routes a ≡ b disc-0 members to TRP
   consistently on both sides. No consequence either way.

## SCORE AGAINST P-10

No falsifier fired on any of my legs: no MENU/AGG-equivalent discrepancy in
the convolution route (so HM3-4 and every A_L/A^{(j)} aggregation stand), no
tooth anomaly, engine/series ties hold. Both findings are outside P-10's map
(display precision inside [r1] brackets; conditionality-record completeness).

## COUNTER

PE2: **0 critical / 0 gaps / 2 minor.** 2-clean acceptance counter: **0/2**
(this pass is not clean; word-level repair then PE3).
