# HEX3 passPE5 report — hostile verification of HEX3_PROOF_2026-08-08.md at r3 (b6a1d69)

**VERDICT: NOT CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAPS + 2 MINOR.** Both
findings are one-clause phrasing repairs in non-theorem prose, both surfaced
by W-12's r4/PE6 events that POSTDATE HEX3 r3 (so r3 could not have folded
them); every theorem (HEX3.A/B/C), every transport lemma, the r3 repair
itself, the species table, the machine leg, and the fresh route survived.
Counter stays 0/2 (a finding, however small, is not a clean pass); r4 owed
on m1+m2, then the 2-clean bar applies afresh.

**Pass:** PE5 (fifth hostile pass; arc PE1 0C+2G+2m @ d177fd8 → r1 @ 2580f12
→ PE2 0C+1G+1m @ f60348b → r2 @ a707430 → PE3 CLEAN @ fca1a97 (1/2) → PE4
0C+0G+1m @ 34a946b (counter reset) → r3 @ b6a1d69 = the target audited
here). **Verifier:** fresh-context Fable, 2026-08-09. **Target byte-state:**
HEX3_PROOF at HEAD == b6a1d69 (r3); runner + artifacts byte-frozen at seal
e3f3459 (md5 83faf7ed… re-verified; `git diff e3f3459 -- hex3_checks.py`
empty; committed artifact md5s == §S10's display: 6e4b3207…, ce6f4116…).
All four prior reports and the r3 diff read in full first; their routes not
re-walked. **Charges:** (1) the r3 text attacked clause by clause; (2) the
L438 category slip's blast radius INSIDE HEX3 (W-12 PE6 checked only W-12's
consumption); (3) the U₃^conv law's proof re-derived — telescoping,
renewal-GF, the order-9 recurrence; (4) species table spot-verification
against the classifier definitions (GENIND's consumption surface); (5) free
hunt. **Fresh route (disjoint from PE1 small-row enumerator / PE2
poly-identities + field tables / PE3 renewal-GF inversion + 9 DVR types /
PE4 partial fractions + 6 DVR types):** a DEPTH-N scan beyond the battery's
window — own C enumerator, first-ever N = 10, 11, 12 at q = 2, N = 7 at
q = 3, N = 6 at q = 4, plus first-ever (8,4), (9,4), (16,3), (16,4) — the
first machine instantiation of the k = 3 stratum anywhere, and the first
q = 16 instances anywhere. EXACT legs, all integer.

---

## m1 [MINOR] — S0's certification warrant "Ore applies to every lift — W-12 S2.3" (L80–81) carries the over-claim W-12 r4 STRUCK from S2.3; the correction W-12's sweep says is "owed at HEX3's own arc" comes due at this pass

Quote (S0, the razor-separation paragraph, warranting the load-bearing
inequality):

> Every conservative-DECIDED member is σ-decided (its read terminates with
> all consulted data in-window and separable residuals: Ore applies to
> every lift — W-12 S2.3), so **U₃^σ ≤ U₃^conv always**

W-12 r4 (d2d91b7 + 5728258, landed 2026-08-08 19:28/19:32 — ninety minutes
AFTER HEX3 r3 at 17:53) struck exactly this "every lift" phrasing from its
own S2.3 as MINOR 2, with a concrete counter-instance: in equal
characteristic 3, the in-window member F = y³ + b₀ (a TRP-RAM3(h) state,
3 ∤ h) has lifts with F′ ≡ 0, hence disc = 0 and NO splitting type — Ore
does not apply to those lifts. W-12 r4's m2 blast-radius sweep
(W12_PROOF L1768) explicitly dispositions THIS HEX3 site: "HEX3_PROOF
L80–81 … SAME loose phrasing, conclusion UNAFFECTED … A phrasing correction
owed at HEX3's own arc; no number and no box moves." PE5 is the first
HEX3-arc pass since r4 landed, so the owed correction surfaces here.

Independently re-verified (not just inherited from the sweep): the
conclusion U₃^σ ≤ U₃^conv is intact because U₃^σ's own definition (S0,
the bullet immediately above) quantifies over disc ≠ 0 lifts only —
a conservative-DECIDED member's read terminates with in-window separable
residuals, the post-r4 S2.3 pins one σ on every disc ≠ 0 lift from the
member's own read data, so no two disc ≠ 0 lifts disagree and the member
is outside U₃^σ. The eq-char-3 counter-instance member is
conservative-DECIDED with a disc = 0 lift, and does not disturb the
inequality. Zero theorem blast radius; THEOREM HEX3.B's chain is valid at
the pinned (disc ≠ 0) notion. Repair shape (one clause): "Ore applies to
every disc ≠ 0 lift — W-12 S2.3 [post-r4 form]".

## m2 [MINOR] — the L438 parenthetical "(all lifts genuinely ambiguous)" is a category slip (W-12 PE6's find); verified ZERO blast radius inside HEX3; repair owed at this arc

Quote (S6, HEX3-BOX-1):

> The S3.2-species lower bound (all lifts genuinely ambiguous) shows
> U₃^σ ≥ q^N is attained by fully-hidden states

W-12 PE6 found the slip (members are ambiguous — each admits two disc ≠ 0
lifts of distinct σ per LEMMA W12-S3.2; a single lift has one σ and cannot
be "ambiguous") and verified it harmless for W-12's OWN consumption only.
This pass's charge: the blast radius INSIDE HEX3. Site enumeration — the
lower bound q^N ≤ U₃^σ appears at S0 (sourced from "LEMMA W12-S3.2's
constructed species", the correct form), S1 (THEOREM HEX3.B's display),
S5.3 (the bound chain), S8.1 (the annex bracket) — every site consumes
W12-S3.2's STATEMENT (byte-unchanged through W-12 r4, per W12_PROOF L917),
none consumes the parenthetical's mis-stated form; nothing in HEX3's
mathematics touches per-lift ambiguity at all (lifts enter only through
W12-L1's product bijection, a different surface). Blast radius zero;
the defect is the unrepaired one-line parenthetical itself. Secondary
looseness in the same sentence, same tier: "fully-hidden states" — the
S3.2 species is b₁ = b₀ = 0 with b₂ FREE (b₂ visible in general); what is
hidden is the separation data (B₁, B₀), which is what blocks
certification. Repair shape: one line, e.g. "(each member genuinely
ambiguous: two disc ≠ 0 lifts of distinct σ)" + "states with all
separation data hidden".

---

## Charge-by-charge record

**(1) The r3 text — every changed clause attacked; CORRECT, and its
arithmetic verified exactly.**
* *The conditionalization is faithful to the pinned semantics:* W-12.D's
  (A2) (re-read at W12 HEAD) defines the residue as "the σ-undecided
  residue AND any window-boundary (tail) families"; the repaired clause now
  asserts membership in the second component only under BOX-1's open
  lemma — with the n = 2 side (W-11-proved, W-12 S3.4's r(N) routing
  display re-checked at L379–385) and the n = 3 DBL side (W-12 r2's G2
  leg; W12-L1(c) exists and carries the certificates) correctly kept as
  the PROVED sides. Citation check: all three cites verified byte-faithful
  at W-12 HEAD (r5).
* *The divergence price, re-derived from scratch:* the N-linear part of
  the k-term (q−1)q^{4k−1}(q^M−1)R(M) is (q−1)²·(N−3k)/2·q^{2N−2k−3}
  (averaged over the ⌊(M−1)/2⌋ parity steps), so the all-k slope of
  U₃^conv·q^{−2N} = q·u·q^{−2N} is Σ_{k≥1}(q−1)²/(2q²)·q^{−2k} =
  (q−1)²/(2q²(q²−1)) = **(q−1)/(2q²(q+1))** ✓ — the r3 display. At q = 2:
  1/24 ✓. Numerically from the exact law at N = 200/202 and 201/203
  (both parities, exact rationals): 0.0416666… = 1/24 ✓. S5.3's excess
  bound gives undecided·q^{−2N} slope ≤ 1/(2q(q+1)) ✓, and
  (q−1)/(2q²(q+1)) ≤ 1/(2q(q+1)) ⟺ (q−1)/q ≤ 1 ✓ — domination exact, as
  the r3 record claims.
* *The (2,7) mass:* whole-space k = 1 floor-mass = q·(q−1)q³·(q^M−1)·
  ⌊(M−1)/2⌋(q−1)q^{M−2} = ⌊(N−4)/2⌋(q−1)²q^{2N−4}(1−q^{−(N−3)}) = 960 at
  (2,7) ✓ (exponent check: 1+3+(M−2)+M = 2N−4 with M = N−3 ✓).
* *The pin-robust route:* under BOX-7, conv-UNDECIDED = σ-undecided ⊔
  (conv-undecided ∧ σ-certified), and the second component is exactly the
  certified B₀ = 0-exit (boundary-tail) states — the decomposition is
  definitionally exact given the pin, so HEX3.B's bound on U₃^conv
  dominates both r(3,N) TRP legs however BOX-1 resolves ✓ (PE4's charge-2
  argument re-checked, not just cited).
* *The arc records* (header, BOX-2, S10) all three carry the same
  PE3→PE4→r3 history, consistent with the prior reports and the commit
  log ✓.

**(2) L438 blast radius inside HEX3 — ZERO (finding m2 above records the
unrepaired slip itself).**

**(3) The law's proof re-derived.**
* *Telescoping (S5.2):* coefficient of t(N−3l) after substitution =
  (q−1)q^{3l} + (q−1)²Σ_{k=1}^{l−1}q^{3k+4(l−k)−1} = (q−1)q^{3l} +
  (q−1)(q^{4l−1}−q^{3l}) = (q−1)q^{4l−1} ✓; head terms −q^{2M−2} cancel
  against the substituted u(N−3k) heads ✓. Machine: telescoped ==
  first-step as exact integers, N ≤ 60, twelve q values including
  non-prime 4, 8, 9, 16, 25, 27 — 0 mismatches.
* *Renewal GF:* 1−A = 1−(q−1)q³x³/(1−q³x³) = (1−q⁴x³)/(1−q³x³) ✓;
  A/(1−A) = (q−1)q³x³/(1−q⁴x³) whose expansion (q−1)Σq^{4k−1}x^{3k}
  reproduces the telescoped display ✓.
* *The order-9 recurrence, re-derived (not imported from PE3/PE4):*
  T = Σ(q^M−1)R(M)x^M = [qx/(1−q²x) − x/(1−qx)] +
  (q−1)q^{−2}[G(q²x)−G(qx)], G(y) = Σ⌊(M−1)/2⌋y^M = y³/((1−y)²(1+y))
  (coefficient check c_n = ⌊n/2⌋+1 ✓); with S = x/(1−q²x) and the α
  kernel, den(U) | D = (1−q²x)²(1+q²x)(1−qx)²(1+qx)(1−q⁴x³), degree 9.
  Machine: Σᵢ Dᵢ u(N−i) = 0 verified exactly for N = 10..60 at
  q = 2, 3, 5, 16 ✓.
* *S5.3 bound:* R(M) ≤ q^{M−1}(M+1)/2 re-proved (the note's
  "⟺ M ≥ 1" display checks: qM+q−2q−(M−1)(q−1) = M−1 ≥ 0) ✓; k-term
  bound, geometric sum 1/(q+1), N−3k+1 ≤ N−2 at k ≥ 1, and the final
  (1+N)q^{−N} chain all re-derived ✓.
* *R(M) from W12-L0 (S4):* the bracket sum q^{M−1} +
  Σ_{w=1}^{⌊(M−1)/2⌋}(q−1)q^{M−2} ✓, and the R-recursion R(M) = q^{M−1} +
  (q−1)Σq^jR(M−2j) checked at M = 4, 5 by hand and machine-wide via the
  β3 keys ✓.
* *β-assembly (S5.1):* the u₀-sums re-derived — β2: Σ_w q^{M−1−w} =
  (q^{M−1}−1)/(q−1) giving (q−1)q^{3k}R(q^{M−1}−1) ✓; β3: the R-recursion
  gives (q−1)q^{3k}q^{M−1}(R−q^{M−1}) ✓; the k-bracket collapses to
  u(M) + (q^M−1)R(M) − q^{2M−2} ✓ (the (q−2)+1+1 → q coefficient check).
* *H-2(i) at the corner (the r1-repaired pairing):* j = 1:
  (2/3)(N−1) < N−k ⟸ k < (N+2)/3, true STRICTLY at k = ⌊(N−1)/3⌋ ✓;
  j = 2: k < (2N+1)/6 vs k ≤ (2N−2)/6 ✓.

**(4) Species table — 11 entries hand-verified against the S2 classifier
definitions + closed forms, and the full per-key surface tied three
independent ways.** Hand: (Zp,2,7) ALPHA(1) = (4096,576), ALPHA(2) =
(64,64), VERT1(4,1) = (2048,384), VERT1(6,1) = (512,96), VERT2(5,1) =
(512,256); (Zp,3,6) FULL11SQ(1) = (39366,7290), VERT2(5,1) = (2916,2916);
(Fqt,4,4) ALPHA(1) = (192,192), FULL11SQ(1) = (384,384); (Zp,2,9)
VERT1(8,2) = (1024,384), VERT2(8,2) = (512,512) — each locus re-counted
from the S2 digit-slot definitions (letters × free digits; the VERT2
exponent 3N−3−u₀−t−(u₀+t)/2 re-derived from the three-coordinate window
census), each drained value from the S3 transports. Machine: (i) my own
C enumerator's per-key tallies == the committed JSON on 7 rows
key-by-key ((Fqt,2,6/7/8),(3,4),(3,5),(4,4),(4,5)); (ii) == my own
closed-form transcription BOTH directions on all 15 rows run (8
validation + 7 never-measured); (iii) the isolated battery re-run's
SPECIES family 172/0. GENIND's consumption tie (md5-frozen
hex3_checks_results.json ce6f4116) re-hashed == the committed artifact ✓.

**(5) Free hunt.**
* *XREAD count reconciled from first principles:* rows with
  q^{3(N−1)} ≤ 65,536: Zp sum 77,500 + Fqt sum 80,704 = **158,204** ✓ ==
  the preregistered/observed count. Family total 4+92+172+158,204+23+17 =
  158,512 ✓.
* *Roster mass:* Σ q^{3(N−1)} over the 46 rows = 67,410,225 ✓ exact.
* *Census sanity (not a fifth recount):* 21 + 25 rows, 17 shared, 29
  distinct pairs re-counted from the frozen roster lists ✓.
* *S8.1 annex currency at W-12 HEAD (r5):* the applied BOX-3 annex block
  in W12_PROOF (L1672–1683) == HEX3 §S8.1 verbatim; W-12's r4/r5 changes
  (S3.2 proof repair with statement byte-unchanged per its own record,
  σ-labeling clause, S2.3 strike, S10 P-6 order sentence, HMENU3 annex)
  touch NOTHING HEX3's theorems consume (W12-L0, W12-L1(a)(b), S2.4,
  W-12.C, BOX-3/7 all textually intact; S2.3 consumed only through the
  m1 site above).
* *W-11 anchor (S9 stack):* pins verified at md5 level by the battery's
  PIN family in the isolated run.

## Machine leg (all runs fresh this session)

* PINS: all four md5s (w12_checks.py 7dc0…, w11_checks.py 500a…,
  w10_checks.py a9c3…, w12 JSON 0577…) verified == the runner's pin block
  at copy time; runner md5 83faf7ed… == seal e3f3459; both r3-era diffs
  note-only (`--stat` verified).
* **ISOLATED full re-run** (novel this pass: the entire import closure —
  21 files — copied to /tmp/hex3_pe5_run and run OUTSIDE the repo, so the
  committed artifacts were never touched): exit 0, **GREEN, 158,512
  checks / 0 violations** — PIN 4, LAW 92, SPECIES 172, XREAD 158,204,
  W12TIE 23, CHAR 17; teeth 10/20/13 == preregistered; 46/46 rows,
  326.0 s. Recursive JSON diff vs the committed artifact: 21 leaves, ALL
  elapsed_s, ZERO non-timing.
* Committed artifacts intact: md5 6e4b3207… / ce6f4116… == §S10's display.
* TAUTOLOGY AUDIT: read the runner end to end — u_measured comes only
  from read_fresh enumeration; u_law/species_pred are separate closed-form
  evaluators; W12TIE compares measured (not law) to the committed JSON;
  CHAR compares raw tallies; the teeth compare corrupted predictions to
  MEASUREMENT (and RED if a corruption matches measurement). No family
  compares the law to itself. XREAD ties the fresh reader pointwise to
  the sealed convention. Non-tautological throughout.

## Fresh route — the depth-N scan (all EXACT; /tmp/hex3_pe5_fresh/{reader.c,compare.py,tie_json.py})

Own C implementation (own GF(p^d) table construction from irreducible
polynomials, own lower-hull walk, own synthetic-division multiplicity,
own char-p shift3, own key classification per the S2 definitions; ~33M
states/s). Protocol: validate on committed rows first, then extend.
* **Validation:** 8 rows ((Fqt,2,4..8),(3,4),(3,5),(4,4),(4,5)) — u ==
  law AND per-key species == closed forms both directions AND (on 7 rows)
  per-key == the committed JSON exactly.
* **Beyond the battery's window** (the corpus's deepest rows before this
  pass: N = 9 at q = 2, N = 6 at q = 3, N = 5 at q = 4):
  - **(Fqt,2,10): u = 449,792** — 134,217,728 states; **the first k = 3
    stratum instance anywhere** (ALPHA(3) = (512, 512), fully drained at
    the k = ⌊(N−1)/3⌋ corner where H-2(i)'s ghost-zone inequality is
    tightest);
  - **(Fqt,2,11): u = 1,840,640** — 1,073,741,824 states; ALPHA(3) =
    (4096, 2048) = ((q−1)q^{3N−3−18}, q⁹u(2)) ✓; 21 realized keys;
  - **(Fqt,2,12): u = 7,936,000** — 8,589,934,592 states (the largest
    exact enumeration in this corpus, ~8.6B states single run); 26
    realized keys ALL exact both directions; ALPHA(3) = (32768, 8192) =
    ((q−1)q^{3N−3−18}, q⁹u(3)) ✓;
  - **(Fqt,3,7): u = 734,589** — 387,420,489 states, 9 keys;
  - **(Fqt,4,6): u = 1,387,264** — 1,073,741,824 states, non-prime depth
    extension.
  Every row: u == THEOREM HEX3.A (computed from my own transcription,
  telescoped AND first-step forms), every realized species key ==
  the S5.1 closed forms BOTH directions, partition sum exact, DECIDED
  drain 0.
* **Never-instantiated (q,N) cells:** (8,4): u = 287,232 (first live
  k-term at q = 8); (9,4): u = 578,097; **(16,3): u = 65,536 = 16⁴ — the
  first q = 16 instance anywhere**; **(16,4): u = 17,698,816 —
  LANDED at exactly the preregistered value** (16⁶ + 15·16³·15·R(1);
  predicted in the committed report body BEFORE the run finished,
  commit 7e3185c): 68,719,476,736 states — the largest exact
  enumeration in this corpus — with ALPHA(1) = (61440, 61440) and
  FULL11SQ(1) = (860160, 860160), both == S5.1, the first q = 16 row
  with live k-terms.
* **Second wave (run while the above completed):** (Fqt,3,8):
  u = 7,357,797 on 10,460,353,203 states (depth +2 beyond the battery's
  q = 3 window; 12 keys, k = 2 with M = 2 live); (5,5): u = 450,625
  (depth +1 at q = 5); (5,6): [in flight; prediction u = 12,555,625 —
  the earlier committed figure 22,225,625 was this verifier's own
  arithmetic slip, corrected from the law before the run finished];
  (7,4): u = 129,997 (new cell, live k-term); (7,5): u = 6,456,289
  on 13,841,287,201 states (depth +2 at q = 7); (11,4): u = 1,904,661
  (2.36B states, new cell); **(13,3): u = 28,561 and (13,4):
  u = 5,143,177 (10.6B states) — the first equal-characteristic q = 13
  instances anywhere** (the corpus's q = 13 rows were ℤ_p-only), giving
  a NEW characteristic-independence pair beyond the battery's 17:
  my (Fqt,13,3) u == the committed (Zp,13,3) u_measured (28,561)
  exactly; (25,3): u = 390,625 = 25⁴ and (27,3): u = 531,441 = 27⁴
  (first N = 3 instances at q = 25, 27). Every row: u == the law (both
  forms), species == S5.1 both directions, partition exact, DECIDED
  drain 0. Cumulative fresh-route states this pass: ~36B, all exact.
* *Disclosure (own-bug, caught by my own validation, note untouched):*
  my first GF(4) invocation passed p = 4 (non-prime) instead of
  (p,d) = (2,2), silently building Z/4-flavored tables; the validation
  tie caught it instantly. Fixed by correct (p,d,irred) arguments.

## Disposition

0 CRITICAL, 0 GAPS, 2 MINOR — both one-clause, note-only, non-theorem
phrasing repairs whose blast radius is verified zero (m1: the corrected
warrant is the post-r4 W-12 S2.3 restricted to disc ≠ 0 lifts, under
which U₃^σ ≤ U₃^conv is intact; m2: the L438 parenthetical + its
"fully-hidden" gloss). The law itself now stands machine-exact on a
window strictly deeper than anything the battery or any prior pass
touched (N = 10, 11, 12 at q = 2 with the first k = 3 stratum keys, N = 7
at q = 3, N = 6 at q = 4) and at new prime-power cells ((8,4), (9,4),
(16,3)). Structural bonus: the reader's own invariants (at most ONE
repeated-root side per read state, always on a width-comparable side —
the S2 partition's uniqueness) were hard asserts in my C reader and
never fired across ~11.8B states read, depths no instrument had touched. **Counter stays 0/2 per protocol; r4 owed on m1 + m2, then
PE6 is the next pass.** Per-protocol note for the adjudicator: both
findings are inherited-phrasing corrections that W-12's own arc already
priced ("owed at HEX3's own arc"); if r4 lands as the two one-clause
fixes above, nothing else in the note is known-unmined to this verifier.

*(Appendix — pending rows: (Fqt,2,12) and (Fqt,16,4) results appended
below when the detached runs complete.)*
