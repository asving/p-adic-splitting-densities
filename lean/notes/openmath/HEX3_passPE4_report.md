# HEX3 passPE4 report — hostile verification of HEX3_PROOF_2026-08-08.md (the accepting attempt)

**Pass:** PE4 (fourth hostile pass; arc PE1 0C+2G+2m @ d177fd8 → r1 @ 2580f12 →
PE2 0C+1G+1m @ f60348b → r2 @ a707430 → PE3 CLEAN @ fca1a97, counter 1/2 —
this pass was the accepting attempt: a second consecutive clean pass accepts at
2/2). **Verifier:** fresh-context Fable, 2026-08-08. **Target:**
HEX3_PROOF_2026-08-08.md at HEAD, byte-frozen since r2 (`git diff a707430 HEAD`
empty — verified); runner + artifacts byte-frozen at seal e3f3459. All three
prior reports and both repair diffs (single-file note-only, verified by
`--stat`) read in full. **Charges (unmined per the three reports):** (1) the
α-route re-derived from scratch — the self-similar scaling q^{3k}·u(N−3k) and
its ghost-zone interaction with the CORRECTED N−jk pairing; (2) THE CROSS-NOTE
CHECK: THEOREM HEX3.B's role in W-12's (A2) at the NOW-PINNED definition
(W-12 PE3 report c9c5c0e finding 1 = the σ-pin; W-12 r3 landing in parallel) —
does the (hExhaust-3) discharge survive the pin?; (3) HEX3-W12TIE currency at
HEAD post-W-12-r3 (race noted honestly); (4) the smoke-record discipline
(S7's disclosed record vs the committed runner's `--smoke`); (5) wild-card:
consumer fired-clause aging sweep (HMENU3/GENH4/GENHN/BCFGTIE) + a fourth
independent census recount. Machine leg: pins, byte-identity, full re-run,
count reconciliation, smoke reproduction, artifact restoration. Fresh route
(differs from PE1's enumerator, PE2's poly-identities + block reader + field
tables, PE3's renewal-GF + nine DVR types): (A) the generating function
DERIVED in closed form by partial fractions — PE3's order-9 structural
denominator independently re-derived, proved structural BY HAND, and pushed to
MINIMALITY (new); (B) own enumerator in SIX further never-instantiated DVR
types, including the first ramified ring with non-prime residue field and the
first q = 81 instance anywhere.

**VERDICT: NOT CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAPS + 1 MINOR.** Every
theorem (HEX3.A/B/C), every transport lemma, the discharge scope, the machine
leg, and the census survived; the cross-note check's headline answer is
POSITIVE — **the (hExhaust-3) discharge survives the σ-pin, and is in fact
parse-ROBUST** (analysis under charge 2). The one finding is in the S8.2
downstream aside — the same sentence PE1-m2 and PE2-m1 repaired
arithmetically: its closing consistency clause asserts, as fact, the
σ-decidedness of the transported TRP SPLIT-TAIL mass — which is precisely
HEX3-BOX-1's OPEN tail-σ-certification lemma. The pre-pin ambiguity of
"undecided" hid this; the W-12 σ-pin (r3 — landed at b17238a mid-pass,
byte-identical to the draft audited here) makes it visible.
Counter resets to 0/2 per protocol; repair is one clause, note-only.

---

## m1 [MINOR] — S8.2 item 2's W-12.B consistency clause asserts HEX3-BOX-1's open certification lemma as fact ("belongs to (A2)'s boundary families")

Quote (S8.2 item 2, closing clause; the same sentence whose arithmetic was
repaired at r1-m2 and r2-m1):

> so the conservative residue sits Θ(N(q−1)²·q^{2N−4}) above its head […] —
> consistent with W-12.B only because the SPLIT-TAIL-type mass belongs to
> (A2)'s boundary families, exactly as at n = 2 (W-12 S3.4's r(N) display).

The subject mass is the R-tail N-linear family of U₃^conv — the TRANSPORTED
TRP SPLIT-TAIL mass (R(M)'s floor term; the note's own BOX-1 names these
members). W-12.D's (A2) defines its residue in two components: "the
σ-undecided residue AND any window-boundary (tail) families" — so "belongs to
(A2)'s boundary families" places the mass in the SECOND component, i.e.
asserts it is σ-DECIDED (certified, hence outside W-12.B's undecided count).
For the TRP side that is exactly the OPEN tail-σ-certification lemma:
HEX3-BOX-1 prices these members as "the certifiable CANDIDATES" and W12-BOX-3
named the lemma as deliberately not attempted. The assertion is load-bearing
for the clause it warrants: if the mass were NOT boundary (uncertified), it
would sit inside U₃^σ and undecided(3,q,N)·q^{−2N} would diverge linearly
(the W-12-PE3 computation, asymptotic slope 1/24 at q = 2) — W-12.B would be
FALSE at n = 3. So the sentence resolves W-12.B's n = 3 consistency by
asserting the open lemma. The "exactly as at n = 2" analogy compounds it: at
n = 2 the membership is PROVED (W-11's SPLIT-TAIL certification), and the
n = 3 DBL analogue is also proved (W-12 r2's G2 leg — W-11 certification
through W12-L1(c), no scaling, no ghost-digit loss); the TRP-side transport
goes through σ_m SCALING, which loses ghost digits — exactly why BOX-1 is
open. The sentence conflates the proved (DBL) and open (TRP) sides of the
same genre.

Why three passes missed it: pre-pin, "undecided(n,q,N)" in W-12.B was
ambiguous (the c9c5c0e finding), and the clause could be read as σ-free
routing commentary; HEX3's own S0 razor-separation already fixes the
semantics, but the sentence sits in corroboration prose that PE1/PE2 audited
arithmetically (each repairing a factor in the SAME sentence) without
checking its final clause's warrant. Under the now-pinned (A2)/BOX-7
semantics the clause reads unambiguously as asserting the open lemma.

Classification: **MINOR** (same tier as PE1-m2/PE2-m1 on this sentence):
S8.2 is explicitly downstream corroboration prose; NO consumer relies on its
truth (W-12 r3's consuming-surface sweep cites this remark only for its
PARSE — "it routes the N-linear conservative mass to (A2)'s boundary
families — the pinned parse" — not for its truth); W-12.B remains a
conjecture; and the theorems are untouched — HEX3.B's discharge does not use
the clause and is parse-robust (charge 2). The claim may well be TRUE
(BOX-1 itself expects the certification to go through), but it is unproven
and stated as fact, in tension with the note's own BOX-1. Repair shape (one
clause): "…consistent with W-12.B only if the SPLIT-TAIL-type mass belongs
to (A2)'s boundary families — at n = 2 that membership is W-11-PROVED
(W-12 S3.4's r(N) display); at n = 3 for the TRP side it is precisely
HEX3-BOX-1's open certification lemma."

---

## Charge-by-charge record

**(2) THE CROSS-NOTE CHECK — HEX3.B at W-12's pinned (A2): the discharge
SURVIVES THE PIN, and is parse-robust.** (Reported first; it is the check
that matters most.)

* *Race status, honest:* at read time W-12 r3 was an UNCOMMITTED working-tree
  draft (W12_PROOF last commit = 99f1813 = r2; the draft diff was captured
  and audited). All checks below were run against BOTH the committed r2
  state and the r3 draft. **The race resolved mid-pass: r3 LANDED at
  b17238a while this report was being drafted, and the landed diff is
  BYTE-IDENTICAL to the audited draft** (diff-of-diffs empty) — everything
  below therefore holds at the new HEAD verbatim. The r3 σ-pin is exactly
  the c9c5c0e-F1 repair: the S1 σ-DECIDED sentence
  pinned to W12-BOX-7's lift-certification notion; the W-12.B bullet gains
  the σ-scoping clause ("NOT the conservative-read residue, whose normalized
  mass DIVERGES linearly at n = 3 (THEOREM HEX3.A)"); an [r3] F1 repair
  record with a consuming-surface sweep; the PE3-MINOR-1 wording fix; an arc
  record. Neither annex touched; no theorem statement moved; W12-L0/L1,
  S2.4, W-12.C — everything HEX3 consumes — untouched.
* *HEX3's quantities are already typed at the pinned notion.* S0's
  U₃^σ := "members … admitting two disc ≠ 0 lifts of different splitting
  type" is exactly the complement of BOX-7's lift-certification "Decided"
  (negation of "window digits force ONE σ across all disc ≠ 0 lifts"; every
  TRP member has disc ≠ 0 lifts, so not-forced ⟺ two lifts disagree). The
  r3 sweep independently lists "the BOX-3 annex's bracket quantity U₃^σ"
  among consumers of the PINNED notion — consistent with my read.
* *HEX3.B's chain re-typed link by link under the pin:*
  undecided(3,q,N) = (q−1)q^{2N−1} + U₃^σ (THEOREM W-12.C @ pin — the
  identity the r3 record confirms is stated at the BOX-7 notion)
  ≤ (q−1)q^{2N−1} + U₃^conv (conv-decided ⟹ σ-decided: a certification
  statement, valid under both parses — re-derived by PE1, re-checked here)
  ≤ (1+N)q^{2N}. Every link BOX-7-typed. **The (hExhaust-3) discharge
  survives the pin.**
* *Parse-robustness (stronger, worth recording):* under the pin, r(3,N)'s
  TRP mass splits as U₃^σ (the σ-undecided component) ⊔ {certified TRP
  boundary tails} (the boundary-family component), and U₃^conv is EXACTLY
  the union of the two (drained = σ-undecided ∪ certified-tail). HEX3.B
  bounds U₃^conv, so it dominates BOTH r(3,N) TRP legs at once: the
  discharge holds REGARDLESS of where the BOX-1 certification split lands.
  The vanishing claim never needed the split — only the S8.2 aside does
  (finding m1).

**(1) The α-route re-derived from scratch — CONFIRMED, including the
ghost-zone/corrected-pairing interaction.**
* *Retained windows re-derived from the scaling itself:* σ_k retains
  B_j/π^{(3−j)k} mod π^{N−3k}, i.e. B_j mod π^{(N−3k)+(3−j)k} = π^{N−jk} —
  the ghost zone at abscissa j is {≥ N−jk} (B₂ ↔ {≥ N−2k}, B₁ ↔ {≥ N−k},
  B₀ fully retained): the r1 pairing, re-derived independently.
* *Chord vs ghost:* hull heights at abscissa j are ≤ (3−j)(N−1)/3 (convexity
  from (0, u₀ ≤ N−1) to (3,0); u₀ ≥ N exits UNDECIDED on retained data).
  (3−j)(N−1)/3 < N−jk re-proved: j = 1 ⟺ k < (N+2)/3 (true, k ≤ (N−1)/3);
  j = 2 ⟺ k < (2N+1)/6 (true, k ≤ (2N−2)/6) — STRICT on the whole range
  including the k = ⌊(N−1)/3⌋ corner. A ghost-range point (j, v ≥ N−jk)
  sits strictly above the chord, hence above the lower hull — never a
  vertex; whether v(B_j) ≥ N−jk is itself retained-determinable (all
  retained digits vanish); residual coefficients live at hull lattice
  heights ≤ chord < ghost. Update congruences re-checked: B₀′ needs B₁ mod
  π^{N−k−1} and B₂ mod π^{N−2k−2}; B₁′ mod π^{N−k} needs B₂ mod π^{N−2k−1}
  — all inside the retained windows.
* *v(s) ≥ k+1 chain-wide from D_k — INTEGRALITY does the work:* a width-3
  side from (3,0) has slope v(B₀)/3 ≥ (3k+1)/3, integer ⟹ ≥ k+1; width-2
  slope v(B₁)/2 ≥ (2k+1)/2, integer ⟹ ≥ k+1; width-1 slope v(B₂) ≥ k+1.
* *The α-map:* pins at heights k, 2k, 3k all sit below the ghost thresholds
  (3k < N); the (y−z)³ shift identities (c₂+3z, c₁+2c₂z+3z², c₀+c₁z+c₂z²+z³
  all = 0) re-expanded, valid verbatim in the char-2/3 degenerations; the
  z-slice → D_k translation is injective with q^{3N−3−6k} on both sides —
  bijection; the shear (j,v) ↦ (j, v−(3−j)k) is affine-in-j (preserves
  hulls, lattice points, residual positions); the drain window is exact
  (v(B₀) ≥ N ⟺ v(B₀/π^{3k}) ≥ N−3k). Ghost fiber = 2k B₂-digits + k
  B₁-digits = q^{3k}, verdict constant on fibers ⟹ D_k drain =
  q^{3k}·u(N−3k), α-term (q−1)q^{3k}u(N−3k). ✓ = S5.1.
* *Machine tie at the corner:* my OWN enumerator (fresh route, leg B)
  reproduces the (Zp,2,7) species table per key against the committed JSON,
  including ALPHA(2) = (64, 64) at k = 2 = ⌊(N−1)/3⌋ (locus 2⁶ ✓, drained
  2⁶·u(1) ✓) and ALPHA(1) = (4096, 576) (drained 2³·u(4) = 8·72 ✓); the
  same table reproduced in the NEW ring ℤ₂[√−2] at (2,7).

**(3) HEX3-W12TIE at HEAD — CURRENT, verified across the r3 landing.**
`w12_checks_results.json` md5 re-hashed == the HEX3-PIN value (0577…);
single-commit history (c16c717) re-verified. The §S8.1 annex block,
quote-normalized, is EQUAL (702 chars) between the HEX3 note and W12_PROOF
both at the r2 state and after the r3 landing (b17238a, byte-identical to
the audited draft) — r3 leaves the applied annex intact and is note-only
(runner + artifacts untouched; seal f669cb0 md5 re-verified in its own
commit record). Fresh full-run W12TIE 23/23 GREEN this session. Nothing
HEX3 consumes moved: the r3 hunks touch S1's σ-DECIDED sentence (pinning
exactly the parse HEX3's S0 already uses), the W-12.B bullet (not consumed
by HEX3's theorems), the new [r3] F1 record, one S7 oracle-warrant wording,
and the arc record.

**(4) Smoke-record discipline — REPRODUCED TO THE DIGIT, with all six
figures + teeth hand-derived first.** `--smoke` fresh run: PIN 4 / LAW 24 /
SPECIES 30 / XREAD 26,730 / W12TIE 12 / CHAR 4, teeth 1/4/1, GREEN 0.4 s ==
S7's disclosed record. Hand derivations from the frozen SMOKE rosters
(7 ℤ_p + 5 𝔽_q[[t]] rows): XREAD = (64+512+4096+27+729+19683+125) +
(64+512+729+64+125) = 25,236 + 1,494 = 26,730 ✓; CHAR = shared smoke pairs
{(2,3),(2,4),(3,3),(5,2)} = 4 ✓; W12TIE = 12 (every smoke row inside the w12
committed table — the S7/PE3 claim that smoke ⊆ w12-measured re-confirmed) ✓;
T-FLOOR = rows with some N−3k even = {Zp(2,5)} = 1 ✓; T-ALPHA = N ≥ 4 rows =
{Zp(2,4),(2,5),(3,4); Fqt(2,4)} = 4 ✓; T-VERT1 = N ≥ 5 = {Zp(2,5)} = 1 ✓.
The smoke rows are all inside the w12-committed 14 pairs (census
decontamination re-confirmed at the smoke level).

**(5) Wild-card — consumer fired-clause aging sweep + fourth census
recount.**
* *HMENU3 (ACCEPTED 2/2):* fires H-1 (partition, verbatim), H-2(i)/(ii)/(iii)
  (LEMMA HM3-2 by name), H-3, and re-derives HEX3.A term by term; its S6
  display consumes "q·u(q,N) [TRP, HEX3.A]". Every fired clause lives in
  S2/S3/S5 — NONE touched by r2 (the r2 diff = S1 census sites, S7 P-1,
  S8.2, S10 brackets). Fired clauses byte-current at HEAD.
* *GENH4 (r1):* consumes ν₃/P(3) conclusions; its own supplier refresh
  (dff23f8) already tracks HEX3 at r2 + PE3 CLEAN 1/2 + PE4 accepting; no
  consumed value changed in any HEX3 repair (all repairs were census
  bookkeeping, proof-display fixes, and the S8.2 aside).
* *GENHN:* pins HEX3 @ r2 (f60348b + a707430) — current.
* *BCFGTIE:* grep finds NO HEX3-citing surface in BCFGTIE_2026-08-08.md at
  read time (the dispatch brief listed it as a HEX3 consumer; textually it
  consumes W-11/W-12 level-0 machinery only; its note is in-flight).
* *Census, fourth independent recount from primary sources:* roster from the
  frozen runner = 21 + 25 rows, 17 shared, 29 distinct pairs; w12 cubic
  table re-extracted = 14 pairs; recursive sweep of the ENTIRE pinned w12
  JSON: q ∈ {8,9} appear NOWHERE at N ≥ 3; + prototype {(5,3),(7,3),(11,2)};
  29 − 17 = 12, difference set element-for-element == the r2 bracket's
  honest 12-set. The twice-burned census is right.

## Machine leg (this pass; all runs fresh in this session)

* PINS: all four md5s re-hashed and MATCH (w12_checks.py 7dc0…, w11_checks.py
  500a…, w10_checks.py a9c3…, w12 JSON 0577…).
* Runner md5 83faf7ed… == the r1/r2-recorded seal value; `git diff e3f3459 --
  hex3_checks.py` EMPTY; both repair commits single-file note-only.
* FULL RE-RUN (single fresh run): exit 0, **GREEN, 158,512 checks / 0
  violations** — PIN 4, LAW 92, SPECIES 172, XREAD 158,204, W12TIE 23,
  CHAR 17; teeth fired 10/20/13 == preregistered; 46/46 rows, 327.5 s.
  Output diff vs committed = per-row timing decimals only; recursive JSON
  diff = 19 leaves, ALL elapsed_s, ZERO non-timing. Artifacts restored;
  md5s (6e4b…, ce6f…) == §S10's display.
* SMOKE: reproduced to the digit (charge 4 above).

## Fresh route (no runner imports; /tmp/hex3_pe4/leg_a_gf.py, leg_b_rings.py)

**Leg A — the generating function DERIVED (not just verified), denominator
proved structural BY HAND and pushed to MINIMALITY (new beyond PE3).** Own
law transcription; closed form == first-step recursion as POLYNOMIALS in q,
N = 1..60 (extends PE2's N ≤ 40). Derivation: U = S + A·T with
S = x/(1−q²x), A = (q−1)q³x³/(1−q⁴x³), and T = Σ(q^M−1)R(M)x^M computed in
closed form by the parity split — T = qx/(1−q²x) − x/(1−qx) +
((q−1)/q²)[G(q²x) − G(qx)], G(y) = y³/((1−y)²(1+y)) — whence
den(U) | D := (1−q²x)²(1+q²x)(1−qx)²(1+qx)(1−q⁴x³): PE3's order-9
denominator re-derived from scratch and proved STRUCTURAL (each factor
exhibited by an explicit partial fraction). Machine ties: D·U truncates
(coefficients of x^10..x^60 all zero as polynomials in q); P = D·U has
x-degree 9; the order-9 recurrence Σᵢ Dᵢ u(N−i) = 0 verified N = 10..60 at
six primes. **MINIMALITY (new):** P is nonzero at every root of every factor
of D (checked exactly at q = 2..39), and the hand partial-fraction residue
of U at x = −1/q, −(q−1)²/(4q²(q+1)), matches the machine value EXACTLY at
six primes — no factor cancels; D is THE denominator. Own law == committed
u_measured on 46/46 rows.

**Leg B — own enumerator (own hull walk, own deflation multiplicity, own
generic cubic recentering, own residue-field tables) in SIX further
never-instantiated DVR types.** Validation first: (Zp,2,7), (Zp,3,4),
(Fqt,4,4) — u AND every per-key species (locus, drained) == the committed
JSON (including the α-corner keys, charge 1). New rings, ALL GREEN (u == law,
species == S5.1 both directions, partition sum exact, DEC-drain 0):
* **W(F₂₇)** at (27,2) — first mixed-characteristic q = 27;
* **ℤ₂[√−2]** at (2,7) — a new Eisenstein type (π² = −2; PE3 did π² = 2 and
  ∛2), at the DEEP window: k = 2 corner, R(4) parity content, full
  VERT1/VERT2 key set, species table == the (Zp,2,7) table exactly;
* **ℤ₃[√−3] = ℤ₃[ζ₃]** at (3,4) — the Eisenstein-cyclotomic type;
* **W(F₄)[π], π² = 2** at (4,4) — the FIRST ramified ring with NON-PRIME
  residue field ever instantiated in this corpus (e = 2, f = 2 over ℤ₂);
* **W(F₈)** at (8,3) — the first mixed-characteristic q = 8: the
  twice-burned census pair (8,3) now measured in a THIRD ring type,
  8·4096 = 32,768 on the nose;
* **F₈₁[[t]]** at (81,2) — the first q = 81 instance anywhere: u = 6561 = 81².

*Disclosure (own-bug repair, none touched the note):* my first ramified
implementation dropped a sign — with π² = εp, the Witt-coordinate p-digit at
level j is the π-coefficient times ε^j; the omission is invisible at p = 2
and surfaced at p = 3, ε = −1 as a PERIOD-2 CYCLING read chain on
f = x³ − π³ (= x³ + 3π in ℤ₃[√−3]). Fixed in my coordinates, the law holds.
A concrete live demonstration of exactly the gauge/carry seam HEX3.C's
mechanism (J-D0) fences: the law is blind to the DVR only when the digit
bookkeeping is faithful.

## Disposition

0 CRITICAL, 0 GAPS, 1 MINOR (the S8.2 consistency clause — one-clause,
note-only repair; blast radius zero on the theorems and on the discharge).
The headline cross-note verdict: **the (hExhaust-3) discharge survives the
W-12 σ-pin and is parse-robust** — HEX3.B bounds U₃^conv, which dominates
both TRP legs of r(3,N) regardless of how BOX-1's certification resolves.
Machine leg bit-reconciled GREEN; fresh route confirms the law in six more
never-instantiated ring types and closes the denominator question
(structural AND minimal). **Counter resets to 0/2 per protocol** (a finding,
however small, is not a clean pass); r3 owed on m1, then the 2-clean bar
applies afresh. Per-protocol note for the adjudicator: if the repair lands
as the one-clause conditionalization above, nothing else in the note is
known-unmined to this verifier.
