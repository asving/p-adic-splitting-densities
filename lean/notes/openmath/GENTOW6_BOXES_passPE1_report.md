# GENTOW6-BOXES passPE1 — HOSTILE VERIFIER REPORT (2026-08-10)

**VERDICT: NOT CLEAN — 1 CRITICAL + 1 GAP + 2 MINOR.** Target:
GENTOW6_BOXES_2026-08-10.md at HEAD (chain d1eeb869 → 2ae94ded →
a646c7c9 → 90b23648 → b1b6aa61; grade 0/2). Protocol:
quote-and-classify, nothing fixed. The CRITICAL is a displayed
theorem clause refuted by a constructed frame the verifier's own
sealed-style fresh leg machine-confirmed; the downstream clauses
(b1)/(b2)/(c)/(d) SURVIVE at that same frame — the defect is
localized to (a)'s equality sentence and Step III's wording, and
the note's own Step IV parenthetical already contradicts it. The
GAP is an overclaiming "iff" in the two dated append summaries
(GENTOW6_PROOF + PROJECT_STATE #21), not in the boxes note itself;
a second constructed frame refutes the iff's unproved direction.
Both machine legs re-verified bit-identical; the fresh route ran
141/0 on eight frames including m = 6, 7 and the first p = 5 rows.

## FINDINGS

### F-1 — CRITICAL (statement): 6.5(a)'s equality-forcing sentence
### is false at e2(f2 − t*) = 1 geometries

Quote (S2, clause (a), lines 119-122): "Y <= e2 f2 (m - k) +
e2 Sum t + e <= B* + 1, with Y = B* + 1 forcing (k, multiset, e,
steps) = (2, {t*, t*}, 1, 0)." Quote (Step III, line 197-199):
"with Y = B* + 1 forcing k = 2, e = 1, and e2 Sum t = 2 e2 t*".

Step III's own display reads Y <= B* + 1 − (k−2)(e2(f2−t*) − 1):
when e2(f2 − t*) = 1 (e2 = 1, t* = f2 − 1 — a nonempty family
inside the theorem's stated f1 = 1 scope), the k >= 3 all-t*
multisets with e = k − 1 extractions also reach Y = B* + 1
whenever k·i_{t*} >= (k−1)·D' (achievable from D' >= 3: i_{t*} =
D'−1 at k = 3). The note's own Step IV parenthetical (lines
247-249) concedes exactly this ("k >= 3 sources with e = 2 can
reach Y = B* + 1 only when e2(f2 − t*) = 1") — the theorem
statement and Step III contradict Step IV.

CONSTRUCTED COUNTER-FRAME (CE3, verifier's own, machine-confirmed
141/0 leg): Q2, Phi' = x³−2 (e1 = D' = 3, h = 1), e2 = 1, f2 = 2,
u2 = 5, T = {0,1}, t* = 1 (i_1 = 2, a_1 = 1, chat_1 = 1; i_0 = 1,
a_0 = 3; residual z²+z+1 irreducible over F_2; delta = 2, E2 = 10),
Phi2 = Phi'² − 2x²Phi' − 8x, m = 3. B*+1 = 5; the k = 3 diagonal
source −8x⁶Y³ extracts twice (x⁶ = (Y+2)²) to −8Y⁵ = Y^{B*+1} at
x-slot 0 ≠ a* = 1. Measured: ShC_2 = {(1,1): 12, (0,1): −8,
(0,0): 160, (2,0): −32} — the (0,1) = −8 monomial's only trace is
(k, multiset, e, steps) = (3, {t*,t*,t*}, 2, 0), refuting the
forcing clause as displayed.

Failure scenario: a consumer citing 6.5(a)'s equality case
verbatim at an e2 = 1, t* = f2−1 genre (the sealed battery's B3
axis, one i_{t*} larger) derives slot-uniqueness at Y = B*+1 that
is false, e.g. concluding the certificate is the ONLY Y-ceiling
content and mis-pricing coordinate-j* slots.

What SURVIVES (verified at CE3 itself): (b1) held exactly — cert
digit 12 = binom(3,2)·chat²·π² at (a*,b*) = (1,1), v = 2, graded
THETA_2 = 12 nonzero, pin 12 on the floor; (c) vacuous there
(j* = m−1); the refuter sits at v = 3, height 14 = THETA_2 + 2δ −
... i.e. strictly above the graded layer (Step IV's weight fence),
and at x-slot k·i* − (k−1)D' = 0 < a* = 1 — the k >= 3 equality
branches can never reach x-slot a* (k·i* − (k−1)D' < 2i* − D' iff
i* < D', always). The proof of (b) therefore stands via Step IV's
weight sentence; the repair is a conditioning of (a)'s equality
sentence (e2(f2−t*) >= 2, or the explicit k >= 3 exception with
its x-slot displacement), not a re-proof.

RIPPLE SITES carrying the false phrase: GENTOW6_PROOF dated append
(line ~1206, "with the unique equality case"); PROJECT_STATE
append #21 ("the B*+1 Y-ceiling and unique equality case");
ANNEX-REMARK 6.5' delta (i) ("Y-uniqueness is x-shape-blind")
rides the same sentence at f1 >= 2.

### F-2 — GAP (summary overclaim, machine-refuted): "attainment on
### the floor iff p does not divide binom(mu2,2)" in the two dated
### appends

Quote (GENTOW6_PROOF dated append, lines ~1211-1214): "attainment
on the floor iff p does not divide binom(mu2,2), with (b2) the
honest cancellation clause"; PROJECT_STATE append #21 repeats it
("attainment on the floor iff p ∤ binom(m,2)").

The theorem proves only the forward direction; (b2) is explicit:
"No attainment is claimed under (b2)" — the cancellation is at the
certificate SLOT, and nothing rules out floor-height divergence at
another slot of coordinate j*. CONSTRUCTED REFUTER (BP3,
machine-confirmed): Q3, Phi' = x²−3, e2 = 1, f2 = 2, u2 = 3,
t* = 1 (i_1 = 1, a_1 = 1; i_0 = 0, a_0 = 3; z²−z−1 irreducible
over F_3; delta = 1, E2 = 6), Phi2 = Phi'² − 3xPhi' − 27, m = 3,
p = 3 | binom(3,2) = 3. Measured: cert slot (0,1)@j2 = 27 with
v_3 = 3, graded THETA_2 = 7 digit ZERO (the (b2) kill fires,
height 9 > 7) — yet slot (1,0)@j2 = 135 (the m = 3 triple branch
−27xY⁴, e = 1, weight mE2 + delta, plus above-layer stepped
content) has v_3 = 3, graded-7 digit NONZERO: pin(ShC_2) = 7 =
THETA_2. The shadow diverges from DRAIN exactly on the floor at
coordinate j* although p | binom(m,2): the iff's only-if direction
is false, not merely unproved. The boxes note's own sentences
(S2 (b1)/(b2), S6, the record block) are honest — the defect lives
only in the two append summaries (both written by this unit).

Failure scenario: a later note consumes the append's iff as a
p-characterization of mu2 >= 3 attainment and concludes
non-divergence at p | binom(m,2) genres — false at BP3's family
(the same e2(f2−t*) = 1 axis as F-1, where floor-height branches
at non-certificate slots exist).

### F-3 — MINOR: Step IV's source-uniqueness census omits k <= 1

Quote (lines 226-230): "is UNIQUE at that (x, Y)-position among
all sources: a k = 2 non-diagonal multiset ... a k >= 3 multiset
there ...". A k = 1 source CAN sit at Y-position B* when
2t* >= f2 (t = 2t* − f2 in T), which the census never mentions;
it is excluded at the x-position only because i_t < D' <= 2i_{t*}
under (b)'s hypothesis — one missing line, no consequence.

### F-4 — MINOR: run-1 want repair slightly understated as "NO
### theorem-facing want changed"

The B3 (1,0)@j2 want changed from the exact value −8 to
(v = 3, graded-THETA nonzero) after run 1 (seal 78ac4e82 vs
repaired c98cb423, diff verified = the disclosed literals). The
slot is an instrument display slot (the theorem prices only the
certificate slot), and the disclosure is full and hand-traced, so
the sentence is defensible — but the corrected spec is weaker than
the sealed one, and the fresh leg's BP3 (predicted robust v/graded
only, measured 135 vs a naive −27+81 = 54 hand sum) shows exact
stepped-multiplicity wants at e2(f2−t*) = 1 display slots are not
ledger-derivable; the honest phrasing is "one instrument want
weakened to what the ledger licenses, disclosed".

## MACHINE LEG (verifier's re-verification)

* md5 census: runners c98cb423 / 9d6e16cc, outputs 0a4cd16f /
  2d8d617a, REDs a0fb948d / 0269e02e, import 061639c3 — each
  matches the note. Seal-commit versions md5 78ac4e82 (@ 2ae94ded)
  / c0fbd1e4 (@ 90b23648); seal → repaired diffs are exactly the
  two disclosed repair sets (B3 display want + j'=0 disc row; the
  gp Vecrev(0) literal).
* Isolated re-runs (fresh /tmp, this pass): BOX-1 BIT-IDENTICAL
  (md5 0a4cd16f), 459 checks / 0 violations, teeth T-ALLM 3,
  T-COEF 2, T-VAL 7, T-TOPZ 6 — exact; BOX-4 BIT-IDENTICAL
  (2d8d617a), 265 / 0, teeth 4/4/4 — exact.
* Tautology audit: wants are docstring/table literals; the
  measurement path runs from integer Phi2 coefficients through the
  runner's own dev + dual R/E division; gp leg decorrelates;
  graded/pin semantics verified against the note's height
  convention at four committed frames by hand.
* Frozen-note discipline: GENTOW6_PROOF pre-append prefix md5
  157b16ad re-verified byte-identical (67,448 bytes) under the
  current file; the unit's two appends are pure appends.
* Supplier census: GENTOW3 ACCEPTED 2/2 (Step 1/2 ledger stated at
  general mu2 — verified at lines 229/252); GENTOW1 ACCEPTED 2/2;
  GENTOW6_PROOF ACCEPTED 2/2 with 6.3' landed at r1 BEFORE the two
  clean passes ("accepted 6.3'" is fair); obs-1's vector
  [2^19xY, 12288Y, 0] pins [91,61,None] verified at
  GENTOW3_passPE5_report line 209. BOX-4's discharge sentences
  stay inside mu2 = 2 and name the f1 >= 2 × mu2 >= 3 compound as
  uncontacted — no overclaim found in S5.

## FRESH ROUTE (gentow6_boxes_pe1_fresh.py md5 fae8bc99, output
## b377850b — independent implementation, no sealed-runner import)

141 checks / 0 violations on eight frames, wants hand-derived and
preregistered in the docstring: X3 bridge (committed PE5 vector
reproduced exactly by the independent code); F6/F7 = FR5X at
m = 6, 7 (first m > 5 anywhere: digits 61440 = 15·4096 and
86016 = 21·4096, v = 12, pins 61 = THETA_{j*} on the floor —
6.5(b1) extends); P36 = GEN-P3 at m = 6 (p = 3 | 15: graded-21
zero, pin 25 — a NEW p-odd kill row); Q55/Q57 = first p = 5 frames
(Phi' = x²−5, Phi2 = Phi'²−125x, u2 = 7): m = 5 kill
(10·5⁶, v = 7, pin 35) and m = 7 attainment return (21·5⁶, v = 6,
pin 31 = THETA_5) — the binom(m,2) law and both cancellation
directions hold at a third prime; CE3 (F-1's refuter; (b1) held
there); BP3 (F-2's refuter). Dual R/E routes slot-identical and a
third oracle (exact reconstruction F = Σ Ghat_j·K2^j before any
reduction) held at each frame; honest reads DRAIN; floors held at
each coordinate of each frame; six above-top coordinates empty.
The verifier's CE3 full-vector hand ledger matched the machine
exactly, including pins [32, 22, 12].

## RE-VERIFIED CORE (verifier's own derivations, no findings)

j* = (m−2) + floor((2e2t*+1)/(e2f2)) re-derived from B*+1;
the graded digit binom(m,2)·ĉ²·π^{2a}·wrap re-derived from the
diagonal-pair multinomial (m!/((m−2)!2!)), sign (+1)², one
extraction with Y-branch coefficient 1, top-route division, and
checked numerically at seven committed slots (12288/24576/48/12/
972/1944/3240 — each = binom(m,2)·ĉ²·π^{2a} exactly); the S3
FR5X-3 slack assembly (−1+3)·2^18 re-derived by full hand division
(signs confirmed); the BOX-4 R3/R4 hand ledger re-computed
(a_0 = 5, THETA_0 = 47, slot (2,1), digit 256 = 2^{2(5−1)}, w =
2a + 11b); (c) and (d) proofs verified sound; Step V's pair
cancellation verified (the terminal mod-Phi' reduction IS the
iterated tail substitution); the m = 2 specialization to 6.3
checked clause by clause against the accepted 6.3 text.

## GRADE LINE

passPE1 verdict: **NOT CLEAN (1 CRITICAL + 1 GAP + 2 MINOR)**.
The note's acceptance counter STAYS 0/2; a repair round is owed
before any further hostile pass counts. The repair surface is
narrow: condition (a)'s equality sentence (and Step III's wording)
on e2(f2−t*) >= 2 or display the k >= 3 exception with its x-slot
displacement (the CE3 frame is a ready-made battery row), and
strike/date the "iff" in the two append summaries to the forward
implication + the (b2) clause (the BP3 frame is a ready-made
counter-row). Findings F-1/F-2 do not touch the sealed batteries'
measurements, the binom(m,2) law itself, or the BOX-4 discharge.
