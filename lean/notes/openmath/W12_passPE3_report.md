# W12 passPE3 report — hostile verification pass 3 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD = post-r2
(99f1813, all five PE2 findings + ANNEX 2) after the post-r1 HEX3 annex
(8e535d2). Read first: both prior reports (PE1 2b47711, PE2 1be15d2), both
repair diffs (r1 ba0d1a4, r2 99f1813), both dated annexes and their
supplier notes. This pass fixes nothing; it quotes and classifies.
Fences/boxes/annexes are read as part of the statement.
Charge-designated veins: (1) the r2 edits (three-genre disc = 0
disposition + fourth-genre hunt; the r(3,N) boundary-tail display
re-derived from W12-L0 × L1(c); the m_i·b_i fix); (2) the annex
interaction at HEAD with the suppliers MOVED since the annex dates;
(3) CONJECTURE W-12.B's own well-formedness (is c_n(q) well-defined by
the display?); (4) the §S5 J-D1 handoff display re-derived against the
blueprint + JD0 at their pins; (5) one unmined S3 detail (chosen: S3.4's
"(A1)-admissible" claim for the seven TRP families). Provenance: three
prior PE3 incarnations died to API errors; no predecessor draft existed
at /tmp/w12_pe3_draft.md — this pass is a cold start, its own draft
written incrementally there.

**VERDICT: NOT CLEAN — 0 CRITICAL + 1 JUSTIFICATION GAP + 1 minor
(+ 3 uncounted remarks). The gap: the statement complex carries TWO
non-equivalent definitions of the load-bearing quantity behind
CONJECTURE W-12.B — S1's read-anchored "σ-DECIDED" vs BOX-7's
lift-certification "Decided" — which coincide at n = 2 only because
W-11 PROVED its read certifies SPLIT-TAIL, and provably diverge at
n = 3 on the TRP tail genre: under the read-anchored/conservative
parse W-12.B is FALSE at n = 3 (the normalized conservative residue
DIVERGES linearly — verified this pass from THEOREM HEX3.A, whose law
my own transcription ties to all 23 committed U₃ values), while every
PROVED and machine-checked display in the note uses the BOX-7 notion
and is robust. The minor is an r2-introduced per-state description
slip inside the genre-(ii) warrant. Everything else checked CLEAN:
no fourth disc = 0 genre exists (re-proved from scratch); the
boundary-tail mass ⌊(N−1)/2⌋(q−1)²q^{2N−2} re-derived from
W12-L0 × L1(c) and verified against the committed JSON on all 23 rows
(per-w aggregates and N = 2 exact zeros included); the m_i·b_i
integrality route is sound; both annexes are byte-faithful, correctly
dated, and claim NO grade they predate (timeline verified against git
to the second); the §S5 handoff display is byte-faithful to the
blueprint and consistent with JD0 at its pin; the seven TRP families
are (A1)-admissible as claimed (verified family-by-family, first time
in the arc). Machine leg: runner md5-identical to seal f669cb0, re-run
exit 0 GREEN 3,232,506/0, teeth 23/23/8/1273, every count == §S10,
artifacts content-identical ex-timing (committed bytes restored).
Fresh route (disjoint from PE1's and PE2's rows): own arithmetic end
to end on cubic (Zp,7,2), (Fqt,4,2), (Fqt,2,5) and quartic (Fqt,4,3) —
the first prime-power-q fresh route at BOTH degrees — ALL pointwise
identical to the committed JSON. Counter: 0/2 (this pass is not
clean); r3 owed on the two findings — both one-to-two-sentence
display repairs.**

---

## 1. FINDINGS

### FINDING 1 — JUSTIFICATION GAP (W-12.B's quantity is pinned by two non-equivalent in-statement definitions; the wrong parse falsifies the conjecture at n = 3)

**Quotes.** S1 (conventions): "f is σ-DECIDED at window N if every
O-lift of f with disc ≠ 0 has **the read's σ**." W12-BOX-7: "**Decided
= certified on window digits for all disc ≠ 0 lifts**; the DBL side
inherits W-11's proved convention (incl. its SPLIT-TAIL
certification); the TRP side uses the BOX-3 conservative convention."
CONJECTURE W-12.B: "there is c_n(q) ∈ ℚ(q) … with
undecided(n, q, N)·q^{−(n−1)N} → c_n(q)".

**Classification: JUSTIFICATION GAP** (statement-side definitional
seam; blast radius = the CONJECTURE's display only — every proved
chain verified robust, see below). The two definitions are not
equivalent at general n. S1's read description (level-0 → branch
development → polygon → residuals → refine) specifies NO
tail-certification rule, so "the read's σ" on a tail member (constant
term window-hidden) is undefined ⟹ read-anchored undecided counts
every tail member. BOX-7's notion decides exactly the members whose
window digits force one σ across all disc ≠ 0 lifts. At n = 2 the two
agree only because THEOREM W-11 proved its read certifies SPLIT-TAIL
(consumed at pin); at n = 3 the TRP tail-certified genre separates
them — that is BOX-7's own sentence ("The two conventions can disagree
only on deep-tail TRP members"). The consequence is material for
W-12.B, and this pass verified it quantitatively: under the
read-anchored/conservative parse, undecided(3,q,N) contains the full
conservative residue U₃^conv = q·u(q,N) (THEOREM HEX3.A, consumed by
the BOX-3 annex), and the normalized mass q·u(q,N)·q^{−2N} DIVERGES
linearly in N — my own transcription of HEX3.A reproduces all 23
committed U₃ values (0 mismatches) and evaluates at q = 2 to 0.50
(N = 3) → 0.86 (N = 10) → 2.53 (N = 50) → 8.78 (N = 200), asymptotic
slope 1/24 — so NO c₃(q) exists and W-12.B is FALSE at n = 3 under
that parse. Under the same parse even THEOREM W-12.C's displayed DBL
constant (q−1)q^{2N−1} would be wrong (the DBL SPLIT-TAIL mass would
inflate it). Every proved and machine-checked surface uses the BOX-7
notion (the battery's dbl_undecided == (q−1)q^{2N−1} rides W-11's
certification-inclusive convention; the HEX3 annex names W-12.C's
bracket quantity U₃^σ; S3.2's lower bound proves lift-DISAGREEMENT,
valid under both notions) — so the theorems stand; only the
conjecture's content shifts with the parse, and the W-12.B bullet
cites neither BOX-7 nor the σ-scoping. c_n(q) IS well-defined through
the BOX-7 pin (given existence, a rational function is determined by
its values at infinitely many prime powers; positivity for the
bullet's "equivalently" clause is supplied in-bullet by S3.3's
c_n ≥ q^{−(n−1)}). *Repair shape:* one clause in the W-12.B bullet
(and/or S1's definition sentence): "undecided(n, q, N) counts the
non-σ-decided members under BOX-7's certification convention — NOT
the conservative-read residue, whose normalized mass diverges at
n = 3 by HEX3.A: the σ-scoping is load-bearing."

### MINOR 1 — the r2 genre-(ii) warrant describes the post-separation residual imprecisely

**Quote (S7, W12-ORACLE bullet, r2 text):** "covered by the disclosed
CONSERVATIVE CONVENTION: the TRP reader follows the double cluster —
once the digits of a and b separate, the residual **at every deeper
state** is (z+ᾱ)²(z+β̄), never all-separable, refining forever on the
exact-square block — and terminates only at v(b₀) ≥ N ⟹ UNDECIDED."

**Classification: minor** (display precision inside an r2-introduced
machine-bracket warrant; the operative claim is true). The residual is
(z+ᾱ)²(z+β̄) (with ᾱ ≠ β̄) at exactly the separation state; at every
DEEPER state the simple root b has peeled off through a polygon vertex
and the refining side's residual is the SQUARE (z+γ̄)² (g = 2) — as
the same sentence's closing clause ("refining forever on the
exact-square block") itself indicates. The substance was re-derived
from scratch this pass in BOTH characteristics: the exact-square block
(x+(c−a))² yields the side residual (z+γ̄)² at every depth (char ≠ 2:
b₁-digit 2γ̄ on the hull gives z²+2γ̄z+γ̄²; char 2 / p = 2: the
b₁-slot is off-hull/zero and z²+γ̄² = (z+γ̄)² by Frobenius), the
pre-separation residual is (z+ᾱ)³, so NO state is all-separable and
the only exit is the window exit — "reader never decides" holds
exactly as claimed. Operationally confirmed with my own reader
(x²(x+14) @ (Zp,2,4), (x−1)²(x−3) @ (Zp,2,5): both TRP-read,
UNDECIDED). *Repair shape:* "the residual at the separation state is
(z+ᾱ)²(z+β̄), and at every deeper state the refining side's residual
is the square (z+γ̄)²".

### Remarks (uncounted, no repair owed)

* R-1: the header and §S10 arc lines are r1-era ("counter 0/2; PE2
  next") under the repo's era-tag convention; the current arc is
  carried by the ANNEX 2 wrapper ("PE2 0C+3G+2m @ 1be15d2 + r2 applied
  above; counter 0/2, PE3 owed") — consistent, dated, no false
  currency claim.
* R-2: §S5/§S9's W2-OPEN-2a display ("narrowed to the Σ-LAW single
  lemma … forward direction at attempt grade GIVEN Σ-LAW") is now
  superseded by Σ-LAW ACCEPTED 2/2 (a27ed68, 12:05Z, after r2) — the
  display is stale in the STRENGTHENING direction only.
* R-3: W-12.B's second conjunct ("the decided window counts are given
  exactly by finitely many q-polynomial laws in the style of clause
  (i)") is informal under the bullet's "stated precisely" header;
  (A1) one clause below is the precise form it gestures at.

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1a) The r2 three-genre disc = 0 disposition — COMPLETE; fourth-genre
hunt NEGATIVE.** Re-proved from scratch: a monic cubic over ℤ with
disc = 0 has a repeated root α; if α were quadratic-irrational, Galois
conjugation preserves the root multiset WITH multiplicity, forcing the
conjugate ᾱ ∈ {α, β} at multiplicity 2 — impossible (β is simple); so
α = a ∈ ℤ (rational root of a monic ℤ-cubic) and β = e₁ − 2a ∈ ℤ.
Hence every disc = 0 member is (x−a)²(x−b) with a, b ∈ ℤ, and the
level-0-read trichotomy {a = b (cube, TRP-read)} ⊔ {a ≠ b, ā = b̄
(TRP-read)} ⊔ {a ≠ b, ā ≠ b̄ (DBL-read)} is logically exhaustive: NO
fourth genre. Genre (i)'s cover cite verified at its fence (W12-L1's
c̄ ≠ d̄, S2.7 — the Hensel split exists exactly there); genres
(ii)/(iii) ride the conservative convention, re-derived (see MINOR 1)
and operationally spot-checked with my own reader — including the r1
window example for the cube genre ((x−4)³ @ (Zp,2,5): v(b₁) = 4
window-visible, b₀ window-hidden ⟹ genuinely outside the S3.2
species, and UNDECIDED). The battery's operational bracket is
independently confirmed by the machine leg (0 disc-0-decided among
41,923 oracle checks).

**(1b) The r(3,N) boundary-tail display — mass RE-DERIVED and
verified on all 23 rows.** From W12-L0 × L1(c) by my own arithmetic:
per center and per w, the history bracket Σ_{H ending at s < w}
(q−1)^t = q^{w−1} (W-11 S2.5's bracket) times the SPLIT-TAIL(w) leaf
count (q−1)q^{N−1−w} gives (q−1)q^{N−2} — w-free; × q(q−1) patterns
× L1(c)'s q^{N−1} simple-branch fiber = (q−1)²q^{2N−2} per w; × the
⌊(N−1)/2⌋ values of w ⟹ ⌊(N−1)/2⌋(q−1)²q^{2N−2}: the r2 display is
exact, factor for factor. Committed-JSON check (my own extraction,
all 23 cubic rows): Σ of SPLIT-TAIL dbl_keys == the mass on every
row; every per-w aggregate == (q−1)²q^{2N−2} with w-range exactly
{1..⌊(N−1)/2⌋}; all six N = 2 rows have ZERO SPLIT-TAIL keys (the
exact-zero clause); the r2 example (Zp,2,5): 256+128+128 = 512
reproduces (the three keys are the history-resolved w = 1, w = 2@(),
w = 2@(1) fibers — 256, 128, 128 from the closed forms). The
"non-(A1)" clause verified: per-w dens would be (q−1)²q^{−N−2},
N-dependent ⟹ in no (A1)-admissible family ⟹ the (A2) routing is
necessary, exactly as displayed. The r2 parenthetical ("no TRP tail
leg is separately owed") checked: TRP tail-certified members are
conv-UNDECIDED by construction, so HEX3's N·q^{2N−1} bound drains
them with the σ-residue — with both annexes, (A2) at n = 3 is fully
covered: (q−1)q^{2N−1} + ⌊(N−1)/2⌋(q−1)²q^{2N−2} + [TRP ≤ N·q^{2N−1}],
all /q^{3N} → 0. ✓

**(1c) The m_i·b_i fix (r2 G3) — SOUND.** ℓ_F integer-valued on P_F
gives m_ib_i = ℓ(x + b_ie_i) − ℓ(x) ∈ ℤ (both points lie in P_F since
the shift stays inside the AP), positive from m_i > 0, b_i ≥ 1;
ℓ(base) = m₀ + Σm_ia_i ∈ ℤ; the Step-1 display consumes exactly these
two (ratio exponents m_ib_i, leading exponent ℓ(base)) — the corrected
clause is precisely what the display needs, and the recorded
counterexample ℓ = (x+1)/2 on 1 + 2ℤ_{≥0} does kill the r1 claim
(m₁ = 1/2) while satisfying the corrected one (m₁b₁ = 1). "Every
in-note P_F has b_i ∈ {1,2}" re-checked (RAM b = 2; 2SIDED, SPLITEQ,
INERTDEEP b = 1; the TRP families b = 1 or 3 — wait: RAM3's
3∤h set is the union (1+3ℤ)∪(2+3ℤ), each leg b = 3 — the clause
"b_i ∈ {1, 2}" is contradicted by RAM3's b = 3 ONLY if the n = 3 menu
is read as "in-note"; the sentence sits in Step 1's n = 2-instance
context where it is true, and for b = 3 the display works identically
(m·b = 2·3 = 6 ∈ ℤ) — no defect, noted for precision.)

**(2) Annex interaction at HEAD — CLEAN; the dated appends claim no
grade they predate.** Timeline verified against git to the second
(all 2026-08-08 UTC): W12 seal 05:33:16 → verdict 05:41:12 → PE1
06:11:16 → r1 07:23:12 → ANNEX 1 07:23:58 → PE2 08:14:16 → [HMENU3
seal 08:40:17, verdict 08:49, adjudication 08:51:40] → r2 + ANNEX 2
09:02:59 → HEX3 PE1 09:17:44 → HMENU3 PE1 09:17:50 → … → W-11
ACCEPTED fold 10:53:59 → Σ-LAW ACCEPTED 12:05:21 → HEX3 r2 12:13:38 →
HMENU3 ACCEPTED fold 12:44:07 → HEX3 PE3 CLEAN 13:50:23. So: ANNEX
1's "HEX3's own hostile arc has not begun" was TRUE at its date AND
still true at the r2 m2 edit that touched the same sentence (HEX3 PE1
landed 14 minutes later); ANNEX 2's "HMENU3's own hostile arc has not
begun" was TRUE at 09:02:59 (HMENU3 PE1 at 09:17:50). Both wrappers
verify their supplier claims against the correct pre-existing commits
(HEX3 e3f3459/671a126/a0290f9 at 06:39/06:46/07:14; HMENU3
64d3ff9/625fa49 at 08:40/08:49 — all < the respective annex dates).
Annex faithfulness at HEAD: both verbatim blocks byte-identical to
their supplier notes (md5 1345d5eff57114c00c98fb2d600a3676 and
4eb3bacc30e3be0bc8a08a72cf9d9473, both sides); the dated line-cites
verified AT their as-of states (HMENU3 @ 625fa49 lines 573–585 and
HEX3 @ a0290f9 lines 516–527 both reproduce the md5s; HEAD line
numbers have shifted with the suppliers' r1/r2 insertions — the cites
are dated, correct). Supplier motion SINCE the annexes is uniformly
STRENGTHENING (W-11 ACCEPTED 2/2 @ 35e6545; HMENU3 ACCEPTED 2/2 @
050425d; HEX3 1/2 with PE3 CLEAN @ fca1a97; Σ-LAW ACCEPTED 2/2 @
a27ed68), and the HEX3 PE1/PE2 findings (H-2(i) ghost-zone display,
r1-fixed; the never-measured census bookkeeping, twice; an S8.2
aside) touch NEITHER HEX3.A nor HEX3.B — the two conclusions this
note's annex consumes — per the HEX3 reports' own "ALL THEOREMS
SURVIVED" records. The annex wrappers' "(attempt 0/2)" grades
under-claim the current state — the safe direction; no surface at
HEAD claims a grade it predates. ANNEX 2's composition claim ("n = 3
conditionality closed at composition grade … conditional exactly on
the arc grades of the W-11/W-12/HEX3/HMENU3 stack") re-derived
mathematically at (1b) above and found complete: (hMenu-3) = HM3.A/B/C
supplies (A0)+(A1)+decided-complement, (hExhaust-3) + the proved DBL
legs supply (A2); the wrapper's own W-12 arc line was current at its
date and remains the note's most recent arc record. No firing
overstatement: no surface claims W-12.D FIRES at n = 3; "fires
unconditionally" remains n = 2-only.

**(3) CONJECTURE W-12.B well-formedness** — FINDING 1 (the σ-pin
seam) + R-3; with the BOX-7 pin, c_n(q) is well-defined (uniqueness
via rational interpolation at infinitely many prime powers; the
"equivalently" clause's c_n ≠ 0 supplied by S3.3 in-bullet; the
suppressed ring-type argument of undecided(n, q, N) is covered by
S1's two-ring convention + "independent of the characteristic").

**(4) The §S5 J-D1 handoff — FAITHFUL at pins.** The (J-D1) block
quoted in §S5 is byte-identical to GRT_WELD_BLUEPRINT_2026-08-08.md
§S2.4 lines 247–255 (verified character-for-character after
blockquote de-prefixing; the only delta is bold markup on the label);
the S0 row quote == blueprint §S3.1 line 302; "execution-order step
(8)" == the blueprint's S6 line ("(8) W-12 as a composition …");
§S5's consumer fence ("the (H1) row's retirement path, then the IFK
faces O-2/O-3 through the GD carriers — consumed DOWNSTREAM, owned by
their own units") matches the blueprint's Consumers line (which
continues "then CU-1..CU-7" — further-downstream units §S5 need not
name). All composition pins re-verified in git: fold 17d2a32, GRTJA
f131c53, GRTJB+GRTJC 83f47f4, GRTW2 adc6cf3, LIFTCORNER 08f61e9,
WELDMASTER 66b3498, OPEN2ATTACK bd82766/4a970aa, DULEMMA
048cf6d/f819f26 (display-only, no count law consumes it — confirmed).
JD0_PROOF at its pin (file untouched since verdict 9387eb1): its own
S6 item 3 reads "W-12 / J-D1 — downstream composition; untouched
here", exactly complementary to §S5's "owning nothing of them" — the
two notes' ownership fences interlock with no gap and no overlap; W-12
takes from J-D1 only (H-c) of [W12-H], and the order-1 layer consumes
none of it (S2's proofs are elementary + classical, as §S5 states).
The composed conditionality ("the union of the six notes' displayed
boxes + the Σ-LAW residue") was correct at composition and is now
conservative (Σ-LAW since accepted — R-2).

**(5) The chosen unmined S3 detail: S3.4's "(A1)-admissible" claim
for the seven TRP families — VERIFIED IN FULL (first display in the
arc).** The conditionality paragraph asserts the S2.4 families' "
parameter sets and laws are q-uniform shifted-product data, so
(A1)-admissible" — asserted, never checked by PE1/PE2. Verified
family-by-family in AP-index coordinates (whole-space dens =
per-center law × q / q^{3N}; ℓ affine with positive INTEGER
coefficients; ν affine; P a finite union of shifted products):
RAM3(h), 3∤h: P = (1+3ℤ_{≥0}) ∪ (2+3ℤ_{≥0}), ℓ = 2h+1, ν = h+1;
3LIN in (m₃, δ₂, δ₁) ∈ (1+ℤ_{≥0})³: ℓ = 6m₃+3δ₂+δ₁+2;
LINRAM2 (u₁ = 2j+1, u₀ = 3j+2+δ): ℓ = 6j+δ+6; RAM2LIN
(u₀ = 3t+2δ+1): ℓ = 6t+3δ+4; VERT1 (u₀ = 3k+1+δ): ℓ = 6k+δ+4;
VERT2 (u₀ = 3t+2δ+2): ℓ = 6t+3δ+6; FULL(k): ℓ = 6k+2 — all
integer-affine with positive coefficients, all parameter sets
shifted-product, pairwise disjoint (distinct exact polygons/λ),
censuses S_λ q-uniform. The raw-coordinate half-integer carries
(LINRAM2's (3u₁+1)/2) integralize exactly in AP-index coordinates,
consistent with the HMENU3 r1-m1 record and with Step 1's [r2]
m_ib_i clause. ✓

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  7dc040d94fbbb1e8d20ac817b665d418 == `git show f669cb0:…` —
  byte-identical to the seal; committed artifacts at HEAD carry §S10's
  md5s (0557b15f… / 05776c9e…).
* **Re-run (single fresh run, this pass):** exit 0, **3,232,506
  checks / 0 violations, teeth 23/23/8/1273**, zero skips, 325.9 s.
  Every §S10 family count reproduced exactly: PIN 5, LVL0 138, SHAPE
  164, QRT 27, L0HIST 306, BLOCK 1,594,670, L1X 1,594,090, DRAIN3
  1,183, ORACLE 41,923; verdict GREEN.
* **Artifacts:** fresh JSON content-identical to committed ex-timing
  (programmatic strip-and-compare == True); output.txt diff = 9
  timing lines; committed bytes restored, md5s re-verified.

## 4. FRESH ROUTE (own arithmetic, no runner imports)

`/tmp/w12_pe3_fresh.py`, written from scratch this pass: own field
tables (GF(2), GF(4) with ω² = ω+1, GF(7)), own rings ℤ/p^N and
F[t]/t^N, own char-safe synthetic Taylor shift, own lower-hull code,
own direct DBL cubic reader (L1(b) mechanics, W12-L0 keys with
histories), own recursive conservative TRP reader (S2.4 taxonomy +
refinement recursion, window-exit-only undecided), own level-0
classifier. Rows DISJOINT from PE1's (cubic Zp(2,4)/Zp(3,3)/Fqt(2,4),
quartic Zp(3,3)/Zp(2,4)) and PE2's (Fqt(3,3), Zp(5,2)): cubic
**(Zp,7,2)** (117,649 cubics), **(Fqt,4,2)**, **(Fqt,2,5)** (32,768,
refinement depth realized); quartic **(Fqt,4,3)** (262,144 stratum
members) — the FIRST prime-power-q fresh route at both degrees.
Results — **pointwise identical to the committed JSON on every
field** (patterns, sep/dbl/trp totals, dbl_undecided, U₃TRP, species,
deep-decided, and the complete depth-0 and DBL key dictionaries):
(Zp,7,2): dblU = 2058 = (q−1)q^{2N−1}, U₃ = 343 = q·u(7,2), species
49 = q^N all undecided, RAM3(1) = 2058 = 6·7²·7; (Fqt,4,2): 192/64/16
with RAM3(1) = 192, RAM(1) = 576 = (q−1)²q³; (Fqt,2,5): 512/608/32
with 96 deep-decided TRP, 10 depth-0 keys and 15 DBL keys (histories
to depth 2) all exact; (Fqt,4,3) quartic: keys 6144/3072/3072 ==
committed == the S2.5 law 4·256·S_λ(4) per λ, wild (2,2) included.
Each value also re-derived from the S2.4/S2.5/W12-L0 closed forms by
hand. Bonus operational checks: the three r2 genre exemplars read
UNDECIDED by my own reader (§2(1a)).

## 5. ARC / COUNTER

Arc: composed 0/2 → PE1 1C+3G+2m (2b47711) → r1 (ba0d1a4) + HEX3
annex (8e535d2) → PE2 0C+3G+2m (1be15d2) → r2 + HMENU3 annex
(99f1813) → **PE3 (this pass): NOT CLEAN — 0 CRITICAL +
1 JUSTIFICATION GAP + 1 minor; counter stays 0/2; r3 owed.** Both
findings are display-level, one-to-two-sentence repairs (the W-12.B
σ-pin clause; the genre-(ii) per-state residual wording); no theorem
statement, no proved chain, and neither annex is touched. The machine
and fresh legs are arc facts for the record: seal intact, battery
GREEN and reproducible a third time, the instance layer independently
confirmed on four never-fresh-routed rows including the first
prime-power-q rows at both degrees.

— passPE3 verifier, fresh context, 2026-08-08.
