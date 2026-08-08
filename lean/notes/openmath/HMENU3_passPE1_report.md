# HMENU3 passPE1 report — hostile verification of HMENU3_PROOF_2026-08-08.md

**Pass:** PE1 (first hostile arc on the (hMenu-3) discharge note; fresh context;
verifier fixes nothing, quotes and classifies). **Target:**
`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md` at HEAD (seal 64d3ff9, verdict
625fa49). Fences, boxes, and the §S8.1 annex drafts treated as part of the
statement. **Date:** 2026-08-08.

## VERDICT LINE

**NOT CLEAN — 0 CRITICAL + 1 GAP + 1 MINOR.** Every mathematical charge
CONFIRMS the note: LEMMA HM3-1's two-phase classification re-derived and
exhaustive (no third species found; the hunt is documented below), 11 family
counts re-derived from scratch across all three tiers with disjointness
surviving adversarial probing, the five R_τ(q) re-assembled by a fully
independent symbolic summation (Σ = 1 exact; q = 2, 3 numerics exact; engine
β(2)/β(3) tie exact), §S5.4 re-derived SOUND (the discharge does not need
U₃^σ), the annex drafts do not overstate, and q-uniformity spot-checked at 74
committed keys across 3 families in both characteristics. The machine leg is
bit-clean: runner byte-identical to the seal, fresh full run GREEN
183,387/0 with teeth 21/15/10/4, artifacts content-identical ex-timing, and an
independent fresh-route reader (own arithmetic, no runner imports) reproduces
the committed tallies KEY-FOR-KEY on 6 rows / 113,838 states. The two findings
are conditionality-display defects, not mathematical errors; repair is
sentence-level.

---

## FINDINGS

### FINDING 1 — GAP (stale supplier-arc display in the conditionality sentence)

**Quotes.** §S9 bullet 1: "THEOREM W-12.D @ w12 seal f669cb0 / verdict c16c717
/ adjudication 97122f2 / r1 repair ba0d1a4 (arc 0/2, PE1 adjudicated, **PE2
owed**)". HM3-BOX-2: "W-12's own PE arc (r1 done, **PE2 owed**)". §S10:
"conditional exactly on the displayed arc grades (**W-12 PE2 owed**; HEX3 and
this note's hostile arcs unbegun)". COROLLARY HM3.D header: "W-12.D as proved
@ its **0/2-post-r1 arc**".

**Defect.** W-12's PE2 was NOT owed at seal time: the W12 passPE2 report
landed at commit 1be15d2 (2026-08-08 08:14:16Z), 26 minutes BEFORE the HMENU3
seal 64d3ff9 (08:40:17Z) and 37 minutes before the verdict commit. Its verdict
was **NOT CLEAN — 0 CRITICAL + 3 GAPS + 2 minor, r2 owed**. The note's
conditionality display (the exact thing the corollary says it is conditional
on) therefore misdescribes the supplier state: the true W-12 arc state was
"PE2 ran NOT CLEAN (0C + 3G + 2m); r2 owed", not "PE2 owed".

**Why this is a gap, not a critical.** The counter stays 0/2 (PE2 found no
critical), so no grade is inflated; and I checked each of the three W12-PE2
gaps against the clauses HM3.D actually fires: gap (1) (the a ≡ b (mod p)
disc-0 sub-genre read TRP outside W12-L1's c̄ ≠ d̄ fence) concerns disc-0
members and fence wording — the level-0-type partition used by HM3.C is
unaffected; gap (2) ((hExhaust-3) gloss undercounting (A2)'s n = 3 residue by
the transported DBL SPLIT-TAIL boundary leg) is **exactly the leg this note's
S5.3 displays explicitly** — HMENU3 already carries the missing mass in its
r(N); gap (3) ([r1 m1]'s false integrality implication) — the fact W-12.D
Step 1 needs (m_i·b_i ∈ ℤ) does hold for every family here (see FINDING 2).
So no fired clause is touched; the defect is the accuracy of the
conditionality record itself.

**Repair shape (for the composer, not executed here):** update the four
quoted sites to "PE2 ran NOT CLEAN (0C+3G+2m) @ 1be15d2; r2 owed", and note
that S5.3 discharges W12-PE2 gap (2)'s displayed leg.

### FINDING 2 — MINOR (integer-coefficient claim in HM3.B's admissibility clause is raw-coordinate false)

**Quote.** THEOREM HM3.B: "exponent ℓ affine with strictly positive integer
coefficients (m carries 5, k/t carry ≥ 3, **w/j/u/k′ carry ≥ 1**)".

**Defect.** In the raw parameter u (RAM-leaf families: DBL-RAM, B1/B2/B3-RAM,
and likewise u₁ in LINRAM2/DEEP-LINRAM2), the exponent carries u with
coefficient **3/2**, not an integer: e.g. B2-RAM(m,k,w;u) has ℓ = 5m + 6k +
w + (3u+1)/2 + 4. The claim is true only in AP-index coordinates (u = 2i−1
gives carry 3). This is the same seam as W12-PE2's gap (3): W-12.D Step 1's
[r1 m1] guard requires only m_i·b_i ∈ ℤ, which holds here (3/2 · 2 = 3) — so
(A1)-admissibility and the geometric-series step are unaffected, and my
independent summation (below) confirms every resulting series. Display-level
imprecision only.

**No further findings.** Everything else checked out; the records follow.

---

## CHARGE 1 — LEMMA HM3-1 exhaustiveness (the two-phase chain), re-derived

**Own derivation of (iii), the load-bearing phase-flip.** Post-β, write the
recentered cubic as (x² + A₁x + A₀)(x − ρ̃) with the split root at
v(ρ̃) = m exactly and cluster roots strictly deeper, so v(A₁) ≥ m+1 and
v(A₀) ≥ 2m+1. Then: v(a₂) = v(A₁ − ρ̃) = **m exactly**;
v(a₁) = v(A₀ − ρ̃A₁) ≥ 2m+1; v(a₀) = m + v(A₀) ≥ 3m+1. The segment
(2,m)–(3,0) extended to abscissa 1 has height 2m < 2m+1 ≤ v(a₁) and to
abscissa 0 height 3m < 3m+1 ≤ v(a₀): the polygon has a GENUINE vertex at
(2, m) with rightmost side of length 1 (e = 1, g = 1) at every post-β frame.
Every later recentering has raw depth m + k′ ≥ m+1, so v(center − r_split)
stays m: the vertex persists. Consequences, each checked against the species
definitions: (α) and (β1) need one full side of length 3 — impossible; (β2)
needs vertex at 1 ONLY with a length-2 right side — impossible; the only
repeat-capable configuration left is the length-2 LEFT side with e = 1, g = 2
and repeated residual = the block-refine step ('VERT2', ·, m); e ≥ 2 sides at
n = 3 have g = 1 (the W-12 [r1 F3] point) and cannot repeat; the possible
a₁-cancellation (v(A₀) = m + v(A₁)) sits in digits the hull/residual never
consults, exactly W12-L1(b)'s computation at the σ_m-scaled pattern where
ρ̃/π^m is a unit. **Third-species hunt (all negative):** β-then-α re-entry —
blocked by the persistent vertex; β-then-β1/β2 — same; a second split
(cluster splitting into two simple roots) — that is the block 2SIDED/SPLITEQ
leaf, decided, not a new node; char-3 α degeneration ((y−z)³ = y³ − z³, pins
(0,0,−z³)) — still one pinned triple per letter, and char-3 β1 has c₂ =
z − z′ ≠ 0 so α/β1 stay disjoint; char-2 β2 pins (0, z²) — z ↦ z² injective;
repeated root at z = 0 — impossible (residual constant terms are exact-
valuation digits ≠ 0). **Machine corroboration (own scan):** all 1,031
realized keys across the 41 committed rows obey the two-phase grammar — 0
ALPHA/FULL11SQ/VERT1-steps after a β event, every post-β block-refine step
carries the split depth (t = m) exactly, post-β leaves are exactly the
dictionary leaves {RAM2LIN, 3LIN, VERT2(λ), DRAIN}. **CONFIRMED.**

**Dictionary re-derivation (S1/HM3.A).** Independently recomputed all six
dictionary lines from the vertex-at-(2,m) frame: block refine at k′ ↦
('VERT2', 3m+2k′, m) (u₀ = v(a₀) = 3m + 2k′, parity even ✓, j = k′ ✓);
RAM(u) ↦ ('RAM2LIN', 3m+u, m) (u₀ − t = 2m + u odd ⟺ u odd ✓); 2SIDED(w,
u−w) ↦ ('3LIN', m+(u−w), m+w, m) ✓; SPLITEQ/INERTDEEP(k′) ↦ ('VERT2',
3m+2k′, m, λ) ✓; σ-column: {(2,1)}⊎{(1,1)} = RAM2LIN's σ, {(1,1)²}⊎{(1,1)} =
3LIN's, {(1,1)²/(1,2)}⊎{(1,1)} = VERT2(λ)'s ✓ — the dictionary leaf's own
shape σ equals σ_block ⊎ {(1,1)} in all four cases. **CONFIRMED.**

## CHARGE 2 — the 33-family menu: 11 counts re-derived from scratch; disjointness probed

Re-derived by hand (digit-slot arithmetic from W-12 S2.2/S2.4 conventions +
W12-L0 + the W-11 bracket), then checked against committed enumeration:

1. **SEP censuses** (tier SEP): C₀ = q(q−1)(q−2)/6, q²(q−1)/2, (q³−q)/3; sum
   q²(q−1) ⟹ SEP density (q−1)/q exactly.
2. **A_RAM(u) = (q−1)q^{2M−u−2}** (DBL tier): W12-L0 RAM(u)@H law
   (q−1)q^{M−1−u}q^{M−(u+1)/2}, s-independent on u ≥ 2s+1, × bracket
   q^{(u−1)/2}. Independent match.
3. **A_2SIDED = (q−1)²q^{2M−u−3}** (× bracket q^{w₁−1}). Match.
4. **A_SPLITEQ = ((q−1)(q−2)/2)q^{2M−2k′−3}**. Match.
5. **A_INERTDEEP = (q(q−1)/2)q^{2M−2k′−3}**. Match. (2–5 sum to q^{−2}·q^{2M}
   exactly — the n = 2 menu is density-exhaustive, re-derived.)
6. **TRP-RAM3(h) = (q−1)q^{3N−2h−2}** (tier I): (q−1)q^{N−1−h} ×
   q^{N−⌈2h/3⌉} × q^{N−⌈h/3⌉} with ⌈2h/3⌉+⌈h/3⌉ = h+1 for 3∤h.
7. **DEEP-RAM3(m,h) = (q−1)²q^{3N−5m−2h−3}** (tier II, deep-α): bracket ×
   window-(N−3m) law; h is the REDUCED parameter (raw leaf field = h + 3m).
   Verified against all four committed never-measured spots: (Fqt,2,9)
   (('ALPHA',1),('RAM3',4)) = 131,072 and (('ALPHA',1),('RAM3',5)) = 32,768;
   (Fqt,3,6) (('ALPHA',1),('RAM3',4)) = 26,244 — hand arithmetic.
8. **B2-RAM key law** (β-composite): (q−1)²q^{3k+M−1−w}·L0(RAM(u)@(); M) —
   33 committed keys matched at (2,7)/(2,9)/(3,5)/(3,6), both characteristics
   (incl. the never-measured spot (('VERT1',4,1),('RAM2LIN',4,1)) = 65,536 at
   (Fqt,2,9) and 17,496 at (Fqt,3,6), by hand).
9. **B3 key law** (β3): (q−1)q^{3t+M−1} × [(q−1)·instance-RAM(u), the
   (j)-started L0 bracket] — 8 committed VERT2-step keys matched; my
   independent constrained-bracket derivation Σ_{H: k₁=j}(q−1)^t =
   (q−1)q^{s_max−j} reproduces all four A^{(j)}_L displays, including the
   ranges u ≥ 2j+1, w₁ ≥ j+1, k′ ≥ j+1.
10. **B1 prefactor (q−1)(q−2)q^{3k+M−1}** from the HM3-3 β1 fiber; the q = 2
    exact zero confirmed (no FULL11SQ key exists on any q = 2 row — checked).
11. **LEMMA HM3-4 bracket (q−1)q^{4m−1}**: re-derived by generating function
    (A₁/(1−A₁) with 1−A₁ = (1−q⁴x)/(1−q³x)) AND checked composition-by-
    composition at m = 2 against committed enumeration at (Zp/Fqt,2,9): comp
    (1,1) = 2,048 + comp (2) = 2,048 = 4,096 = b(2)·RAM3(1)@M=3 for h_red = 1
    (and 512+512 = 1,024 for h_red = 2), each composition individually at its
    Π(q−1)q^{3k_i} law.

**Also re-derived:** the deep-LINRAM2 shear (raw ('LINRAM2',5,3) at m = 1 ⟹
window (2,1): u₀-shift +3m, vertex-height shift +2m) — committed spot 32,768
at (Fqt,2,9) and 5,832 at (Fqt,3,6) both reproduced by hand. This exercises
S3.1's three shear rules on a committed value.

**Disjointness, adversarial.** Hunted for a state two families could both
claim: (a) tier boundaries — depth-0 ('RAM3',h) vs deep (('ALPHA',1),
('RAM3',h′)): distinct keys, and the deterministic read gives each state one
chain record; a depth-0 RAM3 frame (3∤u₀) is never an α frame (3|u₀) — the
first-frame partition (H-1) is exclusive by case. (b) Step-vs-leaf symbol
collision: ('VERT2',u₀,t) steps have arity 3, ('VERT2',u₀,t,λ) leaves arity 4
— no tuple collision; same for VERT1. (c) β3-step keys vs β1/β2-route keys
containing deep ('VERT2',·,·) block-refine steps: first entries differ.
(d) Parameter-recovery injectivity: from a B2 raw key, (m from the ALPHA
prefix + step's own depth field, w = u₀_raw − 3m, u = leaf field − 3m) is
uniquely recoverable — checked as the exact arithmetic my 74-key spot check
used; different (m,k,w) fibers have disjoint key sets. (e) Cross-stratum:
level-0 factorization type separates SEP/DBL/TRP (the W12-PE2 gap-1 disc-0
sub-genre lands in TRP by its level-0 type — no double claim). (f) Aggregate
double-counting: aggregation collects raw-key fibers of a partition; the
both-directions MENU+AGG machine checks (1,031 + 707, 0 violations) would
surface any collision as a count mismatch. **No overlapping pair found.**

## CHARGE 3 — COROLLARY HM3.D re-derived by independent symbolic assembly

Own sympy summation (`/tmp/hmenu3_pe1/rtau_independent.py`, no runner code):
directly summed MY re-derived family laws — SEP censuses; DBL = (q−1)·Σa_L;
TRP per-center = amp·(Group I sums) + Σ_m b(m)q^{−9m} × {B1/B2/B3 with my
constrained-bracket A^{(j)}} — with every geometric series done by sympy from
the raw parameter ranges (u odd, 3∤h, w₁ < w₂, u₀ > 3k parity-split, etc.).
Results:

* amplifier Σ b(m)q^{−9m} = (q⁶−1)/(q⁶−q) ✓; per-center TRP total = q^{−3}
  EXACTLY ✓; β3/β-route ratio Σ_j a^{(j)}_L = (q−1)/(q³−1)·Σ a_L verified for
  ALL FOUR L (the note's β_τ collector is right for the same reason).
* **All five R_τ match the displayed closed forms symbolically**, Σ_τ R_τ = 1
  exactly, and E[#roots] = 3R_split + R_12 + R_21 = q/(q+1) exactly.
* q = 2: (4/93, 28/93, 8/31, 22/93, 5/31); q = 3: (63/968, 351/968, 36/121,
  93/484, 10/121) — both vectors exactly as displayed.
* **Engine tie:** with T_τ := (R_τ − SEP_τ − DBL_τ)/q from MY assembly,
  q³·T_τ = om_density_engine β₃(τ) for all five τ, and DBL_τ =
  (q−1)·β₂(block)/q² for all three block types — the monic assembly identity
  holds term for term; Σβ₃ = Σβ₂ = 1 checked. The exploratory line R_τ =
  q³β₃(τ) verified to hold exactly for the three unramified types and to FAIL
  for (2,1),(1,1) and (3,1) — matching the note's scoping.
* The S5.5 intermediate displays re-derived: block densities (1/(q(q+1)),
  1/(q³(q+1)), (q−2)/(2q³(q+1)), 1/(2q²(q+1))), total q^{−2}.

**Conditionality sentence:** the arc-grade LIST (W-12.D, W-11, W-12.A/C +
L0/L1, HEX3, this note) is the right set — nothing consumed is missing from
S9 and nothing in S9 is unconsumed (the NOT-consumed list correctly excludes
the weld notes, measure route, htameFE, tail-σ-certification). But the W-12
grade DESCRIPTION is stale — FINDING 1.

**S5.3 bound re-checked:** term-by-term r(N) ≤ ((N−1)/2 + 1 + N/2)·q^{2N} =
(N + 1/2)·q^{2N} ≤ (N+2)q^{2N} ✓; exactness of the three complement legs
(DBL SPLIT-TAIL aggregate ⌊(N−1)/2⌋(q−1)q^{N−2}, DBL UNDECIDED q^{N−1}, TRP
q·u) re-derived from W12-L0 + HEX3.A. ✓

## CHARGE 4 — §S5.4 (why HEX3-BOX-1 does not bite), re-derived

Checked against THEOREM W-12.D's verbatim statement (W12_PROOF §S1(iii)):
(A0) is quantified over "every window-decided member of a core family" ONLY;
(A2) DEFINES r(N) := q^{nN} − Σ visible core counts ("the σ-undecided residue
AND any window-boundary (tail) families" route through it with no
σ-labeling). Re-walked Steps 1–4: Step 4's upper bound μ_τ ≤ (D_τ(N) +
r(N))/q^{nN} charges the whole residue to EVERY τ simultaneously — no σ-label
on residue members is consulted anywhere. Since every core-menu member here
is conservative-DECIDED (all consulted digits in-window, separable residuals
⟹ Ore certifies every disc ≠ 0 lift at the terminal frame of the read OF f
ITSELF — the transports are analysis devices, the actual chain is
recenterings of f), the reduction consumes exactly {(A1) exact + disjoint,
(A0) on the menu, r(N) → 0} — all delivered. The exact U₃^σ law is needed
only for the exact σ-residue (HEX3-BOX-1's own charge), not for W-12.D.
**S5.4 SOUND — the discharge stands without the tail-σ-certification lemma.**
(Consistent with W12-passPE2's headline conv-vs-σ seam check, which ran
CLEAN.)

## CHARGE 5 — §S8.1 annex drafts

The BOX-2 annex claims exactly what HM3.A/B/C + the battery deliver, carries
the honest grade ("DISCHARGED at composition grade (attempt 0/2)"), and its
conditionality clause ("conditional exactly on the arc grades of
W-11/W-12/HEX3/HMENU3") points at the grades without restating them — it does
not overstate, though a reader resolving those grades through S9 inherits
FINDING 1's staleness. The HEX3 pointer annex is accurate: HEX3-BOX-1
untouched, off the critical path per S5.4 (verified above). The one-decided-
key q = 27 claim, the never-measured spot claims, and "PARI σ-leg on 9,952
deep members" all match the artifacts. **No overstatement.**

## CHARGE 6 — q-uniformity spot-checks (committed JSONs, both characteristics)

Full menu tallies are Zp/Fqt-IDENTICAL (every key, every count) at all four
probed shared pairs (2,7), (3,5), (2,9), (3,6). Three families' polynomial
identities evaluated BY MY OWN arithmetic and matched at **74 committed
keys**: DEEP-RAM3 (18 keys), B2 VERT1→RAM2LIN (48 keys), B3 VERT2→RAM2LIN
(8 keys) — every count = the single q-polynomial law at both ℤ_p and
𝔽_q[[t]], q ∈ {2,3}, including wild p = 2/p = 3 strata (deep-RAM3 at p = 3 =
wild totally ramified behind a refinement; RAM2LIN legs at p = 2).

## MACHINE LEG

* **Runner vs seal:** `git diff 64d3ff9 HEAD -- verification/openmath/
  hmenu3_checks.py` EMPTY; md5 65326f85c218087261f434f8b8cc8dda.
* **Fresh full run** (isolated copy in /tmp, committed inputs): exit 0,
  **GREEN, 448.4 s**, single run. Family counts BIT-IDENTICAL to the verdict
  section: PIN 7/0, MENU 1,031/0, DRAIN 82/0, AGG 707/0, XREAD 171,444/0,
  HEX3TIE 38/0, W12TIE 69/0, DBLTIE 23/0, ORACLE 9,956/0, RTAU 30/0 — total
  183,387/0; teeth 21/15/10/4 all exactly preregistered; artifacts
  content-identical to the committed ones EX-TIMING (structural JSON compare
  = True; committed md5s 7f754887…/daf077d0… reproduced up to elapsed
  fields). Verdict-section arithmetic audited: check total 183,387 ✓, 41 rows
  = 18 ℤ_p + 23 𝔽_q[[t]] ✓, Σ states = 94,824,902 recomputed exactly ✓,
  9,952 = 48+624+6,688+2,592 ✓.
* **Fresh route (no runner imports):** wrote an independent reader
  (`/tmp/hmenu3_pe1/fresh_reader.py`) — own ring arithmetic for ℤ/p^N AND
  F_p[t]/t^N, own lower-hull, own residual factorization (brute-force,
  characteristic-free), own recentering (b₀,b₁,b₂ update by f(x+s)), raw-key
  recording per the S1 spec. Enumerated 6 rows / **113,838 states**:
  (Zp,2,5), (Fqt,2,5), (Zp,3,4), (Fqt,3,4), (Zp,2,6), (Fqt,2,6) — the full
  key histogram equals the committed `menu_tally` **key-for-key on every
  row** (15/15, 9/9, 29/29 keys; deep members 48 and 624 at q = 2 N = 5/6
  included), which independently validates the reader convention, the
  partition, the DRAIN totals, and characteristic-independence at these
  rows. This exceeds the required ≥ 2 families at ≥ 2 (q,N): it is every
  family at 3 (q,N) pairs in both characteristics.

## SCORE AGAINST THE NOTE'S OWN FALSIFIER MAP (P-10)

No falsifier fired on my legs either: no MENU/AGG discrepancy (so HM3-4 and
the A_L aggregations stand), no law violation at the committed spots, no
σ anomaly, engine tie exact. The two findings are outside P-10's map —
conditionality-record accuracy (FINDING 1) and a display quantifier
(FINDING 2).

## COUNTER

PE1: **0 critical / 1 gap / 1 minor.** 2-clean acceptance counter for this
note: **0/2** (this pass is not clean; sentence-level repair then PE2).
