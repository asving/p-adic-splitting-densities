# W12 passPE5 report — hostile verification pass 5 (fresh context) of W12_PROOF_2026-08-08.md

**Target:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` at HEAD = post-r4
(**d2d91b7** + **5728258**). Read first: all four prior reports (PE1 2b47711,
PE2 1be15d2, PE3 c9c5c0e, PE4 26689da), all four repair diffs (r1 ba0d1a4,
r2 99f1813, r3 b17238a, r4 d2d91b7+5728258), both dated annexes, the r4
adjudication (455a2ec), and the supplier notes at the pins the [r4] FIRING
CHECK cites (W-11, HMENU3, GENH4, GENHN). This pass fixes nothing; it quotes
and classifies. Fences/boxes/annexes/repair-records are read as part of the
statement. Charge-designated veins: (1) the r4 witness repair — both lifts'
separability and valuation structure RE-DERIVED here in mixed, equal-2 and
equal-3 characteristic, plus the parity bracket; (2) the (A1) σ-labeling
clause as now worded (exactly what Step 4 consumes? necessity? the four
firing citations at their pins); (3) the [r4]-superseded arc markers;
(4) the full box inventory + conditionality-stack summaries; (5) one unmined
vein (chosen: S2.6 LEMMA W12-L0 and S2.7 LEMMA W12-L1). Draft kept at
/tmp/w12_pe5_draft.md; fresh instruments /tmp/w12_pe5_fresh.py,
/tmp/w12_pe5_fresh2.py, /tmp/pe5_sym.py.

**VERDICT: NOT CLEAN — 0 CRITICAL + 1 JUSTIFICATION GAP + 3 minor
(+ 4 uncounted remarks).**

**THE r4 WITNESS REPAIR IS CORRECT — re-derived from scratch, all three
characteristics** (charge 1, the headline check). I did not re-read the
repair's displayed checks; I recomputed them. disc F_A = (B²−4π^{2K+1})·
π^{2(2K+1)} with v(B²) = 2t exactly (equal char 2: the 4-term vanishes;
otherwise v(4π^{2K+1}) ≥ 2K+1 ≥ 2t+2 > 2t); the two Hensel roots come out at
valuations t and 2K+1−t with unit derivatives u and −u at z ≡ 0, −u;
disc F_B = −4B³π^L − 27π^{2L} is the correct specialization of the general
cubic discriminant 18abc−4a³c+a²b²−4b³−27c² and is a unit times π^{2L} in
equal char 2, a unit times B³π^L in equal char 3, of valuation 3t+L in equal
char ≥ 5 and in mixed characteristic p ≥ 3; the three gcd(F_B, F_B′) legs are
right, including F_B(−2B/3) = (4/27)B³ + π^L ≠ 0 at p ≥ 5; g′(−u) = 3u²−2u² =
u² is a unit as an IDENTITY, not a case split; and the complementary quadratic
of F_B has v(a) = v(b) = L−3t > 0 (from the coefficient identities), which is
exactly what makes its e = 2 block separable in char 2. **The parity bracket
fully cures the degeneracy:** L ≥ 3N with L−N odd forces L ≠ 3N (L−N = 2N is
even), hence L ≥ 3N+1 > 3N = 3t, and L = 3N+1 is always admissible at t = N
(L−N = 2N+1 is odd for every N); I re-checked EVERY t-dependent constraint at
t = N (2K+1 ≥ max(N, 2N+2); 2t < 2K+1; L−3t = 1 odd; the mod-π^N congruence
with B = π^N; the count q·q^{N−1}) and found no residual degeneracy. The
note's own scoping of the deleted branches is exactly right: B = 0 kills
Lift 1 only in equal char 2 and Lift 2 only in equal char 3 — at equal char
p ≥ 5 **both** sealed witnesses are fine, which I verified.

**THE GAP is the r4 MINOR-2 repair's own blast radius:** the [r4] FIRING
CHECK's n = 3 row (the load-bearing new artifact of the F2 repair) vouches
"**SUPPLIED VERBATIM** … which is precisely the clause" for HM3.C's sentence
"so Ore certifies **EVERY lift**" — which is the identical over-claim that the
SAME repair struck from this note's S2.3 as FALSE in equal characteristic at
wild decided shapes, and HM3.C cites that very S2.3 as its warrant. The
needed clause (disc ≠ 0 lifts) is true and provable, so no conclusion moves;
but the firing row rests on a false supplier sentence, and r4 recorded no
blast-radius sweep for m2. **Three minors:** S3.4's Step-4 UPPER bound and
its closing "No other conditionality" sentence still cite (A0) alone — the
hypothesis the F2 record itself demotes to a tautology/restatement — while
only the F2 record's Step-4 re-check routes through the new clause; the note's
HEADER still carries the r1-era arc ("r1 THIS REPAIR … PE2 next") unmarked,
although r4 explicitly marked the two other stale arc displays superseded; and
three surfaces still describe the runner's 85 oracle witness pairs as built
"per the S3.2 proof", which post-r4 is false for 15 of them.

**Everything else checked CLEAN.** The σ-labeling clause is exactly what
Step 4 consumes (no more, no less) and its degenerate-instance bracket
correctly establishes necessity (re-verified, including that the failing
clause is precisely the μ_τ tie and not Σ_τ R_τ = 1); W-11(i)'s σ column and
the (iii) partition are verbatim as cited, and I re-derived the n = 2 clause
family-by-family including equal characteristic 2 where disc = A₁²;
GENH4.C/GENHN.C are correctly restricted to disc ≠ 0 lifts; the box inventory
is complete (all 8 W12 boxes + [W12-H]'s five members + both annexes, no
dangling reference); and LEMMA W12-L0 / LEMMA W12-L1 survive a full
re-derivation, with all six W12-L0 rows aggregating EXACTLY to W-11(ii).
**Machine leg:** runner md5 == seal f669cb0, fresh full run exit 0 GREEN
**3,232,506 / 0**, teeth 23/23/8/1273, every family count == §S10, artifacts
content-identical ex-timing, committed bytes restored. **Fresh route (new to
the arc): equal characteristic p ≥ 5.** Own arithmetic verified the repaired
witness pair over F_p[[t]] for p = 2,3,5,7,11,13 and over ℤ_p for
p = 2,3,5,7,11; own readers reproduced the S2.4 laws, W12-L0's
history-resolved laws, the DBL term and HEX3.A on five equal-characteristic
p ≥ 5 rows including **(F_q[[t]], 5, 4)** — the first row anywhere in the arc
that exercises HEX3.A's N-linear regime at p ≥ 5 — and tie pointwise to the
committed JSON at (Fqt,5,2), (Zp,5,2) and (Zp,7,2). A symbolic leg confirmed
all seven n = 2 series identities and the six W12-L0 → W-11(ii) aggregations
exactly in q. **Counter stays 0/2; r5 owed.**

---

## 1. FINDINGS

### FINDING 1 — JUSTIFICATION GAP: the [r4] FIRING CHECK's n = 3 row vouches "SUPPLIED VERBATIM … precisely the clause" for HM3.C's "Ore certifies EVERY lift", the exact over-claim the same repair struck from S2.3 as FALSE in equal characteristic; the m2 blast radius was never swept

**Quotes.** [r4] FIRING CHECK, n = 3 row (note L431):

> | **n = 3** (HMENU3 COROLLARY HM3.D) | the 33-family cubic core menu … |
> **SUPPLIED VERBATIM.** THEOREM HM3.C: "(A0): every menu member is
> conservative-DECIDED — all consulted data in-window with separable
> residuals — **so Ore certifies EVERY lift** (W-12 S2.3 at the terminal
> frame; W12-L1(c) transports the DBL certificates); **σ_F = the leaf
> table**" — i.e. decidedness for every member AND the label identification,
> **which is precisely the clause** |

The quotation is byte-faithful (HMENU3_PROOF_2026-08-08.md L216–219 carries
exactly those words). And the SAME repair, at S2.3 (note L594–604):

> and (A0)-strongly (every disc ≠ 0 lift has this σ ~~— in fact every
> lift~~ **[r4, PE4 m2: the struck parenthetical is FALSE in equal
> characteristic at wild decided shapes … a TRP-RAM3(h) member with 3∤h
> whose b₁, b₂ vanish in-window admits the lift F = y³ + b₀ with v(b₀) = h,
> and in equal characteristic 3 that lift has F′ ≡ 0, hence disc = 0 and no
> σ at all …]**

**Classification: JUSTIFICATION GAP** (the genre of PE2's FINDING 3: true
conclusion, wrong warrant). The clause (A1) now needs is "every member of
every core class is σ-DECIDED … with forced σ = σ_F", i.e. a statement about
**disc ≠ 0** lifts. HM3.C's sentence asserts the strictly stronger "Ore
certifies EVERY lift" — and that stronger sentence is FALSE in HM3.C's own
menu: TRP-RAM3(1) is one of the seven depth-0 TRP families HM3.B aggregates,
its members with b₂ = b₁ = 0 in-window and v(b₀) = 1 exist at every window
N ≥ 2, and over F_q[[t]] with p = 3 the lift F = y³ + b₀ has F′ ≡ 0, disc = 0
and no σ — so Ore certifies it for no σ at all. Three consequences, stated
exactly:

1. The row's warrant is an over-claim. What is true and needed — every
   disc ≠ 0 lift has the leaf label — follows from S2.3 POST-r4 (the
   surviving, correctly restricted clause), so **the n = 3 firing survives**;
   the note's evidence for it, as displayed, does not.
2. It is an internal inconsistency of a single repair: r4 struck the sentence
   in its own S2.3 and, in the same commit, quoted the identical sentence
   approvingly as the supplier's supply. Note also the direction of the
   citation chain: HM3.C's warrant for its sentence IS "W-12 S2.3 at the
   terminal frame" — i.e. HM3.C inherited the defect from the pre-r4 S2.3
   text.
3. No blast-radius sweep for m2 is recorded anywhere in r4 (contrast r2,
   which recorded a consuming-surface sweep for its F1, and r3's ~40-surface
   σ-sweep). At least one downstream note (HMENU3, THEOREM HM3.C — a
   THEOREM statement, at 0/2) carries the identical over-claim uncorrected
   and unnotified.

*Repair shape (one clause + one line):* in the n = 3 row, "SUPPLIED, modulo
the same 'every lift' over-claim this repair's MINOR 2 struck in S2.3: what
HM3.C needs and what S2.3 proves is the disc ≠ 0 restriction, which is
exactly the clause"; plus an m2 blast-radius line naming HMENU3 HM3.C (and
any other surface asserting all-lift certification) as inheriting the struck
sentence.

### MINOR 1 — S3.4's Step-4 UPPER bound and its "No other conditionality" close still cite (A0) alone; only the F2 record's re-check routes through the new clause

**Quotes.** S3.4 Step 4, lower bound (repaired in situ at L1026–1031) vs
upper bound, one sentence later (L1031–1035):

> Upper bound: a type-τ F with disc ≠ 0 truncates into SOME window-N class —
> either a visible core class, which is then necessarily a τ one (**by (A0)
> applied to F itself**: F is a disc ≠ 0 lift of its own truncation), or into
> the rest

and S3.4's close (L1092–1093): "**No other conditionality: (A0) at the
order-1 decided shapes is S2.3's Ore argument.**"

**Classification: minor** (display; the note contains the correct derivation
in the same repair). Under the r3 pin, (A0) read as the member's own forced σ
is the tautology the F2 record itself diagnoses; read with r4's new gloss
("the read's type" = σ_F) it is conditioned on "every **window-decided**
member", so applying it at F's truncation still needs that truncation to be
decided — which now comes from (A1)'s clause, not from (A0). The F2 record's
STEP-4 RE-CHECK does this correctly ("… because F is a disc ≠ 0 lift of its
own truncation and the clause says every such lift has type σ_F — same
clause, applied at F"), and the note's clause-vs-(A0) redundancy is honest.
So the defect is that r4 bracketed the lower bound at its site and left the
upper bound and the conditionality close pointing at the demoted hypothesis:
a reader of §S3 alone gets the pre-r4 warrant. *Repair: two pointers.*

### MINOR 2 — the note's HEADER still carries the r1-era arc, unmarked, while r4 marked the two other stale arc displays superseded

**Quote (L5–8):**

> **Attempt grade 0/2** (arc: composed → PE1 NOT CLEAN 1C+3G+2m @ 2b47711 →
> **r1 THIS REPAIR**, note-only, [r1] tags, minimality contract — F1
> (CRITICAL, W-12.A display) + F2/F3/F4 + m1/m2 repaired in place; counter
> 0/2; **PE2 next**).

**Classification: minor** (record hygiene, at the note's most prominent
site). At HEAD the arc record has four displays: this header (r1-era,
unmarked), §S10's "**[r1] ARC (superseded — the CURRENT arc is the [r4] ARC
at the end of this note)**", the tail "**[r3] ARC (superseded by the [r4] ARC
below)**", and "**[r4] ARC (CURRENT …) … PE5 next**". So there is exactly one
CURRENT display, but the header is a live unqualified contradiction of it
("r1 THIS REPAIR"; "PE2 next"), and it is stale by three repairs. PE3's
remark R-1 excused this under "the repo's era-tag convention"; r4 then
adopted an explicit supersede-marking convention and applied it to two of the
three stale displays — which is what makes the omission inconsistent rather
than conventional. (ANNEX 2's wrapper "counter 0/2, PE3 owed" is inside a
dated-append fence and is correctly date-scoped, per PE3's annex audit.)
*Repair: one parenthetical, or a superseded marker like the other two.*

### MINOR 3 — three surfaces still attribute the runner's 85 species witness pairs to "the S3.2 proof", which post-r4 is false for 15 of them

**Quotes.** S7 W12-ORACLE (L1333–1337): "AMBIGUITY WITNESSES: for every S3.2
species member, the two constructed lifts F_A, F_B (exact integer polynomials
**per the S3.2 proof**) give σ_A, σ_B EQUAL TO their predicted values and
σ_A ≠ σ_B"; S7 P-7: "all 85 species witness pairs hit their PREDICTED σ_A and
σ_B"; §S10 P-7 (L1589): "all 85 species pairs hit their PREDICTED σ_A and
σ_B — LEMMA W12-S3.2's constructed lifts confirmed by the independent
engine."

**Classification: minor** (record completeness; the fact is disclosed
elsewhere in the note and no number changes). I read the runner source: at
`w12_checks.py` L1043–1065 the witness builder sets `B = b2` (the canonical
integer lift) and, in the `else` branch for `B == 0`, builds the SEALED pair
with `predA = ((1,1),(2,1))`, `predB = ((3,1))` — i.e. exactly the two
branches r4 DELETED from the proof. Those are the b₂ = 0 members, one per
centre: q per oracle row, so 15 of the 85 pairs (rows Zp (2,3),(2,4),(3,2),
(3,3),(5,2) with 8+16+9+27+25 = 85 pairs). Post-r4 the proof's predicted σ
for those members is σ_A = {(1,1)³}, σ_B = {(2,1),(1,1)}, not the pair the
runner scores. The note DOES disclose this — at exactly one site, the [r4]
scope bracket on the S3.2 machine line ("the frozen runner builds the SEALED
pair (B = 0 at the b₂ = 0 members) … it is simply silent about equal
characteristic") — and the disclosure is accurate (I confirmed both sealed
witnesses have disc ≠ 0 with σ_A ≠ σ_B in mixed characteristic). The three
sites above were not updated. *Repair: one cross-reference each.*

### Remarks (uncounted, no repair owed)

* **R-1 (the n ≥ 6 firing row is stale at HEAD, in the strengthening
  direction).** The [r4] row says "the clause at μ ≥ 3 leaves IS the named
  open box [GENHN-HE(μ ≥ 3)]". True when written: HE3 commit 2 (872327b,
  19:33:31Z) landed 33 s AFTER r4 commit 2 (5728258, 19:32:58Z) and
  claims [GENHN-HE(μ ≥ 3)] CLOSED; HE3 commit 3 (6f5a072) then re-opened part
  of it as HE3-BOX-6. Same genre as PE4's R-2 race; W-12's own statement does
  not depend on it.
* **R-2 (the "no theorem statement moved" phrasing).** The [r4] ARC says "no
  theorem statement moved (the only statement-adjacent change is (A1) gaining
  a hypothesis clause, i.e. a STRENGTHENING of W-12.D's hypotheses …)". (A1)
  is part of THEOREM W-12.D's statement, so the statement did move (the
  theorem got weaker); the sentence discloses this in its own second half, so
  it is self-correcting, but the two halves contradict.
* **R-3 (the "sealed double-lift oracle leg" is a two-lift sample).** The
  n = 2 firing row cites it for pinned strength alongside S2.3. Read at the
  source, `w11_checks.py` L637–663 compares σ of the two lifts (a₁,a₀) and
  (a₁+p^N, a₀+p^N) on the decided members of one mixed-characteristic row
  (1,070 members) — corroboration, not certification. The row already
  attributes the proof to S2.3, so nothing is over-claimed; worth knowing
  when the leg is cited again.
* **R-4 (the clause's quantifier at non-visible x).** "EVERY member of every
  class (F, x)" quantifies over classes that (A1) defines as sets of window-N
  polynomials only for visible x (ν_F(x) ≤ N). Step 4 needs only visible
  classes at each window; the extra quantification is vacuous rather than
  wrong. One word ("visible") would make it exact. Also unchanged since PE4:
  W12-S2.1's/W12-L1(c)'s branchwise transport of the pinned notion still does
  not display the one-line disc-factorization step (PE4's R-3) — I re-verified
  it (cross-resultants are units, so disc(ΠF_i) ≠ 0 ⟺ ∀i disc(F_i) ≠ 0).

---

## 2. CHARGE-BY-CHARGE VERIFICATION RECORD

**(1) The r4 witness repair, re-derived (not re-read).** See the verdict
paragraph for the derivation. Additional checks made here:

* **What the deleted branches did, per characteristic.** B = 0: Lift 1 =
  y(y²+π^{2K+1}) is inseparable exactly in equal char 2 (disc(y²+c) = −4c);
  Lift 2 = y³+π^L is inseparable exactly in equal char 3 (F′ ≡ 0). At equal
  char p ≥ 5 BOTH are separable (disc −4π^{2K+1} ≠ 0; F′ = 3y² with
  gcd(F,F′) = 1 as F(0) = π^L ≠ 0), and in mixed characteristic both are
  fine. So the r4 record's scoping of the defect to p ∈ {2,3} and its claim
  that only ONE witness dies in each of those characteristics (hence "the
  sealed proof established nothing", not "established the opposite") is
  exactly right, and the degraded bound U₃^TRP ≥ q^N − q is the correct
  pre-repair statement.
* **The record's own machine numbers.** disc F_A valuation 2t+2(2K+1)
  (= 18 at N = 2 char 2 with 2K+1 = 7 ✓), disc F_B valuation 2L in char 2
  (14 at N = 2, L = 7 ✓) and 3N+L in char 3 (13 ✓), mixed-char valuations 2L
  at p = 2 (because L−3N ≤ 2 in the repaired regime) and 3N+L at p = 3,5 —
  all reproduced by my instrument at every row it ran. One harmless
  redundancy: "L = whichever of {3N+1, 3N+2} makes L−N odd" is always 3N+1
  (L−N = 2N+1 is odd for every N).
* **Nothing else in S3.2 needs t ≤ N−1.** The count (q centres × q^{N−1}
  free b₂, b₂ = 0 included via t = N), the mod-π^N congruence, the
  σ_A ≠ σ_B separation and the trivial upper bound q^{3N−2} are all
  t-uniform.

**(2) The (A1) σ-labeling clause.**

*Is it exactly what Step 4 consumes?* YES. The clause is equivalent to "all
disc ≠ 0 lifts of every member of every visible core class have type σ_F"
(given R-1's totality, "σ-DECIDED with forced σ = σ_F" adds nothing beyond
this). Step 4's lower bound needs precisely that the union of visible σ_F = τ
classes lies in the type-τ locus modulo the disc = 0 null set; the upper
bound needs precisely the same statement applied at F's own truncation. No
step needs more (Steps 1–3 use no σ-notion; I re-checked that Step 3 is
purely the (A1) partition plus (A2)'s definition of r(N)), and nothing needed
is missing — the only over-quantification is R-4's non-visible x.

*Does the degenerate-instance bracket show necessity?* YES, and I verified
each clause of it independently. With d_F = 0 the parameter set is the
one-point set (the empty shifted product), ℓ_F ≡ 0 has no parameter
coefficients to be positive, ν_F ≡ 0 is affine, and the single class per
window is all q^{2N} monic quadratics with dens·q^{2N} = q^{2N} exact and
trivial disjointness — so sealed (A1) holds; r(N) ≡ 0 gives (A2); (A0) under
the r3 pin's reading is the tautology. R_split = 1 and R_inert = R_ram = 0,
so **Σ_τ R_τ = 1 still holds** and the clause that fails is exactly the μ_τ
tie (μ_split = q/(2(q+1)) ≠ 1) — the note says precisely this. The clause
excludes the instance for the reason given (that F contains W-11(iii)'s
σ-undecided residue and SEP-INERT members, so no single σ_F works).

*Do the four firing citations hold at their pins?*

| firing | verdict at the pin |
|---|---|
| n = 2, W-11(i)+(iii) | **VERIFIED.** W11_PROOF L112–136: (i) is a seven-row table whose header is "The decided leaves of the n = 2 read are EXACTLY the seven families" and whose third column is σ (split / inert / ram / split / split / inert / split); (iii) reads "The families of (i) plus the σ-undecided residue partition all q^(2N) polynomials". Both as cited. I also re-derived the clause family by family at the PIN's strength, including equal characteristic 2 where disc f = A₁²: RAM(h) members have every A₁ ≠ 0 lift of type ram (F′ = A₁ ≠ 0 ⟹ separable; polygon slope h/2 ⟹ e = 2); SPLITEQ/INERTDEEP in char 2 force c₁ ≠ 0 (separability of the residual), so every lift has A₁ ≠ 0 and the in-window residual fixes σ; 2SIDED and both SEP rows likewise. HOLDS |
| n = 3, HM3.C | quotation byte-faithful, **but the quoted sentence is an over-claim — FINDING 1** |
| n = 4, GENH4.C | **VERIFIED.** GENH4_PROOF L135–145: "At every decided stage leaf of either genre (any history, any window), **EVERY lift with disc ≠ 0** has the σ claimed by the leaf dictionary", with the dictionary as W-12 transcribes it. Correctly restricted |
| n = 5, GENHN.C | **VERIFIED.** GENHN_PROOF L188–200: same wording ("EVERY lift with disc ≠ 0"), dictionary stage-RAM ↦ {(2e₁,f₁)} etc. as transcribed |
| n ≥ 6 | the row's "openly NOT supplied" is honest; stale at HEAD only per R-1 |

*(A0)'s new gloss.* With "the read's type" = σ_F, (A0) is implied by the
clause and hence redundant-but-retained, and it is true at every firing. The
only place the retained-and-demoted (A0) still carries proof weight is
MINOR 1's two sites.

**(3) Arc single-voicedness.** One CURRENT display; one live unmarked
contradiction (the header) — MINOR 2. Full inventory of arc-voice sites:
L5–8 (header, r1-era, unmarked), L1461 (a W-11 supplier pin, correctly
scoped), L1606–1613 ([r1] ARC, marked superseded), L1625/L1662 (annex
wrappers, dated), L1668 (ANNEX 2's "PE3 owed", dated), L1687–1702 ([r3] ARC,
marked superseded), L1706–1745 ([r4] ARC, CURRENT, "PE5 next").

**(4) Box inventory and the conditionality-stack summaries.** All eight W12
boxes exist in §S6 and are referenced (BOX-1 ×7, BOX-2 ×7, BOX-3 ×7, BOX-4
×1, BOX-5 ×2, BOX-6 ×2, BOX-7 ×6, BOX-8 ×1); [W12-H] appears 15× with all
five members (H-a ×4, H-b ×2, H-c ×4, H-d ×2, H-e ×4); inherited boxes
(W10-BOX-1/3/4, W11-BOX-3/4, HEX3-BOX-1 ×3) and both annexes' named
obligations are all live and pointed. No box is named-but-undefined or
defined-but-unreferenced. The summaries are consistent with r4 with two
exceptions, both already counted: MINOR 1's "No other conditionality: (A0)…"
(now incomplete — the σ-labeling clause is what the order-1 shapes supply),
and the header (MINOR 2). Everything else re-checked: S1's n = 3
conditionality bullet, S3.4's "Conditionality at n ≥ 3", S9's per-supplier
pins and its "One line" (THEOREM W-12.D's hypothesis set = "nothing — an
unconditional reduction" is still true after the strengthening: adding a
hypothesis to a reduction adds no conditionality to it), §S10's grade box,
and the two dated annex wrappers (which discharge BOX-2/BOX-3's named
obligations at composition grade while the body's "conditional on" reading
stands — the layering PE2/PE3 already audited). (H-e)'s closing gloss
"which is exactly (A0) well-posedness at composite stages" is now slightly
imprecise post-r4 (what the composite-stage layer owes is the σ-labeling
clause), but (H-e)'s own statement — "separable order-r residual ⟹ σ-decided
with (e, f) read off" — already IS decidedness-plus-label, so nothing is
under-priced.

**(5) The chosen unmined vein: S2.6 LEMMA W12-L0 and S2.7 LEMMA W12-L1 —
CLEAN, with a new six-row cross-check.**

* **W12-L0, all six rows re-derived from digit counting** at a node
  C(2s+1, s+1): RAM(u) = (q−1)q^{N−1−u}·q^{N−(u+1)/2} (the (q−1)q^{N−1−u}
  exact-valuation count × the v(A₁) ≥ (u+1)/2 cell); 2SIDED = two exact-
  valuation pins; SPLITEQ/INERTDEEP = the residual census (q−1)(q−2)/2 resp.
  q(q−1)/2 (every monic irreducible quadratic has nonzero constant term)
  × q^{N−2k−1}·q^{N−k−1}; SPLIT-TAIL = A₀ = 0 with v(A₁) = w exact;
  UNDECIDED = A₀ = 0 with v(A₁) ≥ M+1. **The claimed s-independence is
  exact**: on the stated ranges the leaf constraint subsumes the node
  constraint ((u+1)/2 ≥ s+1 ⟺ u ≥ 2s+1; w ≥ s+1 in 2SIDED/tail;
  k ≥ s+1 in SPLITEQ/INERTDEEP).
* **The instance bracket** Σ over histories H ⊆ {1,…,k−1} of (q−1)^{|H|} =
  (1+(q−1))^{k−1} = q^{k−1}, which is the note's 1 + Σ_{s=1}^{k−1}(q−1)q^{s−1}
  grouped by the last refinement depth — both forms verified, symbolically too.
* **All six aggregations == W-11(ii)** (the note displays only the UNDECIDED
  one as its consistency check): RAM at u = 2k−1 gives q^{k−1}·(q−1)q^{2N−3k}
  = (q−1)q^{2N−2k−1} ✓; 2SIDED gives q^{w₁−1}(q−1)²q^{2N−2−2w₁−w₂} =
  (q−1)²q^{2N−3−w₁−w₂} ✓; SPLITEQ ((q−1)(q−2)/2)q^{2N−2k−3} ✓; INERTDEEP
  ((q−1)/2)q^{2N−2k−2} ✓; SPLIT-TAIL q^{w−1}(q−1)q^{N−1−w} = (q−1)q^{N−2},
  which is exactly W-11(ii)'s "independent of w" ✓; UNDECIDED q^M·q^{N−1−M}
  = q^{N−1} ✓. All six confirmed symbolically in q, N and the parameters
  (§4).
* **Tail-cell exactness**: Σ_{w=s+1}^{M}(q−1)q^{N−1−w} + q^{N−1−M} =
  q^{N−1−s} = the node's whole A₀ = 0 cell, and M = ⌊(N−1)/2⌋ is exactly the
  largest w with 2w < N — so the SPLIT-TAIL/UNDECIDED boundary is genuinely
  s-independent and correctly placed for split-certification against every
  lift (u ≥ N > 2w).
* **W12-L1(b)** re-expanded: (x²+B₁x+B₀)(x−ρ̃) gives a₂′ = B₁−ρ̃,
  a₁′ = B₀−ρ̃B₁, a₀′ = −ρ̃B₀ as displayed; v(a₂′) = 0 makes the principal
  polygon the hull of {(0,u),(1,v(a₁′)),(2,0)} = the block's hull; all three
  trichotomy cases, the refine step (res(ρ̃−s) = ρ̄ still a unit) and the tail
  exit transfer as claimed, with the cubic's side residual R_f = −ρ̄·R_g a
  unit multiple (so same type, same roots, same refinement letter — and the
  S2.2 census sweep is unaffected because interior/right vertex values only
  need to be UNITS, not 1). Cardinalities in (a) match (q^{3(N−1)} both
  sides). (c)'s q^{N−1} fiber × q(q−1) patterns × q^{N−1} undecided blocks =
  (q−1)q^{2N−1} ✓.
* **S3.4's n = 2 instance** re-summed exactly: Σ2SIDED = 1/(q²(q+1)),
  ΣSPLITEQ = (q−2)/(2q²(q+1)), ΣINERTDEEP = 1/(2q(q+1)), R_split = R_inert =
  q/(2(q+1)), R_ram = 1/(q+1), Σ_τ R_τ = 1; r(N) = q^N +
  q⌊(N−1)/2⌋(q−1)q^{N−2} is the exact complement of the six core aggregates
  by W-11(iii).

---

## 3. MACHINE LEG

* **Seal:** `verification/openmath/w12_checks.py` md5
  **7dc040d94fbbb1e8d20ac817b665d418** == `git show
  f669cb0:verification/openmath/w12_checks.py | md5sum` — byte-identical;
  committed artifacts at HEAD carry §S10's md5s (0557b15f… / 05776c9e…).
* **Fresh full re-run (single run, this pass):** exit 0, **3,232,506 checks /
  0 violations**, teeth **W12-T-SHAPE 23 / T-DRAIN 23 / T-CENSUS4 8 /
  T-SIGMA 1273**, zero skips, 328.2 s, verdict GREEN — the FIFTH green run of
  the arc. Every §S10 family count reproduced EXACTLY: PIN 5, LVL0 138,
  SHAPE 164, QRT 27, L0HIST 306, BLOCK 1,594,670, L1X 1,594,090, DRAIN3
  1,183, ORACLE 41,923 (sum 3,232,506).
* **Artifacts:** fresh JSON content-identical to the committed one after
  stripping timing (programmatic compare == True); `w12_checks_output.txt`
  diff = 16 lines, all per-row elapsed times. Committed bytes RESTORED and
  md5s re-verified. No other file under `verification/openmath/` touched by
  this pass (the two untracked `genh4_*_smoke.*` files predate it).

## 4. FRESH ROUTE — equal characteristic p ≥ 5 (untouched by all four prior passes) + a symbolic identity leg

`/tmp/w12_pe5_fresh.py`, `/tmp/w12_pe5_fresh2.py`, `/tmp/pe5_sym.py`, written
this pass; own truncated-power-series arithmetic over F_p, own lower-hull
code, own depth-0 TRP classifier, own conservative recursive TRP reader, own
n = 2 block reader with refinement histories, own residual-type census — no
import of any repo runner. Prior passes ran mixed-char ℤ_p rows (PE1, PE2),
prime-power F_q[[t]] rows at q = 4, 8, 9 (PE3), and two exotic mixed-char
rings (PE4); **no pass had run equal characteristic p ≥ 5.**

**(A) The S3.2 witness pair, own arithmetic, six characteristics.** For
p = 2, 3, 5, 7, 11, 13 over F_p[[t]] and p = 2, 3, 5, 7, 11 over ℤ_p, at
N = 2 and 3, for every admissible t ∈ [1, N−1] ∪ {N}: gcd(F, F′) computed in
GF(p)[y,t] has deg_y = 0 for both lifts; disc F_A and disc F_B are nonzero
with valuations EXACTLY 2t+2(2K+1) and (2L at p = 2 / 3t+L at p ≥ 3); the
F_A Hensel roots land at valuations t and 2K+1−t (residual 0 to full
precision) and the F_B unit root at s ≡ −u; and v(a) = L−3t for the
complementary quadratic (the char-2 separability of its e = 2 block). **0
failures.** The SEALED pair was scored too: disc = 0 **iff** p = 2 for
Lift 1 and **iff** p = 3 for Lift 2 in equal characteristic, and both
nonzero in mixed characteristic — an independent confirmation of exactly the
r4 diagnosis, now also at p = 11, 13 which the repair's own leg does not
cover.

**(B) Own readers over F_q[[t]], q = 5, 7, 11, 13 — plus the committed tie.**

| row | depth-0 keys vs S2.4 | U₃^conv per centre vs HEX3.A | W12-L0 keys | undec/centre | DBL term |
|---|---|---|---|---|---|
| (Fqt,5,2) | 1 key exact | 25 == u(5,2) | 2 exact | 5 | 500 |
| (Fqt,7,2) | 1 key exact | 49 == u(7,2) | 2 exact | 7 | 2,058 |
| (Fqt,11,2) | 1 key exact | 121 == u(11,2) | 2 exact | 11 | 13,310 |
| (Fqt,13,2) | 1 key exact | 169 == u(13,2) | 2 exact | 13 | 26,364 |
| (Fqt,5,3) | 3 keys exact | 625 == u(5,3) | 6 exact | 25 | 12,500 |
| (Fqt,7,3) | 3 keys exact | 2,401 == u(7,3) | 6 exact | 49 | 100,842 |
| **(Fqt,5,4)** | **7 keys exact** | **17,625 == u(5,4) = 5⁶ + 4·5³·4·R(1)** | 9 exact | 125 | 312,500 |

0 mismatches anywhere. Every DBL term equals (q−1)q^{2N−1} and every
undecided-per-centre equals q^{N−1} (W-11's drainage), and the SPLIT-TAIL
per-centre total equals ⌊(N−1)/2⌋(q−1)q^{N−2}. **(Fqt,5,4) is the first row
anywhere in the arc that exercises HEX3.A's N-LINEAR term at p ≥ 5** (the
k = 1 summand is live only at N ≥ 4): my conservative reader's 17,625 matches
the law's 15,625 + 2,000 exactly. **Committed-JSON ties:** at (Fqt,5,2) and
(Zp,5,2) my whole-space depth-0 key dictionary, `dbl_undecided` (500),
`species` (25) and `U3TRP_measured_conservative` (125) are all EQUAL to the
committed row; at (Zp,7,2) the same four quantities (2,058 / 49 / 343) are
EQUAL to my **F_q[[t]]** row — a cross-characteristic pair at (7,2) that the
frozen kit cannot form (BOX-6: no mixed-char prime-power rows; and (7,2)
exists only as a ℤ_p row), so §S10 P-6's nine shared pairs gain a tenth in my
instrument.

**(C) Symbolic identity leg (exact in q).** All six W12-L0 → W-11(ii)
aggregation identities, the instance bracket, all four n = 2 series, R_split,
R_inert and Σ_τ R_τ = 1 verified as rational-function identities in q
(sympy, convergent branch |q^{-1}| < 1), and independently as exact rationals
at q = 2,3,4,5,7,8,9,11,13,16,25,27 (truncation error < 10^{−60}).
**HEX3.A's normalized slope**, computed from my own transcription of the law
at N = 400 and 800: q = 2 → 0.0416666667 = 1/24; q = 5 → 0.0133333333;
q = 7 → 0.0076530612; q = 11 → 0.0034435262; q = 13 → 0.0025359256 — each
equal to (q−1)/(2q²(q+1)) to 10 places. This confirms r4's FINDING-3
replacement text (Θ(N·q^{2N}) with that mean slope) at four prime powers no
pass had checked, and I re-derived the slope analytically as well (the
N-linear part of Σ_k (q−1)q^{4k−1}q^{N−3k}·⌊(N−3k−1)/2⌋(q−1)q^{N−3k−2}
normalizes to N(q−1)/(2q²(q+1))). I also re-checked r4's committed-number
arithmetic: normalized ×q^{−2N} the q = 2 sequence is 0.5000, 0.5625,
0.59375, 0.664062, 0.691406 (RISING) with step ratios 4.5, 4.222, 4.474,
4.165 — all > 4, as the repair states.

**Disclosed own-instrument notes:** my first symbolic checker compared whole
sympy `Piecewise` objects against closed forms and reported seven spurious
FAILs; the convergent branch of each Piecewise is the wanted value, and the
corrected checker (`/tmp/pe5_sym.py`) returns True on all seven. My first
numeric tolerance (1e−40 with 120-term double sums) was tighter than the
truncation error at q = 2; re-run at 300 terms with a 10^{−60} bar, exact
rationals. Neither affected any verdict above.

## 5. ARC / COUNTER

Arc: composed 0/2 → PE1 1C+3G+2m (2b47711) → r1 (ba0d1a4) + BOX-3 annex
(8e535d2) → PE2 0C+3G+2m (1be15d2) → r2 + BOX-2 annex (99f1813) → PE3
0C+1G+1m (c9c5c0e) → r3 σ-pin (b17238a) → PE4 1C+2G+2m (26689da) → r4
(d2d91b7 + 5728258) → **PE5 (this pass): NOT CLEAN — 0 CRITICAL + 1
JUSTIFICATION GAP + 3 minor; counter stays 0/2; r5 owed.** The r4 repair's
mathematics is sound in the vein it was written for — I re-derived both lifts
in all three characteristics and the parity bracket does cure the sealed
vertex condition's degeneracy at t = N — and the σ-labeling clause is exactly
the hypothesis Step 4 needs, with a correct necessity instance and three of
its four firing citations verified verbatim at their pins. What remains is
one warrant defect and three record defects, all one-clause repairs: the
n = 3 firing row leans on HM3.C's "Ore certifies EVERY lift", the very
sentence this repair struck from S2.3 as false in equal characteristic (and
the m2 blast radius, including HM3.C itself, was never swept); §S3.4's
Step-4 upper bound and conditionality close still cite the demoted (A0); the
header's arc display is three repairs stale and unmarked while its two
siblings were marked; and three surfaces still credit the frozen runner's
b₂ = 0 witness pairs to a proof that no longer contains them. Arc facts for
the record: seal intact, battery GREEN and reproducible a FIFTH time at
identical counts, and the note's law suite now confirmed in equal
characteristic p ≥ 5 for the first time — including a row that exercises the
annexed HEX3.A's N-linear regime at p = 5, and a (7,2) cross-characteristic
pair the frozen kit cannot form.

— passPE5 verifier, fresh context, 2026-08-08.
