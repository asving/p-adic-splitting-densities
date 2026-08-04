# SURVK2 pass PE1 — first hostile content verification + the A = {1} counterexample probe

Verifier: SURVK2-PE1 (fresh context, Fable). Object:
`lean/notes/openmath/SURVK2_PROOF_2026-08-08.md` at 53e0883 (confirmed via
`git log -1 --format=%h -- <file>`). Charge: quote-and-classify
(CRITICAL / GAP / NOTE) on K2-L1..L7, K2-THM-A, K2-COR, the (K2-RES) boxes,
the g0 >= 3 predictions, the machine leg, the instrument's three-commit
record — PLUS a dedicated counterexample probe at the A = {1} corner
(new file `verification/openmath/survk2_pe1_ext.py`). Fix nothing.

## 0. Machine leg re-run (charge 6, first half)

* Pins: six verified by direct md5 (survk2_derive_checks.py
  d8493ab90e3578fae60032cde73a3b81, its output c44c19c7..., its results
  6d1e5987...; survk2_instrument.py 389b1db9... rev 2, its results
  1ac516df..., its output 0db6f784...) — all EQUAL to the note's
  displays; the remaining engine pins re-verified by the fresh
  derive-checks run's K2-PIN family (10/10 green).
* Three-commit record verified in git: 10ec9f3 (seal: note + runner rev 1),
  dbe0cb9 (amendment, pre-verdict: runner rev 2 + 28-line bracket),
  5e2b8e4 (verdict: results + output + note results section). The note is
  at 53e0883, one commit later; adjudication ac97b2a after that.
* `survk2_derive_checks.py` RE-RUN fresh (scratch outdir): output
  byte-identical to the committed output except two 0.1 s timing digits;
  332 live rows, REG 303 / non-REG 29 / glued groups 38, fact cells 1,311,
  fibers with two n=3 windows 0, placement-pair fibers 0, ALL sixteen
  families 0 violations. Reproduction EXACT.
* `survk2_instrument.py` re-run launched read-only to a scratch dir
  (runs ~50 min: ten deliberate 300 s g0>=3 timeouts); verdict appended
  below at §6.

## 1. Charge 1 — K2-L1 (window normal form) and K2-L2 (budget), re-derived

Re-derivation from the ACCEPTED [RMG] S2.2 inventory (read directly from
RMENGINE_2026-08-08.md S2.2/S2.1/L-NORM/S3.2, plus the walk code):

* K2-L1(a): the walk fires the LOWEST overflowing level; level-0
  promotion and correction both require j0 >= P0; hence level-0 events
  are consecutive and a window closes exactly when j0 < P0. CONFIRMED.
* K2-L1(b) at exponent level: interior levels see the window only through
  the +1-per-promotion feed into level 1; level-0 corrections have no
  dump vector (the i = 0 form) and touch only j0 and the coefficient;
  all p_w promotions land in j1 before any interior event can fire
  (priority). CONFIRMED.
* K2-L1(c)/(d) — one over-breadth (finding G2 below): the interchangeability /
  realization claim is stated for arbitrary continuations, but branch
  AVAILABILITY of junk children is coefficient-dependent (pi-junk child
  exists iff X-hat != 0 for the CURRENT coefficient; L-NORM(b) gives only
  w0 >= w+1 "absent iff X-hat = 0"). Swapping drain content changes the
  running coefficient, so a downstream JUNK edge of the original path
  need not exist on the substituted path. For junk-free continuations
  (promotions/exits/L-children only — L-NORM(a) never absent) the claim
  is exact, and every consumer in this note (K2-L7 fibers, THM-A) is
  junk-free. GAP, statement-hygiene, consumers unaffected.
* K2-L2, re-derived: parked < P0 at every arrival (root sigma1 <=
  2(e0-1) < e0 g0 NEEDS g0 >= 2 — fine on this note's class; after any
  window, < P0 by (a); and any mid-chain arrival lands on a drained
  state by priority). Arrival <= P0 (reduced dumps a_{c,0} <= P0-1 plus
  the Y +1; reduced d-cells j0(D) <= P0-1 plus y2 <= 1). Opening
  j0 <= 2P0 - 1, so n = floor(j0/e0) <= 2g0 - 1. EXACT for any g0 >= 2,
  both stages, any d0. CONFIRMED — with two nits (notes N2, N1 below): the
  claim-table's "any g0" silently includes g0 = 1 where the root leg
  fails (2(e0-1) >= P0 = e0 at e0 >= 2), and the mid-window Y-return
  sentence claims net consumption ">= e0 - 1 >= 1", false at e0 = 1
  (net 0 at k = g0-1); the budget conclusion needs only net >= 0, which
  holds, and window termination rides on [RMG] tree-finiteness, so the
  conclusion is unaffected.

## 2. Charge 2 — K2-L3, THE HARD STEP, re-derived exhaustively

Setting (from the accepted corr_table display): at g0 = 2 the level-0
moves and their unit costs are C1 = e0(g0-1) = 1 unit, C0 = 2 units,
promotion = 2 units; events fire at n >= 2; junk-free drains keep the
sub-e0 remainder r invariant (all consumptions are multiples of e0 —
this is why unit bookkeeping is exact; Y-returns would break it and are
excluded from the junk-free inventory).

Exhaustive re-derivation (independent, by hand, then re-verified by a
brute-force enumerator in the probe file, decorrelated from the
composer's legal_drains_g2):

    n <= 1: no drains (below firing threshold).  n = 2: [C1] (f=1),
    [C0] (f=0), [promo] (f=0) — and after [C1], u = 1 < 2 closes, so
    nothing longer.  n = 3: first event C1 -> u=2 MUST refire (priority):
    [C1,C1] (f=1), [C1,C0] (f=0), [C1,promo] (f=0); first event C0 or
    promo -> u=1 closes: [C0] (f=1), [promo] (f=1).  EIGHT drains total.
    The display's list is EXACTLY this. No missed pattern found.

* (i) no order-multiplicity: [C0,C1] and [promo,C1] stall at u=1 before
  the C1 — each (K,p) has a unique legal order. CONFIRMED.
* (ii) unique exchange: classes by (consumed units, p): n=3 gives
  (2,0):{[C1,C1],[C0]} — the ONLY multi-member class anywhere; (2,1),
  (3,0), (3,1) singletons; n=2 all singletons. CONFIRMED. (Note the
  near-miss the display rightly does not pair: [C0] vs [promo] at n=2
  share units 2 but differ in p — not interchangeable.)
* (iii) T0 quantum: the seed window's budget is t-linear (j0(D_t) =
  s1(u1) + t e0, W-D2(iv)+); k = 1 is the only unit-mass index at
  g0 = 2, so the cross-seed pairing quantum g0 - k = 1 is forced.
  CONFIRMED.
* (iv) per-(n, units, p) signed counts: the exchange class nets
  (+1) + (-1) = 0 (parity |K| = 2 vs 1), all others +-1. CONFIRMED.
* Hypothesis hygiene: the display presumes BOTH digits available
  (A = {0,1}); the lemma header does not say so, though (R2) pins it at
  the theorem and S7(c) boxes the complement. NOTE (N6).

## 3. Charge 3 — K2-THM-A: forms, dichotomy, (K2-REG)

* The four class-vector evaluations re-derived from K2-L4 (residues
  multiply in K0; sign = correction parity; kappa-rho cancels from every
  within-group comparison): S always protected; P1 protected iff not-I1;
  P2 protected iff not-I3; T1: a=c iff I1, b=c iff I3, a=b iff I2, and
  under I3 & not-I1 the residual a-class cannot collide with b (a=b
  under I3 would force I1). Case table: I1 -> T1 gives (0,-1) or (-1)
  [the (-1) sub-case = additionally I3]; not-I1 & I3 -> (-1,0);
  not-I1 & not-I3 -> (-1,-1,+1) [not-I2] or (-2,+1) [I2] — NOT protected
  under the machine's protected() predicate (one nonzero class at +-1 OR
  a {-1,+1} pair; three nonzero classes / a -2 disqualify). The
  displayed table is COMPLETE and each entry re-derives. CONFIRMED.
* The dichotomy: (R4a) S present -> done; (R4b) P1 & T1 present: not-I1
  -> the P1 is a protected (+1,-1) pair; I1 -> the T1 is protected.
  I1 is tower-level (single t = 0 instance at g0 = 2 since P1/T1 span
  seeds {0,1} after rebase), so the split is coherent row-wide. Every
  I1/I3 truth combination lands on a protected form. CONFIRMED.
* "Under EVERY residue assignment" is coherent: which cells exist at
  beta_min is residue-independent GIVEN the availability data (L-children
  never absent; junk cells sit strictly above the bottom; availability
  itself is pinned by (R2) and the realized (R3)/(R4) forms). CONFIRMED.
* (K2-REG) is machine-decidable row-by-row: (R0)-(R4) each evaluated on
  the realized beta_min system; the note's disclosure (iii) states the
  row-fact honestly. No hidden hypothesis found in the predicate itself.
* REDUNDANCY note (N4): (R2) is not actually consumed by THM-A's proof —
  a system satisfying (R3)+(R4) with A = {1} would still be protected
  (S present, or P1/T1 both present is impossible without C0). Harmless
  conservatism, worth recording since the A-corner boxes lean on (R2).
* Scope-statement nit (folded into G1): K2-L7(ii)'s "<= 1 branch window" hypothesis
  does NOT by itself exclude the S7(e) placement pair (which has ZERO
  exchange-branch windows — the freedom is promotion PLACEMENT across a
  two-window chain at equal totals); F-B's prose does fence "placement
  shapes" out, and THM-A is insulated by (R3) (a placement pair
  duplicates a (t,K) entry and falls outside the four forms), but the
  lemma's own scope line ("<= 1 branch window — the realized class")
  under-describes the excluded set. GAP, statement-scope only.
* Same family (folded into G1; REALIZED — see 4.3): fibers with equal (I, pi-vec) but DIFFERENT interior
  event ORDER would have different arrival sequences; K2-L7's statement
  quietly conditions on the arrival sequence ("determined by I and the
  promotion placements") and the proof does not show arrival sequences
  are fiber-constant. An interior-order pair would produce |S_t| = 2
  (same sign, same class twice). Machine-absent (K2-CHAIN 0; K2-FIB got
  = want on all fibers) and THM-A again insulated by (R3), but K2-L7(ii)
  as a LEMMA carries this unstated conditioning. GAP.

[continued in §4-§7 below]

## 4. Charges 4-5 — the probe (survk2_pe1_ext.py) and the boxes

New instrument `verification/openmath/survk2_pe1_ext.py` (verifier-owned,
engines read-only), output `survk2_pe1_ext_output.txt`, results
`survk2_pe1_ext_results.json`. Final state: 0 probe violations, 5 findings.

### 4.1 THE A = {1} CORNER IS PROVABLY CLASS-EMPTY (the headline)

The note's (K2-RES)(c) presents A = {1} (psi0_0 = 0, psi0_1 != 0) as "the
sharpest known counterexample CANDIDATE to (SURV-K2) itself ... Needs a
tower with psi0_0 = 0 ... (machine-dark corner)". It is not machine-dark;
it is EMPTY on the note's own class, twice over:

1. **The class pin forbids it directly.** The [ILN] S0.1 class — cited in
   this note's own Scope line — pins every read (ITERLAWN_PROOF
   S0.1, the read-j bullet): "psi_j in K_j[y] monic irreducible,
   deg psi_j = g_j >= 1, **psi_j(0) != 0**". At j = 0 this is literally
   psi0_0 != 0. A tower with psi0_0 = 0 is OUTSIDE the class (SURV-K2)
   quantifies over.
2. **Irreducibility alone already forces it at g0 >= 2.** psi0(0) = 0
   means y | psi0, contradicting irreducibility at degree >= 2 (and
   K_1 = K_0[y]/(psi0) would not be a field — the engine's
   mk_field_ext/pick_irreducible enforce exactly this:
   grb_order2_check.py:428-445, 491-494).

Machine witness (probe A): 96-tower engine grid (kinds x p in {2,3,5} x
d0 in {1,2} x four level-0 reads incl. e0 = 1 x two idx parities): psi0_0
!= 0 on ALL 96 (A-census: {(0,1): 88, (0,): 8}); field-level exhaustive
scan of every monic degree-2 polynomial over every K0 in the grid
(q = 2,3,4,5,9,25): irreducible-with-zero-constant-term count = 0
everywhere. VERDICT: **the A = {1} stratum of (K2-RES)(c), and A = 0
(empty set) with it, are vacuous class-wide; the explicit counterexample
candidate to (SURV-K2) CANNOT be realized.** Free consequences the note
leaves on the table: (R2) reduces to the single condition psi0_1 != 0;
the only realizable availability corner is A = {0} (only C0) — which the
box itself argues safe, and whose safety arithmetic the probe verified
independently (all (units,p) drain classes singletons at n <= 3;
cross-seed toggle killed by parked-parity disjointness). The A = {0}
shape is realizable at odd characteristic only (char 2: an Artin-Schreier
scan finds zero irreducibles y^2 + c; probe A1 counts 1/4/2/16 of them at
q = 3/9/5/25). Note also the box's "(A = 0 and A = {2} are safe...)" —
"A = {2}" is a notation slip (indices vs masses; should be A = {0} in the
note's own (R2) index notation).

### 4.2 Independent drain inventories (probe B; decorrelated enumerator)

Unit-level brute force AND a raw-j0-level enumerator (no unit
abstraction; e0 in {2,3}, every sub-e0 residue) agree with each other and
with the note's K2-L3 display exactly (eight drains; unique legal order
per (K,p); the (2,0)-exchange the unique multi-member class; per-class
signed counts in {0,+-1}). The g0 >= 3 failure candidates re-derived
independently: the n = 5 masses-{1,3} window gives exactly {C0} and
{C2,C2,C2}, both sign -, class count -2; {C2,C1} has exactly 2 legal
orders; the g0 = 2 promo placement pair gives exactly 2 paths net -2.
The note's S7(d)/(e) arithmetic is CORRECT as displayed. (Bonus census:
at g0 = 3 FULL availability the n <= 5 multi-member classes all net in
{0,+1} — the -2 window genuinely needs the psi0_1 = 0 restriction, which
the box correctly states as "masses {1,3} available".)

### 4.3 Glued dump-swap rows by hand (probe C) — and a REALIZED
### duplicate-book pair the S8 censuses do not see

* SDG2BF[1479,1485] slot (5,0,0) and SDG2BZ same key: the 2-cell glued
  kill group re-traced; glue quantum verified: rider dump0 = 4 (+C1) vs
  other dump0 = 1, difference = 3 = e0(g0-k) EXACTLY; residues equal
  (char 2: all residues are 1 — the kill identity is trivially true,
  which is why the dump-swap kills concentrate on char 2); rows
  instance-protected via the S-form group at slot (2,0,0). Matches the
  instrument witness verbatim.
* SDW4G2F[2635,2635] slot (4,0,0,0) — the note's worked 5-cell group:
  re-traced, net -1 single class, protected, books dump(1,) count 0 and
  dump(4,) count -1: the note's record is ACCURATE. BUT the dump(4,)
  book contains TWO cells with IDENTICAL (t, K, I, pc, sign) =
  (t=1, K={C0,C1}, dump(4,), pc=(0,0,1,2), -) — distinguished ONLY by
  cross-window correction placement:
      windows A: dump-window [C0], seed-window [C1]
      windows B: dump-window [C1], seed-window [C0]
  (probe C2b prints both decompositions). This is a REALIZED same-sign
  same-class duplicate-book pair inside one fiber — the shape K2-L3(i)'s
  fiber-level gloss says never occurs ("distinct cells of a fiber have
  distinct (t, K, placement) content, never duplicated books" — the
  placements ARE distinct, the (t,K,I) books are NOT), and the shape
  K2-L7's proof declares "machine-absent" ("the >= 2-branch shapes are
  exactly the S7 candidates, machine-absent"). The S8 K2-CHAIN brackets
  miss it structurally: "placement-pair fibers: 0" counts only
  PROMOTION-placement vectors (pvs), and "0 fibers with two n = 3
  windows" is evaluated on ONE representative cell (fc[0]) although
  window budgets differ across the fiber's cells (cell A's seed window
  has n = 2, cell B's n = 3). The per-seed count still lands at -1 (the
  {C1,C1,C1} rider offsets), so K2-CHAIN's |S_t| <= 1 verdict is
  unharmed — but the note's SCOPING argument for K2-L7(ii) (per-window
  product, <= 1 branch window) demonstrably does not describe the
  realized class. THM-A is insulated: the witness is on a glued
  (non-REGULAR) row, and any single-book duplicate would break (R3)
  (falls into the S7(b) box, which correctly anticipates richer
  mass-classes). See finding G1.
* Probe E (full-roster duplicate-book census, all 332 rows re-traced
  with an independent selection replication — row count 332 matches):
  EXACTLY ONE duplicate-book fiber exists in the entire traced set —
  the SDW4G2F[2635,2635] slot (4,0,0,0) witness above — and it is on a
  glued row. So the duplicate shape is realized (contradicting the
  "machine-absent" sentence) but confined to the boxed stratum;
  REGULAR-locus instances: zero, independently re-confirmed.

### 4.4 The two hand re-derivations (charge 6) + the CROSS event

* T0 kill, EQ3G2B[1479,1485] slot (5,0,0): psi0 = y^2 + y + 2 over F3
  (irreducible: disc = 2, a non-square mod 3; psi0(0) = 2 != 0). Probe
  prints x_0 = x_1 = 2, psibar_1 = 1. BY HAND in F3: I1: psibar_1*x_1 =
  1*2 = 2 = x_0 — HOLDS; the pair (t=0, K={}) vs (t=1, K={C1}) has
  residues x_0*rho = 2rho and x_1*psibar_1*rho = 2rho — equal, signs
  -/+, KILLED; both printed res = 1 pins rho = 2 (2*2 = 4 = 1 in F3),
  consistent. Row survives via the S-form (t=1, K={C0}) at slot
  (2,0,0). EXACT match to the instrument's display witness.
* Exchange kill, K2G2P5B[1479,1479] slot (4,1,0): psi0 = y^2 + 4y + 1
  over F5 — I PREDICTED this polynomial by hand from pick_irreducible's
  enumeration order (idx = h1 % 2 = 1; second match at b = 1) before
  reading the probe output, and it matched. BY HAND in F5: I3:
  psibar_1^2 = 16 = 1 = psibar_0 — HOLDS; {C0} (+) vs {C1,C1} (-) same
  class (both printed res 3), KILLED; row survives via the 1-cell -1
  group at slot (1,1,0).
* Bonus (the loud event): K2W4G2Z[2635,2635] re-traced; psi0 = y^2+y+2
  over F3; probe D3 verifies (I1, I3, I2) = (False, False, True) and
  the group vector (-1, +2) at slot (4,0,0,0) with the protected
  (-1,+1) survivor at slot (1,0,0,0). BY HAND: x_1 = 1, x_0 = 2,
  psibar_1 = 1, psibar_0 = 2: I1: 1*1 = 1 != 2; I3: 1 != 2; I2: 1*2 = 2
  = 2*1 — exactly the note's not-I1 & not-I3 & I2 T1-corner, global
  sign flipped, classes ((a=b) merged +2, c at -1). The note's S6
  parenthetical derivation of the CROSS event is CONFIRMED cell-exact.

### 4.5 The remaining boxes and records (charge 5)

* (K2-RES)(a): glue algebra and instance record accurate (probe C); the
  target statement ("glued case table, finite per glue shape") fair.
* (K2-RES)(b): the displayed -2 example's arithmetic checks (classes
  A = x0*ps0 (-), B = x0*ps1^2 (+), C = x1*ps1*ps0 (+), D = x1*ps1^3 (-);
  the merger identity as displayed; 0 instances per K2-SHAPE).
  It also correctly catches the hypothetical single-book analogue of the
  4.3 duplicate shape.
* (K2-RES)(c): see 4.1 — the stratum is class-empty (finding G4).
* (K2-RES)(d): both g0 >= 3 pillar failures re-derived from K2-L2's
  n <= 2g0-1 = 5 (probe B3): derivations CORRECT as sealed predictions.
* (K2-RES)(e): arithmetic correct (probe B4); but "[0 instances]" is a
  claim about the PROMO shape only — the correction-placement analogue
  is realized (4.3) and belongs to (a)/(b); worth one sentence in any
  cure (folded into G1).
* K2-COR: consumption grades ride correctly (SD-L6/SD-L7/S-L3/S-THM(b)
  all daggered at their standing grades; the binding W-arc 0/2 cap is
  stated in the header, the grade table, and the dependency line —
  consistent). The remainder-law re-derivations from the four forms
  check: survivors single-seed +-1, per-seed |S_t| <= 1 on forms,
  taxonomy keyed by (n_cf, parity).
* Header nit: the grade-cap sentence lists W-D2(iv) and W-D3 as the
  WMULTDCX consumption but K2-L2/K2-L4 also cite W-D1 (anchor
  reducedness, stage-1 seed coefficient); the S9 dependency line has it
  right ("W-D1, W-D2(iv), W-D3 frame"). NOTE only.

## 5. Findings (quote-and-classify)

**CRITICAL: none.**

**G1 (GAP) — K2-L7(ii)/K2-L3(i)/S8: the realized class is NOT the
"<= 1 branch window" class, and duplicated books ARE realized.**
Quotes: K2-L3(i) "distinct cells of a fiber have distinct (t, K,
placement) content, never duplicated books"; K2-L7 proof "the >= 2-branch
shapes are exactly the S7 candidates, machine-absent"; S8 K2-CHAIN
"branch census: 0 fibers with two n = 3 windows, 0 placement-pair
fibers"; claims table "PROVED (attempt; g0 = 2, <= 1 branch window — the
realized class)". Refuting instance (probe C2b, in the committed traced
set): SDW4G2F[2635,2635] slot (4,0,0,0), fiber (dump(4,), pc=(0,0,1,2)):
cells {C0@dump,C1@seed} and {C1@dump,C0@seed} — identical (t,K,I,pc,sgn)
books, same residue class, same sign; plus the seed window IS a realized
n = 3 exchange-branch window in the same fiber. The S8 censuses are
sound for what they literally measure but do not measure this shape
(promo-only pvs; representative-cell window budgets). CONSEQUENCE
CONTAINED: |S_t| <= 1 still machine-true on all 332 rows (the {C1,C1,C1}
rider offsets here); THM-A untouched ((R3) excludes duplicate books on
REGULAR rows; the witness row is glued/non-REGULAR, i.e. inside the
S7(a) open box). The defect is the lemma's scope justification and three
over-strong prose claims, not any REGULAR-locus theorem.

**G2 (GAP) — K2-L1(c)/(d): interchangeability asserted for arbitrary
continuations; junk-child availability is coefficient-dependent.**
Quote: "replacing one by the other yields a legal path with identical
interior history" + "(d) the full tree realizes EVERY legal choice".
The pi-junk child exists iff X-hat != 0 for the CURRENT coefficient
(L-NORM(b): "absent iff X-hat = 0"); swapping drain content changes the
coefficient, so a junk edge of the original continuation need not exist
on the substituted path. Exact for junk-free continuations
(promotions/exits/L-children; L-NORM(a)); every consumer here is
junk-free, so no downstream damage. Statement needs the junk-free
qualifier.

**G3 (GAP) — K2-L5(a): the any-d0 pi-junk exclusion's replay
justification.** Quote: "replay C's remaining choices verbatim — legal,
since the walk depends only on exponents and these coincide (K2-L1(d))".
The walk's FIRING depends only on exponents; the BRANCH AVAILABILITY of
junk children does not. Repairable at d0 = 1 (take the L-child at any
blocked downstream pi-fork: same exponents, line drops further). At
d0 >= 2 a downstream Y-fork blocks even the fallback (the note itself
notes the Y-child "changes the exponent trajectory ... the L-shadow
replay below can be blocked" — but deploys this caveat only against the
Y-exclusion, not against its own pi-exclusion replay). Under (R0) as
used by THM-A ( beta_min cells Y-edge-free) the argument closes, so the
theorem is unaffected; the LEMMA's "(any d0)" pi-clause carries a
justification gap for paths mixing pi-junk with later Y-edges.
Machine-true everywhere (K2-JBOT 689/689).

**G4 (GAP) — (K2-RES)(c) mis-boxes a class-empty stratum as the sharpest
open counterexample.** Quote: "THE AVAILABILITY CORNER A = {1}
(psi0_0 = 0, psi0_1 != 0) — the sharpest known counterexample CANDIDATE
to (SURV-K2) itself ... Needs a tower with psi0_0 = 0 and the P1-only
line arithmetic; all 16 traced g0 = 2 towers have A = {0,1}
(machine-dark corner)." The S0.1 class pin (quoted at this note's Scope
line) requires psi_j(0) != 0, and irreducibility at g0 >= 2 forces it
independently: the corner is PROVABLY EMPTY, the candidate unrealizable,
and the "all 16 towers have A = {0,1}" mystery is a two-line theorem,
not an instance accident (see 4.1; probe A). In the note's favor —
coverage extends for free — but the box as written materially misstates
the residual risk profile and (R2)'s content.

**Notes (no grade): N1** K2-L2 prose "consumes e0(g0-k) - 1 >= e0 - 1 >=
1 net" fails at e0 = 1 (net 0 at k = g0-1); budget conclusion needs only
>= 0; window termination rides on [RMG] finiteness. **N2** claims-table
"any g0" on K2-L1/L2/L4 silently means g0 >= 2 (root bound uses
2(e0-1) < e0g0). **N3** "A = {2}" notation slip in S7(c). **N4** (R2) is
not consumed by THM-A's proof ((R3)+(R4) suffice) — harmless
conservatism, relevant after G4. **N5** header cap sentence omits W-D1
from the WMULTDCX consumption list (dependency line correct). **N6**
K2-L3's display presumes A = {0,1} without saying so in the lemma
header.

## 6. Instrument arc adjudication + instrument re-run

The three-commit record is coherent in git (seal 10ec9f3 with runner rev
1 + PENDING-verdict note; amendment dbe0cb9 pre-verdict, runner rev 2 =
atomic buffering + 300 s K2 budget, roster and all PRED-1..7 byte-
unchanged, the g0 >= 3 expected-untested consequence declared BEFORE the
run's verdict; verdict 5e2b8e4 from artifacts). ADJUDICATION of the
mid-battery amendment: what was read before amending = the union phase's
replication count (286/286) and the K2G3AF prep stall — harness/cost
telemetry, not any candidate-law verdict; the amendment touches no
verdict logic; the timing-dependence of the K2 row set is disclosed and
the verdicts are law-keyed over the listed rows. The seal's evidentiary
value for PRED-1..7 over the traced set is PRESERVED; the g0 in {3,4}
clause of PRED-2 is honestly dead (coverage failure on record). The
wording quirk (timeouts surfacing as "ENGINE UNSUPPORTED
(TimeoutError)") is disclosed in the note and visible in the fresh
re-run.

**Instrument re-run COMPLETE (read-only, scratch outdir):** all nine
verdict families 0 violations; 332 live rows (union 286 replicated
tower-by-tower + K2 46); 102 kill rows; ten g0 >= 3 towers
budget-timeout as disclosed ("ENGINE UNSUPPORTED (TimeoutError('K2
tower budget'))" — the wording quirk the note discloses, reproduced
verbatim); output IDENTICAL to the committed
survk2_instrument_output.txt up to per-tower timing digits, the elapsed
line, and the outdir path; results JSON field-by-field EQUAL to the
committed artifact on every field except elapsed (final, violations,
counters, union_g2_rows, law, mutations, pair_census, a0tab, qbrec,
qcrec, qdrows, grprec — all byte-equal). THE FAMILIES REPRODUCE.

## 7. Verdict

The spine holds under hostile re-derivation: K2-L1(a)(b), K2-L2, the
complete K2-L3 inventory (independently brute-forced at unit AND raw-j0
level), K2-L4/L5(b)(c)/L6, K2-L7(i)(iii), the four-form evaluations,
the I1/I3 dichotomy, K2-THM-A on (K2-REG), K2-COR's capped consequence
chain, and the g0 >= 3 failure predictions are all CONFIRMED; both
runners reproduce exactly; the T0, exchange, and CROSS witnesses
re-derive by hand to the digit. The grade-cap discipline (binding W-arc
0/2 cap) is stated consistently. No critical error found. Four gaps:
G1 (the realized class is not the "<= 1 branch window" class — a
same-sign duplicate-book fiber is REALIZED at SDW4G2F[2635,2635],
exactly one on the roster, glued stratum; three prose claims and two S8
census glosses overstate; THM-A insulated by (R3)); G2 (K2-L1(c)/(d)
junk-free qualifier missing); G3 (K2-L5(a) any-d0 pi-exclusion replay
justification; closed under (R0) as used); G4 ((K2-RES)(c)'s A = {1}
counterexample candidate is PROVABLY CLASS-EMPTY — the S0.1 pin
psi_j(0) != 0 plus irreducibility; the box materially misstates the
residual risk, in the theorem's favor). Six notes N1-N6. The note's
honest conditionality display (attempt grade, capped, 0/0 own arc)
is accurate throughout.

SURVK2-PE1 FINDINGS: 0 critical, 4 gaps
VERDICT: GAPS-ONLY
