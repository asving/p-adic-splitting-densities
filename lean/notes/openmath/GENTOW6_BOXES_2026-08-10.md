# GENTOW6 SUB-BOX UNIT: GENTOW6-BOX-1 (mu2 >= 3 attainment) +
# GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row),
# 2026-08-10

**STATUS: COMPLETE — both machine legs GREEN (BOX-1: 459/0 with
teeth 3/2/7/6 exact, S4; BOX-4: 265/0 with teeth 4/4/4 exact, S5;
both sealed two-commit, both isolated re-runs bit-identical, both
run-1 REDs kept + disclosed). Grade 0/2 (attempt; hostile arc
owed). Prove-first per the standing directive: BOX-1 is attempted
as a THEOREM, not re-boxed — and PROVED at f1 = 1.**

Charge (two legs): (1) GENTOW6-BOX-1 — THEOREM GENTOW-6.3 is
scoped to mu2 = 2; derive and prove the mu2 >= 3 attainment
statement or display the exact obstruction; machine leg at >= 3
frames including FR5X's geometry and a new mu2 = 3 frame. (2)
GENTOW6-BOX-4 — the box's ask verbatim (GENTOW6_PROOF S5): "First
x-ful-digit certificate row (an f1 >= 2 genre with some
c_t*eta^{W(t)} not in F_Q) = the box's ask; until it runs, 6.3' is
prose-only", at SEALED BATTERY grade (the PE2/PE3 instruments are
hostile-arc verifier legs, not sealed apparatus).

Sources consumed (never edited): GENTOW6_PROOF_2026-08-09.md at
HEAD (FROZEN; THEOREM GENTOW-6.3 + its GT6-r1 f1 = 1 scope pin,
ANNEX-THEOREM GENTOW-6.3' (S6.1), the S5 boxes), GENTOW3_PROOF
(THEOREM GENTOW-3 Steps 0-2 — the weight ledger and the k*delta
extraction pricing, stated and proved at GENERAL mu2 on 𝒯; the
functoriality sentence identifying the shadow with the reduced
two-variable division), GENTOW1_PROOF (Step 0 carry monotonicity),
GENHN erratum 59c1966 (corrected chat_t), GENTOW3_passPE5_report.md
@ 0633c6a3 (obs-1: the three measured certificate configurations at
FR5X; the FR5X-3 measured vector G = [2^19*x*Y, 12288*Y, 0], pins
[91, 61, None]); machine: gentow6_pe2_fresh.py (md5
061639c322dfd98a48dc399f07e6dd04, committed PE2 leg — LEG-2 imports
it), gentow3_pe5_fresh.py's committed FR5X values as cross-pins.

## STATUS TABLE

| leg | statement | status |
|---|---|---|
| (1) BOX-1 | THEOREM GENTOW-6.5 (S2) | PROVED at f1 = 1; machine leg GREEN 459/0 (S4); box CLOSED at f1 = 1 |
| (2) BOX-4 | sealed battery rows R1-R4 (S5) | RUN GREEN 265/0; box DISCHARGED (S5) |

## S1. WHAT BOX-1 ACTUALLY ASKS, AND WHAT THE DATA ALREADY SAYS

**The box (GENTOW6_PROOF S5, verbatim core).** "THEOREM 6.3 is
scoped to mu2 = 2. At mu2 >= 3 the source layer has k-fold products
(multinomial coefficients != 1 off the diagonal appear at the top
pair only through (t*,...,t*), coefficient 1 again — the diagonal
argument LOOKS uniform) but the Y-bookkeeping of (a) needs the
k-extraction ledger re-derived; not claimed."

**The box's parenthetical guess is REFUTED by accepted data.** The
top height-THETA branch at mu2 = m >= 3 is NOT a (t*,...,t*)
m-fold product with coefficient 1: it is the DIAGONAL PAIR
{t*, t*} tensored with m-2 leading factors, and its multinomial
coefficient is binom(m,2) = m(m-1)/2. GENTOW3-PE5's accepted FR5X-3
measurement shows exactly this: the attained coordinate's digit is
12288 = 3 * 4096 = binom(3,2) * (the mu2 = 2 digit chat^2 pi^{2a}),
at the SAME height 61 but at coordinate j = 1, not j = 0. The
binomial is the whole new phenomenon: it can VANISH mod p, and then
the top-slot certificate cancels — an arithmetic condition on
(p, m) that has no mu2 = 2 shadow (binom(2,2)... binom(m,2) at
m = 2 is 1, killing no residue).

**obs-1's three configurations are the statement's shape.**
GENTOW3-PE5 obs-1 measured, at FR5X (mu2 = 2 and 3), three distinct
certificate configurations: ATTAINED (FR5X-3 at j = 1, height 61 =
THETA_1), SLACK (FR5X-3 at j = 0: the height-87 = THETA_0 digit
bit-measured ZERO, pin 91), IDENTICALLY-ZERO (FR5X-3 at j = 2;
FR5X-2 at j = 1). A correct mu2 >= 3 attainment theorem must
therefore be TOP-COORDINATE-scoped: it claims attainment at ONE
coordinate j* (with an explicit p-condition), proves the
coordinates above j* identically zero, and leaves the coordinates
below j* as displayed genre arithmetic (their assembly is
multi-branch and can cancel — S3 derives FR5X-3's j = 0 slack
exactly). All three measured configurations become the three
clauses (b), (c), and the S3 display.

## S2. THEOREM GENTOW-6.5 (mu2-general attainment at the top
## coordinate, f1 = 1)

**Setting (GENTOW-6.3's, restated for one pass; f1 = 1 so D' = e1
and the corrected chat_t lifts are scalar monomials).** Tower genre
(Q; e1, 1, mu1; h), key Phi' (deg D' = e1), inner data (u2, e2, f2),
E2 = e2 f2 u2, delta = u2 - e2 D' h >= 1, THETA_j = (m - j) E2 +
delta at mu2 = m; K2(x, Y) = Y^{e2 f2} - Sum_{t in T} chat_t
pi^{a_t} x^{i_t} Y^{e2 t}, T = {t < f2 : chat_t != 0} (0 in T),
t* = max T, all chat_t units, e1 a_t + i_t h = u2(f2 - t) with
0 <= i_t < e1; slot height of a digit c at (a, b) is
e1 e2 * v(c) + w(a, b), w(a, b) = a e2 h + b u2. Self-shadow
object: f = Phi2^m, m = mu2 >= 2; honest composed read DRAIN
(C_j = 0, j < m); shadow ShC_j = [Ghat_j mod Phi'] where Ghat_j is
the exact two-variable division chain of F = dev(Phi2^m) by K2
(functoriality of monic division — GENTOW-3 S2's setting sentence,
consumed; also machine-checked as the dual route P-DUAL, S4).

**Named constants.**

    B* := e2 f2 (m - 2) + 2 e2 t*      (the top pair Y-exponent)
    j* := floor((B* + 1) / (e2 f2)) = (m - 2) + floor((2 e2 t* + 1)/(e2 f2))
    b* := (2 e2 t* + 1) mod (e2 f2)
    a* := 2 i_{t*} - D'                 (when 2 i_{t*} >= D')

> **THEOREM GENTOW-6.5.** For f = Phi2^m (m >= 2) at any f1 = 1
> tower genre, at the corrected chat_t:
>
> (a) [k-EXTRACTION LEDGER + Y-CEILING] Every monomial of F =
> dev(Phi2^m) = CARRY(K2(x,Y)^m) traces to a k-multiset source
> {t_1, ..., t_k} of lift factors (0 <= k <= m) at entry position
> (x^{Sum i_{t_kappa}}, Y^{e2 f2 (m-k) + e2 Sum t_kappa}), source
> coefficient (-1)^k M {m choose the multiset} Prod chat pi^{Sum a},
> with e dev-extractions (each raising Y by exactly 1 and costing
> delta of weight; e <= floor(Sum i / D') <= k - 1). Division steps
> only LOWER the Y-exponent (by e2(f2 - s) >= e2(f2 - t*) > 0 per
> step, s in T) and the terminal reduction mod Phi' is Y-neutral
> (in R = O[x]/(Phi') extracted content is killed, never promoted).
> Consequently every branch of every ShC_j satisfies
>
>     Y <= e2 f2 (m - k) + e2 Sum t + e <= B* + 1 ,
>
> with Y = B* + 1 forcing (k, multiset, e, steps) =
> (2, {t*, t*}, 1, 0).
>
> (b) [CERT-TOP-m] If 2 i_{t*} >= D', the height-THETA_{j*} graded
> digit of ShC_{j*} at slot (a*, b*) is EXACTLY
>
>     binom(m,2) * (chat_{t*})^2 * pi^{2 a_{t*}} * (wrap unit) ,
>
> assembled from the unique branch of (a)'s equality case. Hence:
> (b1) if p does NOT divide binom(m,2) = m(m-1)/2: the digit is
> nonzero in the residue field — the shadow diverges from DRAIN at
> EXACTLY THETA_{j*} at coordinate j*, on the floor (attainment);
> (b2) if p | binom(m,2): the height-THETA_{j*} digit at (a*, b*)
> is ZERO — the top-slot certificate CANCELS, and any content at
> that slot sits strictly above the floor. No attainment is claimed
> under (b2).
>
> (c) [ABOVE-TOP VANISHING] ShC_j == 0 identically (every height)
> for every coordinate j > j*. (Unconditional — no overflow
> hypothesis.)
>
> (d) [NO-OVERFLOW EXACTNESS] If m * max_{t in T} i_t < D', then
> F = K2^m term by term and ShC_j = C_j = 0: the key-power witness
> is shadow-exact.
>
> At m = 2 these specialize to the sealed THEOREM GENTOW-6.3:
> (b1) is 6.3(b) verbatim (binom(m,2) = m(m-1)/2 = 1 at m = 2 —
> no p-condition survives, which is WHY the mu2 = 2 theorem needed
> none, "no binomial coefficient, no characteristic condition" as
> 6.3(b)'s proof says); (b2) is
> empty at m = 2; (c) is the battery's measured ShC_1 = 0 rows
> (A5/A7/C, GEN-R2X/P3/P3b pins (THETA_0, None)); (d)'s hypothesis
> 2 max i_t < D' is 6.3(c)'s "i_t + i_{t'} < D' for every pair"
> verbatim (the pair maximum is the diagonal).

*Proof.*

**Step I (source census — weight m E2, exact).** Every term of K2
has weight E2 exactly (side terms of the key; GENTOW-3 Step 1,
consumed), so every monomial of the multinomial expansion of K2^m
sits at weight m E2 exactly. A monomial chooses the leading term
Y^{e2 f2} from m - k factors and lift terms t_1, ..., t_k from the
rest: position (x^{Sum i}, Y^{e2 f2 (m-k) + e2 Sum t}), coefficient
(-1)^k * (the multinomial count of the multiset) * Prod_kappa
chat_{t_kappa} pi^{a_{t_kappa}}. Since f1 = 1, each i_t <= e1 - 1 <
D', so k <= 1 monomials have x-degree < D' and never overflow:
x-overflowing sources have k >= 2.

**Step II (the CARRY = dev bookkeeping).** F = dev(Phi2^m) is
obtained from K2^m by iterating the x-carry x^{D'} = Y + tail
(tail = x^{D'} - Phi' as an x-polynomial of degree < D', evaluated
at Y = Phi' this is an identity; GENTOW-1 Step 0's split, consumed:
tail branches at weight >= parent with equality exactly on the
key's side terms, the Y-branch at parent + delta exactly). Each
extraction consumes exactly D' of x-degree and tail steps strictly
lower x-degree, so a source of x-degree I admits at most
floor(I / D') extractions along any branch; with I = Sum i <=
k(e1 - 1) < k D' this gives e <= k - 1. Entry Y-exponents of F's
monomials are therefore e2 f2 (m-k) + e2 Sum t + e with those
constraints.

**Step III (reduction to Delta; the Y-ceiling).** Set Delta :=
F - K2^m. The exact division is O[x]-linear in the dividend, and
the iterated division of K2^m by K2 is exact with Ghat_j = 0 for
every j < m; hence Ghat_j(F) = Ghat_j(Delta) for j < m — ONLY
Delta's monomials feed the shadow coordinates. Delta =
Sum_{overflowing sources mu} (CARRY(mu) - mu), and by Step I every
overflowing source has k >= 2. Per source, CARRY(mu)'s branches
split as: extracted branches (e >= 1) at Y = entry(mu) + e, and
the single e = 0 iterated-tail branch (in-grid) at Y = entry(mu);
the -mu term also sits at Y = entry(mu). So every Delta-monomial
has

    Y <= entry(mu) + e <= e2 f2 (m-k) + k e2 t* + (k-1)
       = B* + 1 - (k - 2)(e2 (f2 - t*) - 1)  <=  B* + 1

(k >= 2; e2(f2 - t*) >= 1 since t* < f2), with Y = B* + 1 forcing
k = 2, e = 1, and e2 Sum t = 2 e2 t*, i.e. the diagonal multiset
{t*, t*} (t <= t* termwise). The iterated exact division of Delta
by K2 (monic in Y of degree e2 f2) routes each monomial either
through the top term (Y^N lands at coordinate floor(N / e2 f2),
in-coordinate slot b = N mod e2 f2, coefficient unchanged) or
through a lift term of K2 (Y-change -e2(f2 - s) < 0, coefficient
multiplied by that lift coefficient, weight floor preserved —
GENTOW-3 Step 1's weight-monotone division, consumed); no step
raises Y. The terminal reduction ShC_j = [Ghat_j mod Phi']
substitutes x^{D'} |-> tail inside coefficients: in R the Phi'-part
of an x-overflow is ZERO (Phi' = 0 in R) — the reduction is the
pure iterated tail route and never promotes content to a higher b.
This proves (a), and (c) follows: coordinate-j content needs
Y >= j e2 f2, and j > j* gives j e2 f2 >= (j* + 1) e2 f2 > B* + 1
(definition of floor as an integer inequality) — no Delta-branch
reaches any height there. No overflow hypothesis was used: with no
overflowing source, Delta = 0 outright.

**Step IV (the unique top branch and its digit = (b)).** At the
height-THETA_{j*} graded layer, GENTOW-3 Step 2's ledger (accepted
at general mu2) prices every branch at weight m E2 + (number of
extractions) * delta, so the layer carries e = 1 branches with
every other step weight-exact. A height-THETA branch landing at
slot (a*, b*) of coordinate j* has Y = j* e2 f2 + b* = B* + 1: by
(a)'s equality case it is the diagonal pair source {t*, t*} with
its single extraction and no division steps. Its source monomial —
x-position 2 i_{t*}, Y-position B*, coefficient binom(m,2)
(-chat_{t*})^2 pi^{2 a_{t*}} = binom(m,2) chat_{t*}^2 pi^{2 a_{t*}}
— is UNIQUE at that (x, Y)-position among all sources: a k = 2
non-diagonal multiset at Y-position B* would need t + t' = 2 t*
with t, t' <= t*, forcing the diagonal; a k >= 3 multiset there
would need f2 (k - 2) = Sum t - 2 t* <= (k - 2) t*, i.e. f2 <= t*,
contradiction. Its carry: 2 i_{t*} < 2 D' (i < e1 = D' twice), so
the first rewrite's Y-branch has coefficient exactly 1 and x-part
a* = 2 i_{t*} - D' < D', in-grid — the branch terminates with ONE
extraction; the parallel tail branches carry e = 0 (Step V). Direct
route through the division (zero steps): coordinate j*, slot b*,
coefficient unchanged; weight m E2 + delta reads at coordinate j*
as height (m - j*) E2 + delta = THETA_{j*}; the coherent normalizer
contributes its wrap unit (GENTOW-6.3(b)'s clause, unchanged). So
the graded digit at (a*, b*) at height THETA_{j*} is binom(m,2)
chat_{t*}^2 pi^{2 a_{t*}} (wrap unit) exactly. chat_{t*}, the wrap,
and pi^{2a} normalization are units, so the residue digit is zero
iff p | binom(m,2). If p does not divide it: nonzero digit at
exactly the floor height (GENTOW-3(i) forbids anything lower):
divergence at exactly THETA_{j*} — (b1). If p | binom(m,2): the
graded layer at that slot is zero and slot content, if any, sits
strictly above — (b2). Branches at the same Y = B* + 1 do not
exist besides this one (equality case); same-height branches at
other Y land at other slots; multi-extraction branches (k >= 3
sources with e = 2 can reach Y = B* + 1 only when e2(f2 - t*) = 1)
cost >= 2 delta of weight and sit strictly above the graded layer —
they cannot touch the height-THETA digit. ∎(b)

**Step V (tail/source pairs cancel exactly; (d)).** Within Delta,
each source mu contributes the pair (its e = 0 iterated-tail
branch, -mu), both at the same Y-position. Division routes depend
on Y alone and are coefficient-linear, so the two members of the
pair arrive at every Ghat_j at the same slots, carrying (tail
image of mu's coefficient) and (-mu's coefficient) respectively;
the terminal reduction mod Phi' maps -mu's coefficient to exactly
minus the iterated tail image (the reduction IS the iterated tail
substitution): the pair cancels coefficientwise in every ShC_j.
Every surviving ShC-monomial therefore traces to an EXTRACTED
branch (e >= 1) — this is the sealed 6.3(a)'s "tail-only routes
are shared by both reads and cancel", re-derived m-generally. For
(d): if m * max i_t < D', every monomial of K2^m has x-degree
Sum i <= k max i <= m max i < D': no source overflows, CARRY is
the identity, F = K2^m, the exact division has Ghat_j = 0 for
j < m, and ShC_j = 0 = C_j. ∎

**COROLLARY GENTOW-6.5C (obs-1 explained).** At FR5X (p = 2,
e2 = 2, f2 = 1, t* = 0, i_0 = 1, a_0 = 6, chat = 1, D' = 2,
delta = 9, E2 = 26): (i) m = 2: j* = 0, digit binom(2,2)... = 1 *
2^{12} = 4096 at (0,1), height 61 = THETA_0, ShC_1 == 0 — the
measured [4096*Y, 0]. (ii) m = 3: j* = 1, digit binom(3,2) * 4096
= 12288 at (0,1) of coordinate 1, height 61 = THETA_1 (p = 2 does
not divide 3): attainment; ShC_2 == 0; coordinate 0 is below j*
and its assembly cancels at the graded layer (S3): slack with pin
91. The measured [2^19*x*Y, 12288*Y, 0] realizes all three
configurations of one theorem. ∎

## S3. THE LOWER COORDINATES (j < j*): DISPLAYED GENRE ARITHMETIC,
## NOT A THEOREM CLAUSE — obs-1's SLACK derived exactly

Below j*, height-THETA_j content assembles from SEVERAL branches
(direct k >= 3 extractions and division-stepped pair branches meet
at the same slots) and its vanishing is genre arithmetic — the
mu2 >= 3 analogue of the sealed quadrichotomy's regime-(3) display.
Worked at FR5X-3, coordinate 0, slot (1,1) (the measured slack):

* the TRIPLE direct branch: source (-chat nhat)^3 with multinomial
  binom(3,3) = 1: -(2^6 x)^3 = -2^18 x^3 at Y^0; x^3 = x*x^2
  extracts once (3 < 2 D') to -2^18 x at Y^1, slot (1,1), v = 18,
  height 4*18 + w(1,1) = 72 + 15 = 87 = THETA_0;
* the STEPPED PAIR branch: the top branch's content binom(3,2) *
  4096 at Y^3 takes one division step through the lift term -64x
  (Y-change -2, coefficient * 64x, sign + from subtracting
  quotient*K2): +3 * 2^18 x at Y^1, same slot (1,1), same height 87.

Assembly: (-1 + 3) * 2^18 x = +2^19 x — the graded height-87 digit
is (-1 + 3) mod 2 = 0: CANCELLED (p = 2 kills the pair-minus-triple
arithmetic), and the slot VALUE 2^19 x sits at height 91. This IS
obs-1's measured slack row (G_0 = 2^19 x Y, pin 91 > 87 = THETA_0),
now derived from the ledger. The general j < j* classification
(which genres cancel at which lower coordinates) is finite
arithmetic per (genre, m, j), displayed only — it extends
GENTOW6-BOX-3's regime-3 fence to mu2 >= 3 and is NOT claimed as a
theorem; obs-1 shows it is genuinely conditional (the same genre
attains at j* while cancelling at j = 0).

**ANNEX-REMARK GENTOW-6.5' (f1-general form; prose grade).** At
f1 >= 2 read the corrected lifts as (LIFT) shapes (GENTOW6_PROOF
S6.1) and replace, exactly as ANNEX-THEOREM GENTOW-6.3' does at
m = 2: the census runs over MONOMIAL k-multisets (one monomial from
each chosen digit's x-support {i_t + e1 r : lambda_{t,r} != 0});
I_t := i_t + e1 r_max(t); the top slot is (2 I_{t*} - D', b*) at
coordinate j* under 2 I_{t*} >= D', with digit binom(m,2) *
lift(lambda_{t*,r*})^2 * pi^{2(a_{t*} - r* h)} * (wrap unit) — the
same three localized deltas as 6.3' ((i) Y-uniqueness is x-shape-
blind, (ii) max-forces-diagonal on the monomial pair (r*, r*),
(iii) the digit a unit multiple with the SAME binom(m,2) residue
condition — Step II's extraction count e <= floor(Sum I / D') <=
k - 1 survives since each lift monomial has x-degree <= I_t <=
D' - 1). Grade: prose at this note's 0/2, riding accepted 6.3'
(itself machine-contacted at m = 2 only — S5's row); no m >= 3
f1 >= 2 machine contact exists anywhere; named honestly, not
claimed beyond the display.

## S4. MACHINE LEG — BOX-1 (gentow6_box1_mu3.py, two-commit seal)

Runner: `verification/openmath/gentow6_box1_mu3.py` — self-
contained integer-exact primitives (own code; no import of any
sealed runner). SEVEN frames on FOUR geometries:

    X3  = FR5X geometry (Q2, Phi' = x^2-2, e2 = 2, f2 = 1, u2 = 13,
          Phi2 = Phi'^2 - 64x) at mu2 = 3   [obs-1's geometry]
    X4  = same at mu2 = 4                    [p | binom(4,2) = 6]
    A53 = FAM-A5 genre (u2 = 5, Phi2 = Phi'^2 - 4x) at mu2 = 3
    B3  = FAM-B genre (Q2, e2 = 1, f2 = 2, u2 = 3, T = {0,1},
          t* = 1, Phi2 = Phi'^2 - 2x Phi' - 8) at mu2 = 3
          [the f2 >= 2 / t* > 0 / j* = m-1 axis]
    P33/P34/P35 = GEN-P3 genre (Q3, Phi' = x^2-3, u2 = 5,
          Phi2 = Phi'^2 - 18x, chat = 2) at mu2 = 3, 4, 5
          [odd p; p | binom(3,2) and p | binom(4,2) both live]

DUAL ORACLES: (R) the reduced division route (coefficients reduced
mod Phi' at every step — the shadow's own definition) vs (E) the
EXACT two-variable division with one terminal reduction (the
proof's Step III object) — bit-equality of every slot dict is the
functoriality face of the proof, checked per frame and per member;
plus PARI/gp decorrelation rows (factorpadic carriers, poldisc).

PREREGISTERED PREDICTIONS (sealed in the runner docstring at
commit 1, before the first run) — P-DUAL, P-X3 (the committed PE5
vector {(1,1): 2^19}@j0 / {(0,1): 12288}@j1 / 0@j2, pins
[91, 61, None], graded 87-digit zero at (1,1)@j0, graded 61-digit
nonzero at (0,1)@j1), P-X4 (v((0,1)@j2) = 13 exactly: graded
THETA_2 = 61 digit ZERO, 65-digit nonzero; pin(ShC_2) = 65;
ShC_3 == 0), P-A53 (v((0,1)@j1) = 4, pin 21 = THETA_1, ShC_2 == 0),
P-B3 (v((0,1)@j2) = 2 AND v((1,0)@j2) = 3 — TWO slots at height
7 = THETA_2; pin(ShC_2) = 7), P-P33/P-P34 (graded THETA digit at
the top slot ZERO — binom(3,2) and binom(4,2) both = 0 mod 3),
P-P35 (v((0,1)@j3) = 4, pin 21, ShC_4 == 0; binom(5,2) = 10 a
3-unit), P-FLOOR (every frame, every j: pin(ShC_j) >= THETA_j or
None), P-TOP (ShC_j == 0 at every j > j* per frame), P-PERS (deep
in-budget perturbations above THETA keep every mindiff_j), P-PARI
(carriers {(4,1)} at X/P3 geometries, {(2,2)} at B; poldisc != 0
on perturbed members). TEETH: T-ALLM (mutant "attainment whenever
2 i_{t*} >= D', every m" — must die at X4/P33/P34), T-COEF (mutant
coefficient m for binom(m,2) — must die at X4 (v = 14 vs 13) and
P34 (4 a 3-unit vs 6 = 0)), T-VAL (v* - 1 mutant at the four
attainment frames), T-TOPZ (mutant "content above j*" at the six
frames with j* < mu2 - 1).

**RESULTS (verdict commit; seal 78ac4e82 @ 2ae94ded, run-1 RED
kept at gentow6_box1_mu3_output_run1_RED.txt md5 a0fb948d): run 2
GREEN — 459 checks, 0 violations, teeth kill counts EXACT
(T-ALLM 3, T-COEF 2, T-VAL 7, T-TOPZ 6); isolated re-run
BIT-IDENTICAL (fresh /tmp scratch); repaired runner md5 c98cb423,
output md5 0a4cd16f.** Run-1 RED = 3 INSTRUMENT literals, all
hand-traced before repair and disclosed in the runner docstring, NO
theorem-facing want changed: (i) my B3 display-slot want claimed
the value at (1,0)@j2 was the triple branch -8 EXACTLY; measured
40 = -8 + 48 — at e2(f2 - t*) = 1 a division step lowers Y by one
and stays INSIDE the coordinate band, so the top branch's stepped
content (+48x, v = 4, height 9) shares the slot; the graded
height-7 = THETA_2 digit is -1 (the triple alone) and v_2(40) = 3,
both exactly the ledger's claim — the corrected want (v = 3,
graded nonzero) is what the ledger licenses, and the CERTIFICATE
slot (0,1) measured 12 exact on run 1 already; (ii)+(iii) the two
poldisc-0 rows had drawn j' >= 2 perturbations (Phi2 a repeated
factor by construction — poldisc 0 is correct there); the disc row
is now the dedicated j' = 0 member. Run-2 highlights, each
preregistered: the committed PE5 FR5X-3 vector reproduced
bit-exactly on both routes; X4's top slot 24576 with v = 13 (the
p = 2 | binom(4,2) cancellation, pin 65 = THETA_2 + e1e2); A53's
48 = 3 * 16 at pin 21; B3's certificate 12 = 3 * 4 at pin 7 with
the second THETA slot (1,0) graded -1; P33/P34's odd-p
cancellations (972 = 4*3^5, 1944 = 8*3^5: graded 21-digit zero,
pins 25) vs P35's return of attainment (3240, v = 4, pin
21 = THETA_3); P33's j0 attained at 31 with value 11664 = 2^4*3^6
(the S3 assembly -1+3 = 2 a 3-unit) while A53/X3's j0 cancelled at
p = 2 (128/524288, pins 35/91); every ShC_j above j* empty at the
six frames carrying one; routes R and E slot-identical at 125
coordinate comparisons; floors held at 125 rows; 128 persistence
checks on 28 perturbed members; 11 PARI jobs GREEN (carriers
{(4,1)}/{(4,1)}/{(2,2)}/{(4,1)}, four nonzero poldiscs).

## S5. BOX-4 — THE SEALED BATTERY-GRADE x-FUL-DIGIT CERTIFICATE ROW
## (gentow6_box4_row.py, two-commit seal)

**The box's ask (GENTOW6_PROOF S5 + the post-PE3 fold, verbatim
scope).** A SEALED BATTERY-grade certificate row at an f1 >= 2
genre with some c_t eta^{W(t)} not in F_Q — the PE2/PE3 fresh
instruments exercised 6.3'(b')'s display as hostile-arc verifier
legs, so the box stayed OPEN pending a row of the note's own
sealed apparatus.

Runner: `verification/openmath/gentow6_box4_row.py`, importing the
COMMITTED gentow6_pe2_fresh.py (md5 of record
061639c322dfd98a48dc399f07e6dd04, never edited) for its integer
primitives + gp bridge, plus its own dual R/E shadow routes as in
S4. Geometry (PE2's LEG A, reused): Q2, Phi' = x^4 + 2x^2 + 4
(e1 = 2, f1 = 2, h = 1, D' = 4; eta = res(x^2/2), eta^2 + eta + 1
= 0, K = F_4). FOUR rows at mu2 = 2:

    R1 = u2 = 9,  c_0 = eta:    Phi2 = Phi'^2 - 8x^3   [PE2 reprod.]
    R2 = u2 = 9,  c_0 = 1+eta:  Phi2 = Phi'^2 - 8x^3 - 16x  [PE2 r.]
    R3 = u2 = 11, c_0 = eta:    Phi2 = Phi'^2 - 16x^3  [NEW ROW]
    R4 = u2 = 11, c_0 = 1+eta:  Phi2 = Phi'^2 - 16x^3 - 32x [NEW]

R3/R4 constants (hand ledger, preregistered): nhat(11): i_0 = 1,
a_0 = 5; W(0) = 0; lambda(eta) = (0,1), lambda(1+eta) = (1,1);
I_0 = 3, 2 I_0 = 6 >= D'; E2 = 22, delta = 3, THETA_0 = 47;
w(a, b) = 2a + 11b. 6.3'(b') certificate: slot (a*, b*) = (2, 1)
at j* = 0, digit lift(lambda_{0,1})^2 * 2^{2(5-1)} = 256, v = 8,
height 4*8 + w(2,1) = 47 = THETA_0 — divergence EXACTLY on the
floor. Predicted full vectors (ledger-derived pre-seal): R3:
ShC_0 = {(2,1): 256, (0,1): -512}; R4: ShC_0 = {(2,1): 256,
(0,1): 512} (the mixed monomial pair (r,r') = (0,1) of the single
digit t = 0 feeds (0,1) with opposite-sign tail routing, the
x^4-overflow +1024 Y against the x^6 chain's -512 Y); R1/R2: PE2's
committed {(2,1): 64, (0,1): -128} / {(2,1): 64, (0,1): 128};
honest read DRAIN at all four; pins = THETA_0 exactly at all four;
ShC_1 == 0 at all four (the (c)-face: B* + 1 = 1 < 2 = e2 f2).
PERTURBATION SWEEP: 10 deep in-budget perturbations per row keep
mindiff_0. PARI: dev cross-check per row (gp divrem), factorpadic:
Phi' one factor (4, f 2); each Phi2 one factor deg 8; poldisc != 0
on perturbed rows. TEETH: T-F1EVAL (the f1 = 1-evaluation mutant —
reads the digit as chat pi^a x^i, i_0 = 1: predicts NO overflow
(2 i_0 = 2 < 4 = D') hence shadow-exactness: must die at ALL FOUR
rows), T-VAL2 (v* - 1 at the certificate slot, 4 rows), T-SLOT
(mutant b* = 0: the slot (a*, 0) graded read must NOT carry the
certificate).

**RESULTS (verdict commit; seal c0fbd1e4 @ 90b23648, run-1 RED
kept at gentow6_box4_row_output_run1_RED.txt md5 0269e02e): run 2
GREEN — 265 checks, 0 violations, teeth kill counts EXACT
(T-F1EVAL 4, T-VAL2 4, T-SLOT 4); isolated re-run BIT-IDENTICAL;
repaired runner md5 9d6e16cc, output md5 2d8d617a.** Run-1 RED = a
single gp want-string literal (my want rendered the zero dev slot
as [0] where gp's Vecrev(0) prints []; the four DEV jobs mismatched
on that token with every printed coefficient identical), disclosed
in the docstring; the 24 QCERT + 8 QDEV + 88 QDUAL + 120 QPERS +
12 teeth + 9 non-DEV GP checks were GREEN already on run 1; no
prediction changed. Run-2 highlights, each preregistered: the four
x-ful-digit certificate rows measured EXACTLY the 6.3'(b') display
— ShC_0 = {(2,1): 64, (0,1): -128} / {(2,1): 64, (0,1): 128} /
{(2,1): 256, (0,1): -512} / {(2,1): 256, (0,1): 512} with cert
digits 64/64/256/256 at v = 6/6/8/8 = 2(a_0 - r* h) and pins
37/37/47/47 = THETA_0 exactly on the floor (R3/R4 the FIRST
u2 = 11 x-ful rows anywhere); honest DRAIN and ShC_1 empty at all
four (the above-top face); dev vectors triple-confirmed (own
route, the committed pe2.dev path, gp divrem); 40 perturbed
members held mindiff_0 at the floor with mindiff_1 clean; PARI
carriers {(2,2)} for Phi' and {(4,2)} for all four Phi2 (R3/R4 new
keys), four nonzero poldiscs; the f1 = 1-evaluation mutant
(predicting shadow-exactness from 2 i_0 = 2 < D') died at every
row.

**GENTOW6-BOX-4 DISCHARGE.** The box's ask — a SEALED
BATTERY-grade x-ful-digit certificate row — has now RUN: sealed
apparatus (two-commit seal, preregistered wants, teeth, dual
oracles, perturbation sweeps), four rows, GREEN. ANNEX-THEOREM
GENTOW-6.3' loses its "machine-unexercised at f1 >= 2 /
prose-only" fence at mu2 = 2: its (b') display now has
sealed-battery machine contact at four x-ful digit data on two
u2 values. What the discharge does NOT claim: 6.3' remains a prose
derivation at its note's grade (machine contact is evidence, not
proof), and the f1 >= 2 x mu2 >= 3 compound (ANNEX-REMARK 6.5')
stays machine-uncontacted — named in S6.

## S6. RESIDUE + GRADE BOX

* **Delivered:** BOX-1 = THEOREM GENTOW-6.5, PROVED at f1 = 1
  (the box's k-extraction ledger = clause (a); the attainment
  claim = (b1) with the binom(m,2) p-condition the box's own
  parenthetical missed; obs-1's three configurations =
  (b1)/(b2)+S3/(c)), machine leg GREEN 459/0 at 7 frames — box
  CLOSED at f1 = 1. BOX-4 = the sealed battery-grade x-ful-digit
  rows R1-R4, GREEN 265/0 — box DISCHARGED.
* **NOT delivered / named:** the j < j* lower-coordinate
  classification at mu2 >= 3 (S3 display only — genre arithmetic,
  extends GENTOW6-BOX-3's fence; no new box needed: it is BOX-3's
  geography one m up); the f1 >= 2 x mu2 >= 3 compound (ANNEX-
  REMARK 6.5', prose only, no machine contact — a NEW honest fence
  since BOX-4's leg is mu2 = 2).
* **Statement fence:** no sealed display of GENTOW6_PROOF is
  edited; this note is a separate instrument + the frozen note
  gains only dated appends.

**Record sentences (no universal quantifiers).** The BOX-1 battery's
459 checks passed with 0 violations on the seven constructed frames
named in S4, with the four preregistered kill counts exact; the
committed PE5 FR5X-3 vector was reproduced bit-identically on both
routes; the binom(m,2) digits measured 12288, 24576, 48, 12, 972,
1944, 3240 at the seven top slots, each at its predicted valuation;
the three p | binom(m,2) rows cancelled in grade and the four
p-unit rows attained their floors exactly; the six above-top
coordinates measured empty. The BOX-4 battery's 265 checks passed
with 0 violations on the four x-ful rows; the four certificate
digits 64, 64, 256, 256 sat at v = 6, 6, 8, 8 with pins 37, 37,
47, 47 on the floor; the f1 = 1-evaluation mutant died at each of
the four rows.

**GRADE: 0/2 (attempt).** Hostile arc owed. Natural PE1 targets:
Step III's linearity reduction (Ghat_j(F) = Ghat_j(Delta)), Step
IV's uniqueness-at-the-slot, the S3 sign conventions, and the R3/R4
hand ledgers.

---

# APPEND (same unit family, new agent): GENTOW6-BOX-2 (the count
# ledger) + GENTOW6-BOX-3 (regime-3 classification), 2026-08-10

**STATUS (this append): BOTH BOXES PROVE-FIRST DELIVERED — S7 =
THEOREM GENTOW-6.6 (the window count ledger pricing (f_S, g) ↦
f_S·g, the box's own Jacobian/content identity, PROVED with an
explicit N_0) + S8 = THEOREM GENTOW-6.7 (regime-3 top-slot
classification at mu2 = 2) with COROLLARY-THEOREM GENTOW-6.7C (the
j*-1 band one m up — the (binom(m,2) - binom(m,3)) law). Machine
legs S9 (two sealed runners, two-commit each). Grade of the append:
0/2 (attempt; hostile arc owed), riding the frozen notes it cites.**

## S7. GENTOW6-BOX-2 — THE COUNT LEDGER (THEOREM GENTOW-6.6)

**The box verbatim (GENTOW6_PROOF S5).** "GENTOW6-BOX-2 (the count
LEDGER at partial sides). From S2: the product-measure count of the
f-locus per window (pricing (f_S, g) ↦ f_S·g) — open already at
FULL sides (GENTOW-1's count-law remark), not a partial-side
novelty." S2's parked sentence sharpens the ask: "the count of f's
per window as a product over (class boxes) x (sibling data), which
requires pricing the multiplication map (f_S, g) ↦ f_S·g on ambient
windows (a Jacobian/content identity)."

**What is proved here.** Exactly that pricing: the Jacobian of the
multiplication map IS the Sylvester matrix, its content is the
resultant, the resultant valuation is a GENRE CONSTANT c_J on the
box pair (residual separation), and for explicit window depths the
per-window count of the product locus is the product of the
GENTOW-1(b) clipped box counts divided by q^{c_J}. What is NOT
claimed: the GENH5-DENS-style per-genre AGGREGATION over keys and
genres (summing cells to densities) — a different seam, named in
S10; at a one-class (full-side) locus there is no product to price
and the ledger is GENTOW-1(b) + its R2a clip verbatim.

**Setting.** O = the ring of integers of the base local field Q of
the genre, pi its uniformizer, q = |O/pi|, v = the valuation with
v(pi) = 1. Monic polynomials of degree d are identified with
coefficient vectors in O^d. For a compact open B ⊆ O^d, the
window-N count is #(B mod pi^N) := the number of pi^N-classes
meeting B. HYPOTHESES on a pair of "boxes" B_S (degree d_S), B_g
(degree d_g), d := d_S + d_g:

* (H1) [CELLS] each box is a union of pi^H-balls in its coefficient
  space (one H for both). [The bouquet budget boxes qualify with
  H = the max digit floor: GENTOW-1(b)'s composed-digit coordinates
  are triangular-unimodular in the coefficients — a bijection of
  O^{d} that is 1-Lipschitz with 1-Lipschitz inverse, hence
  carrying pi^N-classes to pi^N-classes and cells to cells.]
* (H2) [SEPARATION] v(Res(u, w)) = c, one finite constant, for
  every (u, w) ∈ B_S x B_g.
* (H3) [INJECTIVITY] (u, w) ↦ u·w is injective on B_S x B_g.

> **THEOREM GENTOW-6.6 (the window count ledger).** Under (H1)-(H3),
> with m(u, w) := u·w (monic, degree d):
>
> (a) [SYLVESTER-JACOBIAN] the derivative of m at (u, w) is the
> O-linear map (alpha, beta) ↦ u·beta + w·alpha (deg alpha < d_S,
> deg beta < d_g); its matrix in the monomial bases is the
> Sylvester matrix Syl(u, w), so det(dm) = ±Res(u, w) and
> |det dm| = q^{-c} on the box pair. The elementary divisors
> pi^{e_1}, ..., pi^{e_d} of dm satisfy Sum e_i = c, each e_i <= c,
> hence dm(O^d) ⊇ pi^c O^d.
>
> (b) [BALL IMAGE] for k >= c + 1 and (u, w) in the box pair:
>
>     m((u, w) + pi^k O^d) = u·w + dm_{(u,w)}(pi^k O^d)
>
> exactly — an affine coset containing u·w + pi^{k+c} O^d, of
> measure q^{-dk-c}.
>
> (c) [LEDGER] for N >= N_0 := c + max(c, H) + 1:
>
>     #(m(B_S x B_g) mod pi^N)
>         = q^{-c} · #(B_S mod pi^N) · #(B_g mod pi^N),
>
> and each fiber of the window map (pairs mod pi^N over one image
> class) has exactly q^c members.
>
> (d) [BOUQUET INSTANTIATION — the box's geography] at a two-class
> partial-side geography (S1/S2's setting: level-1 polygon one side
> of slope kappa2, twist-coherent residual psi2^{mu2*} · r^{m'},
> psi2 != r irreducible), take B_S := the GENTOW-6.2 block budget
> box at the psi2-block genre (LEMMA GENTOW-1(a)(b) floors at
> mu2 ↦ mu2*), B_g := the same at the r-class genre (mu2 ↦ m',
> key Phi2' of the r-class). Then (H2) holds with the closed form
>
>     c = c_J := mu2* · m' · D2 · E2 / (e1 e2)
>       [ = deg(f_S) · m' E2/(e1e2) = deg(g) · mu2* E2/(e1e2),
>         an integer: c_J = mu2* m' f1 f2^2 e2 u2 ],
>
> (H3) holds, and with the bouquet factorization (every locus
> member factors into box members: LEMMA GENTOW-6.2 + HE6R1-2(b),
> at their notes' grades) the partial-side locus L satisfies, for
> N >= N_0:
>
>     #(L mod pi^N) = q^{ Sum_{S-box slots} max(0, N - floor)
>                       + Sum_{g-box slots} max(0, N - floor) - c_J }.
>
> Multi-class bouquets iterate pairwise (Res is multiplicative in
> each argument, so the constants ADD over class pairs).

*Proof.*

**(a).** m is bilinear plus the base point: m(u + alpha, w + beta)
= uw + (u beta + w alpha) + alpha·beta; the linear part in the
monomial bases x^i·(coefficient columns) is precisely the classical
Sylvester layout (columns = shifts x^i·u, x^j·w), whose determinant
is ±Res(u, w) — the Sylvester identity. |det| = q^{-c} by (H2).
The elementary divisor sum is v(det) = c and each single divisor is
at most the sum since all are >= 0. dm(O^d) ⊇ pi^c O^d follows
slotwise from the Smith normal form. ∎(a)

**(b).** (⊇) Given target uw + dm(z), z ∈ pi^k O^d: solve
m((u,w) + x) = uw + dm(z) for x ∈ pi^k O^d by Newton iteration
x_0 := z, x_{n+1} := z - dm^{-1}(Q(x_n)) where Q(alpha, beta) :=
alpha·beta is the quadratic part and dm^{-1} denotes a choice of
preimage with ||dm^{-1}(y)|| <= q^c ||y|| (Smith form; possible for
y ∈ dm(O^d), and Q(x) ∈ pi^{2k}O^d ⊆ pi^{k+c+1}O^d ⊆ dm(pi^{k+1}O^d)
since 2k >= k + c + 1). The iteration is a contraction on pi^k O^d
(successive differences shrink by q^{-(k-c)} <= q^{-1} per step:
||Q(x_n) - Q(x_{n-1})|| <= q^{-k}||x_n - x_{n-1}||, then dm^{-1}
costs q^c), so it converges in the complete lattice to an exact
solution. (⊆) m((u,w) + x) - uw = dm(x) + Q(x) ∈ dm(pi^k O^d) +
pi^{2k} O^d = dm(pi^k O^d) by the same containment. The coset
contains uw + pi^{k+c}O^d by (a)'s last clause scaled by pi^k, and
its measure is |det dm| · q^{-dk}. ∎(b)

**(c).** Set k := max(c + 1, H). By (H1) the box pair is a disjoint
union of P_k := #(B_S mod pi^k) · #(B_g mod pi^k) balls of radius
pi^k. By (b) each ball maps ONTO an affine coset of measure
q^{-dk-c}; by (H3) these images are pairwise disjoint. For
N >= k + c each coset is a union of pi^N-balls (it contains a
pi^{k+c}-ball around each member, and is a coset of a lattice
⊇ pi^{k+c}O^d ⊇ pi^N O^d), numbering q^{dN} · q^{-dk-c} each. So
#(image mod pi^N) = P_k · q^{d(N-k) - c} = q^{-c} · #(B_S mod pi^N)
· #(B_g mod pi^N), the last step because above depth k every
pi^k-class of a box splits into exactly q^{d_box(N-k)} classes
(balls). FIBERS: fix an image class F = f + pi^N O^d (inside one
ball-image coset, uniquely, by disjointness). m is 1-Lipschitz
(integral polynomial), so m^{-1}(F) ∩ (the ball) is pi^N-saturated,
and it is carried bijectively onto F by m with the coset's constant
scaling; its measure is q^{-dN} · q^{+c} (inverse Jacobian), hence
it meets exactly q^c pi^N-classes. ∎(c)

**(d).** THE SEPARATION LEMMA (GENTOW-6.6a): for f_S ∈ B_S, g ∈
B_g, and any root x0 of f_S: v(g(x0)) = m' E2 / (e1 e2). Proof: x0
is a tower-node point of the genre (full inner side at the block —
LEMMA GENTOW-6.2 puts f_S on 𝒯* and GENTOW-1 Step 4 reads
v(Phi'(x0)) = u2/(e1e2) with eta2(x0) a psi2-root). Evaluate g
through its level-1 read g = Sum_J A_J Phi'^J: every side slot
ties at value mu1' u2/(e1e2) (side of slope kappa2 = u2/e2 in
dv-heights, J-term value (mu1'-J)u2/(e1e2) + J u2/(e1e2)), slots
above the side sit strictly higher, and the height-graded sum of
the tied side terms is (coherent unit) · r^{m'}(eta2(x0)) — the
same coherent-normalizer side-residual computation as GENTOW-1(d),
one class over. Since r != psi2 are distinct irreducibles and
eta2(x0) is a psi2-root, r^{m'}(eta2(x0)) != 0 in the residue
field: the ultrametric minimum is attained exactly once in grade,
so v(g(x0)) = mu1' u2/(e1e2) = m' E2/(e1e2), constant across both
boxes. Then v(Res(f_S, g)) = Sum over the deg(f_S) = mu2* D2 roots
= c_J, and the displayed symmetric/integral forms are arithmetic
(D2 = e2 f2 e1 f1, E2 = e2 f2 u2). (H3): a common root of f_S and
g would carry an eta2-residue killing both psi2 and r —
impossible; so in u·w = u'·w' the root multiset splits by residual
class, forcing u = u' (monic with the same roots with multiplicity)
and w = w'. Injectivity across distinct pairs with the same
product: the same argument. The ledger display then composes (c)
with GENTOW-1(b)'s clipped counts (R2a form) at each box, both
clips inactive at N >= N_0 >= H. For multi-class: multiply blocks
in one at a time; at each step the "sibling" is a product of
blocks, its evaluation constant at a fixed root class is the SUM
of the per-class constants (v(g g')(x0) = v(g(x0)) + v(g'(x0)),
each priced by the lemma), which is Res-multiplicativity. ∎

**Honest fences.** (i) The theorem prices the MULTIPLICATION; it
does not aggregate cells over genres/keys (GENH5-DENS geography —
named residue, S10). (ii) (d) consumes LEMMA GENTOW-6.2 (this
arc), COR GENTOW-4.C's discharge (GENTOW4 ACCEPTED 2/2), HE6R1-2(b)
and GENTOW-1(a)(b)(d)+R2a (GENTOW1 ACCEPTED 2/2) at their recorded
grades. (iii) N_0 is a sufficient depth, not claimed sharp; below
N_0 the machine leg records exploratory rows without wants.
