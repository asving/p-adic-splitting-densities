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
> with Y = B* + 1 forcing zero division steps, the all-t* multiset
> {t*, ..., t*}, and e = k - 1. When e2(f2 - t*) >= 2 this pins
> (k, multiset, e, steps) = (2, {t*, t*}, 1, 0); at e2(f2 - t*) = 1
> geometries every k >= 3 with k i_{t*} >= (k - 1) D' contributes a
> further equality branch (k, {t*, ..., t*}, k - 1, 0), and each
> such branch lands at x-slot <= k i_{t*} - (k - 1) D' < a* (each
> extraction consumes exactly D' of x-degree; i_{t*} < D') at
> weight m E2 + (k - 1) delta >= m E2 + 2 delta, strictly above the
> height-THETA_{j*} graded layer. [r1 2026-08-10: sentence
> corrected per passPE1 F-1 — the sealed sentence forced
> (2, {t*, t*}, 1, 0) unconditionally; refuted at the
> e2(f2 - t*) = 1 frame CE3 (S11), where the k = 3 all-t* source
> -8 x^6 Y^3 extracts twice to -8 Y^{B*+1} at x-slot 0 != a* = 1.]
>
> (b) [CERT-TOP-m] If 2 i_{t*} >= D', the height-THETA_{j*} graded
> digit of ShC_{j*} at slot (a*, b*) is EXACTLY
>
>     binom(m,2) * (chat_{t*})^2 * pi^{2 a_{t*}} * (wrap unit) ,
>
> assembled from the unique GRADED-LAYER branch of (a)'s equality
> census (the k = 2 diagonal; (a)'s k >= 3 equality branches, when
> they exist, sit above the layer and off the slot). Hence:
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

(k >= 2; e2(f2 - t*) >= 1 since t* < f2). Exactly:

    (B* + 1) - (e2 f2 (m-k) + e2 Sum t + e)
       = (k-2)(e2(f2-t*) - 1) + e2(k t* - Sum t) + (k-1-e) ,

three non-negative terms (k >= 2; t <= t* termwise; e <= k - 1),
and division steps only subtract further. So Y = B* + 1 forces
zero division steps, Sum t = k t* (the all-t* multiset), e = k - 1,
and (k-2)(e2(f2-t*) - 1) = 0. At e2(f2 - t*) >= 2 that pins the
diagonal pair (k, multiset, e, steps) = (2, {t*, t*}, 1, 0); at
e2(f2 - t*) = 1 every k >= 3 whose extraction budget allows
e = k - 1 (Step II: (k-1) D' <= Sum i = k i_{t*}) contributes too.
Each such k >= 3 branch spends exactly D' of x-degree per
extraction (tail steps spend more), so it terminates at x-slot
<= k i_{t*} - (k-1) D' < 2 i_{t*} - D' = a* (the gap is
(k-2)(D' - i_{t*}) > 0 since i_{t*} <= e1 - 1 < D'), and its
weight is m E2 + (k-1) delta >= m E2 + 2 delta, strictly above
the height-THETA_{j*} graded layer (weight m E2 + delta, Step IV).
[r1 2026-08-10: census corrected per passPE1 F-1 — the sealed
sentence forced k = 2 unconditionally; refuted at CE3 (S11).] The iterated exact division of Delta
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
(a)'s corrected equality census it is an all-t* source with
e = k - 1 and no division steps, and the k >= 3 members (live only
at e2(f2 - t*) = 1) are excluded twice over — their weight
m E2 + (k-1) delta >= m E2 + 2 delta sits strictly above the
graded layer, and their x-slot <= k i_{t*} - (k-1) D' < a* misses
the slot — leaving the diagonal pair source {t*, t*} with
its single extraction and no division steps. Its source monomial —
x-position 2 i_{t*}, Y-position B*, coefficient binom(m,2)
(-chat_{t*})^2 pi^{2 a_{t*}} = binom(m,2) chat_{t*}^2 pi^{2 a_{t*}}
— is UNIQUE at that (x, Y)-position among all sources: a k = 0
source sits at Y-position e2 f2 m = B* + 2 e2(f2 - t*) > B*; a
k = 1 source sits at Y-position B* only when t = 2 t* - f2 lies in
T (needs 2 t* >= f2), and its x-position i_t <= e1 - 1 < D' <=
2 i_{t*} ((b)'s hypothesis) misses 2 i_{t*} [r1 2026-08-10: the
k <= 1 lines added per passPE1 F-3]; a k = 2
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
strictly above — (b2). Branches at the same Y = B* + 1 besides
this one are exactly (a)'s k >= 3 equality branches (live only at
e2(f2 - t*) = 1, with e = k - 1 >= 2): they cost (k-1) delta >=
2 delta of weight, sit strictly above the graded layer, and land
at x-slot < a* — doubly clear of the height-THETA digit (at CE3
the -8 Y^{B*+1} branch measures v = 3 at height THETA_{j*} + delta
and x-slot 0 — S11); same-height branches at other Y land at
other slots. ∎(b)

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
blind [r1 2026-08-10: as corrected at S2 — at e2(f2 - t*) = 1 the
Y = B* + 1 census also carries k >= 3 all-t* monomial branches
whenever k I_{t*} >= (k - 1) D', landing at x-slot <=
k I_{t*} - (k - 1) D' < 2 I_{t*} - D' (since I_{t*} <= D' - 1) at
weight >= m E2 + 2 delta, above the graded layer],
(ii) max-forces-diagonal on the monomial pair (r*, r*),
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
hand-traced before repair and disclosed in the runner docstring; no
CERTIFICATE-slot want changed, and one instrument display-slot want
was WEAKENED from an exact value to what the ledger licenses
(valuation + graded digit) [r1 2026-08-10 precision per passPE1
F-4; the sealed phrasing "NO theorem-facing want changed" left the
weakening implicit]: (i) my B3 display-slot want claimed
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
j*-1 band one m up — the 2 binom(m,3) law of record, 6.7C'; the
seal's binom(m,2) - binom(m,3) display was REFUTED BY THE
INSTRUMENT at m >= 4 and corrected via the descent-multiplicity
LEMMA 6.7D — see the dated block in S8). Machine legs S9 (two
sealed runners, two-commit each). Grade of the append: 0/2
(attempt; hostile arc owed), riding the frozen notes it cites.**

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

## S8. GENTOW6-BOX-3 — REGIME-3 CLASSIFICATION (THEOREM GENTOW-6.7)
## + THE j*-1 BAND ONE m UP (COROLLARY-THEOREM GENTOW-6.7C)

**The box verbatim (GENTOW6_PROOF S5).** "GENTOW6-BOX-3 (regime-3
classification). Which non-x-free, no-top-overflow members diverge,
and exact THETA-attainment via entry drivers: displayed only
(E-ENTRY witness; the pair-sum digit display of the quadrichotomy
clause (3)); no theorem." The S6 residue of this note's first
append adds the lead consumed here: the j < j* lower-coordinate
classification at mu2 >= 3 "is BOX-3's geography one m up."

**Honest scope split.** The box bundles two asks. (i) The KEY-POWER
regime-3 classification (the quadrichotomy clause (3) pair-sum
display made a theorem): PROVED below as THEOREM GENTOW-6.7, with
the attainment criterion the residue of an explicit pair sum chi —
and its m-up extension at the first lower coordinate PROVED at a
named geography class as COROLLARY-THEOREM GENTOW-6.7C. (ii) The
MEMBER classification (entry drivers: which members f = Phi2^2 +
Sum C_j Phi2^j attain exactly THETA) is NOT proved here: the
E-ENTRY witness already shows a member whose entry branch lands
ABOVE the floor (31 > 29) and DRAINS the shadow; the entry-pair
single-extraction ledger (entry digit c at (j', a, b) crossing lift
t, overflow iff a + i_t >= D', digit -c chat_t (unit) at Y-exponent
b + e2 t + (j'-1) e2 f2 + 1) prices each branch, but a member's
graded assembly mixes FREE digits at arbitrary depths — the
classification is per-member finite arithmetic with no genre-level
statement; the obstruction is displayed at S8.1 below. Box verdict
in S10.

**Setting = GENTOW-6.3's (S2 above), mu2 = 2, f1 = 1, corrected
chat_t.** Recall: T = {t < f2 : chat_t != 0}, t* = max T, lift data
(i_t, a_t) with e1 a_t + i_t h = u2 (f2 - t), D' = e1, pair source
census (GENTOW-6.3(a)): the height-THETA graded discrepancy layer
is single-extraction branches, one per x-overflowing pair
(i_t + i_{t'} >= D'). REGIME 3: some pair overflows and
2 i_{t*} < D' (forces f2 >= 2 and t < t' mixing).

**Named objects.**

    s*    := max { t + t' : (t,t') in T^2, i_t + i_{t'} >= D' }
    j*3   := floor((e2 s* + 1) / (e2 f2)),  b*3 := (e2 s* + 1) mod e2 f2
    I(s*) := { i_t + i_{t'} : t + t' = s*, i_t + i_{t'} >= D' }
    a(s*, I) := (u2 (2 f2 - s*) - I h) / e1   [an integer: sum the
                two defining identities e1 a + i h = u2(f2 - t)]
    chi(s*, I) := Sum_{t <= t', t + t' = s*, i_t + i_{t'} = I}
                  (2 - delta_{tt'}) c-bar_t c-bar_{t'}   in K
                  [c-bar = residue of the corrected chat]

> **THEOREM GENTOW-6.7 (regime-3 classification at the top overflow
> coordinate; mu2 = 2, f1 = 1).** For f = Phi2^2 at a regime-3
> genre:
>
> (a) [CEILING] every discrepancy branch has Y-exponent
> <= e2 s* + 1, with equality exactly for the zero-division-step
> extracted branches of the overflowing pairs with t + t' = s*.
> Consequently ShC_j == 0 identically for every j > j*3, and the
> slots of ShC_{j*3} with b > b*3 are empty.
>
> (b) [TOP-SLOT DIGITS] for each I in I(s*), the height-THETA_{j*3}
> graded digit of ShC_{j*3} at slot (I - D', b*3) is
>
>     chi(s*, I) · pi^{a(s*, I)} · (wrap unit),
>
> read as: the slot's height-THETA graded component has residue
> chi(s*, I) times the shared unit. Hence
> (b1) if chi(s*, I) != 0 in K for some I in I(s*): the shadow
> diverges from DRAIN at EXACTLY THETA_{j*3} at coordinate j*3
> (GENTOW-3(i) floors it; the digit attains it);
> (b2) if chi(s*, I) = 0 for every I in I(s*): the height-THETA
> graded layer at every s*-slot is ZERO and any content there sits
> strictly above the floor. No attainment is claimed at the s*-
> slots; the lower-s slots assemble multiple branches (direct
> lower-s pairs + division-stepped descendants of the s*-branches)
> and their vanishing is displayed genre arithmetic per slot —
> the S3 cascade, machine-measured at both faces in S9.
>
> (c) [SPECIALIZATION] regime 2 is the degenerate case s* = 2t*,
> I(s*) = {2 i_{t*}} with the single diagonal pair: chi = c-bar_{t*}^2
> != 0 unconditionally — THEOREM GENTOW-6.3(b) verbatim, which is
> WHY no residue condition appears there. At f2 = 1 regime 3 is
> empty (T = {0}: the only pair is the diagonal).

*Proof.* (a) By 6.3(a) (consumed; its proof is the mu2 = 2 case of
6.5 Steps I-III above), discrepancy content traces to extracted
branches of x-overflowing pair sources; a pair (t, t') enters at
Y-exponent e2(t + t'), one extraction raises it by exactly 1
(i_t + i_{t'} <= 2e1 - 2 < 2D': single rewrite), and every
division/recarry step strictly lowers Y (by e2(f2 - s) >= 1,
s in T). Overflowing pairs have t + t' <= s* by definition of s*,
so Y <= e2 s* + 1 with equality forcing t + t' = s* and zero
steps. Pairs with t + t' > s* exist only as NON-overflowing
sources: in-grid, tail-route-only, shared by both reads and
cancelled (6.3(a)'s last clause). Coordinate j content requires
some slot Y = j e2 f2 + b >= j e2 f2; for j > j*3,
j e2 f2 >= (j*3 + 1) e2 f2 > e2 s* + 1 by the floor definition —
empty; at j = j*3, b > b*3 likewise exceeds the ceiling. ∎(a)
(b) Fix I in I(s*). The sources entering at position
(x^I, Y^{e2 s*}) are exactly the pairs {t, t'} with t + t' = s*
and i_t + i_{t'} = I; each carries source coefficient
(2 - delta_{tt'}) chat_t chat_{t'} pi^{a_t + a_{t'}} with
a_t + a_{t'} = a(s*, I) SHARED across the slot (the weight
identity: e1(a_t + a_{t'}) + I h = u2(2f2 - s*)). The single
extraction has Phi'-branch coefficient exactly 1 and in-grid
x-part x^{I - D'} (I - D' < D'); zero division steps reach
coordinate j*3 slot (I - D', b*3) directly with coefficient
unchanged and the coherent normalizer's wrap unit (6.3(b)'s
clause). By (a)'s equality case no other branch reaches Y-exponent
e2 s* + 1; branches at the same height but other Y land at other
slots; and the graded digit at height THETA_{j*3} reads the
coefficient sum's residue at valuation a(s*, I): the terms whose
integer coefficient (2 - delta) is a p-unit contribute their
residues, terms with p | (2 - delta) sit one grade up — both
exactly captured by chi(s*, I) computed in K. If some chi != 0:
nonzero graded digit at height THETA_{j*3}, and GENTOW-3(i)
(consumed, at its arc grade) forbids discrepancy content below
THETA: divergence exactly on the floor, coordinate j*3 — (b1). If
all chi = 0: each s*-slot's graded THETA-layer vanishes and its
value (if any) has valuation > a(s*, I) — (b2). ∎(b)
(c) Arithmetic of the definitions; at 2 i_{t*} >= D' the maximum
s* = 2t* is attained by the diagonal (t <= t* termwise), I = 2
i_{t*} is its only element, delta_{tt'} = 1, chi = c-bar^2, a
product of units in the field K. ∎

**S8.1 (the member/entry-driver half: the displayed obstruction).**
For members, the same ledger prices each entry x lift overflow
branch at weight (entry digit weight) + E2 (j' - 1 co-factors
priced separately) + delta, and the E-ENTRY witness (GENTOW6_PROOF
S4: f_E = Phi2^2 + 4x^2 Phi2 + 16 Phi' at FAM-E) realizes the
branch that lands at the C_0 slot and CANCELS it (shadow DRAIN,
divergence displayed at 31 >= THETA_0 = 29, NOT on the floor).
Whether a member attains EXACTLY THETA_j depends on the residues
and depths of ITS free entry digits (the branch height moves
linearly with v(c)), so the class of exactly-THETA members is cut
by per-member congruences, not by genre data alone: a genre-level
trichotomy would have to quantify over the free budget box, and
the two measured members (E-ENTRY above the floor; the S9
perturbation rows holding their floors) already witness both
behaviors INSIDE one genre. That is the exact obstruction to a
theorem-shaped classification of ask (ii); it stays displayed.

> **COROLLARY-THEOREM GENTOW-6.7C (the j* - 1 band one m up: the
> binomial-difference law).** Fix a tower genre with f1 = 1,
> f2 = 1, e2 = 2, e1 = D' = 2, i_0 = 1 (so T = {0}, u2 = 2 a_0 + h
> odd, chat := chat_0, any p, any h with gcd(h, e1) = 1 — the
> FR5X / FAM-A5 / GEN-P3 geography class), and f = Phi2^m, m >= 3.
> Then at coordinate j* - 1 = m - 3 (one below THEOREM GENTOW-6.5's
> top coordinate):
>
> (i) the discrepancy branches with one extraction (the
> height-THETA graded layer's population, 6.5 Step IV) have ODD
> Y-exponent; the band's odd slot is Y = 2m - 5, i.e. slot
> (a, b) = (1, 1) of ShC_{m-3}, and it receives EXACTLY TWO
> branches: the k = 3 direct branch (source multinomial
> binom(m,3), coefficient -binom(m,3) chat^3 pi^{3 a_0} x after
> extraction) and the k = 2 top branch after ONE division step
> (+binom(m,2) chat^3 pi^{3 a_0} x);
>
> (ii) the slot's total one-extraction value is therefore
>
>     ( binom(m,2) - binom(m,3) ) · chat^3 · pi^{3 a_0} · x
>     [ note binom(m,2) - binom(m,3) = binom(m,2)(5 - m)/3 ],
>
> and the height-THETA_{m-3} graded digit of ShC_{m-3} at (1,1) is
> its residue times the wrap unit: the shadow diverges from DRAIN
> exactly on the floor at coordinate m - 3 iff
> p does NOT divide binom(m,2) - binom(m,3);
>
> (iii) at m = 5 the integer coefficient is ZERO (binom(5,2) =
> binom(5,3) = 10): the two branches cancel IDENTICALLY (every p,
> every unit chat) and the (1,1) slot carries no one-extraction
> content at all;
>
> (iv) instantiations: m = 3: coefficient 2 — cancels iff p = 2
> (obs-1's FR5X-3 j = 0 slack, and A53's measured 128-at-pin-35;
> attained at GEN-P3, the measured 11664-at-31); m = 4:
> coefficient 2; m = 5: zero; m = 6: coefficient -5 — cancels iff
> p = 5, so attainment RETURNS at p = 2 and p = 3 one coordinate
> below a top coordinate that itself cancels at p = 3
> (binom(6,2) = 15). The three FR5X configurations (attained /
> slack / identically-zero) are clauses 6.5(b1) at j*, 6.7C(ii) at
> j* - 1 with p | 2, and 6.5(c) above j*, of one ledger.
>
> *Proof.* At this genre class every source is a k-multiset of the
> single digit t = 0: entry position (x^k, Y^{2(m-k)}), coefficient
> (-1)^k binom(m,k) chat^k pi^{k a_0}; every division step is
> through the single lift term (Y-change -e2 f2 = -2, coefficient
> times +chat pi^{a_0} x); every extraction raises Y by 1 and
> consumes x^2. So along any branch Y ≡ e (the extraction count)
> mod 2: the graded (weight m E2 + delta, e = 1) population sits at
> odd Y — (i)'s parity clause. Band m - 3 means Y in
> {2m - 6, 2m - 5}; odd member 2m - 5. One-extraction branches
> reaching it: k-source, one extraction, s steps: Y = 2(m - k) + 1
> - 2s = 2m - 5 gives k + s = 3 with k >= 2 (x-overflow needs
> x^k, k >= D' = 2; e <= floor(k/2) limits nothing here): (k, s) =
> (3, 0) and (2, 1). Their x-slots: k = 3: x^3 extracts once
> (3 < 2D') to x^1, no steps: slot (1,1); k = 2: x^2 extracts to
> x^0, one step multiplies by chat pi^{a_0} x: slot (1,1) — the
> same slot, and the pi-powers match (3 a_0 both). Signs: the
> k = 3 source carries (-1)^3 = -1; the k = 2 source (+1) and the
> division step emits MINUS the quotient times the lift term
> -chat nhat, i.e. +chat pi^{a_0} x per step. Total = (ii)'s
> display; the weight ledger (6.5 Step IV) puts both branches at
> m E2 + delta exactly, reading at coordinate m - 3 as height
> THETA_{m-3}, and 6.5's Step V cancels the tail/source pairs, so
> the slot's graded THETA-layer is exactly the displayed residue
> times the wrap unit. Attainment as in 6.7(b1) via GENTOW-3(i).
> Multi-extraction branches have e >= 2, weight >= m E2 + 2 delta
> (above the graded layer) AND even-or-higher parity displacement:
> e = 2 branches sit at EVEN Y (never at (1,1)-type slots of this
> class); e = 3 branches (k = 6) land at Y = 2(m - 6) + 3 with at
> most floor(k/2) extractions — a different band. So the (1,1)
> slot value is EXACTLY (ii)'s display: (iii) is the m = 5
> degeneration, integrally zero. (iv) is arithmetic + the cited
> committed measurements. ∎

**Conditionality (named).** 6.7 consumes THEOREM GENTOW-6.3(a) and
GENTOW-3(i); 6.7C consumes THEOREM GENTOW-6.5 Steps I-V (this
note, 0/2) — both ride their notes' grades. The 6.7C geography
class is f2 = 1, i_0 = 1, e1 = 2 EXACTLY as stated; deeper bands
(j* - 2 and below) assemble three or more branches (k = 4 tail-
carry routes enter) and stay displayed, not claimed.

[**RUN-1 CORRECTION (dated 2026-08-10, THEOREM-FACING; the sealed
instrument caught it — artifact gentow6_box3_regime3_output_run1_
RED.txt).** COROLLARY-THEOREM 6.7C's displayed coefficient
binom(m,2) - binom(m,3) is FALSE at m >= 4: the instrument
measured the (1,1) slot values 46656 = 8 x 5832 (P34, m = 4),
116640 = 20 x 5832 (P35), 233280 = 40 x 5832 (P36) against the
display's 2/0/-5 multiples — the display's m = 5 "integral
degeneration" clause (iii) and the m-instantiations (iv) are
WITHDRAWN. Root cause, re-derived from this note's own objects
(not transcribed): the (ii)-display priced the pair branch's
descent as ONE division step of coefficient chat nhat, but at
T = {0} the iterated K2-division has the closed K2-adic form

    LEMMA GENTOW-6.7D (descent multiplicity). K2 = Y^{e2} -
    chat nhat (f2 = 1) gives, exactly,
    Y^{e2 r + b} = Sum_j binom(r, j) (chat nhat)^{r-j} K2^j Y^b
    (0 <= b < e2): a monomial entering at coordinate r reaches
    coordinate j with multiplicity binom(r, j) and factor
    (chat nhat)^{r-j}, each such route weight-exact (nhat's term
    carries weight E2 = wt(Y^{e2})). Proof: Y^{e2} = K2 +
    chat nhat and the binomial theorem; the expansion IS the
    iterated exact division. ∎

    At mu2 = 2 every descent has r - j <= 1 with r <= 1, so
    binom(r, j) = 1 — THEOREM 6.7's displays are untouched (and
    measured GREEN); at m = 3 likewise binom(1, 0) = 1, which is
    why the committed FR5X/A53/P33 rows could not catch the slip.

**COROLLARY-THEOREM GENTOW-6.7C' (statement of record, supersedes
(ii)-(iv)).** In 6.7C's setting the (1,1) slot of ShC_{m-3} has
one-extraction value EXACTLY

    [ binom(m,2) binom(m-2, m-3) - binom(m,3) binom(m-3, m-3) ]
      · chat^3 pi^{3 a_0} x  =  2 binom(m,3) · chat^3 pi^{3a_0} x

(pair branch: extracted at Y^{2m-3} = Y^{2(m-2)} Y, descends
r = m-2 to j = m-3 with multiplicity m-2 and one factor chat nhat;
triple branch: enters at Y^{2(m-3)} Y directly, multiplicity 1;
census (i) unchanged), and the graded THETA_{m-3} digit is
2 binom(m,3) · c-bar^3 · (wrap unit): attainment at coordinate
m-3 exactly on the floor iff p does NOT divide 2 binom(m,3).
Since 2 binom(m,3) >= 2, there is NO integral degeneration; at
p = 2 the slot cancels in grade at EVERY m (the factor 2) — the
X3/A53 measured slack rows; at p = 3: 2 binom(m,3) is a unit at
m = 3, 4, 5, 6 except none (v_3(2binom(m,3)) = 0 there):
attainment at P33/P34/P35/P36, measured. The corrected law
reproduces every measured value including the committed m = 3
rows (both laws coincide at m = 3). ∎

The three FR5X configurations re-read: attained at j* (6.5(b1)),
slack at j*-1 BECAUSE p = 2 | 2 binom(m,3) (not because of a
binomial difference), identically-zero above j* (6.5(c)).]

## S9. MACHINE LEGS (BOX-2 + BOX-3), TWO-COMMIT SEALS

### S9.1 BOX-2 leg — gentow6_box2_ledger.py

Sealed at commit 82a51147 (runner md5 a840024f, docstring
preregistered, no pre-seal run). **RUN 1 GREEN — 576 checks, 0
violations, teeth kill counts EXACT (T-NOJ 4, T-FIB1 4, T-RESC 1,
T-CEN 4); isolated re-run in a fresh /tmp scratch BIT-IDENTICAL
(output md5 091ce8a1).** No RED run: run 1 is the verdict run.
Highlights, each preregistered:

* the Sylvester-determinant = resultant identity held at 100 + 100
  + 60 sampled box pairs (Bareiss det vs the Euclidean-remainder
  oracle, two in-file algorithms), with |gp polresultant| matching
  on the 12 gp rows;
* v(Res) measured CONSTANT at the predicted separation constants:
  2 (L1, p = 3 same-side distinct-residual avatar), 1 (L2, p = 2
  distinct-slope avatar), 20 = c_J = mu2* m' D2 E2/(e1e2) at the
  FAM-P5 bouquet frame (60/60 pairs, box digits drawn to depth 12);
* Smith profiles: divisor-valuation sums = c_J with every divisor
  <= c_J (the dm(O^d) >= pi^c lattice clause), 3 pairs per frame;
* THE LEDGER BY FULL ENUMERATION: L1 at N = 5: 4,782,969 pairs ->
  image EXACTLY 3^12 = 531441 = q^{-2} x pairs, every fiber
  EXACTLY 9 = q^{c_J}, image set == the census congruence cell
  (500/500 sampled cell members attained); L2 at N = 4, 5, 6:
  images 2^6/2^9/2^12 = 2^{3N-6}, fibers all 2, cell equality
  (300/300 at N = 6); EXPLORATORY rows below N_0 (disclosed as
  no-want rows at seal): L1 N = 3, 4 measured 81 and 6561 — the
  ledger value 3^{4N-8} already exact BELOW the theorem's
  conservative N_0 = 5;
* window stability at the tower frame: f' = f_S g + 3^45 x^7
  Newton-refactored through the Sylvester system to f_S' g' == f'
  mod 3^90 with f_S' == f_S mod 3^25 and both factors back inside
  their GENTOW-1(a) budget boxes (floors [6,5,4,4|3,3,2,1] and
  [3,3,2,1], computed from the display and matching the hand pins);
* the T1 pair's product read the single side (0,15)->(6,0) at
  level 1; factorpadic put each key in one degree-4 factor;
  poldisc != 0.

**Record sentences (no universal quantifiers).** The battery's 576
checks passed with 0 violations on the three constructed frames
named in S9.1; the L1-N5 enumeration counted 531441 images with
every measured fiber equal to 9; the L2 enumerations matched
2^{3N-6} at the three windows run; the 60 T1 resultant rows each
measured v = 20; the four preregistered kill counts were exact.

### S9.2 BOX-3 leg — gentow6_box3_regime3.py

Sealed at commit b6fb54ec (seal md5 17fecec4, docstring
preregistered, no pre-seal run; imports the COMMITTED
gentow6_box1_mu3.py engine, md5 c98cb423 asserted at import).
**RUN 1 RED — 5 violations, ALL on the corollary's j*-1 rows
(P34/P35/P36 + CFORM + one T-M5SUM row), THEOREM-FACING: the seal's
6.7C display refuted, artifact kept (md5 c07980ad), correction =
LEMMA GENTOW-6.7D + COROLLARY 6.7C' (the dated S8 block). RUN 2
(repaired wants, md5 72383f91) GREEN — 215 checks, 0 violations,
teeth kill counts EXACT (T-TOPPAIR 3, T-CHI 3, T-CVAL 3, T-M5SUM 3,
T-OLDLAW 3, T-PARITY 3); isolated re-run in a fresh /tmp scratch
BIT-IDENTICAL (output md5 a122d9ca).** The regime-3 rows needed NO
repair: on run 1 the R3A-R3E slot dicts, pins, graded flags, the
battery reproductions, floors, triple-route equalities, PARI rows,
and four of six teeth were already GREEN. Highlights, each a
run-2 want:

* THEOREM 6.7's faces, one frame each: (b2) at p = 2 — R3A's
  s*-slot {(0,0): 16} sits one grade up (chi = 2 = 0 mod 2, pin 12
  > THETA_1 = 9) while its j0 CASCADE attains ({(1,1): 48} graded
  nonzero at 17 = THETA_0: the s = 0 diagonal survives one
  coordinate down); (b1) at p = 3 — R3B's {(0,0): 108} exactly on
  the floor (pin 9 = THETA_1) with the INTEGRAL (1,1) cancellation
  (+324x - 324x = 0) and the (2,0) = -1944 graded attainment at
  j0; (a) — R3C's ShC_1 == {} identically above s* = 0 with
  {(0,1): 16} on the floor at j0; the TWO-PAIR slot at odd p —
  R3D (units 1,1,1: chi = 1 + 2 = 0 mod 3, cancel, pin 20 > 16)
  vs R3E (units 2,2,1: chi = 4 + 4 = 2 mod 3, attain, pin
  16 = THETA_1), identical geometry, one unit flipped: genre
  arithmetic in the literal sense;
* the corrected corollary law measured EXACTLY at four m-values:
  (1,1) slot values 524288/128/11664 (m = 3, both laws), 46656
  (m = 4), 116640 (m = 5 — the withdrawn degeneration's slot is
  PRESENT and attained at p = 3), 233280 (m = 6, attained at
  j*-1 = 3 while the top coordinate cancels at 3 | binom(6,2));
  the recorded companion slots (0,0) matched the k = 4 e = 2
  branch predictions 104976/524880/1574640 from the seal;
* the committed 6.5-battery vectors X3/A53/P33 reproduced
  bit-exactly (the required battery frame), P36's ShC_4 =
  {(0,1): 4860} with graded-21 zero (p = 3 | binom(6,2), the
  6.5(b2) face at m = 6) and ShC_5 == {};
* 20 perturbation rows held their floors; triple-route (committed
  R/E + this file's fresh route F) slot-identical on the ten
  self-shadows; PARI carriers {(3,2)}/{(3,2)}/{(4,2)}/{(4,3)}/
  {(4,3)}/{(4,1)} and three nonzero poldiscs.

**Record sentences (no universal quantifiers).** The run-2 battery's
215 checks passed with 0 violations on the ten frames named in
S9.2; the six preregistered kill counts were exact; the five s*-slot
values 16, 108, 16, 243, 648 each measured at the predicted
valuation and graded flag; the four corollary slots measured the
2 binom(m,3) multiples 46656, 116640, 233280 and the m = 3 trio;
the run-1 RED's five violations were confined to the corollary rows
and produced the 6.7D/6.7C' correction.

## S10. VERDICTS + RESIDUE (this append)

* **GENTOW6-BOX-2: CLOSED at its own ask.** The box's parenthetical
  defines the ask — "pricing (f_S, g) ↦ f_S·g on ambient windows (a
  Jacobian/content identity)" — and THEOREM GENTOW-6.6 delivers it:
  Sylvester-Jacobian (a), the separation constant c_J with closed
  form at the bouquet geography (b/d), the per-window product
  ledger with explicit N_0 and fiber law (c), machine leg GREEN
  576/0 with the ledger ENUMERATED exact at two avatar frames and
  the pricing verified at the FAM-P5 bouquet frame. NOT delivered
  (named, not this box's parenthetical): the GENH5-DENS-style
  aggregation of cells over genres/keys.
* **GENTOW6-BOX-3: the KEY-POWER half CLOSED (mu2 = 2) as THEOREM
  GENTOW-6.7 (chi-criterion, b1/b2 + ceiling + specialization),
  machine leg GREEN at five new regime-3 genres; the one-m-up lead
  delivered as LEMMA 6.7D + COROLLARY-THEOREM 6.7C' (the
  2 binom(m,3) law of record, instrument-corrected), reproducing
  the FR5X three-configuration target as 6.5(b1)/6.7C'-at-p=2/
  6.5(c). The MEMBER half (entry-driver exact-THETA classification)
  stays OPEN with the obstruction DISPLAYED (S8.1): exactly-THETA
  membership is cut by per-member congruences on free digits — the
  two measured behaviors inside one genre (E-ENTRY above-floor
  DRAIN vs the floor-holding perturbation rows) witness that no
  genre-level trichotomy can decide it.
* **Grade: 0/2 (attempt).** Hostile arc owed. Natural PE1 targets:
  6.6(c)'s fiber argument and N_0 arithmetic, 6.6(d)'s separation
  lemma normalization, 6.7(b)'s "no other branch" fence at
  e2(f2-t*) = 1, the 6.7D consumption inside 6.7C', and the R3D/E
  hand ledgers.
* **Statement fence:** GENTOW6_PROOF stays frozen; this note's S8
  keeps the refuted 6.7C display visible under its dated
  correction block (6.7C' governs).

---

# APPEND (GENTOW6-BOXES r1 REPAIR unit, 2026-08-10): passPE1 REPAIR
# ROUND — F-1 (CRITICAL) REPAIRED IN PLACE, F-3/F-4 MINORS LANDED,
# F-2 BRACKETED AT THE GENTOW6_PROOF APPEND; CE3 + BP3 ADOPTED

## S11. THE REPAIR ROUND (verdict passPE1 = NOT CLEAN, 3ae577e8;
## grade STAYS 0/2)

**F-1 (CRITICAL, 6.5(a)'s equality sentence) — REPAIRED, re-derived
from Step III's own display.** The sealed sentence forced
(k, multiset, e, steps) = (2, {t*, t*}, 1, 0) at Y = B* + 1
unconditionally. Re-derivation (Step III, this round): the deficit
(B* + 1) - (branch Y) decomposes EXACTLY as (k-2)(e2(f2-t*) - 1) +
e2(k t* - Sum t) + (k-1-e) plus the division-step losses — all
non-negative — so equality forces zero division steps, the all-t*
multiset, e = k - 1, AND (k-2)(e2(f2-t*) - 1) = 0. The k = 2 pin
is therefore CORRECT exactly when e2(f2 - t*) >= 2 and FALSE in
general at e2(f2 - t*) = 1, where every k >= 3 with
k i_{t*} >= (k-1) D' (Step II's extraction budget) contributes an
equality branch; each such branch spends exactly D' of x-degree
per extraction (tail steps spend more), landing at x-slot <=
k i_{t*} - (k-1) D' = a* - (k-2)(D' - i_{t*}) < a* (i_{t*} < D'),
at weight m E2 + (k-1) delta >= m E2 + 2 delta, strictly above the
height-THETA_{j*} graded layer. Both exception properties are now
DISPLAYED in (a); Step III carries the deficit identity; Step IV's
two consumption sites cite the corrected census (the (a*, b*)
digit claim survives the exception TWICE OVER: weight fence +
x-slot displacement). Consumer verdicts, walked this round:
(b1)/(b2) SURVIVE (Step IV as repaired; at CE3 the certificate
digit 12 = binom(3,2) ĉ² π² measured at (a*, b*) = (1, 1), pin
12 = THETA_2 — attainment holds THROUGH the exception's presence);
(c) SURVIVES (consumes only the ceiling Y <= B* + 1, never the
equality census; CE3 measures ShC_j empty above j* = m - 1
vacuously, X3/X4 measure it live); (d) SURVIVES (no-overflow gives
Delta = 0 outright, census-free); S3's display SURVIVES (FR5X has
e2(f2 - t*) = 2 — the exception is dead there); COROLLARY 6.5C
SURVIVES (same frame); ANNEX-REMARK 6.5' carries its dated
bracket (the exception transposes with I_{t*} for i_{t*}).

**Clause verification at three frames (fresh instrument, this
round's isolated re-run BIT-IDENTICAL, md5 b377850b):**

* CE3 (Q2, Phi' = x^3 - 2, D' = 3; e2 = 1, f2 = 2, t* = 1,
  i_{t*} = 2, delta = 2, E2 = 10; Phi2 = Phi'^2 - 2x^2 Phi' - 8x,
  m = 3; B* + 1 = 5, j* = 2, (a*, b*) = (1, 1), THETA_2 = 12):
  e2(f2 - t*) = 1 and 3 i_{t*} = 6 = 2 D' — the k = 3 exception is
  LIVE and feasibility-tight. Measured ShC_2 = {(1,1): 12,
  (0,1): -8, (0,0): 160, (2,0): -32}: the -8 at x-slot 0 =
  3 i_{t*} - 2 D' < a* = 1, v = 3, height 14 = THETA_2 + delta —
  exactly the displayed exception branch (3, {t*,t*,t*}, 2, 0);
  the certificate slot (1,1) holds the graded floor digit 12.
* X3 (FR5X at m = 3; e2 = 2, f2 = 1, t* = 0): e2(f2 - t*) = 2 >= 2
  — the repaired clause pins the diagonal pair, agreeing with the
  sealed sentence; measured ShC_1 = {(0,1): 12288} single-slot,
  pin 61 = THETA_1 (no second Y = B* + 1 trace, as forced).
* B3 (FAM-B at m = 3; e2 = 1, f2 = 2, t* = 1, i_{t*} = 1, D' = 2):
  e2(f2 - t*) = 1 but 3 i_{t*} = 3 < 2 D' = 4 — the exception's
  FEASIBILITY fence bites: no k >= 3 equality branch exists, and
  the measured second THETA-slot (1,0) is Step IV's stepped
  content at Y = B* (a division-step trace, not an equality
  branch). The clause's two gates (e2(f2 - t*) = 1 AND the budget)
  are each witnessed separately by CE3 vs B3.

**F-2 (GAP, the dated appends' "iff") — corrected at the ripple
sites; the boxes note's own (b1)/(b2)/S6 sentences were already
honest.** Independent re-derivation of the failure: (b2) prices
ONE slot — the certificate slot (a*, b*) — and says nothing about
other slots of coordinate j*; a floor-height branch at another
slot can carry the divergence when p | binom(m,2). BP3 (Q3,
Phi' = x^2 - 3, D' = 2; e2 = 1, f2 = 2, u2 = 3, t* = 1, i_1 = 1,
a_1 = 1, delta = 1, E2 = 6; Phi2 = Phi'^2 - 3x Phi' - 27, m = 3,
p = 3 | binom(3,2) = 3; THETA_2 = 7, (a*, b*) = (0, 1)) measures
ShC_2 = {(0,1): 27, (1,0): 135}: the certificate slot 27 = 3^3
sits at height 2*3 + 3 = 9 > 7 (the (b2) kill fires exactly), yet
(1,0) = 135 = 27*5 sits at height 2*3 + 1 = 7 = THETA_2 with
graded digit 5, a 3-unit: pin(ShC_2) = 7 — attainment ON the
floor with p | binom(m,2). Against X4 (p = 2 | binom(4,2), pin
65 > THETA_2 = 61: attainment FAILS), the converse direction is
genre-dependent both ways. The record of record: attainment on
the floor IF p does not divide binom(mu2,2); the iff is WITHDRAWN
(dated bracket at the GENTOW6_PROOF append; PROJECT_STATE #22
already carries the orchestrator's correction).

**F-3 (MINOR) — LANDED:** Step IV's source census gains its
k <= 1 lines (k = 0 sits at Y-position B* + 2 e2(f2 - t*) > B*;
k = 1 reaches Y-position B* only via t = 2 t* - f2 in T and is
excluded at the x-position by i_t < D' <= 2 i_{t*}).

**F-4 (MINOR) — LANDED:** S4's run-1 disclosure now states the
B3 display-slot want was WEAKENED (exact value -> valuation +
graded digit, what the ledger licenses), certificate-slot wants
untouched.

**CE3 + BP3 ADOPTED as battery rows (this note's row table).**
Verification before adoption: the verifier's committed fresh
instrument (verification/openmath/gentow6_boxes_pe1_fresh.py,
md5 fae8bc99, committed at 3ae577e8, NO import of any sealed
runner; dual R/E routes + exact-reconstruction third oracle +
per-coordinate floors) re-ran this round in an isolated /tmp
scratch: output BIT-IDENTICAL to the committed
gentow6_boxes_pe1_fresh_output.txt (md5 b377850b), 141 checks /
0 violations across its eight frames; the CE3 and BP3 vectors
above are read from that output and the CE3 full-vector hand
ledger in the passPE1 report matched it slot by slot. Rows of
record (both at m = 3, both on the e2(f2 - t*) = 1 axis):

    CE3: ShC_2 = {(1,1): 12, (0,1): -8, (0,0): 160, (2,0): -32},
         pin 12 = THETA_2  [the F-1 exception witness + (b1) live]
    BP3: ShC_2 = {(0,1): 27, (1,0): 135},
         pin  7 = THETA_2  [the F-2 converse refuter; (b2) fires]

Sealed artifacts BYTE-FROZEN this round: gentow6_box1_mu3.py
(c98cb423) / output (0a4cd16f), gentow6_box4_row.py (9d6e16cc) /
output (2d8d617a), REDs, and the pe1_fresh pair — untouched;
re-verified by md5 before commit. **Grade after this round: 0/2
(the repair round does not count toward acceptance; hostile
passes resume on the repaired text).**
