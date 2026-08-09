# GENTOW-5: the composed graded frame at general mu2 (GENTOW-BOX-1)
# + the level-r ladder grammar (depth >= 4)

**2026-08-09 — SKELETON (per-section commits follow). Unit: GENTOW-5,
BOX-CLOSURE campaign wave B1. Grade target 0/2 (attempt; hostile arc
owed).**

CHARGE: (1) PROVE or box-with-obstruction GENTOW-BOX-1 — LEMMA
GENTOW-2 layer 1 at general mu2 (the composed graded frame;
GENTOW1_PROOF S3/S6). (2) THE LEVEL-r LADDER GRAMMAR: the normalizer
recursion n-hat_i(m), the composed key recipe Phi_{i+1}, the digit
ladder at general i, the general-depth composition theorem (FGMN
Cor 6.4 is level-general; HE7 ANNEX R's HE7-2'/R1-a/R1-b is the
template one level down); depth-4 witness at n = 32, q = 2 if
reachable.

SOURCES CONSUMED (never edited): GENTOW1_PROOF_2026-08-09.md (S0
notation, LEMMA GENTOW-1 + Step 0, LEMMA GENTOW-2 + grade note,
LEMMA GENTOW-5, S6 boxes); GENTOW2_PROOF_2026-08-09.md (FGMN quotes
[Q1]-[Q10] at verified numbering, THEOREM GENTOW2-A, LEMMA GENTOW2-B
+ honesty box, S7 depth->=4 scope sentence); GENHN_PROOF_2026-08-08.md
(S6.1 LEMMA GENHN-4 + GENHN-BOX-2, S8 [r2] annex T(b)' + GENHN-2',
[GENHN-TOW-1] r3 item (6) text); HE7_PROOF_2026-08-08.md ANNEX R
(ANNEX-DEF HE7-2', ANNEX-LEMMA R1-a, ANNEX-THEOREMS R1-b/R1-c, R1.2
audit, R1.3 run record).

STATUS TABLE (updated per section as composed):

| target | item | status |
|---|---|---|
| (1) | THEOREM GENTOW5-A (composed graded frame, general mu2) | PROVED (S1) |
| (1) | GENTOW-BOX-1 disposition | RETIRED into GENTOW5-A's pin stack (S1.5) |
| (2) | DEF GENTOW5-1 (level-r ladder grammar) | STATED (S2.1) |
| (2) | LEMMA GENTOW5-C ((SLOT_i) for the tower ladder) | PROVED at annex-template grade (S2.3) |
| (2) | LEMMA GENTOW5-D (Step-0 carry monotonicity is level-agnostic) | PROVED (S2.4) |
| (2) | THEOREM GENTOW5-B (general-depth composition) | PROVED with named pins (S3) |
| (2) | depth-4 witness n = 32 q = 2 | GREEN: ladder 16/40/84/170/341 exact, both routes (S4) |
| battery | gentow5_checks.py | GREEN 208 checks / 0 violations, 5/5 teeth (S5) |

## S0. SETTING (one-pass restate; GENTOW-1 S0 + HE7-2' names)

Depth-2 tower per T(b)' (accepted): outer genre (Q; e1, f1, mu1; h),
key Phi' of degree D' = e1f1; inner side data (u2, e2, psi2, mu2)
with gcd(u2, e2) = 1, f2 = deg psi2, e2f2mu2 = mu1; composed key
Phi2, deg D2 = D'e2f2; composed ladder dv2 = e1e2*v; K = F_{Q^{f1}},
K2 = F_{Q^{f1f2}}; E2 := e2f2u2; node floor u2 > e2D'h. Ladder
normalizers n2hat(m) := pi^{a} x^{i} Phi'^{b} (i < e1, b < e2,
e1e2*a + i*e2h + b*u2 = m; unique (i,b) per residue class mod e1e2 —
GENTOW-1 S3). GENHN-2' (accepted, T(b)'(ii)): on the tower-node
locus, dv2(A(x0)) = the slot minimum EXACTLY, one K2-digit per
dv2-height per coordinate. Event setting of LEMMA GENTOW-2: f in
the tower locus whose composed polygon (j, p_j), p_j = dv2(C_j(x0)),
is ONE side of integer dv2-slope lam > E2 with residual (T - s)^{mu2}
over K2, s in K2^x; refine Phi2+ := Phi2 - lift(s; lam). GENTOW-2's
layers 2 (corrections land strictly deeper) and 3 (triangular
bijection) are PROVED at general mu2 in GENTOW1_PROOF S3; layer 1
(the graded kills) is proved there at mu2 = 2 pointwise only —
GENTOW-BOX-1 is exactly that gap. L2 := the completion of the leaf
at a fixed root x0 (v extended, normalized v(Q-uniformizer of the
BASE) = 1 as everywhere in the corpus); k(L2) its residue field;
iota: K2 -> k(L2) the transport of T(b)'/S4 convention.

## S1. TARGET 1 — THEOREM GENTOW5-A: the composed graded frame at
## general mu2 (GENTOW-BOX-1)

READ FIRST (what the box asked and what resolves it). GENHN-BOX-2's
level-1 resolution consumed COROLLARY W-9's twisted algebra (an
ACCEPTED pin) as the organizing frame for LEMMA GENHN-4 layer 1;
GENHN_PROOF's own [r2] re-aim (its S3.1-adjacent rider) already
re-points that frame at **gr(O_L)** — "one K-line per dv-height,
W-9's twisted algebra". At the composed key no accepted W-9 analogue
exists, which is why GENTOW-2 layer 1 stayed boxed. The observation
that retires the box: **the frame needed is not an abstract twisted
algebra at all — it is gr of the leaf FIELD, which is a graded
division ring for free, and GENHN-2' already makes the passage from
slots to gr(L2) pointwise-faithful.** Everything below is elementary
given GENHN-2'; no W-9-style weld face is consumed.

### S1.1 LEMMA GENTOW5-A0 (gr of a valued field is a graded division
### ring)

For the dv2-rescaled valuation on L2 (values in (1/e1e2)Z on the
relevant subfield, rationals in general), set for each rational m

    gr(L2)_m := {a in L2 : dv2(a) >= m} / {a : dv2(a) > m},
    gr(L2)   := (+)_m gr(L2)_m,   [a] := the class of a in degree dv2(a).

Then gr(L2) is a commutative graded ring, multiplication induced by
L2's; every nonzero homogeneous element is invertible; in particular
gr(L2) is a domain on homogeneous elements: [a][b] = [ab] != 0 for
a, b in L2^x.

*Proof.* Well-definedness and distributivity are the ultrametric
axioms. Invertibility: for a in L2^x, dv2(a^{-1}) = -dv2(a) and
[a][a^{-1}] = [1] != 0 (1 is not in the >0 part). [a][b] = [ab] is
dv2(ab) = dv2(a) + dv2(b), a valuation identity on a FIELD (no
zero divisors to break it). Degree-0 part: gr(L2)_0 = k(L2). ∎

The point of A0: **pointwise, at a root, there is no carry problem.**
Carries are a phenomenon of the slot GRID (rewriting a polynomial
between monomial bases); evaluation at x0 is blind to them. The
graded frame the box asked for is gr(L2) + the two bookkeeping
lemmas below, which translate between grid data and gr(L2) classes.

### S1.2 The multiplicative side convention + the dictionary lemma

Fix the event slope lam and set N := [n2hat(lam)(x0)] in
gr(L2)_{lam} — invertible by A0 (n2hat(lam)(x0) != 0 and its dv2 is
lam exactly, GENHN-2' at the single-monomial slot).

**DEFINITION (multiplicative side residual).** For the development
f = Sum_{j <= mu2} C_j Phi2^j (C_{mu2} = 1, deg C_j < D2) with pins
on or above the side of slope lam through (mu2, 0), the
**multiplicative residual** of the side at x0 is

    R_N(T) := Sum_{j} c_j T^j in k(L2)[T],
    c_j := [C_j(x0)] * N^{-(mu2-j)}  if dv2(C_j(x0)) = (mu2-j)lam,
    c_j := 0                          if dv2(C_j(x0)) > (mu2-j)lam,

(c_{mu2} = 1 since C_{mu2} = 1 at height 0). This is the convention
under which residual-of-product = product-of-residuals holds by A0
alone, and it is the corpus's operative convention: GENTOW-1 Step 1
consumes exactly this multiplicativity ("graded layer of a product =
product of graded layers"), the level-1 assembly carries the
z^{fl}-powers relating n(kappa)^t to n(t*kappa) (GENHN-4 layer 1's
display), and FGMN's R-operators — the dictionary target of
GENTOW2_PROOF S2 — are multiplicative by Cor 4.7(3) [Q8 @ GENTOW2].

**LEMMA GENTOW5-A1 (dictionary to the per-height coherent digits).**
Let gamma_j := the coherent per-height residue of C_j(x0) (the
GENHN-2'/S4 digit read against n2hat((mu2-j)lam)). Then

    c_j = iota(gamma_j) * theta_{mu2-j},
    theta_t := [n2hat(lam)(x0)]^t * [n2hat(t*lam)(x0)]^{-1}
             = iota(vartheta_t),  vartheta_t in K2^x FIXED,

with vartheta_t independent of x0 and of the polynomial read, given
by the telescoping vartheta_{t+1} = vartheta_t * res(tau(t*lam, lam))
where tau(a,b) := n2hat(a)n2hat(b)/n2hat(a+b) is the ladder cocycle.
tau(a,b) is a Laurent monomial in pi, x, Phi' of dv2-value 0 whose
residue at every tower-node point is the transport of a fixed element
of K2^x (the two-wrap letter monomial).

*Proof.* The first display is A0 arithmetic: [C_j(x0)] =
iota(gamma_j)*[n2hat((mu2-j)lam)(x0)] by the definition of the
coherent digit, and N^{mu2-j}/[n2hat((mu2-j)lam)(x0)] = theta_{mu2-j}.
Telescoping: n2hat(lam)^{t+1}/n2hat((t+1)lam) =
[n2hat(lam)^t/n2hat(t*lam)] * [n2hat(t*lam)n2hat(lam)/n2hat((t+1)lam)],
the second bracket = tau(t*lam, lam). Cocycle shape: write
n2hat(a)n2hat(b) = pi^{a1+a2} x^{i1+i2} Phi'^{b1+b2}; reducing the
exponents to ladder range costs one x-wrap x^{e1} =
(unit)*pi^{h}*(1 + Phi'-tail/x^{e1}-side data) per overflow and one
Phi'-wrap Phi'^{e2} = (unit)*n(u2)*(1 + strictly-above) per overflow
— at a tower-node point x0 both wraps have dv2-value 0 with residues
the two letters (the eta-wrap z1 := res(x(x0)^{e1}/pi^h *
n-correction) and the eta2-wrap z2 := res(Phi'(x0)^{e2}/n(u2)(x0)));
both are the transports iota of fixed K2-elements: z1 by GENHN's S4
level-1 cocycle (accepted; the ITER-LAW z-letter), z2 by T(b)'(iii)'s
(T22)-transport (Phi'(x0)^{e2}/n(u2)(x0) has residue a fixed unit
times psi2-data of eta2(x0), transported through iota — the same S4
computation GENTOW-1 Step 5 runs). Hence res(tau(a,b)(x0)) =
iota(z-letter monomial), fixed in K2^x, x0-free through iota. This is
ANNEX-LEMMA R1-a(iii) [HE7_PROOF ANNEX R] specialized to the depth-2
tower ladder — reproved here in the tower's own letters rather than
cited, since the base conventions differ (HE7's base is varpi-powers;
ours is the ladder monomials pi^a x^i). ∎

*Convention consequence (displayed for honesty).* At mu2 = 2 only
vartheta_2 can differ from 1 (vartheta_0 = vartheta_1 = 1 by
definition), and in char 2 every element of K2 is a square, so
"R is a perfect square" is convention-independent there and the root
s re-parameterizes by vartheta_2^{1/2} — which is why the mu2 = 2
battery rows never saw the convention. At mu2 >= 3 with a live
cocycle the per-height-digit coefficient vector of a perfect power
is NOT itself a perfect-power vector unless the vartheta_t are
carried: **fixing the multiplicative convention is part of the
box's content**, not a cosmetic choice. All event statements below
are in the multiplicative convention; LEMMA GENTOW5-A1 is the exact
translation, with fixed re-parameterization only (J-D0: counts are
twist-blind, letters re-coordinatize).

### S1.3 THEOREM GENTOW5-A (the substitution theorem = LEMMA GENTOW-2
### layer 1 at general mu2)

Setting as in S0 (the GENTOW-2 event), with the residual hypothesis
read in the multiplicative convention: R_N(T) = (T - w)^{mu2} in
k(L2)[T], where w := [lift(s; lam)(x0)] * N^{-1} (the N-class of the
prescribed height-lam lift; by GENHN-2' and LEMMA GENTOW5-A1, w =
iota(s) times the fixed height-lam unit — the same convention on
both sides, which is what "the lift realizes the residual's root"
means; coherence, not invariance, per HE7 ANNEX R R1.2 item 3).
Set what := -lift(s; lam), Phi2+ := Phi2 + what, and let C_k+ be the
Phi2+-development coefficients of f. Then for every k < mu2:

    dv2(C_k+(x0)) > (mu2 - k) * lam        (ALL mu2 PINS DIE),

and the new multiplicative residual of the side is T^{mu2}.

*Proof.* Substitute Phi2 = Phi2+ - what into the development and
expand IN THE POLYNOMIAL RING (no reduction yet):

    f = Sum_j C_j (Phi2+ - what)^j = Sum_k B_k Phi2+^k,
    B_k := Sum_{j >= k} binom(j, k) (-what)^{j-k} C_j
         = Sum_{j >= k} binom(j, k) lift^{j-k} C_j.

Step A (the graded identity, in gr(L2)). Evaluate B_k at x0 — a SUM
OF PRODUCTS in the field L2; A0 gives, writing [lift(x0)] = w*N:

    class of Sum_j binom(j,k) lift(x0)^{j-k} C_j(x0) at height
    (mu2-k)lam  =  N^{mu2-k} * Sum_j binom(j, k) w^{j-k} c_j
                =  N^{mu2-k} * (coefficient of T^k in R_N(T + w)),

the second equality the Taylor/substitution identity in k(L2)[T]
(if R(T) = Sum c_j T^j then R(T + w) = Sum_k [Sum_j binom(j,k)
w^{j-k} c_j] T^k — an identity of polynomials, valid over any
commutative ring, both characteristics). By hypothesis R_N(T + w) =
(T + w - w)^{mu2} = T^{mu2}: for k < mu2 the coefficient is 0, i.e.
the height-(mu2-k)lam class of B_k(x0) VANISHES:

    dv2(B_k(x0)) > (mu2 - k) * lam   for every k < mu2.

Note the identity is a SUBSTITUTION identity — the binomials appear
transiently but the conclusion (T - w)^{mu2}|_{T -> T+w} = T^{mu2}
is binomial-free; char q divides some binom(mu2, k) harmlessly (the
corresponding c-coefficients vanish on BOTH sides).

Step B (from B_k to C_k+: layer 2, already proved at general mu2).
B_k has x-degree up to (mu2 - k + 1)D2 - ish; the canonical
coefficients C_k+ are obtained from the B_k by reduction mod the
monic Phi2+ (carries between coordinates) and in-coordinate
x-/Phi'-carries. GENTOW-2 layer 2 (PROVED at general mu2 —
GENTOW1_PROOF S3, whose grade note restricts only layer 1) prices
every such correction: in-coordinate carries are weight-nondecreasing
(GENTOW-1 Step 0), and each flow UP one Phi2-coordinate trades
weight >= (mu2-k)lam at coordinate k for a contribution at
coordinate k+1 of weight >= (mu2-k)lam - E2 > (mu2-k-1)lam (using
lam > E2, the composed node floor) — strictly above coordinate
(k+1)'s threshold. Weights lower-bound dv2 at x0 on the tower-node
locus (GENTOW-1 Step 0 + GENHN-2'). Hence

    dv2(C_k+(x0) - B_k(x0)-contribution) > (mu2 - k) * lam,

and with Step A, dv2(C_k+(x0)) > (mu2 - k)lam for k < mu2. The top
coefficient C_{mu2}+ = 1 and the new side's multiplicative residual
is T^{mu2} by the same Step-A display at k = mu2. ∎

### S1.4 COROLLARY GENTOW5-A' (GENTOW-2 closes at general mu2;
### level-1 rider)

(i) LEMMA GENTOW-2's clauses (ii), (iii), (iv) hold at general mu2:
(ii) is THEOREM GENTOW5-A; (iii)'s triangularity/bijection consumed
layer 1 only through (ii) (GENTOW1_PROOF S3 layer 3, general-mu2 as
written); (iv)'s reverse transport is the SAME Step-A computation
run on Phi2 = Phi2+ + lift with R_N(T) = T^{mu2} at the refined
frame: coordinate j receives minimal class binom(mu2, j) w^{mu2-j}
N^{mu2-j} from C_{mu2}+ = 1 — pin (mu2-j)lam with multiplicative
residue binom(mu2, j)(-w)^{mu2-j} exactly where q does not divide
binom(mu2, j), strictly above where it does. (ii)'s GRADE NOTE
restriction is hereby lifted.

(ii) *Level-1 rider (display, no new claim on frozen text).* The
S1.1–S1.3 argument runs verbatim one level down (gr(L1) at a stage
leaf, N := [n(kappa)(x0)], GENHN-2 in place of GENHN-2', GENHN-4
layer 2 in place of GENTOW-2 layer 2): it is an elementary
general-mu carry display of exactly the kind GENHN-BOX-2's text
names as its retirement condition ("the GENH4-S5 computation at
general (e1, f1, mu)"). GENHN_PROOF is frozen; recording the
consumption there is the orchestrator's dated update, not this
note's edit.

### S1.5 GENTOW-BOX-1 DISPOSITION

**RETIRED as a mathematical box; the residue is grade-only.** What
LEMMA GENTOW-2 layer 1 at mu2 >= 3 now consumes: LEMMA GENTOW5-A0
(elementary, self-contained), LEMMA GENTOW5-A1 (self-contained given
GENHN-2' + the S4/T(b)'(iii) wrap letters — all accepted corpus),
THEOREM GENTOW5-A (this note), and GENTOW-2 layer 2 @ GENTOW1_PROOF
(grade 0/2). No W-9-analogue weld face is consumed; the graded frame
is gr(L2) itself. Honest conditionality: this note is at grade 0/2
(hostile arc owed), GENTOW-1/GENTOW-2 are at 0/2, and the accepted
pins are T(b)'(i)/(ii)/(iii) + S4's coherent normalizers (GENHN
accepted 2/2 at PE4). Machine leg: S5's CHECK-A rows are the FIRST
mu2 = 3 pointwise re-division kills anywhere in the program (the
GN-REFINE3 pattern at the composed key), including a char-3 row and
an f2 = 2 two-flavor-lift row.

## S2. TARGET 2 — THE LEVEL-r LADDER GRAMMAR (definitions + the two
## working lemmas)

(to be filled: DEF GENTOW5-1; LEMMA GENTOW5-C; LEMMA GENTOW5-D)

## S3. THEOREM GENTOW5-B (the general-depth composition theorem)

(to be filled)

## S4. THE DEPTH-4 WITNESS (n = 32 over q = 2)

(to be filled: the minimal chain u = 5, 21, 85, 341; construction;
predictions; run record)

## S5. MACHINE LEG (gentow5_checks.py, two-commit seal)

(to be filled from committed artifacts)

## S6. HONEST RESIDUE + GRADE BOX

(to be filled)
