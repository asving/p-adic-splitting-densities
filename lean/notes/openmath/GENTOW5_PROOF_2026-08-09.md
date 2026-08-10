# GENTOW-5: the composed graded frame at general mu2 (GENTOW-BOX-1)
# + the level-r ladder grammar (depth >= 4)

**2026-08-09 — SKELETON (per-section commits follow). Unit: GENTOW-5,
BOX-CLOSURE campaign wave B1. Grade target 0/2 (attempt; hostile arc
owed).**

**[ARC — passPE1 2026-08-09: NOT CLEAN, 1 CRITICAL + 2 GAP + 3 MINOR
(GENTOW5_passPE1_report.md @ 0160b94); counter stays 0/2. GT5-r1
repair round 2026-08-10 (this commit series): F-1 the dated GAUGE PIN
on DEF GENTOW5-1's key recipe — khat_t := lift_i(c_t ·
vartheta_{i,f_{i+1}-t}; ·), the level-i telescope-twist form derived
from the level-2 erratum (GENHN 59c1966 + HETOW [r1]; GENTOW1
[GT1-r1] precedent), machine-verified at the PE1 fresh frame FR-1
(S2.1 pin); F-2 S3(a)'s (B-2) leg re-based on GENTOW2-B'(5)'s true
transformation law (the y -> eps*y fallback is deleted-as-false at
its source; B-2 on-the-nose is machine-REFUTED at letter-live grades,
GENTOW2 PE4 @ 2f95be6; GENTOW2 r3 cocycle flip IN-FLIGHT at this
commit); F-3 LEMMA GENTOW5-D's top-grid weight DEFINED (E-part = E_i)
with strictness restricted to interior carries (the i = 2 instance
now matches GENTOW1 Step 0 verbatim); F-4 the HE7 ANNEX R pin folded
to ACCEPTED 2/2 (a472155; orchestrator-authorized, ledger B8
87a7b61); F-5/F-6 instrument-strength + wording disclosures. Repair
record S7; sealed artifacts BYTE-FROZEN. Grade stays 0/2; PE2
next.]**

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
| (2) | depth-4 witness n = 32 q = 2 | GREEN: ladder (16,40,84,170,341) exact, resultant + PARI routes (S4.3) |
| battery | gentow5_checks.py | GREEN 92 checks / 0 violations, 5/5 teeth-and-flags as predicted (S5) |

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

    c_j = iota(gamma_j) * theta_{mu2-j}^{-1},
    theta_t := [n2hat(lam)(x0)]^t * [n2hat(t*lam)(x0)]^{-1}
             = iota(vartheta_t),  vartheta_t in K2^x FIXED
    (theta_0 = theta_1 = 1; equivalently gamma_j = c_j*vartheta_{mu2-j}),

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
k(L2)[T], where w := [lift(s; lam)(x0)] * N^{-1} = iota(s) ON THE
NOSE (theta_1 = 1: at the single height lam the two conventions
coincide, so the lift's digit IS the root's coordinate — coherence,
not invariance, per HE7 ANNEX R R1.2 item 3).
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

### S2.1 DEF GENTOW5-1 (the depth-r tower data)

Indices: level 1 = the outer stage (key Phi_1 := Phi', deg D_1 =
e1f1); level i has stage data (e_i, f_i) with properness l_i :=
e_i f_i >= 2 at every i >= 2 (an improper stage is a refinement, not
a level — FGMN Lemma 3.5/Prop 3.7 collapsing, per GENTOW2 S6 (H-f)).
Write ehat_i := e_1 ... e_i, D_i := l_1 ... l_i (l_1 := e1f1),
K_0 := F_Q, K_i := F_{Q^{f_1...f_i}}.

* **Ladders.** dv_i := ehat_i * v. Heights at level-(i+1) points:
  u_1 := h = dv_1(x); u_{i+1} := dv_{i+1}(Phi_i(xi)) with
  gcd(u_{i+1}, e_{i+1}) = 1; so dv_i(Phi_j) = (ehat_i/ehat_{j+1}) *
  u_{j+1} for j < i. Side constants E_i := e_i f_i u_i (E_1 = D_1 h).
  **Floor chain:** u_{i+1} > e_{i+1} E_i (provenance: the level-i
  budgets' node corollary, S3(e); at i = 1 this is the [r1] node
  floor u_2 > e_2 D'h verbatim since E_1 = D'h).

* **Normalizers (the recursion of HE7-2', tower-based).**
  n1hat(m) := pi^a x^{i0} (i0 < e1, e1*a + i0*h = m); for i >= 1

      nhat_{i+1}(k) := nhat_i(m_i(k)) * Phi_i^{b_i(k)},
      e_{i+1} m_i(k) + b_i(k) u_{i+1} = k,  0 <= b_i(k) < e_{i+1}

  (unique since gcd(u_{i+1}, e_{i+1}) = 1). Unrolled: nhat_i(m) =
  pi^a x^{i0} Phi_1^{b_1} ... Phi_{i-1}^{b_{i-1}} with i0 < e1,
  b_j < e_{j+1}. At i = 2 this is GENTOW-1 S3's n2hat verbatim.
  NOTE the base differs from HE7-2's varpi-powers (varpi^k has
  unreduced x-degree); the two systems differ per height by a fixed
  unit — S2.3's remark.

* **Cocycle + letters.** tau_i(a, b) := nhat_i(a) nhat_i(b) /
  nhat_i(a+b); the level letters Lam_i := Phi_i^{e_{i+1}} /
  nhat_i(u_{i+1}) (dv-value 0 at level-(i+1) points), beta_{i,xi} :=
  res(Lam_i(xi)); transport tower iota^{(i+1)} extending iota^{(i)}
  by beta_i -> beta_{i,xi} — ANNEX-DEF HE7-2''s attached objects,
  tower-instantiated.

* **K_i-digit lifts.** For c in K_i and height m, lift_i(c; m) :=
  the sum of the f_1...f_i within-class monomials x^{i0+e1 r}
  Phi_1^{b_1 + e_2 t_1} ... at height m with O-digit coefficients
  realizing c in the coherent normalization (deg < D_i always);
  at i = 2 this is GENTOW-2's lift(s; m).

* **THE COMPOSED KEY RECIPE (the charge's display). [GT5-r1 GAUGE
  PIN — the governing pin of the r1 round; PE1 F-1 CRITICAL].**
  Given stage data (e_{i+1}, f_{i+1}) and monic irreducible
  psi_{i+1} = y^{f_{i+1}} - Sum_{t<f_{i+1}} c_t y^t over K_i with
  c_0 != 0:

      Phi_{i+1} := Phi_i^{e_{i+1} f_{i+1}}
                   - Sum_{t < f_{i+1}} khat_t * Phi_i^{e_{i+1} t},
      khat_t := lift_i(c_t * vartheta_{i, f_{i+1}-t};
                       u_{i+1}(f_{i+1} - t))        (0 if c_t = 0),

  where vartheta_{i,s} := res(nhat_i(u_{i+1})^s / nhat_i(s*u_{i+1}))
  in K_i^x is the FIXED telescope unit of the tau_i-cocycle (S1.2's
  vartheta and S2.3 step (3), run at level i and heights multiples
  of u_{i+1}): vartheta_{i,0} = vartheta_{i,1} = 1,
  vartheta_{i,s+1} = vartheta_{i,s} * res(tau_i(s*u_{i+1}, u_{i+1})).
  [GT5-r1 derivation, NOT a transcription. Why the twist: grouping
  the recipe in Phi_i-slots, the slot-t MULTIPLICATIVE residual
  coefficient (S1.2's convention — the one the side residual and
  FGMN's R-operators read) is res(khat_t / nhat_i(u_{i+1})^{f-t}) =
  digit(khat_t) * res(nhat_i((f-t)u_{i+1}) / nhat_i(u_{i+1})^{f-t})
  = digit(khat_t) * vartheta_{i,f-t}^{-1} (f := f_{i+1}); for that
  coefficient to equal psi_{i+1}'s c_t, the prescribed COHERENT
  digit must be c_t * vartheta_{i,f-t} — LEMMA GENTOW5-A1's
  dictionary gamma = c * vartheta, applied in the BUILDING
  direction. The plain lift lift_i(c_t; ·) is the GAUGE-NAIVE form:
  its multiplicative coefficient is c_t * vartheta^{-1}, wrong
  wherever the letters are live. Level-2 recovery: n1hat monomials
  are pi^a x^{i0}; multiplying s copies of n1hat(u_2) accumulates
  x-exponent s*i(u_2), reduced to ladder range by
  floor(s*i(u_2)/e1) x-wraps x^{e1} = pi^h * (x^{e1}/pi^h), so
  vartheta_{1,s} = eta^{floor(s*i(u_2)/e1)}; at s = f_2 - t this is
  EXACTLY the GENHN dated erratum's corrected chat_t :=
  lift(c_t*eta^{W(t)}), W(t) = floor((f_2-t)*i(u_2)/e1) (erratum
  59c1966, provoked by HETOW PE1 F-1; pinned at GENTOW1 by
  [GT1-r1] 477b1b1). At i >= 2, vartheta_{i,s} is the fixed letter
  monomial in eta, beta_1, ..., beta_{i-1} through iota^{(i)}
  (S2.3 step (3)'s computation). At any frame where each
  c_t * (vartheta_{i,f-t} - 1) = 0 — in particular all letters = 1,
  or f_{i+1} = 1 (only s = 1 occurs, vartheta_{i,1} = 1) —
  corrected = naive. MACHINE VERIFICATION at a letter-live frame
  (the PE1 fresh instrument gentow5_pe1_fresh.py @ 0160b94, FR-1:
  p = 3, Phi_1 = x^2 - 6, eta = 2, (e_2,f_2) = (1,2), u_2 = 3,
  psi_2 = y^2 + y + 2, i(u_2) = 1 so W(1) = 0, W(0) = 1): the
  corrected key Phi_1^2 - 6x*Phi_1 - 54 is the carrier — sigma =
  (2,2), nfeltval(Phi_1) = 3 exact; the gauge-naive key
  Phi_1^2 - 6x*Phi_1 - 27 has sigma = {(4,1)} with degenerate
  residual (y-1)^2 — THEOREM GENTOW5-B (a)/(b) fail at the naive
  display there. This pin governs khat_t at its uses below (S2.4's
  INV-j heights — value-blind, see there; S3's statement + (a),
  (b), (c) Step 5, (d); S4.1's witness keys — seam-blind, see
  there).]
  Monic of degree D_{i+1}; every side term at dv_{i+1}-height
  E_{i+1} exactly (e_{i+1} * u_{i+1}(f_{i+1}-t) + e_{i+1} t u_{i+1}
  = E_{i+1}; the top term e_{i+1} f_{i+1} u_{i+1} = E_{i+1} — the
  vartheta twist is a residue-level unit, height-blind).
  At i = 1 this is T(b)''s Phi2 AT ITS ERRATUM-CORRECTED DISPLAY
  (59c1966), NOT the gauge-naive original; at i = 2 the r3 box's
  Phi3 with vartheta_2-corrected digits.

* **The depth-(i+1) node locus P_{i+1}** := roots xi with
  v(x(xi)) = h/e1 exactly, eta(xi) a psi_1-root, and inductively
  v(Phi_j(xi)) = u_{j+1}/ehat_{j+1} exactly with the level-(j+1)
  residue class a psi_{j+1}-root, for j < i+1 — the tower transport
  chain (T(b)'(iii) at i = 1; GENTOW2-A(d)'s data at i = 2).

First-live arithmetic: a depth-r tower with a live top problem
mu_r >= 2 needs n = D_r * mu_r >= 2^{r+1}; depth 4 first lives at
n = 32 (S4's witness is exactly minimal).

### S2.2 Consistency checks on the recursion (worked pins)

n3hat(85) at the S4 chain ((e_i) = (2,2,2,2), h = 1, u = 5, 21, 85):
recursion: b_3... level 3: 2m + 21b = 85, b < 2 -> b = 1, m = 32;
level 2: 2m' + 5b' = 32, b' < 2 -> b' = 0, m' = 16; base: 2a + i0 =
16 -> i0 = 0, a = 8. n3hat(85) = 2^8 * Phi_2 — matching the direct
unrolled solve (16a + 8 i0 + 20 b_1 + 42 b_2 : mod-parity forces
b_2 = 1, then b_1 = 0, i0 = 0, a = 8... on the dv_4 ladder; see S4).
The r3 witness n2hat(21) = 16 Phi' is the recursion at level 2:
2m + 5b = 21 -> b = 1, m = 8 -> 2a + i0 = 8 -> 2^4. Both match the
committed runners' values (genhnr2_supp L388-389; gentow2 W1).

### S2.3 LEMMA GENTOW5-C ((SLOT_i) + (LIFT_i) for the tower ladder)

**Statement.** Let i >= 1 and assume the tower data of DEF GENTOW5-1
through level i+1 with P_{i+1} nonempty, and (SLOT_{i-1}) at level i
(base: i = 1 is GENHN-2 + HE6-1's transport identity; i = 2 is
GENHN-2' — both accepted). Let xi in P_{i+1}, C in O[x] with
0 != deg C < D_{i+1}, developed C = Sum_{b < e_{i+1} f_{i+1}} c_b
Phi_i^b with deg c_b < D_i. Then
dv_{i+1}(C(xi)) equals the slot minimum EXACTLY; the minimizing b
lie in one class mod e_{i+1}; and the height-k residue against
nhat_{i+1}(k)(xi) is iota^{(i+1)}(Sum_t gamma_t vartheta_t
beta_i^t) != 0 with gamma_t the level-i digit symbols ((SLOT_{i-1}))
and vartheta_t the FIXED twist units of the telescoped tau_i-cocycle
— i.e. one K_{i+1}-digit per dv_{i+1}-height, class separation
mod e_{i+1} between Phi_i-slots and mod ehat_{i+1} overall.
(LIFT_i): k-uniformly above the bound recursion bound_{i+1} =
(l_{i+1}-1)u_{i+1} + e...*bound_i, every K_{i+1}-residue at height k
is realized by some C with deg < D_{i+1} (inverse-twisted digits).

**Proof: ANNEX-THEOREM R1-b/R1-c's proofs, re-based.** The HE7
ANNEX R proofs consume exactly four clauses of their level-i datum:
(a) values exact one level down ((SLOT_{i-1}), our induction
hypothesis); (b) the defining clause w_{i+1}(Phi_i(xi)) = u_{i+1}
exactly (our P_{i+1}, clause j = i); (c) gcd(u_{i+1}, e_{i+1}) = 1
(DEF GENTOW5-1); (d) {1, beta_i, ..., beta_i^{g-1}} a K_i-basis of
K_{i+1} with beta_i := the level-(i+1) residue letter, r_i := its
minimal polynomial irreducible (our psi_{i+1}-root clause of
P_{i+1}, f_{i+1} = deg psi_{i+1}). Steps: (1) values of
c_b(xi)Phi_i(xi)^b are e_{i+1}*w_i(c_b) + b*u_{i+1} exactly by
(a)+(b); (2) cross-class ties impossible: b*u_{i+1} mod e_{i+1}
bijective by (c); (3) within one class, slots b0 + e_{i+1}t: the
monomial identity of R1-b (R1.2) with theta_t telescoping into
tau_i-values; each theta_t has residue a fixed K_i^x-unit by the
S1.2-style cocycle computation run at level i (the letter monomial —
tau_i is a Laurent monomial in pi, x, Phi_1, ..., Phi_{i-1} of
dv-value 0, residue a fixed product of the letters beta_1 ... beta_{i-1}
through iota^{(i)}); (4) summing the class, the residue is the
displayed K_i-combination of beta_i-powers, nonzero by (d) since the
gamma_t vanish iff their slots do not attain and at least one
attains — no cancellation, value exact. (LIFT_i): R1-c verbatim —
prescribe the level-i digits INVERSE-twisted by vartheta_t^{-1}
((LIFT_{i-1}) supplies them one level down; base = the level-1/2
lift lemmas, accepted); the bound arithmetic never sees residues.
**Grade honesty:** this is HE7 ANNEX R's R1-b/R1-c argument
transported onto the tower ladder — the annex is POST-RATIFICATION,
UNPASSED (annex grade); the transport itself (the four-clause
instantiation table above) is this note's, and the base cases i <= 2
rest only on accepted corpus. Every i >= 3 consumer below carries
this annex-grade pin explicitly. ∎

*Remark (HE7 base vs tower base).* HE7-2''s n_1 = varpi-powers and
our n1hat differ per height by the fixed wrap letter (both are
value-m monomials; the quotient is a value-0 Laurent monomial in
x, pi with residue a fixed power of the level-1 letter). By J-D0
(counts twist-blind, letters re-coordinatize; R1.2 item 7) every
count/degree/vanishing statement transports between the two systems;
residue letters re-coordinatize by fixed units. We work in the tower
base throughout; no invariance under CHANGING systems mid-argument
is consumed (that stronger claim is false — HE7-T-BADTWIST).

### S2.4 LEMMA GENTOW5-D (Step-0 carry monotonicity is
### level-agnostic — the charge's check, answered YES)

**Weight. [GT5-r1 — PE1 F-3: the top-grid term is now DEFINED.]**
On monomials M = pi^v x^{a} Phi_1^{J_1} ... Phi_i^{J_i}
(exponents unbounded) define

    wt_i(M) := ehat_i*v + a*(ehat_i/e1)h
               + Sum_{j<i} J_j * (ehat_i/ehat_{j+1}) u_{j+1}
               + J_i * E_i,

i.e. the TOP variable Phi_i carries weight E_i = e_i f_i u_i per
unit exponent — the in-datum lower bound (dv_i(Phi_i(xi)) > E_i on
the tower locus by the field floor, vs the EXACT interior values
dv_i(Phi_j(xi)) = (ehat_i/ehat_{j+1})u_{j+1} for j < i); the
pre-repair display left this term as an undefined "E-part". Note
wt_i consumes NO data beyond the depth-i datum: u_{i+1} does not
appear.

**Statement [GT5-r1 restated — strictness weakened to what the
induction needs].** For every level i, the i reduction moves — the
x-carry (a >= D_1) and the Phi_j-carries (J_j >= l_{j+1}, j < i) —
are wt_i-NONDECREASING; lift-generated terms preserve weight
exactly; the key-part of each INTERIOR carry (the x-carry and the
Phi_j-carries with j < i-1) strictly raises it, while the TOP
carry's key-part (j = i-1: key-part Phi_i at weight E_i =
wt(Phi_{i-1}^{l_i})) PRESERVES it exactly. Hence "all slots at
weight >= W" is the same condition on every grid of the tower (the
two-directional rewriting closes), and per-slot weight arithmetic
converts to the digit floors verbatim as in GENTOW-1 Step 0.
[GT5-r1 consumer note: nondecreasing is all any named consumer of
this lemma uses (GENTOW5-A Step B's grid translation, S3(c) Steps
0/3, S3(d)); the strict FLOW-UP pricing there comes from lam > E
separately, never from this lemma's strict clause. The pre-repair
blanket "the key-part of each carry strictly raises it" was FALSE
at the top carry — and contradicted the lemma's own i = 2
instance: GENTOW1_PROOF S2 Step 0 prices the Phi_2-part "at weight
E2 exactly" (PRESERVED). Under this restatement the i = 2 instance
IS the top-carry case verbatim: at i = 2 the only Phi_j-carry is
j = 1 = i-1, the top carry, key-part Phi_2 at weight E_2 —
GENTOW-1's Step 0 display recovered, contradiction resolved.
Failure mode fenced, worked at the S4 witness chain's grid 4
(u = (1,5,21,85), E_4 = 170): the top carry Phi_3^2 = Phi_4 +
2^8*Phi_2 has wt_4(Phi_3^2) = 2*(ehat_4/ehat_4)*u_4 = 2*85 = 170,
Phi_4-part = E_4 = 170, and lift-part wt(2^8*Phi_2) = 16*8 + 2*21
= 170 — all three EQUAL: any downstream lean on top-carry
strictness would be unsound; none exists in this note (checked at
PE1 and re-checked this round).]

*Proof (the two displays, uniform in j).*
* x-carry: x^{D_1} = Phi_1 + tail, tail monomials x^c pi^g with
  g >= (D_1 - c)h/e1 (Phi_1's one side): tail wt >=
  (ehat_i/e1) D_1 h = wt(x^{D_1}), equality on the side lattice;
  Phi_1-part wt = (ehat_i/ehat_2) u_2 > (ehat_i/ehat_2) e_2 E_1 =
  (ehat_i/e1) D_1 h — STRICT by the floor chain at j = 1.
* Phi_j-carry: Phi_j^{l_{j+1}} = Phi_{j+1} + Sum_t khat_t
  Phi_j^{e_{j+1}t}; each lift term has wt =
  (ehat_i/ehat_{j+1}) [e_{j+1} u_{j+1}... ] — compute:
  khat_t's monomials all sit at dv_j-height u_{j+1}(f_{j+1}-t)
  exactly (single-height lifts, DEF GENTOW5-1 — [GT5-r1] the gauge
  pin's vartheta twist is a residue unit, so the corrected khat_t
  sits at the SAME heights: this display is value-blind, the
  GENTOW1 [GT1-r1] Step-0 immunity verbatim), contributing
  (ehat_i/ehat_{j+1}) e_{j+1} u_{j+1}(f_{j+1}-t) +
  e_{j+1} t (ehat_i/ehat_{j+1}) u_{j+1} = (ehat_i/ehat_{j+1})
  E_{j+1} = wt(Phi_j^{l_{j+1}}) — PRESERVED exactly; the key-part
  splits [GT5-r1]:
    - INTERIOR (j <= i-2): the Phi_{j+1}-part has wt =
      (ehat_i/ehat_{j+2}) u_{j+2} > (ehat_i/ehat_{j+2}) e_{j+2}
      E_{j+1} = (ehat_i/ehat_{j+1}) E_{j+1} — STRICT by floor rung
      j+1 (u_{j+2} > e_{j+2}E_{j+1}), which is IN-DATUM since
      j+2 <= i;
    - TOP (j = i-1): the Phi_i-part has wt = E_i = l_i u_i =
      wt(Phi_{i-1}^{l_i}) — PRESERVED exactly, NO floor rung
      consumed (the pre-repair uniform pricing read the top
      key-part at u_{i+1}/e_{i+1}: non-integer, and at the top grid
      of a depth-r tower rung r references u_{r+1} = EVENT data
      outside the statement's floor chain — PE1 F-3's audit; the
      repair prices it at the defined weight E_i instead).
The only inputs are (INV-j): the recipe keys' side terms at exact
height E_{j+1} (DEF GENTOW5-1's construction, gauge-pin-stable) and
(FLOOR-j): u_{j+1} > e_{j+1} E_j, consumed at rungs 1 (x-carry)
through i-1 (deepest interior carry) — all inside the depth-i
datum. Both are level-uniform; GENTOW-1's Step 0 is the i = 2
instance ("two carries priced by two sides" becomes "i carries
priced by i sides", each the same two lines) — at i = 2 the sole
Phi_j-carry is the TOP carry j = 1, priced PRESERVED at E_2, which
is GENTOW1 S2 Step 0's own display ("the Phi2-part at weight E2
exactly"). The converse rewriting (Phi_{j+1} = Phi_j^{l_{j+1}} -
weight-E_{j+1} lifts) is weight-nondecreasing by the same
displays. ∎

## S3. THEOREM GENTOW5-B (the general-depth composition theorem)

**Statement.** Fix a base (Q; h) and a depth-r tower datum per DEF
GENTOW5-1: stage data (e_i, f_i, psi_i) with properness l_i >= 2
(i >= 2), heights u_i satisfying the floor chain u_{i+1} >
e_{i+1} E_i, keys Phi_1, ..., Phi_r built by THE RECIPE [GT5-r1: in
its GAUGE-CORRECTED form — the S2.1 pin's vartheta-twisted khat_t;
every clause below reads AT that form, and (a)/(b) are FALSE at the
gauge-naive display on letter-live frames (PE1 FR-1's machine
counter-instance, quoted at the S2.1 pin)], and the
terminal inductive valuation nu_r (the MacLane chain mu_0 -(x,
lam_1)-> mu_1 -(Phi_1, lam_2)-> ... -> mu_r = nu_r in FGMN
coordinates, the GENTOW2 S2 dictionary at every level). Then, by
induction on i < r:

(a) [KEY CERTIFICATE, level-general] Phi_{i+1} is a key polynomial
for nu_i and a PRIME polynomial (monic, O-coefficients, irreducible
over K_v), with R_{nu_i}(Phi_{i+1}) = psi_{i+1}.
(b) [ONE-SIDEDNESS AT EVERY LEVEL — the FGMN cite, arbitrary chain
length] for every j <= i+1, the level-(j-1) polygon N_j(Phi_{i+1})
is one-sided of slope -lam_j with residual R_{j-1}(Phi_{i+1}) =
psi_{j-1}^{l_j ... l_{i+1}}, and every root xi of Phi_{i+1} has the
EXACT intermediate values v(Phi_{j-1}(xi)) = u_j / ehat_j — i.e.
xi in P_{i+1}: the recipe's roots ARE depth-(i+1) node points.
(c) [BUDGETS AT LEVEL i+1 — GENTOW-1 re-based] the level-(i+1)
tower-entry locus T_{i+1} (monic f of degree n = mu * D_{i+1} whose
level-(i+1) stage read exhibits the full side of slope
kappa_{i+2} := u_{i+2}/e_{i+2} with residual psi_{i+2}^{mu}) is
weight-characterized: f in T_{i+1} iff every slot of f -
Phi_{i+1}^{mu} clears weight mu*E_{i+1} + 1, with the per-slot digit
floors, the fibration, the node pins p_j >= (mu-j)E_{i+1} + 1, and
the field floor dv_{i+1}(Phi_{i+1}(xi)) > E_{i+1}, exactly as in
LEMMA GENTOW-1 (a)-(d).
(d) [REFINE TRANSFER AT LEVEL i+1, GENERAL mu] at a composed event
of integer dv_{i+1}-slope lam > E_{i+1} with residual (T-s)^{mu}
(multiplicative convention), the refine Phi_{i+1}+ := Phi_{i+1} -
lift_{i+1}(s; lam) kills the mu pins and bijects onto the
lam-floored node — THEOREM GENTOW5-A's statement with 2 -> i+1.
(e) [NODE-FLOOR COROLLARY = the floor chain's provenance] every
side of the level-(i+1) composed polygon of an f in T_{i+1} has
dv-slope > E_{i+1} > dv_{i+1}(x^{D_{i+1}}); hence the NEXT stage's
height obeys u_{i+2} > e_{i+2} E_{i+1} automatically at tower
leaves — the induction feeds itself (COR GENTOW-1.1 at every level).

**Proof.**

*(a) — GENTOW2-A's proof with r+1 for 4.* GENTOW2 S7 already
recorded that THEOREM GENTOW2-A's proof pattern is level-uniform
("Cor 6.4 is proved for chains of any length r, and the
recipe/bridge argument reads verbatim with r+1 in place of 4
PROVIDED the level-r analogues of (B-1)/(B-2) are proved"). The two
provisos are now supplied:
  (B-1 at level i) the dv_i ladder value of a deg < D_i ladder
  element equals its mu_i-value — this is LEMMA GENTOW5-C's
  (SLOT_i) value clause (exactness of the slot minimum), which
  identifies the grid minimum with the inductive-valuation value on
  deg < D_i polynomials at level-i points; at i <= 2 it is the
  accepted GENHN-2/2'.
  (B-2 at level i) [GT5-r1 REWRITTEN — PE1 F-2. The pre-repair
  clause here consumed the y -> eps*y fallback, which GENTOW2 r1
  (dd44d20) DELETED AS FALSE at f >= 2 (a fixed-unit twist scales
  every non-leading digit uniformly, not grade-covariantly; the
  displayed F4 counter-instance kills irreducibility transfer), and
  asserted a fixed-unit form of B-2 that GENTOW2 PE4 (2f95be6) has
  since machine-REFUTED at letter-live grades: the measured unit
  family is GRADE-VARYING (u = 1 at grade 19, z1 at grade 38 on the
  LP1 tower; cocycle res(nhat2(19)^2/nhat2(38)) = z1^2 exact). The
  corrected leg:] the repo K_i-digit read and FGMN's Def 3.16
  epsilon-normalized coordinate agree up to a per-grade,
  x0-free and g-free unit family u_i(beta) in K_i^x — at i = 2 this
  is LEMMA GENTOW2-B'(3) (S5.1 there, [r1]/[r2] state: u(beta) :=
  R_{3,beta}(nhat_2(beta-hat)), DERIVED from B-1 no-cancellation +
  the divide-by-Phi_2 h-step + Lemma 3.17); at i >= 3 the same
  derivation transports with (SLOT_i) = LEMMA GENTOW5-C in place of
  B-1 (per-grade shape and x0-freeness carry; the transport rides
  the S2.3 annex-precedent pin). The discharge of (a) then uses
  B'(5)'s TRUE transformation law, not any eps-substitution: the
  recipe at digit string (c_t) realizes R_{nu_i}(Phi_{i+1}) =
  y^{f_{i+1}} - Sum_t u_i(beta_t) c_t y^t; since u_i is x0-free and
  the digit string is freely prescribable ((LIFT_i)), the
  re-parameterized prescription c_t -> u_i(beta_t)^{-1} c_t
  realizes the TARGET psi_{i+1} exactly — monic irreducible of
  degree f_{i+1} with nonzero constant term, every clause consumed
  downstream intact. Honest conditionality, named: what is consumed
  is B'(3)'s per-grade-unit COMPARISON SHAPE (derived at i = 2,
  transported at i >= 3), never B-2 on-the-nose (u = 1), which is
  FALSE at letter-live grades. [In-flight pin, checked at this
  commit: GENTOW2 r3 — flipping B-2 to its cocycle form u(beta) =
  the vartheta-telescope unit, i.e. FGMN R-read = the repo
  MULTIPLICATIVE read, which PE4's decode leg confirmed at 14/0 —
  is DISPATCHED in this same wave (ledger B9, 87a7b61) and NOT YET
  LANDED at GENTOW2_PROOF HEAD = 7532acb as of this commit. If r3
  lands the cocycle form, the S2.1 gauge-corrected recipe realizes
  psi_{i+1} with NO re-parameterization (its vartheta twist IS the
  u-family); the discharge above does not wait for it — arbitrary
  x0-free u suffices.]
With (B-1)/(B-2 as corrected), LEMMA GENTOW2-B's proof runs at
level i on the re-parameterized prescription: additivity
(Cor 4.7(1) [Q8]) + eq (14) [Q7] give
R_{nu_i}(Phi_{i+1}) = y^{f_{i+1}} - Sum c_t y^t = psi_{i+1}; the
degree-forcing display [Q6] + Lemma 5.3(2) [Q4] certify
Phi_{i+1} in KP(nu_i); Lemma 1.11 [Q1] + Cor 1.13 [Q2] give prime.
Non-equivalence to the previous key: R(Phi_{i+1}) = psi_{i+1} != 1 =
R(Phi_i) by eq (14), Prop 5.7 [Q7]. ∎(a)

*(b) — the cite fires at arbitrary r.* Theorem 6.3 [Q9] with
F = phi = Phi_{i+1}, mu = nu_i (F = phi so phi |_mu F); Corollary
6.4 [Q10] with the length-(i+1) chain: its quantifier is "for any
1 <= j <= r" — THE ONE-SIDEDNESS IS LEVEL-GENERAL IN THE SOURCE;
no per-level work remains. Its display (23) gives the residual
powers R_{j-1}(F) = psi_{j-1}^{l_j...} and the middle clause
mu(phi_j) = v(phi_j(theta)) gives the exact intermediate values at
every root — with the psi_{j}-root residue classes from the
residual power (no root besides psi_j's, the GENTOW2-A consumption
note verbatim), every root lies in P_{i+1}. The repo polygon =
FGMN polygon under the S2 shear (GENTOW2 S2, level-general as an
affine map per level). ∎(b)

*(c) — GENTOW-1's Steps 0-5 with the substitution table
(D', e2, u2, E2, GENHN-2') -> (D_{i+1} composition data, e_{i+2},
u_{i+2}, E_{i+1} -> E_{i+2}, (SLOT_{i+1})).* The audit of each step
for level-blindness:
  Step 0 = LEMMA GENTOW5-D (proved level-agnostic; the ONLY
  level-sensitive content was the carry pricing, now uniform).
  Step 1 (the key power's own development): R_{nu}(Phi_{i+2}^{mu}) =
  psi_{i+2}^{mu} by multiplicativity Cor 4.7(3) [Q8] — cleaner than
  the level-2 hand display; slots at weight >= mu*E_{i+2} with the
  graded layer psi-power by (b) + LEMMA GENTOW5-D's grid
  translation.
  Step 2 (realizability): digits above floors put every slot of
  g := f - Phi_{i+2}^{mu}... (level i+2 per the statement's (c) at
  i+1 — indices as displayed) above the side; the level-(i+1) stage
  read then shows the full side with residual psi^{mu} exactly
  ((SLOT_{i+1}) + Step 1). THE DEEPER READS: rather than the
  level-2 x-polygon display, run the entry ladder bottom-up: at
  level j (j <= i), given xi forced to P_j, the level-j read of f
  has pins = Phi_{i+2}^{mu}'s (g strictly above, by GENTOW5-D both
  grids agree on "above"), whose side residual is the psi_j-power
  of (b)+Cor 4.7(3); the zero-sum 0 = f(xi) forces the level-j side
  polynomial to vanish at the next residue class, i.e. the class is
  a psi_j-root: xi in P_{j+1}. Induction up to j = i+1, then Thm
  6.3 fires on each prime factor (v(Phi_{i+1}(theta)) > nu(Phi_{i+1})
  read off the top side) and Cor 6.4 pins the factor's data. [This
  replaces GENTOW-1 Step 2's outer-grammar display, which does not
  transpose as one line; the ladder argument is the classical
  Ore/Montes ascent and each rung is one (SLOT_j) read.]
  Step 3 (necessity + fibration): verbatim — lattice-digit
  cancellation to one digit higher, off-lattice strictly above,
  Step 0 conversion, triangularity via monic division unipotent in
  the x-filtration (a composition of i+2 monic divisions now — the
  same unipotence).
  Step 4 (node): (SLOT_{i+1}) reads p_j as the slot-min; equality
  realized in every residue class mod ehat_{i+2} by the ITERATED
  class separation (the CRT solve now runs down the recursion:
  choose b_{i+1} mod e_{i+2}, then descend — DEF GENTOW5-1's
  uniqueness clause).
  Step 5 (field floor): every recipe side term at dv-height
  E_{i+2} exactly, common coherent normalizer, residue assembles to
  (unit)*psi_{i+2}(class) = 0, ultrametric strict — verbatim with
  the S1.2 cocycle in place of the level-2 wraps. ∎(c)
*(d)* — S1's proof is level-blind: LEMMA GENTOW5-A0 holds at any
leaf field; LEMMA GENTOW5-A1's cocycle computation is S2.3's step
(3) (the tau_i letter monomial); layer 2 = LEMMA GENTOW5-D + the
flow-up pricing lam > E_{i+1} (the floor); layer 3 as in GENTOW-2.
∎(d)
*(e)* — COR GENTOW-1.1's two-line convexity argument with E_2 ->
E_{i+1}: pins >= (mu-j)E_{i+1} + 1 with right endpoint (mu, 0)
force every side slope > E_{i+1}; and E_{i+1} = e_{i+1}f_{i+1}
u_{i+1} > e_{i+1}f_{i+1} e_{i+1} E_i >= dv_{i+1}(x^{D_{i+1}}) =
D_{i+1} * (ehat_{i+1}/e1) h by telescoping the floor chain down to
E_1 = D_1 h. ∎(e)

**What the induction consumes, per rung (the honest pin stack).**
Accepted 2/2: T(b)'(i)/(ii)/(iii) + GENHN-2/2' + S4 normalizers
(rungs i <= 2). Cited at verified numbering: FGMN [Q1]-[Q10]
(level-general by their own quantifiers; faithfulness per GENTOW2
S6, unchanged). Grade 0/2: GENTOW-1 (budgets pattern), GENTOW-2
(refine pattern), GENTOW2-A/B (cite pattern), THIS NOTE. ANNEX
GRADE (unpassed): HE7 ANNEX R's R1-b/R1-c ARGUMENT, consumed at
rungs i >= 3 through LEMMA GENTOW5-C (the proof is reproduced
tower-side, but its correctness precedent is the annex's — named,
not hidden). The depth->=4 region has machine contact ONLY through
S4's witness (one exact instance) + HE7 R1.3's level-3 leg one
ladder over; no count law at depth >= 3 is claimed measured.

## S4. THE DEPTH-4 WITNESS (n = 32 over q = 2)

### S4.1 The minimal chain (u_{i+1} = 4u_i + 1 — every floor tight)

q = 2, h = 1, all stages (e_i, f_i) = (2, 1), all psi_i = y - 1
(K_i = F_2 throughout — the minimal alphabet; properness l_i = 2).
The floor chain u_{i+1} > e_{i+1}E_i = 4u_i admits the MINIMAL odd
solutions u_{i+1} = 4u_i + 1 from u_1 = h = 1:

    u = (1,) 5, 21, 85, 341;   E_i = 2u_i = (2,) 10, 42, 170;
    dv_i = 2^i v;  D_i = 2^i.

Keys by THE RECIPE (each khat = nhat_i(u_{i+1}), digit 1; S2.2's
recursion solves):

    Phi_1 = x^2 - 2
    Phi_2 = Phi_1^2 - 4x            (nhat_1(5)  = 4x)
    Phi_3 = Phi_2^2 - 16 Phi_1      (nhat_2(21) = 16 Phi_1)
    Phi_4 = Phi_3^2 - 256 Phi_2     (nhat_3(85) = 256 Phi_2)

(Phi_2, Phi_3 are the committed W1 objects of GENTOW2; Phi_4 is
NEW — the first depth-4 key anywhere in the program.) The degree-32
member, one more tight rung (m* = 4*341/4... the top height
m* > e*E_4 = 340, minimal odd 341 on dv_4):

    f32 := Phi_4^2 - 2^16 Phi_3     (nhat_4(341) = 2^16 Phi_3),

deg 32 = the first-live depth-4 degree (S2.1's arithmetic 2^{r+1}).

### S4.2 Preregistered predictions (sealed in the battery docstring)

By THEOREM GENTOW5-B (b)+(e) every root xi of f32 carries the EXACT
ladder v(x) = 1/2, v(Phi_1) = 5/4, v(Phi_2) = 21/8, v(Phi_3) =
85/16, v(Phi_4) = 341/32; f32 is irreducible over Q_2 with
e = 32, f = 1 (RAM leaf at the odd top height). Machine forms:
* P-B4 (RESULTANT LADDER, exact-integer — the "nfeltval-only"
  route, PARI-free): v_2(Res(f32, g)) = 32*v(g(xi)) for g = x,
  Phi_1, Phi_2, Phi_3, Phi_4 -> (16, 40, 84, 170, 341); and at the
  depth-4 KEY itself: v_2(Res(Phi_4, g)) -> (8, 20, 42, 85).
* P-B3 (ONE-SIDEDNESS AT EVERY LEVEL — Cor 6.4's display, exact):
  the Phi_j-adic polygons of Phi_{i+1} and f32 are one-sided of the
  predicted slopes (5, 21, 85/2, 341/2 at the top reads; chords
  with on-chord support ONLY at the char-2-surviving binomial spots
  {0, l...}: e.g. Phi_1-adic Phi_4 on-chord at j in {0, 8} only,
  Phi_2-adic Phi_4 at j in {0, 4} only — (y+1)^{2^k} = y^{2^k}+1).
* P-B1/B2 (grammar arithmetic): floor chain tight; every recipe
  side term at height E_{i+1} exactly.
* P-C (PARI leg, DETACHED): factorpadic(f32, 2) returns ONE factor
  of degree 32; nfinit([f32,[2]]) + idealprimedec gives a single
  prime with (e, f) = (32, 1) and nfeltval ladder (16, 40, 84, 170,
  341). Budgeted with timeout; infeasibility disclosed, not fatal
  (P-B4 is the exact witness either way).
* T-B1 (tooth, the even-height mutant AT the node — STRONG FORM,
  hand-derived before the seal): f32m := Phi_4^2 - 2^20 Phi_1
  (height 340 = 2*E_4 exactly, gcd(340, 2) != 1). Derivation
  (pre-seal, disclosed): f32m = Phi_3^4 - 512 Phi_2 Phi_3^2 +
  2^16(Phi_2^2 - 16 Phi_1) = Phi_3 * (Phi_3^3 - 512 Phi_2 Phi_3 +
  2^16) since Phi_2^2 - 16 Phi_1 = Phi_3 — the node-height digit
  hits the key relation exactly and the mutant COLLAPSES INTO THE
  DRAIN: Phi_3 | f32m over Z. Machine form: remainder(f32m, Phi_3)
  = 0, hence Res(f32m, Phi_3) = 0 (ladder entry infinite != 170)
  and the single-(e = 32)-factor read is refuted without PARI. The
  gcd != 1 proviso is machine-load-bearing at depth 4.

### S4.3 Run record (VERDICT — appended from the committed
### artifacts after the sealed run)

**GREEN on both routes.** Exact-integer route (P-B4, artifact
`gentow5_output_exact.txt`): v2(Res(f32, g)) = (16, 40, 84, 170,
341) for g = (x, Phi_1, Phi_2, Phi_3, Phi_4) and v2(Res(Phi_4, g)) =
(8, 20, 42, 85) — EXACT at the predicted rungs. PARI route (P-C,
artifact `gentow5_output_full.txt`): factorpadic(f32, 2) = one
degree-32 factor; nfinit([f32,[2]]) + idealprimedec = one prime with
(e, f) = (32, 1); nfeltval ladder [16, 40, 84, 170, 341] EXACT.
Polygon reads (P-B3): 10 polygons one-sided with on-chord support
exactly the char-2 binomial spots, pin tables printed in the
artifacts. T-B1 fired (drain collapse exact + `C4 nfactors=2
degs=[8, 24]`). **f32 = Phi_4^2 - 2^16 Phi_3 is the first depth-4
contact anywhere in the program: a degree-32, e = 32 witness whose
four-rung intermediate ladder is exact on two independent routes.**

## S5. MACHINE LEG (gentow5_checks.py, two-commit seal)

INSTRUMENT: `verification/openmath/gentow5_checks.py`, sealed at
commit 4b279a7 (predictions P-A1..A4, T-A1W/T-A2W/T-A4W, P-B1..B4,
T-B1, P-C1..C4 in the docstring BEFORE the first run; the T-B1 drain
factorization and the A-row residual arithmetic were hand-derived
pre-seal and disclosed in S4.2/S1.2). Run 1: 85/86 — the single flag
was an instrument-wiring defect in T-A1W's survivor comparison (the
predicted survivor (j=2, slotmin 10) WAS in the alive list; the check
read the first list entry — the wrong-height refine also drags the
j = 0, 1 coordinates below their event pins, which is additional
tooth-firing). Repaired + disclosed in the docstring (committed
before re-run); no prediction changed; no reader/kill logic touched.
UNIT NOTE (disclosed): the f32@* and Phi4@Phi3 polygon rows print one
dv-scale above the canonical N_j normalization; one-sidedness and
on-chord support are affine-invariant.

VERDICT RUN (exact leg, artifact `gentow5_output_exact.txt`):

    GREEN — 86 checks, 0 violations, exit 0.
    * P-A1/A2/A3 mu2 = 3 KILLS: all three pins die at all three
      frames (q = 2; q = 3 char-3; K2 = F4 two-flavor lift) — the
      FIRST mu2 = 3 pointwise re-division transports at the composed
      key anywhere in the program (GN-REFINE3 one level up).
    * P-A4 live-twist mu2 = 2 kill: the vartheta_2-corrected member
      dies; T-A4W THE CONVENTION TOOTH FIRED: the naive-digit twin
      keeps its pin at 22 exactly — LEMMA GENTOW5-A1's fixed-unit
      dictionary is machine-load-bearing, not decorative.
    * T-A1W (wrong height) and T-A2W (wrong digit, char 3, surviving
      pin 33 exactly) FIRED as predicted.
    * P-B1/B2: floor chain tight (u = 5, 21, 85, 341), recipe side
      heights (10, 42, 170) = (E2, E3, E4) and top event 341 exact.
    * P-B3: 10 polygons (Phi2/Phi3/Phi4/f32 at every lower key)
      one-sided with on-chord support EXACTLY the char-2 binomial
      spots {0, L} — Cor 6.4's display verified at depth 4, incl.
      the pin tables printed in the artifact.
    * P-B4 THE RESULTANT LADDERS: v2(Res(f32, ·)) =
      (16, 40, 84, 170, 341) and v2(Res(Phi4, ·)) = (8, 20, 42, 85)
      EXACT — the depth-4 witness by the PARI-free integer route.
    * T-B1 FIRED: Phi3 | f32m exactly (remainder 0, resultant 0) —
      the even-height-at-node mutant collapses into the drain.

PARI leg (detached; verdict from the committed artifact
`gentow5_output_full.txt`, md5 839a8660…; runner-as-run md5
5fa684c7…; exact-leg artifact md5 dc499a49…):

**GREEN — full run 92 checks, 0 violations** (86 exact + 6 PARI;
`grep -c VIOLATION` = 0). PARI lines verbatim from the artifact:
`C1 nfactors=1 deg1=32` (P-C1: f32 irreducible over Q_2 at degree
32); `C2 nprimes=1 e=32 f=1` and `C2 ladder=[16, 40, 84, 170, 341]`
(P-C2: the four-rung intermediate ladder EXACT on the independent
nfeltval route — matching P-B4's integer-resultant route rung for
rung); `C3a nfactors=1 deg=4 / e=4 f=1` and `C3b nfactors=1 deg=4 /
e=4 f=1` (P-C3: the refined keys of rows A-1 and A-2/A-4 keep
carrier at q = 2 and q = 3); `C4 nfactors=2 degs=[8, 24]` (P-C4:
the node-height mutant is NOT a single factor — the degree-8 piece
is the drain factor Phi_3 that T-B1's exact division already
exhibited). The run also reproduced the 86 exact checks unchanged.

## S6. HONEST RESIDUE + GRADE BOX

**What this note PROVES (grade 0/2, hostile arc owed):**
* TARGET 1: THEOREM GENTOW5-A + LEMMAS GENTOW5-A0/A1 — LEMMA
  GENTOW-2 layer 1 at GENERAL mu2. GENTOW-BOX-1 is RETIRED as a
  mathematical box: the "composed graded frame" is gr(leaf field)
  (a graded division ring — elementary) + GENHN-2' (accepted) + the
  fixed-unit dictionary; no W-9-analogue weld face. Residue: this
  note's own arc grade; and the mu2 >= 3 machine rows are three
  constructed frames, not a sweep (GENTOW-BOX-2's coverage
  discipline applies to them verbatim).
* TARGET 2: DEF GENTOW5-1 + LEMMAS GENTOW5-C/D + THEOREM GENTOW5-B —
  the level-r ladder grammar and the general-depth composition
  theorem, with the depth-4 witness EXACT on two independent routes.

**Named conditionality stack (per consumer):**
* Accepted 2/2: LEMMA GENHN-T(b)'(i)/(ii)/(iii), GENHN-2/2', the S4
  coherent normalizers, the [r1] node floor (= floor chain rung 1).
* Cited at verified numbering: FGMN [Q1]-[Q10] via GENTOW2_PROOF S3
  (Cor 6.4's level quantifier "for any 1 <= i <= r" carries the
  one-sidedness at every depth; faithfulness audit GENTOW2 S6).
* Grade 0/2 (same campaign, hostile arcs owed): GENTOW-1, GENTOW-2
  layers 2-3, GENTOW2-A/B, THIS NOTE.
* ANNEX GRADE (post-ratification, unpassed): HE7 ANNEX R's
  R1-a/R1-b/R1-c ARGUMENT — consumed at rungs i >= 3 through LEMMA
  GENTOW5-C (reproved tower-side, but the argument's precedent and
  its only hostile-adjacent scrutiny live in the annex). THE GRADE
  CAP FOR DEPTH >= 3 CLAIMS IS THIS PIN plus this note's arc.
* Machine coverage (GENTOW5-BOX-A): CHECK-A exercises mu2 in {2,3},
  q in {2,3}, K2 in {F2, F3, F4}, e2 in {1,2}, f2 in {1,2}, d = 1,
  depth 2; CHECK-B exercises ONE depth-4 chain (all-(2,1) stages,
  q = 2, minimal heights). The proofs are uniform in the stage data;
  the coverage gap is machine-side, named here. The vartheta
  direction (theta vs theta^{-1}) is machine-tested only up to
  self-inverse units (F3; disclosed at T-A4W) — an F5-frame or
  F4-live-twist row would pin it; proof-side the direction is
  S1.2's derivation.

**What stays OPEN (not claimed):** tower COUNT laws at depth >= 3
(no ledger, no measurement); partial inner sides ([GENHN-TOW-1] item
(4)) at every depth; the genre-general faithfulness geography (item
(3)); sigma laws behind [GENHN-HE(mu >= 3)] wherever the top problem
has mu >= 3 — none of these is touched by GENTOW5-B, which is a
carrier/read/budget/refine theorem, not a density display.

**Consumption path (not executed here):** GENTOW1_PROOF's S3 grade
note and S6 GENTOW-BOX-1, GENHN_PROOF's GENHN-BOX-2 and
[GENHN-TOW-1] item (6) depth->=4 sentence, and GENTOW2_PROOF S7's
depth->=4 bullet are candidates for the orchestrator's dated
consumption updates after this note's own hostile arc; the four
source notes are byte-untouched by this unit.
