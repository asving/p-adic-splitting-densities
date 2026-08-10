# GENTOW-1: composed entry budgets, inner refine transfer, composed window ledger
## ([GENHN-TOW-1] items (1), (2), (5) — proof attempt, BOX-CLOSURE campaign wave B1)

**2026-08-09 — COMPLETE at attempt grade 0/2 (hostile arc owed).
Unit: GENTOW-1. Composed in per-section commits; machine leg
sealed-then-verdict (S5).
[ARC — passPE1 2026-08-09: NOT CLEAN, 1 GAP + 2 MINOR
(GENTOW1_passPE1_report.md @ 606e85c); counter stays 0/2.
GT1-r1 repair round 2026-08-09 (this commit): F-1 dated gauge
annex — the corrected chat_t := lift(c_t·eta^{W(t)}) display
pinned at the S0/S2/S3/S6 consumption sites (S7.1, per GENHN
erratum 59c1966 + HETOW [r1]); m-1 P-1 SCORED GREEN 20/0
(gentow1_r1_p1.py, S7.2); m-2 GENTOW-BOX-1 retirement
back-pointer (S6). Sealed machine artifacts BYTE-UNTOUCHED;
statements unchanged (manifest S7.4). Grade stays 0/2; PE2
next.]**

CHARGE (Asvin directive, ledger 2026-08-09: prove the boxes; a box
survives only after genuine attempts fail): PROVE [GENHN-TOW-1] items
(1) composed entry budgets (the GENHN-1 analogue at the composed key
Phi_2, + the depth-3 node floor rider = item (6)(beta)), (2) the inner
refine transfer (GENHN-4 one level up), (5) the composed window ledger
(GENHN-3 at dv_2). Sources consumed (never edited — GENHN_PROOF's
acceptance pass is live): GENHN_PROOF_2026-08-08.md S8 [r2] annex
(LEMMA GENHN-T(b)': composed carrier (i), composed slot lemma
GENHN-2' (ii), corrected leaf read (iii), stage shadow (iv)), S3.2
LEMMA GENHN-1 + its [r2] corrected floor display (the r2-F2 form), S5
LEMMA GENHN-3 + the f1>=3 band annex, S6.1 LEMMA GENHN-4, S9.1
[GENHN-TOW-1]; machine recipes: genhnr2_supp.py (SUPP-A/B/C),
genhn_pe3_fresh.py (FR1 e2=3 genre, FR2 q=3 f2=2 genre).

STATUS TABLE (updated per section as composed):

| item | lemma | status |
|---|---|---|
| (1) budgets + node | LEMMA GENTOW-1 | PROVED (S2) |
| (1) rider: depth-3 floor (6)(beta) | COR GENTOW-1.1 | PROVED (S2.4) |
| (2) inner refine transfer | LEMMA GENTOW-2 | PROVED at mu2=2 pointwise; general mu2 layer-1 via graded frame (disclosed, GENHN-BOX-2 pattern) (S3) |
| (5) composed window ledger | LEMMA GENTOW-5 | PROVED (S4) |
| battery | gentow1_checks.py | GREEN 1,128 checks / 0 violations, 5/5 teeth (S5) |

## S0. SETTING AND NOTATION (all from T(b)', restated for one-pass reading)

Outer genre (Q; e1, f1, mu1; h), key Phi' (deg D' = e1f1), dv = e1*v.
Inner CS event on the level-1 stage read: side of dv-slope kappa2 =
u2/e2 (gcd(u2,e2)=1, u2 > e2*D'h by the [r1] node floor), residual
psi2^{mu2} over K = F_{Q^{f1}}, f2 = deg psi2, FULL side e2f2mu2 =
mu1. Composed key Phi2 = Phi'^{e2f2} - Sum_{t<f2} chat_t
n(u2(f2-t)) Phi'^{e2t}, monic, deg D2 = D'e2f2. [GT1-r1 GAUGE PIN
(dated annex S7.1): chat_t := lift(c_t·eta^{W(t)}) with W(t) =
floor((f2−t)·i(u2)/e1) — the CORRECTED display per GENHN's dated
erratum 59c1966 (at f1 >= 2 per digit: the exact-height (LIFT)
output L_{(f2−t)u2}(c_t·eta^{W(t)})), NOT the gauge-naive plain
lift of c_t; at eta = 1 the two coincide. This pin governs chat_t
at its uses below (S2 Steps 0/1/5, S3).] Composed ladder
dv2 = e1e2*v. Composed basis {x^a Phi'^b : a<D', b<e2f2}; slot
(a,b) at dv2-offset w(a,b) := a*e2h + b*u2; GENHN-2' (accepted
annex): dv2(A(x0)) = min(e1e2*v(c_{a,b}) + w(a,b)) EXACTLY on the
tower-node locus, one K2-digit per dv2-height, K2 = F_{Q^{f1f2}}.

THE ONE NEW CONSTANT: **E2 := e2f2u2** — the dv2-height of every
side term of Phi2 (Phi'^{e2f2}(x0): e2f2*dv2(Phi'(x0)) = e2f2u2;
lift term t: e2*u2(f2-t) + e2t*u2 = e2f2u2). E2 plays the role D'h
played at level 1 (there the key's side height and dv(x^{D'})
coincided at D'h; here they SPLIT: E2 > dv2(x^{D2}) = D2e2h =
e2f2*(e2D'h), by u2 > e2D'h).

WEIGHT: for a monomial pi^v x^a Phi'^b Phi2^j define wt :=
e1e2*v + a*e2h + b*u2 + j*E2. Note wt = dv2 of the evaluated
monomial at any tower-node point where dv2(Phi') = u2 and
dv2(Phi2) = E2 hold exactly; on the actual locus dv2(Phi2(x0)) > E2
(S2.2), so wt is a LOWER bound with the j-graded part strict.

## S1. THE EXAMPLE BATTERY (examples-first; the laws read off tables)

Five constructed tower families (per the standing examples-first
discipline; recipes: genhnr2_supp SUPP-A/B + genhn_pe3 FR1/FR2 +
fresh):

| family | genre | q | Phi2 | u2 | E2 | dv2 | n |
|---|---|---|---|---|---|---|---|
| FAM-A5 | (2,1,4)->(2,1,2) | 2 | (x²−2)²−4x | 5 | 10 | 4v | 8 |
| FAM-A7 | (2,1,4)->(2,1,2) | 2 | (x²−2)²−8x | 7 | 14 | 4v | 8 |
| FAM-B | (2,1,4)->(1,2,2), K2=F4 | 2 | Phi'²−2xPhi'−8 | 3 | 6 | 2v | 8 |
| FAM-C | (2,1,6)->(3,1,2), e2=3 | 2 | (x²−2)³−8x | 7 | 21 | 6v | 12 |
| FAM-D | (2,1,4)->(1,2,2), K2=F9 | 3 | (x²−3)²+27 | 3 | 6 | 2v | 8 |

**THE BUDGET TABLES (machine output, gentow1_checks run of
2026-08-09; * = consumed pin).** v-floors per composed slot
(a,b) at coordinate j:

    FAM-A5 j=0: (0,0):6*  (1,0):5  (0,1):4  (1,1):4
           j=1: (0,0):3   (1,0):3* (0,1):2  (1,1):1
    FAM-A7 j=0: (0,0):8*  (1,0):7  (0,1):6  (1,1):5
           j=1: (0,0):4   (1,0):4* (0,1):2  (1,1):2
    FAM-B  j=0: (0,0):7*  (1,0):6  (0,1):5  (1,1):5*
           j=1: (0,0):4*  (1,0):3  (0,1):2  (1,1):2*
    FAM-C  j=0: (0,0):8*  (1,0):7  (0,1):6 (1,1):6 (0,2):5 (1,2):5
           j=1: (0,0):4   (1,0):4* (0,1):3 (1,1):2 (0,2):2 (1,2):1
    FAM-D  j=0: (0,0):7*  (1,0):6  (0,1):5  (1,1):5*
           j=1: (0,0):4*  (1,0):3  (0,1):2  (1,1):2*

READ OFF THE TABLES (then proved in S2): (i) the floor at slot
(j,a,b) is the SIDE HEIGHT (mu2−j)E2 minus the slot offset w(a,b),
divided by e1e2 and ceiled, +1 at the lattice slots — e.g. FAM-C
(0,(0,1)): ceil((42−7)/6) = 6, no pin (35 ≢ 0 mod 6); (ii) at
f1f2 = 1 exactly ONE pinned slot per coordinate; at f2 = 2 (FAM-B,
FAM-D) exactly TWO pinned slots per pinned height ((0,0) and (1,1)
— the two flavor components of the one consumed K2-digit,
two-step class separation made visible); (iii) node floors
[21,11]/[29,15]/[13,7]/[43,22]/[13,7] = (mu2−j)E2 + 1, realized
exactly by the NODE-EQ anchors (16Phi', 32xPhi', 64x, 64Phi',
729x — all tRAM with PARI sigma the composed-RAM dictionary
value); (iv) the mutant base dv2(x^{D2}) = 8/8/4/18/4 sits BELOW
E2 = 10/14/6/21/6 — the gap the wrong-floor tooth exploits.

**THE REFINE TABLE (old-key read -> refined-key read; all rows
PARI-exact on the refined decided sigma; wrong-normalizer variant
keeps the pin on every row = T-REFWRONG x8):**

    A5-R1 lam=13 s=1     : old (26,14,tEVEN) -> new (31,14,t2SIDED)
    A5-R2 lam=21 s=1     : old (42,22,tEVEN) -> new (47,22,t2SIDED)
      [n2hat(21) = 16Phi' — the r3 witness normalizer, exercised]
    A7-R1 lam=15 s=1     : old (30,19,tEVEN) -> new (35,16,t2SIDED)
    B-R1  lam=7  s=eta2  : old (14, 9,tEVEN) -> new (15, 8,tRAM)
    B-R2  lam=8  s=1+eta2: old (16,10,tEVEN) -> new (19,11,tRAM)
      [two-monomial K2-digit lift 16 + 4xPhi']
    C-R1  lam=22 s=1     : old (44,24,tEVEN) -> new (47,25,tRAM)
    D-R1  lam=9  s=1     : old (18, 9,tDBL ) -> new (19,10,tRAM)
    D-R2  lam=10 s=eta2  : old (20,10,tDBL ) -> new (21,13,tRAM)
      [q=3: BOTH event pins (lam AND 2lam) show and BOTH die]

Read off: the old key sees the alpha-event at exactly (2lam, lam)
heights with the (T−s)²-residues (q=2: the lam-pin vanishes, 2s=0;
q=3: tDBL with both pins — the binomial char-sensitivity);
the refine kills the pins into the lam-floored node; heights
transport on the dv2-ladder; eta2-flavored and two-monomial lifts
behave identically to monomial ones. (Then proved in S3.)

## S2. LEMMA GENTOW-1 (composed entry budgets; item (1))

**Definition (the tower-entry locus 𝒯).** Fix the tower genre data
(Q; e1,f1,mu1; h; Phi'; u2, e2, psi2, mu2), full inner side
e2f2mu2 = mu1, and the composed key Phi2. 𝒯 := the monic f of
degree n = mu2*D2 on the genre-G opening locus whose level-1 stage
read exhibits the full inner side: the (J, dv(A_J))-polygon is ONE
side of slope kappa2 = u2/e2 from (0, mu1*kappa2) to (mu1, 0) with
twist-coherent residual psi2^{mu2} (S4 normalizers).

**LEMMA GENTOW-1.**
(a) [WEIGHT CHARACTERIZATION] monic f of degree n lies on 𝒯 iff
every composed slot of g := f − Phi2^{mu2} has weight >= mu2*E2+1;
equivalently, in f = Phi2^{mu2} + Sum_{j<mu2} C_j Phi2^j,
C_j = Sum c_{j,a,b} x^a Phi'^b (a < D', b < e2f2):

    v(c_{j,a,b}) >= ceil( ((mu2−j)E2 − w(a,b)) / (e1e2) ) + [pin],
    [pin] = 1  iff  e1e2 | (mu2−j)E2 − w(a,b) >= 0,

the composed side height at the slot, ceiled to the digit grid,
plus one consumed digit at each lattice slot — the r2-F2 level-1
display verbatim with (D'h, ih, e1) ↦ (E2, w(a,b), e1e2).
(b) [FIBRATION] f ↦ (c_{j,a,b}) is a triangular-unimodular digit
bijection from 𝒯 onto the budget box (digits free above floors);
one K2-digit per dv2-height per coordinate (GENHN-2'); per window
N the free-O-digit count is Sum_{j,a,b} (N − floor(j,a,b)).
(c) [NODE] on 𝒯: p_j := dv2(C_j(x0)) >= (mu2−j)E2 + 1 for j < mu2
at every root x0, equality realizable at every j (two-step class
separation supplies a slot in every residue class mod e1e2).
(d) [NODE AT THE FIELD] every root x0 of every f in 𝒯 has
dv2(Phi2(x0)) > E2 — the psi-cancellation (HE6-0) argument one
level up. (dv2(Phi2(x0)) need not be an integer on 𝒯 — RAM leaves
have e(L) = 2e1e2; the strict inequality is the statement.)

*Proof.*

**Step 0 (carry monotonicity — the weight bookkeeping hinge).**
Extend wt to all monomials pi^v x^{a'} Phi'^{J} by wt := e1e2*v +
a'e2h + J*u2; on the composed grid (J = b + j*e2f2) this equals
e1e2*v + w(a,b) + j*E2 (b*u2 + j*e2f2*u2 = b*u2 + j*E2). The two
reduction moves are weight-monotone:
* x-carry (a' >= D'): x^{D'} = Phi' + (Phi'-tail); tail monomials
  x^c pi^g have g >= (D'−c)h/e1 (the key's one side), so
  e1e2*g + c*e2h >= D'e2h = wt(x^{D'}) — tail weight preserved or
  raised; the Phi'-part has weight u2 > e2D'h ([r1] node floor) —
  strictly raised.
* Phi'-carry (b' >= e2f2): Phi'^{e2f2} = Phi2 + Sum_t chat_t
  n(u2(f2−t)) Phi'^{e2t}; each lift term has weight
  e2*u2(f2−t) + e2t*u2 = E2 = wt(Phi'^{e2f2}) (n(m) = x^i pi^a with
  e1*a + ih = m has weight e2*m) — preserved; the Phi2-part at
  weight E2 exactly. [GT1-r1: chat_t = the corrected lifts (S0 pin,
  S7.1); this display is VALUE-BLIND — it prices heights only, and
  lift(c_t·eta^{W(t)}) and lift(c_t) sit at the same height, so
  Step 0 is unchanged under the gauge correction.]
Hence: expansions of one polynomial on the level-1 grid and on the
composed grid are related by weight-nondecreasing rewriting in
both directions (Phi2 = Phi'^{e2f2} − (weight-E2 lift terms) for
the converse), and by the ultrametric each final slot's valuation
clears the minimum initial weight: **"all slots of P at weight
>= W" is the same condition on both grids.** Per-slot arithmetic:
wt >= mu2*E2 + 1 for the slot (j,a,b) is EXACTLY v >= the displayed
floor (off-lattice the ceil strictly exceeds the side; on-lattice
the pin supplies the +1).

**Step 1 (Phi2^{mu2}'s own level-1 data — from T(b)'(i), consumed).**
Phi2's level-1 development is one-sided of slope kappa2 with
residual psi2: slots at weight >= E2, the weight-E2 graded layer =
psi2's coefficients at the side lattice (the T(b)' display; at
f1 >= 2 the literal development differs from the display only
strictly above the side — the [r2] parenthetical). [GT1-r1: read AT
THE CORRECTED KEY (S0 pin, S7.1) — the erratum's scope clause:
T(b)'(i)'s carrier/slot/residual mechanism holds at the corrected
key; at the gauge-naive key the weight-E2 layer is c_t·eta^{−W(t)},
NOT psi2's coefficients, and this step fails at eta != 1.] Multiplicativity
of side residuals (graded layer of a product = product of graded
layers, as in (i)'s proof): Phi2^{mu2} has slots at weight
>= mu2*E2 with weight-mu2*E2 layer psi2^{mu2}, and every
off-lattice slot strictly above.

**Step 2 (⟸ realizability).** Digits >= floors give every slot of
g weight >= mu2*E2 + 1 (Step 0 arithmetic); by Step 0 all level-1
slots of g sit strictly above the inner side (level-1 weight =
e2*(dv-height) + J*u2, so wt >= mu2*E2 + 1 iff dv-height >
kappa2*(mu1 − J)). Adding Phi2^{mu2} (Step 1): f's level-1 pins are
the full inner side with residual psi2^{mu2} exactly. Outer
grammar: a weight-wt grid monomial has x-height wt − B(u2 − e2D'h),
B := b + j*e2f2 <= mu1 − 1, so x-height >= mu2*E2 + 1 −
(mu1−1)(u2 − e2D'h) = u2 + (mu1−1)e2D'h + 1 > mu1*e2D'h = n*e2h:
strictly above the outer side, whose side + residual psi^{mu1}
Phi2^{mu2} supplies ((i)'s x-polygon raised to mu2). So f ∈ 𝒯.

**Step 3 (⟹ necessity + fibration).** f ∈ 𝒯: its level-1 side
digits at the lattice equal psi2^{mu2}'s coefficients — the same
K-digit data Phi2^{mu2} carries (Step 1, same coherent-normalizer
convention as the residual's definition). In g = f − Phi2^{mu2}
the lattice digits cancel to one digit higher (residue equality
lifts to O-digit agreement mod one more pi-power per component:
weight >= mu2*E2 + e1e2 there), off-lattice slots of both sit at
weight >= mu2*E2 + 1 (strictly-above f-pins; Step 1 for the key
power). Step 0 converts to the composed floors. Triangularity: the
coordinate map is a composition of monic divisions (by Phi2, then
Phi'), unipotent in the x-degree filtration: c_{j,a,b} = the
coefficient of f at degree jD2 + bD' + a plus an Ô-combination of
strictly higher-degree coefficients — a digit bijection; Steps 2+3
identify image and budget box. Free-count display immediate. ∎(a,b)

**Step 4 (node (c)).** All roots x0 of f ∈ 𝒯 are tower-node points:
the full inner side forces v(Phi'(x0)) = u2/(e1e2) exactly with
eta2(x0) a psi2-root (the level-1 Newton polygon of the inner read
has the one side of slope kappa2, residual psi2^{mu2} zero-free at
the corners — T(b)'(iii)'s (T1')/(T2') transport, consumed). So
GENHN-2' reads p_j exactly as the slot-min; by (a)'s floors each
slot has e1e2*v + w >= (mu2−j)E2 + 1. Equality: pick the residue
class: solve b*u2 ≡ target (mod e2) (gcd(u2,e2) = 1), then
a*h ≡ (target − b*u2)/e2 (mod e1) (gcd(h,e1) = 1) — a slot with
w(a,b) ≡ (mu2−j)E2 + 1 (mod e1e2) inside a < e1 <= D',
b < e2 <= e2f2; set its digit at the floor, rest empty: on 𝒯 by
(b), pin at exactly (mu2−j)E2 + 1. ∎(c)

**Step 5 (field floor (d)).** Phi2(x0) = Phi'(x0)^{e2f2} − Sum_t
chat_t(x0) n(u2(f2−t))(x0) Phi'(x0)^{e2t}: every term at dv2 = E2
exactly ((T1),(T12)); the height-E2 residue under the coherent
height-E2 normalizer is (unit)·psi2(eta2(x0)) — the S4 cocycle
enters every term identically, exactly (i)'s side-residual
computation — and psi2(eta2(x0)) = 0 (T22). Ultrametric:
dv2(Phi2(x0)) > E2. ∎ [GT1-r1: "the residue is
(unit)·psi2(eta2(x0))" holds at the CORRECTED chat_t (S0 pin,
S7.1); at the gauge-naive lifts the term-t residue carries the
extra factor eta^{−W(t)}-bar and the sum is NOT psi2(eta2(x0)) —
(d) then FAILS at eta != 1: machine-confirmed, nfeltval(Phi2^N) =
3·pr.e EXACTLY at 20/20 scored prime rows of the fresh frame F1
(S7.1).]

**COROLLARY GENTOW-1.1 (the depth->=3 node floor — [GENHN-TOW-1]
item (6)(beta)'s missing provenance).** Every side of the composed
polygon (j, p_j) of an f ∈ 𝒯 has dv2-slope

    kappa3 > E2 = e2f2u2 > dv2(x^{D2}) = D2*e2h.

*Proof.* Pins p_j >= (mu2−j)E2 + 1 (GENTOW-1(c)) with right
endpoint (mu2, 0): the rightmost (minimal) side slope is
>= min_j p_j/(mu2−j) >= E2 + 1/mu2 > E2; convexity gives every
side slope > E2; and E2 = e2f2*u2 > e2f2*(e2D'h) = D2*e2h by the
[r1] node floor u2 > e2D'h. ∎ This is the exact level-2 analogue
of the [r1] floor (level 1: kappa2 > D'h = dv(x^{D'}), where the
key's side height and dv(x^{D'}) coincide; at level 2 they split
and the SHARPER constant E2 is the true floor — the witness:
kappa3 = 21/2 > E2 = 10 > dv2(x^{D2}) = 8). Item (6)(beta) is
hereby discharged INTO item (1); item (6)(alpha) (the iterated
carry-cancellation bookkeeping) is untouched and keeps the box.

**Remark (count-law unlock, honest scope).** With (b), tower count
laws take the W-12.A cell-law form on the composed keying with
entry exponent Sum(N − floor) — the battery's budget tables are
the first measured contact (S5); the per-genre tower count LEDGERS
(the GENH5-DENS-style displays) are a counting unit NOT executed
here.

## S3. LEMMA GENTOW-2 (inner refine transfer; item (2))

**Setting (the composed-alpha event = the transported inner refine).**
f ∈ 𝒯 whose composed polygon (j, p_j) is one side of integer
dv2-slope lam > E2 with residual (T − s)^{mu2} over K2, s ∈ K2^×
(the composed frame's stage-alpha event; by GENTOW-1(c) any
composed side has slope > E2, so lam >= E2 + 1 automatically — the
composed floor plays S6.1's "kappa > S′"). LADDER NORMALIZERS
(the r3 mechanism's n̂₂, now with provenance): n2hat(m) :=
pi^{a0} x^i Phi'^b, i < e1, b < e2, e1e2*a0 + i*e2h + b*u2 = m —
the (i,b)-pair is unique per residue class mod e1e2 (two-step
separation) and a0 >= 0 whenever m > E2 (since u2 > e2D'h forces
E2 >= (e1−1)e2h + (e2−1)u2 + 1). K2-DIGIT LIFT: for s =
Sum_{t<f2} s_t eta2^t (s_t ∈ K), lift(s; m) := Sum over the f1f2
within-class monomials x^{i+e1r} Phi'^{b+e2t} at height m with
O-digit coefficients realizing the components in the coherent
normalization (the same S4-cocycle convention as the entry lifts
chat_t [GT1-r1: = the CORRECTED convention — the S0 pin's
eta^{W}-corrected lifts, S7.1]); deg lift < D2 always
(x-exponents < e1f1 = D', Phi'-exponents < e2f2).

**LEMMA GENTOW-2 (refine transfer at the composed key).** Set
Phi2+ := Phi2 + what, what := −lift(s; lam). Then:
(i) [INVARIANTS] Phi2+ keeps every T(b)' key invariant: monic of
degree D2; level-1 development one-sided of slope kappa2 with
residual psi2 and side digits byte-unchanged (what's slots sit at
weight lam > E2, strictly above the key's side); x-polygon one
side of slope h/e1 (what's x-heights >= lam − (e2f2−1)(u2−e2D'h)
> dv2(x^{D2})); hence the (i)-forcing chain reruns verbatim:
Phi2+ irreducible with carrier (e1e2, f1f2), and GENTOW-1 +
GENHN-2' hold verbatim at Phi2+.
(ii) [THE KILLS] in the Phi2+-development of f the mu2 event pins
die: p_j+ > (mu2−j)*lam for every j < mu2.
(iii) [TRIANGULARITY + BIJECTION] (digits at Phi2) ↦ (digits at
Phi2+) is triangular (new digit = old digit + strictly-lower-height
data), bijecting the event slice onto the lam-floored node box;
|K2| − 1 letter choices of s per step.
(iv) [TRANSPORTED EVENT DATA — the inner refine read back] for a
deeper member g in the Phi2+-frame (pins above the lam-node), the
OLD-key read of g exhibits exactly the alpha-event: pin
p_j(old) = (mu2−j)*lam with residue binom(mu2, j)(−s̄)^{mu2−j}
(coherent normalization, wrap units included) at every j with
p ∤ binom(mu2, j), the other coordinates strictly above — at
mu2 = 2, q = 2 the j = 1 pin vanishes (2s = 0) and the event is
carried by p_0 = 2*lam alone; at q = 3 both pins show. Heights
transport by dv2 = e2*dv and residues by the eta2-dictionary —
the inner-stage (LIFT)-move data is exactly recoverable from the
composed frame.

*Proof.*
(i) what's slots sit at dv2-height lam > E2 while the key's
level-1 side and residual live at weight E2: strictly-above
additions change neither (GENTOW-1 Step 0/Step 1 grammar). The
x-side: a weight-lam grid monomial with Phi'-exponent b has
x-height lam − b(u2 − e2D'h) >= lam − (e2f2−1)(u2−e2D'h) >
E2 − (e2f2−1)(u2 − e2D'h) = u2 + (e2f2−1)e2D'h > e2f2*e2D'h =
dv2(x^{D2}): strictly above the x-side through (D2, 0), constant
term untouched. With the side data identical, (i)'s forcing chain
gives the same carrier; GENHN-2'/GENTOW-1 depend only on these
invariants. ∎(i)
(ii)+(iii) — three layers, GENHN-4 one level up:
* LAYER 1 (graded kills). GENHN-2' makes the composed slot model
  pointwise faithful (one K2-digit per dv2-height, slot-min =
  valuation), so the graded computation happens in gr(O_{L2}) —
  one K2-line per height, with wrap units x0^{e1} =
  (eta-unit)·pi^h, Phi'(x0)^{e2} = (eta2-unit)·n(u2)(x0) and the
  normalizer cocycle n2hat(m)·n2hat(m') = (wrap unit in
  K2^×)·n2hat(m+m'): the units enter the residual assembly and
  the carry products IDENTICALLY (the S4 computation with the
  second wrap adjoined), so the development transforms by the
  substitution T ↦ T + s̄ on the residual polynomial:
  (T − s)^{mu2} ↦ T^{mu2} — all mu2 pins die. The identity is a
  substitution identity, binomial-free, both characteristics
  (GENHN-4 layer 1 verbatim). GRADE NOTE (honesty): at mu2 = 2
  this is verified pointwise-elementarily by the battery's refine
  rows (actual polynomial re-division, no formula — the
  GN-REFINE3 pattern; 8 rows across all five families, q ∈ {2,3},
  monomial and Phi'-flavored and two-monomial K2-digit
  normalizers); at general mu2 layer 1 consumes the composed
  graded frame exactly as GENHN-4 layer 1 consumed W-9's —
  GENHN-BOX-2's disclosure pattern one level up, named in S6.
* LAYER 2 (corrections land strictly deeper, in-window). The
  non-graded corrections are (a) the products what^{i−j}·C_i
  beyond their exact-height parts: dv2 >= (i−j)lam + (mu2−i)lam
  + 1 = (mu2−j)lam + 1 (each factor exceeds its side height only
  in correction terms; exact-height products ARE layer 1); (b)
  the x- and Phi'-degree overflows of what·C_i reduced mod Phi2+:
  by carry monotonicity (GENTOW-1 Step 0 — the x-carry priced by
  Phi''s side, the Phi'-carry priced by Phi2's side, the
  Phi2+-recarry weight-graded) every overflow lands at weight >=
  its raw weight: in-window positions, moving upward only
  (LEMMA GENTOW-5(c)(d)). THE LEVEL-2 NOVELTY sits exactly here:
  at level 1 one carry (x) priced by one side (Phi''s); here two
  carries priced by the two sides — both displays are Step 0.
* LAYER 3 (bijectivity). Triangular by layers 1–2; image inside
  the lam-floored node {p_j+ > (mu2−j)lam} by (ii); onto by
  cardinality: slot strings are key-independent (GENHN-2' at
  Phi2+ via (i)), the mu2 pinned digits are the event data and
  the remaining slots biject. ∎(ii),(iii)
(iv) Write the Phi2-development of g by substituting Phi2+ =
Phi2 + what into g = Sum C_i+ (Phi2+)^i: coordinate j receives
Sum_{i >= j} binom(i, j) what^{i−j} C_i+ plus weight-raised
carries; the minimal-height term is binom(mu2, j) what^{mu2−j}
from C_{mu2}+ = 1, at dv2 = (mu2−j)lam with residue
binom(mu2,j)(−s̄)^{mu2−j}·(wraps); every C_i+ (i < mu2)
contribution sits at dv2 > (mu2−i)lam + (i−j)lam = (mu2−j)lam
(pins above the lam-node). At p | binom(mu2, j) the pin datum
vanishes and the coordinate sits strictly above — the
characteristic-sensitive display of the level-1 refine, now at
the composed key. ∎

## S4. LEMMA GENTOW-5 (composed window ledger; item (5))

**LEMMA GENTOW-5 (caps, raggedness, consultation, content — GENHN-3
at dv2).** Window N (ambient coefficients known mod pi^N). On 𝒯,
per coordinate C_j:
(a) [CAP + FIRST-BAND] a computed dv2-value is LIFT-STABLE iff
< e1e2*N: an out-of-window O-digit at v = N in the (0,0)-class
gives dv2 = e1e2*N, undercutting every computed value >= e1e2*N
and tying none below it; all in-window slot digits agree across
lifts (by (e)'s triangularity mod pi^N). At f1f2 >= 2, at the
FIRST band height m = e1e2*N exactly: every unread digit lives at
height >= e1e2*N and joins the height-m residue only on
complementary K2-flavors, so by GENHN-2''s independence a nonzero
readable part cannot be cancelled: the VALUE is exact for every
lift while the full K2-residue is not determined — the level-1
f1 >= 3 band annex's clause (1) transported verbatim with
(f1, eta) ↦ (f1f2, (eta, eta2)). Deeper band heights are
value-unstable (the undercut); no trichotomy is claimed there
(conservative drain), exactly as the annex's (3).
(b) [RAGGED STRINGS] the class-(a,b) slot string of C_j ends at
e1e2*(N−1) + w(a,b): ragged across the e1e2 height-classes (each
residue mod e1e2 realized exactly once in the (i < e1, b < e2)
range — two-step separation); WITHIN one dv2-height the K2-digit's
f1f2 component O-digits die at different lift-depths (the
within-digit band — new at level 2 for e2 >= 2, where it mixes the
eta- and eta2-flavors).
(c) [CONSULTATION] every digit consulted by a readable event sits
strictly inside its class string: a consulted height m satisfies
m < e1e2*N and m ≡ w(a,b) (mod e1e2), hence m <= e1e2*(N−1) +
w(a,b) — one congruence, GENHN-3(c) verbatim on the dv2-ladder.
(d) [UPWARD CARRIES] along composed chains (GENTOW-2 refines),
every update determines new digits at height d from old digits at
heights <= d (GENTOW-2 layer 2 = Step-0 carry monotonicity): deep
composed histories never consult the ragged band; per-node laws
uniform below the caps.
(e) [CAPPED-WINDOW CONTENT IDENTITY] the composed digit map is
triangular-unimodular over Ô (GENTOW-1(b)), so it induces a
BIJECTION (f mod pi^N, monic deg n) ↔ (composed digits c_{j,a,b}
mod pi^N): the certified windows at Phi2 — every decided composed
read at heights < e1e2*N is a function of the window data, the
budget/count display of GENTOW-1(b) is exact per window, and
counts computed in composed digits equal counts computed on
ambient coefficients (the GENIND capped-window content identity at
the composed frame).

*Proof.* (a) Undercut instance: the class-(0,0) digit at v = N has
height e1e2*N and every unread digit has v >= N, hence height
>= e1e2*N + w >= e1e2*N: values below the cap can neither move nor
tie; in-window stability is (e) mod pi^N. First-band: the unread
components at height exactly e1e2*N occupy the complementary
flavors {eta^r eta2^t : (r,t) out-of-window at m}; GENHN-2''s
tower-basis independence (the K-components along {eta2^t} each
force res = 0) says a nonzero readable combination survives any
assignment of the unread flavors. (b) v <= N−1 ⟺ height <=
e1e2*(N−1) + w(a,b); class surjectivity is GENTOW-1 Step 4's CRT
display. (c) the congruence line. (d) GENTOW-2 layer 2. (e)
c_{j,a,b} = (f's coefficient at x-degree jD2 + bD' + a) + an
Ô-combination of strictly higher-degree coefficients (GENTOW-1
Step 3): unipotent over Ô, hence bijective mod pi^N. ∎

**Scope remark (honest).** (i) The BAND ADJUDICATION (which band
reads exit UND vs decide — the GENH4-CAP(F)/r3 trichotomy one
level up) is claimed here ONLY in the transported first-band form
(a); a composed band trichotomy display with census would be the
analogue of the [r2] f1 >= 3 annex's (2) and is NOT derived — it
was not part of item (5)'s box text (which asks for GENHN-3 +
BOX-4 at dv2). (ii) BOX-4's extraction seams concern EMBEDDED
genres; the tower's first-live shape is full-side (the tower block
IS f), so the extraction-certification layer is vacuous here;
partial inner sides — where extraction seams would return — are
[GENHN-TOW-1] item (4), untouched.

## S5. MACHINE LEG (sealed battery, two-commit discipline)

INSTRUMENT: `verification/openmath/gentow1_checks.py`, sealed at
commit 982abe7 (predictions P-1..P-9 + 5 teeth in the docstring,
BEFORE the first full run; wiring smoke disclosed there — two
pre-seal constant slips named). RUN 1 crashed on instrument
defects, repaired and REDISCLOSED in the docstring (commit before
re-run): the sealed P-7 check compared reads INCLUDING above-cap
values (over-claiming GENTOW-5(a), whose content is stability
below e1e2·N only — the 25 run-1 flags were all above-cap p1
appearances under lifts, below-cap data and sigma identical);
plus a +oo nfeltval parser guard and a DRAIN-member PARI skip
(members with Phi2 | f carry no scored mu2 = 2 read). No
prediction changed. Runner md5 at the verdict run:
6df4b213ed0aab6afa37ac7b418540aa.

VERDICT RUN (this repo, 2026-08-09, output
`gentow1_checks_output.txt` md5 25667bf6, ~5s + PARI):

    GREEN — 1,128 checks, 0 violations, 5/5 teeth.
    Tally: NEC 350, REAL 180, ROUNDTRIP 150, NODE-EQ 5, MUTANT 5,
    WINDOW 35, STRINGS 22, BELOWNODE 1, SHADOW 3, UNDERCUT 2,
    REFINE 40, GP-SIG 94, GP-DISC 57, GP-NODE 171, GP-EF 8,
    TEETH 5.

What the scored rows of this run verified (per prediction):
* P-2/P-4 (both budget directions): 10 level-1-recipe members +
  ~4 deep perturbations per family satisfy the composed floors +
  node pins + strict-above (NEC 350); 12 random in-budget members
  per family pass the level-1 entry gate + strict-above, with
  decided reads PARI-exact (REAL 180, GP-SIG rows).
* P-3 (node oracle): 171 GP-NODE row-checks — per irreducible
  factor per prime of the scored members, e1e2·nfeltval(Phi2)
  > E2·pr.e (STRICT, the field floor GENTOW-1(d)), with
  e1·val(x) = h·pr.e and e1e2·val(Phi') = u2·pr.e exact (the
  (T1)/(T12) transport at leaves).
* P-5: the five NODE-EQ anchors hit p0 = mu2·E2 + 1 exactly, tRAM,
  PARI both routes (the node floor is SHARP).
* P-6: the 8 refine rows of S1's table (REFINE 40 + GP-EF 8: the
  refined keys keep carrier (e1e2, f1f2) by PARI).
* P-7/P-8/P-9: window stability below the cap on 6 lifts/family +
  mod-p^N reads (WINDOW 35), string ends (STRINGS 22), digit
  round-trips (ROUNDTRIP 150).
* TEETH: T-MUTFLOOR x5 (per family, 8/8 members clearing the
  dv2(x^{D2})-based mutant floors but below the true E2-floors are
  REJECTED by the level-1 truth — the wrong-floor mutant is
  machine-dead); T-BELOWNODE (a digit AT weight mu2·E2 breaks the
  entry endpoint: dv(A0) = 12 ≠ 10); T-REFWRONG x8 (wrong-height,
  wrong-residue at q=3, and wrong-flavor normalizers all leave the
  event pin alive); T-UNDERCUT x2 (a v = N' digit with
  e1e2·N' <= m* changes the read); T-SHADOW (the three PE1
  corrected-read regressions: pins (25,14)/(21,14)/(21,14), sigma
  {(8,1)} PARI-exact).
Unscored diagnostics: 8 (sigma of undecided/off-locus probes,
printed in the output).

## S6. HONEST RESIDUE + GRADE BOX

**What stays in [GENHN-TOW-1] (untouched here):** item (3) the
genre-general faithfulness geography; item (4) partial inner sides
(e2f2mu2 < mu1 — 𝒯's definition here is FULL-side; every S2–S4
statement is scoped to it); item (6)(alpha) the iterated
carry-cancellation bookkeeping at depth >= 3 (the Okutsu-optimality
content — COR GENTOW-1.1 discharges only the (beta) leg, the
depth-3 node floor, and does so with the sharper constant E2).

**GENTOW-BOX-1 (the mu2 >= 3 graded-frame consumption —
GENHN-BOX-2 one level up).** LEMMA GENTOW-2 layer 1 at mu2 >= 3
consumes the composed graded frame (one K2-line per dv2-height,
the two-wrap cocycle) rather than re-deriving the carry
digit-by-digit; at mu2 = 2 (every first-live tower shape, n <= 15)
the battery's refine rows are pointwise re-division checks with no
formula consulted. An elementary general-mu2 carry display would
retire this box exactly as GENH4-S5's would retire GENHN-BOX-2.
Note mu2 >= 3 towers first live at n = e1f1·e2f2·mu2 >= 2·2·3 = 12
with sigma behind [GENHN-HE(mu2)] regardless. [GT1-r1 back-pointer
(PE1 m-2): GENTOW5 S1.5 (grade 0/2, hostile arc owed) RETIRES this
box as a mathematical box with the residue grade-only — read the
retirement THERE with its stated 0/2 conditionality — and since
GENTOW-2 layer 3's image clause consumes layer 1, at mu2 >= 3 the
BIJECTION inherits the graded-frame conditionality too.]

**GENTOW-BOX-2 (machine coverage).** Rows exercise: mu2 = 2 only;
f1 = 1 outer keys only (D' = 2); q ∈ {2, 3}; e2 ∈ {1, 2, 3},
f2 ∈ {1, 2}; d = 1 ambients; depth 2 only. The S2–S4 proofs are
uniform in (e1, f1, e2, f2, mu2, q, h) — the coverage gap is
machine-side, named here (the f1 >= 2 outer and mu2 >= 3 rows are
constructible follow-ups; iterated depth >= 3 rows exist in
genhnr2_supp SUPP-C and stay with item (6)).

**GRADE: 0/2 (attempt; composed this session, no hostile arc).**
Conditionality stack: consumes LEMMA GENHN-T(b)' (i)/(ii)/(iii)
(GENHN accepted 2/2 at PE4) [GT1-r1: AT THE CORRECTED KEY — the
GENHN dated gauge erratum 59c1966 (chat_t := lift(c_t·eta^{W(t)}),
from HETOW PE1 F-1) is a pinned consumption of this note, dated
annex S7.1], the [r1] node floor u2 > e2D'h (GENHN-1 erratum,
inside the accepted text), S4's coherent normalizers, and — at
mu2 >= 3 only — the graded frame (GENTOW-BOX-1). Machine leg = S5
(this unit's sealed battery) [GT1-r1: + the P-1 supplement and the
PE1 fresh route, S7.2].

**Consumption path (not executed here):** discharge of items
(1)/(2)/(5) into GENHN_PROOF's [GENHN-TOW-1] box text is the
orchestrator's dated consumption update after this note's own
hostile arc; GENHN_PROOF is byte-untouched by this unit.

## S7. [GT1-r1] PE1 REPAIR RECORD + THE DATED GAUGE ANNEX
## (2026-08-09, post-passPE1)

PE1 verdict (GENTOW1_passPE1_report.md @ 606e85c): NOT CLEAN —
1 GAP (F-1) + 2 MINOR (m-1, m-2); counter stays 0/2. This section
is the r1 repair round. Tag convention: this round's edits are
marked [GT1-r1] (bare [r1] in the body refers, as before, to
GENHN-1's node-floor erratum). Sealed machine artifacts
(gentow1_checks.py, gentow1_checks_output.txt, gentow1_pe1_fresh.py,
gentow1_pe1_fresh_output.txt) are BYTE-UNTOUCHED by this round.

### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t
### display, pinned

**The seam.** This note's verdict commit (5eca905, 08-09 15:16)
predates the GENHN dated erratum (59c1966, 08-09 20:13, provoked by
HETOW PE1 F-1), which established that LEMMA GENHN-T(b)''s original
DISPLAY of the composed key's lift coefficients — chat_t = a plain
lift of psi2's coefficient c_t — is GAUGE-NAIVE: the normalizer
monomials are not multiplicative (nhat(u2)^{f2−t} =
nhat((f2−t)u2)·(x^{e1}/pi^h)^{W(t)}), so the plain lift's
coherent-normalizer slot residue is c_t·eta^{−W(t)}, not c_t. The
note as composed consumed the pre-erratum display and carried no
gauge annex — PE1's F-1.

**THE PINNED CORRECTED DISPLAY (per erratum 59c1966 + HETOW [r1]):**

    chat_t := lift(c_t·eta^{W(t)}),
    W(t)   := floor((f2−t)·i(u2)/e1)

(i(u2) = the x-exponent of nhat(u2); at f1 >= 2 per digit: the
exact-height (LIFT) output L_{(f2−t)u2}(c_t·eta^{W(t)}), the
HETOW [r1] F-4 no-overflow form). At eta = 1 — and at any frame
where each c_t·(eta^{W(t)} − 1) = 0 — corrected = naive. Site pins
placed this round (grep "chat" + the T(b)'-display consumptions):
the S0 key display (the governing pin), S2 Step 0 (Phi'-carry;
value-blind, unchanged), S2 Step 1 (graded layer read at the
corrected key), S2 Step 5 (the value-LIVE site: the residue
computation), S3's K2-digit lift convention, and the S6
conditionality stack. LEMMA GENTOW-1 Steps 1/3/5 and LEMMA
GENTOW-2's frame consume "graded layer of Phi2 = psi2 under the
coherent normalizers" — true at the CORRECTED key (the erratum's
scope clause: T(b)''s carrier/slot/sigma mechanism holds there).

**Wrap-immunity of this note's own content (two independent legs,
both already on record at PE1).** The BUDGETS/WINDOWS/FLOORS are
valuation-level: (leg 1) the PE1 verifier re-derived Step 0
independently and recorded it VALUE-BLIND — "heights only ...
wrap-immune, unaffected by F-1" (report, clean charge 1; the S0/S2
displays price heights, and the corrected and naive lifts sit at
the same height); (leg 2) the PE1 fresh route
(gentow1_pe1_fresh.py @ 6993b7c, sealed 9e9d994) — GREEN 373
checks / 0 violations over its two frames — ran the program's
FIRST eta != 1 budget frame, F1: p = 3, Phi' = x^2−6, eta = 2,
(e2,f2) = (1,2), K2 = F9, AT THE CORRECTED KEY:
floors, entry gate, strict-above, node pins, field floor, refine
transport ((14,7) -> (19,11), q = 3 both pins), sigma {(4,2)} both
oracles. What is gauge-LIVE is the FRAME (key normalization,
residual, sigma): at the gauge-naive key the fresh route's teeth
fired — ef(Phi2^N) = {(4,1)} != {(2,2)} (degenerate twisted
residual (T−1)^2), field floor (d) FAILS exactly (nfeltval = 3·pr.e
at 20/20 scored prime rows, no psi-cancellation), naive-box members
sigma {(8,1)} != {(4,2)}.

**eta = 1 battery blindness (disclosed).** The five committed
S1/S5 families sit at eta = 1 (q = 2 with Phi' = x^2−2; q = 3 with
Phi' = x^2−3), where the naive and corrected displays coincide —
the sealed battery is structurally blind to this seam (add this to
GENTOW-BOX-2's coverage reading). The eta != 1 machine coverage is
the fresh route's F1 frame plus the erratum's own frame X +
hetowr1_supp.py's three frames.

### S7.2 (m-1 repair): the sealed P-1 prediction, SCORED

P-1 was sealed in the runner docstring (982abe7) but no runner row
scored the BASE keys' ef (GP-EF's 8 rows are the refined keys; S5's
per-prediction list starts at P-2 — the honest no-row state at
PE1). Scored this round by supplement `gentow1_r1_p1.py` (output
`gentow1_r1_p1_output.txt`; base keys transcribed from S1's table,
decorrelated from the sealed constructors): GREEN, 20 checks /
0 violations — the five base keys factorpadic-irreducible (one row,
multiplicity 1, degree D2), ONE prime with (e,f) = (e1e2, f1f2) =
(4,1)/(4,1)/(2,2)/(6,1)/(2,2), and the P-1 valuation normalizations
exact (e1·v(x) = h·pr.e; e1e2·v(Phi') = u2·pr.e). Disclosure: the
scoring is post-hoc to the seal (prediction sealed 08-09, scored at
r1); the fresh route had already scored the base-key ef directly at
the eta != 1 frame (ef(Phi2^C) = {(2,2)}, F1).

### S7.3 (m-2 repair): executed as the one-sentence [GT1-r1]
### back-pointer in S6's GENTOW-BOX-1 paragraph.

### S7.4 EDIT MANIFEST (for PE2's diff)

Body state before this round: md5
dc99fc250094a4db96c66c8aa93c3187 = the PE1 target (verdict commit
5eca905). [GT1-r1] edit sites: (1) header ARC line; (2) S0 gauge
pin at the key display; (3) S2 Step 0 Phi'-carry pin; (4) S2
Step 1 corrected-key pin; (5) S2 Step 5 value-live pin; (6) S3
lift-convention pin; (7) S6 GENTOW-BOX-1 back-pointer sentence;
(8) S6 conditionality-stack erratum pin + machine-leg pointer;
(9) this S7. Edit shape: [GT1-r1]-bracketed INSERTIONS plus this
S7 — checkable as `git diff 5eca905..HEAD` on this file; the
statement displays of LEMMA GENTOW-1, LEMMA GENTOW-2, LEMMA
GENTOW-5, and COR GENTOW-1.1 sit outside the inserted brackets
(the pins fix the consumed chat_t reading; the floors, bounds, and
clause texts are the composed ones). Grade stays 0/2; PE2 next.

### Dated correction (2026-08-10, post-PE2)

PE2 came back CLEAN (0C/0G/1m; report `GENTOW1_passPE2_report.md`
@ 1e99926); the acceptance counter moved 0/2 -> 1/2 and HOLDS at
1/2 through this correction (append-only, no content of the
verified body touched). The one MINOR (m-1): S7.1's eta != 1
coverage sentence above ("the fresh route's F1 frame plus the
erratum's own frame X + hetowr1_supp.py's three frames") reads as
a five-item frame list — it conflates INSTRUMENT LEGS with
DISTINCT FRAMES. Corrected reading: the distinct eta != 1 frames
on record at r1 number THREE, reached by three instruments, with
frame X a single genre datum counted ONCE:

1. **X = PE1's F1 = hetowr1_supp.py's first frame** (one frame,
   three instrument legs): p = 3, Phi' = x^2−6, e1 = 2, eta = 2
   (ord 2), (e2,f2) = (1,2), u2 = 3, psi2 = Z^2+Z+2,
   (W(0),W(1)) = (1,0). Legs: the PE1 fresh route
   `gentow1_pe1_fresh.py` (sealed 9e9d994; 373/0) as F1; the
   GENHN erratum 59c1966's frame-X machine confirmation
   (5f821dc); `hetowr1_supp.py` frame X.
2. **Z** (`hetowr1_supp.py` only): p = 5, Phi' = x^2−10, e1 = 2,
   eta = 2 with ord(eta) = 4, (e2,f2) = (1,2), u2 = 3,
   psi2 = Z^2+Z+1, (W(0),W(1)) = (1,0).
3. **W** (`hetowr1_supp.py` only): p = 5, Phi' = x^3−10, e1 = 3,
   eta = 2, (e2,f2) = (1,2), u2 = 5, psi2 = Z^2+Z+1,
   (W(0),W(1)) = (1,0).

Instrument legs != frames: three instruments, three distinct
frames — not five. Seam-diversity caveat carried from the PE2
report: the three enumerated frames sit at i(u2) = 1 with
W(0) = 1, W(1) = 0 (X, Z, and W alike per the pins above); a
gauge-live frame at i(u2) >= 2 or W(0) >= 2 remains uncovered
machine-side. The wrap-immunity legs the annex leans on (PE1's
Step 0 value-blind re-derivation; F1 at 373/0) are unaffected by
this count repair. BYTE-FREEZE: pre-append body md5 c2f4f3d1
(c2f4f3d148b1ab94c5f9f95aa01de139) = commit 477b1b1, 38,204
bytes, re-verified by prefix after the append; sealed artifacts
byte-untouched; statement displays untouched.

### Dated acceptance record + correction (2026-08-10, post-PE3)

**ACCEPTANCE.** PE2 CLEAN (0C/0G/1m; report `GENTOW1_passPE2_report.md`
@ 1e99926) + PE3 CLEAN (0C/0G/1m; report `GENTOW1_passPE3_report.md`
@ 4aff731): the acceptance counter closed 1/2 -> **2/2 — ACCEPTED**.
The note is FROZEN as of this record; dated appends only. The arc in
one breath: the gauge consumption at PE1 (F-1 — the note consumed the
pre-erratum gauge-naive chat_t display) -> the r1 gauge annex (S7.1,
the corrected key `chat_t := lift(c_t*eta^{W(t)})` pinned at the nine
manifest sites) -> two consecutive cleans (PE2 @ 1e99926, PE3 @
4aff731). PE3 additionally re-derived the ONTO cardinality argument
and GENTOW-5(c)/(d) on its own paper and ran a fresh route GREEN
85/0 (sealed 4ccc8c5: H1 first non-prime-q frame, q = 4; H2 first
gauge-live x mu2 = 3 frame).

**PE3 m-1 CURE (the seam-diversity sentence).** The post-PE2 dated
correction above states "the three enumerated frames sit at
i(u2) = 1 with W(0) = 1, W(1) = 0 (X, Z, and W alike per the pins
above)" — the i(u2) leg is FALSE at frame W. Verified at the
`hetowr1_supp.py` source: `def i(self, k): return k % self.e1`
(line 102) with frame W's constructor
`FW = Frame('W', 5, 3, [-10, 0, 0, 1], 2, 5, -1, -1, ((3, 2),))`
(line 155), i.e. e1 = 3, u2 = 5, so **i(u2) = 5 mod 3 = 2** at
frame W (frames X and Z: u2 = 3, e1 = 2, i(u2) = 1). The
(W(0),W(1)) = (1,0) pins stand: W(0) = floor(2*2/3) = 1 at frame W
(NOT floor(2*1/3) = 0 — do not consume i(u2) = 1 in frame-W wrap
arithmetic). Corrected caveat: frame W IS a machine-covered
gauge-live i(u2) = 2 datum, so the i(u2) >= 2 axis is NOT uncovered;
**the honest residual uncovered seam axis is W(0) >= 2 only**. The
slip's direction was conservative (coverage understated); statement
displays and sealed artifacts byte-untouched by this append.

BYTE-FREEZE: pre-append body md5 3b204e4a
(3b204e4a08f11249c3bb901a6773872e) = commit 0bb7610, 40,228 bytes,
re-verified by prefix after this append; edit shape append-only.

### Dated correction (2026-08-10, post-GENTOW5-r2): the S3 K2-digit
### lift display corrected to the per-flavor base re-solve

**Provenance.** GENTOW5's r2 (PE2 F-2) corrected ITS lift display
and flagged this note's S3 for the same defect ("GENTOW1 S3's
fixed-base READING of its lift display fails the same way at
seam-live heights — a display-level defect there, flagged for that
note's own arc"; GENTOW5_PROOF_2026-08-09.md S2, machine row
FA1-LIFT, gentow5_pe2_fresh.py @ 40f313a, 22/0). Adjudicated this
round; honest statement-repair under standing authority.

**THE DEFECT (display-level, machine-witnessed at GENTOW5's
FR-A).** S3's setting sentence, quoted: "K2-DIGIT LIFT: for s =
Sum_{t<f2} s_t eta2^t (s_t ∈ K), lift(s; m) := Sum over the f1f2
within-class monomials x^{i+e1r} Phi'^{b+e2t} at height m with
O-digit coefficients realizing the components in the coherent
normalization". With (i, b) bound to n2hat(m)'s base exponents
(the sentence's only antecedent) this is the FIXED-BASE display:
base solved once at m, steps e1r, e2t added, pi-exponent left to
compensate. At seam-live heights the compensating pi-exponent goes
NON-INTEGER and the displayed flavor DOES NOT EXIST. Counter-
instance (GENTOW5 PE2's frame FR-A: p = 3, e1 = 2, h = 1, e2 = 1,
u2 = 3; m = 14, n2hat(14) = 3^7): the t = 1 flavor as displayed
demands pi-exponent (14 − 3)/2 = 11/2 — no such monomial; machine
row FA1-LIFT asserts the fixed-base flavor's non-existence AND
runs the green chain on the re-solved member 3^5·x·Phi_1 =
n2hat(11)·Phi_1 (the x-exponent re-solves 0 -> 1).

**THE CORRECTED DISPLAY (the base RE-SOLVES per flavor).**

    lift(s; m) := Sum_{r,t} d_{r,t} · M_{r,t}(m),
    M_{r,t}(m)  := n2hat(m − Delta(r,t)) · x^{e1·r} · Phi'^{e2·t},
    Delta(r,t)  := e1e2h·r + e2u2·t,

indexed 0 <= r < f1, 0 <= t < f2 (a flavor is absent when
n2hat(m − Delta(r,t)) has no ladder solution), with O-digit
coefficients d_{r,t} realizing the components of s in the coherent
normalization — GENTOW5's [GT5-r2] corrected display at i = 2
(Delta specialized by ehat_2 = e1e2; dv2(x) = e2h, dv2(Phi') =
u2). Each M_{r,t}(m) sits at dv2-height m EXACTLY (n2hat
contributes m − Delta(r,t); x^{e1r} adds e1e2h·r; Phi'^{e2t} adds
e2u2·t), and the exponents stay in ladder range (x-exponent
i′ + e1r < e1f1 = D′ since i′ < e1; Phi'-exponent b′ + e2t < e2f2
since b′ < e2, the re-solved base exponents), so the frozen
sentence "deg lift < D2 always" stands as written.

**ADJUDICATION (what S3 actually consumes; checked at each use
site this round).** The correction changes the truth value of the
DISPLAY SENTENCE ONLY — as written it names f1f2 monomials of the
fixed-base exponent pattern "at height m", and at seam-live
heights no such monomials exist (FR-A above). The consuming
sentences read lift/what through interface properties the
corrected display preserves: (1) height-lam exactness [proof (i)
"what's slots sit at dv2-height lam > E2"; (iv)'s minimal-height
term at (mu2−j)lam]; (2) deg lift < D2 with Phi'-exponents < e2f2
[proof (i)'s x-side bound is parameterized by (weight,
Phi'-exponent) only — "a weight-lam grid monomial with
Phi'-exponent b has x-height lam − b(u2 − e2D'h)" — pattern-free];
(3) the coherent-normalization residue realization [layer 1's
substitution T ↦ T + s̄; (iv)'s residue binom(mu2,j)(−s̄)^{mu2−j}];
(4) O-digit freeness of the flavors [(iii)'s triangularity/
bijection and "|K2| − 1 letter choices" — supplied under the
corrected display by the class-separation derivation, GENTOW5-C's
(LIFT_i) clause at i = 2]. The battery's eight refine rows
(A5-R1/A5-R2/A7-R1/B-R1/B-R2/C-R1/D-R1/D-R2) re-divided ACTUAL
polynomials PARI-exact — the machine objects were the true
(re-solved) monomials, e.g. B-R2's two-monomial lift 16 + 4xPhi'
carrying the re-solved x-exponent; no sealed artifact or row is
touched. Truth values of LEMMA GENTOW-2's clauses (i)–(iv), their
proof sentences, and S4's ledger sentences: UNCHANGED by this
correction.

BYTE-FREEZE: pre-append body md5 06ee4edb
(06ee4edb86527692f82902a497646e88) = commit 31388f4, 42,255 bytes,
re-verified by prefix after this append; edit shape append-only;
the S3 display sentence itself stays byte-frozen — this dated
correction GOVERNS its reading.
