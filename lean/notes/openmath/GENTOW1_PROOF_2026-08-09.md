# GENTOW-1: composed entry budgets, inner refine transfer, composed window ledger
## ([GENHN-TOW-1] items (1), (2), (5) — proof attempt, BOX-CLOSURE campaign wave B1)

**2026-08-09 — SKELETON (composition in progress; per-section commits
follow). Grade 0/2 (attempt; hostile arc later). Unit: GENTOW-1.**

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
| battery | gentow1_checks.py | GREEN 15,478 checks / 0 violations, 5/5 teeth (S5) |

## S0. SETTING AND NOTATION (all from T(b)', restated for one-pass reading)

Outer genre (Q; e1, f1, mu1; h), key Phi' (deg D' = e1f1), dv = e1*v.
Inner CS event on the level-1 stage read: side of dv-slope kappa2 =
u2/e2 (gcd(u2,e2)=1, u2 > e2*D'h by the [r1] node floor), residual
psi2^{mu2} over K = F_{Q^{f1}}, f2 = deg psi2, FULL side e2f2mu2 =
mu1. Composed key Phi2 = Phi'^{e2f2} - Sum_{t<f2} chat_t
n(u2(f2-t)) Phi'^{e2t}, monic, deg D2 = D'e2f2. Composed ladder
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

## S1. THE EXAMPLE BATTERY (examples-first; laws read off tables)

[Section composed at S5-commit from the sealed runner's tables:
families FAM-A (2,1,4)->(2,1,2) q=2 u2 in {5,7}; FAM-B
(2,1,4)->(1,2,2) q=2 K2=F4; FAM-C (2,1,6)->(3,1,2) q=2 e2=3 n=12;
FAM-D (2,1,4)->(1,2,2) q=3 K2=F9. Exact budget/window/refine tables
via slot arithmetic + PARI (idealprimedec valuations = nfeltval
route, factorpadic route).]

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
  weight E2 exactly.
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
strictly above the side — the [r2] parenthetical). Multiplicativity
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
dv2(Phi2(x0)) > E2. ∎

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
chat_t); deg lift < D2 always (x-exponents < e1f1 = D',
Phi'-exponents < e2f2).

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

[runner gentow1_checks.py; preregistered predictions in its
docstring; >= 3 teeth incl. wrong-floor mutant; verdict from
committed artifacts]

## S6. HONEST RESIDUE (what this note does NOT prove)

[GENHN-TOW-1] items (3) faithfulness geography, (4) partial inner
sides, (6)(alpha) iterated carry bookkeeping: NOT touched here.
Discharge of items (1)/(2)/(5) into GENHN_PROOF is the
orchestrator's later dated consumption update, not this note.
