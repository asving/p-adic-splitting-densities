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

[statement + proof: see S3 commit]

## S4. LEMMA GENTOW-5 (composed window ledger; item (5))

[statement + proof: see S4 commit]

## S5. MACHINE LEG (sealed battery, two-commit discipline)

[runner gentow1_checks.py; preregistered predictions in its
docstring; >= 3 teeth incl. wrong-floor mutant; verdict from
committed artifacts]

## S6. HONEST RESIDUE (what this note does NOT prove)

[GENHN-TOW-1] items (3) faithfulness geography, (4) partial inner
sides, (6)(alpha) iterated carry bookkeeping: NOT touched here.
Discharge of items (1)/(2)/(5) into GENHN_PROOF is the
orchestrator's later dated consumption update, not this note.
