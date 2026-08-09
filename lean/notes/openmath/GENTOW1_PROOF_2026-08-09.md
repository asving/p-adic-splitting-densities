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

[statement + proof: see S2 commit]

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
