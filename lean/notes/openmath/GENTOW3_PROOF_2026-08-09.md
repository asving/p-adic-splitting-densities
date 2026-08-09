# GENTOW-3: THE FAITHFULNESS GEOGRAPHY ([GENHN-TOW-1] item (3))
## When the stage-shadow read agrees with the composed read

**2026-08-09 — SKELETON (sections filled per-commit; machine leg
sealed-then-verdict). Unit: GENTOW-3, BOX-CLOSURE campaign wave B1.
Grade target: 0/2 (attempt; hostile arc owed).**

CHARGE: characterize EXACTLY when the stage-shadow read (T(b)'(iv):
the coefficientwise mod-Phi' projection G-hat_j(theta, Y)) agrees
with the composed read (the Phi2-development of f itself) — the
per-height criterion, T(a)'s event-band survival as a theorem, and
the leaf-depth failure quantified at the PE1 anchors.

SOURCES CONSUMED (never edited): GENHN_PROOF_2026-08-08.md S8 [r2]
annex — LEMMA GENHN-T(b)' clauses (i)-(iv), especially (iv) [THE
STAGE SHADOW + FAITHFULNESS THRESHOLD] and its proof (functoriality
of monic division; discrepancy Phi'(x0)H_j at dv2 >= u2 +
dv2(H_j-class)); GENHN_passPE1_report.md (the three refuted n = 8
instances, the 16Phi'-at-21 mechanism); GENTOW1_PROOF_2026-08-09.md
(LEMMA GENTOW-1 budgets + Step 0 carry monotonicity, LEMMA GENTOW-5
ledger, the constant E2 = e2f2u2); machine: gentow1_checks.py
(families imported additively).

## STATUS TABLE

| deliverable | statement | status |
|---|---|---|
| (a) per-height criterion | THEOREM GENTOW-3 (S2) | PROVED |
| (b) T(a) event-band survival | COR GENTOW-3.C (S3) | PROVED |
| (c) leaf failure quantified | S4 (PE1 anchors = first violation) | DONE |
| battery | gentow3_checks.py (S5) | GREEN 1,032/0, 3/3 teeth |

## S0. THE ONE CONSTANT AND THE THRESHOLD (announced up front)

    delta := u2 − e2·D'h   (>= 1: the [r1] node floor, integers)
    THETA_j := (mu2 − j)·E2 + delta     (per composed coordinate j)

THE GEOGRAPHY (proved in S2): the stage-shadow read is
digit-faithful at every consulted dv2-height < THETA_j; at
overflow genres it fails AT THETA_j (attained by the key power's
own shadow); at x-free genres (every lift coefficient of the
composed key an x-free monomial) it is faithful at EVERY height.
The entry band (heights <= (mu2−j)E2) sits below THETA_j with
margin delta at every genre — T(a)'s survival. At delta = 1 the
first leaf height IS the threshold (the PE1 geography, 21 = 20+1);
at delta >= 2 a faithful leaf band of width delta − 1 exists
(FAM-A7: pins 29, 30 faithful; first violation 31).

## S1. THE EXAMPLE TABLES (examples-first) — filled at verdict

## S2. THEOREM GENTOW-3 (the per-height criterion)

**Setting (T(b)' + GENTOW-1 S0, restated for one pass).** Tower
locus 𝒯 (full inner side e2f2mu2 = mu1): outer genre
(Q; e1, f1, mu1; h), key Phi' (deg D' = e1f1), inner slope
kappa2 = u2/e2, composed key Phi2 (deg D2), dv2 = e1e2·v, slot
offsets w(a,b) = a·e2h + b·u2, E2 = e2f2u2. THE TWO READS at
member f ∈ 𝒯, per composed coordinate j < mu2:
* COMPOSED (honest): C_j from f = Phi2^{mu2} + Σ C_j Phi2^j in
  Ô[x]; pins/residues by GENHN-2' slot-mins (accepted annex).
* STAGE SHADOW (the refuted T(b) object): the two-variable division
  F(x,Y) = Y^{mu1} + Σ A_J(x) Y^J = Σ_j Ĝ_j(x,Y)·K2(x,Y)^j carried
  out over R = Ô[x]/(Phi') — every coefficient reduced mod Phi';
  K2(x,Y) is the Y-form of the key (Phi2 = K2(x,Phi')). Shadow
  coordinate ShC_j := Σ_b ḡ_{j,b}(x)Phi'^b (deg ḡ < D'), read on
  the same slot grid. (Functoriality of monic division identifies
  this with T(b)'(iv)'s Ĝ_j(θ,Y) — the (iv) proof, consumed.)

X-FREE GENRES: call the genre x-free iff every lift coefficient
ĉ_t·n̂(u2(f2−t)) of Phi2 (t < f2, ĉ_t ≠ 0) is an x-free monomial
π^a — equivalently i(u2(f2−t)) = 0, i.e. e1 | u2(f2−t)·h⁻¹-class;
witness FAM-D: Phi2 = (x²−3)² + 27, lift = −27 = π³-flavor.

**THEOREM GENTOW-3 (the faithfulness geography).** Set
delta := u2 − e2D'h (≥ 1, the [r1] node floor) and
THETA_j := (mu2 − j)·E2 + delta. On 𝒯:
(i) [FLOOR] every dv2-height at which ShC_j and C_j carry
different slot digits is ≥ THETA_j; equivalently the first
disagreeing height pin(ShC_j − C_j) ≥ THETA_j.
(ii) [FAITHFUL BAND] at every height m < THETA_j the two reads'
digits agree — values, classes, and K2-residues. Consequently any
read whose consulted heights at coordinate j are all < THETA_j
(pins, deciding residues, event data) returns identical output on
both reads; in particular if the composed pin p_j < THETA_j then
the shadow pin equals it with the same residue.
(iii) [X-FREE EXACTNESS] at an x-free genre the discrepancy is
ZERO at every height: ShC_j = C_j identically on 𝒯 — the shadow
IS the composed read.
(iv) [ATTAINMENT — the leaf-depth failure] at a non-x-free genre
whose key power's self-overflow is non-cancelling (certificate
below; machine-checked at FAM-A5/A7/B/C), the floor is ATTAINED:
f = Phi2^{mu2} has composed read DRAIN (C_j = 0) while its shadow
read carries a nonzero digit at exactly THETA_j at the touched
coordinate(s) — and deep perturbations (disc ≠ 0) keep the
divergence. The shadow read at heights ≥ THETA_j is NOT a function
of the honest data.

*Proof.*

**Step 0 (weights, from GENTOW-1 Step 0 — consumed).** For a
two-variable monomial π^v x^{a'} Y^{b'} (a', b' unrestricted) set
wt := e1e2·v + a'·e2h + b'·u2. The x-carry x^{D'} = Phi' + tail
splits weight-monotonically: tail branches at weight ≥ parent
(equality on the key's side), the Phi'-branch at parent + delta
EXACTLY (x^{D'}-part carries D'e2h, the Phi'-part u2). The
Phi'-carry Phi'^{e2f2} = Phi2 + lifts is weight-preserving with
the Phi2-part at E2 (GENTOW-1 Step 0 verbatim).

**Step 1 (the division ledger: Ĝ_j sits at weight ≥ (mu2−j)E2).**
On 𝒯 the entry pins lie weakly above the inner side:
e2·dv(A_J) ≥ (mu1 − J)u2, so every term of A_J·Y^J has
wt ≥ (mu1−J)u2 + J·u2 = mu1·u2 = mu2·E2; Y^{mu1} likewise. Every
term of K2 has wt = E2 exactly (side terms of the key — T(b)'(i)).
Monic division in Y is weight-monotone against such a key: the
step killing a top term c·x^α Y^{β+e2f2} of the running remainder
(wt ≥ W) subtracts c x^α Y^β·K2, whose terms sit at
(wt of killed term) − E2 + E2 ≥ W; the quotient term c x^α Y^β at
≥ W − E2. Induction down the Y-degree: remainders stay ≥ W,
quotients ≥ W − E2. Iterating the K2-division mu2 times from
F (wt ≥ mu2E2): every term of Ĝ_j(x,Y) has wt ≥ (mu2−j)E2 — in
the UNREDUCED weight (x-degrees kept literal; the division is
LINEAR in F, so Ĝ_j-terms are A_J·(products of K2-coefficients),
x-degree ≤ (D'−1) + Σ i_t-parts).

**Step 2 (the discrepancy floor = (i)).** The shadow run reduces
every coefficient mod Phi' at every step; the honest composed C_j
re-expands Ĝ_j(x, Phi') on the slot grid. Their difference is
exactly the content routed through Phi'-branches of x-carries:
* an x-overflow monomial of Ĝ_j (a' ≥ D', wt ≥ (mu2−j)E2 by
  Step 1) reduces along x^{D'} = Phi' + tail: the shadow keeps
  only the iterated tail route (weight ≥ parent); every branch
  retaining k ≥ 1 Phi'-factors sits at wt ≥ parent + k·delta ≥
  (mu2−j)E2 + delta = THETA_j (Step 0);
* branches whose Phi'-exponent reaches e2f2 recarry through
  Phi2 = Phi'^{e2f2} − lifts INTO coordinate j+1: arriving content
  came from Ĝ_{j'} (j' ≤ j) overflow branches with k ≥ e2f2 − b' ≥
  1 extractions per Phi2-step, each Phi2-absorption spending E2 of
  weight: slot weight at the receiving coordinate j ≥
  (mu2−j')E2 + k·delta − (j−j')E2 ≥ (mu2−j)E2 + delta = THETA_j.
  Recarry moves content only UPWARD in j (division uniqueness —
  T(b)'(iv)'s recarry remark, consumed);
* the reduction discrepancy at each division step feeds forward
  into later steps only through coefficients already ≥ THETA-
  floored; subsequent multiplications by K2-coefficients (wt = E2
  each, prices one j-step) and subtractions preserve the ledger.
By GENHN-2' each slot digit's dv2-value is the slot-min exactly and
heights separate classes (one K2-digit per height), so
"difference supported at weights ≥ THETA_j" reads off as: every
disagreeing HEIGHT is ≥ THETA_j. ∎(i)
(ii) is (i) restated: below THETA_j the digit strings coincide, and
every displayed read-output (pin values, residues, labels, σ,
event data) is a function of the consulted digits. ∎(ii)
(iii): at an x-free genre every K2-coefficient is x-free, the
division's coefficient arithmetic never raises x-degree above
deg A_J ≤ D'−1 < D': no x-overflow ever occurs, reduction mod Phi'
is the identity on every coefficient, and Σ_b g_{j,b}Phi'^b (all
x-degrees < D2, Phi'-exponents < e2f2) is the unique composed
development: ShC_j = C_j. ∎(iii)
(iv): for f = Phi2^{mu2} the composed division is exact: C_j = 0,
all j < mu2 — the honest read is DRAIN. The shadow object is the
self-shadow of the key power: K2(x,Phi')^{mu2} = Phi2^{mu2}, but
the shadow division sees F = the level-1 development of Phi2^{mu2},
whose x-overflow content (the products of x-ful lift monomials
crossing D') re-enters as genuine level-1 data that the reduced
K2-powers can no longer cancel. All terms of K2^{mu2} sit at
wt = mu2E2 exactly; the minimal surviving branch is a single
Phi'-extraction: height THETA_j at the touched coordinate,
NONZERO whenever the assembled K2-digit does not cancel — the
per-genre CERTIFICATE, decided by one finite computation
(machine-checked: A5/A7/C touch j = 0 with digits 16Phi'/64Phi'/
64Phi' at 21/31/43; B touches BOTH: ShC_1 = 4Phi' + 8x at 7,
ShC_0 = 64Phi' + 64x at 13). Deep perturbation f = Phi2^{mu2} + g
(g in-budget with slots at heights > THETA_j, disc ≠ 0): both
reads shift by the SAME g-digits (linearity of both divisions in
f), so the divergence at THETA_j persists while the honest read
becomes a decided leaf — two members with identical shadow data
and different honest reads are then immediate (vary g above the
shadow's fake pin), and conversely the PE1 triple varies the
shadow read at fixed honest σ. ∎(iv)

**Scope remarks (honest).** (1) The certificate in (iv) is a
non-cancellation of one explicitly displayed K2-digit; it is
decided per genre by finite arithmetic, machine-checked at the
five battery families, NOT proved as a genre-general
non-vanishing (GENTOW3-BOX-1, S6) — the floor (i)/(ii)/(iii) is
general. (2) Attainment via entry-digit-driven overflows (genres
where the key self-power stays below D' in x but products with
full-degree entry digits overflow) is covered by the same Step-2
ledger but no witness battery row is shipped; named in
GENTOW3-BOX-1. (3) Everything is per-coordinate and in-window;
the window interaction is GENTOW-5(a)'s cap (consulted heights
also < e1e2·N) — orthogonal, composes by min.

## S3. COROLLARY GENTOW-3.C (T(a) event-band survival) — S3 commit

## S4. THE LEAF-DEPTH FAILURE QUANTIFIED (PE1 anchors) — S4 commit

## S5. MACHINE LEG (sealed battery gentow3_checks.py) — verdict

## S6. HONEST RESIDUE + GRADE BOX — final commit
