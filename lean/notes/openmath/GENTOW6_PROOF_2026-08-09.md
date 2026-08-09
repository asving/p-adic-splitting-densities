# GENTOW-6: THE BOX RESIDUE UNIT — the mixed-side multiplicity tie
# (GENTOW4-BOX-1), the partial-side block budget layer
# (GENTOW4-BOX-2), and the attainment certificate (GENTOW3-BOX-1),
# 2026-08-09

**STATUS: SKELETON (per-section commits follow). Unit: GENTOW-6,
BOX-CLOSURE campaign residue wave. Grade 0/2 (attempt; hostile arc
owed).**

Charge (three targets, priority order): (1) GENTOW4-BOX-1 — the
mixed-side tie mu2*(r) = m_r, literature-first (FGMN residual
multiplicativity; GENTOW2's faithful-cite pattern) or via HE7's
frozen bouquet machinery; (2) GENTOW4-BOX-2 — the partial-side
entry-budget layer (GENTOW-1's budget lemma at the block factor);
(3) GENTOW3-BOX-1 — the self-shadow attainment certificate made
genre-general or honestly scoped.

Sources consumed (never edited): GENTOW4_PROOF (S0 setting, THEOREM
GENTOW-4.A, LEMMA GENTOW-4.2, COR GENTOW-4.C), GENTOW3_PROOF
(THEOREM GENTOW-3, S0 constants delta/THETA), GENTOW1_PROOF (LEMMA
GENTOW-1, Step 0, LEMMA GENTOW-5, E2), GENTOW2_PROOF (the cite
pattern + the tower<->MacLane dictionary + shear), HE7_PROOF (LEMMAS
HE7-5/6/9/10/11, ANNEX-LEMMA HE7-13'(a)), HE6_PROOF (LEMMAS
HE6-3/HE6-4/HE6-5), HE6R1_RECON (LEMMA HE6R1-2(a)(b)(c) + RIDER),
the FGMN local print
(docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt,
numbering verified at GENTOW2's ledger); machine:
gentow4_checks.py + gentow3_checks.py (imported additively).

## STATUS TABLE

| target | statement | status |
|---|---|---|
| (1) mixed-side tie | LEMMA GENTOW-6.1 (S1) | TBD |
| (2) block budgets | LEMMA GENTOW-6.2 + COR GENTOW-6.2C (S2) | TBD |
| (3) attainment | THEOREM GENTOW-6.3 (S3) | TBD |
| battery | gentow6_checks.py (S4) | TBD |

## S1. LEMMA GENTOW-6.1 (the mixed-side multiplicity tie) —
## PROVED-VIA-CITE + independent corpus derivation

**Setting (GENTOW-4 S0, restated for one pass).** Tower entry,
partial inner side: outer genre (Q; e1, f1, mu1; h), key Phi'
(deg D' = e1f1), dv = e1·v; f monic on the genre-G opening locus,
disc f != 0, Phi' ∤ f (GENTOW-4.1(d) peel); P(F) = the level-1
polygon; fix a side of slope kappa = u/l (lowest terms, l = the
repo's e2 when the side is the inner one) with residual

    R_kappa = c · Prod_r r^{m_r},   c in K^x,  r monic irreducible
    over K = F_{Q^{f1}}, coherent (S4) normalization.

For each r, C_{kappa,r} is the label class, f_{kappa,r} its block
factor (GENTOW-4.A(i)), and — when l·deg r >= 2, so the class has a
composed key Phi2_r (deg D2_r = D'·l·deg r) — mu2*(r) :=
Sum_{lambda2 > T2} L_{lambda2}(P2(f)) is the composed length read
through LEMMA HE6R1-2 at the class's datum (GENTOW-4.A(ii)), with
deg f_{kappa,r} = D2_r·mu2*(r). GENTOW-4.2 proved mu2*(r) = m_r at
PURE-POWER sides (R_kappa = c·psi2^{mu2}) and boxed the mixed case
as GENTOW4-BOX-1. The box closes here:

> **LEMMA GENTOW-6.1 (multiplicity tie, every side shape).** In the
> setting above, for every side of P(F) and every monic irreducible
> r | R_kappa:
>
>     deg f_{kappa,r} = D'·l·deg(r)·m_r ,
>
> i.e. the block's own level-1 polygon is the single side of slope
> kappa and length l·deg(r)·m_r with residual EXACTLY psi_r-power
> r^{m_r} (monic; unit-free), and consequently, at every class with
> l·deg r >= 2 read through the composed key,
>
>     mu2*(r) = m_r
>
> — the composed polygon length equals the level-1 residual
> multiplicity, class by class, at MIXED sides included.

*Proof.* Three steps: the block's pure-power residual with exponent
k_r (I), residual multiplicativity (II — the cite), and the UFD
match k_r = m_r (III).

**Step I (block single-side + pure-power residual — ANNEX-LEMMA
HE7-13'(a)'s argument at the tower entry).** f_{kappa,r} =: f_C is
monic in O[x], divides f, Phi' ∤ f_C, and its roots are exactly
C_{kappa,r} (GENTOW-4.A(i), from LEMMAS HE7-6/HE7-11's arguments at
the level-1 labels). Every root of f_C has dv(Phi'(rho)) = kappa
(the class definition), so by LEMMA HE6-3(b) applied to f_C — whose
hypotheses (monic on the opening locus, disc != 0 as a divisor of
f, Phi' ∤ f_C) hold — every slope lambda of f_C's own polygon
carries D'·L_lambda(f_C) > 0 roots at dv(Phi') = lambda: kappa is
the ONLY slope. The polygon is one side from (0, dv(A_0^C)) to
(M_C, 0), M_C = deg f_C / D' (top development coefficient = 1 since
D' | deg f_C, GENTOW-4.A(i)'s divisibility via LEMMA HE7-5), of
slope kappa and length M_C, so l | M_C and deg R^{(C)} = M_C/l for
the block residual R^{(C)}. Its irreducible factors: by LEMMA HE6-4
applied to f_C, every monic irreducible r' | R^{(C)} has a nonempty
class among f_C's roots — some rho in C has iota_rho(r')(beta_rho)
= 0; but iota_rho(r)(beta_rho) = 0 too, and both r, r' are monic
irreducible over K, both equal THE minimal polynomial of beta_rho
over iota_rho(K): r' = r. (This is HE7-13'(a)'s level-2 derivation
verbatim one level down; the level-1 inputs HE6-3/HE6-4/HE6-5 are
all (SEP)-free.) So R^{(C)} = c_C·r^{k_r}, c_C in K^x, k_r =
M_C/(l·deg r) in Z_{>=1}. Monicity: f_C is monic with development
top coefficient 1 attaining the right endpoint (M_C, 0), so
R^{(C)}'s leading coefficient is the residue of 1 under the
height-0 normalizer: c_C = 1 and R^{(C)} = r^{k_r} exactly.

**Step II (residual multiplicativity — the FGMN cite).** Claim: for
monic g, h on the opening locus with Phi' ∤ gh,

    (MULT)  L_kappa(P(gh)) = L_kappa(P(g)) + L_kappa(P(h))  and
            R_kappa^{(gh)} = gamma·R_kappa^{(g)}·R_kappa^{(h)},
            gamma in K^x,

per slope kappa (a factor with no kappa-side contributing length 0
and residual a nonzero constant). CITE (GENTOW2's dictionary +
shear, consumed): instantiate the FGMN chain of GENTOW2 S2 at depth
2 — mu0 −(x, h/e1)→ mu1 −(Phi', lambda)→ mu2 with lambda the shear
image of kappa (kappa = e(mu1)(w2 + lambda), w2 = mu1(Phi');
GENTOW2's NORMALIZATION SHEAR carries the repo pin cloud
bijectively onto the FGMN cloud, lines to lines). Quotes at the
verified layout numbering
(docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt):
* **Theorem 2.8** (L543–546): "Let mu be a valuation and phi a key
  polynomial for mu. Then, N^-_{mu,phi}(gh) = N^-_{mu,phi}(g) +
  N^-_{mu,phi}(h) for any non-zero g, h in K[x]." — polygon
  additivity (Minkowski sum: sides join, per-slope lengths add).
* **Corollary 4.7(3)** (L1121–1134): "R_i(gh) = R_i(g)R_i(h) for
  all g, h in K[x]." — residual-operator multiplicativity, proved
  there from Theorem 4.2 + Lemma 4.1, no hypothesis on g, h.
* **Corollary 4.4(4)** (L1084–1090): "deg R_i(g) = (s'(g) −
  s(g))/e_i and R_i(g)(0) != 0." — a factor with no kappa-side has
  s'(g) = s(g), hence R_i(g) a nonzero CONSTANT: it perturbs (MULT)
  only through gamma.
Instantiation map: i = 2, phi_2 = Phi', g, h as given; FGMN's R_2
at slope lambda ↔ the repo residual R_kappa up to the shear + the
coherent-normalizer twist. FAITHFULNESS of the transport for what
Step III consumes: the repo residual and R_2(g) differ by (i) the
shear reparametrization of the side lattice (an affine bijection of
abscissas), (ii) a K^x scalar per height from the twist cocycle,
and (iii) a fixed unit rescaling T ↦ (unit)·T of the variable
(GENTOW2 S2's dictionary rows, incl. psi2 = R_2(phi_3) via FGMN
Cor 5.6(2)); each of the three maps carries irreducible
factorizations to irreducible factorizations bijectively and
preserves MULTIPLICITIES and DEGREES (unit scalings and variable
unit-rescalings of K[T] are ring automorphisms fixing degrees;
the shear only relabels the lattice). So (MULT) for the repo
residual follows from Thm 2.8 + Cor 4.7(3) + Cor 4.4(4). ALSO,
REPO-SIDE (corroboration, no new load): (MULT) is GENTOW-1 Step
1's own mechanism — the weight-graded layer of a product is the
product of the weight-graded layers computed side-term by
side-term (carries land strictly above the side by Step 0's carry
monotonicity; endpoint terms multiply exactly since polygon
vertices attain uniquely at the extremal abscissas), and the side
layer IS the residual in the coherent normalization; the graded
digits multiply as K-digits times wrap units (the S4 cocycle),
whence the K^x scalar gamma. Both legs give the same display.

**Step III (UFD match).** Apply (MULT) to the bouquet
f = Prod_{(kappa',r')} f_{kappa',r'} (GENTOW-4.A(i); finitely many
classes; the S2 peels put Phi' ∤ f). At the fixed slope kappa:
blocks at kappa' != kappa have single-side polygons of slope kappa'
(Step I), i.e. no kappa-side — residual contribution a nonzero
constant; blocks at (kappa, r') contribute r'^{k_{r'}} (Step I).
So, with gamma* in K^x collecting the scalars,

    c·Prod_r r^{m_r} = R_kappa^{(f)} = gamma*·Prod_r r^{k_r}.

K[T] is a UFD and the r are pairwise distinct monic irreducibles:
m_r = k_r for every r (and c = gamma*). With Step I's degree
display deg f_{kappa,r} = D'·M_C = D'·l·deg(r)·k_r =
D'·l·deg(r)·m_r. At a class read through the composed key,
deg f_{kappa,r} = D2_r·mu2*(r) = D'·l·deg(r)·mu2*(r) (LEMMA
HE6R1-2(b) at the class's datum, available by GENTOW-4.1(c));
divide: mu2*(r) = m_r. ∎

**COROLLARY GENTOW-6.1C (consumption).** (a) LEMMA GENTOW-4.2's
pure-power tie is the one-class case (consistency: two proofs).
(b) In THEOREM GENTOW-4.A(iv), the level-1 residual now PREDICTS
every class's composed length: the block menu of a mixed side is
computable from R_kappa's factorization alone — mu2*(r) = m_r
needs no composed read to be known in advance (the read still
DECIDES sigma; what is new is the level-1 forecast). (c) The same
two ingredients (HE7-13'(a) + (MULT) at the level-2 frame, where
FGMN's chain has one more link and Cor 4.7(3) holds verbatim) tie
k = the multiplicity of r in R_lambda at HE7-13'(a)'s level-2
blocks; this is HE7-BOX-4's content — NOT consumed by anything
here, flagged for HE7's own ledger (its consumption is the
orchestrator's, not this unit's).

**Scope remark (honest).** Step I consumes LEMMA HE6-3/HE6-4 at
f_C, which need f_C monic on the opening locus with disc f_C != 0
— both inherited from f (divisor of a squarefree O[x]-polynomial;
the opening-locus conditions are root-wise). Step II's cite is to
the verified LOCAL print at verified line numbers; the repo-side
leg is displayed but the cite alone carries the load (GENTOW2's
pattern). No claim is made at sides of f with kappa <= D'h (none
exist: GENTOW-4.1(a)).

## S2. LEMMA GENTOW-6.2 (the block budget layer) — TBD

## S3. THEOREM GENTOW-6.3 (the attainment certificate) — TBD

## S4. MACHINE LEG — TBD

## S5. HONEST RESIDUE + GRADE BOX — TBD
