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

## S2. LEMMA GENTOW-6.2 (the block budget layer — GENTOW4-BOX-2's
## budget display)

GENTOW-1's budget/fibration lemma is proved on the FULL-side locus
𝒯 (one side, residual psi2^{mu2}). GENTOW4-BOX-2 records that the
partial-side geography had no budget display. The prompt of the box
resolves exactly as expected: the bouquet makes each block a
full-side instance one level in, so GENTOW-1 fires AT THE BLOCK
verbatim with mu2 ↦ mu2*, and COR GENTOW-4.C's projection makes the
display visible on f's own pins.

> **LEMMA GENTOW-6.2 (block entry membership).** In the S1 setting,
> fix the inner class S = C_{kappa2,psi2} (l·f2 >= 2, composed key
> Phi2, E2 = e2f2u2), let f_S be its block factor and mu2* = m_{psi2}
> its composed length (S1). Then f_S lies on GENTOW-1's tower-entry
> locus 𝒯* := 𝒯(Q; e1, f1, mu1* ; h; Phi'; u2, e2, psi2, mu2*) with
> mu1* := e2f2·mu2* — the FULL-side locus at the block genre: f_S is
> monic of degree mu2*·D2 on the genre-G opening locus with
> disc f_S != 0, and its level-1 polygon is ONE side of slope kappa2
> from (0, mu1*·kappa2) to (mu1*, 0) with twist-coherent residual
> psi2^{mu2*} exactly.
>
> *Proof.* Monic, degree D2·mu2* = D'·mu1*: S1 Step I + LEMMA
> HE6R1-2(b). Opening locus + disc != 0: rootwise/divisor-inherited
> from f. Single side of slope kappa2, length mu1*, residual
> monic = psi2^{mu2*}: S1 Step I with r = psi2, k_{psi2} = m_{psi2}
> = mu2* (S1 Step III). Twist coherence: the block residual is
> computed in the same coherent S4 normalization as f's (Step I
> reads it through the same normalizers). Endpoints: right endpoint
> (mu1*, 0) is the monic top; left endpoint (0, mu1*·kappa2) is on
> the side since the polygon has no other side. ∎

> **COROLLARY GENTOW-6.2C (the budget display at the block + its
> projection).** With LEMMA GENTOW-6.2, the following hold VERBATIM
> at f_S — LEMMA GENTOW-1(a)(b)(c)(d), COROLLARY GENTOW-1.1, LEMMA
> GENTOW-2 (at its stated scope), LEMMA GENTOW-5 — each with
> mu2 ↦ mu2*, i.e.:
> (a) [BUDGETS] in f_S = Phi2^{mu2*} + Sum_{j<mu2*} C_j^S Phi2^j,
> the composed digits obey
>
>     v(c^S_{j,a,b}) >= ceil( ((mu2*−j)E2 − w(a,b)) / (e1e2) ) + [pin],
>     [pin] = 1 iff e1e2 | (mu2*−j)E2 − w(a,b) >= 0
>
> — GENTOW-1(a)'s display with the block side height (mu2*−j)E2;
> (b) [FIBRATION] f_S ↦ (c^S_{j,a,b}) bijects the block locus onto
> the budget box; per window N the free-O-digit count is
> Sum_{j,a,b} (N − floor*(j,a,b)) — the COUNT layer at the block;
> (c) [NODE + FIELD FLOORS] p_j^S >= (mu2*−j)E2 + 1 (sharp), and
> dv2(Phi2(x0)) > E2 at every root x0 of f_S;
> (d) [PROJECTION VISIBILITY] via COR GENTOW-4.C (c_g-translation),
> (a)+(c) display on f's own pins: wherever (j, p_j) lies on the
> >T2 initial segment of P2(f), p_j − c_g clears the (a)/(c) floors
> — the budget test runs on f without exhibiting f_S; and the block
> window ledger (GENTOW-5 at f_S) caps consulted block heights at
> e1e2·N − c_g when read through f's window-N data.
>
> *Proof.* (a)–(c): GENTOW-1 and GENTOW-5's proofs are stated for
> an arbitrary member of 𝒯 at its genre; LEMMA GENTOW-6.2 puts f_S
> in 𝒯* and the constants (u2, e2, f2, E2, w(a,b), dv2) are those
> of the class — only mu2 is re-instantiated. (d): COR GENTOW-4.C
> proved p_j^S = p_j − c_g on the >T2 hull and already transported
> the node floors; the budget floors (a) transport by the same
> displayed equality; the window shift: a block digit consulted at
> block height m corresponds through HE6R1-2(b) to f-data at height
> m + c_g, and f's window-N cap is e1e2·N (GENTOW-5(a) at f), so
> the block read is lift-stable below e1e2·N − c_g. ∎

**What GENTOW4-BOX-2 asked beyond this, honestly parked.** The box
names "budget/count LAWS on the partial-side locus" — the display
above supplies the budget/count layer PER BLOCK (and per class,
each at its own key, by the same instantiation). What is NOT
delivered: the product-measure ledger for the f-locus itself — the
count of f's per window as a product over (class boxes) x (sibling
data), which requires pricing the multiplication map
(f_S, g) ↦ f_S·g on ambient windows (a Jacobian/content identity).
That counting seam was already open at FULL sides (GENTOW-1's
count-law remark: "the per-genre tower count LEDGERS ... a counting
unit NOT executed here") and is not specific to partial sides; it
stays named as GENTOW6-BOX-2 (S5). The box's BUDGET half is closed
by the display above; the LEDGER half was never a partial-side
novelty.

## S3. THEOREM GENTOW-6.3 (the attainment certificate — GENTOW3-BOX-1
## made genre-general at mu2 = 2)

**Setting (GENTOW-3 S0/S2, restated).** Full-side tower genre;
Phi2 = Phi'^{e2f2} − Sum_{t in T} chat_t·nhat(u2(f2−t))·Phi'^{e2t},
T := {t < f2 : chat_t != 0} (nonempty: Phi2 irreducible needs the
t = 0 term, 0 in T), nhat(m) = pi^{a_m} x^{i_m} with
e1·a_m + i_m·h = m, 0 <= i_m < e1. Write i_t := i_{u2(f2−t)},
a_t := a_{u2(f2−t)}, and t* := max T. X-FREE genre ⟺ i_t = 0 for
every t in T (GENTOW-3's definition). delta = u2 − e2D'h,
THETA_j = (mu2−j)E2 + delta. The self-shadow object: f = Phi2^{mu2},
honest composed read C_j = 0 (DRAIN); shadow read ShC_j from the
K2-division of F = the level-1 development of Phi2^{mu2} over
R = Ô[x]/(Phi'). THEOREM GENTOW-3(i) floors every discrepancy at
THETA_j; clause (iv)'s ATTAINMENT rested on a per-genre certificate
(machine-checked at 4 families) — GENTOW3-BOX-1. Scope here:
**mu2 = 2** (every first-live tower shape; GENTOW-BOX-2's
geography) — the mu2 >= 3 display is written where it is uniform
and boxed where it is not (S5).

> **THEOREM GENTOW-6.3 (attainment at mu2 = 2, every genre).** For
> f = Phi2^2 at any tower genre:
>
> (a) [SOURCE CLASSIFICATION] the height-THETA graded layer of the
> discrepancy (ShC_j − C_j over the composed grid) is a sum of
> SINGLE-Phi'-extraction branches, one per x-overflowing lift pair:
> the products (chat_t nhat_t Phi'^{e2t})·(chat_{t'} nhat_{t'}
> Phi'^{e2t'}), (t, t') in T^2, with i_t + i_{t'} >= D'; a pair's
> branches enter at two-variable position (x^{i_t+i_{t'}}, Y^{e2(t+t')}),
> are extracted to Y-exponent e2(t+t') + 1, and every subsequent
> division/recarry step emits terms of Y-exponent LOWERED by
> e2f2 − e2s >= e2(f2 − t*) >= e2 > 0 (s in T) at the same weight.
> Multi-extraction branches sit at weight >= THETA + delta; tail
> (non-extraction) routes are shared by both reads and cancel.
>
> (b) [CERT-TOP: the top-lift certificate] if 2·i_{t*} >= D', the
> composed slot at two-variable position (x^{2i_{t*}−D'}, Y^{2e2t*+1})
> — composed coordinate j* = floor((2e2t*+1)/(e2f2)), slot
> b* = (2e2t*+1) mod e2f2, a* = 2i_{t*} − D' — receives EXACTLY ONE
> height-THETA branch, of digit
>
>     (chat_{t*})^2 · pi^{2a_{t*}} · (wrap unit) ,   v = 2a_{t*},
>
> nonzero in the field K2: the shadow diverges at height
> THETA_{j*} = (2−j*)E2 + delta at coordinate j*, exactly on the
> floor. In particular GENTOW-3(iv)'s certificate holds
> UNCONDITIONALLY at every genre with 2i_{t*} >= D'.
>
> (c) [NO-OVERFLOW EXACTNESS] if i_t + i_{t'} < D' for every pair
> (t, t') in T^2, then the level-1 development of Phi2^2 equals
> K2(x, Y)^2 term by term on the grid (no x-carry ever fires), the
> shadow division is the honest division, and ShC_j = C_j = 0: the
> key-power witness is shadow-EXACT.
>
> (d) [REGIME 3] genres with some i_t >= 1 (non-x-free) and no
> overflowing pair exist (witness FAM-E, S4: (e1,f1,mu1;h) =
> (3,1,4;1)/Q2, e2 = 2, f2 = 1, u2 = 7, i_0 = 1, 2i_0 = 2 < 3 = D'),
> and there the geography's failure clause survives through ENTRY-
> driven overflows: a displayed member (S4's E-ENTRY row: an entry
> digit at a slot with a + i_{t} >= D') has shadow read != honest
> read at a displayed height >= THETA_j, both reads decided,
> PARI-adjudicated. Attainment AT EXACTLY THETA via entry drivers,
> and the general classification of which regime-3 members diverge,
> is NOT claimed as a theorem — GENTOW6-BOX-3 (S5).
>
> *Proof.* (a) GENTOW-3 Step 2's ledger already classifies
> discrepancy content as x-carry Phi'-branch routes, k extractions
> costing k·delta above the weight-2E2 source layer; at height
> THETA = 2E2 + delta exactly, k = 1 and every non-extraction step
> is weight-exact. The weight-2E2 monomials of F with x-degree >= D'
> are exactly the overflowing lift-pair products: expanding
> K2(x,Y)^2 multinomially at mu2 = 2, the terms are Y^{2e2f2}
> (x-free), the k = 1 terms −2chat_t nhat_t Y^{e2f2+e2t} (x-degree
> i_t < e1 <= D': never overflow), and the pair terms
> chat_t chat_{t'} nhat_t nhat_{t'} Y^{e2(t+t')} of x-degree
> i_t + i_{t'}. A single extraction rewrites x^{I} (D' <= I < 2D',
> since i < e1 <= D' each) as x^{I−D'}·Phi' + x^{I−D'}·tail with
> the Phi'-part in-grid (I − D' < D'), raising the Y(=Phi')-
> exponent by exactly 1. Subsequent processing of a height-THETA
> branch keeps weight (else it leaves the layer): the shadow-side
> division steps subtract quotient·K2, emitting lift terms with
> Y-change −e2f2 + e2s (s in T); the honest-side re-expansion of
> Phi'-exponents >= e2f2 recarries Phi'^{e2f2} = Phi2 + lifts with
> the same Y-change on lift parts and a terminal Phi2-part
> (coordinate j+1, Y-change −e2f2). Every step's Y-change is
> <= −e2(f2 − t*) <= −e2 < 0 since s <= t* < f2. Secondary
> extraction inside a tail factor would add a second Phi'
> (weight >= THETA + delta: out of the layer) except when the tail
> step was weight-exact — and then it is still a k=1 branch counted
> above with the same Y-bookkeeping (+1 total from its one
> extraction). Tail-only routes: identical in the two reads (the
> shadow's mod-Phi' reduction keeps exactly the tail route),
> difference zero. ∎(a)
> (b) The certificate slot has Y-exponent 2e2t* + 1 = B* + 1 with
> B* = 2e2t* the MAXIMAL Y-exponent among pair terms (t + t' <=
> 2t*), attained only by (t,t') = (t*,t*) (t, t' <= t* forces
> equality). A height-THETA branch reaching Y-exponent B* + 1
> starts at pair Y-exponent e2(t+t') and reaches e2(t+t') + 1 −
> (nonneg. multiple of the positive step deficits) <= B* + 1, with
> equality iff zero steps and t + t' = 2t*: the (t*,t*) direct
> branch alone. Its digit: the pair coefficient (chat_{t*})^2
> (multinomial coefficient 1: the diagonal), times
> nhat_{t*}^2 = pi^{2a_{t*}} x^{2i_{t*}}, one extraction
> coefficient 1 (I = 2i_{t*} < 2D': the single x^{D'}-rewrite,
> Phi'-branch coefficient exactly 1), times the coherent
> normalizer's wrap unit. A product of units in K2^x: nonzero — no
> binomial coefficient, no characteristic condition, no zero
> divisors. Coordinate/height: weight 2E2 + delta at coordinate j*
> reads at coefficient height 2E2 + delta − j*E2 = THETA_{j*}. The
> x-slot a* = 2i_{t*} − D' < D' and no other height-THETA branch
> lands at (a*, Y^{B*+1}) by the uniqueness just shown (branches
> at the same Y-exponent but other x-slots differ in position, not
> height). ∎(b)
> (c) With no overflowing pair, every product of grid monomials in
> the expansion of Phi2^2 keeps x-degree < D' (pair x-degrees
> i_t + i_{t'} < D'; k=1 terms i_t < D'; the leading term x-free),
> so dev(Phi2^2) = K2(x,Y)^2 with in-grid coefficients and the
> R-division of F by K2 is the literal square: Ĝ_2 = 1, Ĝ_1 = Ĝ_0
> = 0 = ShC_j = C_j. ∎(c)
> (d) is a construction + machine adjudication, not a theorem:
> S4's FAM-E rows. ∎
>
> **Consequences for the geography (GENTOW-3's trichotomy is
> really a QUADRICHOTOMY at mu2 = 2).** Per genre: (1) x-free ⟹
> faithful at every height (GENTOW-3(iii)); (2) 2i_{t*} >= D' ⟹
> the floor THETA is attained by the key power itself — the
> divergence is generic at leaf depth (GENTOW-3(iv), now proved,
> no per-genre certificate left); (3) non-x-free with some
> overflowing pair but 2i_{t*} < D': attainment content exists at
> the maximal overflowing pair's slots but its digit is the
> DISPLAYED pair sum Sum_{t+t'=s, i_t+i_{t'}=I} m_{tt'} chat_t
> chat_{t'}·(units) (m_{tt'} = 2 − delta_{tt'}) — vanishing is a
> genre arithmetic condition (char-2 kills the off-diagonal m = 2
> terms one pi-depth down), NOT decided here beyond the display;
> (4) non-x-free, no overflowing pair ⟹ key-power shadow-EXACT
> and only entry-driven divergence remains (regime 3). At f2 = 1
> (T = {0}, t* = 0) regimes (2)/(3) collapse: attainment ⟺
> 2i_0 >= D', with digit chat_0^2 pi^{2a_0}·unit — the four
> GENTOW-3 battery families (A5/A7/B/C) all sit in regime (2),
> which is the ALGEBRAIC REASON the machine never saw the
> certificate vanish: their certificate digit is a unit square
> times pi^{2a}, and a field kills no unit.
>
> **Machine face of (b) at the four families (predicted, verified
> S4):** A5: (chat,a,i) = (1,2,1), digit 16Phi' (v=4) at (j*,b*) =
> (0,1), THETA_0 = 21. A7: (1,3,1) ⟹ 64Phi' at 31. C: (1,3,1) ⟹
> 64Phi' at 43 (E2 = 21). B (f2 = 2, t* = 1, chat_1 = 1, a_1 = 1,
> i_1 = 1, 2i_1 = 2 = D'): digit 4Phi' (v = 1·2 = 2) at coordinate
> j* = floor(3/2) = 1, slot b* = 1, THETA_1 = 7 — exactly the
> battery's ShC_1 = 4Phi' + 8x pin (the 8x is a downstream chain
> term at the same height, different slot; the certificate slot
> digit is the predicted 4).

## S4. MACHINE LEG (gentow6_checks.py — imports B1/B2 additively)

Runner: `verification/openmath/gentow6_checks.py`, importing
gentow1_checks (B1 families + slot algebra), gentow3_checks (the
shadow read), gentow4_checks (partial-side families, composed_read,
gp bridge) — none edited. Three legs mirror S1/S2/S3; predictions
P-1…P-9 + four teeth are preregistered in the runner docstring
(sealed at commit 1 with the pre-seal smoke DISCLOSED there: one
wiring finding — the unperturbed B2-reproduction row P5R.r2m1 drew
sib_block = the simple key exactly, so the composed read PEELs;
fix = the same height-46 perturbation as the constructed rows).

* **LEG-1 (S1's tie).** FAM-P5 geography (Q3, side [0,6] slope 5/2,
  residual deg 3): constructed product rows realize multiplicity
  profiles (m_{T-1}, m_{T-2}) ∈ {(1,2),(2,1),(0,3),(3,0)} — the
  (1,2)/(0,3)/(3,0) shapes are NEW (B2 only had (1,2)-transpose);
  per row, per class: m_r measured by res_factor on the level-1
  side digits vs mu2*(r) measured by composed_read at the class
  key; PARI decorrelated leg: nodev6 class-degree sums =
  D2·m_r (the deg display of LEMMA GENTOW-6.1), poldisc ≠ 0;
  (1,2)-profile rows fully decided, sigma = PARI sig1.
* **LEG-2 (S2's block layer).** On non-perturbed product rows the
  block factor f_S is known EXACTLY (coprime-class product):
  check LEMMA GENTOW-6.2's display (single side slope 5/2 to
  (M_C, 0), residual = psi2^{mu2*} monic via res_factor), COR
  GENTOW-6.2C(a)(c) budget + node floors at (mu2*, E2) incl.
  the RAM-anchor sharpness p_0^S = mu2*·E2 + 1, and COR 6.2C(d)'s
  projection p_j(f) − c_g = p_j(f_S) on the >T2 initial hull.
* **LEG-3 (S3's certificate).** Self-shadow of Phi2^2 at SEVEN
  cert rows — B1's A5/A7/B/C plus NEW genres GEN-R2X (e1 = 3,
  u2 = 11: first e1 = 3 certificate, a* = 1), GEN-P3/GEN-P3b
  (p = 3: first odd-p certificates, killing any char-2-luck
  reading): slot (a*,b*) of ShC_{j*} nonzero with v = 2a_{t*},
  height = THETA_{j*} = the pin. Regime-4 rows: FAM-E
  ((3,1,4;1)/Q2, u2 = 7, i_0 = 1, no overflowing pair):
  self-shadow ≡ 0 (THEOREM 6.3(c)); E-ENTRY row f_E = Phi2² +
  4x²·Phi2 + 16·Phi' (entry digit with a + i_0 = 3 ≥ D'): honest
  tRAM(31) = PARI, shadow diverges at 31 ≥ THETA_0 = 29 and flips
  the label (hand-traced pre-seal: the overflow's Phi'-kill
  exactly cancels the C_0 digit — shadow DRAIN) — THEOREM 6.3(d)'s
  witness. Teeth: T-TIE-CONST (mu2* ≡ 2 mutant), T-CERT-V
  (valuation off-by-one), T-ODDP (p = 2-only mutant), T-SHEXACT
  (regime-4 ⟹ member-faithful over-claim).

**RESULTS (commit 2): PENDING — full run after the seal.**

## S5. HONEST RESIDUE + GRADE BOX — TBD
