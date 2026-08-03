#!/usr/bin/env python3
"""tr3s4_check.py — the TR3-S4 preregistered falsifier family (2026-08-08).

UNIT UNDER TEST: lean/notes/openmath/TR3S4_2026-08-08.md — TR-3'-GEN at ORDER 3
on the e0 = 1, e1 >= 2, e2 = 1 stratum, the COMPOSED TWISTED identity: under
{sigma0, sigma1, sigma2} and the normalized-l convention (H-l), with the
ordinate identity supplied by Lemma HV3-E2 (v3 = w2, derived in-note),

    (coeff)  sigma2( C^F3_j ) == z2^(theta2*s_j) * c^G3_{s_j}  at every slot
             (abscissa s_j = j at e2 = 1; support equal),
    (form)   sigma2( R^F_3(f) )(y) == z2^(theta2*s0(f)) * R_lambda3(f)(z2^theta2 * y),
    theta2 = l1*g1*gamma2,

for every nonzero f, plus the S6.2 display lemmas (KEY0-LIFT: the GMN-lawful
level-3 key class is the theta2-twisted psi2 class, divergence criterion in
BOTH the class and literal forms; ORD-INV-LIFT: matched-label ord transport)
and the S3 Lemma HV3-E2 (two-way v3).

WHY A NEW FAMILY (beyond strata3e2_probe, which measured (TWIST-3) 0/1,656 at
seed 20260818): this family tests the COMPOSED identity END-TO-END and the
note's route as separate falsifiable rows, on FRESH draws (seed 20260819) over
a FRESH OFF-ROSTER tower roster (no row equals a probe row):
  * a FRESH FGMN pipeline (R2w_at below at STRIDE e1, reading at ARBITRARY
    integer weights; fresh_R3 at i = 3): the probe's Tower3.R3w HARD-CODES
    off-line slot coefficients to zero; here every slot coefficient (on- AND
    off-line) is COMPUTED, so Lemma Z2-e2 (off-line vanishing) becomes a
    tested prediction instead of an implementation assumption;
  * the two-form is checked on SIDE READS as LISTS (Def 3.18 j0 law + length
    + nonzero ends + the elementwise TWISTED tie side[k] ==
    z2^(theta2*(s+k)) * gco[k]);
  * the route steps are separate rows (RI kernels / RII A-GEN-3 inner
    TR3-S1 + m0 / RIII the Lemma EXP-3 INTEGER identity + t2 integrality +
    its field form / RIV recomposition from LEVEL-2 GMN data only);
  * the HV row is Lemma HV3-E2's face: v3 computed TWO WAYS — (a) the
    geometric (E4)-min with exact fractions (e1 * min_i{ w1(a_i) +
    i*(w1(Phi1) + h1/e1) }, Fraction arithmetic) and (b) the MacLane
    operator w2 — plus the ordinate expansion w2(A*Phi2^i) == w2(A) +
    i*w2(Phi2) on both legs;
  * the K/O rows seal the S6.2 displays INCLUDING the two divergence-
    criterion forms (the probe's sole RED was a sealed display clause
    conflating them — both forms are preregistered predictions here);
  * a PRESCRIBED-VALUE family (W): f is CONSTRUCTED to have FGMN slot
    values v_j fixed a priori; BOTH pipelines must return their predicted
    lists (fresh side: the v-list; GMN side: z2^(-theta2*s_j)*v_j) — an
    end-to-end test against a two-sided a-priori prediction; half the
    draws add sub-line noise; holes force j0 > 0 corners.

INDEPENDENCE PERIMETER (stated exactly).  This harness IMPORTS from
strata3_probe: the Tower3 object (levels 0-2 = N-1's Tower verbatim; level-3
layer Phi3/eps2/realize2/w3) and the GMN side gmn2/gmn3 (fresh implementations
of Defs 2.19-2.21 at r = 2, 3; normalized l hard-coded — the (H-l) hypothesis,
so this family CANNOT falsify the normalization choice; gmn3's ordinate
u_i = w2 + i*w2(Phi2) hard-codes the HV3-E2 READING — the HV row tests that
reading against the geometric (E4)-min, which is the decorrelated leg).
FRESH here: the seed, every draw, the roster, the FGMN pipeline
R2w_at/fresh_R3 (cross-validated against the probe operators in rows XV/Z2
and used for every E2E row), the route decomposition, the W prescription, the
HV geometric leg.  Shared inputs carry their external legs: N-1's
T0/T11/P11/P12 for levels 0-2; this run RE-FIRES the CERT legs per tower
(G.T1_T2/T5/T11 + strata3_probe.cert3_pari on Z_p rows).  sigma2 = identity
of the shared concrete K2 model (the sigma-content is the note's S2
mathematics, not testable numerics).  The author of this script also wrote
the note — NO model diversity here; per the pass-7 F2c standing rule the
acceptance arc REQUIRES a verifier-owned from-note implementation on
off-roster instances (displayed as the acceptance obligation, note S8.4).

DETERMINISTIC: random.seed(20260819) (fresh; 20260808/12/15/16/17/18 used by
the parents).  EXACT arithmetic only.

FRESH ROSTER (all e0 = 1, e2 = 1, e1 in {2,3}; triples (e_j,h_j,g_j); NO row
equals a strata3e2_probe row R2A-R2F; deg Phi3 = d0*g0*g1*g2*e1 <= 12):
  S4A (1; 1,1,2; 2,1,2; 1,1,1)  e1=2; g1=2; g2=1 corner        degPhi3=8
  S4B (1; 1,2,1; 2,1,2; 1,1,2)  g0=1 corner (K1=K0); h0=2      degPhi3=8
  S4C (2; 1,1,1; 3,1,2; 1,2,1)  d0=2; e1=3; h2=2; g2=1 corner  degPhi3=12
  S4D (1; 1,1,1; 3,2,2; 1,1,2)  e1=3,h1=2: l1=2, l1p=-1        degPhi3=12
over {Z_2, Z_3, F_2[[t]], F_3[[t]]} = 16 towers.
DESIGN TABLE (disclosed pre-seal; tower constants ONLY — theta2, ord(z2),
visibility; computed from the tower data, NO CF/cG comparison run pre-seal):
  S4A: theta2=10  p=2: ord 5 BLIND | p=3: ord 5 BLIND   (both ring kinds)
  S4B: theta2=10  p=2: ord 3 VIS   | p=3: ord 4 VIS
  S4C: theta2=8   p=2: ord 5 VIS   | p=3: ord 5 VIS
  S4D: theta2=20  p=2: ord 3 VIS   | p=3: ord 8 VIS
i.e. 12/16 towers twist-visible; the 4 blind = S4A everywhere (designed
degenerate controls, where the law degenerates to IDENT-3).

================ PREREGISTERED PREDICTIONS (sealed BEFORE the run) ===========
E2A  per-abscissa composed TWISTED identity, fresh FGMN pipeline vs gmn3:
     CF3_j == z2^(theta2*j) * cG3_j at EVERY abscissa of the union range
     (both zero off-line/off-window), support == the GMN on-line set.
     PREDICTED: 0.  [THE LAW]
E2B  the assembled two-form on side reads: first-nonzero index j0 == s0(f),
     length d+1, ends nonzero, and side[k] == z2^(theta2*(s+k)) * gco[k]
     elementwise.  PREDICTED: 0.
RI   kernel row (note S3 Lemma KER-13): the level-3 eq-(12) split has
     s == 0 and l2 == 0; per nonzero inner digit the level-1 split has
     s == 0, l0 == 0, and eps1 == 1; level-2 slot weights integral
     ((SLOT-2') congruence).  PREDICTED: 0.
RII  inner identity row (note S4 Lemma A-GEN-3 = accepted TR3-S1 on the
     digit): at every on-line slot, the fresh stride-e1 level-2 read list
     of the digit A == the gmn2 coefficient list under the slot/abscissa
     re-indexing m = m0 + k, with zeros below m0 and beyond, first nonzero
     == m0 = (s2(A) - s(gamma_j))/e1 in Z_{>=0}.  PREDICTED: 0.
RIII Lemma EXP-3 row: t2 := (s2(A) - l1*u_j)/e1 integral, AND the INTEGER
     identity (l1p*s - l1*u') + m0 == t2 + theta2*j at every on-line slot
     ((s,u') = eq12(gamma_j, e1, h1)), AND the field form
     eps2(gamma_j) * z2^(m0 - t2) == z2^(theta2*j).  PREDICTED: 0.
RIV  recomposition row (the chain's right side from LEVEL-2 GMN data only):
     CF3_j == z2^(t2 + theta2*j) * sum_k c^G2_k(A) z2^k, rebuilt from
     gmn2's list (NOT via gmn3).  PREDICTED: 0.
Z2   off-line vanishing (note S4 Lemma Z2-e2) + own-weight cross-validation:
     (z-i) for drawn nonzero A and beta = w2(A) - k (k = 1..3): R2w_at(A,
     beta) is ALL ZERO; (z-ii) R2w_at(A, w2(A)) == Tower.R2w(A) elementwise
     (fresh stride-e1 transcription vs the N-1-certified operator).
     PREDICTED: 0.
HV   Lemma HV3-E2 two-way row: (h-i) v3geo(P) := e1 * min_i{ Fr(w1(a_i)) +
     i*(Fr(w1(Phi1)) + Fr(h1,e1)) } over the Phi1-development (exact
     Fractions) == w2(P) for drawn P; (h-ii) ordinate expansion:
     w2(A*Phi2^i) == w2(A) + i*w2(Phi2) AND v3geo(A*Phi2^i) == the same,
     for drawn A, i in {1,2}.  PREDICTED: 0.
XV   fresh-vs-probe FGMN cross-validation: fresh_R3(f) == Tower3.R3w(f)
     elementwise on the shared slot range.  PREDICTED: 0.
W    prescribed-value two-sided end-to-end: constructed f with FGMN slot
     values v_j fixed a priori (holes allowed, half the draws
     noise-dressed): fresh side list == the v-prescription from the first
     prescribed slot, j0 == that slot, AND gmn3 list == the
     z2^(-theta2*s_j)-twisted prescription with s == that slot.
     PREDICTED: 0 violations, 0 construction failures.
K    key rows (note S6.2 step 0 + probe V4/P4'): (k-i) fresh side read of
     Phi3 == psi2 with j0 = 0 (FGMN-normalized key datum); (k-ii)
     gmn3(Phi3): s0 = 0, d = g2, gco[k] == z2^(-theta2*k) * psi2_k for all
     k (the theta2-twisted class, P4' primary); (k-iii) CLASS divergence
     (monicized z2^(theta2*g2)*gco != psi2) iff some k < g2 has psi2_k != 0
     and z2^(theta2*(g2-k)) != 1; (k-iv) LITERAL divergence (gco != psi2 as
     lists) iff some k <= g2 has psi2_k != 0 and z2^(theta2*k) != 1.
     PREDICTED: 0.
O    matched-label ord transport (ORD-INV-LIFT): with kG the monic twisted
     key (kG_k = z2^(theta2*(g2-k)) * psi2_k), ord_{kG}(gmn3 list) ==
     ord_{psi2}(fresh side list) on every E2E sample; histogram REPORTED,
     must contain some ord >= 1.  Naive shared-psi2 pairing mismatches
     REPORTED (no prediction).  PREDICTED: 0 mismatches (matched labels).
CERT external/integrity legs re-fired per tower: G.T1_T2(nf=4) + G.T5 +
     G.T11(PARI) on the order-2 substate (e1 >= 2 rows); cert3_pari
     (order-3 PARI leg, Z_p rows: Phi3 irreducible/Q_p, unique prime,
     (e,f) = (e1, d0*g0*g1*g2) — RAMIFIED keys); gmn-side P0 integrity
     (strata3_probe.VIOL stays empty).  PREDICTED: 0.
METERS (teeth; all must fire as stated):
     m0pos:    on-line slots with m0 > 0                       — pred > 0
     t2nz:     on-line slots with t2 != 0                      — pred > 0
     epsnz:    on-line slots with eps2(gamma_j) != 1           — pred > 0
     vis:      twist-visible slots (z2^(theta2*j) != 1)        — pred > 0
     identkill: naive IDENT-3 refuted at visible slots         — pred == vis
     j0pos:    samples with j0 > 0                             — pred > 0
     noff:     off-line slots carrying a NONZERO digit         — pred > 0
     noisy/holes: W draws dressed/holed                        — pred > 0
     wfail:    W construction failures                         — pred == 0
     ordhi:    ord histogram contains ord >= 1                 — pred yes
     naive:    naive shared-psi2 ord mismatches                — REPORT ONLY
EXIT: 0 iff every row at its predicted count and all meters fire.
Output: tee to tr3s4_check_output.txt; JSON tr3s4_check_results.json.
"""
import random, sys, os, time, json
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_ord, eq12, INF)
import strata3_probe as S3P
from strata3_probe import Tower3, gmn2, gmn3, cert3_pari

VIOL = []
COUNTS = {}
ORD_HIST = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

ROSTER4 = [
    # (tag, d0, (e0,h0,g0), (e1,h1,g1), (e2,h2,g2))
    ("S4A", 1, (1,1,2), (2,1,2), (1,1,1)),
    ("S4B", 1, (1,2,1), (2,1,2), (1,1,2)),
    ("S4C", 2, (1,1,1), (3,1,2), (1,2,1)),
    ("S4D", 1, (1,1,1), (3,2,2), (1,1,2)),
]

class Meters:
    def __init__(self):
        self.m0pos = 0; self.t2nz = 0; self.epsnz = 0
        self.vis = 0; self.identkill = 0
        self.j0pos = 0; self.noff = 0
        self.noisy = 0; self.holes = 0; self.wfail = 0
        self.naive = 0

def theta2_of(T3):
    return T3.T.l1 * T3.T.g1 * T3.T.gamma2

# ------------- the FRESH FGMN pipeline (Def 3.16 at i = 2 stride e1; i = 3) ---
def R2w_at(T, A, beta):
    """FRESH level-2 weight read of nonzero A at ARBITRARY integer weight
    beta <= w2(A), Def 3.16 at i = 2 at STRIDE e1 (e0 = 1): forced abscissa
    progression s(beta) + m*e1, slot weights (SLOT-2') beta_m =
    (beta - (s+m*e1)*gamma2)/e1; eps1 == 1 (level-1 kernel, checked).
    Slot-indexed output (m-th entry = slot m).  Computes off-line reads
    honestly (Lemma Z2-e2's face)."""
    K1 = T.K1
    d1 = dev(T.R, A, T.Phi1)
    s, u = eq12(beta, T.e1, T.h1)
    out = []
    jmax = (len(d1)-1 - s)//T.e1 if len(d1)-1 >= s else -1
    for m in range(jmax + 1):
        sm = s + m*T.e1
        a = d1[sm]
        num = beta - sm*T.gamma2
        note("RI")
        if num % T.e1 != 0:
            viol("RI", T.tag, f"(SLOT-2') weight not integral at beta={beta}, "
                              f"abscissa {sm}")
            out.append(K1["zero"]); continue
        bm = num // T.e1
        if not a:
            out.append(K1["zero"]); continue
        s1v, _u1v = eq12(bm, T.e0, T.h0)
        note("RI")
        if s1v != 0 or T.l0 != 0:
            viol("RI", T.tag, f"level-1 kernel: s({bm})={s1v}, l0={T.l0}")
        e1v = T.eps1(bm)
        note("RI")
        if e1v != K1["one"]:
            viol("RI", T.tag, f"eps1({bm}) != 1 (level-1 kernel)")
        out.append(K1["mul"](e1v, T.R1w_at_z1(a, bm)))
    return out

def evalK2(T3, lst):
    K2, K1 = T3.K2, T3.T.K1
    v = K2["zero"]; zp = K2["one"]
    for c in lst:
        if not K1["isz"](c):
            v = K2["add"](v, K2["mul"](K2["embed"](c), zp))
        zp = K2["mul"](zp, T3.z2)
    return v

def fresh_R3(T3, f, M):
    """FRESH level-3 weight read (Def 3.16 at i = 3, e2 = 1): every slot
    coefficient computed as eps2(gamma_j) * R_{2,gamma_j}(A_j)(z2) via
    R2w_at — including off-line slots (predicted 0 by Lemma Z2-e2, checked
    downstream in E2A's support row)."""
    T, K2 = T3.T, T3.K2
    d2 = dev(T3.R, f, T.Phi2)
    vals = [T.w2(A) if A else INF for A in d2]
    assert any(v < INF for v in vals), "fresh_R3 of 0"
    g = min(T3.e2*vals[j] + j*T3.gamma3 for j in range(len(d2))
            if vals[j] < INF)
    s3, u3 = eq12(g, T3.e2, T3.h2)
    note("RI")
    if s3 != 0 or T3.l2 != 0:
        viol("RI", T3.tag, f"level-3 kernel: s(gamma)={s3}, l2={T3.l2}")
    coeffs = []
    for j in range(len(d2)):
        A = d2[j]
        gj = g - j*T3.gamma3
        if not A:
            coeffs.append(K2["zero"]); continue
        if vals[j] > gj:
            M.noff += 1
        coeffs.append(K2["mul"](T3.eps2(gj), evalK2(T3, R2w_at(T, A, gj))))
    return coeffs, g, d2, vals

# -------------------------------- HV row (S3) ---------------------------------
def v3geo(T, P):
    """Geometric (E4)-min leg of Lemma HV3-E2, exact Fractions:
    e1 * min_i{ w1(a_i) + i*(w1(Phi1) + h1/e1) } over the Phi1-development."""
    d1 = dev(T.R, P, T.Phi1)
    best = None
    lam = Fraction(T.h1, T.e1)
    for i, a in enumerate(d1):
        if not a: continue
        val = Fraction(T.w1(a)) + i*(Fraction(T.w1Phi1) + lam)
        if best is None or val < best: best = val
    assert best is not None, "v3geo of 0"
    v = T.e1 * best
    return v

def hv_row(T3, ndraws=8):
    T, R = T3.T, T3.R
    for _ in range(ndraws):
        P = T.rand_opoly(random.randrange(0, int(1.6*T.degPhi2) + 2), pimax=4)
        if not P: P = [R["pi_pow"](random.randrange(0, 3))]
        note("HV")
        vg = v3geo(T, P)
        if vg != T.w2(P):
            viol("HV", T3.tag, f"two-way v3 fails: geo {vg} != w2 {T.w2(P)}")
    for i in (1, 2):
        A = T.rand_opoly(random.randrange(0, T.degPhi2), pimax=3)
        if not A: A = [R["one"]]
        prod = pmul(R, A, ppow(R, T.Phi2, i))
        note("HV")
        lhs_op = T.w2(prod)
        lhs_geo = v3geo(T, prod)
        rhs = T.w2(A) + i*T.w2Phi2
        if lhs_op != rhs or lhs_geo != rhs:
            viol("HV", T3.tag, f"ordinate expansion fails at i={i}: "
                               f"op {lhs_op} geo {lhs_geo} vs {rhs}")

# ------------------------------- the E2E check --------------------------------
def check_sample(T3, f, shape, M):
    T, K2, K1 = T3.T, T3.K2, T3.T.K1
    th2 = theta2_of(T3)
    coeffs, g, d2, vals = fresh_R3(T3, f, M)
    s, d, gco, on, s2map, r2map, uvec = gmn3(T3, f)
    # E2A per-abscissa composed twisted identity + support
    jmax = max(len(coeffs) - 1, s + d)
    for j in range(jmax + 1):
        CF = coeffs[j] if j < len(coeffs) else K2["zero"]
        cG = gco[j - s] if s <= j <= s + d else K2["zero"]
        note("E2A")
        twist = K2["pow"](T3.z2, th2*j)
        if CF != K2["mul"](twist, cG):
            viol("E2A", T3.tag, f"[{shape}] TWISTED identity FAILS at "
                                f"abscissa {j}: CF={CF} cG={cG} theta2={th2}")
            return
        if (not K2["isz"](CF)) != (j in on):
            viol("E2A", T3.tag, f"[{shape}] support mismatch at {j}")
            return
        if K2["isz"](CF):
            continue
        if twist != K2["one"]:
            M.vis += 1
            if CF != cG: M.identkill += 1
        # route rows at on-line slots
        A = d2[j]
        gj = g - j*T3.gamma3
        sfa, ufa = eq12(gj, T.e1, T.h1)
        e2v = T3.eps2(gj)
        if e2v != K2["one"]: M.epsnz += 1
        innr = R2w_at(T, A, gj)
        s2G, d2G, co2G, on2G, _, _ = gmn2(T, A, tag=T3.tag)
        note("RII")
        if (s2G - sfa) % T.e1 != 0 or s2G < sfa:
            viol("RII", T3.tag, f"[{shape}] m0 not in Z>=0 at slot {j}: "
                                f"s2={s2G}, s(gamma_j)={sfa}")
            return
        m0 = (s2G - sfa)//T.e1
        mtop = max(len(innr) - 1, m0 + d2G)
        first_nz = None
        for m in range(mtop + 1):
            c2F = innr[m] if m < len(innr) else K1["zero"]
            c2G = co2G[m - m0] if m0 <= m <= m0 + d2G else K1["zero"]
            if c2F != c2G:
                viol("RII", T3.tag, f"[{shape}] inner TR3-S1 identity fails "
                                    f"at slot-index {m} (outer slot {j})")
                return
            if first_nz is None and not K1["isz"](c2F):
                first_nz = m
        if first_nz != m0:
            viol("RII", T3.tag, f"[{shape}] m0 law fails: first nonzero "
                                f"{first_nz} != m0 = {m0}")
            return
        if m0 > 0: M.m0pos += 1
        note("RIII")
        num = s2G - T.l1*uvec[j]
        if num % T.e1 != 0:
            viol("RIII", T3.tag, f"[{shape}] t2 not integral at slot {j}")
            return
        t2 = num // T.e1
        if t2 != 0: M.t2nz += 1
        if (T.l1p*sfa - T.l1*ufa) + m0 != t2 + th2*j:
            viol("RIII", T3.tag, f"[{shape}] EXP-3 integer identity fails at "
                 f"slot {j}: ({T.l1p}*{sfa}-{T.l1}*{ufa})+{m0} != {t2}+{th2}*{j}")
            return
        if K2["mul"](e2v, K2["pow"](T3.z2, m0 - t2)) != \
           K2["pow"](T3.z2, th2*j):
            viol("RIII", T3.tag, f"[{shape}] EXP-3 field form fails at slot {j}")
            return
        note("RIV")
        rl2 = K2["zero"]; zp = K2["one"]
        for cc in co2G:
            if not K1["isz"](cc):
                rl2 = K2["add"](rl2, K2["mul"](K2["embed"](cc), zp))
            zp = K2["mul"](zp, T3.z2)
        pred = K2["mul"](K2["pow"](T3.z2, t2 + th2*j), rl2)
        if pred != coeffs[j]:
            viol("RIV", T3.tag, f"[{shape}] recomposition (level-2 GMN data) "
                                f"fails at slot {j}")
            return
    # E2B side two-form as lists (twisted elementwise tie)
    note("E2B")
    j0 = 0
    while j0 < len(coeffs) and K2["isz"](coeffs[j0]): j0 += 1
    side = fp_norm(K2, coeffs[j0:])
    glist = fp_norm(K2, gco)
    ok = (j0 == s and len(side) == d + 1 and len(glist) == d + 1
          and side and not K2["isz"](side[0]) and not K2["isz"](side[-1]))
    if ok:
        for k in range(d + 1):
            if side[k] != K2["mul"](K2["pow"](T3.z2, th2*(s + k)), glist[k]):
                ok = False; break
    if not ok:
        viol("E2B", T3.tag, f"[{shape}] two-form: j0={j0} vs s0={s}, "
                            f"len={len(side)} vs d+1={d+1}")
        return
    if j0 > 0: M.j0pos += 1
    # XV cross-validation vs the probe pipeline
    note("XV")
    pco = T3.R3w(f)
    top = max(len(coeffs), len(pco))
    for j in range(top):
        a = coeffs[j] if j < len(coeffs) else K2["zero"]
        b = pco[j] if j < len(pco) else K2["zero"]
        if a != b:
            viol("XV", T3.tag, f"[{shape}] fresh vs probe FGMN differ at "
                               f"slot {j}")
            return
    # O matched-label ord transport (+ naive report)
    note("O")
    kG = [K2["mul"](K2["pow"](T3.z2, th2*(T3.g2 - k)), T3.psi2[k])
          for k in range(len(T3.psi2))]
    o1 = fp_ord(K2, glist, kG)
    o2 = fp_ord(K2, side, fp_norm(K2, T3.psi2))
    ORD_HIST[o2] = ORD_HIST.get(o2, 0) + 1
    if o1 != o2:
        viol("O", T3.tag, f"[{shape}] matched-label ord: GMN(kG) {o1} != "
                          f"FGMN(psi2) {o2}")
    if fp_ord(K2, glist, fp_norm(K2, T3.psi2)) != o2:
        M.naive += 1

# ------------------------- Z2 constructed off-line row ------------------------
def z2_row(T3, ndraws=6):
    T, K1 = T3.T, T3.T.K1
    for _ in range(ndraws):
        A = T.rand_opoly(random.randrange(0, T.degPhi2), pimax=3)
        if not A: A = [T.R["pi_pow"](random.randrange(0, 3))]
        b = T.w2(A)
        note("Z2")
        mine = R2w_at(T, A, b)
        ref = T.R2w(A)
        top = max(len(mine), len(ref))
        for m in range(top):
            x = mine[m] if m < len(mine) else K1["zero"]
            y = ref[m] if m < len(ref) else K1["zero"]
            if x != y:
                viol("Z2", T3.tag, f"own-weight cross-validation fails at "
                                   f"slot {m}")
                break
        for k in range(1, 4):
            note("Z2")
            lst = R2w_at(T, A, b - k)
            if any(not K1["isz"](c) for c in lst):
                viol("Z2", T3.tag, f"Lemma Z2-e2 fails: R_(2,{b-k}) of A with "
                                   f"w2={b} is nonzero")

# ---------------------- W prescribed-value construction -----------------------
def w_row(T3, M, ndraws=5):
    T, R, K2 = T3.T, T3.R, T3.K2
    th2 = theta2_of(T3)
    for _ in range(ndraws):
        nslots = random.choice([2, 3, 4])
        base = T3.gamma3*(nslots + 2) + T.g1*T.gamma2 + T.g0*T.h0 + 4
        vv = [None if random.random() < 0.3 else T3.rand_K2(nonzero=True)
              for _ in range(nslots)]
        if vv[-1] is None: vv[-1] = T3.rand_K2(nonzero=True)
        has_hole = any(t is None for t in vv)
        if has_hole: M.holes += 1
        f = []
        try:
            for j, v in enumerate(vv):
                if v is None: continue
                gj = base - j*T3.gamma3
                tau = K2["mul"](K2["inv"](T3.eps2(gj)), v)
                f = padd(R, f, pmul(R, T3.realize2(tau, gj),
                                    ppow(R, T.Phi2, j)))
        except AssertionError as exc:
            M.wfail += 1
            viol("W", T3.tag, f"construction failure: {exc}")
            continue
        noisy = random.random() < 0.5
        if noisy:
            M.noisy += 1
            noise = T.rand_opoly(random.randrange(0, T.degPhi2 + 3), pimax=2)
            f = padd(R, f, pscal(R, R["pi_pow"](base + 2), noise))
        jstar = next(j for j, v in enumerate(vv) if v is not None)
        predF = [K2["zero"] if v is None else v for v in vv[jstar:]]
        predG = [K2["zero"] if v is None else
                 K2["mul"](K2["pow"](T3.z2, -th2*(jstar + k)), v)
                 for k, v in enumerate(vv[jstar:])]
        note("W")
        coeffs, g, d2, vals = fresh_R3(T3, f, M)
        j0 = 0
        while j0 < len(coeffs) and K2["isz"](coeffs[j0]): j0 += 1
        side = fp_norm(K2, coeffs[j0:])
        s, d, gco, on, _, _, _ = gmn3(T3, f)
        okF = (g == base and j0 == jstar and side == fp_norm(K2, predF))
        okG = (s == jstar and fp_norm(K2, gco) == fp_norm(K2, predG))
        if not (okF and okG):
            viol("W", T3.tag, f"prescribed two-sided E2E fails (noisy={noisy}, "
                              f"holes={has_hole}): okF={okF} okG={okG} "
                              f"j0={j0}/{jstar} s={s}")

# ------------------------------ K key rows ------------------------------------
def k_row(T3, M):
    T, K2 = T3.T, T3.K2
    th2 = theta2_of(T3)
    psi2n = fp_norm(K2, T3.psi2)
    # (k-i) FGMN-normalized key datum (probe V4 face)
    note("K")
    coeffs, g, d2, vals = fresh_R3(T3, T3.Phi3, M)
    j0 = 0
    while j0 < len(coeffs) and K2["isz"](coeffs[j0]): j0 += 1
    side = fp_norm(K2, coeffs[j0:])
    if j0 != 0 or side != psi2n:
        viol("K", T3.tag, f"(k-i) fresh side read of Phi3 != psi2 (j0={j0})")
    # (k-ii) the twisted class law (P4' primary)
    note("K")
    s, d, gco, on, _, _, _ = gmn3(T3, T3.Phi3)
    okii = (s == 0 and d == T3.g2)
    if okii:
        for k in range(T3.g2 + 1):
            want = K2["mul"](K2["pow"](T3.z2, -th2*k), T3.psi2[k])
            if gco[k] != want:
                okii = False; break
    if not okii:
        viol("K", T3.tag, f"(k-ii) gmn3(Phi3) != twisted psi2 class "
                          f"(s0={s}, d={d})")
    # (k-iii) CLASS divergence criterion (monic representatives)
    note("K")
    kG = [K2["mul"](K2["pow"](T3.z2, th2*(T3.g2 - k)), T3.psi2[k])
          for k in range(len(T3.psi2))]
    diverged = fp_norm(K2, kG) != psi2n
    crit = any((not K2["isz"](T3.psi2[k])) and
               K2["pow"](T3.z2, th2*(T3.g2 - k)) != K2["one"]
               for k in range(T3.g2))
    if diverged != crit:
        viol("K", T3.tag, f"(k-iii) class-divergence criterion mismatch: "
                          f"diverged={diverged} crit={crit}")
    # (k-iv) LITERAL divergence criterion (the P4'-secondary lesson, sealed)
    note("K")
    lit = fp_norm(K2, gco) != psi2n if okii else None
    litcrit = any((not K2["isz"](T3.psi2[k])) and
                  K2["pow"](T3.z2, th2*k) != K2["one"]
                  for k in range(T3.g2 + 1))
    if lit is not None and lit != litcrit:
        viol("K", T3.tag, f"(k-iv) literal-divergence criterion mismatch: "
                          f"lit={lit} crit={litcrit}")

# ----------------------------------- main -------------------------------------
def run_tower(T3, M, pari):
    T, R = T3.T, T3.R
    gv0 = len(G.VIOL); sv0 = len(S3P.VIOL)
    G.T1_T2(T, nf=4); G.T5(T); G.T11(T, pari)
    cert3_pari(T3, pari)
    note("CERT", (len(G.VIOL) - gv0) + (len(S3P.VIOL) - sv0) + 1)
    k_row(T3, M)
    z2_row(T3, ndraws=6)
    w_row(T3, M, ndraws=5)
    hv_row(T3, ndraws=8)
    for _ in range(10):
        f = T.rand_opoly(random.randrange(0, int(2.2*T3.degPhi3) + 1),
                         pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        check_sample(T3, f, "rand", M)
    for _ in range(4):
        check_sample(T3, T3.rand_structured3(random.choice([2, 3, 4])),
                     "struct", M)
    for _ in range(3):
        a = random.randrange(1, 4)
        h = T.rand_opoly(random.randrange(0, T.degPhi2 + 2), pimax=3)
        if not h: h = [R["one"]]
        check_sample(T3, pmul(R, ppow(R, T.Phi2, a), h), f"Phi2^{a}*g", M)
    for _ in range(3):
        a = random.randrange(1, 4)
        h = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not h: h = [R["one"]]
        check_sample(T3, pmul(R, ppow(R, T.Phi1, a), h), f"Phi1^{a}*g", M)
    for k in range(0, 3):
        check_sample(T3, [R["pi_pow"](k)], f"pi^{k}", M)
    for _ in range(2):
        mu = random.choice([1, 2])
        check_sample(T3, pmul(R, ppow(R, T3.Phi3, mu),
                              T3.rand_structured3(2)), f"Phi3^{mu}*Q", M)

def main():
    t0 = time.time()
    random.seed(20260819)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); PARI legs skipped "
              "-> CERT RED if predicted")
    M = Meters()
    configs = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    tower_recs = []
    for kind, p in configs:
        for tag, d0, r0, r1, r2 in ROSTER4:
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            run_tower(T3, M, pari)
            th2 = theta2_of(T3)
            zt = T3.K2["pow"](T3.z2, th2)
            tower_recs.append(dict(tower=full, d0=d0, r0=r0, r1=r1, r2=r2,
                                   theta2=th2, gamma2=T3.T.gamma2,
                                   gamma3=T3.gamma3, degPhi3=T3.degPhi3,
                                   visible=(zt != T3.K2["one"])))
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"viol={len(VIOL)} G={len(G.VIOL)} S3P={len(S3P.VIOL)}")
    print()
    print("=" * 78)
    print("TR3-S4 FALSIFIER — PREDICTED vs OBSERVED (violations; samples in "
          "parens)")
    print("=" * 78)
    fams = [
        ("E2A", "per-abscissa TWISTED identity + support     ", 0),
        ("E2B", "two-form as lists (twisted tie) + j0 law    ", 0),
        ("RI",  "kernels: lvl-1/3 dead, (SLOT-2') integral   ", 0),
        ("RII", "A-GEN-3: inner TR3-S1 + m0 law              ", 0),
        ("RIII","EXP-3 integer identity + t2 + field form    ", 0),
        ("RIV", "recomposition from level-2 GMN data         ", 0),
        ("Z2",  "off-line vanishing + own-weight cross-val   ", 0),
        ("HV",  "two-way v3 (geo Fractions vs w2) + ordinates", 0),
        ("XV",  "fresh vs probe FGMN pipeline                ", 0),
        ("W",   "prescribed two-sided values (noise/holes)   ", 0),
        ("K",   "key rows: V4 + P4' + both divergence forms  ", 0),
        ("O",   "matched-label ord transport (kG vs psi2)    ", 0),
    ]
    all_green = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:4} {desc:46} pred {pred}  obs {obs:5d} ({n:6d})  "
              f"{verdict}")
    certv = len(G.VIOL) + len(S3P.VIOL) + \
        sum(1 for v in VIOL if v[0] == "CERT")
    cv = "GREEN" if certv == 0 else "RED"
    if certv: all_green = False
    print(f"CERT external/integrity legs (G + S3P + local)     pred 0  "
          f"obs {certv:5d} ({COUNTS.get('CERT',0):6d})  {cv}")
    mrows = [("m0pos: on-line slots with m0 > 0", M.m0pos > 0, M.m0pos),
             ("t2nz: on-line slots with t2 != 0", M.t2nz > 0, M.t2nz),
             ("epsnz: slots with eps2 != 1 (revival live)", M.epsnz > 0,
              M.epsnz),
             ("vis: twist-visible slots", M.vis > 0, M.vis),
             ("identkill == vis (naive IDENT-3 refuted)",
              M.identkill == M.vis and M.vis > 0, M.identkill),
             ("j0pos: samples with j0 > 0", M.j0pos > 0, M.j0pos),
             ("noff: off-line nonzero-digit slots computed", M.noff > 0,
              M.noff),
             ("noisy: W draws noise-dressed", M.noisy > 0, M.noisy),
             ("holes: W draws with holes", M.holes > 0, M.holes),
             ("wfail: W construction failures == 0", M.wfail == 0, M.wfail)]
    for desc, ok, val in mrows:
        tag = "MATCH" if ok else "MISMATCH"
        if not ok: all_green = False
        print(f"METER {desc}: {val}  {tag}")
    hist = " ".join(f"{k}:{v}" for k, v in sorted(ORD_HIST.items()))
    ordhi = any(k >= 1 and v > 0 for k, v in ORD_HIST.items())
    if not ordhi: all_green = False
    print(f"METER ord histogram: {hist} (pred: some ord >= 1)  "
          f"{'MATCH' if ordhi else 'MISMATCH'}")
    print(f"METER naive shared-psi2 ord mismatches (REPORT ONLY): {M.naive}")
    vis_towers = sum(1 for r in tower_recs if r["visible"])
    print(f"DESIGN check: twist-visible towers {vis_towers}/16 "
          f"(disclosed table: 12/16)"
          f"  {'MATCH' if vis_towers == 12 else 'MISMATCH'}")
    if vis_towers != 12: all_green = False
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]: print("  ", v)
    if G.VIOL:
        print(f"{len(G.VIOL)} G VIOLATIONS (first 10):")
        for v in G.VIOL[:10]: print("  ", v)
    if S3P.VIOL:
        print(f"{len(S3P.VIOL)} S3P VIOLATIONS (first 10):")
        for v in S3P.VIOL[:10]: print("  ", v)
    total = sum(COUNTS.values())
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    verdict = all_green and not VIOL and not G.VIOL and not S3P.VIOL
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if verdict else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "tr3s4_check_results.json"), "w") as fh:
        json.dump(dict(seed=20260819,
                       violations=[list(v) for v in VIOL],
                       g_violations=[list(v) for v in G.VIOL],
                       s3p_violations=[list(v) for v in S3P.VIOL],
                       counts=COUNTS,
                       meters=dict(m0pos=M.m0pos, t2nz=M.t2nz, epsnz=M.epsnz,
                                   vis=M.vis, identkill=M.identkill,
                                   j0pos=M.j0pos, noff=M.noff, noisy=M.noisy,
                                   holes=M.holes, wfail=M.wfail,
                                   naive=M.naive),
                       ord_hist=ORD_HIST,
                       towers=tower_recs), fh, indent=1, default=str)
    return 0 if verdict else 1

if __name__ == "__main__":
    sys.exit(main())
