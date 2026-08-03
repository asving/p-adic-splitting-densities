#!/usr/bin/env python3
"""strata3_probe.py — DEPTH-3 STRATA PROBE (synthesis-6 queue #6; charter =
docs/SYNTHESIS_PASS6_2026-08-08.md F3(c): "deeper strata are NOT yet
finite-algebra — at order >= 3 the inner reads are marched operators with
their own eps-systems and the eps-recurrence can REVIVE even on e0 = 1
strata; next stratum candidate: ORDER 3, all-e_j = 1; entry per the [M]-row
protocol: a preregistered depth-3 probe MEASURING the composed
eps-recurrence; a compose unit only if a law returns exact").

THE PROBED STRATUM: order-3 towers with e0 = e1 = e2 = 1 (E3 = 1, totally
unramified reads) and MIXED residue growth g_j (several g_j >= 2), over the
four base rings {Z_2, Z_3, F_2[[t]], F_3[[t]]}.  The FGMN level-3 residual
operator (Def 3.16 one-step recursion, transcribed below) is compared
slot-by-slot against a FRESH GMN order-3 implementation (Defs 2.19-2.21 at
r = 3, the level-generic recursion quoted from the print at
/tmp/litunit/gmn.txt:1823-1906: c_i = z2^{t2(i)} * R_2(a_i)(z2),
t2(i) = (s2(a_i) - l1*u_i)/e1).

MACHINERY LINEAGE: grb_order2_check.py (N-1) Tower objects reused VERBATIM
for levels 0-2 (base rings, Phi0/Phi1/Phi2, K0/K1, R1w/R2w, eps1 reading C,
realize1) — those carry N-1's external pins (T0/T11/P11/P12 PARI) and are
re-certified per instance here (CERT2 = G.T1_T2/T5/T11 on the underlying
order-2 tower).  The level-3 layer (K2, eps2, R3w/R3s, realize2, Phi3) is
NEW, transcribed from the same printed Def 3.15/3.16 recursion one level up
(the transcription is validated INTERNALLY by V1-V5 multiplicativity /
carry / key-lift rows and EXTERNALLY by CERT3 = PARI factorpadic +
idealprimedec on the order-3 Z_p towers).  The GMN side (gmn1/gmn2/gmn3
below) is implemented FRESH from the printed Defs; it shares the Tower
object and w1/w2 consumed as v2/v3 (the pinned Def-2.5 identity v2 = w1 and
its displayed order-3 extension v3 = w2 — hypothesis (H-v3) below).

MATCHED-KEY DISCIPLINE (TR3S2 ORD-INV): both sides consume the SAME keys
Phi0/Phi1/Phi2 at every level.  On this stratum theta = l0*g0*h0 = 0 and
theta2 = l1*g1*gamma2 = 0, so the FGMN-normalized and GMN-lawful key classes
COINCIDE (every state is twist-INVISIBLE) — displayed and checked (P4).

DETERMINISTIC: random.seed(20260817) (fresh seed; 20260815/16 used by the
parents).  EXACT arithmetic only.  PARI fires on the Z_p rows (CERT2 T11 +
CERT3).

=========================== EPS TRANSCRIPTION =================================
Def 3.15 (corrected reading C, N-1's triple pin; the raw extraction's
floating prime is NOT consulted):  eps_i(alpha) = z_i^(l'_i s(alpha) -
l_i u(alpha)), (s,u) the eq-(12) split of alpha at FGMN read i = project
read i-1.  Project transcription used here:
    eps1(beta), beta in Gamma_1: split by (e0,h0), value z1^(l0p*s - l0*u)
      [grb_order2_check.Tower.eps1, reading C — reused verbatim];
    eps2(beta), beta in Gamma_2: split by (e1,h1), value z2^(l1p*s - l1*u)
      [NEW, the same formula one level up; z2 = root of psi1 in
      K2 = K1[z]/(psi1)].
Def 3.16 at i = 3:  R_{3,gamma}(f)_j = eps2(gamma_j) *
    R_{2,gamma_j}(A_{s_j})(z2),  s_j = s(gamma) + j*e2,
    gamma_j = (gamma - s_j*gamma3)/e2  (Lemma-RESCALE integer weights,
    gamma3 = e2*w2(Phi2) + h2) — the exact one-level-up mirror of the
    N-1-certified R2w.

ON THIS STRATUM (all e_j = 1): every eq-(12) split has s == 0 and every
l_j = 0, hence eps1 == eps2 == 1 IDENTICALLY under reading C.  The
extraction ambiguity at level 2 is ALIVE here nonetheless: reading P would
give eps2(beta) = z2^(l1*s - l1p*u) = z2^(-beta) != 1 — a slot-geometric
z2-character.  This probe therefore also DISCRIMINATES the Def-3.15 reading
at level 2 on PARI-certified towers (meter M1), which no previous unit did.

======================= PREREGISTERED CANDIDATE LAWS ==========================
(sealed BEFORE the run; the derivation below is itself part of what the run
tests — the strata_probe A3 discipline)

CANDIDATE 1 (IDENT-3, the TR3-S1 sigma-compose shape composed across both
levels — THE PREDICTED LAW).  For every nonzero f, every on-line slot j of
the level-3 read:
    (IDENT-3)   C^F3_j = c^G3_{s_j}     (identity; discrepancy == 1).
DERIVATION (fixed pre-run).  All e_j = 1 gives eps1 == eps2 == 1 (reading
C).  So C^F3_j = R_{2,gamma_j}(A_j)(z2) = sum_k C^F2_k(A_j) z2^k, the sum
indexed from the FORCED abscissa s(gamma_j) = 0.  TR3-S1 (accepted theorem,
e0 = 1) applied to the digit A_j gives C^F2_k(A_j) = c^G2_k(A_j) at every
abscissa k.  The GMN side: c^G3_j = z2^{t2(j)} R_2(A_j)(z2) with
t2(j) = (s2(A_j) - l1*u_j)/e1 = s2(A_j)  (l1 = 0), and R_2(A_j)(z2) =
sum_m c^G2_{s2+m}(A_j) z2^m (Def 2.21 evaluation from the ACTUAL initial
abscissa s2(A_j)).  Hence c^G3_j = sum_k c^G2_k z2^k = C^F3_j.  QED
(conditional on: the transcriptions above, (H-v3), and TR3-S1).
The forced-vs-actual abscissa bookkeeping is EXACTLY the level-3 Lemma
A-GEN mechanism: C^F3_j = eps2(gamma_j) * z2^{m0} * R_2^GMN(A_j)(z2) with
m0 = (s2(A_j) - s(gamma_j))/e1 in Z_{>=0}  (row P2), and the GMN t2
exponent absorbs it via t2 = m0 + (l1p*s - l1*u)-terms — at this stratum
t2 = m0 = s2(A_j).

CANDIDATE 2 (the eps-recurrence REVIVAL hypothesis, operationalized).  The
corrected-eps twist reappears at level 2 with the level-2 constants:
    (TWIST-3)   C^F3_j = z2^{theta2 * s_j} * c^G3_{s_j},
                theta2 := l1 * g1 * gamma2   (the level-shift of TR3-S2's
                theta = l0*g0*h0 = l0*g0*gamma1; gamma2 = w2(Phi2)/e1/g1).
ON THIS STRATUM theta2 = 0 (l1 = 0): CANDIDATE 2 DEGENERATES TO CANDIDATE 1
— the two are indistinguishable here BY DESIGN of the stratum; (TWIST-3) is
the sealed candidate shape for the NEXT stratum (order 3, e1 >= 2).  What
does NOT degenerate here: (a) the reading-P level-2 twist z2^{-gamma_j}
(slot-geometric, ratio step z2^{gamma3} — meter M1 counts its visible slots
and requires the run to refute it wherever visible); (b) any UNWRITTEN
marched-eps contribution (would appear as a C1 RED with a measured
slot-keyed ratio != 1 — the D-ITER precedent: RED => the measured table is
the result).

===================== PREREGISTERED PREDICTIONS (exact) =======================
C1  (IDENT-3) exact at every on-line slot, every sample, every tower.
    PREDICTED: 0 violations.  [THE PROBED LAW]
    RED handling: bug-detector rows (P0/V*/CERT*) green first; then the
    witness (tower, f, slot, both values) is printed and the FULL measured
    ratio table of the first failing tower is reported — the measured shape
    is then the unit's result (no-law report, D-ITER precedent).
P0  GMN-3 side integrity: t2 integral (Def 2.19's printed congruence),
    component endpoints e2-congruent, c^G3 != 0 on-line (Def 2.20's note).
    PREDICTED: 0.  [SEALED — GMN's printed proofs, under (H-v3)]
P1  Support agreement level 3: C^F3_j != 0 iff abscissa on the GMN on-line
    set.  PREDICTED: 0.  [CONJ component]
P2  Level-3 Lemma A-GEN z-shift: eps2(gamma_j)^{-1} C^F3_j ==
    z2^{m0} * R_2^GMN(A_j)(z2), m0 = (s2(A_j) - s(gamma_j))/e1 in Z_{>=0}.
    PREDICTED: 0.  [CONJ component]
P3  Digit-level order-2 identity (TR3-S1 on the probed digits, matched
    abscissas): C^F2_k(A_j) == c^G2_k(A_j) at every abscissa, every on-line
    digit.  PREDICTED: 0.  [SEALED — TR3-S1 accepted theorem, e0 = 1]
P4  Key tie: gmn3(Phi3) == psi2 exactly (s0 = 0, d = g2) — the GMN-lawful
    and FGMN-normalized key classes COINCIDE on this stratum (theta2 = 0,
    twist-invisible everywhere; the ORD-INV display).  PREDICTED: 0.
P5  Matched-label ord transport: ord_{psi2}(R_lambda3(f)) ==
    ord_{psi2}(R3(f)) for every sample (labels matched — SHARED key at
    every level).  PREDICTED: 0 mismatches; ord histogram REPORTED, must
    contain >= 1 (Phi3^mu families).
V1  VAL-3 multiplicativity w3(fg) = w3(f) + w3(g).  PREDICTED: 0.  [BUG-DET]
V2  R3 total multiplicativity R3(fg) = R3(f)R3(g) in K2[y] (Cor 4.7(3) one
    level up).  PREDICTED: 0.  [transcription validator]
V3  W-MULT level 3: R3w(fg) == y^delta R3w(f) R3w(g), delta =
    floor((s(wf)+s(wg))/e2) == 0 identically at e2 = 1 — the E3-degenerate
    no-carry control (D-REAL's carry track is EMPTY on this stratum).
    PREDICTED: 0, all deltas 0.
V4  Key lift: Phi3 monic, deg = e2*g2*deg(Phi2), w3(Phi3) = e2*g2*gamma3,
    one-sided, R3(Phi3) == psi2 EXACTLY, j0 = 0.  PREDICTED: 0.
V5  Two-form/support shape: support at on-line slots, j0 = floor(s0/e2),
    nonzero ends, length = d+1.  PREDICTED: 0.
CERT2  underlying order-2 tower certification: G.T1_T2 (8 samples), G.T5,
    G.T11 (PARI, Z_p) per instance.  PREDICTED: 0.
CERT3  order-3 external leg (Z_p rows): PARI factorpadic(Phi3) irreducible
    over Q_p; idealprimedec on Q[x]/(Phi3) (maximal at p): UNIQUE prime,
    (e,f) == (e0*e1*e2, d0*g0*g1*g2) = (1, d0*g0*g1*g2).  PREDICTED: 0.
    Honest deferral: no PARI analogue for the F_p[[t]] rows (as N-1).
M1  Reading-P discrimination meter: at every on-line slot with
    z2^{-gamma_j} != 1 the reading-P transcription's prediction
    z2^{-gamma_j}*C^F3_j == c^G3 must FAIL.  PREDICTED: p_refuted ==
    p_visible, and p_visible > 0 overall (teeth; the G2 lesson).
M2  m0 > 0 exercised (inner z-shift genuinely live): count > 0 overall.
M3  t2 != 0 exercised: count > 0 overall.
M4  Towers with z2^{gamma3} != 1 (P-visibility carrier): count > 0,
    listed per tower.

(H-v3) DISPLAYED HYPOTHESIS: the GMN-3 ordinate u_i = w2(A_i) + i*w2(Phi2)
consumes v3 = w2 — the order-3 extension of the PINNED order-2 Def-2.5
identity v2 = w1 (v_r(P) = e_{r-1}-normalized principal height = w_{r-1}'s
formula).  Both sides consume the SAME w2 (shared-input scope, as in
strata_probe/tr3s2); the GMN-verbatimness of t2's u_i rides this display.

RED DISCIPLINE: classify via P0/V*/CERT* first; only with those green does
a RED count as mathematics; any surviving RED is the headline result,
reported with the exact witness and the full measured table.

================================ TOWER ROSTER =================================
All rows all-e_j = 1; triples (e_j, h_j, g_j); mixed g_j with several >= 2;
h_j varied so gamma2 = g0*h0 + h1 and gamma3 = g1*gamma2 + h2 vary; d0 in
{1,2}.  deg Phi3 = d0*g0*g1*g2 (<= 12).
  3A (1; 1,1,2; 1,1,2; 1,1,2)  g=(2,2,2)                deg Phi3 = 8
  3B (1; 1,2,2; 1,1,2; 1,3,2)  h=(2,1,3) varied         deg Phi3 = 8
  3C (1; 1,1,2; 1,2,2; 1,1,3)  g2 = 3 (cubic psi2)      deg Phi3 = 12
  3D (2; 1,1,2; 1,1,1; 1,1,2)  g1 = 1 corner: z2 in K1  deg Phi3 = 8
  3E (1; 1,1,1; 1,2,2; 1,1,2)  g0 = 1 corner: K1 = K0   deg Phi3 = 4
  3F (2; 1,3,2; 1,1,2; 1,2,1)  g2 = 1 refinement corner deg Phi3 = 8
All over {Z_2, Z_3, F_2[[t]], F_3[[t]]} = 24 instances.

EXIT: 0 iff every preregistered row at its predicted count and all meters
MATCH.  Output: strata3_probe_output.txt (tee), strata3_probe_results.json.
"""
import random, math, sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_mul, fp_ord, fp_eval, eq12, bezout,
                              INF, Tower, mk_field_ext, _field_elems)

VIOL = []
COUNTS = {}
ORD_HIST = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# --------------------- deterministic irreducible pick (deg <= 3) -------------
def _no_root(F, A):
    return all(not F["isz"](fp_eval(F, A, e)) for e in _field_elems(F))

def pick_irr3(F, g, idx=0):
    """(idx+1)-th monic irreducible of degree g (<= 3) over F with nonzero
    constant term, deterministic enumeration order, EARLY EXIT (no full
    census — needed for the larger K2's)."""
    found = 0
    if g == 1:
        for c in _field_elems(F):
            if F["isz"](c): continue
            if found == idx: return [F["neg"](c), F["one"]]
            found += 1
    elif g == 2:
        for b in _field_elems(F):
            if F["isz"](b): continue
            for a in _field_elems(F):
                cand = [b, a, F["one"]]
                if _no_root(F, cand):           # deg 2: no root <=> irreducible
                    if found == idx: return cand
                    found += 1
    elif g == 3:
        for b in _field_elems(F):
            if F["isz"](b): continue
            for a in _field_elems(F):
                for c in _field_elems(F):
                    cand = [b, a, c, F["one"]]
                    if _no_root(F, cand):       # deg 3: no root <=> irreducible
                        if found == idx: return cand
                        found += 1
    raise RuntimeError("no irreducible found")

# ============================ the order-3 tower ===============================
class Tower3:
    """Order-3 all-e_j=1 tower: grb_order2_check.Tower VERBATIM for levels
    0-2, plus the level-3 layer (K2, eps2, w3, R3w/R3s, realize2, Phi3)."""
    def __init__(self, kind, p, d0, r0, r1, r2, tag):
        self.tag = tag
        self.T = Tower(kind, p, d0, r0, r1, tag + "/L12", mode="C")
        T = self.T
        self.R = T.R
        self.kind, self.p = kind, p
        self.e2, self.h2, self.g2 = r2
        assert math.gcd(self.e2, self.h2) == 1
        self.K2 = mk_field_ext(T.K1, T.psi1)
        self.z2 = self.K2["z"]
        self.l1, self.l1p = T.l1, T.l1p
        self.l2, self.l2p = bezout(self.e2, self.h2)
        self.gamma3 = self.e2*T.w2Phi2 + self.h2
        self.psi2 = pick_irr3(self.K2, self.g2, idx=(T.h0 + T.h1) % 2)
        self.Phi3 = self.build_Phi3()
        self.degPhi3 = self.e2*self.g2*T.degPhi2
        self.w3Phi3 = self.e2*self.g2*self.gamma3
        self.E3 = T.e0*T.e1*self.e2

    # ---- eps2: Def 3.15 one level up (reading C default; P for the meter) ----
    def eps2(self, beta, mode="C"):
        s, u = eq12(beta, self.T.e1, self.T.h1)
        expo = (self.l1p*s - self.l1*u) if mode == "C" else \
               (self.l1*s - self.l1p*u)
        return self.K2["pow"](self.z2, expo)

    # ---- level-2 read VALUE at z2 (Def 3.16's inner evaluation) ----
    def R2v(self, A):
        K2 = self.K2
        coeffs = self.T.R2w(A)
        v = K2["zero"]; zp = K2["one"]
        for c in coeffs:
            if not self.T.K1["isz"](c):
                v = K2["add"](v, K2["mul"](K2["embed"](c), zp))
            zp = K2["mul"](zp, self.z2)
        return v

    # ---- level-3 valuation ----
    def w3_data(self, f):
        d2 = dev(self.R, f, self.T.Phi2)
        vals = [self.T.w2(A) if A else INF for A in d2]
        if all(v == INF for v in vals):
            return d2, vals, INF
        g = min(self.e2*vals[j] + j*self.gamma3 for j in range(len(d2))
                if vals[j] < INF)
        return d2, vals, g
    def w3(self, f):
        return self.w3_data(f)[2]

    # ---- level-3 FGMN weight read (Def 3.16 at i = 3) ----
    def R3w(self, f, with_meta=False):
        K2 = self.K2
        d2, vals, g = self.w3_data(f)
        assert g < INF, "R3w of 0"
        s3, u3 = eq12(g, self.e2, self.h2)
        jmax = (len(d2)-1 - s3)//self.e2 if len(d2)-1 >= s3 else -1
        coeffs, online = [], []
        for j in range(jmax + 1):
            sj = s3 + j*self.e2
            A = d2[sj]
            num = g - sj*self.gamma3
            assert num % self.e2 == 0, "gamma_j not integral"
            gj = num // self.e2
            on = bool(A) and vals[sj] == gj
            if A and vals[sj] < gj:
                raise AssertionError("slot below the line: w3 min wrong")
            c = K2["mul"](self.eps2(gj), self.R2v(A)) if on else K2["zero"]
            coeffs.append(c); online.append(on)
        if with_meta:
            att = [i for i in range(len(d2)) if vals[i] < INF
                   and self.e2*vals[i] + i*self.gamma3 == g]
            return coeffs, dict(gamma=g, s3=s3, u3=u3, online=online,
                                s0=min(att), sprime=max(att), dev=d2,
                                vals=vals)
        return coeffs
    def R3s(self, f):
        coeffs, meta = self.R3w(f, with_meta=True)
        j0 = 0
        while j0 < len(coeffs) and self.K2["isz"](coeffs[j0]): j0 += 1
        return fp_norm(self.K2, coeffs[j0:]), j0, meta

    # ---- realize a K2 class at level-2 weight beta (anchor rep) ----
    def realize2(self, tau, beta):
        """O[x] poly C, deg < deg Phi2, w2(C) = beta, level-2 weight-read
        VALUE R2v(C) == tau (tau a K2 tuple over K1 in the z2-power basis)."""
        T, R = self.T, self.R
        s, u = eq12(beta, T.e1, T.h1)
        C = []
        for m in range(T.g1):
            tm = tau[m] if m < len(tau) else T.K1["zero"]
            if T.K1["isz"](tm): continue
            k = s + m*T.e1
            num = beta - k*T.gamma2
            assert num % T.e1 == 0
            gm = num // T.e1
            tm_adj = T.K1["mul"](T.K1["inv"](T.eps1(gm)), tm)
            C = padd(R, C, pmul(R, T.realize1(tm_adj, gm),
                                ppow(R, T.Phi1, k)))
        return C

    # ---- canonical state-key lift, one level up (build_Phi2 mirror) ----
    def build_Phi3(self):
        T, R = self.T, self.R
        P = []
        for k, c in enumerate(self.psi2):
            if self.K2["isz"](c): continue
            gp = (self.g2 - k)*self.gamma3
            if gp == 0:
                Ck = [R["one"]]
            else:
                tau = self.K2["mul"](self.K2["inv"](self.eps2(gp)), c)
                Ck = self.realize2(tau, gp)
            P = padd(R, P, pmul(R, Ck, ppow(R, T.Phi2, self.e2*k)))
        return P

    # ---- samples ----
    def rand_K2(self, nonzero=False):
        while True:
            c = tuple(self.T.rand_K1() for _ in range(self.T.g1))
            if not nonzero or not self.K2["isz"](c): return c
    def rand_structured3(self, nslots=3):
        T, R = self.T, self.R
        base = self.gamma3*(nslots + 2) + T.g1*T.gamma2 + T.g0*T.h0 + 4
        f = []
        for j in range(nslots):
            gp = base - j*self.gamma3 + random.choice([0, 0, 1])*self.e2
            if random.random() < 0.15: continue
            f = padd(R, f, pmul(R, self.realize2(self.rand_K2(nonzero=True),
                                                 gp),
                                ppow(R, T.Phi2, j)))
        noise = T.rand_opoly(random.randrange(0, T.degPhi2 + 3), pimax=3)
        f = padd(R, f, pscal(R, R["pi_pow"](base + 2), noise))
        if not f:
            f = [R["pi_pow"](base)]
        return f

# ===================== FRESH GMN side (orders 1, 2, 3) ========================
def gmn1(T, a):
    """GMN order-1 data for a nonzero digit a: (s1, r1val), r1val =
    R_1(a)(z1) = sum_k c_{s1+k*e0} z1^k in K1 (fresh from Defs 1.6/1.9)."""
    R, K1 = T.R, T.K1
    d0v = dev(R, a, T.Phi0)
    um = [w0(R, b) if b else INF for b in d0v]
    line = min(T.e0*um[m] + m*T.h0 for m in range(len(d0v)) if um[m] < INF)
    on = [m for m in range(len(d0v)) if um[m] < INF
          and T.e0*um[m] + m*T.h0 == line]
    s1, sp1 = min(on), max(on)
    val = K1["zero"]; zp = K1["one"]
    for m in range(s1, sp1 + 1, T.e0):
        b = d0v[m] if m < len(d0v) else []
        if b and um[m] < INF and T.e0*um[m] + m*T.h0 == line:
            val = K1["add"](val, K1["mul"](K1["embed"](T.res_digit(b, um[m])),
                                           zp))
        zp = K1["mul"](zp, T.z1)
    return s1, val

def gmn2(T, f, tag="?"):
    """GMN (18) + Defs 2.19-2.21 at r = 2: (s, d, coeffs, on, s1map, umap),
    coeffs = [c_s, c_{s+e1}, ...] in K1 (fresh implementation)."""
    R, K1 = T.R, T.K1
    d1 = dev(R, f, T.Phi1)
    u = [(T.w1(a) + i*T.w1Phi1) if a else INF for i, a in enumerate(d1)]
    vals = [(T.e1*u[i] + i*T.h1) if u[i] < INF else INF for i in range(len(d1))]
    m = min(v for v in vals if v < INF)
    on = [i for i in range(len(d1)) if vals[i] == m]
    s, sp = min(on), max(on)
    if (sp - s) % T.e1 != 0:
        viol("P0", tag, "level-2 component endpoints not e1-congruent")
    d = (sp - s)//T.e1
    coeffs, s1map, umap = [], {}, {}
    for k in range(d + 1):
        i = s + k*T.e1
        ai = d1[i] if i < len(d1) else []
        if (not ai) or vals[i] != m:
            coeffs.append(K1["zero"]); continue
        s1, r1val = gmn1(T, ai)
        s1map[i], umap[i] = s1, u[i]
        num = s1 - T.l0*u[i]
        if num % T.e0 != 0:
            viol("P0", tag, f"t1({i}) not integral")
            coeffs.append(K1["zero"]); continue
        coeffs.append(K1["mul"](K1["pow"](T.z1, num//T.e0), r1val))
    return s, d, coeffs, set(on), s1map, umap

def gmn3(T3, f):
    """GMN Defs 2.19-2.21 at r = 3 (the level-generic recursion, print
    gmn.txt:1823-1906): c_i = z2^{t2(i)} R_2(A_i)(z2), t2(i) =
    (s2(A_i) - l1*u_i)/e1, u_i = w2(A_i) + i*w2(Phi2)  [(H-v3)].
    Returns (s, d, coeffs, on, s2map, r2map, u)."""
    T, R, K2 = T3.T, T3.R, T3.K2
    d2 = dev(R, f, T.Phi2)
    u = [(T.w2(A) + i*T.w2Phi2) if A else INF for i, A in enumerate(d2)]
    vals = [(T3.e2*u[i] + i*T3.h2) if u[i] < INF else INF
            for i in range(len(d2))]
    m = min(v for v in vals if v < INF)
    on = [i for i in range(len(d2)) if vals[i] == m]
    s, sp = min(on), max(on)
    note("P0")
    if (sp - s) % T3.e2 != 0:
        viol("P0", T3.tag, "level-3 component endpoints not e2-congruent")
    d = (sp - s)//T3.e2
    coeffs, s2map, r2map = [], {}, {}
    for kk in range(d + 1):
        i = s + kk*T3.e2
        Ai = d2[i] if i < len(d2) else []
        if (not Ai) or vals[i] != m:
            coeffs.append(K2["zero"]); continue
        s2i, d2i, co2, on2, _, _ = gmn2(T, Ai, tag=T3.tag)
        r2val = K2["zero"]; zp = K2["one"]
        for cc in co2:
            if not T.K1["isz"](cc):
                r2val = K2["add"](r2val, K2["mul"](K2["embed"](cc), zp))
            zp = K2["mul"](zp, T3.z2)
        s2map[i], r2map[i] = s2i, r2val
        num = s2i - T3.l1*u[i]
        note("P0")
        if num % T.e1 != 0:
            viol("P0", T3.tag, f"t2({i}) not integral: s2={s2i}, u_i={u[i]}")
            coeffs.append(K2["zero"]); continue
        t2 = num // T.e1
        ci = K2["mul"](K2["pow"](T3.z2, t2), r2val)
        note("P0")
        if K2["isz"](ci):
            viol("P0", T3.tag, f"c^G3 == 0 at on-line abscissa {i}")
        coeffs.append(ci)
    return s, d, coeffs, set(on), s2map, r2map, u

# ----------------------------- value printing --------------------------------
def k2_repr(T3, v):
    """decompose v as z2^a * z1^b if possible, else raw."""
    K2 = T3.K2
    z1e = K2["embed"](T3.T.z1)
    ordz1 = 1; x = z1e
    while x != K2["one"] and ordz1 < 700:
        x = K2["mul"](x, z1e); ordz1 += 1
    ordz2 = 1; x = T3.z2
    while x != K2["one"] and ordz2 < 700:
        x = K2["mul"](x, T3.z2); ordz2 += 1
    for a in range(ordz2):
        za = K2["pow"](T3.z2, a)
        for b in range(ordz1):
            if K2["mul"](za, K2["pow"](z1e, b)) == v:
                return f"z2^{a}*z1^{b}" if a or b else "1"
    return f"raw:{v}"

# =============================== probe families ===============================
class Meters:
    def __init__(self):
        self.p_visible = 0
        self.p_refuted = 0
        self.m0pos = 0
        self.t2nz = 0

def probe3(T3, f, shape, M):
    T, K2 = T3.T, T3.K2
    note("C1")
    coeffs, meta = T3.R3w(f, with_meta=True)
    g, s3 = meta["gamma"], meta["s3"]
    s, d, gco, on, s2map, r2map, uvec = gmn3(T3, f)
    if s < s3 or (s - s3) % T3.e2 != 0:
        viol("P1", T3.tag, f"[{shape}] GMN on-line start {s} below/off the "
                           f"forced abscissa class {s3}")
        return
    jmax = max(len(coeffs) - 1, (s + d*T3.e2 - s3)//T3.e2)
    ratio_table = []
    red_here = False
    for j in range(jmax + 1):
        sj = s3 + j*T3.e2
        CF = coeffs[j] if j < len(coeffs) else K2["zero"]
        if s <= sj <= s + d*T3.e2 and (sj - s) % T3.e2 == 0:
            cG = gco[(sj - s)//T3.e2]
        else:
            cG = K2["zero"]
        note("P1")
        if (not K2["isz"](CF)) != (sj in on):
            viol("P1", T3.tag, f"[{shape}] support mismatch at abscissa {sj}: "
                 f"CF!=0 is {not K2['isz'](CF)}, on-line is {sj in on}")
            return
        if K2["isz"](CF):
            continue
        gj = (g - sj*T3.gamma3)//T3.e2
        # C1 THE LAW (IDENT-3)
        ratio = K2["mul"](CF, K2["inv"](cG))
        ratio_table.append((sj, k2_repr(T3, ratio)))
        if CF != cG:
            viol("C1", T3.tag,
                 f"[{shape}] IDENT-3 FAILS at abscissa {sj} (slot {j}): "
                 f"measured ratio CF/cG = {k2_repr(T3, ratio)}  "
                 f"[CF={CF}, cG={cG}]")
            red_here = True
            continue                    # keep measuring the full table
        # P2 level-3 Lemma A-GEN z-shift
        note("P2")
        sfa, ufa = eq12(gj, T.e1, T.h1)
        s2i = s2map.get(sj)
        if s2i is None or (s2i - sfa) % T.e1 != 0 or s2i < sfa:
            viol("P2", T3.tag, f"[{shape}] m0 not in Z>=0 at abscissa {sj}")
            return
        m0 = (s2i - sfa)//T.e1
        inner = K2["mul"](K2["inv"](T3.eps2(gj)), CF)
        if inner != K2["mul"](K2["pow"](T3.z2, m0), r2map[sj]):
            viol("P2", T3.tag, f"[{shape}] level-3 A-GEN z-shift fails "
                               f"at abscissa {sj} (m0={m0})")
            return
        if m0 > 0: M.m0pos += 1
        if (s2i - T3.l1*uvec[sj])//T.e1 != 0: M.t2nz += 1
        # P3 digit-level order-2 identity (TR3-S1 on the digit)
        note("P3")
        A = meta["dev"][sj]
        co2F, meta2 = T.R2w(A, with_meta=True)
        s2F = meta2["s2"]
        s2G, d2G, co2G, on2G, _, _ = gmn2(T, A, tag=T3.tag)
        kmax = max(len(co2F) - 1, (s2G + d2G*T.e1 - s2F)//T.e1)
        for k in range(kmax + 1):
            ak = s2F + k*T.e1
            c2F = co2F[k] if k < len(co2F) else T.K1["zero"]
            if s2G <= ak <= s2G + d2G*T.e1 and (ak - s2G) % T.e1 == 0:
                c2G = co2G[(ak - s2G)//T.e1]
            else:
                c2G = T.K1["zero"]
            if c2F != c2G:
                viol("P3", T3.tag, f"[{shape}] digit-level order-2 identity "
                                   f"fails at inner abscissa {ak}")
                return
        # M1 reading-P discrimination
        pfac = K2["mul"](T3.eps2(gj, mode="P"),
                         K2["inv"](T3.eps2(gj, mode="C")))
        if pfac != K2["one"]:
            M.p_visible += 1
            if K2["mul"](pfac, CF) != cG:
                M.p_refuted += 1
    if red_here:
        viol("C1", T3.tag, f"[{shape}] full measured ratio table "
                           f"(abscissa, CF/cG): {ratio_table}")
        return
    # V5 two-form/support shape
    note("V5")
    side, j0, _ = T3.R3s(f)
    if j0 != (meta["s0"] - s3)//T3.e2 or j0 != meta["s0"]//T3.e2:
        viol("V5", T3.tag, f"[{shape}] j0={j0} != floor(s0/e2)")
        return
    d_pred = (meta["sprime"] - meta["s0"])//T3.e2
    if len(side) != d_pred + 1 or (side and (K2["isz"](side[0])
                                             or K2["isz"](side[-1]))):
        viol("V5", T3.tag, f"[{shape}] side length/ends: len={len(side)} "
                           f"vs d+1={d_pred+1}")
        return
    # P5 matched-label ord transport (SHARED key psi2 both sides)
    note("P5")
    o1 = fp_ord(K2, fp_norm(K2, gco), T3.psi2)
    o2 = fp_ord(K2, side, T3.psi2)
    ORD_HIST[o1] = ORD_HIST.get(o1, 0) + 1
    if o1 != o2:
        viol("P5", T3.tag, f"[{shape}] ord mismatch: ord_psi2(R_lam3)={o1}, "
                           f"ord_psi2(R3)={o2}")

def pairs3(T3, npairs=10):
    K2 = T3.K2
    for _ in range(npairs):
        f = T3.rand_structured3(random.choice([2, 3]))
        h = T3.rand_structured3(random.choice([2, 3]))
        fh = pmul(T3.R, f, h)
        note("V1")
        wf, wh, wfh = T3.w3(f), T3.w3(h), T3.w3(fh)
        if wfh != wf + wh:
            viol("V1", T3.tag, f"VAL-3: w3(fh)={wfh} != {wf}+{wh}")
            continue
        note("V2")
        Rf, _, _ = T3.R3s(f); Rh, _, _ = T3.R3s(h); Rfh, _, _ = T3.R3s(fh)
        if fp_norm(K2, Rfh) != fp_mul(K2, Rf, Rh):
            viol("V2", T3.tag, "R3(fh) != R3(f)R3(h)")
        note("V3")
        sf, _ = eq12(wf, T3.e2, T3.h2); sh, _ = eq12(wh, T3.e2, T3.h2)
        delta = (sf + sh)//T3.e2
        if delta != 0:
            viol("V3", T3.tag, f"delta={delta} != 0 on the e2=1 stratum")
        Wf = T3.R3w(f); Wh = T3.R3w(h); Wfh = T3.R3w(fh)
        pred = fp_mul(K2, [K2["zero"]]*delta + [K2["one"]],
                      fp_mul(K2, fp_norm(K2, Wf), fp_norm(K2, Wh)))
        if fp_norm(K2, Wfh) != pred:
            viol("V3", T3.tag, f"W-MULT-3 fails (delta={delta})")

def key3(T3):
    T, R, K2 = T3.T, T3.R, T3.K2
    note("V4")
    P3p = T3.Phi3
    if len(P3p) - 1 != T3.degPhi3:
        viol("V4", T3.tag, f"deg Phi3 = {len(P3p)-1} != {T3.degPhi3}")
    lead = P3p[-1] if P3p else R["zero"]
    if R["isz"](lead) or not R["isz"](R["add"](lead, R["neg"](R["one"]))):
        viol("V4", T3.tag, "Phi3 not monic")
    d2, vals, g = T3.w3_data(P3p)
    if g != T3.w3Phi3:
        viol("V4", T3.tag, f"w3(Phi3) = {g} != e2*g2*gamma3 = {T3.w3Phi3}")
    for j, c in enumerate(d2):
        if c and T3.e2*vals[j] + j*T3.gamma3 < T3.w3Phi3:
            viol("V4", T3.tag, f"Phi3 slot {j} below weight")
    side, j0, meta = T3.R3s(P3p)
    if j0 != 0:
        viol("V4", T3.tag, f"R3(Phi3): j0 = {j0} != 0")
    if side != fp_norm(K2, T3.psi2):
        viol("V4", T3.tag, "R3(Phi3) != psi2 exactly")
    # P4 GMN-side key tie: the two key classes COINCIDE (theta2 = 0)
    note("P4")
    s, d, gco, on, _, _, _ = gmn3(T3, P3p)
    if s != 0 or d != T3.g2:
        viol("P4", T3.tag, f"gmn3(Phi3): s0={s}, d={d} (g2={T3.g2})")
    if fp_norm(K2, gco) != fp_norm(K2, T3.psi2):
        viol("P4", T3.tag, "gmn3(Phi3) != psi2 (key classes DIVERGE on the "
                           "theta2=0 stratum?!)")

def run_tower(T3, M, nf=24):
    T, R = T3.T, T3.R
    key3(T3)
    for _ in range(nf):
        f = T.rand_opoly(random.randrange(0, int(2.2*T3.degPhi3) + 1),
                         pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        probe3(T3, f, "rand", M)
    for _ in range(nf//2):
        probe3(T3, T3.rand_structured3(random.choice([2, 3, 4])), "struct", M)
    for _ in range(nf//2):
        a = random.randrange(1, 2*T3.e2 + 2)
        h = T.rand_opoly(random.randrange(0, T.degPhi2 + 2), pimax=3)
        if not h: h = [R["one"]]
        probe3(T3, pmul(R, ppow(R, T.Phi2, a), h), f"Phi2^{a}*g", M)
    for _ in range(nf//2):
        a = random.randrange(1, 4)
        h = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not h: h = [R["one"]]
        probe3(T3, pmul(R, ppow(R, T.Phi1, a), h), f"Phi1^{a}*g", M)
    for k in range(0, 3):
        probe3(T3, [R["pi_pow"](k)], f"pi^{k}", M)
    for _ in range(nf//4):
        mu = random.choice([1, 2])
        probe3(T3, pmul(R, ppow(R, T3.Phi3, mu), T3.rand_structured3(2)),
               f"Phi3^{mu}*Q", M)
    pairs3(T3, npairs=10)

# ==================================== main ====================================
ROSTER3 = [
    # (tag, d0, (e0,h0,g0), (e1,h1,g1), (e2,h2,g2))
    ("3A", 1, (1,1,2), (1,1,2), (1,1,2)),
    ("3B", 1, (1,2,2), (1,1,2), (1,3,2)),
    ("3C", 1, (1,1,2), (1,2,2), (1,1,3)),
    ("3D", 2, (1,1,2), (1,1,1), (1,1,2)),
    ("3E", 1, (1,1,1), (1,2,2), (1,1,2)),
    ("3F", 2, (1,3,2), (1,1,2), (1,2,1)),
]

def cert3_pari(T3, pari):
    if T3.kind != "Zp" or pari is None: return
    note("CERT3")
    coeffs = [int(c) for c in T3.Phi3]
    F = pari.Pol(list(reversed(coeffs)))
    fac = pari.factorpadic(F, T3.p, 80)
    if len(fac[0]) != 1 or int(fac[1][0]) != 1:
        viol("CERT3", T3.tag, f"PARI: Phi3 NOT irreducible over Q_{T3.p}")
        return
    nf = pari.nfinit([F, [T3.p]])
    dec = pari.idealprimedec(nf, T3.p)
    T = T3.T
    e_pred, f_pred = T3.E3, T.d0*T.g0*T.g1*T3.g2
    if len(dec) != 1:
        viol("CERT3", T3.tag, f"PARI: {len(dec)} primes above p (pred 1)")
        return
    pr = dec[0]
    if (int(pr[2]), int(pr[3])) != (e_pred, f_pred):
        viol("CERT3", T3.tag, f"PARI (e,f) = ({int(pr[2])},{int(pr[3])}) "
                              f"!= pred ({e_pred},{f_pred})")

def main():
    t0 = time.time()
    random.seed(20260817)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); CERT PARI legs skipped "
              "-> RED if predicted")
    configs = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    M = Meters()
    tower_recs = []
    cert2_viol = 0; cert2_n = 0
    for kind, p in configs:
        for tag, d0, r0, r1, r2 in ROSTER3:
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            # CERT2: re-certify the underlying order-2 tower (N-1 families)
            gv0, gc0 = len(G.VIOL), sum(G.COUNTS.get(k, 0)
                                        for k in ("T1", "T2", "T5", "T11"))
            G.T1_T2(T3.T, nf=8)
            G.T5(T3.T)
            G.T11(T3.T, pari)
            cert2_viol += len(G.VIOL) - gv0
            cert2_n += sum(G.COUNTS.get(k, 0)
                           for k in ("T1", "T2", "T5", "T11")) - gc0
            # CERT3: external leg on the order-3 key
            cert3_pari(T3, pari)
            # the probe
            run_tower(T3, M, nf=24)
            zg = T3.K2["pow"](T3.z2, T3.gamma3)
            tower_recs.append(dict(
                tower=full, d0=d0, r0=r0, r1=r1, r2=r2,
                gamma2=T3.T.gamma2, gamma3=T3.gamma3,
                degPhi3=T3.degPhi3,
                z2_pow_gamma3_nontrivial=(zg != T3.K2["one"])))
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)} "
              f"(+CERT2 {cert2_viol}, G-side {len(G.VIOL)})")
    # ------------------------------- report ---------------------------------
    print()
    print("=" * 78)
    print("DEPTH-3 STRATA PROBE — PREDICTED vs OBSERVED (violations; samples "
          "in parens)")
    print("=" * 78)
    fams = [
        ("C1", "(IDENT-3) C^F3_j == c^G3_{s_j}       [THE LAW]   ", 0),
        ("P0", "GMN-3 integrity (t2 int, comp, c!=0) [SEALED]    ", 0),
        ("P1", "support agreement level 3            [CONJ comp.]", 0),
        ("P2", "level-3 A-GEN z-shift (m0 in Z>=0)   [CONJ comp.]", 0),
        ("P3", "digit-level order-2 identity         [TR3-S1]    ", 0),
        ("P4", "key tie gmn3(Phi3)=psi2 (ORD-INV)    [SEALED]    ", 0),
        ("P5", "matched-label ord transport          [derived]   ", 0),
        ("V1", "VAL-3 multiplicativity               [BUG-DET]   ", 0),
        ("V2", "R3 total multiplicativity            [BUG-DET]   ", 0),
        ("V3", "W-MULT-3, delta == 0 (no-carry ctrl) [BUG-DET]   ", 0),
        ("V4", "key lift R3(Phi3)=psi2 exact         [BUG-DET]   ", 0),
        ("V5", "two-form/support shape + j0          [BUG-DET]   ", 0),
    ]
    all_green = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:3} {desc:57} pred {pred}  obs {obs:5d} ({n:6d})  "
              f"{verdict}")
    cert3_obs = sum(1 for v in VIOL if v[0] == "CERT3")
    c3v = "GREEN" if cert3_obs == 0 else "RED"
    if cert3_obs: all_green = False
    print(f"CERT3 PARI order-3 external leg (Zp rows)                  "
          f"pred 0  obs {cert3_obs:5d} ({COUNTS.get('CERT3',0):6d})  {c3v}")
    c2v = "GREEN" if cert2_viol == 0 else "RED"
    if cert2_viol: all_green = False
    print(f"CERT2 order-2 tower certification (G.T1/T2/T5/T11)         "
          f"pred 0  obs {cert2_viol:5d} ({cert2_n:6d})  {c2v}")
    m1 = "MATCH" if (M.p_refuted == M.p_visible and M.p_visible > 0) \
         else "MISMATCH"
    if m1 == "MISMATCH": all_green = False
    print(f"M1 reading-P refuted at P-visible slots: {M.p_refuted}"
          f"/{M.p_visible} (pred: equal, > 0)  {m1}")
    m2 = "MATCH" if M.m0pos > 0 else "MISMATCH"
    m3 = "MATCH" if M.t2nz > 0 else "MISMATCH"
    if m2 == "MISMATCH" or m3 == "MISMATCH": all_green = False
    print(f"M2 inner z-shift m0 > 0 exercised: {M.m0pos} slots "
          f"(pred > 0)  {m2}")
    print(f"M3 t2 != 0 exercised: {M.t2nz} slots (pred > 0)  {m3}")
    m4n = sum(1 for r in tower_recs if r["z2_pow_gamma3_nontrivial"])
    m4 = "MATCH" if m4n > 0 else "MISMATCH"
    if m4 == "MISMATCH": all_green = False
    print(f"M4 towers with z2^gamma3 != 1: {m4n}/{len(tower_recs)} "
          f"(pred > 0)  {m4}")
    hist = " ".join(f"{k}:{v}" for k, v in sorted(ORD_HIST.items()))
    m5 = "MATCH" if any(k >= 1 and v > 0 for k, v in ORD_HIST.items()) \
         else "MISMATCH"
    if m5 == "MISMATCH": all_green = False
    print(f"P5 ord histogram (ord: count): {hist}   (pred: some ord >= 1)  "
          f"{m5}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    if G.VIOL:
        print(f"{len(G.VIOL)} CERT2 VIOLATIONS (first 10):")
        for v in G.VIOL[:10]:
            print("  ", v)
    total = sum(COUNTS.values()) + cert2_n
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    verdict = all_green and not VIOL and not G.VIOL
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if verdict else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "strata3_probe_results.json"), "w") as fh:
        json.dump(dict(
            seed=20260817,
            violations=[list(v) for v in VIOL],
            cert2_violations=[list(v) for v in G.VIOL],
            counts=COUNTS,
            cert2_n=cert2_n,
            meters=dict(p_visible=M.p_visible, p_refuted=M.p_refuted,
                        m0pos=M.m0pos, t2nz=M.t2nz),
            ord_hist=ORD_HIST,
            towers=tower_recs), fh, indent=1, default=str)
    return 0 if verdict else 1

if __name__ == "__main__":
    sys.exit(main())
