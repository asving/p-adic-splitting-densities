#!/usr/bin/env python3
"""iterlaw4_probe.py — (ITER-LAW-n) AT n = 4: the sealed level-4 cocycle probe
(wave-19 unit 1; charter = L3CONVERGENCE_2026-08-08.md S4, executed exactly).
Sealed preregistration = lean/notes/openmath/ITERLAW4_PROBE_2026-08-08.md.
Two-commit seal: this file + the prereg are committed BEFORE the battery runs.

THE PRIMARY CANDIDATE (ITER-LAW-4) = the (ITER-LAW-n) recursion of
ITERLAWR_PROBE S6 / L3CONVERGENCE S2 Candidate 2, unrolled at n = 4, every
constant explicit.  For gamma, gamma' in W4 (4-fold iterated eq-(12-int)
splits s4,s3,s2,s1; s_j-defect := s_j(g)+s_j(g')-s_j(g+g')):

    c4(g,g') = zb4^{d4} * z3^{D3} * z2^{D2} * z1^{D1}

    d4 = floor((s4(g)+s4(g'))/e3)  in {0,1}            [top carry]
    S3 = d4*gamma4                                      [top shift]
    D3 = (s3-defect + l2*S3)/e2    in Z                 [new middle exponent]
    S2 = D3*gamma3 + S3*(l2p - l2*w2Phi2)               [composed shift, rung 2]
    D2 = (s2-defect + l1*S2)/e1    in Z                 [middle exponent]
    S1 = D2*gamma2 + S2*(l1p - l1*w1Phi1)               [composed shift, rung 1]
    D1 = (s1-defect + l0*S1)/e0    in Z                 [inner exponent]

with gamma2 = e1*w1Phi1+h1, gamma3 = e2*w2Phi2+h2, gamma4 = e3*w3Phi3+h3,
w1Phi1 = e0*g0*h0, w2Phi2 = e1*g1*gamma2, w3Phi3 = e2*g2*gamma3, and
(l0,l0p),(l1,l1p),(l2,l2p),(l3,l3p) the normalized Bezout pairs at
(e_j,h_j).  At e3 = 1 this collapses verbatim to the measured (ITER-LAW-3);
at e3 = e2 = 1 to the ACCEPTED order-2 law.

DISTINGUISHED ALTERNATIVE (ALT, the "level-3-naive" template — the exact
analogue of the level-3 cycle's separation pair, one knob): S2 replaced by
the naive per-level composition at the NEW level, S2n := gamma3*d3c,
d3c := floor((s3(g)+s3(g'))/e2) (plain carry), recursion continued downward
(D2n from S2n, S1n = D2n*gamma2 + S2n*(l1p-l1*w1Phi1), D1n).  Coincides with
the primary exactly at d4 = 0; ALT violation counts and separation meters
MSEP4i/MSEP4f are recorded, never part of the primary prediction.

HARNESS OF RECORD (the sealed iterlawr_probe.py calculus consumed VERBATIM
by import — grb_order2_check.Tower levels 0-2, strata3_probe.Tower3 level 3
incl. its psi2-pick shim, iterlawr_probe.Composite3 as the level-3 prober +
closed_form2 as the accepted-order-2 reference; chosen over the
level3_xcheck from-notes reconstruction because the sealed calculus IS the
calculus the measured (ITER-LAW-3) was measured on — seal 911431c — so the
F0/F-SUB fidelity legs tie the new level-4 layer to the exact object of
record; the decorrelated-reimplementation role is already discharged, six
ways, by the convergence fleet).  NEW here (the only added calculus, the
exact one-level-up mirror of the Tower3 layer): eps3 (Def 3.15 reading C at
level 3), w4/R4w/R4s (Def 3.16 at i = 4), realize3 + build_Phi4 (canonical
eps2-corrected state-key lift one level up; CERT-only — the cocycle does NOT
consume Phi4), K4 = K3[zb4]/(psi3), val4(f) = sum_j R4w(f)_j zb4^j, the
4-read anchors/cocycle, and this battery.  The LIFT-DEV secondary leg
transcribes the notes' PLAIN standard-lift recursion (level3_xcheck.py LIFT
display) into harness types for Phi3 only.

DETERMINISTIC: seed 20260905 (fresh in this genre), exact arithmetic only.
VERDICT DISCIPLINE (the RED-line lesson, pre-agreed wording): THREE verdict
lines — LAW (primary predicted-0 families only), CONTROL (meters + mutation
teeth; failures = PARTIAL(teeth), never law-RED), SECONDARY (LIFT-DEV-4).
Exit 0 iff all three clean.  JSON: iterlaw4_probe_results.json.
Usage: iterlaw4_probe.py [--design]   (--design: construction + constants +
letter orders + mutation/LD design-time visibility + cost probe ONLY; no law
comparison, no val4 of any pair, no measured anchor value).
"""
import random, math, sys, os, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, bezout, INF, Tower, mk_field_ext, fp_norm)
import strata3_probe as S3MOD
from strata3_probe import Tower3
import strata_probe as SP
import iterlawr_probe as ILP          # side effect: installs the disclosed
from iterlawr_probe import Composite3, closed_form2, k3_repr   # psi2 shim

VIOL = []
COUNTS = {}
HARNESS_EVENTS = []
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# roster: (tag, d0, r0, r1, r2, r3), r_j = (e_j, h_j, g_j)
ROWS = [
    ("A4",  1, (2,1,1), (2,1,1), (2,1,1), (2,1,1)),  # E4=16 stacked, triple cascade
    ("P",   1, (2,1,1), (2,1,1), (2,1,1), (2,1,2)),  # E4=16 g3=2: zb4 teeth; frozen pair w/ A4
    ("Q",   1, (2,1,2), (2,1,2), (2,1,2), (2,1,2)),  # E4=16 ALL-LETTERS (M2-S8 flag row)
    ("R",   1, (2,3,1), (2,3,1), (2,3,1), (2,3,2)),  # E4=16 h-track (all h=3), g3=2
    ("S",   2, (2,1,1), (2,1,1), (2,1,1), (2,1,1)),  # E4=16 d0=2 base inertia
    ("B4",  1, (3,2,1), (1,1,2), (2,1,1), (2,1,1)),  # E4=12 stacked e0=3, dead middle e1=1
    ("D1",  1, (2,1,1), (1,1,2), (3,1,1), (2,1,1)),  # E4=12 e1=1, e2=3 mixed
    ("D2",  1, (3,2,1), (2,1,1), (1,1,2), (2,1,1)),  # E4=12 e2=1, stacked e0=3
    ("C0",  1, (1,1,2), (2,1,1), (2,1,1), (2,1,1)),  # E4=8  e0=1 control
    ("C1",  1, (2,1,1), (1,1,2), (2,1,1), (2,1,1)),  # E4=8  e1=1 control
    ("C2",  1, (2,1,1), (2,1,1), (1,1,2), (2,1,1)),  # E4=8  e2=1 control
    ("C3",  1, (2,1,1), (2,1,1), (2,1,1), (1,1,2)),  # E4=8  e3=1 control: measured lvl-3 two ways
    ("T",   1, (2,1,1), (2,1,1), (2,1,1), (3,2,1)),  # E4=24 stretch (REDUCED legs)
    ("MUA", 1, (1,1,2), (2,1,2), (3,1,2), (2,1,2)),  # E4=12 all-g=2 mutation row (e1!=e2!=e3)
    ("MUB", 1, (1,1,2), (3,2,2), (2,1,2), (3,1,2)),  # E4=18 all-g=2 mutation row (flipped ineqs)
    ("LD1", 1, (1,1,1), (2,1,2), (2,1,1), (2,1,1)),  # E4=8  LIFT-DEV dev row (g2=1, z2 live)
    ("LD2", 1, (1,1,1), (2,1,2), (2,3,1), (2,1,1)),  # E4=8  LIFT-DEV dev row (h2=3 variant)
    ("LD3", 1, (1,1,1), (2,1,2), (2,1,2), (2,1,1)),  # E4=8  LIFT-DEV invariance row (g2=2)
]
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
# REDUCED legs (W1xW1 block only; no G5/G7/GSWAP; all per-pair legs +
# F-CLASS still run): row T on ALL rings, and rows Q/MUA/MUB on the two
# F_p[[t]] rings — fixed PRE-SEAL from the disclosed design-phase cost
# probe (Fpt core op 0.6-0.9 s on MUB, ~40-75 ms on Q; Zp cheap).
def is_reduced(kind, base):
    return base == "T" or (kind == "Fpt" and base in ("Q", "MUA", "MUB"))
MUT_ROWS = ("MUA", "MUB")
MUT_CONFIGS = [("Zp", 3), ("Fpt", 2)]
LD_DEV_ROWS = ("LD1", "LD2")          # g2 = 1: deviation factor predicted
LD_INV_ROWS = ("LD3",)                # g2 = 2: invariance predicted
CERT4P_SKIP = ("Q", "MUA", "MUB")     # degPhi4 in {256,192,288} > caps (64/32); deferrals counted

# ---------------------------------------------------------------------------
# field-order utilities (fast pow is built into mk_field_ext; orders via
# factored group order — needed because K4 can be F_{p^16})
def _factorize(n):
    fs = {}; d = 2
    while d*d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1: fs[n] = fs.get(n, 0) + 1
    return fs

def field_ord(K, x):
    if K["isz"](x): return None
    n = K["q"] - 1
    if x == K["one"]: return 1
    for pf in _factorize(n):
        while n % pf == 0 and K["pow"](x, n // pf) == K["one"]:
            n //= pf
    return n

# ============================ the order-4 tower ===============================
class Tower4:
    """Order-4 tower: Tower3 VERBATIM for levels 0-3 (incl. canonical
    eps1-corrected Phi2 and eps2-corrected Phi3), plus the level-4 layer:
    K3, eps3, w4, R4w/R4s, realize3, canonical Phi4 — the exact one-level-up
    mirror of strata3_probe.Tower3's level-3 layer."""
    def __init__(self, kind, p, d0, r0, r1, r2, r3, tag, phi3_plain=False):
        self.tag = tag
        self.T3 = Tower3(kind, p, d0, r0, r1, r2, tag + "/L0123")
        T3 = self.T3; T = T3.T
        self.T = T
        self.R = T.R
        self.kind, self.p = kind, p
        self.e3, self.h3, self.g3 = r3
        assert math.gcd(self.e3, self.h3) == 1
        self.plain = bool(phi3_plain)
        if phi3_plain:                 # LIFT-DEV twin: notes' plain std lift
            T3.Phi3 = build_Phi3_plain(T3)
        self.K3 = mk_field_ext(T3.K2, T3.psi2)
        self.z3 = self.K3["z"]
        self.l2, self.l2p = T3.l2, T3.l2p
        self.l3, self.l3p = bezout(self.e3, self.h3)
        self.gamma4 = self.e3*T3.w3Phi3 + self.h3
        self.psi3 = S3MOD.pick_irr3(self.K3, self.g3, idx=(T.h1 + T3.h2) % 2)
        self.Phi4 = self.build_Phi4()
        self.degPhi4 = self.e3*self.g3*T3.degPhi3
        self.w4Phi4 = self.e3*self.g3*self.gamma4
        self.E4 = T.e0*T.e1*T3.e2*self.e3

    # ---- eps3: Def 3.15 one more level up (reading C) ----
    def eps3(self, beta):
        s, u = eq12(beta, self.T3.e2, self.T3.h2)
        return self.K3["pow"](self.z3, self.l2p*s - self.l2*u)

    # ---- level-3 read VALUE at z3 (Def 3.16's inner evaluation, one up) ----
    def R3v(self, A):
        K3 = self.K3
        coeffs = self.T3.R3w(A)
        v = K3["zero"]; zp = K3["one"]
        for c in coeffs:
            if not self.T3.K2["isz"](c):
                v = K3["add"](v, K3["mul"](K3["embed"](c), zp))
            zp = K3["mul"](zp, self.z3)
        return v

    # ---- level-4 valuation ----
    def w4_data(self, f):
        d3 = dev(self.R, f, self.T3.Phi3)
        vals = [self.T3.w3(A) if A else INF for A in d3]
        if all(v == INF for v in vals):
            return d3, vals, INF
        g = min(self.e3*vals[j] + j*self.gamma4 for j in range(len(d3))
                if vals[j] < INF)
        return d3, vals, g
    def w4(self, f):
        return self.w4_data(f)[2]

    # ---- level-4 FGMN weight read (Def 3.16 at i = 4) ----
    def R4w(self, f, with_meta=False):
        K3 = self.K3
        d3, vals, g = self.w4_data(f)
        assert g < INF, "R4w of 0"
        s4, u4 = eq12(g, self.e3, self.h3)
        jmax = (len(d3)-1 - s4)//self.e3 if len(d3)-1 >= s4 else -1
        coeffs, online = [], []
        for j in range(jmax + 1):
            sj = s4 + j*self.e3
            A = d3[sj]
            num = g - sj*self.gamma4
            assert num % self.e3 == 0, "gamma_j not integral"
            gj = num // self.e3
            on = bool(A) and vals[sj] == gj
            if A and vals[sj] < gj:
                raise AssertionError("slot below the line: w4 min wrong")
            c = K3["mul"](self.eps3(gj), self.R3v(A)) if on else K3["zero"]
            coeffs.append(c); online.append(on)
        if with_meta:
            att = [i for i in range(len(d3)) if vals[i] < INF
                   and self.e3*vals[i] + i*self.gamma4 == g]
            return coeffs, dict(gamma=g, s4=s4, u4=u4, online=online,
                                s0=min(att), sprime=max(att))
        return coeffs
    def R4s(self, f):
        coeffs, meta = self.R4w(f, with_meta=True)
        j0 = 0
        while j0 < len(coeffs) and self.K3["isz"](coeffs[j0]): j0 += 1
        return fp_norm(self.K3, coeffs[j0:]), j0, meta

    # ---- realize a K3 class at level-3 weight beta (realize2 mirror) ----
    def realize3(self, tau, beta):
        T3 = self.T3; R = self.R
        s, u = eq12(beta, T3.e2, T3.h2)
        C = []
        for m in range(T3.g2):
            tm = tau[m] if m < len(tau) else T3.K2["zero"]
            if T3.K2["isz"](tm): continue
            k = s + m*T3.e2
            num = beta - k*T3.gamma3
            assert num % T3.e2 == 0
            gm = num // T3.e2
            tm_adj = T3.K2["mul"](T3.K2["inv"](T3.eps2(gm)), tm)
            C = padd(R, C, pmul(R, T3.realize2(tm_adj, gm),
                                ppow(R, T3.T.Phi2, k)))
        return C

    # ---- canonical state-key lift, one level up (build_Phi3 mirror) ----
    def build_Phi4(self):
        T3 = self.T3; R = self.R
        P = []
        for k, c in enumerate(self.psi3):
            if self.K3["isz"](c): continue
            gp = (self.g3 - k)*self.gamma4
            if gp == 0:
                Ck = [R["one"]]
            else:
                tau = self.K3["mul"](self.K3["inv"](self.eps3(gp)), c)
                Ck = self.realize3(tau, gp)
            P = padd(R, P, pmul(R, Ck, ppow(R, T3.Phi3, self.e3*k)))
        return P

# ---- the notes' PLAIN standard lift of psi2 (LIFT-DEV twin; level3_xcheck
#      LIFT recursion transcribed into harness types; d0 = 1 rows only) ----
def _lift0_plain(T, beta, xi):
    assert beta >= 0
    return pscal(T.R, T.R["pi_pow"](beta), T.liftK0(xi))
def _lift1_plain(T, beta, xi):
    R = T.R
    s, u = eq12(beta, T.e0, T.h0)
    C = []
    for m in range(T.g0):
        cm = xi[m] if m < len(xi) else T.K0["zero"]
        if T.K0["isz"](cm): continue
        C = padd(R, C, pmul(R, _lift0_plain(T, u - m*T.h0, cm),
                            ppow(R, T.Phi0, s + m*T.e0)))
    return C
def _lift2_plain(T3, beta, xi):
    T = T3.T; R = T.R
    s, u = eq12(beta, T.e1, T.h1)
    b0 = u - s*T.w1Phi1
    C = []
    for m in range(T.g1):
        cm = xi[m] if m < len(xi) else T.K1["zero"]
        if T.K1["isz"](cm): continue
        C = padd(R, C, pmul(R, _lift1_plain(T, b0 - m*T.gamma2, cm),
                            ppow(R, T.Phi1, s + m*T.e1)))
    return C
def build_Phi3_plain(T3):
    T = T3.T; R = T3.R
    P = []
    for k, c in enumerate(T3.psi2):
        if T3.K2["isz"](c): continue
        P = padd(R, P, pmul(R, _lift2_plain(T3, (T3.g2 - k)*T3.gamma3, c),
                            ppow(R, T.Phi2, T3.e2*k)))
    return P

# ============================ the level-4 prober ==============================
class Composite4:
    """Level-4 canonical-anchor composite prober for one Tower4 (Composite3
    mirror one level up).  with_shadow: also hold the SEALED level-3 prober
    Composite3(T4.T3) for the F0b / F-SUB / F-INF measured-shadow legs."""
    def __init__(self, T4, with_shadow=True):
        self.T4 = T4
        T3 = T4.T3; T = T3.T
        self.C3 = Composite3(T3) if with_shadow else None
        self.K4 = mk_field_ext(T4.K3, T4.psi3)
        self.zb4 = self.K4["z"]
        self.z3_4 = self.K4["embed"](T4.z3)
        self.z2_4 = self.K4["embed"](T4.K3["embed"](T3.z2))
        self.z1_4 = self.K4["embed"](T4.K3["embed"](T3.K2["embed"](T.z1)))
        E4 = T4.E4
        base = ((T4.e3 - 1)*T4.gamma4 + T4.e3*(T3.e2 - 1)*T3.gamma3
                + T4.e3*T3.e2*(T.e1 - 1)*T.gamma2 + E4*(T.e0 - 1)*T.h0 + E4)
        G0 = ((base + E4 - 1)//E4)*E4
        # deterministic window scan: u1 >= 0 on the whole needed range
        # (pairs AND associativity triples go up to 3*(G0 + 8*E4) + 2)
        while True:
            hi = 3*(G0 + 8*E4) + 2
            if all(self.split(g)[7] >= 0 for g in range(G0, hi + 1)):
                break
            G0 += E4
        self.Gamma0 = G0
        self._anch, self._aval, self._coc = {}, {}, {}

    def split(self, gamma):
        T4 = self.T4; T3 = T4.T3; T = T3.T
        s4, u4 = eq12(gamma, T4.e3, T4.h3)
        b3 = u4 - s4*T3.w3Phi3
        s3, u3 = eq12(b3, T3.e2, T3.h2)
        b2 = u3 - s3*T.w2Phi2
        s2, u2 = eq12(b2, T.e1, T.h1)
        b1 = u2 - s2*T.w1Phi1
        s1, u1 = eq12(b1, T.e0, T.h0)
        return s4, s3, s2, s1, b3, b2, b1, u1

    def anchor(self, gamma):
        if gamma in self._anch: return self._anch[gamma]
        T4 = self.T4; T3 = T4.T3; T = T3.T; R = T.R
        s4, s3, s2, s1, b3, b2, b1, u1 = self.split(gamma)
        assert u1 >= 0, f"window: gamma={gamma}, u1={u1}"
        f = pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1))
        f = pmul(R, f, ppow(R, T.Phi1, s2))
        f = pmul(R, f, ppow(R, T.Phi2, s3))
        f = pmul(R, f, ppow(R, T3.Phi3, s4))
        self._anch[gamma] = f
        return f

    def val4(self, f, want_meta=False):
        """K4 value of the level-4 weight read; also (nz-slots, gamma)."""
        T4 = self.T4; K4 = self.K4
        coeffs, m = T4.R4w(f, with_meta=True)
        v = K4["zero"]; zp = K4["one"]; nz = []
        for j, c in enumerate(coeffs):
            if not T4.K3["isz"](c):
                nz.append(j)
                v = K4["add"](v, K4["mul"](K4["embed"](c), zp))
            zp = K4["mul"](zp, self.zb4)
        if want_meta:
            return v, nz, m["gamma"]
        return v

    def anchor_val(self, gamma):
        if gamma in self._aval: return self._aval[gamma]
        v = self.val4(self.anchor(gamma))
        self._aval[gamma] = v
        return v

    def eps_chain(self, gamma):
        """K4-embedded eps3(b3)*eps2(b2)*eps1(b1) — the L6-4 prediction."""
        T4 = self.T4; T3 = T4.T3; T = T3.T
        _, _, _, _, b3, b2, b1, _ = self.split(gamma)
        e3v = T4.eps3(b3)
        e2v = T4.K3["embed"](T3.eps2(b2))
        e1v = T4.K3["embed"](T3.K2["embed"](T.eps1(b1)))
        return self.K4["embed"](T4.K3["mul"](e3v, T4.K3["mul"](e2v, e1v)))

    def constants(self, ga, gb):
        """All prereg-S1 constants for the pair (primary + ALT); None where
        non-integral."""
        T4 = self.T4; T3 = T4.T3; T = T3.T
        s4a, s3a, s2a, s1a, b3a, b2a, b1a, _ = self.split(ga)
        s4b, s3b, s2b, s1b, b3b, b2b, b1b, _ = self.split(gb)
        s4c, s3c, s2c, s1c, b3c, b2c, b1c, _ = self.split(ga + gb)
        d4 = (s4a + s4b)//T4.e3
        d3c = (s3a + s3b)//T3.e2
        d2c = (s2a + s2b)//T.e1
        d1c = (s1a + s1b)//T.e0
        # primary recursion
        S3 = d4*T4.gamma4
        numD3 = s3a + s3b - s3c + T4.l2*S3
        D3 = numD3//T3.e2 if numD3 % T3.e2 == 0 else None
        S2 = (None if D3 is None
              else D3*T3.gamma3 + S3*(T4.l2p - T4.l2*T.w2Phi2))
        numD2 = None if S2 is None else s2a + s2b - s2c + T.l1*S2
        D2 = (numD2//T.e1 if numD2 is not None and numD2 % T.e1 == 0
              else None)
        S1 = (None if D2 is None
              else D2*T.gamma2 + S2*(T.l1p - T.l1*T.w1Phi1))
        numD1 = None if S1 is None else s1a + s1b - s1c + T.l0*S1
        D1 = (numD1//T.e0 if numD1 is not None and numD1 % T.e0 == 0
              else None)
        # ALT: level-3-naive at the new level (S2 -> gamma3*d3c)
        S2n = T3.gamma3*d3c
        numD2n = s2a + s2b - s2c + T.l1*S2n
        D2n = numD2n//T.e1 if numD2n % T.e1 == 0 else None
        S1n = (None if D2n is None
               else D2n*T.gamma2 + S2n*(T.l1p - T.l1*T.w1Phi1))
        numD1n = None if S1n is None else s1a + s1b - s1c + T.l0*S1n
        D1n = (numD1n//T.e0 if numD1n is not None and numD1n % T.e0 == 0
               else None)
        return dict(d4=d4, d3c=d3c, d2c=d2c, d1c=d1c,
                    S3=S3, D3=D3, S2=S2, D2=D2, S1=S1, D1=D1,
                    S2n=S2n, D2n=D2n, S1n=S1n, D1n=D1n,
                    b3a=b3a, b3b=b3b, b3c=b3c, b2a=b2a, b2b=b2b,
                    b1a=b1a, b1b=b1b)

    def law_value(self, cst, which="primary"):
        """K4 value of the closed form; None if non-integral."""
        K4 = self.K4
        if which == "primary":
            D3, D2, D1 = cst["D3"], cst["D2"], cst["D1"]
        else:
            D3, D2, D1 = cst["D3"], cst["D2n"], cst["D1n"]
        if D3 is None or D2 is None or D1 is None:
            return None
        return K4["mul"](K4["pow"](self.zb4, cst["d4"]),
               K4["mul"](K4["pow"](self.z3_4, D3),
               K4["mul"](K4["pow"](self.z2_4, D2),
                         K4["pow"](self.z1_4, D1))))

    def cocycle(self, ga, gb):
        key = (ga, gb)
        if key in self._coc: return self._coc[key]
        K4 = self.K4
        prod = pmul(self.T4.R, self.anchor(ga), self.anchor(gb))
        vp, nz, gmeas = self.val4(prod, want_meta=True)
        vt = self.anchor_val(ga + gb)
        c = K4["mul"](vp, K4["inv"](vt))
        out = (c, vp, nz, gmeas)
        self._coc[key] = out
        return out

def k4_repr(C, v, cap=4096):
    """decompose v as zb4^a*z3^b*z2^c*z1^d if cheap, else 'raw'."""
    K4 = C.K4
    ords = [field_ord(K4, x) or 1
            for x in (C.zb4, C.z3_4, C.z2_4, C.z1_4)]
    total = 1
    for o in ords: total *= o
    if total > cap:
        return f"raw(ords={ords}):{v!r}"
    for a in range(ords[0]):
        za = K4["pow"](C.zb4, a)
        for b in range(ords[1]):
            zab = K4["mul"](za, K4["pow"](C.z3_4, b))
            for c in range(ords[2]):
                zabc = K4["mul"](zab, K4["pow"](C.z2_4, c))
                for d in range(ords[3]):
                    if K4["mul"](zabc, K4["pow"](C.z1_4, d)) == v:
                        return (f"zb4^{a}*z3^{b}*z2^{c}*z1^{d}"
                                if a or b or c or d else "1")
    return f"nonmonomial:{v!r}"

# ---------------------------------------------------------------------------
def run_tower(T4, results):
    T3 = T4.T3; T = T3.T
    tag = T4.tag; base = tag.split(",")[-1]
    reduced = is_reduced(T4.kind, base)
    C = Composite4(T4, with_shadow=True)
    C3 = C.C3
    K4, K3f, E4 = C.K4, T4.K3, T4.E4
    G0 = C.Gamma0
    wins = [list(range(G0 + k*E4, G0 + (k+1)*E4)) for k in (0, 1, 7)]
    W1, W2, W3 = wins
    mc = dict(md4=0, mid3=0, mid2=0, inn=0, trip=0, mv=0, msep4f=0,
              finfdev=0, jfloor=0, jceil=0)
    def k4emb3(v):    # K3-value -> K4
        return K4["embed"](v)
    # ---- F-SUB FIRST (the M4-R1 gate, law-free, measured vs measured):
    #      c4 on the (e3 Z)^2-subwindow == embed(MEASURED c3 of the subtower)
    subw = [g for g in W1 if g % T4.e3 == 0]
    for ga in subw:
        for gb in subw:
            note("FSUB")
            s4a = C.split(ga)[0]; s4b = C.split(gb)[0]
            if s4a != 0 or s4b != 0:
                viol("FSUB", tag, f"subwindow s4 != 0 at ({ga},{gb})")
                continue
            cval = C.cocycle(ga, gb)[0]
            c3m = C3.cocycle(ga//T4.e3, gb//T4.e3)[0]
            if cval != k4emb3(c3m):
                viol("FSUB", tag, f"F-SUB fails at ({ga},{gb}): measured "
                     f"{k4_repr(C, cval)} vs embed(c3 "
                     f"{k3_repr(C3, c3m)})")
    # ---- F0a: the ACCEPTED order-2 law on the level-2 subtower ----
    C2 = SP.Composite(T)
    W1_2 = list(range(C2.Gamma0, C2.Gamma0 + T.E2))
    for ga in W1_2:
        for gb in W1_2:
            note("F0a")
            c2m, _ = C2.cocycle(ga, gb)
            cf2, _ = closed_form2(C2, ga, gb)
            if cf2 is None or c2m != cf2:
                viol("F0a", tag, f"LEVEL-2 accepted law fails at ({ga},{gb})"
                                 " — HARNESS suspect")
    # ---- F0b: the measured (ITER-LAW-3) on the level-3 subtower (the sealed
    #      Composite3 + the sealed closed form, its own W x W block) ----
    W1_3 = list(range(C3.Gamma0, C3.Gamma0 + T3.E3))
    for ga in W1_3:
        for gb in W1_3:
            note("F0b")
            c3m = C3.cocycle(ga, gb)[0]
            lv3 = C3.law_value(C3.constants(ga, gb), "primary")
            if lv3 is None or c3m != lv3:
                viol("F0b", tag, f"(ITER-LAW-3) fails on subtower at "
                                 f"({ga},{gb}) — HARNESS suspect")
    # ---- G1: anchor values = eps-chain, windows ----
    for win in (wins if not reduced else [W1]):
        for g in win:
            note("G1")
            v = C.anchor_val(g)
            pred = C.eps_chain(g)
            if v != pred or K4["isz"](v):
                viol("G1", tag, f"ANCHOR-VAL-4 fails at gamma={g}")
    # ---- pair blocks: G2/G3/G4/G6/F-INF/F-J + meters ----
    blocks = ([(W1, W1), (W3, W3), (W1, W3)] if not reduced
              else [(W1, W1)])
    tbl1 = {}          # W1xW1 value table (for G7/F-CLASS/records)
    itab1 = {}         # W1xW1 integer table (for FROZEN)
    for A, B in blocks:
        for ga in A:
            for gb in B:
                cst = C.constants(ga, gb)
                d4, d3c, d2c, d1c = (cst["d4"], cst["d3c"], cst["d2c"],
                                     cst["d1c"])
                # meters
                if d4 == 1: mc["md4"] += 1
                if T3.g2 == 1 and d3c == 1: mc["mid3"] += 1
                if T.g1 == 1 and d2c == 1: mc["mid2"] += 1
                if T.g0 == 1 and d1c == 1: mc["inn"] += 1
                if (T3.g2 == 1 and d3c == 1 and T.g1 == 1 and d2c == 1
                        and T.g0 == 1 and d1c == 1):
                    mc["trip"] += 1
                # G2 PAIR-VAL both forms + single-top-slot shape
                note("G2")
                cval, vp, nz, gmeas = C.cocycle(ga, gb)
                if gmeas != ga + gb or nz != [d4]:
                    viol("G2", tag, f"shape at ({ga},{gb}): gamma={gmeas} "
                         f"(want {ga+gb}), nz={nz} (want [{d4}])")
                e3sum = T4.eps3(cst["b3a"] + cst["b3b"])
                e2sum = T4.K3["embed"](T3.eps2(cst["b2a"] + cst["b2b"]))
                e1sum = T4.K3["embed"](T3.K2["embed"](
                    T.eps1(cst["b1a"] + cst["b1b"])))
                predA = K4["mul"](K4["pow"](C.zb4, d4),
                        K4["mul"](K4["pow"](C.z3_4, d3c),
                        K4["mul"](K4["pow"](C.z2_4, d2c),
                        K4["mul"](K4["pow"](C.z1_4, d1c),
                                  K4["embed"](T4.K3["mul"](e3sum,
                                      T4.K3["mul"](e2sum, e1sum)))))))
                predB = K4["mul"](K4["pow"](C.zb4, d4),
                        K4["mul"](C.anchor_val(ga), C.anchor_val(gb)))
                if vp != predA:
                    viol("G2", tag, f"PAIR-VAL-4(a) fails at ({ga},{gb})")
                if vp != predB:
                    viol("G2", tag, f"PAIR-VAL-4(b) [W-MULT-4] fails at "
                                    f"({ga},{gb})")
                # G4 integrality (per-level warrants)
                note("G4")
                if cst["D3"] is None or cst["D2"] is None or cst["D1"] is None:
                    viol("G4", tag, f"integrality fails at ({ga},{gb}): "
                         f"D3={cst['D3']}, D2={cst['D2']}, D1={cst['D1']}")
                # G3 THE CANDIDATE
                note("G3")
                lawv = C.law_value(cst, "primary")
                if lawv is None or cval != lawv:
                    viol("G3", tag,
                         f"ITER-LAW-4 fails at ({ga},{gb}): measured "
                         f"{k4_repr(C, cval)}, cst="
                         f"{ {k: cst[k] for k in ('d4','d3c','d2c','d1c','D3','S2','D2','S1','D1','D2n','D1n')} }")
                if lawv is not None and lawv != K4["one"]:
                    mc["mv"] += 1
                # ALT comparison (recorded; NOT a primary violation)
                nv = C.law_value(cst, "alt")
                if nv is None or (lawv is not None and nv != lawv):
                    mc["msep4f"] += 1
                    note("ALTDIFF")
                    if d4 != 1:
                        note("ALTSEP_AT_D4_0")   # L1-analogue fence: pred 0
                        viol("MSEP0", tag,
                             f"ALT separation at d4=0 at ({ga},{gb})")
                if nv is None or cval != nv:
                    note("ALTVIOL")
                # F-J: the J-window at every rung (M3 leg promoted)
                if cst["D3"] is not None:
                    note("FJ3")
                    lo = (T4.l2*cst["S3"])//T3.e2
                    hi = -((-T4.l2*cst["S3"])//T3.e2)
                    J = cst["D3"] - d3c
                    if J not in (lo, hi):
                        viol("FJ3", tag, f"J3 window fails at ({ga},{gb}): "
                             f"J={J} not in [{lo},{hi}]")
                    else:
                        mc["jfloor" if J == lo else "jceil"] += 1
                if cst["D2"] is not None:
                    note("FJ2")
                    lo = (T.l1*cst["S2"])//T.e1
                    hi = -((-T.l1*cst["S2"])//T.e1)
                    if cst["D2"] - d2c not in (lo, hi):
                        viol("FJ2", tag, f"J2 window fails at ({ga},{gb})")
                if cst["D1"] is not None:
                    note("FJ1")
                    lo = (T.l0*cst["S1"])//T.e0
                    hi = -((-T.l0*cst["S1"])//T.e0)
                    if cst["D1"] - d1c not in (lo, hi):
                        viol("FJ1", tag, f"J1 window fails at ({ga},{gb})")
                # F-INF: inflation-defect identity vs the MEASURED level-3
                # shadow (M4-R2 one level up)
                b3a, b3b = cst["b3a"], cst["b3b"]
                okwin = all(C3.split(x)[5] >= 0
                            for x in (b3a, b3b, b3a + b3b))
                if not okwin:
                    note("FINFMISS")
                    viol("FINFMISS", tag,
                         f"F-INF shadow window miss at ({ga},{gb})")
                else:
                    note("FINF")
                    c3sh = C3.cocycle(b3a, b3b)[0]
                    cst3 = C3.constants(b3a, b3b)
                    d3s, D2s, D1s = cst3["d3"], cst3["D2"], cst3["D1"]
                    if D2s is None or D1s is None:
                        viol("FINF", tag, f"shadow constants non-integral "
                                          f"at ({ga},{gb})")
                    else:
                        pred = K4["mul"](K4["pow"](C.zb4, d4),
                               K4["mul"](k4emb3(c3sh),
                               K4["mul"](K4["pow"](C.z3_4, cst["D3"] - d3s),
                               K4["mul"](K4["pow"](C.z2_4, cst["D2"] - D2s),
                                   K4["pow"](C.z1_4, cst["D1"] - D1s)))))
                        if cval != pred:
                            viol("FINF", tag,
                                 f"inflation-defect identity fails at "
                                 f"({ga},{gb})")
                        devtup = (cst["D3"] - d3s, cst["D2"] - D2s,
                                  cst["D1"] - D1s)
                        if devtup != (0, 0, 0):
                            mc["finfdev"] += 1
                            if d4 == 0:
                                note("FINF0")
                                viol("FINF0", tag,
                                     f"shadow deviation at d4=0 at "
                                     f"({ga},{gb}): {devtup}")
                # G6 degeneration displays (every e_j = 1 rung)
                if 1 in (T.e0, T.e1, T3.e2, T4.e3):
                    note("G6")
                    ok = True
                    if T.e0 == 1 and cst["D1"] != 0: ok = False
                    if T.e1 == 1 and not (cst["D2"] == 0
                                          and cst["S1"] == cst["S2"]):
                        ok = False
                    if T3.e2 == 1 and not (cst["D3"] == 0
                                           and cst["S2"] == cst["S3"]):
                        ok = False
                    if T4.e3 == 1:
                        # measured level-3 law two ways (M3-S3 style)
                        cst3 = C3.constants(ga, gb)
                        if not (d4 == 0
                                and cst["D3"] == cst3["d3"]
                                and cst["D2"] == cst3["D2"]
                                and cst["D1"] == cst3["D1"]):
                            ok = False           # way 1: split-chain verbatim
                        elif cval != k4emb3(C3.cocycle(ga, gb)[0]):
                            ok = False           # way 2: value tie
                    if T3.e2 == 1 and T4.e3 >= 2 and cst["D2"] is not None:
                        # C2 display: the (ITER-LAW-3) FORM with gamma3->gamma4
                        s2def = cst["D2"]*T.e1 - T.l1*cst["S2"]
                        numD2f = s2def + T.l1*T4.gamma4*d4
                        if numD2f % T.e1 != 0 or numD2f//T.e1 != cst["D2"]:
                            ok = False
                    if not ok:
                        viol("G6", tag, f"degeneration display fails at "
                                        f"({ga},{gb})")
                # tables
                if A is W1 and B is W1:
                    r, s = ga - G0, gb - G0
                    tbl1[(r, s)] = cval
                    itab1[(r, s)] = (d4, cst["D3"], cst["D2"], cst["D1"])
    # ---- G5 associativity (measured AND closed), skipped on reduced ----
    if not reduced:
        triples = [(a, b, t) for a in W1 for b in W1 for t in W1]
        if len(triples) > 216:
            triples = random.sample(triples, 216)
        for (a, b, t) in triples:
            note("G5")
            lhs = K4["mul"](C.cocycle(a, b)[0], C.cocycle(a + b, t)[0])
            rhs = K4["mul"](C.cocycle(b, t)[0], C.cocycle(a, b + t)[0])
            if lhs != rhs:
                viol("G5", tag, f"cocycle identity (measured) fails at "
                                f"({a},{b},{t})")
            parts = [C.law_value(C.constants(x, y), "primary")
                     for (x, y) in ((a, b), (a + b, t), (b, t), (a, b + t))]
            if any(pp is None for pp in parts):
                viol("G5", tag, f"closed form non-integral at ({a},{b},{t})")
            elif K4["mul"](parts[0], parts[1]) != K4["mul"](parts[2], parts[3]):
                viol("G5", tag, f"cocycle identity (closed) fails at "
                                f"({a},{b},{t})")
        # quotient-table triple identity (window AND quotient, M2 lane)
        for _ in range(216):
            r = random.randrange(E4); s = random.randrange(E4)
            t = random.randrange(E4)
            note("G5")
            lhs = K4["mul"](tbl1[(r, s)], tbl1[((r + s) % E4, t)])
            rhs = K4["mul"](tbl1[(s, t)], tbl1[(r, (s + t) % E4)])
            if lhs != rhs:
                viol("G5", tag, f"QUOTIENT cocycle identity fails at "
                                f"({r},{s},{t})")
        # swap symmetry on the quotient table
        for (r, s) in list(tbl1):
            note("GSWAP")
            if tbl1[(r, s)] != tbl1[(s, r)]:
                viol("GSWAP", tag, f"swap symmetry fails at ({r},{s})")
    # ---- G7 Z/E4 descent: simultaneous AND 4 MIXED blocks ----
    if not reduced:
        def table(wa, wb):
            return {(r, s): C.cocycle(wa[r], wb[s])[0]
                    for r in range(E4) for s in range(E4)}
        for name, wa, wb in (("W2xW2", W2, W2), ("W3xW3", W3, W3),
                             ("W2xW1", W2, W1), ("W1xW2", W1, W2),
                             ("W3xW1", W3, W1), ("W1xW3", W1, W3)):
            t = table(wa, wb)
            for k in tbl1:
                note("G7")
                if t[k] != tbl1[k]:
                    viol("G7", tag, f"descent fails: block {name} at {k}")
    # ---- F-CLASS: kappa_Z + the (INV-4) H^2-class monomial (M2 leg) ----
    note("FCLASSK")
    kZ = sum(itab1[(k, 1)][0] for k in range(E4))
    kZ_pred = (E4//T4.e3)*T4.l3
    if kZ != kZ_pred:
        viol("FCLASSK", tag, f"kappa_Z(d4-table) = {kZ} != (E4/e3)*l3 = "
                             f"{kZ_pred}")
    note("FCLASSS")
    sig = K4["one"]
    for k in range(E4):
        sig = K4["mul"](sig, tbl1[(k, 1)])
    invm = K4["mul"](K4["pow"](C.zb4, (E4//T4.e3)*T4.l3),
           K4["mul"](K4["pow"](C.z3_4, T.e0*T.e1*T4.l2),
           K4["mul"](K4["pow"](C.z2_4, T.e0*T.l1),
                     K4["pow"](C.z1_4, T.l0))))
    ords = [field_ord(K4, x) or 1 for x in (C.zb4, C.z3_4, C.z2_4, C.z1_4)]
    m = 1
    for o in ords: m = m*o//math.gcd(m, o)
    x = K4["mul"](sig, K4["inv"](invm))
    ok_class = (K4["pow"](x, m//math.gcd(m, E4)) == K4["one"])
    if not ok_class:
        viol("FCLASSS", tag, "sigma(c4) != INV-4 monomial mod M^{E4}")
    top = K4["pow"](C.zb4, (E4//T4.e3)*T4.l3)
    top_escapes = (K4["pow"](top, m//math.gcd(m, E4)) != K4["one"])
    results["class"][tag] = dict(kappaZ=kZ, kappaZ_pred=kZ_pred,
                                 letter_ords=ords, m=m,
                                 class_ok=bool(ok_class),
                                 field_blind=(m == 1),
                                 top_escapes_ME4=bool(top_escapes))
    # ---- records ----
    if base in ("P", "R"):
        vals = sorted({k4_repr(C, v) for v in tbl1.values()
                       if v != K4["one"]})
        results["valuesets"][tag] = vals
    if base in ("A4", "P"):
        results["itabs"][tag] = {f"{r},{s}": list(v)
                                 for (r, s), v in itab1.items()}
    results["meters"][tag] = mc
    results["Gamma0"][tag] = G0

# ---------------------------------------------------------------------------
def g8_symbolic4(n=20000):
    """Integer layer, pure Z: L1 at all four levels, INNER-SHIFT-4, the two
    composed-shift identities, D3/D2/D1 integrality, generalized EXP at all
    three sub-levels, J-windows, NO-cross-level-denominator phantom counters;
    MSEP4i + ALT nonintegrality census."""
    msep4i = 0; altni = 0; phantom = 0
    for _ in range(n):
        note("G8")
        e0 = random.randrange(1, 13)
        h0 = random.choice([h for h in range(1, 40) if math.gcd(h, e0) == 1])
        e1 = random.randrange(1, 13)
        h1 = random.choice([h for h in range(1, 40) if math.gcd(h, e1) == 1])
        e2 = random.randrange(1, 13)
        h2 = random.choice([h for h in range(1, 40) if math.gcd(h, e2) == 1])
        e3 = random.randrange(1, 13)
        h3 = random.choice([h for h in range(1, 40) if math.gcd(h, e3) == 1])
        g0 = random.randrange(1, 5); g1 = random.randrange(1, 5)
        g2 = random.randrange(1, 5)
        l0, l0p = bezout(e0, h0); l1, l1p = bezout(e1, h1)
        l2, l2p = bezout(e2, h2)
        w1P = e0*g0*h0; gam2 = e1*w1P + h1
        w2P = e1*g1*gam2; gam3 = e2*w2P + h2
        w3P = e2*g2*gam3; gam4 = e3*w3P + h3
        ga = random.randrange(-3000, 3001)
        gb = random.randrange(-3000, 3001)
        def split4(g):
            s4, u4 = eq12(g, e3, h3); b3 = u4 - s4*w3P
            s3, u3 = eq12(b3, e2, h2); b2 = u3 - s3*w2P
            s2, u2 = eq12(b2, e1, h1); b1 = u2 - s2*w1P
            s1, u1 = eq12(b1, e0, h0)
            return s4, s3, s2, s1, b3, b2, b1
        s4a, s3a, s2a, s1a, b3a, b2a, b1a = split4(ga)
        s4b, s3b, s2b, s1b, b3b, b2b, b1b = split4(gb)
        s4c, s3c, s2c, s1c, b3c, b2c, b1c = split4(ga + gb)
        d4 = (s4a + s4b)//e3
        if d4 not in (0, 1) or s4c != s4a + s4b - d4*e3:
            viol("G8", "symbolic", f"L1(lvl4) fails {(e3,h3,ga,gb)}"); continue
        if b3c != b3a + b3b + d4*gam4:
            viol("G8", "symbolic", f"INNER-SHIFT-4 fails {(e3,h3,ga,gb)}")
            continue
        S3 = d4*gam4
        numD3 = s3a + s3b - s3c + l2*S3
        if numD3 % e2 != 0:
            if numD3 % (e2*e1) == 0: phantom += 1
            viol("G8", "symbolic",
                 f"D3 non-integral {(e0,h0,e1,h1,e2,h2,e3,h3,ga,gb)}")
            continue
        D3 = numD3//e2
        S2 = D3*gam3 + S3*(l2p - l2*w2P)
        if b2c != b2a + b2b + S2:
            viol("G8", "symbolic", f"composed shift (rung 2) fails "
                 f"{(e1,h1,e2,h2,e3,h3,ga,gb)}: b2''-b2-b2'="
                 f"{b2c-b2a-b2b} vs S2={S2}")
            continue
        numD2 = s2a + s2b - s2c + l1*S2
        if numD2 % e1 != 0:
            if numD2 % (e1*e0) == 0: phantom += 1
            viol("G8", "symbolic",
                 f"D2 non-integral {(e0,h0,e1,h1,e2,h2,e3,h3,ga,gb)}")
            continue
        D2 = numD2//e1
        S1 = D2*gam2 + S2*(l1p - l1*w1P)
        if b1c != b1a + b1b + S1:
            viol("G8", "symbolic", f"composed shift (rung 1) fails "
                 f"{(e0,h0,e1,h1,e2,h2,e3,h3,ga,gb)}")
            continue
        numD1 = s1a + s1b - s1c + l0*S1
        if numD1 % e0 != 0:
            viol("G8", "symbolic",
                 f"D1 non-integral {(e0,h0,e1,h1,e2,h2,e3,h3,ga,gb)}")
            continue
        D1 = numD1//e0
        # generalized EXP at the three sub-levels (exponent assembly)
        d3carry = (s3a + s3b)//e2
        ssum3, _ = eq12(b3a + b3b, e2, h2)
        if d3carry + ((ssum3 - l2*(b3a + b3b)) - (s3c - l2*b3c))//e2 != D3:
            viol("G8", "symbolic", f"EXP(rung3) fails {(e2,h2,ga,gb)}")
            continue
        d2carry = (s2a + s2b)//e1
        ssum2, _ = eq12(b2a + b2b, e1, h1)
        if d2carry + ((ssum2 - l1*(b2a + b2b)) - (s2c - l1*b2c))//e1 != D2:
            viol("G8", "symbolic", f"EXP(rung2) fails {(e1,h1,ga,gb)}")
            continue
        d1carry = (s1a + s1b)//e0
        ssum1, _ = eq12(b1a + b1b, e0, h0)
        if d1carry + ((ssum1 - l0*(b1a + b1b)) - (s1c - l0*b1c))//e0 != D1:
            viol("G8", "symbolic", f"EXP(rung1) fails {(e0,h0,ga,gb)}")
            continue
        # J-windows, symbolic leg
        for (D, dc, l, S, e) in ((D3, d3carry, l2, S3, e2),
                                 (D2, d2carry, l1, S2, e1),
                                 (D1, d1carry, l0, S1, e0)):
            if D - dc not in ((l*S)//e, -((-l*S)//e)):
                viol("G8", "symbolic", f"J-window fails {(e,l,S,D,dc)}")
                break
        # separation census
        if S2 != gam3*d3carry:
            msep4i += 1
        numD2n = s2a + s2b - s2c + l1*gam3*d3carry
        if numD2n % e1 != 0:
            altni += 1
    return msep4i, altni, phantom

# ---------------------------------------------------------------------------
def cert3_internal4(T3, tag):
    """Level-3 data certification (transcribed verbatim from the sealed
    iterlawr_probe.cert3_internal, local counters): psi2 + Phi3 shape +
    R3s(Phi3) == psi2."""
    T, R, K2t = T3.T, T3.R, T3.K2
    note("CERT3")
    ok = True
    if math.gcd(T3.e2, T3.h2) != 1: ok = False
    if K2t["isz"](T3.psi2[0]): ok = False
    if T3.psi2[-1] != K2t["one"]: ok = False
    if not S3MOD._no_root(K2t, T3.psi2) and T3.g2 >= 2: ok = False
    if not ok:
        viol("CERT3", tag, "psi2 data bad (gcd/const/monic/irred)")
    P3 = T3.Phi3
    if len(P3) - 1 != T3.degPhi3:
        viol("CERT3", tag, f"deg Phi3 = {len(P3)-1} != {T3.degPhi3}")
    lead = P3[-1] if P3 else R["zero"]
    if R["isz"](lead) or not R["isz"](R["add"](lead, R["neg"](R["one"]))):
        viol("CERT3", tag, "Phi3 not monic")
    d2v, vals, g = T3.w3_data(P3)
    if g != T3.w3Phi3:
        viol("CERT3", tag, f"w3(Phi3) = {g} != {T3.w3Phi3}")
    for j, c in enumerate(d2v):
        if c and T3.e2*vals[j] + j*T3.gamma3 < T3.w3Phi3:
            viol("CERT3", tag, f"Phi3 slot {j} below weight")
    side, j0, _ = T3.R3s(P3)
    if j0 != 0 or side != fp_norm(K2t, T3.psi2):
        viol("CERT3", tag, "R3s(Phi3) != psi2 exactly")

def cert4_internal(T4):
    """Level-4 data certification (cert3 mirror one level up): psi3 + Phi4
    shape + R4s(Phi4) == psi3 (the V4 key check two levels up)."""
    T3, R, K3t = T4.T3, T4.R, T4.K3
    tag = T4.tag
    note("CERT4")
    ok = True
    if math.gcd(T4.e3, T4.h3) != 1: ok = False
    if K3t["isz"](T4.psi3[0]): ok = False
    if T4.psi3[-1] != K3t["one"]: ok = False
    if not S3MOD._no_root(K3t, T4.psi3) and T4.g3 >= 2: ok = False
    if not ok:
        viol("CERT4", tag, "psi3 data bad (gcd/const/monic/irred)")
    P4 = T4.Phi4
    if len(P4) - 1 != T4.degPhi4:
        viol("CERT4", tag, f"deg Phi4 = {len(P4)-1} != {T4.degPhi4}")
    lead = P4[-1] if P4 else R["zero"]
    if R["isz"](lead) or not R["isz"](R["add"](lead, R["neg"](R["one"]))):
        viol("CERT4", tag, "Phi4 not monic")
    d3v, vals, g = T4.w4_data(P4)
    if g != T4.w4Phi4:
        viol("CERT4", tag, f"w4(Phi4) = {g} != {T4.w4Phi4}")
    for j, c in enumerate(d3v):
        if c and T4.e3*vals[j] + j*T4.gamma4 < T4.w4Phi4:
            viol("CERT4", tag, f"Phi4 slot {j} below weight")
    side, j0, _ = T4.R4s(P4)
    if j0 != 0 or side != fp_norm(K3t, T4.psi3):
        viol("CERT4", tag, "R4s(Phi4) != psi3 exactly")

def cert4_pari(T4, pari):
    """PARI leg (Z_p rows): Phi4 irreducible over Q_p (degPhi4 <= 64) and
    (e,f) = (E4, d0*g0*g1*g2*g3) via p-maximal nfinit (degPhi4 <= 32).
    Q/MUA/MUB exceed the caps: preregistered deferrals, counted."""
    if T4.kind != "Zp" or pari is None: return
    base = T4.tag.split(",")[-1]
    if base in CERT4P_SKIP:
        note("CERT4P_DEFER"); return
    note("CERT4P")
    T3 = T4.T3; T = T3.T
    coeffs = [int(c) for c in T4.Phi4]
    F = pari.Pol(list(reversed(coeffs)))
    fac = pari.factorpadic(F, T4.p, 120)
    if len(fac[0]) != 1 or int(fac[1][0]) != 1:
        viol("CERT4P", T4.tag, f"PARI: Phi4 NOT irreducible over Q_{T4.p}")
        return
    if T4.degPhi4 > 32: return
    nf = pari.nfinit([F, [T4.p]])
    dec = pari.idealprimedec(nf, T4.p)
    e_pred, f_pred = T4.E4, T.d0*T.g0*T.g1*T3.g2*T4.g3
    if len(dec) != 1:
        viol("CERT4P", T4.tag, f"PARI: {len(dec)} primes above p (pred 1)")
        return
    pr = dec[0]
    if (int(pr[2]), int(pr[3])) != (e_pred, f_pred):
        viol("CERT4P", T4.tag, f"PARI (e,f) = ({int(pr[2])},{int(pr[3])}) "
                               f"!= pred ({e_pred},{f_pred})")

# ---------------------------------------------------------------------------
# MUTATION CONTROLS (post-battery, sealed; all-letters rows MUA/MUB; each
# mutation must be detected at FIELD level (>= 1) AND at WARRANT (integer)
# level (>= 1); m4 additionally carries the STRUCTURAL top-slot leg.
def mutated_value4(C, cst, mut):
    """(d4m, D3m, D2m, D1m) after the mutation, or 'NONINT' (detection), or
    ('swap', ...) for m6."""
    T4 = C.T4; T3 = T4.T3; T = T3.T
    d4, d3c = cst["d4"], cst["d3c"]
    if cst["D3"] is None or cst["D2"] is None or cst["D1"] is None:
        return None
    s3def = cst["D3"]*T3.e2 - T4.l2*cst["S3"]
    s2def = cst["D2"]*T.e1 - T.l1*cst["S2"]
    s1def = cst["D1"]*T.e0 - T.l0*cst["S1"]
    def chain(D3m, S3m):
        S2m = D3m*T3.gamma3 + S3m*(T4.l2p - T4.l2*T.w2Phi2)
        numD2 = s2def + T.l1*S2m
        if numD2 % T.e1 != 0: return "NONINT"
        D2m = numD2//T.e1
        S1m = D2m*T.gamma2 + S2m*(T.l1p - T.l1*T.w1Phi1)
        numD1 = s1def + T.l0*S1m
        if numD1 % T.e0 != 0: return "NONINT"
        return (d4, D3m, D2m, numD1//T.e0)
    if mut == "m1":       # drop l2*gamma4*d4 from D3 (chain follows)
        numD3 = s3def
        if numD3 % T3.e2 != 0: return "NONINT"
        return chain(numD3//T3.e2, cst["S3"])
    if mut == "m2":       # ALT: naive composed shift at the new level
        S2m = T3.gamma3*d3c
        numD2 = s2def + T.l1*S2m
        if numD2 % T.e1 != 0: return "NONINT"
        D2m = numD2//T.e1
        S1m = D2m*T.gamma2 + S2m*(T.l1p - T.l1*T.w1Phi1)
        numD1 = s1def + T.l0*S1m
        if numD1 % T.e0 != 0: return "NONINT"
        return (d4, cst["D3"], D2m, numD1//T.e0)
    if mut == "m3":       # D3 denominator e2 -> e1
        numD3 = s3def + T4.l2*cst["S3"]
        if numD3 % T.e1 != 0: return "NONINT"
        return chain(numD3//T.e1, cst["S3"])
    if mut == "m4":       # d4 modulus e3 -> e2 (exponents kept primary)
        d4m = None        # computed by caller (needs both s4 splits)
        return ("d4mut",)
    if mut == "m6":       # letter swap z3 <-> z2
        return ("swap", cst["D3"], cst["D2"], cst["D1"])
    return None

def mutation_controls4(results):
    """Field + warrant (+ m4 structural) detection on MUA/MUB over
    MUT_CONFIGS.  Detection = mutated closed form differs from the MEASURED
    cocycle (field) / mutated integer constants differ from primary or lose
    integrality (warrant) / measured top slot != mutated d4 (structural)."""
    muts = ("m1", "m2", "m3", "m4", "m5", "m6")
    detf = {m: 0 for m in muts}
    detw = {m: 0 for m in muts}
    dets = {"m4": 0}
    tested = {m: 0 for m in muts}
    perrow = {}
    for kind, p in MUT_CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            if tag not in MUT_ROWS: continue
            full = f"{kind},p={p},{tag}"
            T4 = Tower4(kind, p, d0, r0, r1, r2, r3, full)
            C = Composite4(T4, with_shadow=False)
            T3 = T4.T3; T = T3.T; K4 = C.K4; E4 = T4.E4
            W1 = list(range(C.Gamma0, C.Gamma0 + E4))
            rowdet = {m: 0 for m in muts}
            # m5: anchor prediction without eps3
            for g in W1:
                tested["m5"] += 1
                v = C.anchor_val(g)
                _, _, _, _, b3, b2, b1, _ = C.split(g)
                bad = K4["embed"](T4.K3["mul"](
                    T4.K3["embed"](T3.eps2(b2)),
                    T4.K3["embed"](T3.K2["embed"](T.eps1(b1)))))
                if v != bad:
                    detf["m5"] += 1; rowdet["m5"] += 1
                if T4.eps3(b3) != T4.K3["one"]:
                    detw["m5"] += 1     # warrant: eps3 genuinely nontrivial
            for ga in W1:
                for gb in W1:
                    cval, vp, nz, gmeas = C.cocycle(ga, gb)
                    cst = C.constants(ga, gb)
                    prim = (cst["d4"], cst["D3"], cst["D2"], cst["D1"])
                    for m in ("m1", "m2", "m3", "m6"):
                        tested[m] += 1
                        mv = mutated_value4(C, cst, m)
                        if mv == "NONINT":
                            detf[m] += 1; detw[m] += 1; rowdet[m] += 1
                            continue
                        if mv is None:
                            continue
                        if mv[0] == "swap":
                            if (mv[1], mv[2]) != (mv[2], mv[1]):
                                detw[m] += 1
                            val = K4["mul"](K4["pow"](C.zb4, cst["d4"]),
                                  K4["mul"](K4["pow"](C.z2_4, mv[1]),
                                  K4["mul"](K4["pow"](C.z3_4, mv[2]),
                                            K4["pow"](C.z1_4, mv[3]))))
                        else:
                            if mv != prim:
                                detw[m] += 1
                            val = K4["mul"](K4["pow"](C.zb4, mv[0]),
                                  K4["mul"](K4["pow"](C.z3_4, mv[1]),
                                  K4["mul"](K4["pow"](C.z2_4, mv[2]),
                                            K4["pow"](C.z1_4, mv[3]))))
                        if val != cval:
                            detf[m] += 1; rowdet[m] += 1
                    # m4: d4 with wrong modulus e2, + structural top-slot leg
                    tested["m4"] += 1
                    s4a = C.split(ga)[0]; s4b = C.split(gb)[0]
                    d4m = (s4a + s4b)//T3.e2
                    if d4m != cst["d4"]:
                        detw["m4"] += 1
                        if nz != [d4m]:
                            dets["m4"] += 1      # fires even at zb4 = 1
                        val = K4["mul"](K4["pow"](C.zb4, d4m),
                              K4["mul"](K4["pow"](C.z3_4, cst["D3"]),
                              K4["mul"](K4["pow"](C.z2_4, cst["D2"]),
                                        K4["pow"](C.z1_4, cst["D1"]))))
                        if val != cval:
                            detf["m4"] += 1; rowdet["m4"] += 1
            perrow[full] = rowdet
    results["mutations"] = dict(field=detf, warrant=detw,
                                structural=dets, tested=tested,
                                perrow=perrow)
    return detf, detw, dets

# ---------------------------------------------------------------------------
# LIFT-DEV-4 secondary leg: plain-Phi3 twin vs canonical, factor
# eps2(gamma3)^{d3c} at g2 = 1 (LD1/LD2), invariance at g2 = 2 (LD3).
def run_liftdev(results):
    ldvis = 0
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            if tag not in LD_DEV_ROWS + LD_INV_ROWS: continue
            full = f"{kind},p={p},{tag}"
            try:
                T4c = Tower4(kind, p, d0, r0, r1, r2, r3, full + "/canon")
                T4p = Tower4(kind, p, d0, r0, r1, r2, r3, full + "/plain",
                             phi3_plain=True)
                Cc = Composite4(T4c, with_shadow=False)
                Cp = Composite4(T4p, with_shadow=False)
                assert Cc.Gamma0 == Cp.Gamma0, "LD window mismatch"
                K4 = Cc.K4; E4 = T4c.E4
                T3c = T4c.T3
                # LDCERT: plain Phi3 sanity (deg, monic, w3; NOT the R3s key)
                note("LDCERT")
                P3p = T4p.T3.Phi3
                lead = P3p[-1] if P3p else T4p.R["zero"]
                okc = (len(P3p) - 1 == T4p.T3.degPhi3
                       and not T4p.R["isz"](lead)
                       and T4p.R["isz"](T4p.R["add"](lead,
                                        T4p.R["neg"](T4p.R["one"])))
                       and T4p.T3.w3(P3p) == T4p.T3.w3Phi3)
                if not okc:
                    viol("LDCERT", full, "plain Phi3 shape bad")
                phi_differs = (list(P3p) != list(T3c.Phi3))
                fac_pred_base = K4["embed"](T4c.K3["embed"](
                    T3c.eps2(T3c.gamma3)))
                W1 = list(range(Cc.Gamma0, Cc.Gamma0 + E4))
                ndev = 0
                for ga in W1:
                    for gb in W1:
                        cc = Cc.cocycle(ga, gb)[0]
                        cp = Cp.cocycle(ga, gb)[0]
                        fac = K4["mul"](cp, K4["inv"](cc))
                        cst = Cc.constants(ga, gb)
                        if tag in LD_DEV_ROWS:
                            note("LDDEV")
                            pred = K4["pow"](fac_pred_base, cst["d3c"])
                            if fac != pred:
                                viol("LDDEV", full,
                                     f"c4^plain/c4^canon at ({ga},{gb}) != "
                                     f"eps2(gamma3)^{cst['d3c']}")
                            if pred != K4["one"]:
                                ldvis += 1
                            if fac != K4["one"]:
                                ndev += 1
                        else:
                            note("LDINV")
                            if fac != K4["one"]:
                                viol("LDINV", full,
                                     f"plain-lift NON-invariance at g2=2, "
                                     f"({ga},{gb})")
                results["liftdev"][full] = dict(
                    phi3_differs=phi_differs, deviating_pairs=ndev)
            except Exception as exc:
                HARNESS_EVENTS.append((full, "LIFTDEV", repr(exc)))
    results["liftdev"]["LDVIS"] = ldvis
    return ldvis

# ---------------------------------------------------------------------------
def design_mode():
    """Construction + constants + letter orders + design-time visibility of
    every mutated constant and of the LIFT-DEV factor + cost probe.  NO law
    comparison, NO val4/anchor value of anything (predictions only)."""
    t0 = time.time()
    print("DESIGN MODE: tower constants (no law evaluation, no measured value)")
    print(f"{'tower':16} {'E4':>3} {'g2c':>4} {'g3c':>5} {'g4c':>6} {'G0':>7} "
          f"{'degF4':>6} {'l0':>3} {'l1':>3} {'l2':>3} {'l3':>3} "
          f"{'ord(zb4,z3,z2,z1)':>20}")
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            full = f"{kind},p={p},{tag}"
            T4 = Tower4(kind, p, d0, r0, r1, r2, r3, full)
            C = Composite4(T4, with_shadow=False)
            T3 = T4.T3; T = T3.T
            ords = tuple(field_ord(C.K4, x) or 1
                         for x in (C.zb4, C.z3_4, C.z2_4, C.z1_4))
            print(f"{full:16} {T4.E4:>3} {T.gamma2:>4} {T3.gamma3:>5} "
                  f"{T4.gamma4:>6} {C.Gamma0:>7} {T4.degPhi4:>6} "
                  f"{T.l0:>3} {T.l1:>3} {T4.l2:>3} {T4.l3:>3} "
                  f"{str(ords):>20}")
    print(f"[{time.time()-t0:6.1f}s] all towers constructed")
    # mutation design-time visibility (m4-lesson institutionalized): counts
    # of INTEGER divergence and PREDICTED-FIELD divergence per mutation, on
    # the mutation battery rows — predictions only, no measured values.
    print("MUTATION DESIGN VISIBILITY (int-div pairs / field-visible pairs):")
    for kind, p in MUT_CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            if tag not in MUT_ROWS: continue
            full = f"{kind},p={p},{tag}"
            T4 = Tower4(kind, p, d0, r0, r1, r2, r3, full)
            C = Composite4(T4, with_shadow=False)
            T3 = T4.T3; T = T3.T; K4 = C.K4
            W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
            out = {}
            for m in ("m1", "m2", "m3", "m4", "m6"):
                ci = cf = 0
                for ga in W1:
                    for gb in W1:
                        cst = C.constants(ga, gb)
                        if cst["D1"] is None: continue
                        prim = (cst["d4"], cst["D3"], cst["D2"], cst["D1"])
                        pv = C.law_value(cst, "primary")
                        if m == "m4":
                            s4a = C.split(ga)[0]; s4b = C.split(gb)[0]
                            d4m = (s4a + s4b)//T3.e2
                            if d4m == cst["d4"]: continue
                            ci += 1
                            mv4 = K4["mul"](K4["pow"](C.zb4, d4m),
                                  K4["mul"](K4["pow"](C.z3_4, cst["D3"]),
                                  K4["mul"](K4["pow"](C.z2_4, cst["D2"]),
                                            K4["pow"](C.z1_4, cst["D1"]))))
                            if mv4 != pv: cf += 1
                            continue
                        mv = mutated_value4(C, cst, m)
                        if mv == "NONINT":
                            ci += 1; cf += 1; continue
                        if mv is None: continue
                        if mv[0] == "swap":
                            if cst["D3"] == cst["D2"]: continue
                            ci += 1
                            val = K4["mul"](K4["pow"](C.zb4, cst["d4"]),
                                  K4["mul"](K4["pow"](C.z2_4, mv[1]),
                                  K4["mul"](K4["pow"](C.z3_4, mv[2]),
                                            K4["pow"](C.z1_4, mv[3]))))
                        else:
                            if mv == prim: continue
                            ci += 1
                            val = K4["mul"](K4["pow"](C.zb4, mv[0]),
                                  K4["mul"](K4["pow"](C.z3_4, mv[1]),
                                  K4["mul"](K4["pow"](C.z2_4, mv[2]),
                                            K4["pow"](C.z1_4, mv[3]))))
                        if val != pv: cf += 1
                out[m] = (ci, cf)
            # m5 visibility: anchors with eps3(b3) != 1 (prediction only)
            c5 = sum(1 for g in W1
                     if T4.eps3(C.split(g)[4]) != T4.K3["one"])
            out["m5"] = (c5, c5)
            print(f"  {full:16} " + "  ".join(
                f"{m}:{out[m][0]}/{out[m][1]}" for m in
                ("m1", "m2", "m3", "m4", "m5", "m6")))
    # LIFT-DEV design visibility: eps2(gamma3) order + d3c=1 pair count
    print("LIFT-DEV DESIGN VISIBILITY (eps2(gamma3) != 1?, d3c=1 pairs):")
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            if tag not in LD_DEV_ROWS: continue
            full = f"{kind},p={p},{tag}"
            T4 = Tower4(kind, p, d0, r0, r1, r2, r3, full)
            C = Composite4(T4, with_shadow=False)
            T3 = T4.T3
            ev = T3.eps2(T3.gamma3)
            nontriv = (ev != T3.K2["one"])
            W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
            nd3 = sum(1 for ga in W1 for gb in W1
                      if C.constants(ga, gb)["d3c"] == 1)
            print(f"  {full:16} eps2(gamma3)!=1: {nontriv}   "
                  f"d3c=1 pairs: {nd3}")
    # cost probe (disclosed): pmul + dev cost on the heaviest rows; no read,
    # no value, no comparison.
    print("COST PROBE (pmul(anchor,anchor)+dev by Phi3; seconds/pair core op):")
    for tag in ("Q", "MUB", "T"):
        for kind, p in CONFIGS:
            row = next(r for r in ROWS if r[0] == tag)
            full = f"{kind},p={p},{tag}"
            T4 = Tower4(kind, p, row[1], row[2], row[3], row[4], row[5], full)
            C = Composite4(T4, with_shadow=False)
            a1 = C.anchor(C.Gamma0 + T4.E4 - 1)
            a2 = C.anchor(C.Gamma0 + T4.E4 - 2)
            tt = time.time()
            for _ in range(3):
                pr = pmul(T4.R, a1, a2)
                dev(T4.R, pr, T4.T3.Phi3)
            dt = (time.time() - tt)/3
            print(f"  {full:16} {dt*1000:8.1f} ms")
    print(f"[{time.time()-t0:6.1f}s] design OK: all towers constructed, "
          "windows scanned, visibility verified")

# ---------------------------------------------------------------------------
def main():
    if "--design" in sys.argv:
        design_mode(); return 0
    t0 = time.time()
    random.seed(20260905)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); PARI legs skipped "
              "-> RED if predicted")
    results = {"meters": {}, "Gamma0": {}, "valuesets": {}, "class": {},
               "itabs": {}, "liftdev": {}, "harness_events": []}
    # ---- CERT phase ----
    gv0 = len(G.VIOL)
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            full = f"{kind},p={p},{tag}"
            try:
                T4 = Tower4(kind, p, d0, r0, r1, r2, r3, full)
                G.T1_T2(T4.T, nf=6)
                G.T5(T4.T)
                G.T11(T4.T, pari)
                cert3_internal4(T4.T3, full)
                cert4_internal(T4)
                cert4_pari(T4, pari)
            except Exception as exc:
                HARNESS_EVENTS.append((full, "CERT", repr(exc)))
        print(f"[{time.time()-t0:6.1f}s] CERT ring ({kind},p={p}) done")
    cert2_viol = len(G.VIOL) - gv0
    cert2_n = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
    print(f"[{time.time()-t0:6.1f}s] CERT done: level-2 {cert2_viol} viol "
          f"({cert2_n} samples)")
    # ---- main battery ----
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2, r3 in ROWS:
            full = f"{kind},p={p},{tag}"
            try:
                T4 = Tower4(kind, p, d0, r0, r1, r2, r3, full)
                run_tower(T4, results)
            except Exception as exc:
                HARNESS_EVENTS.append((full, "BATTERY", repr(exc)))
            print(f"[{time.time()-t0:7.1f}s]   {full} done "
                  f"(cum viol = {len(VIOL)})")
    # ---- FROZEN g_top fence: A4 vs P integer tables, per ring ----
    for kind, p in CONFIGS:
        ta = results["itabs"].get(f"{kind},p={p},A4")
        tp = results["itabs"].get(f"{kind},p={p},P")
        note("FROZEN")
        if ta is None or tp is None or ta != tp:
            viol("FROZEN", f"{kind},p={p}",
                 "g_top-invariance fails: A4 vs P integer tables differ")
    # ---- G8 symbolic ----
    msep4i, altni, phantom = g8_symbolic4(20000)
    print(f"[{time.time()-t0:6.1f}s] G8 symbolic done (MSEP4i = {msep4i}, "
          f"ALT-nonintegral = {altni}, cross-denominator phantoms = "
          f"{phantom})")
    # ---- mutation controls ----
    try:
        detf, detw, dets = mutation_controls4(results)
    except Exception as exc:
        detf, detw, dets = {}, {}, {}
        HARNESS_EVENTS.append(("mutation_phase", "MUT", repr(exc)))
    print(f"[{time.time()-t0:6.1f}s] mutation controls done: field={detf} "
          f"warrant={detw} structural={dets}")
    # ---- LIFT-DEV secondary leg ----
    ldvis = run_liftdev(results)
    print(f"[{time.time()-t0:6.1f}s] LIFT-DEV leg done (LDVIS = {ldvis})")
    results["harness_events"] = HARNESS_EVENTS
    # ------------------------------- report ---------------------------------
    print(); print("=" * 78)
    print("PREREGISTERED vs OBSERVED (violations; samples in parentheses)")
    print("=" * 78)
    law_fams = [
        ("FSUB", "F-SUB gate: c4|_(e3Z)^2 == embed(measured c3) "),
        ("F0a",  "LEVEL-2 FIDELITY: accepted law on subtower    "),
        ("F0b",  "LEVEL-3 FIDELITY: measured (ITER-LAW-3)       "),
        ("G1",   "L6-4 ANCHOR-VAL eps-chain                     "),
        ("G2",   "L7-4 PAIR-VAL both forms + top-slot shape     "),
        ("G3",   "THE CANDIDATE (ITER-LAW-4) closed form        "),
        ("G4",   "D3/D2/D1 per-level integrality                "),
        ("G5",   "cocycle identity, window AND quotient         "),
        ("GSWAP","swap symmetry                                 "),
        ("G6",   "degenerations (e_j = 1 collapses, C3 two-way) "),
        ("G7",   "Z/E4 descent: simultaneous + 4 MIXED blocks   "),
        ("G8",   "integer layer symbolic (20k draws)            "),
        ("MSEP0","ALT separation off d4=1 (master-switch fence) "),
        ("FINF", "inflation-defect identity vs measured shadow  "),
        ("FINF0","shadow deviation at d4=0                      "),
        ("FINFMISS", "F-INF shadow window misses                "),
        ("FJ3",  "J-window rung 3                               "),
        ("FJ2",  "J-window rung 2                               "),
        ("FJ1",  "J-window rung 1                               "),
        ("FCLASSK", "kappa_Z(d4-table) == (E4/e3)*l3            "),
        ("FCLASSS", "class(c4) == INV-4 monomial mod M^{E4}     "),
        ("FROZEN", "g_top-invariance (A4 vs P integer tables)   "),
        ("CERT3", "level-3 data cert (psi2/Phi3/R3s key)        "),
        ("CERT4", "level-4 data cert (psi3/Phi4/R4s key)        "),
        ("CERT4P", "PARI level-4 (Phi4 irred, (e,f))            "),
    ]
    law_red = 0
    for fam, desc in law_fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == 0 else "RED"
        law_red += obs
        print(f"{fam:8} {desc} pred 0  obs {obs:5d} ({n:6d})  {verdict}")
    cert2_verdict = "GREEN" if cert2_viol == 0 else "RED"
    law_red += cert2_viol
    print(f"CERT2    level-2 subtower (T1/T2/T5/T11+PARI)        "
          f"pred 0  obs {cert2_viol:5d} ({cert2_n:6d})  {cert2_verdict}")
    print(f"CERT4P deferrals (degPhi4 > cap, preregistered): "
          f"{COUNTS.get('CERT4P_DEFER', 0)}")
    # ---- meters + controls ----
    control_bad = []
    def meter_ok(rows_needed, key):
        bad = []
        for kind, p in CONFIGS:
            for tag in rows_needed:
                full = f"{kind},p={p},{tag}"
                if results["meters"].get(full, {}).get(key, 0) <= 0:
                    bad.append(full)
        return bad
    e3ge2 = tuple(t for t, _, _, _, _, r3 in ROWS if r3[0] >= 2)
    meter_specs = [
        ("MD4    > 0 on all e3>=2 rows", e3ge2, "md4"),
        ("MC-3   (g2=1 & d3c=1) on A4,P,S,T", ("A4", "P", "S", "T"), "mid3"),
        ("MC-2   (g1=1 & d2c=1) on A4,P,S,T", ("A4", "P", "S", "T"), "mid2"),
        ("MC-1   (g0=1 & d1c=1) on A4,P,S,T", ("A4", "P", "S", "T"), "inn"),
        ("MC-TRP (triple cascade) on A4", ("A4",), "trip"),
        ("MV     (visible c4 != 1) on P,Q,R,MUA,MUB",
         ("P", "Q", "R", "MUA", "MUB"), "mv"),
    ]
    for label, rows_needed, key in meter_specs:
        bad = meter_ok(rows_needed, key)
        if bad: control_bad.append(f"METER {label}: MISS {bad}")
        print(f"METER {label:42} {'MET' if not bad else 'MISS: ' + str(bad)}")
    if msep4i <= 0: control_bad.append("METER MSEP4i")
    print(f"METER MSEP4i (symbolic ALT/composed separation) = {msep4i} "
          f"(pred > 0)  {'MET' if msep4i > 0 else 'MISS'}")
    msep4f = sum(m.get("msep4f", 0) for m in results["meters"].values())
    print(f"METER MSEP4f (field-level separation, report) = {msep4f}; "
          f"ALT violations vs measured = {COUNTS.get('ALTVIOL', 0)} / "
          f"{COUNTS.get('G3', 0)} pairs; ALT symbolic nonintegral = {altni}")
    if ldvis <= 0: control_bad.append("METER LDVIS")
    print(f"METER LDVIS (LIFT-DEV factor visible) = {ldvis} (pred > 0)  "
          f"{'MET' if ldvis > 0 else 'MISS'}")
    for m in ("m1", "m2", "m3", "m4", "m5", "m6"):
        df, dw = detf.get(m, 0), detw.get(m, 0)
        okf, okw = df >= 1, dw >= 1
        if not okf: control_bad.append(f"MUTATION {m} field")
        if not okw: control_bad.append(f"MUTATION {m} warrant")
        extra = (f"  structural {dets.get('m4', 0)}"
                 if m == "m4" else "")
        print(f"MUTATION {m}: field {df}, warrant {dw}{extra} "
              f"(pred >= 1 each)  "
              f"{'MET' if okf and okw else 'NOT DETECTED — teeth'}")
    if dets.get("m4", 0) < 1:
        control_bad.append("MUTATION m4 structural")
    # ---- harness events ----
    if HARNESS_EVENTS:
        print(f"{len(HARNESS_EVENTS)} HARNESS EVENTS (bug detectors first):")
        for h in HARNESS_EVENTS[:20]:
            print("  ", h)
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 40):")
        for v in VIOL[:40]:
            print("  ", v)
    for tag, vals in results["valuesets"].items():
        print(f"value set {tag}: {vals}")
    for tag, cl in results["class"].items():
        if cl.get("top_escapes_ME4"):
            print(f"TOP-CARRY IMAGE ESCAPES M^E4 (M2-S8 flag) on {tag}: {cl}")
    total = sum(COUNTS.values()) + cert2_n
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    # ---- THE THREE VERDICT LINES (pre-agreed wording; law-keyed) ----
    sec_fams = ("LDDEV", "LDINV", "LDCERT")
    sec_red = sum(1 for v in VIOL if v[0] in sec_fams)
    law_names = {f for f, _ in law_fams}
    law_viol = sum(1 for v in VIOL if v[0] in law_names) + cert2_viol
    law_green = (law_viol == 0 and not HARNESS_EVENTS)
    print(f"LAW VERDICT (ITER-LAW-4 primary, predicted-0 families): "
          f"{'GREEN' if law_green else f'RED — {law_viol} violations'}"
          f"{' [+harness events]' if HARNESS_EVENTS else ''}")
    print(f"CONTROL VERDICT (meters + mutation teeth, SEPARATE from the law): "
          f"{'MET' if not control_bad else 'PARTIAL(teeth): ' + '; '.join(control_bad)}")
    print(f"SECONDARY VERDICT (LIFT-DEV-4, conjecture-grade prediction): "
          f"{'GREEN' if sec_red == 0 else f'RED — {sec_red} violations'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "iterlaw4_probe_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                       cert2_violations=cert2_viol, cert2_samples=cert2_n,
                       msep4i=msep4i, msep4f=msep4f, alt_nonintegral=altni,
                       phantom_cross_denominator=phantom,
                       meters=results["meters"], Gamma0=results["Gamma0"],
                       valuesets=results["valuesets"],
                       cls=results["class"], itabs=results["itabs"],
                       liftdev=results["liftdev"],
                       mutations=results.get("mutations"),
                       control_bad=control_bad,
                       law_green=law_green, secondary_red=sec_red,
                       harness_events=HARNESS_EVENTS),
                  fh, indent=1, default=str)
    return 0 if (law_green and not control_bad and sec_red == 0) else 1

if __name__ == "__main__":
    sys.exit(main())
