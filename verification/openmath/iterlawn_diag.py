#!/usr/bin/env python3
"""iterlawn_diag.py — POST-SEAL-LABELED DIAGNOSTIC for the general-n compose
note lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md.  NOT a sealed battery,
NOT a proof step, NOT part of any seal; labeled per the post-seal-diagnostic
discipline (the iterlaw3_proof_diag precedent).  All sealed artifacts are
consumed READ-ONLY (imports byte-untouched).

LEG A (4 reads = RUNG n = 3; sealed-harness REUSE): iterlaw4_probe's
  Tower4/Composite4 machinery imported verbatim, three SEALED roster rows
  (A4, B4, C3) at (Zp, 3).  Tests the note's NEW generic intermediate
  identities that the sealed battery did NOT display in this form:
    A1  the shift cascade beta_j'' = beta_j + beta_j' + S_j  (j = 3,2,1)
    A2  the (*)-positivity display: S_j = 0  or  e_j*S_j >= gamma_{j+1}
    A3  COR-4 monodromy: F(g+E4)/F(g) == rho = z3^{-l2*e0*e1} * z2^{-l1*e0}
        * z1^{-l0}   (F = the eps-chain / L6-4 anchor value)
    A4  DCX_m outer-locus census (m = 2,3) + the measured law re-checked ON
        those pairs (instance evidence for the open corner, never a proof)
    A5  e_j = 1 passthrough census (B4: e1 = 1 -> D2 = 0 and S1 = S2)
LEG B (5 reads = RUNG n = 4; FRESH — the first 5-read data in the campaign):
  a minimal Tower5/Composite5 layer, the exact one-level-up mirror of
  Tower4/Composite4 (same construction discipline; canonical eps-corrected
  lifts at every level; Phi5 never needed — the cocycle consumes Phi0..Phi4).
  3 tiny shapes x 2 rings, E5 <= 12, full W1xW1 blocks:
    B1  L6-(5): val5(anchor) == embed(eps4*eps3*eps2*eps1 chain), != 0
    B2  W-MULT-(5): val5(phi*phi') == zb5^{d5}*val5(phi)*val5(phi'), single
        nonzero top slot at d5, w5(P) = g+g'  (the G2-shape clause)
    B2' L7-(5) explicit form: == zb5^{d5}*prod_j z_j^{dj_pl}*embed(prod_j
        eps_j(B_j))
    B3  (ITER-LAW-5): c5 == zb5^{d5}*z4^{D4}*z3^{D3}*z2^{D2}*z1^{D1} per the
        (ITER-LAW-n) recursion (D_j integral at every pair)
    B4  integer cascade j = 4..1 + (*)-positivity + D_j-integrality
    B5  COR-4: phi_{g+E5} == pi*phi_g (poly identity), one-sided-mixed
        descent c5(g+E5,g') == c5(g,g'), monodromy rho (4 letters)
    B6  degenerations: T5C (e4 = 1): d5 == 0, (D4,D3,D2,D1) == the 4-read
        subtower constants of the SAME pair, and c5 == K5-embed(c4) (the
        two-way tie, computed in ONE field tower to avoid cross-dict embeds);
        e_j = 1 passthroughs per shape (D_j = 0, S_{j-1} = S_j)
    B7  DCX_m outer censuses (m = 2..5) + law-on-DCX counter (T5B' is
        DCX_2-live by design: e0 = 3, g0 = g1 = 1)
Exact arithmetic throughout; deterministic (full blocks, no sampling, no
seed needed).  Exit 0 iff ZERO violations in every family.
"""
import sys, os, math, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, pnorm, padd, pmul, ppow, pscal,
                              eq12, bezout, INF, mk_field_ext)
import strata3_probe as S3MOD
import iterlawr_probe as ILP                      # installs the psi2 shim
import iterlaw4_probe as IL4
from iterlaw4_probe import Tower4, Composite4

VIOL = []
CNT = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:200]))
    print(f"  VIOLATION [{fam}] {tag}: {detail}")

# =========================== the 5-read layer ================================
class Tower5:
    """Levels 0-4 = Tower4 VERBATIM (canonical eps1-corrected Phi2,
    eps2-corrected Phi3, eps3-corrected Phi4); plus the level-5 layer:
    K4 = K3[z4]/(psi3), eps4, w5/R5w, K5 = K4[zb5]/(psi4), val5 — the exact
    one-level-up mirror of Tower4's level-4 layer.  No Phi5 (not consumed)."""
    def __init__(self, kind, p, d0, r0, r1, r2, r3, r4, tag):
        self.tag = tag
        self.T4 = Tower4(kind, p, d0, r0, r1, r2, r3, tag + "/L01234")
        T4 = self.T4; T3 = T4.T3; T = T3.T
        self.T3, self.T = T3, T
        self.R = T.R
        self.e4, self.h4, self.g4 = r4
        assert math.gcd(self.e4, self.h4) == 1
        self.K4 = mk_field_ext(T4.K3, T4.psi3)
        self.z4 = self.K4["z"]
        self.l3, self.l3p = T4.l3, T4.l3p
        self.l4, self.l4p = bezout(self.e4, self.h4)
        self.gamma5 = self.e4*T4.w4Phi4 + self.h4
        self.psi4 = S3MOD.pick_irr3(self.K4, self.g4, idx=(T3.h2 + T4.h3) % 2)
        self.K5 = mk_field_ext(self.K4, self.psi4)
        self.zb5 = self.K5["z"]
        self.E5 = T.e0*T.e1*T3.e2*T4.e3*self.e4
        # cert-lite: the level-4 weight key (w4 of Phi4 == e3*g3*gamma4)
        assert T4.w4(T4.Phi4) == T4.w4Phi4, "w4(Phi4) key failed"

    def eps4(self, beta):
        s, u = eq12(beta, self.T4.e3, self.T4.h3)
        return self.K4["pow"](self.z4, self.l3p*s - self.l3*u)

    def R4v(self, A):
        """level-4 read VALUE at z4 (Tower4.R4w coeffs dotted with z4^j)."""
        K4 = self.K4
        coeffs = self.T4.R4w(A)
        v = K4["zero"]; zp = K4["one"]
        for c in coeffs:
            if not self.T4.K3["isz"](c):
                v = K4["add"](v, K4["mul"](K4["embed"](c), zp))
            zp = K4["mul"](zp, self.z4)
        return v

    def w5_data(self, f):
        d4 = dev(self.R, f, self.T4.Phi4)
        vals = [self.T4.w4(A) if A else INF for A in d4]
        if all(v == INF for v in vals):
            return d4, vals, INF
        g = min(self.e4*vals[j] + j*self.gamma5 for j in range(len(d4))
                if vals[j] < INF)
        return d4, vals, g
    def w5(self, f):
        return self.w5_data(f)[2]

    def R5w(self, f, with_meta=False):
        K4 = self.K4
        d4, vals, g = self.w5_data(f)
        assert g < INF, "R5w of 0"
        s5, u5 = eq12(g, self.e4, self.h4)
        jmax = (len(d4)-1 - s5)//self.e4 if len(d4)-1 >= s5 else -1
        coeffs = []
        for j in range(jmax + 1):
            sj = s5 + j*self.e4
            A = d4[sj]
            num = g - sj*self.gamma5
            assert num % self.e4 == 0, "gamma_j not integral"
            gj = num // self.e4
            on = bool(A) and vals[sj] == gj
            if A and vals[sj] < gj:
                raise AssertionError("slot below the line: w5 min wrong")
            c = K4["mul"](self.eps4(gj), self.R4v(A)) if on else K4["zero"]
            coeffs.append(c)
        if with_meta:
            return coeffs, dict(gamma=g, s5=s5, u5=u5)
        return coeffs

class Composite5:
    def __init__(self, T5):
        self.T5 = T5
        T4 = T5.T4; T3 = T4.T3; T = T3.T
        self.K5 = T5.K5
        K5, K4 = self.K5, T5.K4
        self.zb5 = T5.zb5
        self.z4_5 = K5["embed"](T5.z4)
        self.z3_5 = K5["embed"](K4["embed"](T4.z3))
        self.z2_5 = K5["embed"](K4["embed"](T4.K3["embed"](T3.z2)))
        self.z1_5 = K5["embed"](K4["embed"](T4.K3["embed"](
            T3.K2["embed"](T.z1))))
        E5 = T5.E5
        base = ((T5.e4 - 1)*T5.gamma5 + T5.e4*(T4.e3 - 1)*T4.gamma4
                + T5.e4*T4.e3*(T3.e2 - 1)*T3.gamma3
                + T5.e4*T4.e3*T3.e2*(T.e1 - 1)*T.gamma2
                + E5*(T.e0 - 1)*T.h0 + E5)
        G0 = ((base + E5 - 1)//E5)*E5
        while True:
            hi = 2*(G0 + 3*E5) + 2
            if all(self.split(g)[9] >= 0 for g in range(G0, hi + 1)):
                break
            G0 += E5
        self.Gamma0 = G0
        self._anch, self._aval = {}, {}

    def split(self, gamma):
        T5 = self.T5; T4 = T5.T4; T3 = T4.T3; T = T3.T
        s5, u5 = eq12(gamma, T5.e4, T5.h4)
        b4 = u5 - s5*T4.w4Phi4
        s4, u4 = eq12(b4, T4.e3, T4.h3)
        b3 = u4 - s4*T3.w3Phi3
        s3, u3 = eq12(b3, T3.e2, T3.h2)
        b2 = u3 - s3*T.w2Phi2
        s2, u2 = eq12(b2, T.e1, T.h1)
        b1 = u2 - s2*T.w1Phi1
        s1, u1 = eq12(b1, T.e0, T.h0)
        return s5, s4, s3, s2, s1, b4, b3, b2, b1, u1

    def anchor(self, gamma):
        if gamma in self._anch: return self._anch[gamma]
        T5 = self.T5; T4 = T5.T4; T3 = T4.T3; T = T3.T; R = T.R
        s5, s4, s3, s2, s1, b4, b3, b2, b1, u1 = self.split(gamma)
        assert u1 >= 0, f"window: gamma={gamma}, u1={u1}"
        f = pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1))
        f = pmul(R, f, ppow(R, T.Phi1, s2))
        f = pmul(R, f, ppow(R, T.Phi2, s3))
        f = pmul(R, f, ppow(R, T3.Phi3, s4))
        f = pmul(R, f, ppow(R, T4.Phi4, s5))
        self._anch[gamma] = f
        return f

    def val5(self, f, want_meta=False):
        T5 = self.T5; K5 = self.K5
        coeffs, m = T5.R5w(f, with_meta=True)
        v = K5["zero"]; zp = K5["one"]; nz = []
        for j, c in enumerate(coeffs):
            if not T5.K4["isz"](c):
                nz.append(j)
                v = K5["add"](v, K5["mul"](K5["embed"](c), zp))
            zp = K5["mul"](zp, self.zb5)
        if want_meta:
            return v, nz, m["gamma"]
        return v

    def anchor_val(self, gamma):
        if gamma in self._aval: return self._aval[gamma]
        v = self.val5(self.anchor(gamma))
        self._aval[gamma] = v
        return v

    def eps_chain(self, gamma):
        T5 = self.T5; T4 = T5.T4; T3 = T4.T3; T = T3.T
        _, _, _, _, _, b4, b3, b2, b1, _ = self.split(gamma)
        e4v = T5.eps4(b4)
        e3v = T5.K4["embed"](T4.eps3(b3))
        e2v = T5.K4["embed"](T4.K3["embed"](T3.eps2(b2)))
        e1v = T5.K4["embed"](T4.K3["embed"](T3.K2["embed"](T.eps1(b1))))
        v = T5.K4["mul"](e4v, T5.K4["mul"](e3v, T5.K4["mul"](e2v, e1v)))
        return self.K5["embed"](v)

    def constants(self, ga, gb):
        T5 = self.T5; T4 = T5.T4; T3 = T4.T3; T = T3.T
        A = self.split(ga); B = self.split(gb); C = self.split(ga + gb)
        (s5a, s4a, s3a, s2a, s1a, b4a, b3a, b2a, b1a, _) = A
        (s5b, s4b, s3b, s2b, s1b, b4b, b3b, b2b, b1b, _) = B
        (s5c, s4c, s3c, s2c, s1c, b4c, b3c, b2c, b1c, _) = C
        d5 = (s5a + s5b)//T5.e4
        dpl = dict(d4=(s4a + s4b)//T4.e3, d3=(s3a + s3b)//T3.e2,
                   d2=(s2a + s2b)//T.e1, d1=(s1a + s1b)//T.e0)
        S4 = d5*T5.gamma5
        num = s4a + s4b - s4c + T5.l3*S4
        D4 = num//T4.e3 if num % T4.e3 == 0 else None
        S3 = (None if D4 is None
              else D4*T4.gamma4 + S4*(T5.l3p - T5.l3*T3.w3Phi3))
        num = None if S3 is None else s3a + s3b - s3c + T4.l2*S3
        D3 = (num//T3.e2 if num is not None and num % T3.e2 == 0 else None)
        S2 = (None if D3 is None
              else D3*T3.gamma3 + S3*(T4.l2p - T4.l2*T.w2Phi2))
        num = None if S2 is None else s2a + s2b - s2c + T.l1*S2
        D2 = (num//T.e1 if num is not None and num % T.e1 == 0 else None)
        S1 = (None if D2 is None
              else D2*T.gamma2 + S2*(T.l1p - T.l1*T.w1Phi1))
        num = None if S1 is None else s1a + s1b - s1c + T.l0*S1
        D1 = (num//T.e0 if num is not None and num % T.e0 == 0 else None)
        return dict(d5=d5, dpl=dpl, S4=S4, D4=D4, S3=S3, D3=D3, S2=S2,
                    D2=D2, S1=S1, D1=D1,
                    casc=dict(b4=(b4c - b4a - b4b), b3=(b3c - b3a - b3b),
                              b2=(b2c - b2a - b2b), b1=(b1c - b1a - b1b)),
                    sa=(s5a, s4a, s3a, s2a, s1a), sb=(s5b, s4b, s3b, s2b, s1b))

    def law5(self, c):
        K5 = self.K5
        if any(c[k] is None for k in ("D4", "D3", "D2", "D1")):
            return None
        return K5["mul"](K5["pow"](self.zb5, c["d5"]),
               K5["mul"](K5["pow"](self.z4_5, c["D4"]),
               K5["mul"](K5["pow"](self.z3_5, c["D3"]),
               K5["mul"](K5["pow"](self.z2_5, c["D2"]),
                         K5["pow"](self.z1_5, c["D1"])))))

    # 4-read subtower (levels 0-3) computed IN THE SAME FIELD TOWER (via
    # T5.R4v/K4 and K5-embedding) — the e4 = 1 two-way tie leg.
    def split4(self, gamma):
        T4 = self.T5.T4; T3 = T4.T3; T = T3.T
        s4, u4 = eq12(gamma, T4.e3, T4.h3)
        b3 = u4 - s4*T3.w3Phi3
        s3, u3 = eq12(b3, T3.e2, T3.h2)
        b2 = u3 - s3*T.w2Phi2
        s2, u2 = eq12(b2, T.e1, T.h1)
        b1 = u2 - s2*T.w1Phi1
        s1, u1 = eq12(b1, T.e0, T.h0)
        return s4, s3, s2, s1, b3, b2, b1, u1
    def anchor4(self, gamma):
        T4 = self.T5.T4; T3 = T4.T3; T = T3.T; R = T.R
        s4, s3, s2, s1, b3, b2, b1, u1 = self.split4(gamma)
        assert u1 >= 0
        f = pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1))
        f = pmul(R, f, ppow(R, T.Phi1, s2))
        f = pmul(R, f, ppow(R, T.Phi2, s3))
        f = pmul(R, f, ppow(R, T3.Phi3, s4))
        return f
    def c4_mine(self, ga, gb):
        T5 = self.T5; K4 = T5.K4
        prod = pmul(T5.R, self.anchor4(ga), self.anchor4(gb))
        vp = T5.R4v(prod)
        vt = T5.R4v(self.anchor4(ga + gb))
        return K4["mul"](vp, K4["inv"](vt))
    def constants4(self, ga, gb):
        T4 = self.T5.T4; T3 = T4.T3; T = T3.T
        s4a, s3a, s2a, s1a, _, _, _, _ = self.split4(ga)
        s4b, s3b, s2b, s1b, _, _, _, _ = self.split4(gb)
        s4c, s3c, s2c, s1c, _, _, _, _ = self.split4(ga + gb)
        d4 = (s4a + s4b)//T4.e3
        S3 = d4*T4.gamma4
        num = s3a + s3b - s3c + T4.l2*S3
        D3 = num//T3.e2 if num % T3.e2 == 0 else None
        S2 = (None if D3 is None
              else D3*T3.gamma3 + S3*(T4.l2p - T4.l2*T.w2Phi2))
        num = None if S2 is None else s2a + s2b - s2c + T.l1*S2
        D2 = (num//T.e1 if num is not None and num % T.e1 == 0 else None)
        S1 = (None if D2 is None
              else D2*T.gamma2 + S2*(T.l1p - T.l1*T.w1Phi1))
        num = None if S1 is None else s1a + s1b - s1c + T.l0*S1
        D1 = (num//T.e0 if num is not None and num % T.e0 == 0 else None)
        return d4, D3, D2, D1

# ------------------------- DCX outer-locus predicates ------------------------
def dcx_outer_5(T5, c):
    """m -> outer-corner predicate at level m for the pair (5-read tower):
    g_{m-2} = g_{m-1} = 1, delta_{m-1}^pl = 1, s_m = s_m' = e_{m-1}-1
    (the note's DCX_m outer bound; sharp form checked separately at m=2)."""
    T4 = T5.T4; T3 = T4.T3; T = T3.T
    gs = (T.g0, T.g1, T3.g2, T4.g3, T5.g4)
    es = (T.e0, T.e1, T3.e2, T4.e3, T5.e4)
    sa, sb, dpl = c["sa"], c["sb"], c["dpl"]
    # sa = (s5,s4,s3,s2,s1): s_m has index 5-m
    out = {}
    for m in (2, 3, 4, 5):
        gcond = gs[m-2] == 1 and gs[m-1] == 1
        dl = dpl[f"d{m-1}"] == 1
        track = (sa[5-m] == es[m-1]-1) and (sb[5-m] == es[m-1]-1)
        out[m] = gcond and dl and track
    return out

def dcx_sharp2_5(T5, c):
    """the rung-2-sharp DCX_2 predicate: + S1 + s(gamma2 | e0,h0) >= 2 e0."""
    T4 = T5.T4; T3 = T4.T3; T = T3.T
    if not (T.g0 == 1 and T.g1 == 1): return False
    if c["dpl"]["d1"] != 1: return False
    if not (c["sa"][3] == T.e1-1 and c["sb"][3] == T.e1-1): return False
    s_g2, _ = eq12(T.gamma2, T.e0, T.h0)
    S1pl = c["sa"][4] + c["sb"][4]
    return S1pl + s_g2 >= 2*T.e0

# ================================ LEG B ======================================
SHAPES5 = [
    # (tag, d0, r0, r1, r2, r3, r4)   E5 <= 12
    ("T5A", 1, (2,1,1), (1,1,2), (2,1,1), (1,1,2), (2,1,1)),  # E5=8; letters z2,z4; NO DCX_m live (no consecutive g=1 pair)
    ("T5B", 1, (3,2,1), (1,1,1), (2,1,1), (1,1,2), (2,1,1)),  # E5=12; DCX_2-LIVE (e0=3, g0=g1=1); letter z4
    ("T5C", 1, (2,1,1), (2,1,1), (1,1,2), (2,1,1), (1,1,2)),  # E5=8; e4=1 TOP CONTROL (two-way tie); e2=1 passthrough; g4=2 letter zb5
]
RINGS5 = {"T5A": [("Zp",3), ("Fpt",2)],
          "T5B": [("Zp",3), ("Fpt",3)],
          "T5C": [("Zp",3), ("Fpt",2)]}

def run5(tag, d0, r0, r1, r2, r3, r4, kind, p):
    t0 = time.time()
    T5 = Tower5(kind, p, d0, r0, r1, r2, r3, r4, f"{kind},p{p},{tag}")
    C = Composite5(T5)
    T4 = T5.T4; T3 = T4.T3; T = T3.T
    K5 = C.K5; E5 = T5.E5; G0 = C.Gamma0
    W1 = list(range(G0, G0 + E5))
    es = (T.e0, T.e1, T3.e2, T4.e3, T5.e4)
    gammas = (T.h0, T.gamma2, T3.gamma3, T4.gamma4, T5.gamma5)
    # gammas[j] = gamma_{j+1} with gamma_1 := h0 (the note's convention)
    name = f"{kind},p={p},{tag}"
    print(f"-- {name}: E5={E5}, G0={G0}, degPhi4={len(T4.Phi4)-1}, "
          f"psi4 deg={T5.g4}")
    # B1: L6-(5)
    for g in W1:
        note("B1_L6")
        va = C.anchor_val(g)
        if K5["isz"](va) or va != C.eps_chain(g):
            viol("B1_L6", name, f"gamma={g}")
    # pairs
    ncase = dict(dcx2s=0, dcx_outer=0, e1pass=0, e2pass=0, e3pass=0)
    for ga in W1:
        for gb in W1:
            c = C.constants(ga, gb)
            # B4: cascade + integrality + (*)
            note("B4_casc")
            ok = (c["casc"]["b4"] == c["S4"] and c["D4"] is not None
                  and c["casc"]["b3"] == c["S3"] and c["D3"] is not None
                  and c["casc"]["b2"] == c["S2"] and c["D2"] is not None
                  and c["casc"]["b1"] == c["S1"] and c["D1"] is not None)
            if not ok:
                viol("B4_casc", name, f"({ga},{gb}): {c}")
                continue
            note("B4_star")
            for j, Sj in ((4, c["S4"]), (3, c["S3"]), (2, c["S2"]),
                          (1, c["S1"])):
                # (*_j): S_j = 0 or e_j*S_j >= gamma_{j+1}
                if Sj != 0 and es[j]*Sj < gammas[j]:
                    viol("B4_star", name, f"({ga},{gb}) j={j}: S={Sj}")
            # B2/B2': W-MULT both forms
            note("B2_wmult")
            prod = pmul(T5.R, C.anchor(ga), C.anchor(gb))
            vp, nz, gmeas = C.val5(prod, want_meta=True)
            va, vb = C.anchor_val(ga), C.anchor_val(gb)
            rhs = K5["mul"](K5["pow"](C.zb5, c["d5"]), K5["mul"](va, vb))
            if vp != rhs or nz != [c["d5"]] or gmeas != ga + gb:
                viol("B2_wmult", name, f"({ga},{gb}) nz={nz}")
            note("B2p_l7")
            dpl = c["dpl"]
            carry = K5["mul"](K5["pow"](C.z4_5, dpl["d4"]),
                    K5["mul"](K5["pow"](C.z3_5, dpl["d3"]),
                    K5["mul"](K5["pow"](C.z2_5, dpl["d2"]),
                              K5["pow"](C.z1_5, dpl["d1"]))))
            # explicit L7 form: zb5^d5 * prod z_j^{dj_pl} * eps-chain at sums
            T4_ = T4
            _, _, _, _, _, b4a, b3a, b2a, b1a, _ = C.split(ga)
            _, _, _, _, _, b4b, b3b, b2b, b1b, _ = C.split(gb)
            e4v = T5.eps4(b4a + b4b)
            e3v = T5.K4["embed"](T4_.eps3(b3a + b3b))
            e2v = T5.K4["embed"](T4_.K3["embed"](T3.eps2(b2a + b2b)))
            e1v = T5.K4["embed"](T4_.K3["embed"](T3.K2["embed"](
                T.eps1(b1a + b1b))))
            chain = C.K5["embed"](T5.K4["mul"](e4v, T5.K4["mul"](e3v,
                        T5.K4["mul"](e2v, e1v))))
            rhs2 = K5["mul"](K5["pow"](C.zb5, c["d5"]),
                             K5["mul"](carry, chain))
            if vp != rhs2:
                viol("B2p_l7", name, f"({ga},{gb})")
            # B3: the law
            note("B3_law")
            cval = K5["mul"](vp, K5["inv"](C.anchor_val(ga + gb)))
            lv = C.law5(c)
            if lv is None or cval != lv:
                viol("B3_law", name, f"({ga},{gb}) c={c}")
            # B7: DCX censuses (+ law ON the locus, counted above already)
            oc = dcx_outer_5(T5, c)
            if any(oc.values()):
                ncase["dcx_outer"] += 1
            if dcx_sharp2_5(T5, c):
                ncase["dcx2s"] += 1
            # B6 passthrough censuses (e_{j-1} = 1 => D_j = 0, S_{j-1} = S_j)
            for j, (Dj, Sjm1, Sj) in ((2, (c["D2"], c["S1"], c["S2"])),
                                      (3, (c["D3"], c["S2"], c["S3"])),
                                      (4, (c["D4"], c["S3"], c["S4"]))):
                if es[j-1] == 1:
                    note(f"B6_e{j-1}pass")
                    if Dj != 0 or Sjm1 != Sj:
                        viol(f"B6_e{j-1}pass", name, f"({ga},{gb}) j={j}")
            # B6: e4 = 1 top control (two-way tie)
            if T5.e4 == 1:
                note("B6_topcontrol")
                if c["d5"] != 0:
                    viol("B6_topcontrol", name, f"({ga},{gb}) d5 != 0")
                d4s, D3s, D2s, D1s = C.constants4(ga, gb)
                if (c["D4"], c["D3"], c["D2"], c["D1"]) != (d4s, D3s, D2s, D1s):
                    viol("B6_topcontrol", name,
                         f"({ga},{gb}) 5-read constants != 4-read subtower")
                c4v = C.c4_mine(ga, gb)
                if cval != K5["embed"](c4v):
                    viol("B6_topcontrol", name, f"({ga},{gb}) value tie")
    # B5: descent legs
    for g in W1[:4]:
        note("B5_pi")
        lhs = C.anchor(g + E5)
        rhs = pscal(T5.R, T5.R["pi_pow"](1), C.anchor(g))
        if pnorm(T5.R, lhs) != pnorm(T5.R, rhs):
            viol("B5_pi", name, f"gamma={g}")
    rho = K5["mul"](K5["pow"](C.z4_5, -T5.l3*(T.e0*T.e1*T3.e2)),
          K5["mul"](K5["pow"](C.z3_5, -T4.l2*(T.e0*T.e1)),
          K5["mul"](K5["pow"](C.z2_5, -T.l1*T.e0),
                    K5["pow"](C.z1_5, -T.l0))))
    for g in W1:
        note("B5_rho")
        lhs = K5["mul"](C.eps_chain(g + E5), K5["inv"](C.eps_chain(g)))
        if lhs != rho:
            viol("B5_rho", name, f"gamma={g}")
    for ga in W1[:4]:
        for gb in W1:
            note("B5_descent")
            prod = pmul(T5.R, C.anchor(ga + E5), C.anchor(gb))
            vp = C.val5(prod)
            cm = K5["mul"](vp, K5["inv"](C.anchor_val(ga + E5 + gb)))
            prod0 = pmul(T5.R, C.anchor(ga), C.anchor(gb))
            c0 = K5["mul"](C.val5(prod0), K5["inv"](C.anchor_val(ga + gb)))
            if cm != c0:
                viol("B5_descent", name, f"({ga}+E5,{gb})")
    print(f"   censuses: {ncase}; elapsed {time.time()-t0:.1f}s")
    return ncase

# ================================ LEG A ======================================
def runA():
    print("== LEG A: 4-read (RUNG n = 3) sealed-harness REUSE "
          "(read-only; A4, B4, C3 @ Zp,3) ==")
    rows = {r[0]: r for r in IL4.ROWS}
    for base in ("A4", "B4", "C3"):
        tag, d0, r0, r1, r2, r3 = rows[base]
        T4 = Tower4("Zp", 3, d0, r0, r1, r2, r3, f"Zp,p3,{base}")
        C = Composite4(T4, with_shadow=False)
        T3 = T4.T3; T = T3.T
        K4, E4, G0 = C.K4, T4.E4, C.Gamma0
        W1 = list(range(G0, G0 + E4))
        es = (T.e0, T.e1, T3.e2, T4.e3)
        gammas = (T.h0, T.gamma2, T3.gamma3, T4.gamma4)
        name = f"Zp,p=3,{base}"
        gs = (T.g0, T.g1, T3.g2, T4.g3)
        ncase = dict(dcx2s=0, dcx_outer=0)
        s_g2, _ = eq12(T.gamma2, T.e0, T.h0)
        for ga in W1:
            for gb in W1:
                c = C.constants(ga, gb)
                sc = C.split(ga + gb)
                # A1 cascade (j = 3,2,1)
                note("A1_casc")
                casc = (sc[4] - c["b3a"] - c["b3b"],
                        sc[5] - c["b2a"] - c["b2b"],
                        sc[6] - c["b1a"] - c["b1b"])
                if casc != (c["S3"], c["S2"], c["S1"]):
                    viol("A1_casc", name, f"({ga},{gb})")
                # A2 (*)
                note("A2_star")
                for j, Sj in ((3, c["S3"]), (2, c["S2"]), (1, c["S1"])):
                    if Sj != 0 and es[j]*Sj < gammas[j]:
                        viol("A2_star", name, f"({ga},{gb}) j={j}: S={Sj}")
                # A5 passthrough (B4 has e1 = 1)
                for j, e_idx, Dj, Sjm1, Sj in ((2, 1, c["D2"], c["S1"], c["S2"]),
                                               (3, 2, c["D3"], c["S2"], c["S3"])):
                    if es[e_idx] == 1:
                        note(f"A5_e{e_idx}pass")
                        if Dj != 0 or Sjm1 != Sj:
                            viol(f"A5_e{e_idx}pass", name, f"({ga},{gb})")
                # A4 DCX outer census (m = 2, 3) on the 4-read splits
                # split: s4,s3,s2,s1,b3,b2,b1,u1 -> s_m at index 4-m;
                # plain carry at level m-1: floor((s_{m-1}+s_{m-1}')/e_{m-2})
                As = C.split(ga); Bs = C.split(gb)
                live = False
                for m in (2, 3):
                    gcond = gs[m-2] == 1 and gs[m-1] == 1
                    dpl = (As[4-(m-1)] + Bs[4-(m-1)])//es[m-2]
                    track = (As[4-m] == es[m-1]-1 and Bs[4-m] == es[m-1]-1)
                    if gcond and dpl == 1 and track:
                        live = True
                        if m == 2:
                            S1pl = As[3] + Bs[3]
                            if S1pl + s_g2 >= 2*T.e0:
                                ncase["dcx2s"] += 1
                if live:
                    ncase["dcx_outer"] += 1
                    # the measured law ON the locus (instance evidence)
                    note("A4_dcx_law")
                    cv, vp, nz, gm = C.cocycle(ga, gb)
                    lv = C.law_value(c, "primary")
                    if lv is None or cv != lv:
                        viol("A4_dcx_law", name, f"({ga},{gb})")
        # A3 monodromy
        rho = K4["mul"](K4["pow"](C.z3_4, -T3.l2*(T.e0*T.e1)),
              K4["mul"](K4["pow"](C.z2_4, -T.l1*T.e0),
                        K4["pow"](C.z1_4, -T.l0)))
        for g in W1:
            note("A3_rho")
            lhs = K4["mul"](C.eps_chain(g + E4), K4["inv"](C.eps_chain(g)))
            if lhs != rho:
                viol("A3_rho", name, f"gamma={g}")
        print(f"-- {name}: E4={E4}; censuses {ncase}")

def main():
    t0 = time.time()
    print("iterlawn_diag — POST-SEAL-LABELED diagnostic for "
          "ITERLAWN_PROOF_2026-08-08.md (not a proof step; not a seal)")
    runA()
    print("== LEG B: 5-read (RUNG n = 4) FRESH — first 5-read data ==")
    for (tag, d0, r0, r1, r2, r3, r4) in SHAPES5:
        for (kind, p) in RINGS5[tag]:
            run5(tag, d0, r0, r1, r2, r3, r4, kind, p)
    print("\n== COUNTS ==")
    for k in sorted(CNT):
        print(f"  {k}: {CNT[k]}")
    print(f"== VIOLATIONS: {len(VIOL)} ==")
    for v in VIOL[:40]:
        print("  ", v)
    print(f"total elapsed {time.time()-t0:.1f}s")
    print("DIAG VERDICT:", "CLEAN" if not VIOL else "VIOLATIONS PRESENT")
    sys.exit(0 if not VIOL else 1)

if __name__ == "__main__":
    main()
