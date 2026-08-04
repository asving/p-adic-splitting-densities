#!/usr/bin/env python3
"""rmengine_diag.py — POST-SEAL-LABELED DIAGNOSTIC for the generic (RM-m)
engine compose (lean/notes/openmath/RMENGINE_2026-08-08.md, S9).

NOT a proof step, NOT a seal (the iterlawn_diag/[IL3]-diag precedent):
run at composition, results recorded in the note's S9 actuals block.
Sealed harness modules consumed READ-ONLY (imports byte-untouched).

Legs (note S9):
  D1  the four (RM-m) box clauses at m = 3 — the first level-3 engine data:
      canonical division f*Chat3 = R + Q*Phi3 on fired (rung-4 Case-II) and
      breadth inputs; (C-W_R)/(C-W_Q)/(C-READ)=z3^{eps'}*v*tau3/(C-EPS).
  D2  the S2/S4 instruments at m = 3: 3-level tree CONS == division;
      generic measure (S4.1 interval rule, Fractions) strict on every
      in-tree edge; W-WIN window census (display-grade).
  D3  the S3 line calculus: leaf w3 == line exact; promotion Delta-line ==
      the exact quantum (e2*h1 / h2); correction-L Delta-line == 0;
      junk Delta-line > 0; exit cofactor line == parent - w3Phi3.
  D4  the zh-kernel (S3.1): per-leaf zh-formula == harness single-cell
      read; sum over on-line on-grid leaves == read of R == box prediction
      (B-READ + L-ZMULT end-to-end). One tooth: eps2-factor dropped must
      mismatch somewhere.
  D5  LAW-DCX-4 first data (census-grade): measured DCX4 (TRACK & Q1 != 0)
      vs the S6.1 nested-floor law on 5-read window pairs; strata report.
  D6  consistency vs committed artifacts: RM2A/Zp3 engine+tree legs
      re-executed (expect 0 viol; census == rm2_probe_results.json);
      DCX3 v2 law re-implemented independently, re-run on EX1/Zp3
      (live sets vs dcx3_sharp_v2_results.json: 220/220/0).

Deterministic, exact arithmetic, no sampling, no seed.
"""
import sys, os, math, time, json
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, bezout, INF, pdivmod)
import strata3_probe as S3MOD
import iterlawr_probe as ILP           # pick_irr3 shim (disclosed upstream)
import iterlaw4_probe as IL4
from iterlaw4_probe import Tower4, Composite4
import iterlawn_diag as ILN5           # Tower5/Composite5 (read-only)
import rm2_probe as RM2                # Engine2/Tree/anchor2 (read-only)

VIOL = []
CNT = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:220]))
    if sum(1 for v in VIOL if v[0] == fam) <= 6:
        print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:200]}")

def w0poly(R, f):
    f = pnorm(R, f)
    return INF if not f else min(R["val"](c) for c in f)

def pdivpi(R, f, k):
    return pnorm(R, [R["divpi"](c, k) for c in f])

def digit_split_norm(T, prod):
    """DIGIT-SPLIT on the unit part: prod = pi^w*(L + pi*X + Phi0*Y)."""
    R = T.R
    w = w0poly(R, prod)
    return w, RM2.digit_split(T, pdivpi(R, prod, w))

# ---------------- Engine3: the (RM-3) data of a g3 = 1 Tower4 --------------
class Engine3:
    def __init__(self, T4):
        assert T4.g3 == 1, "RM-3 setting needs g3 = 1"
        T3 = T4.T3; T = T3.T; R = T.R
        self.T4, self.T3, self.T, self.R = T4, T3, T, R
        self.K3 = T4.K3
        self.Chat3 = pnorm(R, padd(R, T4.Phi4,
                                   pneg(R, ppow(R, T3.Phi3, T4.e3))))
        self.c3 = T4.psi3[0]
        self.eps3g4 = T4.eps3(T4.gamma4)
        self.tau3 = self.K3["mul"](self.K3["pow"](self.eps3g4, -1), self.c3)

    def s3(self, beta): return eq12(beta, self.T3.e2, self.T3.h2)[0]

    def certs(self):
        T4, T3, R = self.T4, self.T3, self.R
        out = {}
        out["g3_is_1"] = (T4.g3 == 1)
        out["psi3_monic_deg1"] = (len(T4.psi3) == 2
                                  and T4.psi3[1] == self.K3["one"])
        out["Chat3_C1_deg"] = (len(pnorm(R, self.Chat3)) - 1 < T3.degPhi3)
        out["Chat3_C2_w3"] = (T3.w3(self.Chat3) == T4.gamma4)
        out["Chat3_C3_read"] = (out["Chat3_C2_w3"]
                                and T4.R3v(self.Chat3) == self.tau3)
        return out

    def R3v_at(self, f, beta):
        if not pnorm(self.R, f): return self.K3["zero"]
        lam = self.T3.w3(f)
        if lam > beta: return self.K3["zero"]
        assert lam == beta, "R3v_at: input below the target line"
        return self.T4.R3v(f)

    def call(self, f):
        T4, T3, T, R, K3 = self.T4, self.T3, self.T, self.R, self.K3
        lam = T3.w3(f)
        v = T4.R3v(f)
        Q, Rr = pdivmod(R, pmul(R, f, self.Chat3), T3.Phi3)
        wR = T3.w3(Rr) if pnorm(R, Rr) else INF
        wQ = T3.w3(Q) if pnorm(R, Q) else INF
        target = lam + T4.gamma4
        s3l, s3g = self.s3(lam), self.s3(T4.gamma4)
        epsp = (s3l + s3g)//T3.e2
        eps_id = (s3l + s3g - self.s3(target) == T3.e2*epsp)
        pred = K3["mul"](K3["pow"](T4.z3, epsp), K3["mul"](v, self.tau3))
        okW_R = (wR >= target)
        okW_Q = (not pnorm(R, Q)) or (wQ >= target - T3.w3Phi3)
        got = self.R3v_at(Rr, target) if okW_R else None
        okRead = (got == pred) if okW_R else False
        return dict(lam=lam, v=v, R=Rr, Q=Q, wR=wR, wQ=wQ, target=target,
                    epsp=epsp, eps_id=eps_id, pred=pred, got=got,
                    okW_R=okW_R, okW_Q=okW_Q, okRead=okRead,
                    v_zero=K3["isz"](v), Qnz=bool(pnorm(R, Q)))

# ---------------- the level-3 cell tree (S2.2 at m = 3) --------------------
class Tree3:
    """cells b*Phi0^{j0}Phi1^{j1}Phi2^{j2}; identities ID-1/ID-2/ID-3;
    E1-priority; per-edge mu-descent (S4.1 weights) + line laws (S3.2)."""
    CAP = 200000

    def __init__(self, E3):
        T4, T3, T, R = E3.T4, E3.T3, E3.T, E3.R
        self.E3ng, self.T4, self.T3, self.T, self.R = E3, T4, T3, T, R
        self.P0, self.P1, self.P2 = T.e0*T.g0, T.e1*T.g1, T3.e2*T3.g2
        # S4.1 interval weights (Fractions): w0 := 1
        d0 = len(T.Phi0) - 1
        rho0 = self.P0 - 1 + (1 if d0 >= 2 else 0)
        self.w0f = Fr(1)
        lo1, hi1 = Fr(self.w0f*rho0, T.e1), self.w0f*self.P0
        assert lo1 < hi1, "L-MU interval i=1 empty (off T-scope?)"
        self.w1f = (lo1 + hi1)/2
        lo2 = (self.w0f*rho0 + self.w1f*(self.P1 - 1))/T3.e2
        hi2 = self.w1f*self.P1
        assert lo2 < hi2, "L-MU interval i=2 empty (off T-scope?)"
        self.w2f = (lo2 + hi2)/2
        # line scales (S0.1): Gamma_l = gamma_{l+1} * prod_{l<t<3} e_t
        self.G0 = T.h0*T.e1*T3.e2
        self.G1 = T.gamma2*T3.e2
        self.G2 = T3.gamma3
        self.E3s = T.e0*T.e1*T3.e2
        # identity data: lvl1 (std lift), lvl2 (build_Phi2 C_k), lvl3
        self.lvl1 = []          # (i, coeff poly) : C^{(0)}_i
        for i, c in enumerate(T.psi0):
            if i >= T.g0 or T.K0["isz"](c): continue
            self.lvl1.append((i, pscal(R, R["pi_pow"]((T.g0 - i)*T.h0),
                                       T.liftK0(c))))
        self.lvl2 = {}          # k -> C^{(1)}_k poly (deg < degPhi1)
        for k, c in enumerate(T.psi1):
            if k >= T.g1 or T.K1["isz"](c): continue
            gp = (T.g1 - k)*T.gamma2
            tau = T.K1["mul"](T.K1["pow"](T.eps1(gp), -1), c)
            self.lvl2[k] = T.realize1(tau, gp)
        self.lvl3 = {}          # k -> C^{(2)}_k poly (deg < degPhi2)
        for k, c in enumerate(T3.psi2):
            if k >= T3.g2 or T3.K2["isz"](c): continue
            gp = (T3.g2 - k)*T3.gamma3
            tau = T3.K2["mul"](T3.K2["pow"](T3.eps2(gp), -1), c)
            self.lvl3[k] = T3.realize2(tau, gp)
        # identity replays (certs)
        id1 = ppow(R, T.Phi0, self.P0)
        for i, cf in self.lvl1:
            id1 = padd(R, id1, pmul(R, cf, ppow(R, T.Phi0, T.e0*i)))
        self.cert_id1 = (pnorm(R, id1) == pnorm(R, T.Phi1))
        id2 = ppow(R, T.Phi1, self.P1)
        for k, cf in self.lvl2.items():
            id2 = padd(R, id2, pmul(R, cf, ppow(R, T.Phi1, T.e1*k)))
        self.cert_id2 = (pnorm(R, id2) == pnorm(R, T.Phi2))
        id3 = ppow(R, T.Phi2, self.P2)
        for k, cf in self.lvl3.items():
            id3 = padd(R, id3, pmul(R, cf, ppow(R, T.Phi2, T3.e2*k)))
        self.cert_id3 = (pnorm(R, id3) == pnorm(R, T3.Phi3))
        # cell decompositions of the correction coefficients
        self.lvl2_cells = {k: [(i0, b) for i0, b in
                               enumerate(dev(R, cf, T.Phi0)) if b]
                           for k, cf in self.lvl2.items()}
        self.lvl3_cells = {}
        for k, cf in self.lvl3.items():
            cells = []
            for a1, A in enumerate(dev(R, cf, T.Phi1)):
                if not A: continue
                for a0, b in enumerate(dev(R, A, T.Phi0)):
                    if b: cells.append((a0, a1, b))
            self.lvl3_cells[k] = cells

    def mu(self, j):
        return self.w0f*j[0] + self.w1f*j[1] + self.w2f*j[2]

    def line(self, b, j):
        wb = w0poly(self.R, b)
        return self.E3s*wb + j[0]*self.G0 + j[1]*self.G1 + j[2]*self.G2

    def run(self, f, name, res):
        """reduce f (deg < degPhi3); returns (Rpoly, Qpoly, leaves)."""
        T4, T3, T, R = self.T4, self.T3, self.T, self.R
        # initial cells of f (three-level dev)
        cells = {}
        def addc(j, b):
            if not pnorm(R, b): return
            key = tuple(j)
            cells[key] = pnorm(R, padd(R, cells.get(key, []), b))
            if not cells[key]: del cells[key]
        for j2, A2 in enumerate(dev(R, f, T.Phi2)):
            if not A2: continue
            for j1, A1 in enumerate(dev(R, A2, T.Phi1)):
                if not A1: continue
                for j0, b in enumerate(dev(R, A1, T.Phi0)):
                    if b: addc((j0, j1, j2), b)
        Q = []
        leaves = {}
        pops = 0
        maxj = [0, 0, 0]
        P = (self.P0, self.P1, self.P2)
        while True:
            work = None
            for key in cells:
                if key[0] >= P[0] or key[1] >= P[1] or key[2] >= P[2]:
                    work = key; break
            if work is None: break
            b = cells.pop(work)
            pops += 1
            if pops > self.CAP:
                viol("D2-CAP", name, f"pops>{self.CAP}"); return None
            j0, j1, j2 = work
            for t in range(3): maxj[t] = max(maxj[t], work[t])
            mup = self.mu(work); linep = self.line(b, work)
            def edge_check(kind, jc, bc, dline_expect):
                # mu strict descent (D2) + line law (D3)
                if not pnorm(R, bc): return
                for t in range(3): maxj[t] = max(maxj[t], jc[t])
                if self.mu(jc) >= mup:
                    viol("D2-MU", name, f"{kind} {work}->{jc}")
                dl = self.line(bc, jc) - linep
                if dline_expect == "zero" and dl != 0:
                    viol("D3-LINE", name, f"{kind} corr-L dline={dl}")
                if dline_expect == "pos" and dl <= 0:
                    viol("D3-LINE", name, f"{kind} junk dline={dl}")
                if isinstance(dline_expect, int) and dl != dline_expect:
                    viol("D3-LINE", name,
                         f"{kind} promo dline={dl} != {dline_expect}")
                addc(jc, bc)
            if j0 >= P[0]:          # ID-1 at level 1
                edge_check("promo1", (j0 - P[0], j1 + 1, j2), b,
                           T3.e2*T.h1)
                for i, cf in self.lvl1:
                    wsh, (L, X, Y) = digit_split_norm(T, pmul(R, b, cf))
                    base = (j0 - P[0] + T.e0*i, j1, j2)
                    pw = R["pi_pow"](wsh)
                    edge_check("corr1-L", base, pneg(R, pscal(R, pw, L)),
                               "zero")
                    edge_check("corr1-X", base,
                               pneg(R, pscal(R, R["pi_pow"](wsh + 1), X)),
                               "pos")
                    edge_check("corr1-Y", (base[0] + 1, j1, j2),
                               pneg(R, pscal(R, pw, Y)), "pos")
            elif j1 >= P[1]:        # ID-2 at level 2
                edge_check("promo2", (j0, j1 - P[1], j2 + 1), b, T3.h2)
                for k, dcells in self.lvl2_cells.items():
                    for i0, cD in dcells:
                        wsh, (L, X, Y) = digit_split_norm(T, pmul(R, b, cD))
                        base = (j0 + i0, j1 - P[1] + T.e1*k, j2)
                        pw = R["pi_pow"](wsh)
                        edge_check("corr2-L", base,
                                   pneg(R, pscal(R, pw, L)), "zero")
                        edge_check("corr2-X", base,
                                   pneg(R, pscal(R, R["pi_pow"](wsh+1), X)),
                                   "pos")
                        edge_check("corr2-Y", (base[0] + 1, base[1], j2),
                                   pneg(R, pscal(R, pw, Y)), "pos")
            else:                   # j2 >= P[2]: ID-3 = the Phi3-exit level
                cof = pmul(R, b, pmul(R, ppow(R, T.Phi0, j0),
                                      pmul(R, ppow(R, T.Phi1, j1),
                                           ppow(R, T.Phi2, j2 - P[2]))))
                # exit line law: line(cofactor) == parent - w3Phi3
                lc = self.line(b, (j0, j1, j2 - P[2]))
                if lc != linep - T3.w3Phi3:
                    viol("D3-LINE", name, f"exit dline={lc-linep}")
                Q = padd(R, Q, cof)
                for k, dcells in self.lvl3_cells.items():
                    for a0, a1, cD in dcells:
                        wsh, (L, X, Y) = digit_split_norm(T, pmul(R, b, cD))
                        base = (j0 + a0, j1 + a1, j2 - P[2] + T3.e2*k)
                        pw = R["pi_pow"](wsh)
                        edge_check("corr3-L", base,
                                   pneg(R, pscal(R, pw, L)), "zero")
                        edge_check("corr3-X", base,
                                   pneg(R, pscal(R, R["pi_pow"](wsh+1), X)),
                                   "pos")
                        edge_check("corr3-Y", (base[0] + 1, base[1], base[2]),
                                   pneg(R, pscal(R, pw, Y)), "pos")
        # all remaining cells are reduced leaves
        Rpoly = []
        for key, b in cells.items():
            leaves[key] = pnorm(R, padd(R, leaves.get(key, []), b))
            Rpoly = padd(R, Rpoly, pmul(R, b,
                          pmul(R, ppow(R, T.Phi0, key[0]),
                               pmul(R, ppow(R, T.Phi1, key[1]),
                                    ppow(R, T.Phi2, key[2])))))
        res["pops"] = res.get("pops", 0) + pops
        res["maxj"] = [max(a, c) for a, c in zip(res.get("maxj", [0,0,0]),
                                                 maxj)]
        # W-WIN census (display-grade)
        if (maxj[0] > 2*P[0]-1 or maxj[1] > 2*P[1]-1 or maxj[2] > 2*P[2]-1):
            res["win_over"] = res.get("win_over", 0) + 1
        return pnorm(R, Rpoly), pnorm(R, Q), leaves

# ---------------- the zh-kernel at m = 3 (note S3.1) -----------------------
class Zh3:
    def __init__(self, T4):
        T3 = T4.T3; T = T3.T
        self.T4, self.T3, self.T = T4, T3, T
        K3, K2, K1 = T4.K3, T3.K2, T.K1
        self.K3 = K3
        self.z3 = T4.z3
        self.emb2 = lambda v: K3["embed"](v)
        self.emb1 = lambda v: K3["embed"](K2["embed"](v))
        self.emb0 = lambda v: K3["embed"](K2["embed"](K1["embed"](v)))
        self.z2, self.z1 = T3.z2, T.z1

    def val(self, b, j, target):
        """res(bbar)*zh((j0,j1,j2); target) per S3.1, or None if off-grid."""
        T4, T3, T = self.T4, self.T3, self.T
        K3, K2, K1 = self.K3, T3.K2, T.K1
        j0, j1, j2 = j
        s3t, _ = eq12(target, T3.e2, T3.h2)
        if (j2 - s3t) % T3.e2: return None
        t3 = (j2 - s3t)//T3.e2
        lam2 = (target - j2*T3.gamma3)
        if lam2 % T3.e2: return None
        lam2 //= T3.e2
        s2t, _ = eq12(lam2, T.e1, T.h1)
        if (j1 - s2t) % T.e1: return None
        t2 = (j1 - s2t)//T.e1
        lam1 = (lam2 - j1*T.gamma2)
        if lam1 % T.e1: return None
        lam1 //= T.e1
        s1t, _ = eq12(lam1, T.e0, T.h0)
        if (j0 - s1t) % T.e0: return None
        t1 = (j0 - s1t)//T.e0
        wb = w0poly(T.R, b)
        r0 = T.res_digit(b, wb)          # K0 element (unit part residue)
        v = self.emb0(r0)
        v = K3["mul"](self.emb1(K1["pow"](self.z1, t1)), v)
        v = K3["mul"](self.emb1(T.eps1(lam1)), v)
        v = K3["mul"](self.emb2(K2["pow"](self.z2, t2)), v)
        v = K3["mul"](self.emb2(T3.eps2(lam2)), v)
        v = K3["mul"](K3["pow"](self.z3, t3), v)
        return v

    def val_noeps2(self, b, j, target):
        """MUTATION tooth: the eps2(lam2) factor dropped."""
        full = self.val(b, j, target)
        if full is None: return None
        T3, K3 = self.T3, self.K3
        j2 = j[2]
        lam2 = (target - j2*T3.gamma3)//T3.e2
        e2v = self.emb2(T3.eps2(lam2))
        return K3["mul"](K3["pow"](e2v, -1), full)

# ---------------- one m = 3 tower run ---------------------------------------
def run_m3_tower(tag, d0, r0, r1, r2, r3, r4, kind, p, results):
    t0 = time.time()
    T5 = ILN5.Tower5(kind, p, d0, r0, r1, r2, r3, r4, f"{kind},p{p},{tag}")
    T4 = T5.T4; T3 = T4.T3; T = T3.T; R = T.R
    C5 = ILN5.Composite5(T5)
    E3 = Engine3(T4)
    TR = Tree3(E3)
    ZH = Zh3(T4)
    name = f"{tag}/{kind},p={p}"
    certs = E3.certs()
    certs["id1"], certs["id2"], certs["id3"] = (TR.cert_id1, TR.cert_id2,
                                                TR.cert_id3)
    if not all(certs.values()):
        viol("CERT", name, certs)
    res = dict(tower=name, E5=T5.E5, degPhi3=T3.degPhi3, gamma4=T4.gamma4,
               certs=certs,
               muw=[str(TR.w0f), str(TR.w1f), str(TR.w2f)])
    # ---- pair loop: firing + D5 census ----
    W1 = list(range(C5.Gamma0, C5.Gamma0 + T5.E5))
    e3, e2, e1, e0 = T4.e3, T3.e2, T.e1, T.e0
    s1f = lambda b: eq12(b, T.e0, T.h0)[0]
    s2f = lambda b: eq12(b, T.e1, T.h1)[0]
    s3f = lambda b: eq12(b, T3.e2, T3.h2)[0]
    # LAW-DCX-4 u-chain (S6.1): u3 = gamma4 -> u2 -> u1
    u3 = T4.gamma4
    n2 = u3 - s3f(u3)*T3.gamma3
    assert n2 % e2 == 0 and n2 >= 0, "u2 chain"
    u2 = n2//e2
    n1 = u2 - s2f(u2)*T.gamma2
    assert n1 % e1 == 0 and n1 >= 0, "u1 chain"
    u1c = n1//e1
    res["uchain"] = [u3, u2, u1c]
    res["s_chain"] = [s3f(u3), s2f(u2), s1f(u1c)]
    cen = dict(pairs=0, fired=0, e1nz=0, track=0, q1nz=0, meas=0,
               pred=0, mism=0, d_direct=0, d_c2pos=0, d_c1pos=0)
    anch = {}
    def subanchor(g):
        if g in anch: return anch[g]
        s5, s4, s3, s2, s1, b4, b3, b2, b1, u1 = C5.split(g)
        f = pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1))
        f = pmul(R, f, ppow(R, T.Phi1, s2))
        f = pmul(R, f, ppow(R, T.Phi2, s3))
        anch[g] = (pnorm(R, f), (s4, s3, s2, s1))
        return anch[g]
    inputs = {}
    mism_samples = []
    for ga in W1:
        for gb in W1:
            cen["pairs"] += 1
            ah, (s4a, s3a, s2a, s1a) = subanchor(ga)
            bh, (s4b, s3b, s2b, s1b) = subanchor(gb)
            T4sum = s4a + s4b
            E1IH, E0IH = pdivmod(R, pmul(R, ah, bh), T3.Phi3)
            e1nz = bool(pnorm(R, E1IH))
            if e1nz: cen["e1nz"] += 1
            fired = (T4sum >= e3) or (e1nz and T4sum == e3 - 1)
            if fired:
                cen["fired"] += 1
                if pnorm(R, E0IH):
                    k = RM2.poly_key(R, E0IH)
                    if k not in inputs: inputs[k] = (E0IH, "E0")
                if e1nz:
                    k = RM2.poly_key(R, E1IH)
                    if k not in inputs: inputs[k] = (E1IH, "E1")
            # D5: LAW-DCX-4 vs measured (census-grade)
            track = (s4a == e3 - 1 and s4b == e3 - 1 and e1nz)
            if track: cen["track"] += 1
            meas = False
            if e1nz:
                Q1, _ = pdivmod(R, pmul(R, E1IH, E3.Chat3), T3.Phi3)
                if pnorm(R, Q1):
                    cen["q1nz"] += 1
                    d4pl = T4sum // e3
                    meas = ((d4pl == 1 and s4a == e3-1 and s4b == e3-1)
                            or (T4sum == e3 - 1 and e3 == 1))
            pool1 = s1a + s1b + s1f(u1c)
            c1 = pool1 // e0
            pool2 = s2a + s2b + s2f(u2) + c1
            c2 = pool2 // e1
            top = (s3a + s3b) + s3f(u3) + c2
            pred = track and (top >= 2*e2)
            if pred:
                cen["pred"] += 1
                if (s3a + s3b) + s3f(u3) >= 2*e2: cen["d_direct"] += 1
                if c2 > 0: cen["d_c2pos"] += 1
                if c1 > 0: cen["d_c1pos"] += 1
            if meas: cen["meas"] += 1
            if meas != pred:
                cen["mism"] += 1
                if len(mism_samples) < 8:
                    mism_samples.append((ga, gb, meas, pred,
                                         s3a+s3b, s3f(u3), c2, 2*e2))
    res["census"] = cen
    res["mism_samples"] = mism_samples
    # ---- engine inputs: fired + breadth ----
    for u in (0, 1):
        bs = [[R["one"]]]
        if d0 >= 2: bs.append([R["zero"], R["one"]])
        for b in bs:
            for i in range(T.e0*T.g0):
                for j in range(T.e1*T.g1):
                    for k in range(T3.e2*T3.g2):
                        f = pscal(R, R["pi_pow"](u), b)
                        f = pmul(R, f, ppow(R, T.Phi0, i))
                        f = pmul(R, f, ppow(R, T.Phi1, j))
                        f = pmul(R, f, ppow(R, T.Phi2, k))
                        kk = RM2.poly_key(R, pnorm(R, f))
                        if kk not in inputs: inputs[kk] = (pnorm(R, f), "BR")
    two = padd(R, pmul(R, ppow(R, T.Phi2, T3.e2*T3.g2 - 1), T.Phi1),
               pscal(R, R["pi_pow"](1), T.Phi0))
    inputs[RM2.poly_key(R, pnorm(R, two))] = (pnorm(R, two), "BRsum")
    zh_checked = zh_mut_diff = 0
    for kk, (f, prov) in sorted(inputs.items()):
        c = E3.call(f)
        note(f"D1_{prov}")
        if not (c["okW_R"] and c["okW_Q"]):
            viol("D1-WEIGHT", name, f"{prov} lam={c['lam']} wR={c['wR']} "
                                    f"wQ={c['wQ']} tgt={c['target']}")
        if c["okW_R"] and not c["okRead"]:
            viol("D1-READ", name, f"{prov} lam={c['lam']} epsp={c['epsp']}")
        if not c["eps_id"]:
            viol("D1-EPS", name, prov)
        if c["v_zero"]: note("v_zero_rows")
        out = TR.run(pmul(R, f, E3.Chat3), name, res)
        if out is None: continue
        Rp, Qp, leaves = out
        note("D2_CONS")
        if Rp != pnorm(R, c["R"]) or Qp != pnorm(R, c["Q"]):
            viol("D2-CONS", name, f"{prov} tree != division")
        # D3 leaf weight-exactness + D4 zh sums
        target = c["target"]
        zsum = E3.K3["zero"]
        for j, b in leaves.items():
            ln = TR.line(b, j)
            if T3.w3(pmul(R, b, pmul(R, ppow(R, T.Phi0, j[0]),
                     pmul(R, ppow(R, T.Phi1, j[1]),
                          ppow(R, T.Phi2, j[2]))))) != ln:
                viol("D3-LEAF", name, f"{prov} leaf {j} w3 != line")
            if ln == target:
                zv = ZH.val(b, j, target)
                # per-leaf: zh formula == harness single-cell read
                cellpoly = pmul(R, b, pmul(R, ppow(R, T.Phi0, j[0]),
                            pmul(R, ppow(R, T.Phi1, j[1]),
                                 ppow(R, T.Phi2, j[2]))))
                hv = E3.R3v_at(cellpoly, target)
                zh_checked += 1
                if zv is None:
                    if not E3.K3["isz"](hv):
                        viol("D4-ZH", name, f"{prov} off-grid leaf reads !=0")
                else:
                    if zv != hv:
                        viol("D4-ZH", name, f"{prov} leaf {j} zh != harness")
                    zsum = E3.K3["add"](zsum, zv)
                    mz = ZH.val_noeps2(b, j, target)
                    if mz != zv: zh_mut_diff += 1
        note("D4_SUM")
        if c["okW_R"] and zsum != c["pred"]:
            viol("D4-SUM", name, f"{prov} zh-sum != z3^eps' v tau3")
    res["n_inputs"] = len(inputs)
    res["zh_checked"] = zh_checked
    res["zh_mut_diff"] = zh_mut_diff
    print(f"-- {name}: E5={T5.E5} fired={cen['fired']} inputs={len(inputs)} "
          f"track={cen['track']} meas/pred={cen['meas']}/{cen['pred']} "
          f"mism={cen['mism']} pops={res.get('pops',0)} "
          f"maxj={res.get('maxj')} zh={zh_checked} "
          f"({time.time()-t0:.1f}s)")
    results.append(res)

# ---------------- D6a: RM2A/Zp3 consistency re-run --------------------------
def rerun_rm2a(results):
    t0 = time.time()
    T4 = Tower4("Zp", 3, 1, (2,1,1), (2,1,1), (2,1,1), (1,1,2), "RM2A-rr")
    E = RM2.Engine2(T4)
    C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T; R = T.R
    W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
    e2 = T3.e2
    cen = dict(pairs=0, fired=0, II1=0, II2=0, II3=0, e1nz=0, q1nz=0,
               dcx_meas=0)
    cache = {}
    inputs = {}
    for ga in W1:
        for gb in W1:
            cen["pairs"] += 1
            ah, (s3a, s2a) = RM2.anchor2(C, cache, ga)
            bh, (s3b, s2b) = RM2.anchor2(C, cache, gb)
            T3sum = s3a + s3b
            E1IH, E0IH = pdivmod(R, pmul(R, ah, bh), T.Phi2)
            e1nz = bool(pnorm(R, E1IH))
            if e1nz: cen["e1nz"] += 1
            fire2 = (T3sum >= e2); fire3 = (e1nz and T3sum == e2 - 1)
            if fire2 or fire3:
                cen["fired"] += 1
                cen["II2" if (fire2 and e1nz) else
                    "II1" if fire2 else "II3"] += 1
                if pnorm(R, E0IH):
                    k = RM2.poly_key(R, E0IH)
                    if k not in inputs: inputs[k] = E0IH
                if e1nz:
                    k = RM2.poly_key(R, E1IH)
                    if k not in inputs: inputs[k] = E1IH
            if e1nz:
                Q1, _ = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
                if pnorm(R, Q1):
                    cen["q1nz"] += 1
                    d3pl = T3sum // e2
                    if ((d3pl == 1 and s3a == e2-1 and s3b == e2-1)
                            or (T3sum == e2-1 and e2 == 1)):
                        cen["dcx_meas"] += 1
    nviol = 0
    for k, f in sorted(inputs.items()):
        c = E.call(f)
        if not (c["okW_R"] and c["okW_Q"] and c["okRead"] and c["eps_id"]):
            nviol += 1; viol("D6a-ENGINE", "RM2A-rr", str(k)[:60])
        t = RM2.Tree(E, f).run()
        if (t.status == "CAP" or t.bad_edges or
                t.Rpoly != pnorm(R, c["R"]) or t.Q != pnorm(R, c["Q"])):
            nviol += 1; viol("D6a-TREE", "RM2A-rr", str(k)[:60])
    stored = json.load(open(os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        "rm2_probe_results.json")))
    st = [t for t in stored["towers"] if t["tower"] == "RM2A/Zp,p=3"][0]
    keys = ["pairs", "fired", "II1", "II2", "II3", "e1nz", "q1nz",
            "dcx_meas"]
    match = all(cen[k] == st["census"][k] for k in keys)
    match = match and (len(inputs) == st["n_inputs"])
    if not match:
        viol("D6a-CENSUS", "RM2A-rr",
             f"got={cen} n={len(inputs)} stored={st['census']}")
    results.append(dict(tower="D6a-RM2A-rerun", census=cen,
                        n_inputs=len(inputs), engine_viol=nviol,
                        census_match=bool(match)))
    print(f"-- D6a RM2A/Zp3 rerun: census_match={match} "
          f"engine/tree viol={nviol} ({time.time()-t0:.1f}s)")

# ---------------- D6b: DCX3 v2 law re-run on EX1/Zp3 ------------------------
def rerun_dcx3_ex1(results):
    t0 = time.time()
    T4 = Tower4("Zp", 3, 1, (3,1,1), (4,1,1), (2,3,1), (2,1,1), "EX1-rr")
    C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T; R = T.R
    Chat2 = pnorm(R, padd(R, T3.Phi3, pneg(R, ppow(R, T.Phi2, T3.e2))))
    e2, e1, e0 = T3.e2, T.e1, T.e0
    s1f = lambda b: eq12(b, T.e0, T.h0)[0]
    s2f = lambda b: eq12(b, T.e1, T.h1)[0]
    s2g3 = s2f(T3.gamma3)
    u0 = (T3.gamma3 - s2g3*T.gamma2)//T.e1
    W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
    cache = {}
    live = meas_n = mism = 0
    for ga in W1:
        for gb in W1:
            ah, (s3a, s2a) = RM2.anchor2(C, cache, ga)
            bh, (s3b, s2b) = RM2.anchor2(C, cache, gb)
            spa = C.split(ga); spb = C.split(gb)
            s1a, s1b = spa[3], spb[3]      # Composite4.split: s4,s3,s2,s1,...
            E1IH, _ = pdivmod(R, pmul(R, ah, bh), T.Phi2)
            e1nz = bool(pnorm(R, E1IH))
            track = (s3a == e2-1 and s3b == e2-1 and e1nz)
            meas = False
            if e1nz:
                Q1, _ = pdivmod(R, pmul(R, E1IH, Chat2), T.Phi2)
                if pnorm(R, Q1):
                    d3pl = (s3a + s3b)//e2
                    meas = ((d3pl == 1 and s3a == e2-1 and s3b == e2-1)
                            or (s3a + s3b == e2-1 and e2 == 1))
            lvl2 = (s2a + s2b) + s2g3
            pool = s1a + s1b + s1f(u0)
            pred = track and (lvl2 + pool//e0 >= 2*e1)
            if pred: live += 1
            if meas: meas_n += 1
            if meas != pred: mism += 1
    stored = json.load(open(os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        "dcx3_sharp_v2_results.json")))
    st = [t for t in stored["towers"] if t["tower"] == "EX1/Zp,p=3"][0]
    ok = (live == st["census"]["pred_live"]
          and meas_n == st["census"]["dcx_meas"]
          and mism == st["census"]["mism"] == 0)
    if not ok:
        viol("D6b-V2", "EX1-rr",
             f"live={live} meas={meas_n} mism={mism} stored={st['census']}")
    results.append(dict(tower="D6b-EX1-v2-rerun", live=live, meas=meas_n,
                        mism=mism, stored_ok=bool(ok)))
    print(f"-- D6b EX1/Zp3 v2 rerun: live={live} meas={meas_n} mism={mism} "
          f"stored_match={ok} ({time.time()-t0:.1f}s)")

# ---------------- D7 [r1 REPAIR ADDENDUM]: the d0 = 1 FLAT-corner leg --------
# Added at repair round 1 (2026-08-08 campaign, wallclock 2026-08-04), per
# PE-F1 / note S4.1 branch (b) + S4.2: the d0 = 1 flat shapes are INSIDE the
# AMENDED T-scope, so they join the tested scope as a predicted-0 leg.
# POST-SEAL-LABELED like the rest of this diagnostic: NOT a proof step.
# D1-D6 above are UNTOUCHED; their stdout must re-run byte-exact.

class FlatTree3(Tree3):
    """Tree3 with the S4.1 BRANCH-(b) weights (r1): the near-ceiling rule
    w_i := midpoint of (S_i, w_{i-1}P_{i-1}), S_i := sum_{l<i} w_l*rho_l,
    rho_0 = P_0 - 1 (d0 = 1), rho_1 = P_1 - 1 — valid at d0 = 1 for
    ARBITRARY e_i >= 1; (A_i)/(B_i) asserted strictly.  (The base-class
    init runs first with its own rule; on this leg's roster its interval
    asserts happen to pass, and its weights are then OVERWRITTEN.)"""
    def __init__(self, E3):
        Tree3.__init__(self, E3)
        T, T3 = self.T, self.T3
        d0 = len(T.Phi0) - 1
        assert d0 == 1, "D7 flat leg is d0 = 1 only (branch (b))"
        rho = [Fr(self.P0 - 1), Fr(self.P1 - 1)]
        w = [Fr(1)]
        for i, (ei, Pprev) in enumerate(((T.e1, self.P0), (T3.e2, self.P1)),
                                        start=1):
            S = sum(w[l]*rho[l] for l in range(i))
            lo, hi = S, w[i-1]*Pprev
            assert lo < hi, f"branch-(b) interval empty at i={i}"
            w.append((lo + hi)/2)
            assert w[i] < w[i-1]*Pprev, f"(A_{i}) fails"
            assert w[i]*ei > S, f"(B_{i}) fails"
        self.w0f, self.w1f, self.w2f = w

def _d7_retag(n0):
    """Re-tag violations raised by reused Tree3 machinery into the D7
    family so the untouched D1-D6 verdict counters stay clean."""
    for idx in range(n0, len(VIOL)):
        if not VIOL[idx][0].startswith("D7"):
            VIOL[idx] = ("D7-" + VIOL[idx][0],) + tuple(VIOL[idx][1:])

def run_m3_flat_tower(tag, r0, r1, r2, r3, kind, p, results):
    t0 = time.time()
    T4 = Tower4(kind, p, 1, r0, r1, r2, r3, f"D7{tag}")
    T3 = T4.T3; T = T3.T; R = T.R
    E3 = Engine3(T4)
    n0 = len(VIOL)
    TR = FlatTree3(E3)
    ZH = Zh3(T4)
    name = f"D7-{tag}/{kind},p={p}"
    certs = E3.certs()
    certs["id1"], certs["id2"], certs["id3"] = (TR.cert_id1, TR.cert_id2,
                                                TR.cert_id3)
    if not all(certs.values()):
        viol("D7-CERT", name, certs)
    res = dict(tower=name, leg="D7-r1-flat", d0=1,
               eshape=[T.e0, T.e1, T3.e2], degPhi3=T3.degPhi3,
               gamma4=T4.gamma4, certs=certs,
               muwB=[str(TR.w0f), str(TR.w1f), str(TR.w2f)])
    # breadth inputs (d0 = 1): pi^u * Phi0^i Phi1^j Phi2^k reduced, + a sum
    inputs = {}
    for u in (0, 1):
        for i in range(T.e0*T.g0):
            for j in range(T.e1*T.g1):
                for k in range(T3.e2*T3.g2):
                    f = pscal(R, R["pi_pow"](u), [R["one"]])
                    f = pmul(R, f, ppow(R, T.Phi0, i))
                    f = pmul(R, f, ppow(R, T.Phi1, j))
                    f = pmul(R, f, ppow(R, T.Phi2, k))
                    kk = RM2.poly_key(R, pnorm(R, f))
                    if kk not in inputs: inputs[kk] = (pnorm(R, f), "BR")
    two = padd(R, pmul(R, ppow(R, T.Phi2, T3.e2*T3.g2 - 1), T.Phi1),
               pscal(R, R["pi_pow"](1), T.Phi0))
    two = pnorm(R, two)
    if two and len(two) - 1 < T3.degPhi3:
        inputs[RM2.poly_key(R, two)] = (two, "BRsum")
    zh_checked = 0
    d7cnt = dict(calls=0, v_zero=0)
    for kk, (f, prov) in sorted(inputs.items()):
        c = E3.call(f)
        d7cnt["calls"] += 1
        if not (c["okW_R"] and c["okW_Q"]):
            viol("D7-WEIGHT", name, f"{prov} lam={c['lam']} wR={c['wR']} "
                                    f"wQ={c['wQ']} tgt={c['target']}")
        if c["okW_R"] and not c["okRead"]:
            viol("D7-READ", name, f"{prov} lam={c['lam']} epsp={c['epsp']}")
        if not c["eps_id"]:
            viol("D7-EPS", name, prov)
        if c["v_zero"]: d7cnt["v_zero"] += 1
        out = TR.run(pmul(R, f, E3.Chat3), name, res)
        if out is None:
            _d7_retag(n0); continue
        Rp, Qp, leaves = out
        if Rp != pnorm(R, c["R"]) or Qp != pnorm(R, c["Q"]):
            viol("D7-CONS", name, f"{prov} tree != division")
        target = c["target"]
        zsum = E3.K3["zero"]
        for j, b in leaves.items():
            ln = TR.line(b, j)
            if T3.w3(pmul(R, b, pmul(R, ppow(R, T.Phi0, j[0]),
                     pmul(R, ppow(R, T.Phi1, j[1]),
                          ppow(R, T.Phi2, j[2]))))) != ln:
                viol("D7-LEAF", name, f"{prov} leaf {j} w3 != line")
            if ln == target:
                zv = ZH.val(b, j, target)
                cellpoly = pmul(R, b, pmul(R, ppow(R, T.Phi0, j[0]),
                            pmul(R, ppow(R, T.Phi1, j[1]),
                                 ppow(R, T.Phi2, j[2]))))
                hv = E3.R3v_at(cellpoly, target)
                zh_checked += 1
                if zv is None:
                    # L-GRID (r1): on-line leaves must be ON-grid
                    viol("D7-GRID", name, f"{prov} on-line leaf {j} off-grid")
                    if not E3.K3["isz"](hv):
                        viol("D7-ZH", name, f"{prov} off-grid leaf reads !=0")
                else:
                    if zv != hv:
                        viol("D7-ZH", name, f"{prov} leaf {j} zh != harness")
                    zsum = E3.K3["add"](zsum, zv)
        if c["okW_R"] and zsum != c["pred"]:
            viol("D7-SUM", name, f"{prov} zh-sum != z3^eps' v tau3")
    _d7_retag(n0)
    res["n_inputs"] = len(inputs)
    res["zh_checked"] = zh_checked
    res["calls"] = d7cnt["calls"]
    res["v_zero"] = d7cnt["v_zero"]
    print(f"-- {name}: e=({T.e0},{T.e1},{T3.e2}) d0=1 "
          f"wB=({TR.w0f},{TR.w1f},{TR.w2f}) inputs={len(inputs)} "
          f"pops={res.get('pops',0)} maxj={res.get('maxj')} "
          f"zh={zh_checked} vzero={d7cnt['v_zero']} "
          f"({time.time()-t0:.1f}s)")
    results.append(res)

# ---------------- main -------------------------------------------------------
def main():
    t0 = time.time()
    results = []
    print("== rmengine_diag: POST-SEAL diagnostic for RMENGINE (S9) ==")
    # m = 3 rosters (all T-scope: e0=e1=e2=2; g3=1)
    run_m3_tower("RME3A", 1, (2,1,1), (2,1,1), (2,1,1), (2,1,1), (1,1,2),
                 "Zp", 3, results)
    run_m3_tower("RME3A", 1, (2,1,1), (2,1,1), (2,1,1), (2,1,1), (1,1,2),
                 "Fpt", 2, results)
    run_m3_tower("RME3B", 1, (2,1,1), (2,1,1), (2,3,1), (1,1,1), (2,1,1),
                 "Zp", 3, results)
    run_m3_tower("RME3C", 2, (2,1,1), (2,1,1), (2,1,1), (1,1,1), (1,1,2),
                 "Zp", 3, results)
    rerun_rm2a(results)
    rerun_dcx3_ex1(results)
    # D7 [r1 repair addendum, PE-F1]: the d0 = 1 flat shapes join the
    # tested scope (amended T-scope).  Appended AFTER the untouched D1-D6
    # legs; everything they print above must remain byte-exact.
    run_m3_flat_tower("FLTTOP", (2,1,1), (2,1,1), (1,1,1), (2,1,1),
                      "Zp", 3, results)
    run_m3_flat_tower("FLTTOP", (2,1,1), (2,1,1), (1,1,1), (2,1,1),
                      "Fpt", 2, results)
    run_m3_flat_tower("FLTMID", (2,1,1), (1,1,1), (2,1,1), (2,1,1),
                      "Zp", 3, results)
    run_m3_flat_tower("FLTDBL", (2,1,1), (1,1,1), (1,1,1), (2,1,1),
                      "Zp", 3, results)
    nD1 = sum(1 for v in VIOL if v[0].startswith("D1"))
    nD2 = sum(1 for v in VIOL if v[0].startswith("D2"))
    nD3 = sum(1 for v in VIOL if v[0].startswith("D3"))
    nD4 = sum(1 for v in VIOL if v[0].startswith("D4"))
    nD6 = sum(1 for v in VIOL if v[0].startswith("D6") or v[0] == "CERT")
    mism_tot = sum(r["census"]["mism"] for r in results if "census" in r
                   and "mism" in r.get("census", {}))
    print()
    print(f"D1 VERDICT (four box clauses at m=3, predicted-0): "
          f"{'GREEN' if nD1 == 0 else 'RED'} [{nD1} violations]")
    print(f"D2 VERDICT (CONS + mu strict descent, predicted-0): "
          f"{'GREEN' if nD2 == 0 else 'RED'} [{nD2} violations]")
    print(f"D3 VERDICT (line calculus exact, predicted-0): "
          f"{'GREEN' if nD3 == 0 else 'RED'} [{nD3} violations]")
    print(f"D4 VERDICT (zh-kernel == harness reads == box pred, "
          f"predicted-0): {'GREEN' if nD4 == 0 else 'RED'} "
          f"[{nD4} violations]")
    print(f"D5 CENSUS (LAW-DCX-4 vs measured, census-grade): "
          f"mismatches={mism_tot} over "
          f"{sum(r['census']['pairs'] for r in results if 'census' in r and 'pairs' in r.get('census', {}))} pairs")
    print(f"D6 VERDICT (RM2A + DCX3-v2 artifact consistency, predicted-0): "
          f"{'GREEN' if nD6 == 0 else 'RED'} [{nD6} violations]")
    nD7 = sum(1 for v in VIOL if v[0].startswith("D7"))
    print(f"D7 VERDICT [r1 ADDENDUM] (box clauses + tree + branch-(b) mu + "
          f"lines + zh on d0=1 FLAT shapes, predicted-0): "
          f"{'GREEN' if nD7 == 0 else 'RED'} [{nD7} violations]")
    print(f"counts: {dict(sorted(CNT.items()))}")
    print(f"total violations: {len(VIOL)}; elapsed {time.time()-t0:.1f}s")
    out = dict(counts=CNT, violations=VIOL, towers=results,
               elapsed=time.time()-t0)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "rmengine_diag_results.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)

if __name__ == "__main__":
    main()
