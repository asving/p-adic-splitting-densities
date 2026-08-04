#!/usr/bin/env python3
"""rmengine_pe_reimpl.py — RMENGINE-PE round-1 HOSTILE pass, EXECUTION leg.

F2c-genre reimplementation FROM THE NOTE ALONE
(lean/notes/openmath/RMENGINE_2026-08-08.md @ bf18bfe): the note's NEW generic
objects are implemented from the note text, BEFORE re-opening rmengine_diag.py
(which was NOT read).  The sealed harness calculus (grb_order2_check /
strata3_probe / iterlaw4_probe / iterlawn_diag) is consumed READ-ONLY as the
definitional substrate, exactly per the note's PRINT-CONSUMPTION DISPLAY.

Reimplemented from the note:
  * S2.1/S2.2  cells, lines, DIGIT-SPLIT children, the three identity
               families, the E1-priority tree, L-EXACT reassembly
  * S3.1       the lambda/t-chain, the formal read monomial zh, L-ZMULT
               (self-curing internal carries, single top carry)
  * S3.2       L-LINE exact edge quanta (promotion / correction-main / junk /
               exit), leaf w == line
  * S4.1       the (A_i)/(B_i) interval-family measure: weights constructed
               per the note's existence argument (midpoint rule), interval
               inhabitation CHECKED at every probed shape; strict mu-descent
               on every in-tree edge (T-scope); flat-shape feasibility probe
  * S0.2/S5.2  the four box clauses (C-W_R)/(C-W_Q)/(C-READ)/(C-EPS) at the
               canonical division, incl. the z_m^{eps'} v tau_m read pin
  * S6.1/S6.2  LAW-DCX-(m+1): u_l chain, nested pools/carries, L-CAP
               (census-grade; m=2 fresh shapes, m=3 fresh, m=4 FIRST DATA)

FRESH instances (own roster, disjoint from the diag's RME3A/B/C and from the
RM2/DCX3 rosters): m=2 and m=3 towers incl. all-e_i=2 T-boundary shapes, one
FLAT e_1=1 shape (fence predicate must FIRE; theorem NOT tested there), a
FLAT e_2=1 m=3 shape probing the S4.2 fence-box mechanism claim, and an m=4
SMOKE tower (the first level-4 engine data ever).  Mutation controls MU1-MU7.
Exact arithmetic, deterministic, no RNG.  Exit 0 iff zero violations in every
VERDICT family (census families report, never gate).
"""
import sys, os, time, json, hashlib
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import grb_order2_check as G
from grb_order2_check import (dev, pnorm, padd, pneg, pmul, ppow, pscal,
                              pdivmod, eq12, bezout, INF, w0, Tower)
import strata3_probe as S3MOD
from strata3_probe import Tower3
import iterlawr_probe as ILR          # installs the psi2 shim (import order!)
import iterlaw4_probe as IL4
from iterlaw4_probe import Tower4
import iterlawn_diag as ILN
from iterlawn_diag import Tower5

VIOL = []          # verdict-family violations (gate exit code)
CENS = []          # census-family anomalies (report only)
CNT  = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:220]))
    print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:220]}")
def cens(fam, tag, detail):
    CENS.append((fam, tag, str(detail)[:220]))
    print(f"  census-note [{fam}] {tag}: {str(detail)[:220]}")

def prod(xs):
    r = 1
    for x in xs: r *= x
    return r

# ===================== level-4 mirror layer (one level up) ====================
# The note's class pin (S0.1) + the harness one-level-up mirror discipline.
# Needed only for the m=4 smoke: Phi5 = canonical lift of psi4 at g4 = 1.
def realize4(T5, tau, beta):
    """K4 class tau realized at level-4 weight beta (realize3 mirror)."""
    T4 = T5.T4; R = T4.R
    s, u = eq12(beta, T4.e3, T4.h3)
    C = []
    for mm in range(T4.g3):
        tm = tau[mm] if mm < len(tau) else T4.K3["zero"]
        if T4.K3["isz"](tm): continue
        k = s + mm*T4.e3
        num = beta - k*T4.gamma4
        assert num % T4.e3 == 0
        gm = num // T4.e3
        tm_adj = T4.K3["mul"](T4.K3["inv"](T4.eps3(gm)), tm)
        C = padd(R, C, pmul(R, T4.realize3(tm_adj, gm),
                            ppow(R, T4.T3.Phi3, k)))
    return C

def build_Phi5(T5):
    """canonical state-key lift, one level up (build_Phi4 mirror)."""
    T4 = T5.T4; R = T4.R
    P = []
    for k, c in enumerate(T5.psi4):
        if T5.K4["isz"](c): continue
        gp = (T5.g4 - k)*T5.gamma5
        if gp == 0:
            Ck = [R["one"]]
        else:
            tau = T5.K4["mul"](T5.K4["inv"](T5.eps4(gp)), c)
            Ck = realize4(T5, tau, gp)
        P = padd(R, P, pmul(R, Ck, ppow(R, T4.Phi4, T5.e4*k)))
    return P

# ============================ the engine wrapper ==============================
class Eng:
    """Level-m engine data.  Towers/reads/eps/realize come from the sealed
    harness (read-only); everything the note NEWLY displays is computed here
    from the note text."""
    def __init__(self, m, kind, p, d0, reads, tag):
        assert len(reads) == m + 1
        self.m, self.kind, self.p, self.d0, self.reads, self.tag = \
            m, kind, p, d0, reads, tag
        if m == 2:
            T3 = Tower3(kind, p, d0, reads[0], reads[1], reads[2], tag)
            T = T3.T
            self.top = T3; self.grbT = T; self.R = T.R
            self.Phis = [T.Phi0, T.Phi1, T.Phi2]
            self.PhiUp = T3.Phi3
            self.gam = {1: T.gamma1, 2: T.gamma2, 3: T3.gamma3}
            self.K = [T.K0, T.K1, T3.K2]
            self.wm = T.w2
            self.Rvm = T3.R2v
            self.wmPhi = T.w2Phi2
            self.degPhim = T.degPhi2
            self.harness_eps = [None, T.eps1, None]
        elif m == 3:
            T4 = Tower4(kind, p, d0, reads[0], reads[1], reads[2], reads[3], tag)
            T3 = T4.T3; T = T3.T
            self.top = T4; self.grbT = T; self.R = T.R
            self.Phis = [T.Phi0, T.Phi1, T.Phi2, T3.Phi3]
            self.PhiUp = T4.Phi4
            self.gam = {1: T.gamma1, 2: T.gamma2, 3: T3.gamma3, 4: T4.gamma4}
            self.K = [T.K0, T.K1, T3.K2, T4.K3]
            self.wm = T3.w3
            self.Rvm = T4.R3v
            self.wmPhi = T3.w3Phi3
            self.degPhim = T3.degPhi3
            self.harness_eps = [None, T.eps1, T3.eps2, None]
        elif m == 4:
            T5 = Tower5(kind, p, d0, reads[0], reads[1], reads[2], reads[3],
                        reads[4], tag)
            T4 = T5.T4; T3 = T4.T3; T = T3.T
            self.top = T5; self.grbT = T; self.R = T.R
            self.Phis = [T.Phi0, T.Phi1, T.Phi2, T3.Phi3, T4.Phi4]
            self.PhiUp = build_Phi5(T5)
            self.gam = {1: T.gamma1, 2: T.gamma2, 3: T3.gamma3,
                        4: T4.gamma4, 5: T5.gamma5}
            self.K = [T.K0, T.K1, T3.K2, T4.K3, T5.K4]
            self.wm = T4.w4
            self.Rvm = T5.R4v
            self.wmPhi = T4.w4Phi4
            self.degPhim = T4.degPhi4
            self.harness_eps = [None, T.eps1, T3.eps2, T4.eps3, None]
        else:
            raise ValueError(m)
        self.Km = self.K[m]
        self.e = [r[0] for r in reads]; self.h = [r[1] for r in reads]
        self.g = [r[2] for r in reads]
        assert self.g[m] == 1, "engine needs g_m = 1 (box setting)"
        self.P = [self.e[l]*self.g[l] for l in range(m)]
        self.Em = prod(self.e[:m])
        self.Gam = [self.gam[l+1]*prod(self.e[l+1:m]) for l in range(m)]
        self.bez = [bezout(self.e[l], self.h[l]) for l in range(m)]
        # z_l embedded into K_m  (zsKm[l], 1 <= l <= m)
        self.zsKm = [None]*(m+1)
        for l in range(1, m+1):
            v = self.K[l]["z"]
            for i in range(l+1, m+1):
                v = self.K[i]["embed"](v)
            self.zsKm[l] = v
        # canonical correction digit  Chat_m = Phi_{m+1} - Phi_m^{e_m}
        self.Chat = padd(self.R, self.PhiUp,
                         pneg(self.R, ppow(self.R, self.Phis[m], self.e[m])))
        self._prodPhi = {}
        self._corr = None
        self.muw = None

    # ---- K_m helpers ----
    def kmul(self, a, b): return self.Km["mul"](a, b)
    def kisz(self, a):    return self.Km["isz"](a)
    def keq(self, a, b):
        return self.Km["isz"](self.Km["add"](a, self.Km["neg"](b)))
    def kpow(self, a, n): return self.Km["pow"](a, n)
    def emb0m(self, c):
        v = self.K[1]["embed"](c)
        for i in range(2, self.m+1):
            v = self.K[i]["embed"](v)
        return v

    # ---- eps_l per the [ILN] S0.2 convention (mode C), computed in K_m ----
    def epsKm(self, l, beta):
        lo, lp = self.bez[l-1]
        s, u = eq12(beta, self.e[l-1], self.h[l-1])
        return self.kpow(self.zsKm[l], lp*s - lo*u)

    def sm(self, beta):   # s_m(.) at the (e_{m-1}, h_{m-1}) read
        return eq12(beta, self.e[self.m-1], self.h[self.m-1])[0]

    # ---- S2.1: cells, lines ----
    def cells_of(self, f, lvl):
        f = pnorm(self.R, list(f))
        if not f: return []
        if lvl == 0:
            return [(f, ())]
        out = []
        for j, d in enumerate(dev(self.R, f, self.Phis[lvl-1])):
            if not d: continue
            for (b, a) in self.cells_of(d, lvl-1):
                out.append((b, a + (j,)))
        return out

    def line(self, b, j):
        return self.Em*w0(self.R, b) + sum(j[l]*self.Gam[l]
                                           for l in range(self.m))

    def prodPhi(self, j):
        if j in self._prodPhi: return self._prodPhi[j]
        v = [self.R["one"]]
        for l in range(self.m):
            if j[l]:
                v = pmul(self.R, v, ppow(self.R, self.Phis[l], j[l]))
        self._prodPhi[j] = v
        return v

    def cellpoly(self, b, j):
        return pmul(self.R, b, self.prodPhi(j))

    def resKm(self, b):
        d = w0(self.R, b)
        return self.emb0m(self.grbT.res_digit(b, d))

    # ---- S3.1: the lambda/t-chain and the formal read monomial zh ----
    def chain(self, j, target):
        """returns (ongrid, t[1..m], lam[0..m]) ; lam[l] = level-l slot weight."""
        m = self.m
        t = [None]*(m+1); lam = [None]*(m+1)
        lamv = target; lam[m] = lamv
        for l in range(m, 0, -1):
            e, h = self.e[l-1], self.h[l-1]
            s, u = eq12(lamv, e, h)
            if (j[l-1] - s) % e != 0:
                return False, None, None
            t[l] = (j[l-1] - s)//e
            num = lamv - j[l-1]*self.gam[l]
            if num % e != 0:
                viol("V-ZH", self.tag, f"lambda-chain non-integral at l={l} "
                     f"with t integral (note S3.1 claim broken): j={j}")
                return False, None, None
            lamv = num//e
            lam[l-1] = lamv
        return True, t, lam

    def zh(self, j, target):
        ok, t, lam = self.chain(j, target)
        if not ok: return None
        v = self.Km["one"]
        for l in range(1, self.m+1):
            v = self.kmul(v, self.kpow(self.zsKm[l], t[l]))
        for l in range(1, self.m):
            v = self.kmul(v, self.epsKm(l, lam[l]))
        return v

    # ---- reads at a target ----
    def read_at(self, f, target, ctx=""):
        f = pnorm(self.R, list(f))
        if not f: return self.Km["zero"]
        g = self.wm(f)
        if g > target: return self.Km["zero"]
        if g == target: return self.Rvm(f)
        viol("V-BOX", self.tag, f"read_at below target ({ctx}): w={g} < {target}")
        return None

    # ---- [IL3] DIGIT-SPLIT, pi-normalized (S2.1; L-LINE(iii) forces the
    #      normalization: split the unit parts, rescale by pi^{w0(b)+w0(c)}) ----
    def liftdown(self, x):
        r = self.R["res"](x)
        if self.R["kind"] == "Zp":
            return r
        return (r,) if r else ()

    def digit_split(self, b, c):
        R = self.R
        db, dc = w0(R, b), w0(R, c)
        bh = pnorm(R, [R["divpi"](x, db) for x in b])
        ch = pnorm(R, [R["divpi"](x, dc) for x in c])
        Pr = pmul(R, bh, ch)
        Y, rem = pdivmod(R, Pr, self.Phis[0])
        L = pnorm(R, [self.liftdown(x) for x in rem])
        X = padd(R, rem, pneg(R, L))          # = pi * (junk), kept as pi*X
        sc = R["pi_pow"](db + dc)
        Lc, Xc, Yc = pscal(R, sc, L), pscal(R, sc, X), pscal(R, sc, Y)
        # exactness of the split (the [IL3] display, rescaled):
        lhs = pmul(R, b, c)
        rhs = padd(R, Lc, padd(R, Xc, pmul(R, Yc, self.Phis[0])))
        if pnorm(R, padd(R, lhs, pneg(R, rhs))):
            viol("V-ID", self.tag, "DIGIT-SPLIT not exact")
        if self.d0 == 1 and Yc:
            viol("V-ID", self.tag, "Y-child alive at d0=1 (note: absent identically)")
        return Lc, Xc, Yc

    # ---- S2.2: the identity families (correction-digit tables) ----
    def corr_table(self):
        """corr[i] = list of (k, [(c_d, avec)]) for the (ID-(i+1)) identity."""
        if self._corr is not None: return self._corr
        R = self.R; m = self.m; T = self.grbT
        corr = []
        # i = 0: C_k^{(0)} = lift(psi0_k) * pi^{(g0-k)h0}, exponents 0
        row0 = []
        for k in range(self.g[0]):
            c = T.psi0[k]
            if T.K0["isz"](c): continue
            coeff = pscal(R, R["pi_pow"]((self.g[0]-k)*self.h[0]), T.liftK0(c))
            row0.append((k, [(coeff, (0,)*max(0, 0))]))
        corr.append(row0)
        # exactness: Phi0^{P0} == Phi1 - sum_k C_k Phi0^{e0 k}
        acc = self.Phis[1] if m >= 1 else None
        for (k, dc) in row0:
            acc = padd(R, acc, pneg(R, pmul(R, dc[0][0],
                        ppow(R, self.Phis[0], self.e[0]*k))))
        if pnorm(R, padd(R, acc, pneg(R, ppow(R, self.Phis[0], self.P[0])))):
            viol("V-ID", self.tag, "(ID-1) not exact")
        # i >= 1 (g_i = 1 pinned on this roster): C_0^{(i)} = Phi_{i+1}-Phi_i^{e_i}
        for i in range(1, m):
            assert self.g[i] == 1, "roster pins g_i = 1 at 1 <= i <= m-1"
            Chat_i = padd(R, self.Phis[i+1],
                          pneg(R, ppow(R, self.Phis[i], self.e[i])))
            if len(pnorm(R, Chat_i)) - 1 >= len(self.Phis[i]) - 1:
                viol("V-ID", self.tag, f"deg Chat_{i} >= deg Phi_{i}")
            dcells = self.cells_of(Chat_i, i)
            # S2.2 inventory: reduced d-cells, on-line at level i at gamma_{i+1}
            Ei = prod(self.e[:i]); Gami = [self.gam[l+1]*prod(self.e[l+1:i])
                                           for l in range(i)]
            for (cd, av) in dcells:
                if any(av[l] > self.P[l]-1 for l in range(i)):
                    viol("V-ID", self.tag, f"C^({i}) d-cell not reduced: {av}")
                li = Ei*w0(R, cd) + sum(av[l]*Gami[l] for l in range(i))
                if li != self.gam[i+1]:
                    viol("V-ID", self.tag,
                         f"C^({i}) d-cell off-line: {li} != {self.gam[i+1]}")
            dcells = [(cd, av + (0,)*(0)) for (cd, av) in dcells]
            corr.append([(0, dcells)])
        self._corr = corr
        return corr

    # ---- S4.1 L-MU: the (A_i)/(B_i) interval-family weights ----
    def mu_weights(self, verdict=True):
        """midpoint rule per the note's existence proof; interval inhabitation
        CHECKED.  Returns list of Fractions or None if some interval empty."""
        m, d0 = self.m, self.d0
        rho = [Fraction(self.P[0] - 1 + (1 if d0 >= 2 else 0))] + \
              [Fraction(self.P[l] - 1) for l in range(1, m)]
        w = [Fraction(1)]
        for i in range(1, m):
            lo = sum(w[l]*rho[l] for l in range(i)) / self.e[i]
            hi = w[i-1]*self.P[i-1]
            if not lo < hi:
                if verdict:
                    viol("V-IVL", self.tag,
                         f"(A_{i})/(B_{i}) interval EMPTY on T-scope: "
                         f"({lo}, {hi})")
                return None
            w.append((lo + hi)/2)
        # verify (A_i)/(B_i) strictly
        for i in range(1, m):
            if not w[i] < w[i-1]*self.P[i-1]:
                viol("V-IVL", self.tag, f"(A_{i}) fails for midpoint weights")
            if not w[i]*self.e[i] > sum(w[l]*rho[l] for l in range(i)):
                viol("V-IVL", self.tag, f"(B_{i}) fails for midpoint weights")
        return w

    def mu(self, w, j):
        return sum(w[l]*j[l] for l in range(self.m))

# ===================== the S2.2 tree (E1-priority), instrumented ==============
def run_tree(E, init_cells, w, strict_verdict, stats, mut_w=None):
    """init_cells: list of (sign, b, jvec).  Returns (R0, Q, leaves).
    Edge checks: L-LINE quanta (verdict always), mu-descent (verdict iff
    strict_verdict else census counters), W-WIN + window censuses."""
    R = E.R; m = E.m
    corr = E.corr_table()
    R0 = []; Q = []; leaves = []
    stack = list(init_cells)
    nodes = 0
    while stack:
        sign, b, j = stack.pop()
        nodes += 1
        if nodes > 400000:
            viol("V-CONS", E.tag, "tree node cap exceeded"); break
        for l in range(m):
            stats["maxj"][l] = max(stats["maxj"][l], j[l])
            if j[l] >= 2*E.P[l]:
                stats["overwin"] += 1
        i = next((l for l in range(m) if j[l] >= E.P[l]), None)
        if i is None:
            leaves.append((sign, b, j))
            lp = E.cellpoly(b, j)
            R0 = padd(R, R0, lp if sign > 0 else pneg(R, lp))
            continue
        pline = E.line(b, j); pmu = E.mu(w, j)
        pmu_m = E.mu(mut_w, j) if mut_w else None
        # promotion / exit
        if i <= m-2:
            j2 = list(j); j2[i] -= E.P[i]; j2[i+1] += 1; j2 = tuple(j2)
            stats["promo"] += 1
            quantum = E.h[i+1]*prod(E.e[i+2:m])
            if E.line(b, j2) - pline != quantum:
                viol("V-LINE", E.tag,
                     f"promotion quantum {E.line(b,j2)-pline} != {quantum}")
            if E.line(b, j2) - pline != quantum + 1:
                stats["mut_line"] += 1     # MU3 (claims quantum+1) trips here
            dmu = E.mu(w, j2) - pmu
            if not dmu < 0:
                if strict_verdict: viol("V-MU", E.tag, f"promotion dmu={dmu}")
                else: stats["mu_flat_up"] += 1
            if mut_w and not E.mu(mut_w, j2) - pmu_m < 0:
                stats["mut_mu"] += 1
            stack.append((sign, b, j2))
        else:
            j2 = list(j); j2[m-1] -= E.P[m-1]; j2 = tuple(j2)
            stats["exit"] += 1
            cof = E.cellpoly(b, j2)
            cline = E.line(b, j2)
            if cline - pline != -E.wmPhi:
                viol("V-LINE", E.tag, "exit line drop != w_m Phi_m")
            if stats["exit"] <= 200:
                if E.wm(cof) != cline:
                    viol("V-LINE", E.tag,
                         f"exit cofactor w_m {E.wm(cof)} != line {cline} "
                         "(single-digit structural remark)")
            Q = padd(R, Q, cof if sign > 0 else pneg(R, cof))
        # corrections (children sign = -sign)
        for (k, dcells) in corr[i]:
            base = list(j); base[i] -= E.P[i] - E.e[i]*k
            stats["corr_lvl"][i+1] = stats["corr_lvl"].get(i+1, 0) + 1
            for (cd, av) in dcells:
                Lc, Xc, Yc = E.digit_split(b, cd)
                nj = list(base)
                for l in range(min(i, len(av))):
                    nj[l] += av[l]
                njL = tuple(nj)
                wsum = w0(R, b) + w0(R, cd)
                for (cc, tag2, dj0) in ((Lc, "L", 0), (Xc, "X", 0), (Yc, "Y", 1)):
                    if not pnorm(R, cc): continue
                    jj = list(njL); jj[0] += dj0; jj = tuple(jj)
                    cline = E.line(cc, jj)
                    dline = cline - pline
                    if tag2 == "L":
                        stats["corrL"] += 1
                        if w0(R, cc) != wsum:
                            viol("V-LINE", E.tag, "L-child w0 != w0(b)+w0(c_d)")
                        if dline != 0:
                            viol("V-LINE", E.tag, f"corr-L dline {dline} != 0")
                    elif tag2 == "X":
                        stats["junkX"] += 1
                        if not dline >= E.Em:
                            viol("V-LINE", E.tag, f"pi-junk dline {dline} < Em")
                    else:
                        stats["junkY"] += 1
                        if not dline >= E.Gam[0]:
                            viol("V-LINE", E.tag, f"Y-junk dline {dline} < Gam0")
                    dmu = E.mu(w, jj) - pmu
                    if not dmu < 0:
                        if strict_verdict:
                            viol("V-MU", E.tag,
                                 f"corr dmu={dmu} lvl={i+1} child={tag2}")
                        else: stats["mu_flat_up"] += 1
                    if mut_w and not E.mu(mut_w, jj) - pmu_m < 0:
                        stats["mut_mu"] += 1
                    stack.append((-sign, cc, jj))
    stats["nodes"] += nodes
    return pnorm(R, R0), pnorm(R, Q), leaves

def rep(fam, tag, detail):
    (cens if fam.startswith("C-") else viol)(fam, tag, detail)

def new_stats(m):
    return dict(maxj=[0]*m, overwin=0, promo=0, exit=0, corrL=0, junkX=0,
                junkY=0, nodes=0, mu_flat_up=0, mut_mu=0, mut_line=0,
                corr_lvl={}, carries=0)

# ========================= the engine run (S5.2 box) ==========================
def engine_run(E, f, w, strict, stats, mut, boxfam="V-BOX", mut_w=None):
    R = E.R; m = E.m
    f = pnorm(R, list(f))
    lam = E.wm(f); v = E.Rvm(f)
    gtop = E.gam[m+1]; beta = lam + gtop
    tau = E.tau
    prodp = pmul(R, f, E.Chat)
    Qd, Rd = pdivmod(R, prodp, E.Phis[m])
    note("engine_calls")
    if E.kisz(v): note("v_zero_inputs")
    # (C-W_R)
    wR = E.wm(Rd) if Rd else INF
    if not wR >= beta:
        rep(boxfam, E.tag, f"(C-W_R) w_m(R)={wR} < {beta}")
    # (C-W_Q)
    if Qd and not E.wm(Qd) >= beta - E.wmPhi:
        rep(boxfam, E.tag, f"(C-W_Q) w_m(Q)={E.wm(Qd)} < {beta - E.wmPhi}")
    # (C-EPS)
    sl, sg, sb = E.sm(lam), E.sm(gtop), E.sm(beta)
    epsp = (sl + sg)//E.e[m-1]
    if sl + sg - sb != E.e[m-1]*epsp or epsp not in (0, 1):
        rep(boxfam, E.tag, f"(C-EPS) fails: {sl}+{sg}-{sb} vs e*{epsp}")
    # (C-READ)
    if Rd and E.wm(Rd) < beta:
        lhs = None
    else:
        lhs = E.Rvm(Rd) if (Rd and E.wm(Rd) == beta) else E.Km["zero"]
    rhs = E.kmul(E.kpow(E.zsKm[m], epsp), E.kmul(v, tau))
    if lhs is None or not E.keq(lhs, rhs):
        rep(boxfam, E.tag, f"(C-READ) fails at lam={lam}")
    # MU4: eps'+1 mutant visibility
    rhs4 = E.kmul(E.kpow(E.zsKm[m], epsp + 1), E.kmul(v, tau))
    if lhs is not None and not E.keq(lhs, rhs4):
        mut["MU4"] += 1
    # ---- tree (S2.1 initial decomposition + S2.2 reduction) ----
    xcells = E.cells_of(f, m)
    init = []
    for (bx, jx) in xcells:
        for (cD, jD) in E.Dcells:
            Lc, Xc, Yc = E.digit_split(bx, cD)
            js = tuple(jx[l] + jD[l] for l in range(m))
            for (cc, dj0) in ((Lc, 0), (Xc, 0), (Yc, 1)):
                if not pnorm(R, cc): continue
                jj = list(js); jj[0] += dj0; jj = tuple(jj)
                for l in range(m):
                    if jj[l] > 2*E.P[l] - 2 + (1 if (dj0 and l == 0) else 0):
                        viol("V-ID", E.tag, f"initial window broken: {jj}")
                init.append((+1, cc, jj))
    R0, Qt, leaves = run_tree(E, init, w, strict, stats, mut_w=mut_w)
    if R0 != pnorm(R, Rd):
        rep("V-CONS" if strict else "C-FLATCONS", E.tag, "R0 != canonical R")
    if Qt != pnorm(R, Qd):
        rep("V-CONS" if strict else "C-FLATCONS", E.tag, "Q_tree != canonical Q")
    # ---- S3 zh legs (unconditional lemmas: verdict on every terminating tree)
    # B-READ on f
    acc = E.Km["zero"]; ongrid_x = []
    for (bx, jx) in xcells:
        if E.line(bx, jx) != lam: continue
        zv = E.zh(jx, lam)
        if zv is None:
            cens("C-GRID", E.tag, f"equal-line x-cell OFF-grid at own line {jx}")
            continue
        ongrid_x.append((bx, jx))
        acc = E.Km["add"](acc, E.kmul(E.resKm(bx), zv))
    if not E.keq(acc, v):
        viol("V-ZH", E.tag, "B-READ(f) != harness read v")
    # R-read == leaf zh-sum == box prediction
    accR = E.Km["zero"]
    for (sg2, bl, jl) in leaves:
        if E.line(bl, jl) != beta: continue
        zv = E.zh(jl, beta)
        if zv is None:
            cens("C-GRID", E.tag, "equal-line R-leaf OFF-grid")
            continue
        t = E.kmul(E.resKm(bl), zv)
        accR = E.Km["add"](accR, t if sg2 > 0 else E.Km["neg"](t))
    if lhs is not None and not E.keq(accR, lhs):
        viol("V-ZH", E.tag, "leaf zh-sum != R-read at target")
    if lhs is not None and not E.keq(accR, rhs) and boxfam == "V-BOX":
        viol("V-ZH", E.tag, "leaf zh-sum != z^eps' v tau")
    # leaf sample: L-LINE(iv) exactness + single-cell read == res*zh
    for (sg2, bl, jl) in leaves[:30]:
        lp = E.cellpoly(bl, jl); li = E.line(bl, jl)
        if E.wm(lp) != li:
            viol("V-LINE", E.tag, f"leaf w_m {E.wm(lp)} != line {li}")
        zv = E.zh(jl, li)
        if zv is None or not E.keq(E.Rvm(lp), E.kmul(E.resKm(bl), zv)):
            viol("V-ZH", E.tag, "single-cell read != res*zh at own line")
    # ---- L-ZMULT on the initial (x-cell, D-cell) pairs ----
    for (bx, jx) in ongrid_x:
        c1 = E.chain(jx, lam)
        for (cD, jD) in E.Dcells:
            c2 = E.chain(jD, gtop)
            js = tuple(jx[l] + jD[l] for l in range(m))
            zs = E.zh(js, beta)
            if zs is None:
                viol("V-ZH", E.tag, "L-ZMULT: product off-grid"); continue
            zx, zD = E.zh(jx, lam), E.zh(jD, gtop)
            et = (E.sm(lam) + E.sm(gtop))//E.e[m-1]
            rhsz = E.kmul(E.kpow(E.zsKm[m], et), E.kmul(zx, zD))
            if not E.keq(zs, rhsz):
                viol("V-ZH", E.tag, f"L-ZMULT fails at {jx}+{jD}")
            note("zmult_pairs")
            # internal carries (the self-curing tooth) + MU1/MU2 visibility
            deltas = []
            for l in range(1, m):
                s1 = eq12(c1[2][l], E.e[l-1], E.h[l-1])[0]
                s2 = eq12(c2[2][l], E.e[l-1], E.h[l-1])[0]
                deltas.append((s1 + s2)//E.e[l-1])
            if any(d > 0 for d in deltas): stats["carries"] += 1
            if not E.keq(zs, E.kmul(zx, zD)):
                mut["MU1"] += 1          # dropping the top carry visibly wrong
            if any(d > 0 for d in deltas):
                mu2 = rhsz
                for l in range(1, m):
                    mu2 = E.kmul(mu2, E.kpow(E.zsKm[l], deltas[l-1]))
                if not E.keq(zs, mu2):
                    mut["MU2"] += 1      # surviving internal carries visibly wrong
    return dict(lam=lam, beta=beta, vzero=E.kisz(v))

# ===================== LAW-DCX-(m+1) census (S6.1/S6.2) =======================
def law_leg(E, mut):
    R = E.R; m = E.m
    Etot = prod(E.e[:m+1])
    u = {m: E.gam[m+1]}; su = {}
    for l in range(m, 1, -1):
        s = eq12(u[l], E.e[l-1], E.h[l-1])[0]; su[l] = s
        num = u[l] - s*E.gam[l]
        if num % E.e[l-1] != 0 or num < 0:
            viol("V-LAW", E.tag, f"u-chain not in Z>=0 at l={l}")
            return None
        u[l-1] = num//E.e[l-1]
    su[1] = eq12(u[1], E.e[0], E.h[0])[0]
    wPhi = {0: 0}
    for l in range(1, m+1):
        wPhi[l] = E.e[l-1]*E.g[l-1]*E.gam[l]
    def split(gamma):
        s = {}; b = gamma
        for l in range(m+1, 0, -1):
            slv, ulv = eq12(b, E.e[l-1], E.h[l-1])
            s[l] = slv; b = ulv - slv*wPhi[l-1]
        return s, b
    G0 = ((3*E.gam[m+1])//Etot + 1)*Etot
    while not all(split(g)[1] >= 0 for g in range(G0, G0 + Etot)):
        G0 += Etot
    anch = {}
    for gv in range(G0, G0 + Etot):
        s, u1 = split(gv)
        a = pscal(R, R["pi_pow"](u1), [R["one"]])
        for l in range(m):
            a = pmul(R, a, ppow(R, E.Phis[l], s[l+1]))
        anch[gv] = (a, s)
    res = dict(pairs=0, track=0, live=0, chainfed=0, mism=0, maxc=0,
               mu5=0, mu6=0, deficits={})
    for ga in range(G0, G0 + Etot):
        aA, sA = anch[ga]
        for gb in range(G0, G0 + Etot):
            aB, sB = anch[gb]
            res["pairs"] += 1
            strack = (sA[m+1] == E.e[m] - 1 and sB[m+1] == E.e[m] - 1)
            if strack:
                E1 = pdivmod(R, pmul(R, aA, aB), E.Phis[m])[0]
            else:
                E1 = []
            track = strack and bool(pnorm(R, E1))
            if track: res["track"] += 1
            meas = False
            if track:
                Q1 = pdivmod(R, pmul(R, E1, E.Chat), E.Phis[m])[0]
                meas = bool(pnorm(R, Q1))
            c = 0; cs = []
            for l in range(1, m):
                pool = sA[l] + sB[l] + su[l] + c
                c = pool//E.e[l-1]; cs.append(c)
                if c > 2: viol("V-LAW", E.tag, f"L-CAP broken: c_{l}={c}")
            res["maxc"] = max(res["maxc"], c)
            top = sA[m] + sB[m] + su[m] + c
            law = track and (top >= 2*E.e[m-1])
            law5 = track and (top >= 2*E.e[m-1] - 1)      # MU5 mutant
            law6 = track and (sA[m] + sB[m] + su[m] >= 2*E.e[m-1])  # MU6
            if law != meas:
                res["mism"] += 1
                cens("C-LAW", E.tag, f"LAW-DCX-{m+1} mismatch at ({ga},{gb}): "
                     f"law={law} meas={meas} top={top} c={c}")
            if law5 != meas: res["mu5"] += 1
            if law6 != meas: res["mu6"] += 1
            if meas:
                res["live"] += 1
                if c > 0: res["chainfed"] += 1
                d = top - 2*E.e[m-1]
                res["deficits"][d] = res["deficits"].get(d, 0) + 1
    mut["MU5"] += res["mu5"]; mut["MU6"] += res["mu6"]
    return res

# ================= S4.1 interval-family feasibility probe =====================
def ab_probe(d0, EG):
    """EG = [(e_l, g_l)] for l = 0..m-1.  Returns note-rule + grid feasibility
    of the FULL (A_i)/(B_i) system (strict), with witness."""
    m = len(EG)
    P = [e*g for (e, g) in EG]
    rho = [Fraction(P[0] - 1 + (1 if d0 >= 2 else 0))] + \
          [Fraction(P[l] - 1) for l in range(1, m)]
    es = [e for (e, _) in EG]
    def check(w):
        for i in range(1, m):
            if not (w[i] < w[i-1]*P[i-1] and
                    w[i]*es[i] > sum(w[l]*rho[l] for l in range(i))):
                return False
        return True
    # the note's midpoint rule
    w = [Fraction(1)]; ok = True
    for i in range(1, m):
        lo = sum(w[l]*rho[l] for l in range(i))/es[i]; hi = w[i-1]*P[i-1]
        if not lo < hi: ok = False; break
        w.append((lo + hi)/2)
    noterule = ok and check(w)
    # theta-grid search
    thetas = [Fraction(1, 2), Fraction(3, 4), Fraction(7, 8),
              Fraction(15, 16), Fraction(31, 32), Fraction(63, 64)]
    wit = None
    def rec(w):
        nonlocal wit
        if wit is not None: return
        i = len(w)
        if i == m:
            if check(w): wit = list(w)
            return
        lo = sum(w[l]*rho[l] for l in range(i))/es[i]; hi = w[i-1]*P[i-1]
        if not lo < hi: return
        for th in thetas:
            rec(w + [lo + th*(hi - lo)])
            if wit is not None: return
    rec([Fraction(1)])
    return dict(noterule=noterule, grid=wit is not None,
                witness=[str(x) for x in wit] if wit else None)

def t_scope(m, d0, es):
    return (es[0] >= 2 or d0 == 1) and all(es[i] >= 2 for i in range(1, m))

# ============================ batteries & roster ==============================
def battery(E):
    m = E.m; R = E.R
    ins = []
    P = E.P
    zero = (0,)*m
    maxv = tuple(P[l]-1 for l in range(m))
    vecs = [zero, maxv]
    for l in range(m):
        uvec = [0]*m; uvec[l] = min(1, P[l]-1); vecs.append(tuple(uvec))
    vecs.append(tuple(1 if P[l] > 1 else 0 for l in range(m)))
    vecs.append(tuple((P[l]-1) if l % 2 == 0 else 0 for l in range(m)))
    seen = set(); anchors = []
    for a in vecs:
        if a not in seen:
            seen.add(a); anchors.append(a)
    cap = 8 if m >= 4 else 12
    k = 0
    for a in anchors:
        for uu in (0, 1):
            if k >= cap: break
            ins.append(("anch", pscal(R, R["pi_pow"](uu), E.prodPhi(a))))
            k += 1
    if E.d0 >= 2:
        b = pnorm(R, [R["one"], R["one"]])
        ins.append(("bvar", pmul(R, b, E.prodPhi(maxv))))
    if E.g[0] == 1 and E.d0 == 1:
        c0 = E.grbT.K0["neg"](E.grbT.psi0[0])       # psi0 = z - c0
        f = padd(R, ppow(R, E.Phis[0], E.e[0]),
                 pneg(R, pscal(R, R["pi_pow"](E.h[0]), E.grbT.liftK0(c0))))
        ins.append(("v0pair", f))
    ins.append(("twocell", padd(R, ppow(R, E.Phis[0], E.e[0]),
                                [R["pi_pow"](E.h[0])])))
    ins.append(("mixline", padd(R, E.prodPhi(maxv),
                                pscal(R, R["pi_pow"](2), E.prodPhi(zero)))))
    noise = pnorm(R, [R["one"], R["pi_pow"](1), R["zero"], R["one"]])
    ins.append(("noise", padd(R, E.prodPhi(maxv),
                              pscal(R, R["pi_pow"](3), noise))))
    # the box demands deg f < deg Phi_m: drop out-of-spec inputs (bites only
    # at the tiny flat tower M2C where deg Phi_2 = 2)
    return [(nm, f) for (nm, f) in ins
            if f and len(pnorm(R, f)) - 1 < E.degPhim]

def embK(E, v, frm):
    for i in range(frm+1, E.m+1):
        v = E.K[i]["embed"](v)
    return v

def prep(E):
    R = E.R; m = E.m; gtop = E.gam[m+1]
    # V-P0: my eps convention == the sealed harness eps at every shared level
    for l in range(1, m):
        hf = E.harness_eps[l]
        if hf is None: continue
        for beta in (0, 1, E.gam[l], gtop, 7):
            a = embK(E, hf(beta), l)
            if not E.keq(a, E.epsKm(l, beta)):
                viol("V-P0", E.tag, f"eps_{l}({beta}) mismatch vs harness")
    # Chat certificates (S2.1 consumed structure)
    if E.wm(E.Chat) != gtop:
        viol("V-ID", E.tag, f"w_m(Chat) = {E.wm(E.Chat)} != gamma_(m+1) = {gtop}")
    E.tau = E.Rvm(E.Chat)
    if E.kisz(E.tau):
        viol("V-ID", E.tag, "tau_m == 0")
    E.Dcells = E.cells_of(E.Chat, m)
    acc = E.Km["zero"]
    for (cD, jD) in E.Dcells:
        if E.line(cD, jD) != gtop:
            viol("V-ID", E.tag, f"Chat cell off-line: {jD}")
        if any(jD[l] > E.P[l]-1 for l in range(m)):
            viol("V-ID", E.tag, f"Chat cell not reduced: {jD}")
        zv = E.zh(jD, gtop)
        if zv is None:
            viol("V-ID", E.tag, f"Chat cell off-grid: {jD}"); continue
        rv = E.resKm(cD)
        if E.kisz(rv):
            viol("V-ID", E.tag, "Chat cell residue == 0")
        acc = E.Km["add"](acc, E.kmul(rv, zv))
    if not E.keq(acc, E.tau):
        viol("V-ZH", E.tag, "B-READ(Chat) != tau  ((Chat3) certificate)")
    E.corr_table()

ROSTER = [
    ("M2A", 2, "Zp",  5, 1, [(2,1,1), (2,1,1), (2,1,1)]),
    ("M2B", 2, "Zp",  3, 2, [(3,1,2), (2,1,1), (2,3,1)]),
    ("M2F", 2, "Fpt", 2, 1, [(2,1,1), (2,1,1), (2,1,1)]),
    ("M3A", 3, "Zp",  5, 1, [(2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
    ("M3B", 3, "Zp",  3, 2, [(2,1,2), (3,2,1), (2,1,1), (2,1,1)]),
    ("M4A", 4, "Zp",  3, 1, [(2,1,1), (2,1,1), (2,1,1), (2,1,1), (2,1,1)]),
]
FLAT = [
    ("M2C", 2, "Zp", 3, 1, [(2,1,1), (1,1,1), (2,1,1)]),
    ("M3C", 3, "Zp", 3, 1, [(2,1,1), (2,1,1), (1,1,1), (2,1,1)]),
]
SHAPES = [
    ("T2-all2-d1",      1, [(2,1),(2,1)]),
    ("T2-M2Bshape-d2",  2, [(6,1),(2,1)]),
    ("T3-all2-d1",      1, [(2,1),(2,1),(2,1)]),
    ("T3-M3Bshape-d2",  2, [(4,1),(3,1),(2,1)]),
    ("T4-all2-d1",      1, [(2,1),(2,1),(2,1),(2,1)]),
    ("F2-e1flat-d1",    1, [(2,1),(1,1)]),
    ("F2-e1flat-d2",    2, [(2,1),(1,1)]),
    ("F3-e2flat-d1",    1, [(2,1),(2,1),(1,1)]),
    ("F3-e2flat-d2",    2, [(2,1),(2,1),(1,1)]),
    ("F3-e1flat-mid-d1",1, [(2,1),(1,1),(2,1)]),
    ("F3-doubleflat-d1",1, [(2,1),(1,1),(1,1)]),
    ("F3-e1flat-g2-d1", 1, [(2,1),(1,2),(2,1)]),
    ("F4-e3flat-d1",    1, [(2,1),(2,1),(2,1),(1,1)]),
]

def main():
    t0 = time.time()
    mut = dict(MU1=0, MU2=0, MU3=0, MU4=0, MU5=0, MU6=0, MU7=0)
    summary = {}
    for (tag, m, kind, p, d0, reads) in ROSTER:
        es = [r[0] for r in reads]
        if not t_scope(m, d0, es[:m]):
            viol("V-SCOPE", tag, "roster shape off T-scope")
        print(f"== {tag}: m={m} {kind} p={p} d0={d0} reads={reads}")
        E = Eng(m, kind, p, d0, reads, tag)
        prep(E)
        w = E.mu_weights()
        rho = [Fraction(E.P[0]-1 + (1 if d0 >= 2 else 0))] + \
              [Fraction(E.P[l]-1) for l in range(1, m)]
        lo_top = sum(w[l]*rho[l] for l in range(m-1))/E.e[m-1] if m >= 2 else 0
        mut_w = list(w)
        if m >= 2: mut_w[m-1] = lo_top/2          # violates (B_{m-1}) -> MU7
        stats = new_stats(m)
        nin = 0
        for (nm, f) in battery(E):
            engine_run(E, f, w, True, stats, mut, mut_w=mut_w)
            nin += 1
        mut["MU7"] += stats["mut_mu"]; mut["MU3"] += stats["mut_line"]
        law = law_leg(E, mut)
        print(f"   inputs={nin} nodes={stats['nodes']} promo={stats['promo']} "
              f"exit={stats['exit']} corrL={stats['corrL']} junk={stats['junkX']}"
              f"/{stats['junkY']} carries={stats['carries']} maxj={stats['maxj']}"
              f" overwin={stats['overwin']}")
        print(f"   weights={[str(x) for x in w]}")
        print(f"   LAW-DCX-{m+1}: pairs={law['pairs']} track={law['track']} "
              f"live={law['live']} chainfed={law['chainfed']} "
              f"mism={law['mism']} maxc={law['maxc']} deficits={law['deficits']}")
        summary[tag] = dict(m=m, kind=kind, p=p, d0=d0, reads=reads,
                            n_inputs=nin, stats={k: v for k, v in stats.items()},
                            weights=[str(x) for x in w], law=law)
    # ---- flat fence legs ----
    for (tag, m, kind, p, d0, reads) in FLAT:
        es = [r[0] for r in reads]
        fired = not t_scope(m, d0, es[:m])
        if not fired:
            viol("V-SCOPE", tag, "flat shape PASSED the T-scope predicate")
        print(f"== {tag} (FLAT, off T-scope; fence fired={fired}): m={m} "
              f"p={p} d0={d0} reads={reads}")
        probe = ab_probe(d0, [(reads[l][0], reads[l][2]) for l in range(m)])
        print(f"   (A_i)/(B_i) probe: note-rule={probe['noterule']} "
              f"grid-feasible={probe['grid']} witness={probe['witness']}")
        E = Eng(m, kind, p, d0, reads, tag)
        prep(E)
        stats = new_stats(m)
        if probe["grid"]:
            w = [Fraction(x) for x in probe["witness"]]
            for (nm, f) in battery(E)[:8]:
                engine_run(E, f, w, False, stats, mut, boxfam="C-FLATBOX")
            print(f"   EXPLORATORY tree (witness weights): nodes={stats['nodes']}"
                  f" mu_non_descending={stats['mu_flat_up']} "
                  f"corr_lvl={stats['corr_lvl']} promo={stats['promo']} "
                  f"exit={stats['exit']}")
        law = law_leg(E, mut)
        print(f"   LAW-DCX-{m+1} (flat-shape census): pairs={law['pairs']} "
              f"live={law['live']} chainfed={law['chainfed']} mism={law['mism']}")
        summary[tag] = dict(m=m, kind=kind, p=p, d0=d0, reads=reads,
                            fence_fired=fired, probe=probe,
                            stats={k: v for k, v in stats.items()}, law=law)
    # ---- shape-level (A_i)/(B_i) feasibility table ----
    print("== (A_i)/(B_i) feasibility table (shape-level, strict system):")
    shapes_out = {}
    for (nm, d0, EG) in SHAPES:
        r = ab_probe(d0, EG)
        shapes_out[nm] = r
        print(f"   {nm:20s} note-rule={str(r['noterule']):5s} "
              f"grid={str(r['grid']):5s} witness={r['witness']}")
    # ---- verdicts ----
    fams = {}
    for (f, t, d) in VIOL: fams[f] = fams.get(f, 0) + 1
    def vline(name, keys, label):
        n = sum(fams.get(k, 0) for k in keys)
        print(f"{name} ({label}, predicted-0): "
              f"{'GREEN [0 violations]' if n == 0 else f'RED [{n} violations]'}")
        return n
    print()
    vline("R0 VERDICT", ["V-P0", "V-SCOPE"], "harness-eps tie + scope predicate")
    vline("R1 VERDICT", ["V-BOX"], "four box clauses m=2/3/4 incl. FIRST "
          "level-4 engine data")
    vline("R2 VERDICT", ["V-CONS", "V-MU", "V-IVL", "V-ID"],
          "tree==division + strict mu (T-scope) + intervals + identities")
    vline("R3 VERDICT", ["V-LINE"], "line calculus exact quanta")
    vline("R4 VERDICT", ["V-ZH"], "zh kernel: B-READ / L-ZMULT / read triple")
    vline("R6 VERDICT", ["V-LAW"], "LAW structure: u-chain in Z>=0 + L-CAP<=2")
    lawmism = sum(summary[t]["law"]["mism"] for t in summary
                  if summary[t].get("law"))
    lawpairs = sum(summary[t]["law"]["pairs"] for t in summary
                   if summary[t].get("law"))
    print(f"R5 CENSUS (LAW-DCX-(m+1) m=2/3/4 vs measured, census-grade): "
          f"mismatches={lawmism} over {lawpairs} pairs")
    print(f"counters: engine_calls={CNT.get('engine_calls', 0)} "
          f"zmult_pairs={CNT.get('zmult_pairs', 0)} "
          f"v_zero_inputs={CNT.get('v_zero_inputs', 0)}")
    if CNT.get("v_zero_inputs", 0) < 1:
        print("observation [v=0]: no legal input realized v = 0 "
              f"(0/{CNT.get('engine_calls', 0)}); deg f < deg Phi_m caps the "
              "read at <= g_(l-1) slots per level, so the read value is a "
              "z_l-polynomial of sub-minimal degree with nonzero coefficients "
              "at every level -> v != 0 on the whole legal class; the note's "
              "scope remark (ii) v = 0 case appears UNREALIZABLE (vacuous-safe)")
    mutvis = all(mut[k] > 0 for k in mut)
    print(f"R7 VERDICT (mutants MU1-MU7 all visible, predicted-visible): "
          f"{'GREEN ' + str(mut) if mutvis else 'RED ' + str(mut)}")
    if not mutvis:
        viol("V-MUT", "global", f"invisible mutant: {mut}")
    ok = len(VIOL) == 0
    print(f"\nTOTAL: {'ALL GREEN' if ok else str(len(VIOL)) + ' VIOLATIONS'}; "
          f"census notes: {len(CENS)}; elapsed {time.time()-t0:.1f}s")
    out = dict(viol=VIOL, census=CENS, counters=CNT, mutants=mut,
               towers=summary, shapes=shapes_out,
               elapsed=time.time() - t0)
    def md5(fn):
        with open(os.path.join(HERE, fn), "rb") as fh:
            return hashlib.md5(fh.read()).hexdigest()
    out["provenance"] = {fn: md5(fn) for fn in
        ("rmengine_pe_reimpl.py", "grb_order2_check.py", "strata3_probe.py",
         "iterlaw4_probe.py", "iterlawn_diag.py")}
    out["provenance"]["note"] = hashlib.md5(open(os.path.join(
        HERE, "../../lean/notes/openmath/RMENGINE_2026-08-08.md"), "rb")
        .read()).hexdigest() if os.path.exists(os.path.join(
        HERE, "../../lean/notes/openmath/RMENGINE_2026-08-08.md")) else "n/a"
    with open(os.path.join(HERE, "rmengine_pe_reimpl_results.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
