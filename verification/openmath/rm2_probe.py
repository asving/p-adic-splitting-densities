#!/usr/bin/env python3
"""rm2_probe.py — (RM-2) ENGINE PROBE (wave-21 Q1 opening move; probe-first).
Sealed preregistration = lean/notes/openmath/RM2_PROBE_2026-08-08.md.
Two-commit seal: this file + the prereg are committed BEFORE the battery runs.

THE STATEMENT UNDER TEST — the ITERLAWN S4.6 box (RM-m) instantiated at
m = 2 (the FIRST UNPROVED LEVEL; m = 1 is PROVED inside [IL3]†):

  Setting: level 2 of a class tower with g2 = 1; Chat2 the canonical
  correction digit of WELL-DEF-(n)(ii): Phi3 = Phi2^{e2} + Chat2, with
  deg Chat2 < deg Phi2, w2(Chat2) = gamma3, R_{2,gamma3}(Chat2) = tau2
  = eps2(gamma3)^{-1} c2  (psi2 = y + c2, z3 = -c2).
  Input: f in O[x], f != 0, deg f < deg Phi2, lam := w2(f),
  v := R_{2,lam}(f) (the level-2 read value at z2).  Claim: there exist
  R, Q in O[x], deg R < deg Phi2, deg Q < deg Phi2, with

    f*Chat2 = R + Q*Phi2,          w2(R) >= lam + gamma3,
    w2(Q)  >= lam + gamma3 - w2Phi2   (Q = 0 allowed),
    R_{2,lam+gamma3}(R) = z2^{eps'} * v * tau2,
    eps' := floor((s2(lam) + s2(gamma3))/e1)   [the level-2 EPS-carry].

  Since deg f, deg Chat2 < deg Phi2, any decomposition with deg R < deg Phi2
  forces (R, Q) = divmod(f*Chat2, Phi2): the existence claim is EQUIVALENT
  to the canonical division satisfying the displayed clauses.

FIRING PREDICATE (rung-3 consumption; ITERLAWN S4.3/S4.6 case partition):
  CII3(ga,gb) := g2 = 1 AND [ T3 >= e2  (Cases II-1/II-2, delta3^pl = 1)
                              OR (E1IH != 0 AND T3 = e2 - 1)  (Case II-3) ]
  where T3 := s3 + s3' from the iterated splits, and the rung-2 IH exports
  are E1IH := quo(ahat*ahat', Phi2), E0IH := rem(ahat*ahat', Phi2) with
  ahat := pi^{u1} Phi0^{s1} Phi1^{s2} (the sub-Phi2 anchor part) — the
  S4.6 II-2 display "A = E1IH*Phi^{T3+1} + E0IH*Phi^{T3}" read backwards.

LEGS: L1 weight clauses; L2 read clause (provenance-split: E0-consumed /
E1-extra / breadth); L2-EPS carry identity; L3 termination of the probe's
CANDIDATE level-2 reduction tree (E1-priority; the linear measure
mu := e0g0*(e1+1)*j1 + 2*e1*j0, strict descent predicted EXACTLY on the
main scope e0 >= 2 AND e1 >= 2 — the m = 2 analogue of DEV-1's e0 >= 2
erratum scope); CONS tree == division; L4 DCX_3 second-round-overflow
locus vs (a) the S4.7 outer bound and (b) the [IL3] DCX_2 sharp predicate
TRANSPORTED one level up (the S4.7 conjectured family at m = 3):
  DCX3pred := { g1 = g2 = 1, delta2^pl = 1, s3 = s3' = e2 - 1,
                (s2 + s2') + s2(gamma3) >= 2*e1 }.
A violation of any sealed leg is a probe SUCCESS (reported prominently).
Mutation controls MC-A..MC-E; control failures reported SEPARATELY.
DETERMINISTIC: full window blocks, exact arithmetic, no sampling, no seed.
Usage: rm2_probe.py [--design]   (--design: tower certs + firing/roster
censuses ONLY — no engine call, no tree, no Q1, no law comparison;
disclosed pre-seal per the iterlawr/iterlaw4 precedent).
"""
import sys, os, math, time, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, bezout, INF, pdivmod, mk_field_ext)
import strata3_probe as S3MOD
import iterlawr_probe as ILP      # installs the pick_irr3 shim (disclosed)
import iterlaw4_probe as IL4
from iterlaw4_probe import Tower4, Composite4

VIOL = []
CNT = {}
def note(fam, n=1): CNT[fam] = CNT.get(fam, 0) + n
def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)[:240]))
    if sum(1 for v in VIOL if v[0] == fam) <= 8:
        print(f"  VIOLATION [{fam}] {tag}: {str(detail)[:200]}")

# roster: (tag, d0, r0, r1, r2, r3, rationale); ALL rows g2 = 1 (the RM-2
# setting); r_j = (e_j, h_j, g_j)
ROSTER = [
    ("RM2A", 1, (2,1,1), (2,1,1), (2,1,1), (1,1,2),
     "main-scope stack e0=e1=e2=2, g0=g1=g2=1 (deep Case II at all levels)"),
    ("RM2B", 1, (3,2,1), (3,1,1), (2,5,1), (1,1,1),
     "DCX3-live candidate: e1=3, g1=g2=1, h2=5 so s2(gamma3)=l1*h2 mod e1 = 2 "
     "(transported emptiness needs e1>=3 AND s2(gamma3)>=2); e0=3,h0=2"),
    ("RM2C", 2, (2,1,2), (2,1,1), (2,1,1), (1,1,1),
     "junk-alive d0=2 + g0=2 multi-term level-1 identity"),
    ("RM2D", 1, (2,1,1), (2,1,2), (2,1,1), (1,1,1),
     "g1=2 multi-C_k level-2 identity; locus control (DCX3pred forces g1=1)"),
    ("RM2E", 1, (2,1,1), (1,1,2), (2,1,1), (1,1,1),
     "BEND shape: e1=1 (no valid linear mu; promotion edge flat) — census only"),
    ("RM2F", 2, (1,1,2), (2,1,1), (2,1,1), (1,1,1),
     "BEND shape: e0=1 & d0=2 (the DEV-1 fenced corner; junkPhi self-edge) — census only"),
    ("RM2G", 1, (2,1,1), (3,1,1), (1,2,1), (2,1,1),
     "e2=1 II-3-heavy (every E1IH!=0 row fires); DCX3 candidate via the e2=1 "
     "branch; e1=3, h2=2 so s2(gamma3)=2"),
]
RINGS = {t[0]: [("Zp", 3)] for t in ROSTER}
RINGS["RM2A"].append(("Fpt", 2))
RINGS["RM2B"].append(("Fpt", 2))
MAIN_SCOPE = ("RM2A", "RM2B", "RM2C", "RM2D", "RM2G")   # e0 >= 2 and e1 >= 2
CAP_POPS = 3000    # legit main-scope trees need well under 10^3 pops

def poly_key(R, f):
    return tuple(f) if R["kind"] == "Zp" else tuple(tuple(c) for c in f)

def digit_split(T, prod):
    """DIGIT-SPLIT ([IL3] S4.1): prod = L + pi*X + Phi0*Y, deg L,X,Y < d0."""
    R = T.R
    Y, rho = pdivmod(R, prod, T.Phi0)
    L, X = [], []
    for c in rho:
        if R["kind"] == "Zp":
            r = c % T.p
            L.append(r); X.append((c - r)//T.p)
        else:
            r0 = (c[0] % T.p) if c else 0
            rl = (r0,) if r0 else ()
            L.append(rl)
            X.append(R["divpi"](R["add"](c, R["neg"](rl)), 1))
    return pnorm(R, L), pnorm(R, X), pnorm(R, Y)

def monomials(T, f):
    """f (deg < degPhi2) -> [(b, j0, j1)]: b*Phi0^j0*Phi1^j1, deg b < d0."""
    out = []
    for j1, A in enumerate(dev(T.R, f, T.Phi1)):
        if not A: continue
        for j0, b in enumerate(dev(T.R, A, T.Phi0)):
            if b: out.append((b, j0, j1))
    return out

class Engine2:
    """the (RM-2) data of one g2 = 1 Tower4."""
    def __init__(self, T4):
        T3 = T4.T3; T = T3.T; R = T.R
        assert T3.g2 == 1, "RM-2 setting needs g2 = 1"
        self.T4, self.T3, self.T, self.R = T4, T3, T, R
        self.K2 = T3.K2
        self.Chat2 = pnorm(R, padd(R, T3.Phi3,
                                   pneg(R, ppow(R, T.Phi2, T3.e2))))
        self.c2 = T3.psi2[0]
        self.eps2g3 = T3.eps2(T3.gamma3)
        self.tau2 = self.K2["mul"](self.K2["inv"](self.eps2g3), self.c2)
        # level-2 identity: Phi2 = Phi1^{e1g1} + sum_{k<g1} C_k Phi1^{e1 k}
        self.Ck = {}
        for k, c in enumerate(T.psi1):
            if k >= T.g1 or T.K1["isz"](c): continue
            gp = (T.g1 - k)*T.gamma2
            tau = T.K1["mul"](T.K1["inv"](T.eps1(gp)), c)
            self.Ck[k] = T.realize1(tau, gp)
        self.Ck_digits = {k: [(i0, b) for i0, b in enumerate(dev(R, Cp, T.Phi0)) if b]
                          for k, Cp in self.Ck.items()}
        # level-1 identity: Phi0^{e0g0} = Phi1 - sum_{i<g0} lift(psi0_i) pi^{(g0-i)h0} Phi0^{e0 i}
        self.lvl1 = []
        for i, c in enumerate(T.psi0):
            if i >= T.g0 or T.K0["isz"](c): continue
            self.lvl1.append((i, pscal(R, R["pi_pow"]((T.g0 - i)*T.h0),
                                       T.liftK0(c))))

    def vis_certs(self):
        """tower-data certs (design-safe; no law leg evaluated)."""
        T3, T, R = self.T3, self.T, self.R
        out = {}
        out["g2_is_1"] = (T3.g2 == 1)
        out["psi2_monic_deg1"] = (len(T3.psi2) == 2
                                  and T3.psi2[1] == self.K2["one"])
        out["Chat2_C1_deg"] = (len(self.Chat2) - 1 < T.degPhi2)
        out["Chat2_C2_w2"] = (T.w2(self.Chat2) == T3.gamma3)
        out["Chat2_C3_read"] = (out["Chat2_C2_w2"]
                                and self.T3.R2v(self.Chat2) == self.tau2)
        ident = ppow(R, T.Phi1, T.e1*T.g1)
        for k, Cp in self.Ck.items():
            ident = padd(R, ident, pmul(R, Cp, ppow(R, T.Phi1, T.e1*k)))
        out["lvl2_identity"] = (pnorm(R, ident) == pnorm(R, T.Phi2))
        ident1 = ppow(R, T.Phi0, T.e0*T.g0)
        for i, cf in self.lvl1:
            ident1 = padd(R, ident1, pmul(R, cf, ppow(R, T.Phi0, T.e0*i)))
        out["lvl1_identity"] = (pnorm(R, ident1) == pnorm(R, T.Phi1))
        out["z2_ne_1"] = (T3.z2 != self.K2["one"])
        sq = self.K2["mul"](self.eps2g3, self.eps2g3)
        out["eps2g3_sq_ne_1"] = (sq != self.K2["one"])
        return out

    def s2(self, beta): return eq12(beta, self.T.e1, self.T.h1)[0]

    def R2v_at(self, f, beta):
        """level-2 read value of f at target weight beta (0 strictly above)."""
        if not pnorm(self.R, f): return self.K2["zero"]
        lam = self.T.w2(f)
        if lam > beta: return self.K2["zero"]
        assert lam == beta, "R2v_at: input below the target line"
        return self.T3.R2v(f)

    def call(self, f):
        """one engine call on f (deg < degPhi2, f != 0): division + leg data."""
        T3, T, R, K2 = self.T3, self.T, self.R, self.K2
        lam = T.w2(f)
        v = T3.R2v(f)
        Q, Rr = pdivmod(R, pmul(R, f, self.Chat2), T.Phi2)
        wR = T.w2(Rr) if pnorm(R, Rr) else INF
        wQ = T.w2(Q) if pnorm(R, Q) else INF
        target = lam + T3.gamma3
        s2l, s2g = self.s2(lam), self.s2(T3.gamma3)
        epsp = (s2l + s2g)//T.e1
        eps_id = (s2l + s2g - self.s2(target) == T.e1*epsp)
        pred = K2["mul"](K2["pow"](T3.z2, epsp), K2["mul"](v, self.tau2))
        okW_R = (wR >= target)
        okW_Q = (not pnorm(R, Q)) or (wQ >= target - T.w2Phi2)
        got = self.R2v_at(Rr, target) if okW_R else None
        okRead = (got == pred) if okW_R else False
        # mutation-control raw material (checked by the harness, reported
        # separately): MC-A read*z2 (eps'+1), MC-B weight+1, MC-C the
        # z3-SIGN mutation tau2 -> eps2(gamma3)^{-1}*(-c2) (the canonical
        # z_n = -c_{n-1} cancellation sign; visible at every p = 3 tower)
        predA = K2["mul"](K2["pow"](T3.z2, epsp + 1), K2["mul"](v, self.tau2))
        tauC = K2["neg"](self.tau2)
        predC = K2["mul"](K2["pow"](T3.z2, epsp), K2["mul"](v, tauC))
        return dict(lam=lam, v=v, R=Rr, Q=Q, wR=wR, wQ=wQ, target=target,
                    epsp=epsp, eps_id=eps_id, pred=pred, got=got,
                    okW_R=okW_R, okW_Q=okW_Q, okRead=okRead,
                    v_zero=K2["isz"](v), Qnz=bool(pnorm(R, Q)),
                    mcA_trips=(okW_R and got is not None and got != predA),
                    mcB_trips=(wR == target),
                    mcC_trips=(okW_R and got is not None and got != predC))

class Tree:
    """the probe's CANDIDATE level-2 reduction tree (E1-priority):
    nodes b*Phi0^{j0}*Phi1^{j1} (deg b < d0) aggregated per (j0,j1) cell;
    E1 (j0 >= e0g0): level-1 standard-lift identity — promotion child
    (j0-e0g0, j1+1) + DIGIT-SPLIT children of b*lift(psi0_i);
    E2 (j0 < e0g0, j1 >= e1g1): level-2 canonical identity — Phi2-exit
    (joins Q) + DIGIT-SPLIT children of b*(C_k Phi0-digits).
    mu := e0g0*(e1+1)*j1 + 2*e1*j0; strict mu-descent on every in-tree
    edge is THE L3 prediction on the main scope (e0 >= 2 and e1 >= 2)."""
    def __init__(self, E, f):
        self.E = E; T = E.T; R = E.R
        self.e0g0, self.e1g1 = T.e0*T.g0, T.e1*T.g1
        self.mu1 = self.e0g0*(T.e1 + 1); self.mu0 = 2*T.e1
        self.cells = {}
        self.Q = []; self.pops = 0; self.status = "OK"
        self.bad_edges = 0; self.bad_samples = []
        self.win_viol = 0
        self.n_e1child = 0; self.n_e1promo = 0; self.n_e2child = 0
        self.n_exit = 0
        mf = monomials(T, f); mc = monomials(T, E.Chat2)
        for (b, i0, i1) in mf:
            for (c, k0, k1) in mc:
                L, X, Y = digit_split(T, pmul(R, b, c))
                self.add(L, i0 + k0, i1 + k1)
                self.add(pscal(R, R["pi_pow"](1), X), i0 + k0, i1 + k1)
                self.add(Y, i0 + k0 + 1, i1 + k1)
    def mu(self, j0, j1): return self.mu1*j1 + self.mu0*j0
    def add(self, b, j0, j1):
        b = pnorm(self.E.R, b)
        if not b: return
        if j0 >= 2*self.e0g0 or j1 >= 2*self.e1g1:
            self.win_viol += 1
        key = (j0, j1)
        cur = padd(self.E.R, self.cells.get(key, []), b)
        if cur: self.cells[key] = cur
        elif key in self.cells: del self.cells[key]
    def edge(self, pj, cj, kind):
        if kind == "E1promo": self.n_e1promo += 1
        elif kind == "E1child": self.n_e1child += 1
        else: self.n_e2child += 1
        if self.mu(*cj) >= self.mu(*pj):
            self.bad_edges += 1
            if len(self.bad_samples) < 6:
                self.bad_samples.append((pj, cj, kind))
    def run(self):
        E = self.E; T = E.T; R = E.R
        while True:
            red = [c for c in self.cells
                   if c[0] >= self.e0g0 or c[1] >= self.e1g1]
            if not red: break
            self.pops += 1
            if self.pops > CAP_POPS:
                self.status = "CAP"; return self
            j0, j1 = max(red, key=lambda c: self.mu(*c))
            b = self.cells.pop((j0, j1))
            if j0 >= self.e0g0:                       # E1
                self.edge((j0, j1), (j0 - self.e0g0, j1 + 1), "E1promo")
                self.add(b, j0 - self.e0g0, j1 + 1)
                for i, cf in E.lvl1:
                    L, X, Y = digit_split(T, pmul(R, b, cf))
                    nj0 = j0 - self.e0g0 + T.e0*i
                    for poly, dj in ((L, 0),
                                     (pscal(R, R["pi_pow"](1), X), 0),
                                     (Y, 1)):
                        if pnorm(R, poly):
                            self.edge((j0, j1), (nj0 + dj, j1), "E1child")
                            self.add(pneg(R, poly), nj0 + dj, j1)
            else:                                     # E2
                self.n_exit += 1
                self.Q = padd(R, self.Q,
                              pmul(R, pmul(R, b, ppow(R, T.Phi0, j0)),
                                   ppow(R, T.Phi1, j1 - self.e1g1)))
                for k, digs in E.Ck_digits.items():
                    nj1 = j1 - self.e1g1 + T.e1*k
                    for i0c, dc in digs:
                        L, X, Y = digit_split(T, pmul(R, b, dc))
                        for poly, dj in ((L, 0),
                                         (pscal(R, R["pi_pow"](1), X), 0),
                                         (Y, 1)):
                            if pnorm(R, poly):
                                self.edge((j0, j1), (j0 + i0c + dj, nj1),
                                          "E2child")
                                self.add(pneg(R, poly), j0 + i0c + dj, nj1)
        Rp = []
        for (j0, j1), b in self.cells.items():
            Rp = padd(R, Rp, pmul(R, pmul(R, b, ppow(R, T.Phi0, j0)),
                                  ppow(R, T.Phi1, j1)))
        self.Rpoly = pnorm(R, Rp)
        self.Q = pnorm(R, self.Q)
        return self

def anchor2(C, cache, gamma):
    """sub-Phi2 anchor part ahat = pi^{u1} Phi0^{s1} Phi1^{s2}."""
    T = C.T4.T3.T; R = T.R
    s4, s3, s2, s1, b3, b2, b1, u1 = C.split(gamma)
    key = (u1, s1, s2)
    if key not in cache:
        f = pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1))
        cache[key] = pmul(R, f, ppow(R, T.Phi1, s2))
    return cache[key], (s3, s2)

def breadth_inputs(T):
    """the BOX-QUANTIFIER class: monomials pi^u b Phi0^i Phi1^j (+3 sums)."""
    R = T.R; out = []
    bs = [[R["one"]]]
    if T.d0 >= 2: bs.append([R["zero"], R["one"]])
    e0g0, e1g1 = T.e0*T.g0, T.e1*T.g1
    for u in (0, 1):
        for b in bs:
            for i in range(e0g0):
                for j in range(e1g1):
                    f = pscal(R, R["pi_pow"](u),
                              pmul(R, b, pmul(R, ppow(R, T.Phi0, i),
                                              ppow(R, T.Phi1, j))))
                    out.append((f, "BR-mono"))
    pats = [(0, 0, 1, min(1, e0g0 - 1), 0),
            (e0g0 - 1, e1g1 - 1, 0, 0, 0),
            (0, e1g1 - 1, 2, e0g0 - 1, 0)]
    for (i, j, u, i2, j2) in pats:
        f = padd(R, pmul(R, ppow(R, T.Phi0, i), ppow(R, T.Phi1, j)),
                 pscal(R, R["pi_pow"](u),
                       pmul(R, ppow(R, T.Phi0, i2), ppow(R, T.Phi1, j2))))
        out.append((pnorm(R, f), "BR-sum"))
    return out

MC = dict(A=0, B=0, C=0, D=0, E=0)   # trip counters (controls, separate)

def run_engine_input(E, f, prov, name, main_scope, res):
    T = E.T; R = E.R
    if not pnorm(R, f):
        note("input_zero"); return
    c = E.call(f)
    note(f"L1_{prov}")
    if not (c["okW_R"] and c["okW_Q"]):
        viol("L1-WEIGHT", name,
             f"{prov} lam={c['lam']} wR={c['wR']} wQ={c['wQ']} tgt={c['target']}")
    note(f"L2_{prov}")
    if c["okW_R"] and not c["okRead"]:
        viol("L2-READ", name,
             f"{prov} lam={c['lam']} wR={c['wR']} tgt={c['target']} "
             f"epsp={c['epsp']} vzero={c['v_zero']} got={c['got']} "
             f"pred={c['pred']}")
    if not c["eps_id"]:
        viol("L2-EPS", name, f"{prov} lam={c['lam']}")
    if c["v_zero"]: note("v_zero_rows")
    if c["mcA_trips"]: MC["A"] += 1
    if c["mcB_trips"]: MC["B"] += 1
    if c["mcC_trips"]: MC["C"] += 1
    # L3/CONS: the candidate tree
    t = Tree(E, f).run()
    res["tree_pops"] = res.get("tree_pops", 0) + t.pops
    if t.status == "CAP":
        note("tree_cap")
        if main_scope:
            viol("L3-CAP", name, f"{prov} pops>{CAP_POPS}")
        else:
            res["bend_caps"] = res.get("bend_caps", 0) + 1
        return
    if t.n_e1child > 0 and main_scope: MC["E"] += 1
    if t.bad_edges:
        if main_scope:
            viol("L3-TERM", name, f"{prov} bad_edges={t.bad_edges} "
                 f"samples={t.bad_samples}")
        else:
            res["bend_bad_edges"] = res.get("bend_bad_edges", 0) + t.bad_edges
            if "bend_samples" not in res: res["bend_samples"] = t.bad_samples
    if t.win_viol:
        (viol("L3-WINDOW", name, f"{prov} n={t.win_viol}") if main_scope
         else res.__setitem__("bend_win", res.get("bend_win", 0) + t.win_viol))
    note("CONS")
    if t.Rpoly != pnorm(R, c["R"]) or t.Q != pnorm(R, c["Q"]):
        viol("CONS", name, f"{prov} tree (R,Q) != division (R,Q)")

def run_tower(tag, d0, r0, r1, r2, r3, kind, p, design):
    t0 = time.time()
    T4 = Tower4(kind, p, d0, r0, r1, r2, r3, f"{kind},p{p},{tag}")
    E = Engine2(T4)
    C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T; R = T.R
    name = f"{tag}/{kind},p={p}"
    main_scope = tag in MAIN_SCOPE
    vis = E.vis_certs()
    W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
    e2 = T3.e2
    s2g3 = E.s2(T3.gamma3)
    res = dict(tower=name, E4=T4.E4, Gamma0=C.Gamma0, vis=vis,
               degPhi2=T.degPhi2, gamma3=T3.gamma3, s2gamma3=s2g3,
               main_scope=main_scope)
    cen = dict(pairs=0, fired=0, II1=0, II2=0, II3=0, e1nz=0, E0zero=0,
               dcx_pred=0, dcx_meas=0, dcx_mismatch=0, mcD_sep=0,
               q1nz=0)
    cache = {}
    inputs = {}
    mism_samples = []
    for ga in W1:
        for gb in W1:
            cen["pairs"] += 1
            ah, (s3a, s2a) = anchor2(C, cache, ga)
            bh, (s3b, s2b) = anchor2(C, cache, gb)
            T3sum = s3a + s3b
            E1IH, E0IH = pdivmod(R, pmul(R, ah, bh), T.Phi2)
            e1nz = bool(pnorm(R, E1IH))
            if e1nz: cen["e1nz"] += 1
            if not pnorm(R, E0IH): cen["E0zero"] += 1
            fire2 = (T3sum >= e2)
            fire3 = (e1nz and T3sum == e2 - 1)
            fired = fire2 or fire3
            if fired:
                cen["fired"] += 1
                cen["II2" if (fire2 and e1nz) else
                    "II1" if fire2 else "II3"] += 1
            dcx_pred = (T.g1 == 1 and T3.g2 == 1
                        and (s2a + s2b)//T.e1 == 1
                        and s3a == e2 - 1 and s3b == e2 - 1
                        and (s2a + s2b) + s2g3 >= 2*T.e1)
            dcx_pred_mut = (T.g1 == 1 and T3.g2 == 1
                            and (s2a + s2b)//T.e1 == 1
                            and s3a == e2 - 1 and s3b == e2 - 1)
            if dcx_pred: cen["dcx_pred"] += 1
            if dcx_pred_mut and not dcx_pred: cen["mcD_sep"] += 1
            if design: continue
            # ---- sealed measurement side ----
            if fired:
                if pnorm(R, E0IH):
                    k0 = poly_key(R, E0IH)
                    if k0 not in inputs: inputs[k0] = (E0IH, "E0")
                if e1nz:
                    k1 = poly_key(R, E1IH)
                    if k1 not in inputs: inputs[k1] = (E1IH, "E1")
            dcx_meas = False
            if e1nz:
                Q1, _ = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
                if pnorm(R, Q1):
                    cen["q1nz"] += 1
                    d3pl = T3sum // e2
                    dcx_meas = ((d3pl == 1 and s3a == e2 - 1 and s3b == e2 - 1)
                                or (T3sum == e2 - 1 and e2 == 1))
            if dcx_meas:
                cen["dcx_meas"] += 1
                note("L4a")
                if not (T.g1 == 1 and s3a == e2 - 1 and s3b == e2 - 1):
                    viol("L4a-OUTER", name, f"({ga},{gb})")
                if T.e1 <= 2:
                    viol("L4c-EMPTY", name, f"({ga},{gb}) e1={T.e1}")
            note("L4b")
            if dcx_meas != dcx_pred:
                cen["dcx_mismatch"] += 1
                viol("L4b-SHARP", name,
                     f"({ga},{gb}) meas={dcx_meas} pred={dcx_pred} "
                     f"T3={T3sum} s3=({s3a},{s3b}) s2=({s2a},{s2b}) "
                     f"T2+s2g3={(s2a+s2b)+s2g3} 2e1={2*T.e1}")
                if len(mism_samples) < 6:
                    mism_samples.append((ga, gb, dcx_meas, dcx_pred))
            if dcx_pred_mut != dcx_meas and dcx_pred == dcx_meas:
                MC["D"] += 1
    res["census"] = cen
    if design:
        res["design_only"] = True
        print(f"-- {name}: E4={T4.E4} degPhi2={T.degPhi2} vis={vis}")
        print(f"   design census: {cen}; elapsed {time.time()-t0:.1f}s")
        return res
    for k, (f, prov) in sorted(inputs.items()):
        run_engine_input(E, f, prov, name, main_scope, res)
    for f, prov in breadth_inputs(T):
        run_engine_input(E, f, prov, name, main_scope, res)
    res["n_inputs"] = len(inputs)
    res["mism_samples"] = mism_samples
    print(f"-- {name}: E4={T4.E4} fired={cen['fired']} "
          f"(II1/II2/II3={cen['II1']}/{cen['II2']}/{cen['II3']}) "
          f"inputs={len(inputs)} dcx meas/pred={cen['dcx_meas']}/"
          f"{cen['dcx_pred']} mism={cen['dcx_mismatch']}; "
          f"elapsed {time.time()-t0:.1f}s")
    return res

def main():
    design = "--design" in sys.argv
    t0 = time.time()
    print("rm2_probe — (RM-2) ENGINE PROBE"
          + (" [DESIGN MODE: censuses only, no law legs]" if design else ""))
    all_res = []
    for (tag, d0, r0, r1, r2, r3, why) in ROSTER:
        for (kind, p) in RINGS[tag]:
            all_res.append(run_tower(tag, d0, r0, r1, r2, r3, kind, p, design))
    print("\n== COUNTS ==")
    for k in sorted(CNT): print(f"  {k}: {CNT[k]}")
    if not design:
        print("== CONTROLS (separate from the law) ==")
        for k in "ABCDE":
            print(f"  MC-{k}: {'TRIPPED' if MC[k] > 0 else 'NOT-TRIPPED'} "
                  f"(count {MC[k]})")
    print(f"== VIOLATIONS: {len(VIOL)} ==")
    for v in VIOL[:60]: print("  ", v)
    bend = {r["tower"]: {kk: r[kk] for kk in
            ("bend_caps", "bend_bad_edges", "bend_win") if kk in r}
            for r in all_res if not r.get("main_scope") and not design}
    if bend: print("== BEND CENSUS (out-of-scope shapes, separate) ==", bend)
    out = dict(design=design, roster=[r[0] for r in ROSTER],
               counts=CNT, violations=VIOL, controls=MC, bend=bend,
               towers=[{k: v for k, v in r.items()
                        if k not in ("vis",)} | {"vis": r["vis"]}
                       for r in all_res],
               elapsed=round(time.time() - t0, 1))
    fn = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "rm2_probe_results.json" if not design
                      else "rm2_probe_design.json")
    with open(fn, "w") as fh: json.dump(out, fh, indent=1, default=str)
    print(f"results -> {fn}; total elapsed {time.time()-t0:.1f}s")
    if design:
        print("DESIGN MODE COMPLETE (no verdict; no law leg evaluated)")
        return 0
    lawfams = ("L1-WEIGHT", "L2-READ", "L2-EPS", "CONS", "L4a-OUTER")
    termfams = ("L3-TERM", "L3-CAP", "L3-WINDOW")
    locusfams = ("L4b-SHARP", "L4c-EMPTY")
    def n(fams): return sum(1 for v in VIOL if v[0] in fams)
    print(f"LAW VERDICT (RM-2 engine L1/L2/CONS/L4a, predicted-0): "
          f"{'GREEN' if n(lawfams) == 0 else 'RED (probe SUCCESS)'} "
          f"[{n(lawfams)} violations]")
    print(f"TERMINATION VERDICT (L3 main scope, predicted-0): "
          f"{'GREEN' if n(termfams) == 0 else 'RED (probe SUCCESS)'} "
          f"[{n(termfams)} violations]")
    print(f"LOCUS VERDICT (L4b sharp-transport + L4c emptiness, "
          f"conjecture-grade predicted-0): "
          f"{'GREEN' if n(locusfams) == 0 else 'RED (probe SUCCESS)'} "
          f"[{n(locusfams)} violations]")
    print(f"CONTROL VERDICT (mutation teeth, SEPARATE): "
          f"{'MET' if all(MC[k] > 0 for k in 'ABCDE') else 'PARTIAL: ' + str(MC)}")
    return 0 if len(VIOL) == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
