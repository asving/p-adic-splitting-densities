#!/usr/bin/env python3
"""CU-1 PRIMARY GATE (O3adj sec 3.4): T-G -- window geometry at DEPTH 3.

The O3adj adjudication promoted the O-1thr rev-3-recommended depth-3
falsifier to CU-1's primary gate: it exercises every per-site ingredient of
the CU-1 induction step (SPAN/(M6a)/(M6c)/Corollary VTX + REAL-equiv) at
ORDER-2 STATES -- exactly where (V1) (MacLane augmentation multiplicativity)
and (V2) (key initial form / development identity / residual dictionary) are
genuinely consumed rather than proved outright (O1thr rev-4 perimeter).

Setup per (box, depth-1 site, depth-2 site).  Boxes: monic f = X^n + ...,
all a_i = 0 mod p (root key Phi_0 = X, the standing degree-1 slice).

  Depth-1 site nu_0 = (face (e,h), residual psi of degree g, mult mu):
    Phi_1 = sum_k psihat_k p^((g-k)h) X^(ek)      (KEY1 standard lift),
    w_1(B) = min_t (e*v_p(b_t) + t*h)             (VAL1), ghat_0 = e*g*h.
  State o_1 window points: u_k = w_1(C_k) + k*ghat_0, (C_k) = Phi_1-dev of f,
  window = slots 0..mu (the T-F-verified depth-2 geometry).

  Depth-2 site nu_1: a principal face (k0,u0)-(k1,u1) of o_1's window hull,
  slope -h1/e1 (coprime), d1 = (k1-k0)/e1, side value gamma_1 = e1*u0 + k0*h1,
  residual pattern pat_1(kappa) in K_1 = F_p[z]/psi(z) read at stride slots
  by the PINNED level-1 residue normalization: for on-line C with
  beta = w_1(C), support t in t0 + e*N (t0 in [0,e), t0*h = beta mod e),
    res_1(C) := sum_i ((c_{t0+e*i} / p^((beta-(t0+e*i)h)/e)) mod p) * z^i.
  (Since deg C < e*g the z-degree is < g: no psi-reduction, and res_1 != 0
  for every nonzero on-line C -- pat_1 endpoints nonzero is FORCED, asserted.
  Slot-twist normalizations differing from GMN's by unit/z-power twists
  change psi_1 by a unit substitution only; the checker's key is built from
  its OWN psi_1, so the probed laws are convention-consistent.)
  R_1 = sum pat_1(kappa) z'^kappa factored over K_1; each (psi_1, mu_1)
  yields an ORDER-2 state o_2 with
    gamma_2 = e1*e*g*h + h1                        (sec 1.1 recursion, i=1),
    w_2(B)  = min_j (e1*w_1(c_j) + j*gamma_2)      (Phi_1-dev of B),
    Phi_2   = sum_kappa chat_kappa Phi_1^(e1*kappa), chat_kappa the
              weight-(g1-kappa)*gamma_2 lift of psi_1's kappa-coefficient
              (the standard lift one level up; chat_g1 = 1),
    ghat_1  = w_2(Phi_2) = e1*g1*gamma_2 (asserted),
    U_m     = w_2(D_m) + m*ghat_1, (D_m) = Phi_2-dev of f, window 0..mu_1.

Pass/fail checks (a violation FIRES the gate):
  T-G.0 (R1)-support: the harvested face line supports ALL o_1 slots
        (e1*u_k + k*h1 >= gamma_1) -- (M6c) at o_1 in the new configs.
  T-G.1a WGEO(a) display: w_2(f) = gamma_1.
  T-G.1b (V2b) at f:      min_m U_m = w_2(f).
  T-G.1c WGEO(b) vertex law: min_m U_m first attained EXACTLY at m = mu_1;
         D_{mu_1} != 0 and w_2(D_{mu_1}) = gamma_1 - mu_1*ghat_1 (VTX pin).
  T-G.2 (M6c)(i): window faces strictly descend; every beyond-window point
        (m > mu_1) lies STRICTLY ABOVE every window face's extended line.
  T-G.3 (M6c)(ii): principal part of the FULL U-polygon = window hull.
  T-G.4 VTX chain at depth: e1*w_1(D_{mu_1}) <= w_2(D_{mu_1}) ((V2b) at
        level 1 for deg >= deg Phi_1) and vhtx_1 = w_1(D_{mu_1}) <= gamma_1/e1.
  T-G.5 (V1) DIRECT: w_2(A*B) = w_2(A) + w_2(B) on a deterministic pool of
        pairs (Phi_1, Phi_2, f, D_{mu_1}, X+p, p) -- multiplicativity of the
        order-2 augmented valuation, probed as arithmetic.
  T-G.6 (V2b) DIRECT: the Phi_2-development computes w_2 from below for
        B in {f, Phi_1*f}.
REPORTED (not pass/fail): count of instances with w_1(D_{mu_1}) < u_{k1}
        (the naive order-2 (N4)-lower reading -- statement-shaping data for
        the open (M6b)(ii) band, mixed units, NOT a law on record).

Coverage tallies: instances with beyond-window slots at o_2, growth steps
(e1*g1 >= 2) vs refinements, extension-field parents (g >= 2), g1 >= 2
children, saturated parents (mu = 1; laws are state-hypothesis-free at
rev 4, so these are probed too).
"""
import math
import os
import sys
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import o1thr_persite_check as base
from o1thr_rev2_checks import v_int, development, w0
from o1thr_rev3_depth2_check import V_sloped, hull_faces, principal, \
    strictly_above

# ---------------- integer polynomial helpers (coeff lists, low->high) ----
def polmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    while out and out[-1] == 0:
        out.pop()
    return out


def poladd(a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, y in enumerate(b):
        out[i] += y
    while out and out[-1] == 0:
        out.pop()
    return out


def polpow(a, k):
    out = [1]
    for _ in range(k):
        out = polmul(out, a)
    return out


# ---------------- F_q = F_p[z]/psi arithmetic (tuples of length g) -------
def fq_mul(a, b, psi, p):
    g = len(psi) - 1
    c = [0] * (2 * g - 1) if g > 1 else [a[0] * b[0] % p]
    if g > 1:
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    c[i + j] = (c[i + j] + x * y) % p
        for i in range(len(c) - 1, g - 1, -1):
            if c[i]:
                q = c[i]  # psi monic
                for j in range(g + 1):
                    c[i - g + j] = (c[i - g + j] - q * psi[j]) % p
        c = c[:g]
    return tuple(x % p for x in c)


def fq_pow(a, k, psi, p):
    g = len(psi) - 1
    out = tuple([1] + [0] * (g - 1))
    while k:
        if k & 1:
            out = fq_mul(out, a, psi, p)
        a = fq_mul(a, a, psi, p)
        k >>= 1
    return out


def fq_inv(a, psi, p):
    return fq_pow(a, p ** (len(psi) - 1) - 2, psi, p)


# --------- polynomials over F_q: lists of tuples, low->high, trimmed -----
def fqp_trim(r, g):
    while r and not any(r[-1]):
        r.pop()
    return r


def fqp_divmod(a, b, psi, p):
    g = len(psi) - 1
    zero = tuple([0] * g)
    a = list(a)
    binv = fq_inv(b[-1], psi, p)
    q = [zero] * max(len(a) - len(b) + 1, 0)
    while len(a) >= len(b):
        c = fq_mul(a[-1], binv, psi, p)
        off = len(a) - len(b)
        q[off] = c
        for i, bc in enumerate(b):
            t = fq_mul(c, bc, psi, p)
            a[off + i] = tuple((x - y) % p for x, y in zip(a[off + i], t))
        a.pop()
        fqp_trim(a, g)
    return q, a


_IRR_CACHE = {}


def fq_irreducibles(psi, p, d):
    """Monic irreducibles of degree <= d over F_p[z]/psi, cached."""
    g = len(psi) - 1
    key = (p, psi)
    got = _IRR_CACHE.setdefault(key, {})
    elts = [tuple(t) for t in product(range(p), repeat=g)]
    one = tuple([1] + [0] * (g - 1))
    for dd in range(max(got) + 1 if got else 1, d + 1):
        out = []
        lower = [f for d2 in got if d2 <= dd // 2 for f in got[d2]]
        for tup in product(elts, repeat=dd):
            cand = list(tup) + [one]
            if all(fqp_divmod(cand, f, psi, p)[1] for f in lower):
                out.append(cand)
        got[dd] = out
    return got


def fq_factor(R, psi, p):
    """Factor nonzero R over F_q into {(monic irr tuple): mult}."""
    g = len(psi) - 1
    R = fqp_trim(list(R), g)
    assert R, "zero residual polynomial at depth 2"
    lead_inv = fq_inv(R[-1], psi, p)
    R = [fq_mul(c, lead_inv, psi, p) for c in R]
    fac = {}
    irrs = fq_irreducibles(psi, p, max(len(R) - 1, 1))
    for dd in sorted(irrs):
        for f in irrs[dd]:
            while len(R) > len(f) - 1:
                q, r = fqp_divmod(R, f, psi, p)
                if r:
                    break
                R = q
                key = tuple(tuple(c) for c in f)
                fac[key] = fac.get(key, 0) + 1
            if len(R) == 1:
                return fac
    assert len(R) == 1, "factorization incomplete"
    return fac


# ---------------- level-1 residue / lift (pinned normalization) ----------
def res1(C, p, e, h, g):
    """Level-1 residue of nonzero C (deg < e*g) in K_1, tuple of length g."""
    beta = V_sloped(C, p, e, h)
    t0 = next(t for t in range(e) if (beta - t * h) % e == 0)
    out = [0] * g
    for i in range(g):
        t = t0 + e * i
        if t < len(C) and t * h <= beta and C[t]:
            s = (beta - t * h) // e
            out[i] = (C[t] // p ** s) % p
    assert any(out), (C, e, h, beta)   # forced: deg < e*g (see docstring)
    return tuple(out)


def lift_elt(alpha, beta, p, e, h, g):
    """Integer poly c, deg < e*g, w_1(c) = beta, res1(c) = alpha (nonzero)."""
    t0 = next(t for t in range(e) if (beta - t * h) % e == 0)
    c = [0] * (e * g)
    for i, ai in enumerate(alpha):
        if ai:
            t = t0 + e * i
            assert beta - t * h >= 0, (alpha, beta, e, h)
            c[t] = ai * p ** ((beta - t * h) // e)
    return c


# ---------------- the depth-3 probe --------------------------------------
def run_TG(p, n, M, pairs_cap=4):
    boxes = [tuple(p * t for t in tup)
             for tup in product(range(p ** (M - 1)), repeat=n)]
    keys = ('g0', 'g1a', 'g1b', 'g1c', 'g2', 'g3', 'g4', 'g5', 'g6')
    stats = dict.fromkeys(keys, 0)
    stats.update(inst=0, beyond=0, growth=0, ext=0, g1ge2=0,
                 satpar=0, satst=0, lowrep=0)
    ex = {}

    def flag(key, *info):
        stats[key] += 1
        ex.setdefault(key, info)

    for a in boxes:
        f = list(a) + [1]
        for (j0, j1, e, h, pat, psi, mu, L) in base.sites_of_box(a, p, n, M):
            g = len(psi) - 1
            Phi1 = [0] * (e * g + 1)
            for k in range(g + 1):
                Phi1[e * k] = psi[k] * p ** ((g - k) * h)
            ghat0 = e * g * h
            assert V_sloped(Phi1, p, e, h) == ghat0
            C = development(f, Phi1)
            upts = [(k, V_sloped(C[k], p, e, h) + k * ghat0)
                    for k in range(len(C)) if any(C[k])]
            udict = dict(upts)
            wfaces = principal(hull_faces([q for q in upts if q[0] <= mu]))
            psit = tuple(x % p for x in psi)
            for (k0, u0), (k1, u1) in wfaces:
                d1 = math.gcd(u0 - u1, k1 - k0)
                e1, h1 = (k1 - k0) // d1, (u0 - u1) // d1
                gamma1 = e1 * u0 + k0 * h1
                if any(e1 * u + k * h1 < gamma1 for k, u in upts):
                    flag('g0', a, (j0, j1, e, h, psi, mu), (k0, k1, e1, h1))
                    continue
                zero = tuple([0] * g)
                pat1 = []
                for kap in range(d1 + 1):
                    j = k0 + e1 * kap
                    on = j in udict and e1 * udict[j] + j * h1 == gamma1
                    pat1.append(res1(C[j], p, e, h, g) if on else zero)
                assert any(pat1[0]) and any(pat1[-1]), (a, pat1)
                gamma2 = e1 * ghat0 + h1

                def w2(B):
                    dev = development(B, Phi1)
                    return min(e1 * V_sloped(dev[j], p, e, h) + j * gamma2
                               for j in range(len(dev)) if any(dev[j]))

                for psi1, mu1 in fq_factor(pat1, psit, p).items():
                    g1 = len(psi1) - 1
                    site2 = (a, (e, h, psi, mu), (k0, k1, e1, h1, psi1, mu1))
                    stats['inst'] += 1
                    stats['growth'] += e1 * g1 >= 2
                    stats['ext'] += g >= 2
                    stats['g1ge2'] += g1 >= 2
                    stats['satpar'] += mu == 1
                    stats['satst'] += mu1 == 1
                    Phi2 = polpow(Phi1, e1 * g1)
                    for kap in range(g1):
                        if any(psi1[kap]):
                            c = lift_elt(psi1[kap], (g1 - kap) * gamma2,
                                         p, e, h, g)
                            Phi2 = poladd(Phi2, polmul(c, polpow(Phi1,
                                                                 e1 * kap)))
                    ghat1 = e1 * g1 * gamma2
                    assert w2(Phi2) == ghat1, site2
                    D = development(f, Phi2)
                    Upts = [(m, w2(D[m]) + m * ghat1)
                            for m in range(len(D)) if any(D[m])]
                    Ud = dict(Upts)
                    w2f = w2(f)
                    if w2f != gamma1:
                        flag('g1a', site2, w2f, gamma1)
                    Umin = min(u for _, u in Upts)
                    if Umin != w2f:
                        flag('g1b', site2, Umin, w2f)
                    first = min(m for m, u in Upts if u == Umin)
                    if not (first == mu1 and mu1 in Ud
                            and Ud[mu1] == gamma1):
                        flag('g1c', site2, Upts)
                    wpts2 = [q for q in Upts if q[0] <= mu1]
                    wf2 = hull_faces(wpts2)
                    beyond = [q for q in Upts if q[0] > mu1]
                    stats['beyond'] += bool(beyond)
                    if (any(y2 >= y1 for (x1, y1), (x2, y2) in wf2)
                        or any(not strictly_above(m, u, F)
                               for m, u in beyond for F in wf2)):
                        flag('g2', site2, wpts2, beyond)
                    if principal(hull_faces(Upts)) != principal(wf2):
                        flag('g3', site2, Upts)
                    # T-G.4 VTX chain + (N4)-lower report
                    if mu1 < len(D) and any(D[mu1]):
                        vhtx1 = V_sloped(D[mu1], p, e, h)
                        if not (e1 * vhtx1 <= w2(D[mu1])
                                and Fraction(vhtx1)
                                <= Fraction(gamma1, e1)):
                            flag('g4', site2, vhtx1, w2(D[mu1]))
                        stats['lowrep'] += vhtx1 < u1
                    else:
                        flag('g4', site2, 'D_mu1 = 0')
                    # T-G.5 (V1) multiplicativity, deterministic pool
                    pool = [Phi1, Phi2, f, [p, 1], [p]]
                    if mu1 < len(D) and any(D[mu1]) and len(D[mu1]) > 1:
                        pool.append(D[mu1])
                    prs = [(pool[i], pool[i + 1]) for i in
                           range(min(pairs_cap, len(pool) - 1))]
                    for A, B in prs:
                        if w2(polmul(A, B)) != w2(A) + w2(B):
                            flag('g5', site2, A, B)
                    # T-G.6 (V2b) direct
                    for B in (f, polmul(Phi1, f)):
                        devB = development(B, Phi2)
                        m2 = min(w2(devB[j]) + j * ghat1
                                 for j in range(len(devB)) if any(devB[j]))
                        if m2 != w2(B):
                            flag('g6', site2, m2, w2(B))
    hard = sum(stats[k] for k in keys)
    print(f"p={p} n={n} M={M}: boxes={len(boxes)} order-2 instances="
          f"{stats['inst']} beyond-window={stats['beyond']} "
          f"growth(e1*g1>=2)={stats['growth']} ext-field(g>=2)={stats['ext']} "
          f"g1>=2={stats['g1ge2']} sat-parent={stats['satpar']} "
          f"sat-state={stats['satst']}")
    print("   violations " + " ".join(f"T-G.{k[1:]}:{stats[k]}"
                                      for k in keys)
          + f" | REPORT (N4)-lower-naive fails: {stats['lowrep']}")
    for k in keys:
        if stats[k]:
            print(f"   first {k} instance:", ex[k])
    return hard == 0, stats


if __name__ == "__main__":
    cfgs = [(2, 4, 4), (3, 4, 3), (2, 6, 3), (2, 6, 4), (2, 8, 3)]
    if len(sys.argv) > 1:
        cfgs = [tuple(map(int, s.split(','))) for s in sys.argv[1:]]
    ok, tot = True, {}
    for (p, n, M) in cfgs:
        good, st = run_TG(p, n, M)
        ok = ok and good
        for k, v in st.items():
            tot[k] = tot.get(k, 0) + v
    print("TOTALS:", tot)
    print("OVERALL:", "GATE SURVIVES (all T-G pass)" if ok
          else "GATE FIRES (T-G violations found)")
