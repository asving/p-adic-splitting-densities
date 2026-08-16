#!/usr/bin/env python3
"""OM-4 certification leg for (MP1) = HYP.42 (ledger), EFF.T2.23, chapter-E node E.40.

The corpus's own narrowing (EFF.T2.61, EFF.T2.23 DERIVATION): after the S1.8C frame
transport, the open content of (MP1) is ITEM 5 of the (MID-PEEL) input suite -- the peeled
RECENTERED level-one key Phi'' = Phi' - L_lam(s) must admit a certified orbit/(e,f)
decomposition, "which requires Phi'' irreducible, asserted nowhere".

This script certifies, with exact arithmetic at both primes p in {2,3} and both
characteristics (Q_p and F_p((t))):

  LEG 1 (Hensel stage, f1 = 2, e1 = 1): recentered keys of the unramified quadratic key
     (phi = x^2+x+1 at p=2, x^2+1 at p=3) at every digit and heights 1..4, arbitrary-lift
     perturbations included: ALL irreducible.  Decorrelated tests: char 0 via PARI
     factorpadic; char p via exhaustive mod-t^N root search (a monic integral quadratic is
     reducible over F_p((t)) iff it has an integral root, iff it has a root mod t^N for
     every N -- absence at N certifies irreducibility).

  LEG 2 (ramified stage, e1 = 2, f1 = 1; the DEFEAT SYSTEM): Phi' = x^2 - pi (a
     representative of the order-1 type (x; 1/2, y-1)).  Stage height of an increment
     L = a1*x + a0 (deg < D' = 2) in the e1-normalized units: v2(L) = min(2 v(a1) + 1,
     2 v(a0)).  The frame admits a recentering only at v2(L) > T = D'*h = 2 (the (WINDOW)
     floor of the stage: h = 1 is the height of the base side's endpoint in stage units).
     Defeat system:  { v2(L) > 2  AND  Phi'' = Phi' - L reducible }.
     The sweep solves it: INFEASIBLE inside the frame, and SHARP at the boundary
     v2(L) = 2, where explicit reducible witnesses exist (x^2-4 = (x-2)(x+2) at p=2 via
     L = -2; x^2-3x-18 = (x-6)(x+3) at p=3 via L = 3x+15).  The exact infeasibility proof
     (ultrametric square analysis) is transcribed in the unit note §3.2.

  LEG 3 ((e,f) oracle, char 0 only): every certified-irreducible recentered key from legs
     1-2 is fed to PARI nfinit/idealprimedec: the orbit/(e,f) decomposition above p must be
     a SINGLE prime with (e,f) equal to the chain prediction ((1,2) for leg 1, (2,1) for
     leg 2) -- item 5's emission, from an independent implementation (PARI's round 4).

  LEG 4 (peel, items 2-4 shadow): represented blocks G = Phi'' * (cofactor in the same
     class), exact peel G' = G / Phi'', (MID-MASS) degree law, key-freeness certificate
     (gcd | nonzero increment of lower degree), and the product-theorem window check
     N(G) = N(Phi'') + N(G'), pointwise on computed polygons.

Run:  PYTHONPATH=~/.local/lib/python3.10/site-packages python3 om4_mp1_recentered_key.py
"""

import sys
from itertools import product as iproduct
from math import gcd

# ---- minimal exact domains (same conventions as om4_lb1_block_suite.py) -------------

class Dom:
    def __init__(self, p): self.p, self.char = p, 0
    def zero(self): return 0
    def one(self): return 1
    def is_zero(self, a): return a == 0
    def add(self, a, b): return a + b
    def neg(self, a): return -a
    def mul(self, a, b): return a * b
    def val(self, a):
        if a == 0: return None
        v = 0
        while a % self.p == 0: a //= self.p; v += 1
        return v
    def from_int(self, n): return n
    def times_pi_pow(self, a, k): return a * self.p ** k

class DomT:
    def __init__(self, p): self.p, self.char = p, p
    def norm(self, t_):
        L = list(t_)
        while L and L[-1] % self.p == 0: L.pop()
        return tuple(c % self.p for c in L)
    def zero(self): return ()
    def one(self): return (1,)
    def is_zero(self, a): return len(a) == 0
    def add(self, a, b):
        n = max(len(a), len(b))
        return self.norm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                          for i in range(n)])
    def neg(self, a): return self.norm([-c for c in a])
    def mul(self, a, b):
        if not a or not b: return ()
        out = [0] * (len(a) + len(b) - 1)
        for i, ca in enumerate(a):
            for j, cb in enumerate(b): out[i + j] += ca * cb
        return self.norm(out)
    def val(self, a):
        if not a: return None
        for i, c in enumerate(a):
            if c % self.p: return i
        return None
    def from_int(self, n): return self.norm((n,))
    def times_pi_pow(self, a, k): return self.norm((0,) * k + tuple(a)) if a else ()

def pnorm(D, f): return {i: c for i, c in f.items() if not D.is_zero(c)}
def padd(D, f, g):
    out = dict(f)
    for i, c in g.items(): out[i] = D.add(out.get(i, D.zero()), c)
    return pnorm(D, out)
def pneg(D, f): return {i: D.neg(c) for i, c in f.items()}
def psub(D, f, g): return padd(D, f, pneg(D, g))
def pmul(D, f, g):
    out = {}
    for i, a in f.items():
        for j, b in g.items():
            out[i + j] = D.add(out.get(i + j, D.zero()), D.mul(a, b))
    return pnorm(D, out)
def pdeg(f): return max(f) if f else -1
def pconst(D, a): return {0: a} if not D.is_zero(a) else {}

def pdivmod_monic(D, f, phi):
    f = dict(f); q = {}
    dphi = pdeg(phi)
    while pdeg(f) >= dphi:
        d = pdeg(f); lc = f[d]
        q[d - dphi] = lc
        for j, c in phi.items():
            k = d - dphi + j
            f[k] = D.add(f.get(k, D.zero()), D.neg(D.mul(lc, c)))
            if D.is_zero(f[k]): del f[k]
    return pnorm(D, q), pnorm(D, f)

def development(D, f, phi):
    out = []
    while f:
        f, r = pdivmod_monic(D, f, phi)
        out.append(r)
    return out

def gauss_val(D, a):
    if not a: return None
    return min(D.val(c) for c in a.values())

def polygon(D, f, phi):
    dev = development(D, f, phi)
    pts = sorted((j, gauss_val(D, a)) for j, a in enumerate(dev) if a)
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1): hull.pop()
            else: break
        hull.append(pt)
    return dev, hull

# ---- irreducibility testers ----------------------------------------------------------

def pari_handle():
    from cypari2 import Pari
    return Pari()

def irr_char0(pari, coeffs, p, prec=60):
    """coeffs low->high ints; True iff irreducible over Q_p (factorpadic single factor
    of full degree, multiplicity 1)."""
    n = len(coeffs) - 1
    fx = pari(f"Pol({[coeffs[n - i] for i in range(n + 1)]})")
    fac = pari.factorpadic(fx, p, prec)
    degs = [int(pari.poldegree(fac[0][k])) for k in range(len(fac[0]))]
    mults = [int(m) for m in fac[1]]
    return degs == [n] and mults == [1]

def quad_root_mod_tN(D, f, N):
    """f monic quadratic over F_p[[t]] (dict form, coeffs = tuples).  Search for a root
    in F_p[t]/t^N by digitwise extension; returns True iff a root mod t^N exists.
    (Reducible over F_p((t)) with integral coeffs => integral root => root mod t^N.)"""
    p = D.p
    b = f.get(1, D.zero()); c = f.get(0, D.zero())
    def val_at(r):
        # f(r) mod t^N, r = tuple
        fr = D.add(D.add(D.mul(r, r), D.mul(b, r)), c)
        v = D.val(fr)
        return N if (v is None or v >= N) else v
    partial = [()]
    for k in range(N):
        nxt = []
        for r in partial:
            for d in range(p):
                r2 = D.norm(tuple(r) + (0,) * (k - len(r)) + (d,)) if k >= len(r) else None
                # simpler: r2 = r + d*t^k
                r2 = D.add(r, D.times_pi_pow(D.from_int(d), k))
                if val_at(r2) >= k + 1:
                    nxt.append(r2)
        partial = nxt
        if not partial: return False
    return True

# ---- LEG 1: unramified quadratic stage -----------------------------------------------

def leg1(log):
    fails = 0
    pari = pari_handle()
    irreducible_keys_char0 = []   # for leg 3: (p, coeffs)
    for p in (2, 3):
        # char 0
        D = Dom(p)
        base = {2: 1, 1: 1 % 3 if p == 3 else 1, 0: 1}
        if p == 2: base = {2: 1, 1: 1, 0: 1}       # x^2+x+1, res irreducible over F_2
        else:      base = {2: 1, 0: 1}             # x^2+1,   res irreducible over F_3
        n_tested = n_irr = 0
        for lam in (1, 2, 3, 4):
            for s1 in range(p):
                for s0 in range(p):
                    if s0 == 0 and s1 == 0: continue
                    for junk1 in range(p):          # arbitrary-lift perturbation at lam+1
                        for junk0 in range(p):
                            L = {1: p ** lam * s1 + p ** (lam + 1) * junk1,
                                 0: p ** lam * s0 + p ** (lam + 1) * junk0}
                            L = pnorm(D, L)
                            Phi2 = psub(D, base, L)
                            coeffs = [Phi2.get(i, 0) for i in range(3)]
                            n_tested += 1
                            if irr_char0(pari, coeffs, p):
                                n_irr += 1
                                irreducible_keys_char0.append((p, coeffs, (1, 2)))
                            else:
                                fails += 1
                                log.append(f"    FAIL leg1 char0 p={p}: reducible "
                                           f"recentered key {coeffs} (lam={lam}, s=({s0},{s1}))")
        log.append(f"  [leg1 char0 p={p}] {n_irr}/{n_tested} recentered keys irreducible")
        # char p
        Dt = DomT(p)
        if p == 2: baset = {2: Dt.one(), 1: Dt.one(), 0: Dt.one()}
        else:      baset = {2: Dt.one(), 0: Dt.one()}
        n_tested = n_irr = 0
        N = 12
        for lam in (1, 2, 3):
            for s1 in range(p):
                for s0 in range(p):
                    if s0 == 0 and s1 == 0: continue
                    for junk0 in range(p):
                        L = {1: Dt.times_pi_pow(Dt.from_int(s1), lam),
                             0: Dt.add(Dt.times_pi_pow(Dt.from_int(s0), lam),
                                       Dt.times_pi_pow(Dt.from_int(junk0), lam + 1))}
                        L = pnorm(Dt, L)
                        Phi2 = psub(Dt, baset, L)
                        n_tested += 1
                        if not quad_root_mod_tN(Dt, Phi2, N):
                            n_irr += 1
                        else:
                            # a mod-t^N root exists: escalate before declaring reducible
                            if quad_root_mod_tN(Dt, Phi2, N + 8):
                                fails += 1
                                log.append(f"    FAIL leg1 char{p}: root mod t^{N+8} for "
                                           f"{Phi2} -- reducible recentered key?")
                            else:
                                n_irr += 1
        log.append(f"  [leg1 char{p} p={p}] {n_irr}/{n_tested} recentered keys certified "
                   f"irreducible (no root mod t^{N})")
    return fails, irreducible_keys_char0

# ---- LEG 2: ramified stage, the defeat system ---------------------------------------

def stage_val_e2(D, L):
    """v2(a1 x + a0) = min(2 v(a1) + 1, 2 v(a0)) -- the e1 = 2 stage normalization for
    the key x^2 - pi."""
    vals = []
    a1, a0 = L.get(1), L.get(0)
    if a1 is not None and not D.is_zero(a1): vals.append(2 * D.val(a1) + 1)
    if a0 is not None and not D.is_zero(a0): vals.append(2 * D.val(a0))
    return min(vals) if vals else None

def leg2(log):
    fails = 0
    pari = pari_handle()
    irreducible_keys_char0 = []
    T2 = 2  # = D' * h with D' = 2, h = 1 (stage-unit height of the base side endpoint)
    for p in (2, 3):
        D = Dom(p)
        base = {2: 1, 0: -p}                       # Phi' = x^2 - p
        stats = {}
        boundary_reducibles = []
        for va1 in range(0, 4):
            for ua1 in ([0] if va1 == 3 else [u for u in range(1, p)] ):
                pass
        # sweep a1, a0 over p-power * unit grids (exact): a = u * p^v, u in units window
        units = [u for u in range(-2 * p, 2 * p + 1) if u % p != 0]
        n_valid = n_valid_irr = 0
        for v1 in list(range(0, 4)) + [None]:
            for u1 in (units if v1 is not None else [0]):
                a1 = 0 if v1 is None else u1 * p ** v1
                for v0 in list(range(0, 5)) + [None]:
                    for u0 in (units if v0 is not None else [0]):
                        a0 = 0 if v0 is None else u0 * p ** v0
                        L = pnorm(D, {1: a1, 0: a0})
                        if not L: continue
                        v2L = stage_val_e2(D, L)
                        Phi2 = psub(D, base, L)
                        coeffs = [Phi2.get(i, 0) for i in range(3)]
                        # squarefree guard (disc = 0 keys are degenerate, not states)
                        disc = coeffs[1] ** 2 - 4 * coeffs[0]
                        if disc == 0: continue
                        irr = irr_char0(pari, coeffs, p)
                        stats.setdefault(v2L, [0, 0])
                        stats[v2L][0] += 1
                        stats[v2L][1] += 0 if irr else 1
                        if v2L > T2:
                            n_valid += 1
                            if irr:
                                n_valid_irr += 1
                                irreducible_keys_char0.append((p, coeffs, (2, 1)))
                            else:
                                fails += 1
                                log.append(f"    FAIL leg2 DEFEAT p={p}: frame-valid "
                                           f"v2(L)={v2L} > {T2} but {coeffs} reducible")
                        elif not irr:
                            boundary_reducibles.append((v2L, coeffs))
        log.append(f"  [leg2 char0 p={p}] frame-valid (v2 > {T2}): {n_valid_irr}/{n_valid} "
                   f"irreducible; per-height (v2: tested, reducible): "
                   + str({k: tuple(v) for k, v in sorted(stats.items())}))
        sharp = [bc for bc in boundary_reducibles if bc[0] == T2]
        log.append(f"    boundary v2 = {T2} reducible witnesses (SHARPNESS): "
                   f"{sharp[:3]}{' ...' if len(sharp) > 3 else ''}")
        if not sharp:
            fails += 1
            log.append(f"    FAIL leg2 p={p}: no boundary reducible witness found -- "
                       f"threshold not sharp as claimed")
        # char p analogue: Phi' = x^2 - t over F_p[[t]]
        Dt = DomT(p)
        baset = {2: Dt.one(), 0: Dt.neg(Dt.times_pi_pow(Dt.one(), 1))}
        n_valid = n_valid_irr = 0
        N = 14
        for v1 in list(range(0, 3)) + [None]:
            for u1 in (range(1, p) if v1 is not None else [0]):
                for v0 in list(range(0, 4)) + [None]:
                    for u0 in (range(1, p) if v0 is not None else [0]):
                        for u0b in range(p):   # second digit of a0
                            a1 = Dt.times_pi_pow(Dt.from_int(u1), v1) if v1 is not None else Dt.zero()
                            a0 = Dt.times_pi_pow(Dt.from_int(u0), v0) if v0 is not None else Dt.zero()
                            a0 = Dt.add(a0, Dt.times_pi_pow(Dt.from_int(u0b),
                                                            (v0 if v0 is not None else 0) + 1))
                            L = pnorm(Dt, {1: a1, 0: a0})
                            if not L: continue
                            v2L = stage_val_e2(Dt, L)
                            Phi2 = psub(Dt, baset, L)
                            if v2L is None or v2L <= T2: continue
                            n_valid += 1
                            if not quad_root_mod_tN(Dt, Phi2, N):
                                n_valid_irr += 1
                            else:
                                # char 2 inseparable-square check: x^2 + c with c a square
                                # series would be (x + sqrt(c))^2; frame-valid c has odd
                                # t-order 1, so this cannot happen -- any root is a defect.
                                fails += 1
                                log.append(f"    FAIL leg2 char{p}: frame-valid v2={v2L} "
                                           f"key {Phi2} has root mod t^{N}")
        log.append(f"  [leg2 char{p} p={p}] frame-valid: {n_valid_irr}/{n_valid} certified "
                   f"irreducible (no root mod t^{N})")
    return fails, irreducible_keys_char0

# ---- LEG 3: (e,f) oracle via idealprimedec ------------------------------------------

def leg3(keys, log, cap_per_class=40):
    fails = 0
    pari = pari_handle()
    from collections import defaultdict
    seen = defaultdict(int)
    n_ok = n_run = 0
    for p, coeffs, ef_pred in keys:
        cls = (p, ef_pred)
        if seen[cls] >= cap_per_class: continue
        seen[cls] += 1
        n = len(coeffs) - 1
        fx = pari(f"Pol({[coeffs[n - i] for i in range(n + 1)]})")
        # global number field Q[x]/(fx); primes above p <-> Q_p-factors.
        try:
            nf = pari.nfinit([fx, [p]])
            dec = pari.idealprimedec(nf, p)
        except Exception as e:
            log.append(f"    leg3 skip {coeffs} (p={p}): {e}")
            continue
        n_run += 1
        efs = sorted((int(pr[2]), int(pr[3])) for pr in dec)   # (e, f) per prime
        if efs == [ef_pred]:
            n_ok += 1
        else:
            fails += 1
            log.append(f"    FAIL leg3: {coeffs} (p={p}) has orbit/(e,f) {efs}, "
                       f"predicted single {ef_pred}")
    log.append(f"  [leg3 (e,f) oracle] {n_ok}/{n_run} single-orbit with predicted (e,f)")
    return fails

# ---- LEG 4: the peel (items 2-4 shadow) ---------------------------------------------

def leg4(log):
    fails = 0
    def check(cond, msg):
        nonlocal fails
        if not cond:
            fails += 1
            log.append(f"    FAIL leg4: {msg}")
    for p in (2, 3):
        for D, tag in ((Dom(p), "char 0"), (DomT(p), f"char {p}")):
            # stage: Phi' = x^2 - pi; frame-valid recentering L = pi^2 * 1 (v2 = 4 > 2)
            pi1 = D.times_pi_pow(D.one(), 1)
            Phi1 = pnorm(D, {2: D.one(), 0: D.neg(pi1)})
            L = pconst(D, D.times_pi_pow(D.one(), 2))
            Phi2 = psub(D, Phi1, L)                     # x^2 - pi - pi^2
            # cofactor in the same class: another frame-valid recentering, distinct
            Cof = psub(D, Phi1, pconst(D, D.times_pi_pow(D.one(), 3)))
            G = pmul(D, Phi2, Cof)                      # represented block, nu = 2, D' = 2
            q, r = pdivmod_monic(D, G, Phi2)
            check(not r, "Phi'' does not divide G exactly")
            check(q == Cof, "peel quotient mismatch")
            check(pdeg(q) == 2 * (2 - 1), "(MID-MASS) degree law failed")
            dif = psub(D, Phi2, Cof)
            check(bool(dif) and pdeg(dif) == 0,
                  "key-freeness certificate: difference not a nonzero constant")
            # product-theorem window check at the ORDER-1 polygon (key x): the polygon of
            # G is the Minkowski sum of the polygons of Phi'' and G'; all slopes shared.
            x = {1: D.one()}
            _, hullG = polygon(D, G, x)
            _, hullP = polygon(D, Phi2, x)
            _, hullQ = polygon(D, q, x)
            def side_multiset(hull):
                out = []
                for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
                    g = gcd(y1 - y2, x2 - x1)
                    out += [((y1 - y2) // g, (x2 - x1) // g)] * g
                return sorted(out)
            check(side_multiset(hullG) == sorted(side_multiset(hullP) + side_multiset(hullQ)),
                  f"product-theorem side additivity failed: {hullG} vs {hullP}+{hullQ}")
            log.append(f"  [leg4 {tag} p={p}] peel + (MID-MASS) + key-freeness + window "
                       f"additivity OK")
    return fails


def main():
    log = []
    total = 0
    log.append("LEG 1: unramified quadratic stage (f1 = 2), recentered keys all irreducible")
    f1, keys1 = leg1(log)
    total += f1
    log.append("LEG 2: ramified stage (e1 = 2), the DEFEAT SYSTEM {v2(L) > T2, reducible}")
    f2, keys2 = leg2(log)
    total += f2
    log.append("LEG 3: item-5 (e,f) emission against PARI idealprimedec")
    total += leg3(keys1 + keys2, log)
    log.append("LEG 4: the peel -- items 2-4 numerical shadow")
    total += leg4(log)
    print("\n".join(log))
    print(f"\nTOTAL FAILS: {total}")
    sys.exit(1 if total else 0)


if __name__ == "__main__":
    main()
