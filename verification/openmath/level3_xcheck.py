#!/usr/bin/env python3
# level3_xcheck.py -- M5 CROSS-IMPLEMENTATION CONTROL (POST-SEAL DIAGNOSTIC; NOT PREREGISTERED)
#
# Purpose: independent re-implementation of the level-3 cocycle harness, written FROM THE
# NOTES ALONE -- lean/notes/openmath/ITERLAW_2026-08-08.md S0/S5 (the harness calculus:
# eq-(12-int), standard lifts, eps units, R-reads, val, anchors, windows) and
# DITER_RESTATE_2026-08-08.md S2 -- extended from 2 reads to 3 reads (e2,h2,psi2) by the
# same construction pattern.  The sealed runner verification/openmath/iterlawr_probe.py
# was NOT consulted while writing this harness (decorrelation rule of the M5 unit).
#
# Level-3 extension pattern (derived from the notes, recorded here for the note):
#   gammaW[1] = h0 (= e0*w0(Phi0)+h0, w0(Phi0)=0);  wPhi[i+1] = e_i*g_i*gammaW[i+1];
#   gammaW[i+1] = e_i*wPhi[i] + h_i.
#   Standard lift Phi[i+1] = sum_k LIFT_i((g_i-k)*gammaW[i+1], coeff_k(psi_i)) * Phi[i]^(e_i k)
#   (the on-line requirement w_i(a_{e_i k}) = (g_i-k)*gammaW[i+1] forces these weights;
#    at i=0 this is the notes' Phi1 display verbatim since gammaW[1]=h0).
#   LIFT_i(beta, xi): i=0: lift0(xi)*pi^beta (d0=1 throughout this file);
#     i>=1: (s,u)=eq12(beta,e_{i-1},h_{i-1}); beta0 = u - s*wPhi[i-1];
#     sum_m LIFT_{i-1}(beta0 - m*gammaW[i], xi_m) * Phi[i-1]^(s + m e_{i-1}).
#   eps_i(beta) = z_i^(lp_{i-1}*s - l_{i-1}*u), (s,u)=eq12(beta,e_{i-1},h_{i-1}),
#     l_{i-1}*h_{i-1} + lp_{i-1}*e_{i-1} = 1, 0 <= l_{i-1} < e_{i-1}   [pattern of eps1].
#   V_i(a,beta) (the level-i read): i=0: res(b/pi^beta) iff w0(b)=beta exactly, else 0;
#     i>=1: digits a_j of the Phi[i-1]-development, grid j = s + m e_{i-1},
#     slot weight beta_m = beta0 - m*gammaW[i], contribute (eps_{i-1}(beta_m) if i>=2 else 1)
#     * V_{i-1}(digit, beta_m) * z_i^m iff w_{i-1}(digit) = beta_m exactly  [pattern of R2].
#   val_N(f) = V_N(f, w_N(f)).  Anchors: iterated eq12 split top-down;
#   phi_gamma = pi^u1 * Phi0^s1 * Phi1^s2 * Phi2^s3; window u1 >= 0.
#   c3(gamma,gamma') = val3(phi_g * phi_g') / val3(phi_{g+g'}).
#
# F0 legs: with N=2 this same generic machinery must reproduce the ACCEPTED order-2 law
#   c = zbar^d2 * z1^((s1+s1'-s1(g+g') + l0*gamma2*d2)/e0), d2 = floor((s2+s2')/e1)
# EXACTLY (ground truth).  Any F0 failure is a bug in THIS file, never in the law.

import json, sys, itertools

# ---------------- residue fields (nested tower, elements = nested tuples / ints) ------

class FpField:
    def __init__(self, p):
        self.p = p; self.q = p; self.g = 1; self.sub = None
        self.zero = 0; self.one = 1 % p
    def add(self, a, b): return (a + b) % self.p
    def neg(self, a): return (-a) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def iszero(self, a): return a == 0
    def inv(self, a): return pow(a, self.p - 2, self.p)
    def embedsub(self, x): raise RuntimeError("no sub")
    def elements(self): return list(range(self.p))
    def pow(self, a, n):
        r = self.one
        for _ in range(n): r = self.mul(r, a)
        return r

class ExtField:
    # K = sub[y]/(y^g + c_{g-1} y^{g-1} + ... + c_0), mod = [c_0..c_{g-1}] sub-elements
    def __init__(self, sub, mod):
        self.sub = sub; self.mod = list(mod); self.g = len(mod)
        self.q = sub.q ** self.g
        self.zero = tuple([sub.zero] * self.g)
        self.one = tuple([sub.one] + [sub.zero] * (self.g - 1))
        if self.g >= 2:
            self.gen = tuple([sub.zero, sub.one] + [sub.zero] * (self.g - 2))
        else:
            self.gen = (sub.neg(mod[0]),)   # root of y + c0 is -c0
    def add(self, a, b): return tuple(self.sub.add(x, y) for x, y in zip(a, b))
    def neg(self, a): return tuple(self.sub.neg(x) for x in a)
    def iszero(self, a): return all(self.sub.iszero(x) for x in a)
    def embedsub(self, x): return tuple([x] + [self.sub.zero] * (self.g - 1))
    def mul(self, a, b):
        S = self.sub; g = self.g
        arr = [S.zero] * (2 * g - 1)
        for i, x in enumerate(a):
            if S.iszero(x): continue
            for j, y in enumerate(b):
                if S.iszero(y): continue
                arr[i + j] = S.add(arr[i + j], S.mul(x, y))
        for k in range(2 * g - 2, g - 1, -1):
            c = arr[k]
            if S.iszero(c): continue
            arr[k] = S.zero
            for j, mj in enumerate(self.mod):
                arr[k - g + j] = S.add(arr[k - g + j], S.neg(S.mul(c, mj)))
        return tuple(arr[:g])
    def pow(self, a, n):
        assert n >= 0
        r = self.one; base = a
        while n:
            if n & 1: r = self.mul(r, base)
            base = self.mul(base, base); n >>= 1
        return r
    def inv(self, a):
        assert not self.iszero(a)
        return self.pow(a, self.q - 2)
    def ppow(self, a, n):   # allows negative exponents
        if n >= 0: return self.pow(a, n)
        return self.inv(self.pow(a, -n))
    def elements(self):
        subs = self.sub.elements()
        return [tuple(t) for t in itertools.product(subs, repeat=self.g)]

def factorize(n):
    fs = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: fs[n] = fs.get(n, 0) + 1
    return fs

def mult_order(F, a):
    assert not F.iszero(a)
    t = F.q - 1
    for f in factorize(F.q - 1):
        while t % f == 0:
            b = F.pow(a, t // f)
            if b == F.one: t //= f
            else: break
    return t

# ---------------- coefficient rings O (d0 = 1 everywhere: K0 = F_p) -------------------

class ZRing:
    # O = Z_p operationally: elements exact integers, pi = p, val = p-adic valuation
    name = "Zp"
    def __init__(self, p): self.p = p; self.zero = 0; self.one = 1
    def add(self, a, b): return a + b
    def neg(self, a): return -a
    def mul(self, a, b): return a * b
    def iszero(self, a): return a == 0
    def val(self, a):
        if a == 0: return None
        v = 0
        while a % self.p == 0: a //= self.p; v += 1
        return v
    def res(self, a, d):    # class of a/pi^d in F_p; requires val(a) >= d
        assert a % (self.p ** d) == 0
        return (a // (self.p ** d)) % self.p
    def lift(self, x): return int(x)
    def pi(self, m): return self.p ** m

class TRing:
    # O = F_p[[t]] operationally: elements tuples of F_p coeffs (index = t-degree)
    name = "Fp[[t]]"
    def __init__(self, p): self.p = p; self.zero = (); self.one = (1 % p,)
    def _norm(self, L):
        while L and L[-1] == 0: L.pop()
        return tuple(L)
    def add(self, a, b):
        n = max(len(a), len(b))
        return self._norm([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % self.p
                           for i in range(n)])
    def neg(self, a): return tuple((-x) % self.p for x in a)
    def mul(self, a, b):
        if not a or not b: return ()
        L = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x == 0: continue
            for j, y in enumerate(b):
                L[i + j] = (L[i + j] + x * y) % self.p
        return self._norm(L)
    def iszero(self, a): return len(a) == 0
    def val(self, a):
        if not a: return None
        for i, x in enumerate(a):
            if x != 0: return i
        return None
    def res(self, a, d):
        assert (self.val(a) is None) or (self.val(a) >= d)
        return a[d] if d < len(a) else 0
    def lift(self, x): return (x % self.p,) if x % self.p else ()
    def pi(self, m): return tuple([0] * m + [1])

# ---------------- polynomials over O (lists, index = x-degree) ------------------------

def pnorm(R, f):
    while f and R.iszero(f[-1]): f.pop()
    return f

def padd(R, f, g):
    n = max(len(f), len(g))
    return pnorm(R, [R.add(f[i] if i < len(f) else R.zero, g[i] if i < len(g) else R.zero)
                     for i in range(n)])

def pmul(R, f, g):
    if not f or not g: return []
    L = [R.zero] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        if R.iszero(x): continue
        for j, y in enumerate(g):
            if R.iszero(y): continue
            L[i + j] = R.add(L[i + j], R.mul(x, y))
    return pnorm(R, L)

def pscal(R, c, f):
    return pnorm(R, [R.mul(c, x) for x in f])

def pdivmod(R, f, g):
    # g monic (leading coeff = R.one exactly); exact arithmetic in O
    assert g and g[-1] == R.one
    f = list(f); dg = len(g) - 1
    quo = [R.zero] * max(0, len(f) - dg)
    while len(f) - 1 >= dg and f:
        d = len(f) - 1; c = f[-1]
        quo[d - dg] = c
        for j in range(len(g)):
            f[d - dg + j] = R.add(f[d - dg + j], R.neg(R.mul(c, g[j])))
        f = pnorm(R, f)
    return pnorm(R, quo), f

def develop(R, f, Phi):
    # f = sum_j digits[j] * Phi^j, deg digits[j] < deg Phi
    digits = []; f = list(f)
    while f:
        f, rem = pdivmod(R, f, Phi)
        digits.append(rem)
    return digits

# ---------------- eq-(12-int) ----------------------------------------------------------

def eq12(beta, e, h):
    # unique (s,u): u*e + s*h = beta, 0 <= s < e
    if e == 1: return 0, beta
    s = (beta * pow(h % e, -1, e)) % e
    u = (beta - s * h) // e
    assert u * e + s * h == beta
    return s, u

def bezout_norm(e, h):
    # l*h + lp*e = 1, 0 <= l < e  (the NORMALIZED pair of the notes)
    if e == 1: return 0, 1
    l = pow(h % e, -1, e)
    lp = (1 - l * h) // e
    assert l * h + lp * e == 1 and 0 <= l < e
    return l, lp

# ---------------- the tower ------------------------------------------------------------

class BelowLine(Exception): pass

class Tower:
    def __init__(self, R, reads):
        # R: coefficient ring; reads: list of (e, h, psi) with psi = [c0..c_{g-1}]
        # (K_{i+1} = K_i[y]/(y^g + c_{g-1} y^{g-1} + ... + c0)); d0 = 1, Phi0 = x.
        self.R = R; self.reads = reads; self.N = len(reads)
        self.K = [FpField(R.p)]
        self.Phi = [[R.zero, R.one]]          # Phi0 = x
        self.gammaW = [None]                  # gammaW[i] defined for i = 1..N
        self.wPhi = [0]                       # wPhi[i] = w_i(Phi_i); w0(Phi0) = 0
        self.bez = []                         # (l_i, lp_i) for read i
        for i, (e, h, psi) in enumerate(reads):
            assert e >= 1 and h >= 1 and (e == 1 or (h % e) and pow(h % e, -1, e))
            g = len(psi)
            self.K.append(ExtField(self.K[i], psi))
            self.gammaW.append(e * self.wPhi[i] + h)
            self.wPhi.append(e * g * self.gammaW[i + 1])
            self.bez.append(bezout_norm(e, h))
        for i in range(self.N):               # build Phi[i+1] after gammaW known
            e, h, psi = reads[i]; g = len(psi)
            acc = []
            for k in range(g + 1):
                xi = self.K[i].one if k == g else psi[k]
                if self.K[i].iszero(xi): continue
                term = self.LIFT(i, (g - k) * self.gammaW[i + 1], xi)
                term = pmul(self.R, term, self.phipow(i, e * k))
                acc = padd(self.R, acc, term)
            self.Phi.append(acc)
            assert len(acc) - 1 == e * g * (len(self.Phi[i]) - 1), "deg Phi mismatch"
        self.E = 1
        for (e, h, psi) in reads: self.E *= e

    def phipow(self, i, k):
        key = (i, k)
        if not hasattr(self, '_phipowcache'): self._phipowcache = {}
        if key not in self._phipowcache:
            r = [self.R.one]
            for _ in range(k): r = pmul(self.R, r, self.Phi[i])
            self._phipowcache[key] = r
        return self._phipowcache[key]

    def LIFT(self, i, beta, xi):
        # lift xi in K[i] to a poly in O[x], deg < deg Phi[i], w_i = beta (xi != 0)
        if self.K[i].iszero(xi): return []
        if i == 0:
            assert beta >= 0, "LIFT0 at negative weight"
            return [self.R.mul(self.R.lift(xi), self.R.pi(beta))]
        e, h, _ = self.reads[i - 1]
        s, u = eq12(beta, e, h)
        beta0 = u - s * self.wPhi[i - 1]
        acc = []
        for m, xim in enumerate(xi):
            if self.K[i - 1].iszero(xim): continue
            term = self.LIFT(i - 1, beta0 - m * self.gammaW[i], xim)
            term = pmul(self.R, term, self.phipow(i - 1, s + m * e))
            acc = padd(self.R, acc, term)
        return acc

    def w(self, i, f):
        if not f: return None
        if i == 0:
            vs = [self.R.val(c) for c in f if not self.R.iszero(c)]
            return min(vs)
        e, h, _ = self.reads[i - 1]
        best = None
        for j, d in enumerate(develop(self.R, f, self.Phi[i - 1])):
            if not d: continue
            v = e * self.w(i - 1, d) + j * self.gammaW[i]
            if best is None or v < best: best = v
        return best

    def eps(self, i, beta):
        # eps_i(beta) in K[i], i >= 1; = 1 when e_{i-1} = 1
        e, h, _ = self.reads[i - 1]
        l, lp = self.bez[i - 1]
        s, u = eq12(beta, e, h)
        return self.K[i].ppow(self.K[i].gen, lp * s - l * u)

    def V(self, i, a, beta):
        # the level-i read of a at weight beta (element of K[i]); exact on-line tests
        if i == 0:
            if not a: return self.K[0].zero
            b = a[0]
            if self.R.iszero(b): return self.K[0].zero
            wv = self.R.val(b)
            if wv == beta: return self.R.res(b, beta)
            if wv > beta: return self.K[0].zero
            raise BelowLine(f"digit below line at level 0: w={wv} < beta={beta}")
        e, h, _ = self.reads[i - 1]
        digits = develop(self.R, a, self.Phi[i - 1])
        s, u = eq12(beta, e, h)
        beta0 = u - s * self.wPhi[i - 1]
        Ki = self.K[i]
        acc = Ki.zero
        m = 0; idx = s
        while idx < len(digits):
            d = digits[idx]
            if d:
                wd = self.w(i - 1, d)
                bm = beta0 - m * self.gammaW[i]
                if wd == bm:
                    inner = self.V(i - 1, d, bm)
                    if i - 1 >= 1:
                        inner = self.K[i - 1].mul(inner, self.eps(i - 1, bm))
                    acc = Ki.add(acc, Ki.mul(Ki.embedsub(inner), Ki.pow(Ki.gen, m)))
                elif wd < bm:
                    raise BelowLine(f"digit below line at level {i}: w={wd} < beta_m={bm}")
            m += 1; idx += e
        return acc

    def valN(self, f):
        gam = self.w(self.N, f)
        assert gam is not None
        return gam, self.V(self.N, f, gam)

    def anchor(self, gamma):
        # iterated eq12 split, top read down; returns (poly, diag)
        cur = gamma; slist = [None] * (self.N + 1); ulist = [None] * (self.N + 1)
        beta = [None] * (self.N + 1)   # beta[i] = the level-i weight entering read i-1
        beta[self.N] = gamma
        for i in range(self.N, 0, -1):
            e, h, _ = self.reads[i - 1]
            s, u = eq12(cur, e, h)
            slist[i] = s; ulist[i] = u
            cur = u - s * self.wPhi[i - 1]
            beta[i - 1] = cur
        u1 = cur   # = ulist[1] since wPhi[0] = 0
        poly = [self.R.pi(u1)] if u1 >= 0 else None
        if poly is not None:
            for i in range(1, self.N + 1):
                poly = pmul(self.R, poly, self.phipow(i - 1, slist[i]))
        return poly, dict(gamma=gamma, s=slist, u=ulist, beta=beta, u1=u1)

    def window_rep(self, r):
        gamma = r
        while True:
            poly, diag = self.anchor(gamma)
            if diag['u1'] >= 0: return gamma
            gamma += self.E

    def embed_letter(self, i):
        # z_i (K[i].gen) embedded into K[N]
        x = self.K[i].gen
        for j in range(i + 1, self.N + 1):
            x = self.K[j].embedsub(x)
        return x

    def topval(self, x, i):
        # embed K[i] element into K[N]
        for j in range(i + 1, self.N + 1):
            x = self.K[j].embedsub(x)
        return x

    def cocycle(self, g1, g2):
        A1, d1 = self.anchor(g1)
        A2, d2 = self.anchor(g2)
        A3, d3 = self.anchor(g1 + g2)
        assert d1['u1'] >= 0 and d2['u1'] >= 0, "arguments outside window"
        P = pmul(self.R, A1, A2)
        wP, vP = self.valN(P)
        wS, vS = self.valN(A3)
        KN = self.K[self.N]
        assert not KN.iszero(vS), "anchor val vanished (harness alarm)"
        if KN.iszero(vP):
            return None, dict(d1=d1, d2=d2, d3=d3, wP=wP, wS=wS, vP=vP, vS=vS)
        c = KN.mul(vP, KN.inv(vS))
        return c, dict(d1=d1, d2=d2, d3=d3, wP=wP, wS=wS, vP=vP, vS=vS)

# ---------------- monomial matching ----------------------------------------------------

class MonomialTable:
    # value -> exponent tuples (a_N, ..., a_1) for z_N^{a_N} ... z_1^{a_1}, a_i in [0, ord_i)
    # (a_N capped at min(ord_N, capN) -- top exponents are small carries)
    def __init__(self, T, capN=4):
        KN = T.K[T.N]
        self.T = T
        self.letters = [T.embed_letter(i) for i in range(1, T.N + 1)]  # z1..zN embedded
        self.orders = [mult_order(KN, z) for z in self.letters]
        self.capN = min(self.orders[-1], capN)
        ranges = [range(o) for o in self.orders[:-1]] + [range(self.capN)]
        self.table = {}
        for exps in itertools.product(*ranges):
            v = KN.one
            for z, a in zip(self.letters, exps):
                v = KN.mul(v, KN.pow(z, a))
            self.table.setdefault(v, []).append(tuple(exps))
    def match(self, v):
        return self.table.get(v, [])
    def balanced(self, exps):
        # balanced residue representative per letter (min |.|), top exponent as-is
        out = []
        for a, o in zip(exps[:-1], self.orders[:-1]):
            out.append(a - o if (o > 1 and a > o // 2) else a)
        out.append(exps[-1])
        return tuple(out)

# ---------------- psi choice (deterministic, printed; maximal root order preferred) ----

def choose_psi(K, g):
    # monic degree-g poly over K, irreducible, nonzero constant term, root of maximal
    # multiplicative order among candidates (early exit on primitive).  Deterministic scan.
    best = None; best_ord = -1
    elems = K.elements()
    if g == 1:
        for c in elems:
            if K.iszero(c): continue
            F = ExtField(K, [c])
            o = mult_order(F, F.gen)
            if o > best_ord: best, best_ord = [c], o
            if best_ord == F.q - 1: break
        return best
    assert g == 2
    for a in elems:
        for b in elems:
            if K.iszero(b): continue
            # irreducible over a field iff no root in K (degree 2)
            has_root = False
            for x in elems:
                v = K.add(K.mul(x, K.add(x, a)), b)   # x^2 + a x + b
                if K.iszero(v): has_root = True; break
            if has_root: continue
            F = ExtField(K, [b, a])
            o = mult_order(F, F.gen)
            if o > best_ord: best, best_ord = [b, a], o
            if o == F.q - 1: return best
    return best

def build_tower(ringname, p, espec):
    # espec: list of (e, h, g)
    R = ZRing(p) if ringname == "Zp" else TRing(p)
    reads = []
    K = FpField(p)
    Ks = [K]
    for (e, h, g) in espec:
        psi = choose_psi(Ks[-1], g)
        reads.append((e, h, psi))
        Ks.append(ExtField(Ks[-1], psi))
    return Tower(R, reads)

def fmt_elem(x):
    return json.dumps(x) if not isinstance(x, int) else str(x)

# ---------------- F0: the accepted order-2 law (ground truth) --------------------------

def accepted_law_order2(T, g1, g2):
    # zbar^{d2} * z1^{(s1(g1)+s1(g2)-s1(g1+g2)+l0*gamma2*d2)/e0}
    assert T.N == 2
    _, dA = T.anchor(g1); _, dB = T.anchor(g2); _, dC = T.anchor(g1 + g2)
    e1 = T.reads[1][0]; e0 = T.reads[0][0]
    d2 = (dA['s'][2] + dB['s'][2]) // e1
    l0, _ = T.bez[0]
    num = dA['s'][1] + dB['s'][1] - dC['s'][1] + l0 * T.gammaW[2] * d2
    assert num % e0 == 0, "accepted-law exponent not integral (harness bug?)"
    D = num // e0
    KN = T.K[2]
    v = KN.mul(KN.pow(KN.gen, d2), KN.ppow(T.embed_letter(1), D))
    return v, d2, D

def run_f0(rows, log):
    total = 0; bad = 0
    for name, ringname, p, espec in rows:
        T = build_tower(ringname, p, espec)
        E = T.E
        reps = [T.window_rep(r) for r in range(E)]
        rowbad = 0
        for ga in reps:
            for gb in reps:
                c, diag = T.cocycle(ga, gb)
                pred, d2, D = accepted_law_order2(T, ga, gb)
                total += 1
                if c != pred:
                    bad += 1; rowbad += 1
                    log(f"  F0 VIOLATION {name}: g={ga} g'={gb} measured={c} pred=zb^{d2} z1^{D}")
        # descent spot-check (COR-4): translate either representative by E
        dbad = 0
        for ga in reps[:min(4, E)]:
            for gb in reps[:min(4, E)]:
                c0, _ = T.cocycle(ga, gb)
                c1, _ = T.cocycle(ga + E, gb)
                c2, _ = T.cocycle(ga, gb + E)
                if not (c0 == c1 == c2): dbad += 1
        log(f"F0 {name}: ring={ringname} p={p} espec={espec} E2={E} pairs={E*E} "
            f"violations={rowbad} descent_spotbad={dbad}")
    return total, bad

# ---------------- level-3 measurement ---------------------------------------------------

def measure_tower(name, ringname, p, espec, log, jout):
    T = build_tower(ringname, p, espec)
    assert T.N == 3
    E = T.E
    MT = MonomialTable(T)
    o1, o2, o3 = MT.orders
    reps = [T.window_rep(r) for r in range(E)]
    psis = [T.reads[i][2] for i in range(3)]
    log(f"\n== TOWER {name}: ring={ringname} p={p} reads(e,h,g)={[(e,h,len(ps)) for (e,h,ps) in T.reads]}")
    log(f"   E3={E}  gamma1={T.gammaW[1]} gamma2={T.gammaW[2]} gamma3={T.gammaW[3]}  "
        f"w1Phi1={T.wPhi[1]} w2Phi2={T.wPhi[2]}  bez l={[b[0] for b in T.bez]} lp={[b[1] for b in T.bez]}")
    log(f"   psi0={psis[0]} psi1={psis[1]} psi2={psis[2]}")
    log(f"   letter orders: ord(z1)={o1} ord(z2)={o2} ord(z3)={o3} |K3|={T.K[3].q}")
    log(f"   window reps: {reps}")
    amb = set()
    recs = []
    hdr = (f"   {'g':>4} {'gp':>4} | {'s3':>2} {'s3p':>2} {'d3':>2} | {'s2':>3} {'s2p':>3} {'s2s':>3} "
           f"| {'s1':>3} {'s1p':>3} {'s1s':>3} | {'Sig1':>5} {'Sig2':>5} | measured (a3,a2,a1)")
    log(hdr)
    for ga in reps:
        for gb in reps:
            c, diag = T.cocycle(ga, gb)
            dA, dB, dC = diag['d1'], diag['d2'], diag['d3']
            e2 = T.reads[2][0]
            d3 = (dA['s'][3] + dB['s'][3]) // e2
            Sig2 = dC['beta'][2] - dA['beta'][2] - dB['beta'][2]   # realized level-2 shift
            Sig1 = dC['beta'][1] - dA['beta'][1] - dB['beta'][1]   # realized level-1 shift
            if c is None:
                log(f"   {ga:>4} {gb:>4} | VAL ZERO (vP=0) wP={diag['wP']} wS={diag['wS']}")
                recs.append(dict(g=ga, gp=gb, zero=True))
                continue
            matches = MT.match(c)
            mm = [MT.balanced(m) for m in matches]
            mm.sort(key=lambda t: (abs(t[-1]), abs(t[1]) if len(t) > 2 else 0, abs(t[0])))
            if len(matches) > 1: amb.add(len(matches))
            shown = mm[0] if mm else None
            wjump = diag['wP'] - (ga + gb)
            extra = f" wjump={wjump}" if wjump != 0 else ""
            nm = (f"({shown[2]},{shown[1]},{shown[0]})" if shown else "NO-MONOMIAL-MATCH")
            log(f"   {ga:>4} {gb:>4} | {dA['s'][3]:>2} {dB['s'][3]:>2} {d3:>2} | "
                f"{dA['s'][2]:>3} {dB['s'][2]:>3} {dC['s'][2]:>3} | "
                f"{dA['s'][1]:>3} {dB['s'][1]:>3} {dC['s'][1]:>3} | {Sig1:>5} {Sig2:>5} | "
                f"{nm}{' *AMB' + str(len(matches)) if len(matches) > 1 else ''}{extra}")
            recs.append(dict(g=ga, gp=gb, s3=[dA['s'][3], dB['s'][3], dC['s'][3]],
                             s2=[dA['s'][2], dB['s'][2], dC['s'][2]],
                             s1=[dA['s'][1], dB['s'][1], dC['s'][1]],
                             u1=[dA['u1'], dB['u1'], dC['u1']],
                             beta2=[dA['beta'][2], dB['beta'][2], dC['beta'][2]],
                             beta1=[dA['beta'][1], dB['beta'][1], dC['beta'][1]],
                             d3=d3, Sig1=Sig1, Sig2=Sig2, wP=diag['wP'], wS=diag['wS'],
                             value=c, matches=[list(m) for m in mm]))
    if amb:
        log(f"   [ambiguity: some values matched by >1 exponent tuple in the reduced box; "
            f"counts seen: {sorted(amb)} -- exponents reported mod letter-relation lattice]")
    jout.append(dict(name=name, ring=ringname, p=p,
                     espec=[list(x) for x in espec], psis=psis,
                     E3=E, gammaW=T.gammaW[1:], wPhi=T.wPhi[1:],
                     bez=[list(b) for b in T.bez],
                     letter_orders=[o1, o2, o3], reps=reps, pairs=recs))
    return T, recs

# ---------------- M5-CONJ: the composed-shift pattern conjecture (M5's own, derived ----
# from pattern-composing the S5 proof BEFORE reading the sealed prereg; value-based test)
#   c3 =? z3^{d3} * z2^{D2} * z1^{D1},  d3 = floor((s3+s3')/e2),
#   D2 = (s2+s2'-s2'' + l1*Sig2)/e1,  Sig2 = b2''-b2-b2'  (= d3*gamma3, identity),
#   D1 = (s1+s1'-s1'' + l0*Sig1)/e0,  Sig1 = b1''-b1-b1'  (the realized composed shift),
# where s_i are the anchor s-data of gamma, gamma', gamma+gamma' and b_i the anchor betas.

def m5conj_value(T, rec):
    e0 = T.reads[0][0]; e1 = T.reads[1][0]; e2 = T.reads[2][0]
    l0, _ = T.bez[0]; l1, _ = T.bez[1]
    d3 = (rec['s3'][0] + rec['s3'][1]) // e2
    n2 = rec['s2'][0] + rec['s2'][1] - rec['s2'][2] + l1 * rec['Sig2']
    n1 = rec['s1'][0] + rec['s1'][1] - rec['s1'][2] + l0 * rec['Sig1']
    if n2 % e1 != 0 or n1 % e0 != 0:
        return None, (d3, n2, e1, n1, e0)
    D2 = n2 // e1; D1 = n1 // e0
    KN = T.K[3]
    v = KN.pow(KN.gen, d3)
    v = KN.mul(v, KN.ppow(T.embed_letter(2), D2))
    v = KN.mul(v, KN.ppow(T.embed_letter(1), D1))
    return v, (d3, D2, D1)

def run_m5conj(towers_recs, log):
    log("")
    log("---- M5-CONJ (composed-shift pattern conjecture, value-based; NOT the seal) ----")
    tot = 0; bad = 0; nonint = 0
    for name, T, recs in towers_recs:
        rowbad = 0; rownon = 0
        for rec in recs:
            if rec.get('zero'): continue
            tot += 1
            pred, info = m5conj_value(T, rec)
            if pred is None:
                nonint += 1; rownon += 1
                log(f"  {name} g={rec['g']} gp={rec['gp']}: NONINTEGRAL exponent {info}")
            elif pred != rec['value']:
                bad += 1; rowbad += 1
                log(f"  {name} g={rec['g']} gp={rec['gp']}: MISMATCH pred(d3,D2,D1)={info} "
                    f"measured_matches={rec['matches'][:2]}")
        log(f"M5-CONJ {name}: mismatches={rowbad} nonintegral={rownon}")
    log(f"M5-CONJ TOTAL: {tot} pairs, {bad} value mismatches, {nonint} nonintegral -> "
        f"{'GREEN' if bad == 0 and nonint == 0 else 'RED'}")
    return bad, nonint

# ---------------- SEALED CANDIDATE (ITER-LAW-3), implemented from the prereg TEXT ------
# (ITERLAWR_PROBE_2026-08-08.md S1, read AFTER this harness was written and running;
#  the runner iterlawr_probe.py still not consulted at this point):
#   d3 = floor((s3+s3')/e2);  D2 = (s2+s2'-s2'' + l1*gamma3*d3)/e1;
#   Sig = D2*gamma2 + d3*gamma3*(l1p - l1*w1Phi1);
#   D1 = (s1+s1'-s1'' + l0*Sig)/e0;   c3 = z3^d3 * z2^D2 * z1^D1.
# Also checks the prereg's INNER-SHIFT-3 claim Sig == realized Sig1 per pair.

def sealed_candidate_value(T, rec):
    e0 = T.reads[0][0]; e1 = T.reads[1][0]; e2 = T.reads[2][0]
    l0, _ = T.bez[0]; l1, l1p = T.bez[1]
    d3 = (rec['s3'][0] + rec['s3'][1]) // e2
    n2 = rec['s2'][0] + rec['s2'][1] - rec['s2'][2] + l1 * T.gammaW[3] * d3
    if n2 % e1 != 0: return None, None, ('D2 nonintegral', n2, e1)
    D2 = n2 // e1
    Sig = D2 * T.gammaW[2] + d3 * T.gammaW[3] * (l1p - l1 * T.wPhi[1])
    n1 = rec['s1'][0] + rec['s1'][1] - rec['s1'][2] + l0 * Sig
    if n1 % e0 != 0: return None, None, ('D1 nonintegral', n1, e0)
    D1 = n1 // e0
    KN = T.K[3]
    v = KN.pow(KN.gen, d3)
    v = KN.mul(v, KN.ppow(T.embed_letter(2), D2))
    v = KN.mul(v, KN.ppow(T.embed_letter(1), D1))
    return v, Sig, (d3, D2, D1)

def run_sealed_candidate(towers_recs, log):
    log("")
    log("---- SEALED CANDIDATE (ITER-LAW-3, from prereg S1 text) on M5's measurements ----")
    tot = 0; bad = 0; nonint = 0; sigbad = 0
    for name, T, recs in towers_recs:
        rowbad = rownon = rowsig = 0
        for rec in recs:
            if rec.get('zero'): continue
            tot += 1
            pred, Sig, info = sealed_candidate_value(T, rec)
            if pred is None:
                nonint += 1; rownon += 1
                log(f"  {name} g={rec['g']} gp={rec['gp']}: SEALED-CAND {info}")
                continue
            if Sig != rec['Sig1']:
                sigbad += 1; rowsig += 1
                log(f"  {name} g={rec['g']} gp={rec['gp']}: INNER-SHIFT-3 FAILS "
                    f"Sig_sealed={Sig} != realized {rec['Sig1']}")
            if pred != rec['value']:
                bad += 1; rowbad += 1
                log(f"  {name} g={rec['g']} gp={rec['gp']}: SEALED-CAND MISMATCH "
                    f"(d3,D2,D1)={info} measured_matches={rec['matches'][:2]}")
        log(f"SEALED {name}: mismatches={rowbad} nonintegral={rownon} shift-id-fails={rowsig}")
    log(f"SEALED TOTAL: {tot} pairs, {bad} value mismatches, {nonint} nonintegral, "
        f"{sigbad} inner-shift-identity failures -> "
        f"{'GREEN' if bad == nonint == sigbad == 0 else 'RED'}")
    return bad, nonint, sigbad

# ---------------- main ------------------------------------------------------------------

F0_ROWS = [
    ("F0a", "Zp", 3, [(2, 1, 2), (2, 1, 2)]),
    ("F0b", "Fp[[t]]", 3, [(2, 1, 1), (2, 1, 2)]),   # g0=1: Case II live
    ("F0c", "Zp", 2, [(3, 1, 2), (2, 1, 2)]),
    ("F0d", "Zp", 3, [(1, 1, 2), (3, 2, 2)]),        # e0=1 degeneration
    ("F0e", "Fp[[t]]", 2, [(2, 1, 2), (1, 1, 2)]),   # e1=1 degeneration
    ("F0f", "Zp", 3, [(3, 2, 2), (2, 3, 2)]),        # larger h's
]

L3_ROWS = [
    ("L3A", "Zp", 3, [(2, 1, 2), (1, 1, 2), (2, 1, 2)]),   # E3=4 stacked e0, e2 active
    ("L3B", "Zp", 3, [(1, 1, 2), (2, 1, 2), (2, 3, 2)]),   # E3=4, h2=3
    ("L3C", "Zp", 2, [(2, 1, 2), (2, 1, 2), (2, 1, 2)]),   # E3=8 full stack, p=2
    ("L3D", "Zp", 3, [(2, 1, 2), (2, 1, 2), (2, 1, 2)]),   # E3=8 full stack, p=3
    ("L3E", "Fp[[t]]", 2, [(1, 1, 2), (3, 1, 2), (2, 1, 2)]),  # E3=6, e1=3
    ("L3F", "Fp[[t]]", 3, [(3, 2, 2), (1, 1, 2), (2, 1, 2)]),  # E3=6, stacked e0=3 h0=2
    ("L3G", "Zp", 3, [(2, 1, 2), (2, 1, 2), (1, 1, 2)]),   # E3=4, e2=1 control
]

def main():
    outpath = "level3_xcheck_output.txt"
    jsonpath = "level3_xcheck_results.json"
    lines = []
    def log(s):
        print(s); lines.append(s)
    log("level3_xcheck.py -- M5 cross-implementation control (post-seal diagnostic, NON-PREREG)")
    log("harness written from ITERLAW_2026-08-08.md S0/S5 + DITER_RESTATE_2026-08-08.md S2 alone")
    log("")
    log("---- F0: 2-level fidelity against the ACCEPTED order-2 law (ground truth) ----")
    tot, bad = run_f0(F0_ROWS, log)
    log(f"F0 TOTAL: {tot} pairs, {bad} violations -> {'GREEN' if bad == 0 else 'RED (fix THIS harness)'}")
    jout = []
    log("")
    log("---- level-3 towers: exhaustive window pairs, measured cocycle monomials ----")
    log("(columns: gamma, gamma'; s3-data + top carry d3; s2 of the three anchors; s1 of the")
    log(" three anchors; realized inner shifts Sig1 = b1''-b1-b1', Sig2 = b2''-b2-b2';")
    log(" measured monomial c3 = z3^a3 z2^a2 z1^a1 shown as (a3,a2,a1), balanced residues)")
    towers_recs = []
    for row in L3_ROWS:
        T, recs = measure_tower(*row, log, jout)
        towers_recs.append((row[0], T, recs))
    run_m5conj(towers_recs, log)
    run_sealed_candidate(towers_recs, log)
    with open(jsonpath, "w") as f:
        json.dump(jout, f, indent=1)
    with open(outpath, "w") as f:
        f.write("\n".join(lines) + "\n")
    log(f"\nwrote {jsonpath} and {outpath}")
    return 0 if bad == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
