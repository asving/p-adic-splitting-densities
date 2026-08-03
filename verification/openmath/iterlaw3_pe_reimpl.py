#!/usr/bin/env python3
"""ITERLAW3-PE from-note reimplementation (F2c genre; verifier-owned).

Implements, FROM lean/notes/openmath/ITERLAW3_PROOF_2026-08-08.md ALONE (before
opening iterlaw3_proof_diag.py):
  - the 3-read standard-lift harness class (note S0.1), the calculus (S0.2),
    anchors/window/cocycle (S0.3), and the THEOREM display (S0.4);
  - the note's NEW intermediate identities: L2-(3a)/(3b) + D2-INT/D1-INT (S2),
    WINDOW (S2), WELL-DEF invariants (S4.0), the DEV-1 reduction invariants (S4.1),
    L6-(3) (S4.2), CASE-SPLIT with INDEPENDENTLY implemented predicates incl. the
    DCX locus (S4.3/S4.7), the per-case digit shapes S4.4/S4.5/S4.6, W-MULT-(3),
    the theorem S5, degenerations S6.3.
Checks: theorem on every non-DCX pair; per-case intermediate identities within their
case; DCX locus == the note's predicate (measure per tower; empty at e0<=2); the
theorem's status ON DCX pairs reported honestly as instance data for the open lemma
(W-MULT-3-DCX); e2=1 degeneration reproduces the ACCEPTED order-2 law via an own
level-2 cocycle; 6 field-visible mutation controls (visibility verified BEFORE
violation counting); 20k-draw symbolic integer layer.

Verifier: Fable, pass ITERLAW3-PE. Seed 20260803 (fresh to the genre). Fresh towers:
rings Z5/F5[[t]] (new to the ITERLAW genre), d0=2, g2=2, pi-perturbed Phi0 (in-class:
only monic + w0=0 + irreducible reduction are pinned by S0.1).
"""
import sys, json, itertools, random
from math import gcd

INF = 10**9  # valuation of 0 (larger than anything reachable here)

# ---------------- integer kernel: eq-(12-int) + normalized Bezout (S0.2) ----------------
def eq12(beta, e, h):
    if e == 1:
        return 0, beta
    l = pow(h, -1, e)
    s = (l * beta) % e
    u = (beta - s * h) // e
    assert u * e + s * h == beta
    return s, u

def bezout(e, h):
    if e == 1:
        return 0, 1
    l = pow(h, -1, e); lp = (1 - l * h) // e
    assert l * h + lp * e == 1 and 0 <= l < e
    return l, lp

# ---------------- finite fields: prime field + generic extension tower ----------------
class PrimeField:
    def __init__(self, p): self.p = p
    def zero(self): return 0
    def one(self): return 1
    def is_zero(self, a): return a == 0
    def add(self, a, b): return (a + b) % self.p
    def sub(self, a, b): return (a - b) % self.p
    def neg(self, a): return (-a) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def inv(self, a):
        assert a % self.p != 0
        return pow(a, -1, self.p)
    def elements(self): return list(range(self.p))
    def size(self): return self.p

def ptrim(F, a):
    a = list(a)
    while a and F.is_zero(a[-1]): a.pop()
    return a
def padd(F, a, b):
    n = max(len(a), len(b)); z = F.zero()
    return ptrim(F, [F.add(a[i] if i < len(a) else z,
                           b[i] if i < len(b) else z) for i in range(n)])
def pneg(F, a): return [F.neg(x) for x in a]
def psub(F, a, b): return padd(F, a, pneg(F, b))
def pmul(F, a, b):
    if not a or not b: return []
    z = F.zero(); out = [z] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if F.is_zero(x): continue
        for j, y in enumerate(b):
            out[i + j] = F.add(out[i + j], F.mul(x, y))
    return ptrim(F, out)
def pdivmod(F, a, b):
    a = ptrim(F, a); b = ptrim(F, b); assert b
    binv = F.inv(b[-1]); q = [F.zero()] * max(0, len(a) - len(b) + 1)
    r = list(a)
    while len(r) >= len(b):
        c = F.mul(r[-1], binv); k = len(r) - len(b)
        q[k] = c
        r = psub(F, r, pmul(F, [F.zero()] * k + [c], b))
    return ptrim(F, q), r
def pextgcd(F, a, b):
    r0, s0 = ptrim(F, a), [F.one()]
    r1, s1 = ptrim(F, b), []
    while r1:
        q, r = pdivmod(F, r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, psub(F, s0, pmul(F, q, s1))
    return r0, s0
def peval(F, poly, x):
    acc = F.zero()
    for c in reversed(ptrim(F, poly)):
        acc = F.add(F.mul(acc, x), c)
    return acc
def assert_irr(F, m, tag):
    m = ptrim(F, m); d = len(m) - 1
    assert d >= 1, tag
    if d == 1: return
    assert d <= 3, tag + ': irreducibility check only implemented for deg<=3'
    for c in F.elements():
        assert not F.is_zero(peval(F, m, c)), tag + ': reducible (root found)'

class ExtField:
    def __init__(self, base, mod):
        self.base = base
        self.mod = ptrim(base, mod)
        assert len(self.mod) >= 2 and self.mod[-1] == base.one(), 'mod must be monic'
        self.deg = len(self.mod) - 1
        self._mulc = {}; self._invc = {}; self._embc = {}
        self._z = None; self._o = None
    def _norm(self, coeffs):
        r = pdivmod(self.base, ptrim(self.base, list(coeffs)), self.mod)[1]
        r = r + [self.base.zero()] * (self.deg - len(r))
        return tuple(r)
    def zero(self):
        if self._z is None: self._z = tuple([self.base.zero()] * self.deg)
        return self._z
    def one(self):
        if self._o is None: self._o = self._norm([self.base.one()])
        return self._o
    def gen(self): return self._norm([self.base.zero(), self.base.one()])
    def embed(self, c):
        r = self._embc.get(c)
        if r is None: r = self._embc[c] = self._norm([c])
        return r
    def is_zero(self, a): return all(self.base.is_zero(x) for x in a)
    def add(self, a, b): return tuple(self.base.add(x, y) for x, y in zip(a, b))
    def sub(self, a, b): return tuple(self.base.sub(x, y) for x, y in zip(a, b))
    def neg(self, a): return tuple(self.base.neg(x) for x in a)
    def mul(self, a, b):
        r = self._mulc.get((a, b))
        if r is None:
            r = self._norm(pmul(self.base, list(a), list(b)))
            self._mulc[(a, b)] = r; self._mulc[(b, a)] = r
        return r
    def inv(self, a):
        r = self._invc.get(a)
        if r is None:
            assert not self.is_zero(a)
            g, s = pextgcd(self.base, list(a), self.mod)
            assert len(g) == 1, 'mod not irreducible?'
            gi = self.base.inv(g[0])
            r = self._norm([self.base.mul(x, gi) for x in s])
            assert r and self.mul(r, a) == self.one()
            self._invc[a] = r
        return r
    def pow(self, a, n):
        if n < 0: a, n = self.inv(a), -n
        out, b = self.one(), a
        while n:
            if n & 1: out = self.mul(out, b)
            b = self.mul(b, b); n >>= 1
        return out
    def elements(self):
        return [self._norm(list(t)) for t in
                itertools.product(self.base.elements(), repeat=self.deg)]
    def size(self): return self.base.size() ** self.deg

# ---------------- the DVR coefficient rings O (exact; no precision) ----------------
class OZp:
    """O = Z (viewed inside Z_p), pi = p. Elements: python ints. Exact."""
    def __init__(self, p): self.p = p
    def name(self): return 'Z%d' % self.p
    def zero(self): return 0
    def one(self): return 1
    def is_zero(self, a): return a == 0
    def add(self, a, b): return a + b
    def sub(self, a, b): return a - b
    def neg(self, a): return -a
    def mul(self, a, b): return a * b
    def val(self, a):
        if a == 0: return INF
        v = 0
        while a % self.p == 0: a //= self.p; v += 1
        return v
    def pipow(self, u): assert u >= 0; return self.p ** u
    def divpow(self, a, k):
        q, r = divmod(a, self.p ** k); assert r == 0; return q
    def residue(self, a): return a % self.p
    def liftc(self, c): return c % self.p

class OFpt:
    """O = F_p[t] (inside F_p[[t]]), pi = t. Elements: canonical tuples of ints."""
    def __init__(self, p): self.p = p
    def name(self): return 'F%d[[t]]' % self.p
    def _mk(self, coeffs):
        a = [c % self.p for c in coeffs]
        while a and a[-1] == 0: a.pop()
        return tuple(a)
    def zero(self): return ()
    def one(self): return (1,)
    def is_zero(self, a): return a == ()
    def add(self, a, b):
        n = max(len(a), len(b))
        return self._mk([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                         for i in range(n)])
    def sub(self, a, b): return self.add(a, self.neg(b))
    def neg(self, a): return self._mk([-c for c in a])
    def mul(self, a, b):
        if not a or not b: return ()
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): out[i + j] += x * y
        return self._mk(out)
    def val(self, a):
        if a == (): return INF
        for i, c in enumerate(a):
            if c % self.p: return i
        raise AssertionError
    def pipow(self, u): assert u >= 0; return self._mk([0] * u + [1])
    def divpow(self, a, k):
        if a == (): return ()
        assert all(c % self.p == 0 for c in a[:k])
        return self._mk(list(a[k:]))
    def residue(self, a): return a[0] % self.p if a else 0
    def liftc(self, c): return self._mk([c])

# ---------------- O[x] polynomial helpers ----------------
def x_trim(O, f):
    f = list(f)
    while f and O.is_zero(f[-1]): f.pop()
    return f
def x_deg(O, f):
    f = x_trim(O, f); return len(f) - 1  # -1 for 0
def x_add(O, f, g):
    n = max(len(f), len(g)); z = O.zero()
    return x_trim(O, [O.add(f[i] if i < len(f) else z, g[i] if i < len(g) else z)
                      for i in range(n)])
def x_neg(O, f): return [O.neg(c) for c in f]
def x_sub(O, f, g): return x_add(O, f, x_neg(O, g))
def x_mul(O, f, g):
    f = x_trim(O, f); g = x_trim(O, g)
    if not f or not g: return []
    z = O.zero(); out = [z] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if O.is_zero(a): continue
        for j, b in enumerate(g): out[i + j] = O.add(out[i + j], O.mul(a, b))
    return x_trim(O, out)
def x_scal(O, f, c): return x_trim(O, [O.mul(c, a) for a in f])
def x_pow(O, f, n):
    out = [O.one()]
    for _ in range(n): out = x_mul(O, out, f)
    return out
def x_divmod(O, f, g):
    """g monic. Exact in O[x] (division algorithm; the only base fact consumed)."""
    f = x_trim(O, list(f)); g = x_trim(O, g)
    assert g and g[-1] == O.one()
    q = [O.zero()] * max(0, len(f) - len(g) + 1)
    r = f
    while len(r) >= len(g):
        c = r[-1]; k = len(r) - len(g)
        q[k] = c
        r = x_trim(O, x_sub(O, r, x_scal(O, [O.zero()] * k + list(g), c)))
    return x_trim(O, q), r
def x_eq(O, f, g): return x_trim(O, f) == x_trim(O, g)
def x_content(O, f):
    """w0 extended coefficientwise (Gauss content), S0.1."""
    vals = [O.val(c) for c in f if not O.is_zero(c)]
    return min(vals) if vals else INF

# ---------------- the 3-read standard-lift tower (note S0.1/S0.2) ----------------
class Tower3:
    def __init__(self, name, O, phibar, r0, r1, r2, pert=None):
        self.name = name; self.O = O; p = O.p
        # memo caches (pure functions of canonical content; results used read-only)
        self._c = dict(dev0={}, dev1={}, dev2={}, w1={}, w2={}, R1={},
                       eps1={}, eps2={}, cont={})
        Fp = PrimeField(p)
        assert phibar[-1] % p == 1
        assert_irr(Fp, phibar, name + ':phibar')
        self.K0 = ExtField(Fp, phibar); self.d0 = self.K0.deg
        Phi0 = [O.liftc(c) for c in phibar]
        if pert:  # Phi0 = lift(phibar) + pi*pert : still monic, w0=0, same reduction (in-class)
            assert len(pert) <= self.d0
            for i, c in enumerate(pert):
                Phi0[i] = O.add(Phi0[i], O.mul(O.pipow(1), O.liftc(c)))
        self.Phi0 = x_trim(O, Phi0)
        assert x_deg(O, self.Phi0) == self.d0 and self.Phi0[-1] == O.one()
        assert x_content(O, self.Phi0) == 0
        # read 0
        e0, h0, psi0_fn = r0
        self.e0, self.h0 = e0, h0
        assert e0 >= 1 and h0 >= 1 and gcd(e0, h0) == 1
        psi0 = [self.K0._norm(list(c)) for c in psi0_fn(self.K0)]
        assert psi0[-1] == self.K0.one() and not self.K0.is_zero(psi0[0])
        assert_irr(self.K0, psi0, name + ':psi0')
        self.psi0 = psi0; self.g0 = len(psi0) - 1
        self.K1 = ExtField(self.K0, psi0); self.z1 = self.K1.gen()
        self.l0, self.l0p = bezout(e0, h0)
        self.w1Phi1 = e0 * self.g0 * h0
        # Phi1 = the STANDARD LIFT (S0.1)
        Phi1 = []
        for k in range(self.g0 + 1):
            if self.K0.is_zero(psi0[k]): continue
            term = x_scal(O, x_pow(O, self.Phi0, e0 * k), O.pipow((self.g0 - k) * h0))
            Phi1 = x_add(O, Phi1, x_mul(O, self.lift0(psi0[k]), term))
        self.Phi1 = Phi1
        assert x_deg(O, Phi1) == e0 * self.g0 * self.d0 and Phi1[-1] == O.one()
        # read 1
        e1, h1, psi1_fn = r1
        self.e1, self.h1 = e1, h1
        assert e1 >= 1 and h1 >= 1 and gcd(e1, h1) == 1
        self.gamma2 = e1 * self.w1Phi1 + h1
        self.l1, self.l1p = bezout(e1, h1)
        psi1 = [self.K1._norm(list(c)) for c in psi1_fn(self.K1)]
        assert psi1[-1] == self.K1.one() and not self.K1.is_zero(psi1[0])
        assert_irr(self.K1, psi1, name + ':psi1')
        self.psi1 = psi1; self.g1 = len(psi1) - 1
        self.K2 = ExtField(self.K1, psi1); self.z2 = self.K2.gen()
        # Phi2 = the CANONICAL eps1-corrected lift (S0.1; C_k via realize1, S4.0)
        self.welldef_bad = []
        Phi2 = x_pow(O, self.Phi1, e1 * self.g1)  # C_{g1} = 1
        C0 = None
        for k in range(self.g1):
            if self.K1.is_zero(psi1[k]): continue
            gp = (self.g1 - k) * self.gamma2
            tau_k = self.K1.mul(self.K1.inv(self.eps1(gp)), psi1[k])
            Ck = self.realize1(tau_k, gp)
            # WELL-DEF (i) invariants (note S4.0): deg, line, w1, read
            if not (x_deg(O, Ck) < x_deg(O, self.Phi1)): self.welldef_bad.append('deg C_%d' % k)
            if self.w1(Ck) != gp: self.welldef_bad.append('w1 C_%d' % k)
            for j, b in enumerate(self.dev0(Ck)):
                if b and e0 * x_content(O, b) + j * h0 != gp:
                    self.welldef_bad.append('line C_%d' % k)
            if self.R1(Ck, gp) != tau_k: self.welldef_bad.append('read C_%d' % k)
            if k == 0: C0 = Ck
            Phi2 = x_add(O, Phi2, x_mul(O, Ck, x_pow(O, self.Phi1, e1 * k)))
        self.Phi2 = Phi2
        self.Chat = None; self.tau = None; self.c1 = None
        if self.g1 == 1:
            self.Chat = C0  # WELL-DEF (ii): Phi2 = Phi1^{e1} + Chat
            assert x_eq(O, Phi2, x_add(O, x_pow(O, self.Phi1, e1), C0))
            self.c1 = psi1[0]
            self.tau = self.K1.mul(self.K1.inv(self.eps1(self.gamma2)), self.c1)
        self.w2Phi2 = e1 * self.g1 * self.gamma2
        # read 2
        e2, h2, psi2_fn = r2
        self.e2, self.h2 = e2, h2
        assert e2 >= 1 and h2 >= 1 and gcd(e2, h2) == 1
        self.gamma3 = e2 * self.w2Phi2 + h2
        self.l2, self.l2p = bezout(e2, h2)
        psi2 = [self.K2._norm(list(c)) for c in psi2_fn(self.K2)]
        assert psi2[-1] == self.K2.one() and not self.K2.is_zero(psi2[0])
        assert_irr(self.K2, psi2, name + ':psi2')
        self.psi2 = psi2; self.g2 = len(psi2) - 1
        self.K3 = ExtField(self.K2, psi2); self.zbar = self.K3.gen()
        self.E3 = e0 * e1 * e2
        self.s_gamma2 = eq12(self.gamma2, e0, h0)[0]
        # sanity: the defined weights are attained
        assert self.w1(self.Phi1) == self.w1Phi1
        assert self.w2(self.Phi2) == self.w2Phi2

    def _key(self, f):
        return tuple(x_trim(self.O, f))

    # ---- lifts / residues ----
    def lift0(self, t):  # K0 -> O[x], coefficientwise degree-<d0 lift
        return x_trim(self.O, [self.O.liftc(c) for c in t])
    def res(self, b, delta):  # {deg<d0, w0>=delta} -> K0 : class of b/pi^delta (S0.1)
        O = self.O
        return self.K0._norm([PrimeField(O.p).add(0, O.residue(O.divpow(c, delta)))
                              for c in b])
    def realize1(self, tau, gp):  # note S4.0(i) display of realize1
        s, u = eq12(gp, self.e0, self.h0)
        if u < (self.g0 - 1) * self.h0:
            self.welldef_bad.append('realize1 domain @gp=%d' % gp)
        C = []
        for m in range(self.g0):
            if self.K0.is_zero(tau[m]): continue
            term = x_scal(self.O, x_pow(self.O, self.Phi0, s + m * self.e0),
                          self.O.pipow(u - m * self.h0))
            C = x_add(self.O, C, x_mul(self.O, self.lift0(tau[m]), term))
        return C

    # ---- developments and weights (S0.2) ----
    def dev(self, f, Phi):
        f = x_trim(self.O, list(f)); out = []
        while f:
            q, r = x_divmod(self.O, f, Phi)
            out.append(r); f = q
        return out
    def _devc(self, f, Phi, tag):
        k = self._key(f); c = self._c[tag]
        if k not in c: c[k] = self.dev(list(k), Phi)
        return c[k]
    def dev0(self, f): return self._devc(f, self.Phi0, 'dev0')
    def dev1(self, f): return self._devc(f, self.Phi1, 'dev1')
    def dev2(self, f): return self._devc(f, self.Phi2, 'dev2')
    def cont(self, b):
        k = self._key(b); c = self._c['cont']
        if k not in c: c[k] = x_content(self.O, list(k))
        return c[k]
    def w1(self, f):
        k = self._key(f); c = self._c['w1']
        if k not in c:
            best = INF
            for j, b in enumerate(self.dev0(f)):
                if b: best = min(best, self.e0 * self.cont(b) + j * self.h0)
            c[k] = best
        return c[k]
    def w2(self, f):
        k = self._key(f); c = self._c['w2']
        if k not in c:
            best = INF
            for j, a in enumerate(self.dev1(f)):
                if a: best = min(best, self.e1 * self.w1(a) + j * self.gamma2)
            c[k] = best
        return c[k]
    def w3(self, f):
        best = INF
        for j, A in enumerate(self.dev2(f)):
            if A: best = min(best, self.e2 * self.w2(A) + j * self.gamma3)
        return best

    # ---- epsilons (reading C) ----
    def eps1(self, beta):
        c = self._c['eps1']
        if beta not in c:
            s, u = eq12(beta, self.e0, self.h0)
            c[beta] = self.K1.pow(self.z1, self.l0p * s - self.l0 * u)
        return c[beta]
    def eps2(self, beta):
        c = self._c['eps2']
        if beta not in c:
            s, u = eq12(beta, self.e1, self.h1)
            c[beta] = self.K2.pow(self.z2, self.l1p * s - self.l1 * u)
        return c[beta]

    # ---- reads (S0.2) ----
    def R1(self, a, beta):
        """R_{1,beta}(a)(z1); requires w1(a) >= beta (asserted)."""
        ck = (self._key(a), beta); cc = self._c['R1']
        if ck in cc: return cc[ck]
        assert self.w1(a) >= beta
        s, u = eq12(beta, self.e0, self.h0)
        ds = self.dev0(a); acc = self.K1.zero()
        idx, m = s, 0
        while idx < len(ds):
            b = ds[idx]
            if b:
                req = u - m * self.h0
                c = self.cont(b)
                assert c >= req, 'digit strictly below the line'
                if c == req:
                    acc = self.K1.add(acc, self.K1.mul(self.K1.embed(self.res(b, req)),
                                                       self.K1.pow(self.z1, m)))
            idx += self.e0; m += 1
        cc[ck] = acc
        return acc
    def R2v(self, f):
        """(R2v(f), w2(f), read list [(slot j, C_j != 0)])."""
        gamma = self.w2(f)
        s2g, _ = eq12(gamma, self.e1, self.h1)
        ds = self.dev1(f)
        acc = self.K2.zero(); reads = []
        idx, j = s2g, 0
        while idx < len(ds):
            a = ds[idx]
            if a:
                num = gamma - idx * self.gamma2
                assert num % self.e1 == 0
                gj = num // self.e1
                wa = self.w1(a)
                assert wa >= gj
                if wa == gj:
                    Cj = self.K1.mul(self.eps1(gj), self.R1(a, gj))
                    if not self.K1.is_zero(Cj): reads.append((j, Cj))
                    acc = self.K2.add(acc, self.K2.mul(self.K2.embed(Cj),
                                                       self.K2.pow(self.z2, j)))
            idx += self.e1; j += 1
        return acc, gamma, reads
    def val3(self, f):
        """(val3(f), w3(f), read list [(slot j, C_j != 0 in K2)], Phi2-dev)."""
        ds = self.dev2(f)
        gamma = INF
        for j, A in enumerate(ds):
            if A: gamma = min(gamma, self.e2 * self.w2(A) + j * self.gamma3)
        assert gamma < INF
        s3g, _ = eq12(gamma, self.e2, self.h2)
        acc = self.K3.zero(); reads = []
        idx, j = s3g, 0
        while idx < len(ds):
            A = ds[idx]
            if A:
                num = gamma - idx * self.gamma3
                assert num % self.e2 == 0
                gj = num // self.e2
                wA = self.w2(A)
                assert wA >= gj
                if wA == gj:
                    v2, _, _ = self.R2v(A)
                    Cj = self.K2.mul(self.eps2(gj), v2)
                    if not self.K2.is_zero(Cj): reads.append((j, Cj))
                    acc = self.K3.add(acc, self.K3.mul(self.K3.embed(Cj),
                                                       self.K3.pow(self.zbar, j)))
            idx += self.e2; j += 1
        return acc, gamma, reads, ds

    # ---- anchors (S0.3) ----
    def split(self, gamma):
        s3, u3 = eq12(gamma, self.e2, self.h2)
        b2 = u3 - s3 * self.w2Phi2
        s2, u2 = eq12(b2, self.e1, self.h1)
        b1 = u2 - s2 * self.w1Phi1
        s1, u1 = eq12(b1, self.e0, self.h0)
        return dict(s3=s3, u3=u3, b2=b2, s2=s2, u2=u2, b1=b1, s1=s1, u1=u1)
    def anchor_poly(self, d):
        O = self.O
        f = [O.pipow(d['u1'])]
        f = x_mul(O, f, x_pow(O, self.Phi0, d['s1']))
        f = x_mul(O, f, x_pow(O, self.Phi1, d['s2']))
        f = x_mul(O, f, x_pow(O, self.Phi2, d['s3']))
        return f
    # embeddings K1 -> K2 -> K3
    def e12(self, a): return self.K2.embed(a)
    def e23(self, a): return self.K3.embed(a)
    def K3val(self, d3, mid_K2, inner_K1):
        """zbar^d3 * emb(mid * emb(inner)) in K3."""
        v = self.K2.mul(mid_K2, self.e12(inner_K1))
        return self.K3.mul(self.K3.pow(self.zbar, d3), self.e23(v))

# ---------------- checking infrastructure ----------------
VIOL = []
class Ctr:
    def __init__(self): self.fam = {}
    def ck(self, tag, cond, ctx=None):
        f = self.fam.setdefault(tag, [0, 0]); f[0] += 1
        if not cond:
            f[1] += 1
            if len(VIOL) < 60: VIOL.append((tag, ctx))
    def total(self): return (sum(v[0] for v in self.fam.values()),
                             sum(v[1] for v in self.fam.values()))

# ---------------- case trichotomy + DCX (verifier-owned predicates, S4.3/S4.7) ----------------
def case_of(T, d, dP, C, ctx):
    S1 = d['s1'] + dP['s1']; S2 = d['s2'] + dP['s2']
    d1 = S1 // T.e0
    innerI = S1 < T.e0 * T.g0
    innerII = (T.g0 == 1 and d1 == 1)
    C.ck('INNER-DICHOT', innerI != innerII, ctx)
    if T.g1 >= 2: case = 'I'
    elif innerI: case = 'II-1' if S2 >= T.e1 else 'I'
    else: case = 'II-2' if S2 >= T.e1 else ('II-3' if S2 == T.e1 - 1 else 'I')
    isdcx = (T.g0 == 1 and T.g1 == 1 and d1 == 1 and d['s2'] == T.e1 - 1
             and dP['s2'] == T.e1 - 1 and S1 + T.s_gamma2 >= 2 * T.e0)
    return case, isdcx

def dev_matches(T, devP, spec):
    top = max(spec.keys()) if spec else -1
    for j in range(max(len(devP), top + 1)):
        want = spec.get(j, [])
        got = devP[j] if j < len(devP) else []
        if not x_eq(T.O, want, got): return False
    return True

# ---------------- per-case intermediate-identity checks (S4.4/S4.5/S4.6) ----------------
def case_checks(T, case, S1, S2, S3, U, d1, d2, d3, B1, B2, A, devP, C, ctx):
    O, K1, K2 = T.O, T.K1, T.K2
    innerK = K1.mul(K1.pow(T.z1, d1), T.eps1(B1))
    predE0read = K2.mul(K2.pow(T.z2, d2), K2.embed(innerK))
    if case == 'I':
        C.ck('I-dev', dev_matches(T, devP, {S3: A}), ctx)
        C.ck('I-w2A', T.w2(A) == B2, ctx)
        C.ck('I-R2vA', T.R2v(A)[0] == predE0read, ctx)
        return
    # all Case II strata have g1 = 1: WELL-DEF(ii) objects exist
    bstar = B1 + T.gamma2
    sB1 = eq12(B1, T.e0, T.h0)[0]
    epr = (sB1 + T.s_gamma2) // T.e0   # eps' of S4.5/S4.6
    if case == 'II-1':
        k = S2 - T.e1
        a = x_scal(O, x_pow(O, T.Phi0, S1), O.pipow(U))
        E1 = x_mul(O, a, x_pow(O, T.Phi1, k))
        aC = x_mul(O, a, T.Chat)
        E0 = x_neg(O, x_mul(O, aC, x_pow(O, T.Phi1, k)))
        C.ck('II1-dev', dev_matches(T, devP, {S3: E0, S3 + 1: E1}), ctx)
        Q, Rem = x_divmod(O, aC, T.Phi1)
        okw = T.w1(Rem) == bstar
        C.ck('II1-DEV1-w1Rem', okw, ctx)
        if okw:
            C.ck('II1-DEV1-readRem', T.R1(Rem, bstar) ==
                 K1.mul(K1.pow(T.z1, d1 + epr), T.tau), ctx)
        C.ck('II1-DEV1-Qw', (not Q) or T.w1(Q) >= bstar - T.w1Phi1, ctx)
        C.ck('II1-w2E0', T.w2(E0) == B2, ctx)
        C.ck('II1-R2vE0', T.R2v(E0)[0] == predE0read, ctx)
        C.ck('II1-w2E1', T.w2(E1) == B2 - T.e1 * T.gamma2, ctx)
        return
    # II-2 / II-3: inner Case II objects (g0 = 1)
    S1pp = S1 - T.e0
    A1 = x_scal(O, x_pow(O, T.Phi0, S1pp), O.pipow(U))
    A0 = x_neg(O, x_mul(O, T.lift0(T.psi0[0]),
                        x_scal(O, x_pow(O, T.Phi0, S1pp), O.pipow(U + T.h0))))
    A0C = x_mul(O, A0, T.Chat); A1C = x_mul(O, A1, T.Chat)
    Q0, Rem0 = x_divmod(O, A0C, T.Phi1)
    Q1, R1p = x_divmod(O, A1C, T.Phi1)
    omega = S1pp + T.s_gamma2
    c0K1 = K1.embed(T.psi0[0])
    predRem0 = K1.neg(K1.mul(K1.mul(c0K1, T.tau), K1.pow(T.z1, epr)))
    okw = T.w1(Rem0) == bstar
    C.ck('II23-DEV1-w1Rem0', okw, ctx)
    if okw:
        C.ck('II23-DEV1-readRem0', T.R1(Rem0, bstar) == predRem0, ctx)
    C.ck('II23-DEV1-Q0w', (not Q0) or T.w1(Q0) >= bstar - T.w1Phi1, ctx)
    C.ck('II23-DEV1-R1pw', (not R1p) or T.w1(R1p) >= bstar - T.e0 * T.h0, ctx)
    C.ck('II23-Q1-only-if', (not Q1) or omega >= T.e0, ctx)   # note S4.6 claim
    C.ck('II23-Q1-e0ge3', (not Q1) or T.e0 >= 3, ctx)         # note S4.6 claim
    C.ck('II23-Q1w', (not Q1) or T.w1(Q1) >= bstar - T.e0 * T.h0 - T.w1Phi1, ctx)
    if case == 'II-2':
        k = S2 - T.e1
        E1 = x_add(O, x_mul(O, A1, x_pow(O, T.Phi1, k + 1)),
                   x_mul(O, A0, x_pow(O, T.Phi1, k)))
        E0 = x_neg(O, x_add(O, x_mul(O, A1C, x_pow(O, T.Phi1, k + 1)),
                            x_mul(O, A0C, x_pow(O, T.Phi1, k))))
        C.ck('II2-E0-is-digit', x_deg(O, E0) < x_deg(O, T.Phi2), ctx)
        C.ck('II2-dev', dev_matches(T, devP, {S3: E0, S3 + 1: E1}), ctx)
        C.ck('II2-w2E0', T.w2(E0) == B2, ctx)
        C.ck('II2-R2vE0', T.R2v(E0)[0] == predE0read, ctx)
        C.ck('II2-w2E1', T.w2(E1) == B2 - T.e1 * T.gamma2, ctx)
    else:  # II-3
        C.ck('II3-d2is0', d2 == 0, ctx)
        E1 = A1
        E0 = x_sub(O, x_mul(O, A0, x_pow(O, T.Phi1, T.e1 - 1)), A1C)
        C.ck('II3-E0-is-digit', x_deg(O, E0) < x_deg(O, T.Phi2), ctx)
        C.ck('II3-dev', dev_matches(T, devP, {S3: E0, S3 + 1: E1}), ctx)
        C.ck('II3-w2E0', T.w2(E0) == B2, ctx)
        C.ck('II3-R2vE0', T.R2v(E0)[0] == predE0read, ctx)

# ---------------- DCX instance record (open-lemma territory: reported, not asserted) ----------------
def dcx_record(T, case, S1, S2, S3, U, thm_ok, wm_ok, prod_ok, shape_ok, devP, rec, ctx):
    O = T.O
    S1pp = S1 - T.e0
    A1 = x_scal(O, x_pow(O, T.Phi0, S1pp), O.pipow(U))
    A0 = x_neg(O, x_mul(O, T.lift0(T.psi0[0]),
                        x_scal(O, x_pow(O, T.Phi0, S1pp), O.pipow(U + T.h0))))
    A1C = x_mul(O, A1, T.Chat)
    Q1, _ = x_divmod(O, A1C, T.Phi1)
    if case == 'II-2':
        k = S2 - T.e1
        A0C = x_mul(O, A0, T.Chat)
        E0n = x_add(O, x_mul(O, A1C, x_pow(O, T.Phi1, k + 1)),
                    x_mul(O, A0C, x_pow(O, T.Phi1, k)))
    else:
        E0n = x_sub(O, x_mul(O, A0, x_pow(O, T.Phi1, T.e1 - 1)), A1C)
    ovf = x_deg(O, E0n) >= x_deg(O, T.Phi2)
    support = [j for j, A in enumerate(devP) if A]
    rec.append(dict(tower=T.name, pair=ctx[1:], case=case, thm=thm_ok, wmult=wm_ok,
                    prod=prod_ok, shape=shape_ok, q1_nonzero=bool(Q1),
                    naive_E0_overflows=bool(ovf), slot_support=support))

# ---------------- mutation controls on the law's constants ----------------
MUTN = ['M1-drop-top-carry(zbar^d3->1)', 'M2-gamma3+1-inside-D2',
        'M3-Sigma-drops-delta3-term', 'M4-naive-Sigma=gamma2*delta2',
        'M5-D2-plus-delta2-leak', 'M6-l0->l0p-in-D1']
def mutate(T, mid, S1, S2, s1S, s2S, d3, d2, D2, D1, Sig):
    if mid == 0: return (0, D2, D1)
    if mid == 1:
        n = S2 - s2S + T.l1 * (T.gamma3 + 1) * d3
        return None if n % T.e1 else (d3, n // T.e1, D1)
    if mid == 2:
        n = S1 - s1S + T.l0 * (D2 * T.gamma2)
        return None if n % T.e0 else (d3, D2, n // T.e0)
    if mid == 3:
        n = S1 - s1S + T.l0 * (T.gamma2 * d2)
        return None if n % T.e0 else (d3, D2, n // T.e0)
    if mid == 4: return (d3, D2 + d2, D1)
    if mid == 5:
        n = S1 - s1S + T.l0p * Sig
        return None if n % T.e0 else (d3, D2, n // T.e0)

def mut_field(T, m):
    return T.K3val(m[0], T.K2.pow(T.z2, m[1]), T.K1.pow(T.z1, m[2]))

# ---------------- per-pair driver ----------------
def run_pair(T, g, gp, cache, C, dcxrec, mut, census, getv):
    O = T.O
    d, dP, dS = T.split(g), T.split(gp), T.split(g + gp)
    e0, e1, e2 = T.e0, T.e1, T.e2
    S3 = d['s3'] + dP['s3']; S2 = d['s2'] + dP['s2']; S1 = d['s1'] + dP['s1']
    U = d['u1'] + dP['u1']
    d3 = S3 // e2; d2 = S2 // e1; d1 = S1 // e0
    B2 = d['b2'] + dP['b2']; B1 = d['b1'] + dP['b1']
    ctx = (T.name, g, gp)
    # --- integer layer (unconditional, incl. on DCX) ---
    C.ck('WINDOW', dS['u1'] >= 0, ctx)
    C.ck('L2-3a', dS['b2'] == B2 + d3 * T.gamma3, ctx)
    num2 = S2 - dS['s2'] + T.l1 * T.gamma3 * d3
    C.ck('D2-INT', num2 % e1 == 0, ctx); D2 = num2 // e1
    Sig = D2 * T.gamma2 + d3 * T.gamma3 * (T.l1p - T.l1 * T.w1Phi1)
    C.ck('L2-3b', dS['b1'] == B1 + Sig, ctx)
    num1 = S1 - dS['s1'] + T.l0 * Sig
    C.ck('D1-INT', num1 % e0 == 0, ctx); D1 = num1 // e0
    case, isdcx = case_of(T, d, dP, C, ctx)
    # --- CASE-SPLIT degree equivalence (proved for ALL pairs, S4.3) ---
    A = x_mul(O, [O.pipow(U)], x_mul(O, x_pow(O, T.Phi0, S1), x_pow(O, T.Phi1, S2)))
    C.ck('CASESPLIT-DEG', (case == 'I') == (x_deg(O, A) < x_deg(O, T.Phi2)), ctx)
    # --- value layer ---
    vg, pg = getv(g); vgp, pgp = getv(gp); vS, _ = getv(g + gp)
    P = x_mul(O, pg, pgp)
    vP, w3P, readsP, devP = T.val3(P)
    inner = T.K1.mul(T.K1.pow(T.z1, d1), T.eps1(B1))
    mid = T.K2.mul(T.K2.pow(T.z2, d2), T.eps2(B2))
    wm_ok = (vP == T.K3val(d3, mid, inner))
    prod_ok = (vP == T.K3.mul(T.K3.pow(T.zbar, d3), T.K3.mul(vg, vgp)))
    shape_ok = (w3P == g + gp and len(readsP) == 1 and readsP[0][0] == d3)
    c3 = T.K3.mul(vP, T.K3.inv(vS))
    pred = T.K3val(d3, T.K2.pow(T.z2, D2), T.K1.pow(T.z1, D1))
    thm_ok = (c3 == pred)
    if isdcx:
        C.ck('DCX-subcase', case in ('II-2', 'II-3'), ctx)
        C.ck('DCX-e0ge3', e0 >= 3, ctx)
        dcx_record(T, case, S1, S2, S3, U, thm_ok, wm_ok, prod_ok, shape_ok, devP,
                   dcxrec, ctx)
        census['DCX'] = census.get('DCX', 0) + 1
    else:
        C.ck('WMULT-eps-form', wm_ok, ctx)
        C.ck('WMULT-prod-form', prod_ok, ctx)
        C.ck('SINGLE-READ-SHAPE', shape_ok, ctx)
        C.ck('THEOREM', thm_ok, ctx)
        case_checks(T, case, S1, S2, S3, U, d1, d2, d3, B1, B2, A, devP, C, ctx)
        census[case] = census.get(case, 0) + 1
    # --- degenerations (S6.3), unconditional ---
    if e2 == 1:
        C.ck('CX-d3is0', d3 == 0, ctx)
        C.ck('CX-b2isgamma', d['b2'] == g and dP['b2'] == gp, ctx)
        C.ck('CX-D2isdelta2', D2 == d2, ctx)
        C.ck('CX-Sig', Sig == T.gamma2 * d2, ctx)
        naccp = S1 - dS['s1'] + T.l0 * T.gamma2 * d2
        C.ck('CX-D1-accepted-int', naccp % e0 == 0, ctx)
        if naccp % e0 == 0:
            Dacc = naccp // e0
            C.ck('CX-D1-accepted', D1 == Dacc, ctx)
            # the ACCEPTED order-2 law, re-measured by an OWN level-2 cocycle:
            v2P = T.R2v(P)[0]
            c2 = T.K2.mul(v2P, T.K2.inv(T.R2v(getv(g + gp)[1])[0]))
            acc2 = T.K2.mul(T.K2.pow(T.z2, d2),
                            T.K2.embed(T.K1.pow(T.z1, Dacc)))
            C.ck('CX-accepted-law-c2', c2 == acc2, ctx)
            C.ck('CX-c3-equals-c2', c3 == T.e23(c2), ctx)
    if e1 == 1:
        C.ck('CW-D2is0', D2 == 0, ctx)
        C.ck('CW-Sig', Sig == d3 * T.gamma3, ctx)
    if e0 == 1:
        C.ck('CV-D1is0', D1 == 0, ctx)
        C.ck('CV-S1is0', S1 == 0, ctx)
    # --- mutation controls (measured leg) ---
    for mid in range(6):
        m = mutate(T, mid, S1, S2, dS['s1'], dS['s2'], d3, d2, D2, D1, Sig)
        if m is None:
            mut[mid][0] += 1; mut[mid][1] += 1; mut[mid][2] += 1
        else:
            mp = mut_field(T, m)
            if mp != pred: mut[mid][0] += 1
            if mp != c3: mut[mid][1] += 1

# ---------------- window ----------------
def build_window(T, rng):
    G0 = 0
    while not all(T.split(g)['u1'] >= 0 for g in range(G0, G0 + T.E3)):
        G0 += T.E3
        assert G0 < 10000 * T.E3
    M = rng.randrange(2, 10)
    return (list(range(G0, G0 + T.E3)) +
            list(range(G0 + M * T.E3, G0 + (M + 1) * T.E3))), G0, M

# ---------------- tower roster (fresh; verifier-owned; seed 20260803) ----------------
def ic(F, n):
    if isinstance(F, PrimeField): return n % F.p
    return F.embed(ic(F.base, n))

def SPECS(rng):
    return [
        # DCX-live (e0=3, g0=g1=1, s(gamma2)=2): fresh rings Z5 / F5[[t]]
        dict(name='TW1-Z5-DCX', O=OZp(5), phibar=[1, 1], pert=[rng.randrange(5)],
             r0=(3, 2, lambda K: [ic(K, 2), K.one()]),
             r1=(2, 1, lambda K: [ic(K, 2), K.one()]),
             r2=(2, 1, lambda K: [ic(K, 3), K.one()])),
        dict(name='TW1b-F5t-DCX', O=OFpt(5), phibar=[1, 1], pert=None,
             r0=(3, 2, lambda K: [ic(K, 2), K.one()]),
             r1=(2, 1, lambda K: [ic(K, 2), K.one()]),
             r2=(2, 1, lambda K: [ic(K, 3), K.one()])),
        # DCX-live at e1 = 1 (the II-3 corner flavor), e0 = 4
        dict(name='TW2-F3t-DCX-e1is1', O=OFpt(3), phibar=[2, 1], pert=None,
             r0=(4, 1, lambda K: [ic(K, 1), K.one()]),
             r1=(1, 3, lambda K: [ic(K, 1), K.one()]),
             r2=(2, 1, lambda K: [ic(K, 1), K.one()])),
        # g1 = 2 (all Case I at the top), e2 = 3, K2 = F9
        dict(name='TW3-Z3-g1is2', O=OZp(3), phibar=[1, 1], pert=[rng.randrange(3)],
             r0=(2, 1, lambda K: [ic(K, 1), K.one()]),
             r1=(2, 1, lambda K: [ic(K, 2), ic(K, 1), K.one()]),
             r2=(3, 1, lambda K: [K.gen(), K.one()])),
        # g0 = 2 (Case II-1 with g0 >= 2 — the S4.5 ALL-g0 clause), char 2
        dict(name='TW4-F2t-g0is2', O=OFpt(2), phibar=[1, 1], pert=None,
             r0=(2, 1, lambda K: [ic(K, 1), ic(K, 1), K.one()]),
             r1=(2, 1, lambda K: [K.gen(), K.one()]),
             r2=(2, 1, lambda K: [K.add(K.embed(K.base.gen()), K.one()), K.one()])),
        # e2 = 1 degeneration (COR-3 CX: must reproduce the ACCEPTED order-2 law)
        dict(name='TW5-Z3-e2is1', O=OZp(3), phibar=[1, 1], pert=None,
             r0=(2, 1, lambda K: [ic(K, 1), K.one()]),
             r1=(2, 1, lambda K: [ic(K, 1), K.one()]),
             r2=(1, 2, lambda K: [ic(K, 1), K.one()])),
        # e0 = 1 degeneration (COR-3 CV: D1 = 0)
        dict(name='TW6-Z5-e0is1', O=OZp(5), phibar=[2, 1], pert=None,
             r0=(1, 2, lambda K: [ic(K, 2), K.one()]),
             r1=(2, 1, lambda K: [ic(K, 2), K.one()]),
             r2=(2, 1, lambda K: [ic(K, 2), K.one()])),
        # d0 = 2 (K0 = F4), inner Case II live at e0 = 2 (DCX must stay EMPTY)
        dict(name='TW7-Z2-d0is2', O=OZp(2), phibar=[1, 1, 1], pert=[1, 0],
             r0=(2, 1, lambda K: [K.gen(), K.one()]),
             r1=(2, 1, lambda K: [K.add(K.embed(K.base.gen()), K.one()), K.one()]),
             r2=(2, 1, lambda K: [K.embed(K.base.embed(K.base.base.gen())), K.one()])),
        # g2 = 2 (K3 = F16), e1 = 1, g0 = 2, e0 = 3 non-DCX control (g0 != 1)
        dict(name='TW8-F2t-g2is2', O=OFpt(2), phibar=[1, 1], pert=None,
             r0=(3, 2, lambda K: [ic(K, 1), ic(K, 1), K.one()]),
             r1=(1, 1, lambda K: [K.gen(), K.one()]),
             r2=(2, 1, lambda K: [K.embed(K.base.gen()), ic(K, 1), K.one()])),
        # e1 = 3 (II-1/II-2 with k > 0), Z5
        dict(name='TW9-Z5-e1is3', O=OZp(5), phibar=[1, 1], pert=[rng.randrange(5)],
             r0=(2, 1, lambda K: [ic(K, 2), K.one()]),
             r1=(3, 1, lambda K: [ic(K, 2), K.one()]),
             r2=(2, 1, lambda K: [ic(K, 3), K.one()])),
    ]

# ---------------- symbolic integer layer (field-free; note S2 + EXP-KIT integrality) ----------------
def symbolic_leg(rng, n=20000):
    bad = 0
    for _ in range(n):
        def rd():
            e = rng.randrange(1, 7)
            h = rng.randrange(1, 12)
            while gcd(e, h) != 1: h = rng.randrange(1, 12)
            return e, h
        e0, h0 = rd(); e1, h1 = rd(); e2, h2 = rd()
        g0 = rng.randrange(1, 4); g1 = rng.randrange(1, 4)
        w1P = e0 * g0 * h0; gamma2 = e1 * w1P + h1
        w2P = e1 * g1 * gamma2; gamma3 = e2 * w2P + h2
        l0, l0p = bezout(e0, h0); l1, l1p = bezout(e1, h1)
        def split(g):
            s3, u3 = eq12(g, e2, h2); b2 = u3 - s3 * w2P
            s2, u2 = eq12(b2, e1, h1); b1 = u2 - s2 * w1P
            s1, u1 = eq12(b1, e0, h0)
            return s3, b2, s2, b1, s1, u1
        g = rng.randrange(-3000, 3000); gp = rng.randrange(-3000, 3000)
        s3, b2, s2, b1, s1, u1 = split(g)
        s3p, b2p, s2p, b1p, s1p, u1p = split(gp)
        s3S, b2S, s2S, b1S, s1S, u1S = split(g + gp)
        d3 = (s3 + s3p) // e2
        ok = d3 in (0, 1)
        ok &= (b2S == b2 + b2p + d3 * gamma3)                       # L2-(3a)
        n2 = s2 + s2p - s2S + l1 * gamma3 * d3
        ok &= (n2 % e1 == 0); D2 = n2 // e1                          # D2-INT
        Sig = D2 * gamma2 + d3 * gamma3 * (l1p - l1 * w1P)
        ok &= (b1S == b1 + b1p + Sig)                                # L2-(3b)
        n1 = s1 + s1p - s1S + l0 * Sig
        ok &= (n1 % e0 == 0)                                         # D1-INT
        # EXP-KIT(a) integrality + (c) closed-form agreement at both levels
        for (bb, ee, hh, ll) in ((b1, e0, h0, l0), (b1p, e0, h0, l0), (b1S, e0, h0, l0),
                                 (b2, e1, h1, l1), (b2p, e1, h1, l1), (b2S, e1, h1, l1)):
            ok &= ((eq12(bb, ee, hh)[0] - ll * bb) % ee == 0)
        d1 = (s1 + s1p) // e0
        lhs1 = d1 + (eq12(b1 + b1p, e0, h0)[0] - l0 * (b1 + b1p)) // e0 \
                  - (s1S - l0 * b1S) // e0
        ok &= (lhs1 == n1 // e0)                                     # EXP-KIT(c) lvl 1
        d2c = (s2 + s2p) // e1
        lhs2 = d2c + (eq12(b2 + b2p, e1, h1)[0] - l1 * (b2 + b2p)) // e1 \
                   - (s2S - l1 * b2S) // e1
        ok &= (lhs2 == n2 // e1)                                     # EXP-KIT(c) lvl 2
        if u1 >= 0 and u1p >= 0: ok &= (u1S >= 0)                    # WINDOW
        if not ok: bad += 1
    return n, bad

# ---------------- main ----------------
def main():
    rng = random.Random(20260803)
    specs = SPECS(rng)
    towers = []
    print('=' * 78)
    print('ITERLAW3-PE from-note reimplementation  (seed 20260803, %d fresh towers)'
          % len(specs))
    print('=' * 78)
    C = Ctr()
    for sp in specs:
        T = Tower3(sp['name'], sp['O'], sp['phibar'], sp['r0'], sp['r1'], sp['r2'],
                   pert=sp['pert'])
        towers.append(T)
        C.ck('WELL-DEF', not T.welldef_bad, (T.name, tuple(T.welldef_bad)))
        print('%-18s O=%-9s d0=%d (e,h,g)=(%d,%d,%d)(%d,%d,%d)(%d,%d,%d) E3=%-3d '
              'gamma2=%d gamma3=%d s(gamma2)=%d pert=%s'
              % (T.name, T.O.name(), T.d0, T.e0, T.h0, T.g0, T.e1, T.h1, T.g1,
                 T.e2, T.h2, T.g2, T.E3, T.gamma2, T.gamma3, T.s_gamma2,
                 sp['pert'] is not None))
    wins = []
    for T in towers:
        W, G0, M = build_window(T, rng)
        wins.append((T, W, G0, M))
    # --- mutation VISIBILITY pre-pass (formula level only; no val3 measured) ---
    vis = [0] * 6
    for T, W, G0, M in wins:
        for g in W:
            for gp in W:
                d, dP, dS = T.split(g), T.split(gp), T.split(g + gp)
                S3 = d['s3'] + dP['s3']; S2 = d['s2'] + dP['s2']; S1 = d['s1'] + dP['s1']
                d3 = S3 // T.e2; d2 = S2 // T.e1
                n2 = S2 - dS['s2'] + T.l1 * T.gamma3 * d3
                if n2 % T.e1: continue
                D2 = n2 // T.e1
                Sig = D2 * T.gamma2 + d3 * T.gamma3 * (T.l1p - T.l1 * T.w1Phi1)
                n1 = S1 - dS['s1'] + T.l0 * Sig
                if n1 % T.e0: continue
                D1 = n1 // T.e0
                pred = T.K3val(d3, T.K2.pow(T.z2, D2), T.K1.pow(T.z1, D1))
                for mid in range(6):
                    m = mutate(T, mid, S1, S2, dS['s1'], dS['s2'], d3, d2, D2, D1, Sig)
                    if m is None or mut_field(T, m) != pred: vis[mid] += 1
    print('-' * 78)
    print('MUTATION VISIBILITY PRE-PASS (field-level, before any measurement):')
    for mid in range(6):
        print('  %-36s visible on %5d pairs %s'
              % (MUTN[mid], vis[mid], 'OK' if vis[mid] > 0 else '** NOT VISIBLE **'))
    vis_ok = all(v > 0 for v in vis)
    if not vis_ok:
        print('** ABORT: some mutation not field-visible — redesign towers **')
        sys.exit(2)
    # --- main measured pass ---
    mut = [[0, 0, 0] for _ in range(6)]  # visible, violations, non-integral
    dcxrec = []
    tower_rows = []
    npairs = 0
    for T, W, G0, M in wins:
        cache = {}
        def getv(g, T=T, cache=cache):
            if g not in cache:
                d = T.split(g)
                C.ck('ANCHOR-IN-W3', d['u1'] >= 0, (T.name, g))
                poly = T.anchor_poly(d)
                v, w3g, reads, _ = T.val3(poly)
                C.ck('L6-3', v == T.K3val(0, T.eps2(d['b2']), T.eps1(d['b1']))
                     and w3g == g and len(reads) == 1 and reads[0][0] == 0, (T.name, g))
                cache[g] = (v, poly)
            return cache[g]
        census = {}
        for g in W:
            for gp in W:
                run_pair(T, g, gp, cache, C, dcxrec, mut, census, getv)
                npairs += 1
        ndcx = census.get('DCX', 0)
        blk = len(W) ** 2
        row = dict(tower=T.name, G0=G0, M=M, block=blk, census=census,
                   dcx=ndcx, dcx_measure=ndcx / blk,
                   dcx_expected=(T.e0 >= 3 and T.g0 == 1 and T.g1 == 1))
        tower_rows.append(row)
        print('%-18s block %4d  census %s' % (T.name, blk,
              ' '.join('%s:%d' % (k, census[k]) for k in sorted(census))))
    # --- DCX summary ---
    print('-' * 78)
    dcx_ok = True
    for row in tower_rows:
        exp = row['dcx_expected']
        if exp != (row['dcx'] > 0): dcx_ok = False
        print('DCX %-18s measure %3d/%4d = %.4f  (predicate-live expected: %s) %s'
              % (row['tower'], row['dcx'], row['block'], row['dcx_measure'], exp,
                 'OK' if exp == (row['dcx'] > 0) else '** MISMATCH **'))
    dcx_thm = sum(1 for r in dcxrec if r['thm'])
    dcx_wm = sum(1 for r in dcxrec if r['wmult'] and r['prod'] and r['shape'])
    dcx_q1 = sum(1 for r in dcxrec if r['q1_nonzero'])
    dcx_ovf = sum(1 for r in dcxrec if r['naive_E0_overflows'])
    print('DCX instance data (OPEN lemma W-MULT-3-DCX; NOT counted as violations):')
    print('  pairs %d | theorem holds %d | W-MULT(all 3 clauses) holds %d | '
          'Q1!=0 %d | naive-E0 re-overflows %d'
          % (len(dcxrec), dcx_thm, dcx_wm, dcx_q1, dcx_ovf))
    # --- symbolic leg ---
    ns, bads = symbolic_leg(rng)
    print('-' * 78)
    print('SYMBOLIC integer layer (L1/L2-(3a,3b)/D-INTs/EXP-KIT/WINDOW): %d draws, '
          '%d bad' % (ns, bads))
    # --- mutation verdicts ---
    print('-' * 78)
    print('MUTATION CONTROLS (measured leg):')
    mut_ok = True
    for mid in range(6):
        fired = mut[mid][0] > 0 and mut[mid][1] > 0
        if not fired: mut_ok = False
        print('  %-36s visible %5d  violations %5d  (non-integral %d)  %s'
              % (MUTN[mid], mut[mid][0], mut[mid][1], mut[mid][2],
                 'FIRED' if fired else '** DID NOT FIRE **'))
    # --- family table + verdict ---
    print('-' * 78)
    tot, bad = C.total()
    for tag in sorted(C.fam):
        n, b = C.fam[tag]
        print('  %-24s %6d checked  %4d bad%s' % (tag, n, b, '' if b == 0 else '  **'))
    if VIOL:
        print('FIRST VIOLATIONS:')
        for v in VIOL[:25]: print('   ', v)
    green = (bad == 0 and bads == 0 and mut_ok and dcx_ok and vis_ok)
    print('=' * 78)
    print('PAIRS %d  CHECKS %d  VIOLATIONS %d  SYMBOLIC %d/%d  MUTATIONS %s  DCX %s'
          % (npairs, tot, bad, ns - bads, ns, 'all fired' if mut_ok else 'MISS',
             'locus OK' if dcx_ok else 'MISMATCH'))
    print('VERDICT: %s' % ('ALL GREEN' if green else 'RED'))
    json.dump(dict(seed=20260803, pairs=npairs, checks=tot, violations=bad,
                   families={k: v for k, v in sorted(C.fam.items())},
                   towers=tower_rows, dcx_instance=dcxrec,
                   dcx_summary=dict(pairs=len(dcxrec), thm=dcx_thm, wmult=dcx_wm,
                                    q1=dcx_q1, overflow=dcx_ovf),
                   mutations=[dict(name=MUTN[i], visible=mut[i][0],
                                   violations=mut[i][1], nonintegral=mut[i][2])
                              for i in range(6)],
                   symbolic=dict(draws=ns, bad=bads),
                   verdict='ALL GREEN' if green else 'RED'),
              open(__file__.replace('.py', '_results.json'), 'w'), indent=1,
              default=str)
    sys.exit(0 if green else 1)

if __name__ == '__main__':
    main()
