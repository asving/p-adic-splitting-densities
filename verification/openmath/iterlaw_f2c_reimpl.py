#!/usr/bin/env python3
"""iterlaw_f2c_reimpl.py -- F2c verifier-owned FROM-NOTE reimplementation (hostile pass PE).

Implemented from lean/notes/openmath/ITERLAW_2026-08-08.md (+ DITER_RESTATE_2026-08-08.md
S2) ALONE; the sealed falsifier verification/openmath/iterlaw_check.py was NOT opened
before this file was written and first run (F2c ordering per the pass charge).

Contents:
  * the harness tower class (S0 Setting): DVR O in {Z_p proxy (exact Z), F_p[[t]]},
    standard-lift Phi1, residue tower k0 -> K0 -> K1 -> K2 (exact tower arithmetic);
  * the calculus: eq12, Gauss content w0, Phi0/Phi1 developments, w1, w2, eps1
    (reading C), R1-read, R2-read/val, canonical anchors, window W, cocycle;
  * checks: L2 INNER-SHIFT, L3 WINDOW, L4 EPS-CLOSED, L5 EPS-MULT, Lemma EXP,
    L6 ANCHOR-VAL, L7 PAIR-VAL (Cases I and II, incl. single-slot shape),
    THEOREM (ITER-LAW display, checked multiplicatively: val(P) == zbar^d2 z1^D val(phi'')),
    COR-1 integrality, COR-3 degenerations, L1 EQ12-ADD both levels (random draws);
  * mutation controls (each must be DETECTED = nonzero violations somewhere):
      M-ZBAR  : zbar exponent delta2 -> 1-delta2
      M-FIB   : drop the l0*gamma2*delta2 fibration term
      M-DIV   : exponent divisor /e0 -> /1
      M-FLOOR : delta2 floor divisor e1 -> e1+1

Fresh verifier rows, seed 20260803, second window shifted +5*E2 (chosen without
reading the sealed script). Exit 0 iff every check family has 0 violations AND every
mutation control is detected AND coverage duties are met (>=1 row E2>=8; Case-II
coverage>0; degenerate rows e0=1 and e1=1 present).
"""
import sys, json, random
from math import gcd
from itertools import product

SEED = 20260803

# ---------------- finite-field tower (generic, exact) ----------------

class Fp:
    def __init__(self, p): self.p = p
    def zero(self): return 0
    def one(self): return 1
    def add(self, a, b): return (a + b) % self.p
    def sub(self, a, b): return (a - b) % self.p
    def neg(self, a): return (-a) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def inv(self, a):
        assert a % self.p != 0
        return pow(a, self.p - 2, self.p)
    def is_zero(self, a): return a % self.p == 0
    def elems(self): return list(range(self.p))

# polynomials over a field F: tuples, index = degree, trimmed
def ptrim(F, c):
    c = list(c)
    while c and F.is_zero(c[-1]): c.pop()
    return tuple(c)
def pdeg(c): return len(c) - 1
def padd(F, a, b):
    n = max(len(a), len(b)); out = []
    for i in range(n):
        x = a[i] if i < len(a) else F.zero()
        y = b[i] if i < len(b) else F.zero()
        out.append(F.add(x, y))
    return ptrim(F, out)
def pneg(F, a): return tuple(F.neg(x) for x in a)
def psub(F, a, b): return padd(F, a, pneg(F, b))
def pmul(F, a, b):
    if not a or not b: return ()
    out = [F.zero()] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if F.is_zero(x): continue
        for j, y in enumerate(b):
            out[i + j] = F.add(out[i + j], F.mul(x, y))
    return ptrim(F, out)
def pdivmod(F, a, b):
    a = list(a); q = [F.zero()] * max(0, len(a) - len(b) + 1)
    binv = F.inv(b[-1])
    while len(a) >= len(b):
        if F.is_zero(a[-1]):
            a.pop(); continue
        k = len(a) - len(b); c = F.mul(a[-1], binv); q[k] = c
        for i in range(len(b)):
            a[k + i] = F.sub(a[k + i], F.mul(c, b[i]))
        a.pop()
    return ptrim(F, q), ptrim(F, a)
def pinv_mod(F, a, mod):
    r0, r1 = mod, ptrim(F, a)
    s0, s1 = (), (F.one(),)
    while r1:
        q, r = pdivmod(F, r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, psub(F, s0, pmul(F, q, s1))
    assert pdeg(r0) == 0, "not invertible"
    c = F.inv(r0[0])
    return ptrim(F, [F.mul(c, x) for x in s0])
def poly_eval(F, poly, x):
    r = F.zero()
    for c in reversed(poly): r = F.add(F.mul(r, x), c)
    return r

class Ext:
    """K = base[T]/(mod), mod monic tuple over base; elements = tuples of len deg."""
    def __init__(self, base, mod, name="T"):
        self.base = base; self.mod = mod; self.deg = len(mod) - 1; self.name = name
        assert self.deg >= 1 and mod[-1] == base.one()
    def _pad(self, c):
        c = list(c) + [self.base.zero()] * (self.deg - len(c))
        return tuple(c[:self.deg])
    def zero(self): return self._pad(())
    def one(self): return self._pad((self.base.one(),))
    def gen(self):
        if self.deg >= 2:
            return self._pad((self.base.zero(), self.base.one()))
        return self._pad(pneg(self.base, (self.mod[0],)))  # T = -c for mod = T + c
    def embed(self, a): return self._pad((a,))
    def add(self, a, b): return self._pad(padd(self.base, a, b))
    def sub(self, a, b): return self._pad(psub(self.base, a, b))
    def neg(self, a): return self._pad(pneg(self.base, a))
    def mul(self, a, b):
        _, r = pdivmod(self.base, pmul(self.base, ptrim(self.base, a), ptrim(self.base, b)), self.mod)
        return self._pad(r)
    def inv(self, a): return self._pad(pinv_mod(self.base, a, self.mod))
    def is_zero(self, a): return all(self.base.is_zero(x) for x in a)
    def elems(self):
        base_e = self.base.elems(); out = [()]
        for _ in range(self.deg):
            out = [t + (x,) for t in out for x in base_e]
        return [self._pad(t) for t in out]

def fpow(F, a, n):
    if n < 0:
        a = F.inv(a); n = -n
    r = F.one()
    while n:
        if n & 1: r = F.mul(r, a)
        a = F.mul(a, a); n >>= 1
    return r

def irreducible(F, poly):
    """monic poly over F, 1 <= deg <= 3: no-root test suffices for deg 2,3."""
    d = pdeg(poly)
    assert 1 <= d <= 3
    if d == 1: return True
    return all(not F.is_zero(poly_eval(F, poly, x)) for x in F.elems())

def pick_irr(K, g, rng):
    """Seeded choice of a monic irreducible degree-g poly over K with nonzero
    constant term (psi(0) != 0), excluding (deg 1) the case gen == 1 (detection power)."""
    cands = []
    for coeffs in product(K.elems(), repeat=g):
        poly = tuple(coeffs) + (K.one(),)
        if K.is_zero(poly[0]): continue
        if g == 1 and poly[0] == K.neg(K.one()): continue  # would give gen = 1
        if irreducible(K, poly): cands.append(poly)
    assert cands, "no admissible irreducible polynomial"
    cands.sort()
    return cands[rng.randrange(len(cands))]

# ---------------- the DVR O (two kinds) ----------------

class ZpO:
    """O = Z_p, computed in the dense subring Z (exact); pi = p; k0 = F_p."""
    kind = 'Zp'
    def __init__(self, p): self.p = p
    def zero(self): return 0
    def one(self): return 1
    def add(self, a, b): return a + b
    def sub(self, a, b): return a - b
    def neg(self, a): return -a
    def mul(self, a, b): return a * b
    def is_zero(self, a): return a == 0
    def pi_pow(self, n): return self.p ** n
    def from_int(self, n): return n
    def lift_k0(self, c): return c % self.p
    def w0(self, a):
        if a == 0: return None
        v = 0
        while a % self.p == 0:
            a //= self.p; v += 1
        return v
    def res(self, a, d):
        """class of a/pi^d in k0; defined for w0(a) >= d (note S0: res on w0 >= delta)."""
        if a == 0: return 0
        assert d >= 0 and a % (self.p ** d) == 0
        return (a // (self.p ** d)) % self.p

class FptO:
    """O = F_p[[t]] (polynomial representatives; exact); pi = t; k0 = F_p."""
    kind = 'Fpt'
    def __init__(self, p): self.p = p
    def _trim(self, c):
        c = [x % self.p for x in c]
        while c and c[-1] == 0: c.pop()
        return tuple(c)
    def zero(self): return ()
    def one(self): return (1,)
    def add(self, a, b):
        n = max(len(a), len(b))
        return self._trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                           for i in range(n)])
    def sub(self, a, b): return self.add(a, self.neg(b))
    def neg(self, a): return self._trim([-x for x in a])
    def mul(self, a, b):
        if not a or not b: return ()
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] += x * y
        return self._trim(out)
    def is_zero(self, a): return len(self._trim(a)) == 0
    def pi_pow(self, n): return self._trim([0] * n + [1])
    def from_int(self, n): return self._trim([n])
    def lift_k0(self, c): return self._trim([c])
    def w0(self, a):
        a = self._trim(a)
        if not a: return None
        for i, x in enumerate(a):
            if x % self.p != 0: return i
        return None
    def res(self, a, d):
        a = self._trim(a)
        if not a: return 0
        v = self.w0(a)
        assert d >= 0 and v >= d
        return a[d] % self.p if d < len(a) else 0

# ---- O[x] polynomials: lists over O, index = x-degree, trimmed ----
def optrim(O, a):
    a = list(a)
    while a and O.is_zero(a[-1]): a.pop()
    return a
def opadd(O, a, b):
    n = max(len(a), len(b)); out = []
    for i in range(n):
        x = a[i] if i < len(a) else O.zero()
        y = b[i] if i < len(b) else O.zero()
        out.append(O.add(x, y))
    return optrim(O, out)
def opmul(O, a, b):
    if not a or not b: return []
    out = [O.zero()] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if O.is_zero(x): continue
        for j, y in enumerate(b):
            out[i + j] = O.add(out[i + j], O.mul(x, y))
    return optrim(O, out)
def opscale(O, s, a): return optrim(O, [O.mul(s, x) for x in a])
def oppow(O, a, n):
    r = [O.one()]
    for _ in range(n): r = opmul(O, r, a)
    return r
def opdivmod(O, a, b):
    """division by MONIC b over O (exact; only ring ops needed)."""
    assert b and b[-1] == O.one(), "divisor must be monic"
    a = list(a); q = [O.zero()] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b):
        if O.is_zero(a[-1]):
            a.pop(); continue
        k = len(a) - len(b); c = a[-1]; q[k] = c
        for i in range(len(b)):
            a[k + i] = O.sub(a[k + i], O.mul(c, b[i]))
        a.pop()
    return optrim(O, q), optrim(O, a)
def op_content(O, a):
    """Gauss content: w0 extended to O[x] as coefficientwise min (note S0)."""
    vs = [O.w0(c) for c in a if not O.is_zero(c)]
    return min(vs) if vs else None

# ---------------- eq-(12-int) ----------------
def eq12(beta, e, h):
    """unique (s,u): u*e + s*h = beta, 0 <= s < e (gcd(e,h)=1)."""
    if e == 1:
        return 0, beta
    s = (beta * pow(h, -1, e)) % e
    u = (beta - s * h) // e
    assert u * e + s * h == beta and 0 <= s < e
    return s, u

# ---------------- the tower (note S0 Setting; standard lift) ----------------

class Tower:
    def __init__(self, name, O, phi0_int_coeffs, e0, h0, g0, e1, h1, g1, rng):
        self.name = name; self.O = O
        assert e0 >= 1 and h0 >= 1 and gcd(e0, h0) == 1
        assert e1 >= 1 and h1 >= 1 and gcd(e1, h1) == 1
        self.e0, self.h0, self.g0 = e0, h0, g0
        self.e1, self.h1, self.g1 = e1, h1, g1
        # Phi0 monic over O, w0(Phi0)=0, reduction irreducible
        assert phi0_int_coeffs[-1] == 1
        self.Phi0 = [O.from_int(c) for c in phi0_int_coeffs]
        self.d0 = len(phi0_int_coeffs) - 1
        assert op_content(O, self.Phi0) == 0
        p = O.p
        self.k0 = Fp(p)
        phibar = ptrim(self.k0, [self.k0.zero() if O.is_zero(c) else O.res(c, 0) for c in self.Phi0])
        assert pdeg(phibar) == self.d0 and irreducible(self.k0, phibar)
        self.K0 = Ext(self.k0, phibar, "X")
        # Read 0 / Read 1 residual polynomials (seeded fresh choices)
        self.psi0 = pick_irr(self.K0, g0, rng)
        self.K1 = Ext(self.K0, self.psi0, "z1")
        self.z1 = self.K1.gen()
        assert not self.K1.is_zero(self.z1)
        self.psi1 = pick_irr(self.K1, g1, rng)
        self.K2 = Ext(self.K1, self.psi1, "zbar")
        self.zbar = self.K2.gen()
        # standard lift: Phi1 = sum_{k=0}^{g0} lift(psi0,k) pi^{(g0-k)h0} Phi0^{e0 k}
        Phi1 = []
        for k in range(g0 + 1):
            digit = self.lift_K0(self.psi0[k])
            term = opscale(O, O.pi_pow((g0 - k) * h0), digit)
            term = opmul(O, term, oppow(O, self.Phi0, e0 * k))
            Phi1 = opadd(O, Phi1, term)
        self.Phi1 = Phi1
        assert len(Phi1) - 1 == e0 * g0 * self.d0 and Phi1[-1] == O.one()
        # derived data (note S0)
        self.w1Phi1 = e0 * g0 * h0
        self.gamma2 = e1 * self.w1Phi1 + h1
        self.E2 = e0 * e1
        # normalized Bezout pair: l0*h0 + l0p*e0 = 1, 0 <= l0 < e0
        if e0 == 1:
            self.l0, self.l0p = 0, 1
        else:
            self.l0 = pow(h0, -1, e0)
            self.l0p = (1 - self.l0 * h0) // e0
        assert self.l0 * h0 + self.l0p * e0 == 1 and 0 <= self.l0 < e0

    def lift_K0(self, a):
        """coefficientwise degree-<d0 lift of a K0 element to O[x] (note S0)."""
        return optrim(self.O, [self.O.lift_k0(c) for c in a])

    def res_poly(self, b, d):
        """res: {b in O[x], deg b < d0, w0(b) >= d} -> K0, b -> class of b/pi^d."""
        assert len(b) <= self.d0
        out = []
        for c in b:
            out.append(0 if self.O.is_zero(c) else self.O.res(c, d))
        return self.K0._pad(tuple(out))

    # --- level-1 calculus ---
    def phi0_dev(self, A):
        digs = []; cur = list(A)
        while cur:
            cur, r = opdivmod(self.O, cur, self.Phi0)
            digs.append(r)
        return digs
    def w1(self, A):
        digs = self.phi0_dev(A)
        vals = [self.e0 * op_content(self.O, b) + k * self.h0
                for k, b in enumerate(digs) if b]
        return min(vals) if vals else None
    def eps1(self, beta):
        """eps1(beta) = z1^{l0p*s(beta) - l0*u(beta)} (harness eps1, reading C)."""
        s, u = eq12(beta, self.e0, self.h0)
        return fpow(self.K1, self.z1, self.l0p * s - self.l0 * u)
    def R1_read(self, a, beta):
        """R_{1,beta}(a)(z1) = sum_m res(b_{s+m e0}/pi^{u-m h0}) z1^m,
        digit contributes iff w0(b) = u - m h0 EXACTLY, else 0."""
        s, u = eq12(beta, self.e0, self.h0)
        digs = self.phi0_dev(a)
        acc = self.K1.zero(); m = 0
        while s + m * self.e0 < len(digs):
            b = digs[s + m * self.e0]
            need = u - m * self.h0
            if b and need >= 0 and op_content(self.O, b) == need:
                r = self.res_poly(b, need)
                acc = self.K1.add(acc, self.K1.mul(self.K1.embed(r),
                                                   fpow(self.K1, self.z1, m)))
            m += 1
        return acc

    # --- level-2 calculus ---
    def phi1_dev(self, f):
        digs = []; cur = list(f)
        while cur:
            cur, r = opdivmod(self.O, cur, self.Phi1)
            digs.append(r)
        return digs
    def w2(self, f):
        digs = self.phi1_dev(f)
        vals = [self.e1 * self.w1(a) + j * self.gamma2
                for j, a in enumerate(digs) if a]
        return min(vals)
    def val(self, f):
        """val(f) = sum_j C_j(f) zbar^j (note S0 R2-read, reading C).
        Returns (K2 value, [(j, C_j) nonzero], gamma = w2(f))."""
        digs = self.phi1_dev(f)
        g = self.w2(f)
        s2, u2 = eq12(g, self.e1, self.h1)
        total = self.K2.zero(); slots = []
        j = 0
        while s2 + j * self.e1 < len(digs):
            a = digs[s2 + j * self.e1]
            num = g - (s2 + j * self.e1) * self.gamma2
            assert num % self.e1 == 0, "slot weight not integral"
            gj = num // self.e1
            if a and self.w1(a) == gj:
                Cj = self.K1.mul(self.eps1(gj), self.R1_read(a, gj))
                if not self.K1.is_zero(Cj):
                    slots.append((j, Cj))
                    total = self.K2.add(total,
                        self.K2.mul(self.K2.embed(Cj), fpow(self.K2, self.zbar, j)))
            j += 1
        return total, slots, g

    # --- anchors (note S0) ---
    def anchor(self, gamma):
        s2, u2 = eq12(gamma, self.e1, self.h1)
        g1v = u2 - s2 * self.w1Phi1
        s1, u1 = eq12(g1v, self.e0, self.h0)
        return {'s2': s2, 'u2': u2, 'gamma1': g1v, 's1': s1, 'u1': u1}
    def in_W(self, gamma):
        return self.anchor(gamma)['u1'] >= 0
    def phi_anchor(self, gamma):
        a = self.anchor(gamma)
        assert a['u1'] >= 0, "anchor outside window W"
        P = [self.O.pi_pow(a['u1'])]
        P = opmul(self.O, P, oppow(self.O, self.Phi0, a['s1']))
        P = opmul(self.O, P, oppow(self.O, self.Phi1, a['s2']))
        return P

# ---------------- verifier rows (fresh; seed 20260803; my own choices) ----------------
# duties: >=1 row E2>=8 (VA, VF); Case-II rows g0=1 with delta1=1 reachable (VA, VB, VF);
# degenerate e0=1 (VC); degenerate e1=1 (VD); all four base rings; d0 in {1,2}.
ROWS = [
    # name,   ring,  p, phi0,        e0,h0,g0,  e1,h1,g1
    ("VA", 'Fpt', 3, [0, 1],        2, 1, 1,   4, 3, 2),   # E2=8, Case II reachable
    ("VB", 'Zp',  2, [1, 1, 1],     3, 2, 1,   2, 1, 2),   # d0=2, Case II reachable
    ("VC", 'Zp',  3, [0, 1],        1, 2, 2,   3, 2, 1),   # e0=1 degeneration
    ("VD", 'Fpt', 2, [0, 1],        3, 1, 2,   1, 1, 2),   # e1=1 degeneration
    ("VE", 'Zp',  2, [0, 1],        2, 3, 2,   2, 1, 1),   # g0=2: Case I only
    ("VF", 'Fpt', 3, [1, 0, 1],     4, 3, 1,   2, 1, 1),   # E2=8, d0=2, Case II reachable
]

CHECKS = {}
def tally(name, ok, witness=None):
    rec = CHECKS.setdefault(name, [0, 0, []])
    rec[0] += 1
    if not ok:
        rec[1] += 1
        if len(rec[2]) < 3: rec[2].append(witness)

MUTS = {}
def mtally(mut, detected):
    rec = MUTS.setdefault(mut, [0, 0])
    rec[0] += 1
    if detected: rec[1] += 1

COVER = {'caseI_d0': 0, 'caseI_d1': 0, 'caseII': 0}
COVER_BY_ROW = {}

def find_window(T, length):
    """first run of `length` consecutive gamma >= 0 all in W."""
    g = 0
    while True:
        if all(T.in_W(g + i) for i in range(length)):
            return list(range(g, g + length))
        g += 1
        assert g < 10**6

def run_row(T, rng):
    e0, h0, g0, e1, h1 = T.e0, T.h0, T.g0, T.e1, T.h1
    l0, l0p, g2 = T.l0, T.l0p, T.gamma2
    K1, K2 = T.K1, T.K2
    cov = COVER_BY_ROW.setdefault(T.name, {'caseI_d0': 0, 'caseI_d1': 0, 'caseII': 0})

    # ---- integer layer: L1 both levels, L2, L4, L5, EXP (random draws) ----
    N_INT = 2000
    for _ in range(N_INT):
        b = rng.randrange(-10**6, 10**6); bp = rng.randrange(-10**6, 10**6)
        # L1 level 1
        s, u = eq12(b, e0, h0); sp, up = eq12(bp, e0, h0); s2_, u2_ = eq12(b + bp, e0, h0)
        d1 = (s + sp) // e0
        tally('I-L1-lvl1', d1 in (0, 1) and s2_ == s + sp - d1 * e0 and u2_ == u + up + d1 * h0,
              (T.name, b, bp))
        # L1 level 2
        s, u = eq12(b, e1, h1); sp, up = eq12(bp, e1, h1); s2_, u2_ = eq12(b + bp, e1, h1)
        d2 = (s + sp) // e1
        tally('I-L1-lvl2', d2 in (0, 1) and s2_ == s + sp - d2 * e1 and u2_ == u + up + d2 * h1,
              (T.name, b, bp))
        # L2 INNER-SHIFT
        ga = rng.randrange(-10**6, 10**6); gb = rng.randrange(-10**6, 10**6)
        A, B = T.anchor(ga), T.anchor(gb); C = T.anchor(ga + gb)
        d2 = (A['s2'] + B['s2']) // e1
        tally('I-L2-INNER-SHIFT', C['gamma1'] == A['gamma1'] + B['gamma1'] + d2 * g2,
              (T.name, ga, gb))
        # L4 EPS-CLOSED integer identity: (s - l0 b) / e0 = l0p s - l0 u, exactly
        s, u = eq12(b, e0, h0)
        tally('I-L4-EPS-CLOSED', (s - l0 * b) % e0 == 0 and (s - l0 * b) // e0 == l0p * s - l0 * u,
              (T.name, b))
        # L5 EPS-MULT exponent identity
        sp, up = eq12(bp, e0, h0); s2_, u2_ = eq12(b + bp, e0, h0)
        d1 = (s + sp) // e0
        tally('I-L5-EPS-MULT', (l0p * s - l0 * u) + (l0p * sp - l0 * up)
              == d1 + (l0p * s2_ - l0 * u2_), (T.name, b, bp))
        # Lemma EXP
        d2c = rng.randrange(2)
        bpp = b + bp + d2c * g2
        s3, u3 = eq12(bpp, e0, h0)
        lhs_num1 = (s2_ - l0 * (b + bp)); lhs_num2 = (s3 - l0 * bpp)
        ok = (lhs_num1 % e0 == 0 and lhs_num2 % e0 == 0)
        if ok:
            lhs = d1 + (lhs_num1 // e0 - lhs_num2 // e0)
            rhs_num = s + sp - s3 + l0 * g2 * d2c
            ok = rhs_num % e0 == 0 and lhs == rhs_num // e0
        tally('I-EXP', ok, (T.name, b, bp, d2c))

    # ---- field-level L4/L5 on a subsample ----
    for _ in range(200):
        b = rng.randrange(-10**4, 10**4); bp = rng.randrange(-10**4, 10**4)
        s, u = eq12(b, e0, h0)
        tally('F-L4-eps-closed-field',
              T.eps1(b) == fpow(K1, T.z1, (s - l0 * b) // e0), (T.name, b))
        sp, up = eq12(bp, e0, h0); d1 = (s + sp) // e0
        tally('F-L5-eps-mult-field',
              K1.mul(T.eps1(b), T.eps1(bp))
              == K1.mul(fpow(K1, T.z1, d1), T.eps1(b + bp)), (T.name, b, bp))

    # ---- value layer + theorem on anchor windows ----
    W0 = find_window(T, 2 * T.E2)
    W5 = [g + 5 * T.E2 for g in W0]
    for wname, WIN in (('W0', W0), ('W5', W5)):
        for g in WIN:
            tally('W-membership', T.in_W(g), (T.name, wname, g))
        # L6 on all anchors of the window
        for g in WIN:
            A = T.anchor(g)
            v, slots, w2g = T.val(T.phi_anchor(g))
            ok = (w2g == g and len(slots) == 1 and slots[0][0] == 0
                  and v == K2.embed(T.eps1(A['gamma1'])) and not K2.is_zero(v))
            tally('L6-ANCHOR-VAL', ok, (T.name, wname, g))
        # pairs
        for ga in WIN:
            for gb in WIN:
                A, B = T.anchor(ga), T.anchor(gb)
                gc = ga + gb; C = T.anchor(gc)
                tally('L3-WINDOW', C['u1'] >= 0, (T.name, wname, ga, gb))
                if C['u1'] < 0: continue
                d2 = (A['s2'] + B['s2']) // e1
                S1 = A['s1'] + B['s1']; d1 = S1 // e0
                beta, betap = A['gamma1'], B['gamma1']
                P = opmul(T.O, T.phi_anchor(ga), T.phi_anchor(gb))
                vP, slotsP, w2P = T.val(P)
                vC, slotsC, w2C = T.val(T.phi_anchor(gc))
                tally('T-W2-ADDITIVE', w2P == gc, (T.name, wname, ga, gb))
                tally('T-DENOM-NONZERO', not K2.is_zero(vC), (T.name, wname, gc))
                # case classification + coverage (+ note's partition claim)
                caseII = (g0 == 1 and d1 == 1)
                tally('CASE-PARTITION', (not caseII) == (S1 < e0 * g0),
                      (T.name, wname, ga, gb))
                if caseII: cov['caseII'] += 1; COVER['caseII'] += 1
                elif d1 == 1: cov['caseI_d1'] += 1; COVER['caseI_d1'] += 1
                else: cov['caseI_d0'] += 1; COVER['caseI_d0'] += 1
                # L7 PAIR-VAL both displayed forms + single-slot shape
                e_sum = T.eps1(beta + betap)
                lhs7 = K2.mul(K2.embed(K1.mul(fpow(K1, T.z1, d1), e_sum)),
                              fpow(K2, T.zbar, d2))
                tally('L7-PAIR-VAL-formA', vP == lhs7, (T.name, wname, ga, gb))
                lhs7b = K2.mul(K2.embed(K1.mul(T.eps1(beta), T.eps1(betap))),
                               fpow(K2, T.zbar, d2))
                tally('L7-PAIR-VAL-formB', vP == lhs7b, (T.name, wname, ga, gb))
                tally('L7-SINGLE-SLOT', len(slotsP) == 1 and slotsP[0][0] == d2,
                      (T.name, wname, ga, gb))
                # THEOREM (ITER-LAW): val(P) == zbar^d2 z1^D val(phi_{gc}), D integral
                N = A['s1'] + B['s1'] - C['s1'] + l0 * g2 * d2
                tally('COR1-INTEGRALITY', N % e0 == 0, (T.name, wname, ga, gb))
                if N % e0 != 0: continue
                D = N // e0
                rhs = K2.mul(K2.embed(fpow(K1, T.z1, D)), fpow(K2, T.zbar, d2))
                rhs = K2.mul(rhs, vC)
                tally('THEOREM-ITER-LAW', vP == rhs, (T.name, wname, ga, gb))
                # COR-3 degenerations
                if e0 == 1:
                    tally('COR3-e0=1', D == 0 and vP == K2.mul(fpow(K2, T.zbar, d2), vC),
                          (T.name, wname, ga, gb))
                if e1 == 1:
                    tally('COR3-e1=1', d2 == 0 and D == d1, (T.name, wname, ga, gb))
                # ---- mutation controls (each perturbed law must MISS somewhere) ----
                def law_value(d2x, Nx, div):
                    if Nx % div != 0: return None  # integrality breaks: detected
                    return K2.mul(K2.mul(K2.embed(fpow(K1, T.z1, Nx // div)),
                                         fpow(K2, T.zbar, d2x)), vC)
                # M-ZBAR: zbar exponent d2 -> 1-d2
                v_m = law_value(1 - d2, N, e0)
                mtally('M-ZBAR', v_m is None or v_m != vP)
                # M-FIB: drop l0*gamma2*delta2
                v_m = law_value(d2, A['s1'] + B['s1'] - C['s1'], e0)
                mtally('M-FIB', v_m is None or v_m != vP)
                # M-DIV: /e0 -> /1
                v_m = law_value(d2, N, 1)
                mtally('M-DIV', v_m is None or v_m != vP)
                # M-FLOOR: delta2 divisor e1 -> e1+1
                d2m = (A['s2'] + B['s2']) // (e1 + 1)
                v_m = law_value(d2m, A['s1'] + B['s1'] - C['s1'] + l0 * g2 * d2m, e0)
                mtally('M-FLOOR', v_m is None or v_m != vP)

def main():
    rng = random.Random(SEED)
    towers = []
    for (name, ring, p, phi0, e0, h0, g0, e1, h1, g1) in ROWS:
        O = ZpO(p) if ring == 'Zp' else FptO(p)
        T = Tower(name, O, phi0, e0, h0, g0, e1, h1, g1, rng)
        towers.append(T)
        print(f"[row {name}] ring={ring} p={p} d0={T.d0} (e0,h0,g0)=({e0},{h0},{g0}) "
              f"(e1,h1,g1)=({e1},{h1},{g1}) E2={T.E2} gamma2={T.gamma2} "
              f"l0={T.l0} l0p={T.l0p} psi0={T.psi0} psi1={T.psi1}")
    for T in towers:
        run_row(T, rng)
        print(f"[row {T.name}] done; coverage {COVER_BY_ROW[T.name]}")

    print("\n===== CHECK FAMILIES (samples / violations) =====")
    total_s = total_v = 0
    for k in sorted(CHECKS):
        s, v, wit = CHECKS[k]
        total_s += s; total_v += v
        line = f"{k:26s} {s:7d} / {v}"
        if v: line += f"   WITNESSES: {wit}"
        print(line)
    print(f"{'TOTAL':26s} {total_s:7d} / {total_v}")

    print("\n===== MUTATION CONTROLS (samples / detections) =====")
    mut_fail = []
    for k in sorted(MUTS):
        s, d = MUTS[k]
        det = d > 0
        print(f"{k:10s} {s:7d} / {d:7d}   {'DETECTED' if det else '** NOT DETECTED **'}")
        if not det: mut_fail.append(k)

    print("\n===== COVERAGE =====")
    print(f"global: {COVER}")
    for r, c in COVER_BY_ROW.items(): print(f"  {r}: {c}")
    duties = {
        'E2>=8 row present': any(T.E2 >= 8 for T in towers),
        'Case-II coverage > 0': COVER['caseII'] > 0,
        'e0=1 row present': any(T.e0 == 1 for T in towers),
        'e1=1 row present': any(T.e1 == 1 for T in towers),
        'Case-I delta1=1 coverage > 0': COVER['caseI_d1'] > 0,
    }
    for k, v in duties.items(): print(f"  duty: {k}: {'MET' if v else '** UNMET **'}")

    ok = (total_v == 0) and not mut_fail and all(duties.values())
    print(f"\nVERDICT: {'ALL GREEN (exit 0)' if ok else '** RED **'}  "
          f"samples={total_s} violations={total_v} mut_undetected={mut_fail}")
    with open('iterlaw_f2c_reimpl_results.json', 'w') as f:
        json.dump({'seed': SEED, 'checks': {k: v[:2] for k, v in CHECKS.items()},
                   'mutations': MUTS, 'coverage': COVER,
                   'coverage_by_row': COVER_BY_ROW, 'duties': duties,
                   'total_samples': total_s, 'total_violations': total_v,
                   'verdict': 'GREEN' if ok else 'RED'}, f, indent=1, default=str)
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
