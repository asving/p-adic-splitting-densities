#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
iterlawn_pe_reimpl.py -- ITERLAWN-PE (round-1 hostile pass on
lean/notes/openmath/ITERLAWN_PROOF_2026-08-08.md @4df7fdb), execution leg,
genre F2c: FROM-NOTE reimplementation, written BEFORE re-opening
verification/openmath/iterlawn_diag.py (sealed artifacts read-only, never
imported; nothing here shares code with the diag).

Everything below is coded from the note's displays alone:
  S0.1  class pin + canonical eps-corrected lifts (build via REALIZE-(m))
  S0.2  calculus: w_m, level reads, eq12, iterated split, anchors, cocycle
  S0.3  the (ITER-LAW-n) recursion: delta, S_j, D_j
  S2    SHIFT-(n) / D_j-INT / (STAR)-POS / WINDOW-(n) / descent of constants
  S4.1  REALIZE-(m) with the (I_m) DESCENT INVARIANT instrumented per call
  S4.3  (P-DS) digit shapes + the CII_r predicate
  S4.4  CASE-SPLIT-(n) (generic Case I / II-1 / II-2 / II-3 predicates)
  S4.6  (RM-m) box objects: R,Q by monic division; eps'-carry read clause
        + the II-leg substitution identities (structural form of E0new/E1new)
  S4.7  DCX_m detector (second-round Q-overflow) + the OUTER-BOUND predicate
        + the m=2 sharp form + the e_{m-2}>=3 CONJECTURE probe
  S6.3/S6.4  degenerations (passthrough, e_top=1 two-way tie), rho monodromy

FRESH instances (own seed; shapes disjoint from the diag's A4/B4/C3 reuse and
its T5A/T5B/T5C): three 4-read (rung 3, E4<=12), three 5-read (rung 4, E5<=12;
one DCX2-live, one level-3 middle cascade, one e0=1 & d0=2 corner), and one
6-read SMOKE (rung 5) -- the first 6-read data in the campaign.
Mutation controls (6) on the generic identities, visibility pre-verified.

Standing: instance evidence only; nothing here is a proof step.
"""
import sys, time, itertools

# ---------------- base rings O ----------------
class Zp:
    tag = 'Zp'
    def __init__(self, p): self.p = p
    def zero(self): return 0
    def one(self): return 1
    def add(self, a, b): return a + b
    def neg(self, a): return -a
    def mul(self, a, b): return a * b
    def is_zero(self, a): return a == 0
    def val(self, a):
        if a == 0: return None
        v = 0; p = self.p
        while a % p == 0:
            a //= p; v += 1
        return v
    def res(self, a, w):           # residue of a/pi^w in F_p (0 on strict excess)
        if a == 0: return 0
        return (a // self.p**w) % self.p
    def pi_pow(self, w): return self.p**w
    def liftk(self, c): return c % self.p

class Fpt:
    tag = 'Fpt'
    def __init__(self, p): self.p = p
    def _canon(self, L):
        while L and L[-1] == 0: L.pop()
        return tuple(L)
    def zero(self): return ()
    def one(self): return (1,)
    def add(self, a, b):
        n = max(len(a), len(b)); p = self.p
        return self._canon([((a[i] if i < len(a) else 0) +
                             (b[i] if i < len(b) else 0)) % p for i in range(n)])
    def neg(self, a): return tuple((-c) % self.p for c in a)
    def mul(self, a, b):
        if not a or not b: return ()
        p = self.p; out = [0]*(len(a)+len(b)-1)
        for i, ca in enumerate(a):
            if ca:
                for j, cb in enumerate(b):
                    out[i+j] = (out[i+j] + ca*cb) % p
        return self._canon(out)
    def is_zero(self, a): return a == ()
    def val(self, a):
        if not a: return None
        for i, c in enumerate(a):
            if c: return i
    def res(self, a, w): return a[w] if w < len(a) else 0
    def pi_pow(self, w): return (0,)*w + (1,)
    def liftk(self, c):
        c %= self.p
        return (c,) if c else ()

# ---------------- polynomials over O (tuples, trailing zeros stripped) ------
class PolyO:
    def __init__(self, R): self.R = R
    def canon(self, L):
        while L and self.R.is_zero(L[-1]): L.pop()
        return tuple(L)
    def zero(self): return ()
    def one(self): return (self.R.one(),)
    def deg(self, f): return len(f) - 1          # deg(0) = -1
    def add(self, f, g):
        n = max(len(f), len(g)); R = self.R
        return self.canon([R.add(f[i] if i < len(f) else R.zero(),
                                 g[i] if i < len(g) else R.zero()) for i in range(n)])
    def neg(self, f): return tuple(self.R.neg(c) for c in f)
    def sub(self, f, g): return self.add(f, self.neg(g))
    def mul(self, f, g):
        if not f or not g: return ()
        R = self.R; out = [R.zero()]*(len(f)+len(g)-1)
        for i, cf in enumerate(f):
            if not R.is_zero(cf):
                for j, cg in enumerate(g):
                    out[i+j] = R.add(out[i+j], R.mul(cf, cg))
        return self.canon(out)
    def scal(self, a, f): return self.canon([self.R.mul(a, c) for c in f])
    def pow(self, f, k):
        r = self.one()
        for _ in range(k): r = self.mul(r, f)
        return r
    def divmod_monic(self, f, Phi):
        # Phi monic; exact division algorithm in O[x] (note S0.2 base facts)
        R = self.R; d = len(Phi) - 1
        rem = list(f); q = [R.zero()]*max(1, len(f))
        for i in range(len(rem)-1, d-1, -1):
            c = rem[i]
            if R.is_zero(c): continue
            q[i-d] = c
            for j in range(d+1):
                rem[i-d+j] = R.add(rem[i-d+j], R.neg(R.mul(c, Phi[j])))
        return self.canon(q), self.canon(rem)
    def dev(self, f, Phi):
        # Phi-adic development [A_0, A_1, ...], deg A_i < deg Phi
        out = []
        while f:
            f, r = self.divmod_monic(f, Phi)
            out.append(r)
        return out

# ---------------- residue fields: GF(p) and successive extensions ----------
class GFp:
    def __init__(self, p): self.p = p
    def zero(self): return 0
    def one(self): return 1
    def add(self, a, b): return (a + b) % self.p
    def neg(self, a): return (-a) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def inv(self, a):
        assert a % self.p != 0
        return pow(a, self.p - 2, self.p)
    def is_zero(self, a): return a % self.p == 0
    def elems(self): return list(range(self.p))

class Ext:
    """K = base[y]/(mod); mod = tuple of base elems, monic, deg g >= 1.
    Elements: tuples of base elems, length exactly g."""
    def __init__(self, base, mod):
        self.base = base; self.mod = mod; self.g = len(mod) - 1
        assert self.g >= 1
    def zero(self): return (self.base.zero(),)*self.g
    def one(self):
        return (self.base.one(),) + (self.base.zero(),)*(self.g-1)
    def from_base(self, c):
        return (c,) + (self.base.zero(),)*(self.g-1)
    def add(self, a, b): return tuple(self.base.add(x, y) for x, y in zip(a, b))
    def neg(self, a): return tuple(self.base.neg(x) for x in a)
    def is_zero(self, a): return all(self.base.is_zero(x) for x in a)
    def reduce_list(self, L):
        B = self.base; g = self.g; L = list(L)
        if len(L) < g: L += [B.zero()]*(g - len(L))
        for d in range(len(L)-1, g-1, -1):
            c = L[d]
            if B.is_zero(c): continue
            L[d] = B.zero()
            for i in range(g):
                L[d-g+i] = B.add(L[d-g+i], B.neg(B.mul(c, self.mod[i])))
        return tuple(L[:g])
    def mul(self, a, b):
        B = self.base
        out = [B.zero()]*(2*self.g - 1)
        for i, x in enumerate(a):
            if not B.is_zero(x):
                for j, y in enumerate(b):
                    out[i+j] = B.add(out[i+j], B.mul(x, y))
        return self.reduce_list(out)
    def inv(self, a):
        # extended Euclid in base[y] against mod
        B = self.base
        def fpc(L):
            L = list(L)
            while L and B.is_zero(L[-1]): L.pop()
            return L
        def fpsub(f, g2):
            n = max(len(f), len(g2))
            return fpc([B.add(f[i] if i < len(f) else B.zero(),
                              B.neg(g2[i] if i < len(g2) else B.zero())) for i in range(n)])
        def fpmul(f, g2):
            if not f or not g2: return []
            out = [B.zero()]*(len(f)+len(g2)-1)
            for i, x in enumerate(f):
                if not B.is_zero(x):
                    for j, y in enumerate(g2):
                        out[i+j] = B.add(out[i+j], B.mul(x, y))
            return fpc(out)
        def fpdivmod(f, g2):
            f = list(f); q = [B.zero()]*max(1, len(f)); gl = B.inv(g2[-1])
            while len(fpc(f)) >= len(g2):
                f = fpc(f)
                c = B.mul(f[-1], gl); d = len(f) - len(g2)
                q[d] = B.add(q[d], c)
                sub = [B.zero()]*d + [B.mul(c, y) for y in g2]
                f = fpsub(f, sub)
            return fpc(q), fpc(f)
        r0, r1 = fpc(list(self.mod)), fpc(list(a))
        t0, t1 = [], [B.one()]
        assert r1, "inv(0)"
        while len(r1) > 1:
            q, r = fpdivmod(r0, r1)
            r0, r1 = r1, r
            t0, t1 = t1, fpsub(t0, fpmul(q, t1))
            assert r1, "not invertible (modulus not irreducible?)"
        c = B.inv(r1[0])
        t = [B.mul(c, x) for x in t1]
        return self.reduce_list(t)
    def elems(self):
        for tup in itertools.product(self.base.elems(), repeat=self.g):
            yield tuple(tup)

def fpow(F, z, k):
    if k < 0:
        return fpow(F, F.inv(z), -k)
    r = F.one()
    for _ in range(k): r = F.mul(r, z)
    return r

def eq12(beta, e, h):
    if e == 1:
        l, lp = 0, 1
    else:
        l = next(x for x in range(e) if (x*h) % e == 1)
        lp = (1 - l*h)//e
    s = (l*beta) % e
    u = (beta - s*h)//e
    assert u*e + s*h == beta
    return s, u

def bez(e, h):
    if e == 1: return 0, 1
    l = next(x for x in range(e) if (x*h) % e == 1)
    return l, (1 - l*h)//e

# ---------------- the tower (S0.1 construction, S0.2 calculus) --------------
class Tower:
    def __init__(self, name, R, d0, Phi0_spec, reads, psi_specs):
        """reads: list of (e_j,h_j,g_j), j=0..n (NR = n+1 reads, rung n).
        Phi0_spec: list of ints (coeffs, monic, deg d0), mapped via liftk.
        psi_specs[j]: list of coeff specs for psi_j (monic, len g_j+1);
        a coeff spec is an int (prime subfield) or ('z', lev, k) = z_lev^k."""
        self.name = name; self.R = R; self.P = PolyO(R)
        self.reads = reads; self.NR = len(reads); self.n = self.NR - 1
        self.e = [r[0] for r in reads]; self.h = [r[1] for r in reads]
        self.g = [r[2] for r in reads]
        for (e, h, g) in reads:
            assert e >= 1 and h >= 1 and g >= 1
            from math import gcd
            assert gcd(e, h) == 1
        self.l = [0]*self.NR; self.lp = [0]*self.NR
        for j in range(self.NR):
            self.l[j], self.lp[j] = bez(self.e[j], self.h[j])
        # weights (gamma_1 = h_0 uniformizing convention; w_0 Phi_0 := 0)
        self.gam = [None]*(self.NR+1); self.wPhi = [0]*(self.NR+1)
        self.gam[1] = self.h[0]
        self.wPhi[1] = self.e[0]*self.g[0]*self.gam[1]
        for j in range(1, self.NR):
            self.gam[j+1] = self.e[j]*self.wPhi[j] + self.h[j]
            if j+1 <= self.NR:
                self.wPhi[j+1] = self.e[j]*self.g[j]*self.gam[j+1] if j+1 <= self.NR else None
        # residue tower
        p = R.p
        self.k0 = GFp(p)
        Phi0 = tuple(R.liftk(c) for c in Phi0_spec)
        assert len(Phi0) == d0+1 and Phi0[-1] == R.one()
        self.d0 = d0
        phibar = tuple(R.res(c, 0) for c in Phi0)
        assert phibar[-1] == 1
        if d0 >= 2:  # reduction irreducible (deg<=3: no-root test suffices)
            assert d0 <= 3
            for a in self.k0.elems():
                v = 0
                for c in reversed(phibar): v = (v*a + c) % p
                assert v != 0, "phibar reducible"
        self.K = [None]*(self.NR+1)
        self.K[0] = Ext(self.k0, phibar)
        self.z = [None]*(self.NR+1)   # z[m] in K[m], m=1..NR
        self.psi = [None]*self.NR
        for j in range(self.NR):
            Kj = self.K[j]
            spec = psi_specs[j]
            cands = spec[1] if (isinstance(spec, tuple) and spec
                                and spec[0] == 'TRY') else [spec]
            psi = None
            for cand in cands:
                assert len(cand) == self.g[j] + 1
                trial = tuple(self._coeff(Kj, sp, j) for sp in cand)
                if trial[-1] != Kj.one(): continue
                if Kj.is_zero(trial[0]): continue
                if self.g[j] == 2:  # irreducibility by no-root (deg 2)
                    bad = False
                    for a in Kj.elems():
                        v = Kj.zero()
                        for c in reversed(trial):
                            v = Kj.add(Kj.mul(v, a), c)
                        if Kj.is_zero(v): bad = True; break
                    if bad: continue
                else:
                    assert self.g[j] == 1, "only g in {1,2} implemented"
                psi = trial; break
            assert psi is not None, "no valid psi_%d candidate" % j
            self.psi[j] = psi
            self.K[j+1] = Ext(Kj, psi)
            self.z[j+1] = self.K[j+1].reduce_list(
                [Kj.zero(), Kj.one()])
        # memos
        self._wmemo = {}; self._rmemo = {}; self._ememo = {}
        self._amemo = {}; self._smemo = {}
        # instrumentation counters (S4.1 (I_m) + R1/R2/R3)
        self.ct_Im = 0; self.ct_R123 = 0
        # canonical lifts Phi_1..Phi_n (S0.1; built via REALIZE-(m))
        self.Phi = [None]*self.NR
        self.Phi[0] = Phi0
        for m in range(0, self.n):
            self.Phi[m+1] = self._build_lift(m)
        # key gate: w_{m}(Phi_m) = e_{m-1} g_{m-1} gamma_m for all m>=1
        for m in range(1, self.n+1):
            assert self.wlev(m, self.Phi[m]) == self.wPhi[m], \
                "wPhi gate fails at level %d" % m
    def _coeff(self, Kj, sp, j):
        if isinstance(sp, int):
            c = self.k0.add(sp % self.k0.p, 0)
            x = self.K[0].from_base(c)
            return self.embed(x, 0, j)
        if sp[0] == 'X':
            X = self.K[0].reduce_list([self.k0.zero(), self.k0.one()])
            return self.embed(fpow(self.K[0], X, sp[1]), 0, j)
        tag, lev, k = sp
        assert tag == 'z' and 1 <= lev <= j
        x = fpow(self.K[lev], self.z[lev], k)
        return self.embed(x, lev, j)
    def embed(self, x, a, b):
        for l in range(a, b):
            x = self.K[l+1].from_base(x)
        return x
    # ---- eps_m (S0.2), m>=1 in K[m]; eps_0 := 1 in K[0]
    def eps(self, m, beta):
        key = (m, beta)
        if key in self._ememo: return self._ememo[key]
        if m == 0:
            r = self.K[0].one()
        else:
            s, u = eq12(beta, self.e[m-1], self.h[m-1])
            expo = self.lp[m-1]*s - self.l[m-1]*u
            r = fpow(self.K[m], self.z[m], expo)
        self._ememo[key] = r
        return r
    # ---- REALIZE-(m) (S4.1) with the (I_m) descent invariant instrumented
    def realize(self, m, tau, beta, check=True):
        res = self._realize(m, tau, beta)
        if check and not self.K[m].is_zero(tau):
            # R1/R2/R3 via the independent read machinery
            assert self.P.deg(res) < self.P.deg(self.Phi[m]) if m >= 1 else \
                   self.P.deg(res) < self.d0 or m == 0
            assert self.wlev(m, res) == beta, "R2 fails"
            assert self.read(m, beta, res) == tau, "R3 fails"
            self.ct_R123 += 1
        return res
    def _realize(self, m, tau, beta):
        R, P = self.R, self.P
        if m == 0:
            assert beta >= 0, "(I_0) violated"
            self.ct_Im += 1
            pw = R.pi_pow(beta)
            return P.canon([R.mul(pw, R.liftk(0) if c is None else self._liftO(c))
                            for c in tau])
        # (I_m): beta >= e_{m-1} g_{m-1} gamma_m
        assert beta >= self.e[m-1]*self.g[m-1]*self.gam[m], "(I_%d) violated" % m
        self.ct_Im += 1
        s, u = eq12(beta, self.e[m-1], self.h[m-1])
        out = P.zero()
        Km1 = self.K[m-1]
        for i, ti in enumerate(tau):
            if Km1.is_zero(ti): continue
            ki = s + i*self.e[m-1]
            num = beta - ki*self.gam[m]
            assert num % self.e[m-1] == 0
            gi = num // self.e[m-1]
            if m-1 >= 1:
                ti2 = Km1.mul(Km1.inv(self.eps(m-1, gi)), ti)
            else:
                ti2 = ti
            child = self._realize(m-1, ti2, gi)
            out = P.add(out, P.mul(child, P.pow(self.Phi[m-1], ki)))
        return out
    def _liftO(self, c):   # k0 elem (int) -> O
        return self.R.liftk(c)
    def _build_lift(self, m):
        # Phi_{m+1} = sum_{k<=g_m, psi_{m,k}!=0} C_k Phi_m^{e_m k}, C_{g_m}=1
        P = self.P
        out = P.pow(self.Phi[m], self.e[m]*self.g[m])
        for k in range(self.g[m]):
            ck = self.psi[m][k]
            if self.K[m].is_zero(ck): continue
            gp = (self.g[m]-k)*self.gam[m+1]
            if m >= 1:
                tau = self.K[m].mul(self.K[m].inv(self.eps(m, gp)), ck)
                Ck = self.realize(m, tau, gp)
            else:
                # m=0: eps_0 = 1; realize_0(tau,w) = lift(tau) pi^w
                Ck = self.realize(0, ck, gp)
            out = P.add(out, P.mul(Ck, P.pow(self.Phi[m], self.e[m]*k)))
        return out
    # ---- w_m and reads (S0.2)
    def wlev(self, m, f):
        if not f: return None
        key = (m, f)
        if key in self._wmemo: return self._wmemo[key]
        if m == 0:
            r = min(self.R.val(c) for c in f if not self.R.is_zero(c))
        else:
            dv = self.P.dev(f, self.Phi[m-1])
            r = min(self.e[m-1]*self.wlev(m-1, A) + j*self.gam[m]
                    for j, A in enumerate(dv) if A)
        self._wmemo[key] = r
        return r
    def read_coeffs(self, m, lam, f):
        """level-m read at line lam: dict grid-slot j -> C_j in K[m-1]-embedded
        form BEFORE z-packing (m>=1); requires w_m(f) >= lam."""
        assert m >= 1
        dv = self.P.dev(f, self.Phi[m-1])
        s, u = eq12(lam, self.e[m-1], self.h[m-1])
        out = {}
        for a in range(s, len(dv), self.e[m-1]):
            A = dv[a]
            if not A: continue
            num = lam - a*self.gam[m]
            assert num % self.e[m-1] == 0
            sw = num // self.e[m-1]
            wA = self.wlev(m-1, A)
            assert wA is not None and wA >= sw, "digit below its line"
            if wA == sw:
                r = self.read(m-1, sw, A)
                c = self.K[m-1].mul(self.eps(m-1, sw), r) if m-1 >= 1 else \
                    self.K[0].mul(self.eps(0, sw), r)
                j = (a - s)//self.e[m-1]
                out[j] = c
        return out
    def read(self, m, lam, f):
        key = (m, lam, f)
        if key in self._rmemo: return self._rmemo[key]
        if m == 0:
            # K_0-read at weight lam: res coefficientwise, mod phibar
            L = []
            for c in f:
                v = self.R.val(c)
                assert v is None or v >= lam, "coeff below line in read0"
                L.append(self.R.res(c, lam) if not self.R.is_zero(c) else 0)
            r = self.K[0].reduce_list(L)
        else:
            cs = self.read_coeffs(m, lam, f)
            r = self.K[m].zero()
            for j, c in cs.items():
                term = self.K[m].mul(self.embed(c, m-1, m),
                                     fpow(self.K[m], self.z[m], j))
                r = self.K[m].add(r, term)
        self._rmemo[key] = r
        return r
    # ---- split, window, anchors (S0.2)
    def split(self, gama):
        if gama in self._smemo: return self._smemo[gama]
        NR = self.NR
        s = [None]*(NR+1); u = [None]*(NR+1); beta = [None]*(NR)
        s[NR], u[NR] = eq12(gama, self.e[NR-1], self.h[NR-1])
        beta[NR-1] = u[NR] - s[NR]*self.wPhi[NR-1]
        for j in range(NR-1, 1, -1):
            s[j], u[j] = eq12(beta[j], self.e[j-1], self.h[j-1])
            beta[j-1] = u[j] - s[j]*self.wPhi[j-1]
        s[1], u[1] = eq12(beta[1], self.e[0], self.h[0])
        r = {'s': s, 'u': u, 'beta': beta, 'gamma': gama}
        self._smemo[gama] = r
        return r
    def inW(self, gama): return self.split(gama)['u'][1] >= 0
    def tanch(self, gama, r):
        """truncated anchor with reads 0..r (r = n gives the full anchor)."""
        key = (gama, r)
        if key in self._amemo: return self._amemo[key]
        sp = self.split(gama)
        P = self.P
        out = (self.R.pi_pow(sp['u'][1]),)
        for j in range(0, r+1):
            out = P.mul(out, P.pow(self.Phi[j], sp['s'][j+1]))
        self._amemo[key] = out
        return out
    def val_top(self, f, lev=None):
        lev = self.NR if lev is None else lev
        w = self.wlev(lev, f)
        return self.read(lev, w, f), w
    # ---- the S0.3 recursion constants (with mutation hooks)
    def constants(self, ga, gb, mut=None):
        mut = mut or set()
        sa, sb = self.split(ga), self.split(gb)
        NR = self.NR
        delta = (sa['s'][NR] + sb['s'][NR]) // self.e[NR-1]
        S = [None]*(NR+1); D = [None]*(NR+1)
        S[NR-1] = delta*self.gam[NR]
        for j in range(NR-1, 0, -1):
            defect = sa['s'][j] + sb['s'][j] - self.split(ga+gb)['s'][j]
            num = defect + (0 if 'M1' in mut else self.l[j-1]*S[j])
            intok = (num % self.e[j-1] == 0)
            D[j] = num // self.e[j-1] if intok else None
            wterm = self.wPhi[j-1]
            sgn = 1 if 'M3' in mut else -1
            S[j-1] = (D[j] if D[j] is not None else 0)*self.gam[j] + \
                     S[j]*(self.lp[j-1] + sgn*self.l[j-1]*wterm)
        return {'delta': delta, 'S': S, 'D': D,
                'dint_ok': all(D[j] is not None for j in range(1, NR))}

# ---------------- per-pair battery -----------------------------------------
def pair_data(T, ga, gb):
    """All note objects for the pair: splits, B_j, plain carries, CII chain,
    (P-DS) digits at every rung, case labels per level, DCX detectors."""
    NR = T.NR; P = T.P
    sa, sb, sc = T.split(ga), T.split(gb), T.split(ga+gb)
    d = {'sa': sa, 'sb': sb, 'sc': sc}
    d['B'] = [None]*NR
    for j in range(1, NR):
        d['B'][j] = sa['beta'][j] + sb['beta'][j]
    d['ssum'] = [None]*(NR+1); d['dpl'] = [None]*(NR+1)
    for j in range(1, NR+1):
        d['ssum'][j] = sa['s'][j] + sb['s'][j]
        d['dpl'][j] = d['ssum'][j] // T.e[j-1]
    # CII chain (S4.3): CII_1 = (g0=1 & dpl_1=1);
    # CII_r = (g_{r-1}=1) & (dpl_r=1 | (CII_{r-1} & ssum_r = e_{r-1}-1))
    CII = [None]*NR
    CII[1] = (T.g[0] == 1 and d['dpl'][1] == 1)
    for r in range(2, NR):
        CII[r] = (T.g[r-1] == 1) and \
                 (d['dpl'][r] == 1 or (CII[r-1] and d['ssum'][r] == T.e[r-1]-1))
    d['CII'] = CII
    # (P-DS) digits at rung r: Phi_r-dev of P_r = tanch(.,r) * tanch(.,r)
    d['E0'] = [None]*NR; d['E1'] = [None]*NR; d['devlen'] = [None]*NR
    d['support_ok'] = [None]*NR
    for r in range(1, NR):
        Pr = P.mul(T.tanch(ga, r), T.tanch(gb, r))
        dv = P.dev(Pr, T.Phi[r])
        ss = d['ssum'][r+1]
        d['E0'][r] = dv[ss] if ss < len(dv) else ()
        d['E1'][r] = dv[ss+1] if ss+1 < len(dv) else ()
        ok = all((not A) for j, A in enumerate(dv) if j not in (ss, ss+1))
        d['support_ok'][r] = ok
        d['devlen'][r] = len(dv)
        if r == NR-1: d['Ptop'] = Pr
    # case label per level m = 2..n (S4.4; on A := P_{m-1})
    d['case'] = [None]*NR; d['dcx'] = [False]*NR; d['dcx_any'] = [False]*NR
    d['rm_calls'] = []       # (m, which, f, lam) engine calls fired
    for m in range(2, NR):
        E1ih = d['E1'][m-1]; E0ih = d['E0'][m-1]
        ssm = d['ssum'][m]; dplm = d['dpl'][m]; em1 = T.e[m-1]
        Am = P.mul(T.tanch(ga, m-1), T.tanch(gb, m-1))
        overflow = (P.deg(Am) >= P.deg(T.Phi[m]))
        if T.g[m-1] != 1:
            case = 'I'
        elif not E1ih:
            case = 'II-1' if dplm == 1 else 'I'
        else:
            if dplm == 1: case = 'II-2'
            elif ssm == em1 - 1: case = 'II-3'
            else: case = 'I'
        d['case'][m] = case
        # CASE-SPLIT check: Case I <=> deg A < deg Phi_m
        d.setdefault('case_ok', {})[m] = ((case == 'I') == (not overflow))
        # DCX_m detector (S4.7): second-round Q-overflow of the E1-product
        if case in ('II-2', 'II-3'):
            Chat = P.sub(T.Phi[m], P.pow(T.Phi[m-1], em1))
            Q1, R1 = P.divmod_monic(P.mul(E1ih, Chat), T.Phi[m-1])
            k = ssm - em1
            if case == 'II-2':
                fires = bool(Q1) and (k+2 >= em1)
            else:
                fires = bool(Q1) and (em1 == 1)
            d['dcx'][m] = fires
        d['dcx_any'][m] = any(d['dcx'][2:m+1])
    d['dcx_pair'] = any(d['dcx'][2:NR])
    return d

def outer_pred(T, d, m):
    """DCX_m outer-bound predicate (S4.7): g_{m-1}=1, s_m(ga)=s_m(gb)=e_{m-1}-1,
    CII_{m-1} holds for the pair."""
    return (T.g[m-1] == 1 and
            d['sa']['s'][m] == T.e[m-1]-1 and d['sb']['s'][m] == T.e[m-1]-1 and
            (d['CII'][m-1] if m >= 2 else False))

def sharp2_pred(T, d):
    """[IL3] sharp DCX_2 ({g0=g1=1, dpl_1=1, s_2=s_2'=e_1-1, S_1+s(gam_2)>=2e_0});
    S_1 = s_1+s_1' slot sum, s(gam_2) = level-1 eq12 s of gamma_2."""
    if not (T.g[0] == 1 and T.g[1] == 1): return False
    s_g2, _ = eq12(T.gam[2], T.e[0], T.h[0])
    return (d['dpl'][1] == 1 and
            d['sa']['s'][2] == T.e[1]-1 and d['sb']['s'][2] == T.e[1]-1 and
            d['ssum'][1] + s_g2 >= 2*T.e[0])

def expected_E0_read(T, d, r):
    """(P-DS): R_r v(E0) = prod_{j<=r} z_j^{dpl_j} * prod_{j<=r-1} eps_j(B_j)."""
    acc = T.K[r].one()
    for j in range(1, r+1):
        acc = T.K[r].mul(acc, T.embed(fpow(T.K[j], T.z[j], d['dpl'][j]), j, r))
    for j in range(1, r):
        acc = T.K[r].mul(acc, T.embed(T.eps(j, d['B'][j]), j, r))
    return acc

def check_pair(T, ga, gb, C, muts=None, viol=None):
    """Run the full battery on one ordered pair; C = counters dict."""
    muts = muts or set(); viol = viol if viol is not None else []
    NR = T.NR; n = T.n; P = T.P
    d = pair_data(T, ga, gb)
    cst = T.constants(ga, gb, mut=muts)
    sc = d['sc']

    def V(tagc, msg):
        viol.append('%s %s (%d,%d): %s' % (T.name, tagc, ga, gb, msg))

    # K1 SHIFT-(n): beta_j'' = B_j + S_j, all j (mut M2 drops S_j)
    for j in range(1, NR):
        rhs = d['B'][j] + (0 if 'M2' in muts else cst['S'][j])
        C['K1_shift'] += 1
        if sc['beta'][j] != rhs: V('K1', 'SHIFT fails at j=%d' % j)
    # K2 D-INT
    C['K2_dint'] += 1
    if not cst['dint_ok']: V('K2', 'D_j not integral')
    # K3 (STAR)-POS: S_j = 0 or e_j S_j >= gamma_{j+1}  (mut M5v tightens)
    for j in range(1, NR):
        C['K3_star'] += 1
        Sj = cst['S'][j]
        thr = T.gam[j+1]
        ok = (Sj == 0) or (Sj > 0 and T.e[j]*Sj >= thr)
        if not ok: V('K3', '(STAR) fails at j=%d (S=%d)' % (j, Sj))
        if Sj < 0: V('K3', 'S_%d negative' % j)
        if Sj > 0 and T.e[j]*Sj == thr: C['K3_star_eq'] += 1
    # K4 WINDOW
    C['K4_window'] += 1
    if not T.inW(ga+gb): V('K4', 'window not closed under +')
    # K13 passthrough at e_{j-1}=1: D_j=0 and S_{j-1}=S_j
    for j in range(1, NR):
        if T.e[j-1] == 1:
            C['K13_pass'] += 1
            if not (cst['D'][j] == 0 and cst['S'][j-1] == cst['S'][j]):
                V('K13', 'passthrough fails at j=%d' % j)
    # value layer -----------------------------------------------------------
    dcx_pair = d['dcx_pair']
    vala, wa = T.val_top(T.tanch(ga, n)); valb, wb = T.val_top(T.tanch(gb, n))
    valc, wc = T.val_top(T.tanch(ga+gb, n))
    # K5 L6-(n) on ga (per-pair harmless; memoized)
    exp6 = T.K[NR].one()
    for j in range(1, NR):
        exp6 = T.K[NR].mul(exp6, T.embed(T.eps(j, T.split(ga)['beta'][j]), j, NR))
    C['K5_l6'] += 1
    if not (vala == exp6 and wa == ga): V('K5', 'L6 fails')
    # K6 W-MULT top: val(P) = z_top^{dpl_top} val val; single top slot; w = sum
    Ptop = d['Ptop']; wp = T.wlev(NR, Ptop)
    C['K6_wmult'] += 1
    delta = cst['delta']
    if wp != ga+gb: V('K6', 'w(P) != gamma+gamma\'')
    else:
        vp = T.read(NR, wp, Ptop)
        expw = T.K[NR].mul(fpow(T.K[NR], T.z[NR], d['dpl'][NR]),
                           T.K[NR].mul(vala, valb))
        if vp != expw:
            (V if not dcx_pair else lambda a, b: C.__setitem__(
                'ONDCX_wmult_bad', C['ONDCX_wmult_bad']+1))('K6', 'W-MULT value fails')
        cs = T.read_coeffs(NR, wp, Ptop)
        nz = [j for j, c in cs.items() if not T.K[NR-1].is_zero(c)]
        if nz != [delta]:
            (V if not dcx_pair else lambda a, b: None)('K6', 'top slots %s != [delta]' % nz)
    # K7 THE LAW: c_{n+1} = zbar^delta prod z_j^{D_j}   (muts M1/M3/M4 visible)
    C['K7_law'] += 1
    if wp == ga+gb and wc == ga+gb:
        vp = T.read(NR, wp, Ptop)
        c_meas = T.K[NR].mul(vp, T.K[NR].inv(valc))
        dtop = (1 - delta) if 'M4' in muts else delta
        if 'M4' in muts and fpow(T.K[NR], T.z[NR], 1-delta) != \
                fpow(T.K[NR], T.z[NR], delta):
            C['K7_vis'] += 1
        expl = fpow(T.K[NR], T.z[NR], dtop)
        for j in range(1, NR):
            Dj = cst['D'][j] if cst['D'][j] is not None else 0
            expl = T.K[NR].mul(expl, T.embed(fpow(T.K[j], T.z[j], Dj), j, NR))
        if c_meas != expl:
            if dcx_pair:
                C['ONDCX_law_bad'] += 1
            else:
                V('K7', 'LAW fails')
        elif dcx_pair:
            C['ONDCX_law_ok'] += 1
    else:
        V('K7', 'weights wrong for law')
    return d, cst, viol

def deep_checks(T, ga, gb, d, cst, C, muts, viol):
    """K8 (P-DS), K9/K9b CASE-SPLIT + substitution identities, K10 DCX outer
    bound + censuses + conjecture probes, K11 (RM-m) box instance checks."""
    NR = T.NR; n = T.n; P = T.P
    def V(tagc, msg):
        viol.append('%s %s (%d,%d): %s' % (T.name, tagc, ga, gb, msg))
    # ---- K8 (P-DS) at every rung r (package clauses; OFF DCX-(r))
    for r in range(1, NR):
        dcx_r = any(d['dcx'][2:r+1])
        Br = d['B'][r]
        E0, E1 = d['E0'][r], d['E1'][r]
        if dcx_r:
            C['K8_skipped_dcx'] += 1
        else:
            C['K8_pds'] += 1
            if not d['support_ok'][r]: V('K8', 'slot support r=%d' % r)
            if not E0:
                V('K8', 'E0=0 at r=%d' % r)
            else:
                if T.wlev(r, E0) != Br:
                    V('K8', 'w(E0)!=B_r at r=%d' % r)
                elif T.read(r, Br, E0) != expected_E0_read(T, d, r):
                    V('K8', 'E0 certified read fails at r=%d' % r)
            if E1:
                bound = Br - T.e[r-1]*T.gam[r] + (1 if 'M7' in muts else 0)
                w1 = T.wlev(r, E1)
                C['K8_e1'] += 1
                if w1 < bound: V('K8', 'w(E1) < B_r - e gam at r=%d' % r)
                if w1 == Br - T.e[r-1]*T.gam[r]: C['K8_e1_weq'] += 1
                if not d['CII'][r]: V('K8', 'E1!=0 but CII_%d false' % r)
    # ---- K9 CASE-SPLIT + K9b substitution identities, levels m=2..n
    for m in range(2, NR):
        dcx_below = any(d['dcx'][2:m])
        if not dcx_below:
            C['K9_case'] += 1
            if not d['case_ok'][m]:
                V('K9', 'CASE-SPLIT mismatch at m=%d (case %s)' % (m, d['case'][m]))
        case = d['case'][m]
        C['census_case_%s_m%d' % (case, m)] += 1
        if case in ('II-1', 'II-2', 'II-3') and not any(d['dcx'][2:m+1]):
            em1 = T.e[m-1]; ss = d['ssum'][m]; k = ss - em1
            Phim1 = T.Phi[m-1]
            Chat = P.sub(T.Phi[m], P.pow(Phim1, em1))
            E0ih, E1ih = d['E0'][m-1], d['E1'][m-1]
            E0n, E1n = d['E0'][m], d['E1'][m]
            ok = True
            if case == 'II-1':
                Q, Rr = P.divmod_monic(P.mul(E0ih, Chat), Phim1)
                ok = (E1n == P.mul(E0ih, P.pow(Phim1, k)) and
                      E0n == P.neg(P.add(P.mul(Rr, P.pow(Phim1, k)),
                                         P.mul(Q, P.pow(Phim1, k+1)))))
            elif case == 'II-2':
                Q0, R0 = P.divmod_monic(P.mul(E0ih, Chat), Phim1)
                Q1, R1 = P.divmod_monic(P.mul(E1ih, Chat), Phim1)
                ok = (E1n == P.add(P.mul(E1ih, P.pow(Phim1, k+1)),
                                   P.mul(E0ih, P.pow(Phim1, k))) and
                      E0n == P.neg(P.add(P.add(P.mul(R0, P.pow(Phim1, k)),
                                     P.mul(P.add(Q0, R1), P.pow(Phim1, k+1))),
                                     P.mul(Q1, P.pow(Phim1, k+2)))))
            else:  # II-3
                Q1, R1 = P.divmod_monic(P.mul(E1ih, Chat), Phim1)
                ok = (E1n == E1ih and
                      E0n == P.sub(P.sub(P.mul(E0ih, P.pow(Phim1, em1-1)), R1),
                                   P.mul(Q1, Phim1)))
            C['K9b_subst'] += 1
            if not ok: V('K9b', 'substitution identity fails at m=%d %s' % (m, case))
    # ---- K10 DCX detector vs outer bound; censuses; conjecture probes
    for m in range(2, NR):
        if outer_pred(T, d, m): C['census_outer_m%d' % m] += 1
        if d['dcx'][m]:
            C['census_dcx_m%d' % m] += 1
            if not any(d['dcx'][2:m]):
                C['K10_outer'] += 1
                if not outer_pred(T, d, m):
                    V('K10', 'DCX_%d fires OUTSIDE the outer bound' % m)
            if m == 2 and T.e[0] <= 2:
                V('K10', 'DCX_2 nonempty at e0<=2 (contradicts [IL3] sharp emptiness)')
            if m >= 3 and T.e[m-2] <= 2:
                C['CONJ_dcx_at_small_e'] += 1
                viol.append('%s NOTE-CONJ (%d,%d): DCX_%d fires with e_%d=%d<=2 '
                            '(refutes the S4.7 e_{m-2}>=3 CONJECTURE)' %
                            (T.name, ga, gb, m, m-2, T.e[m-2]))
        if m == 2:
            C['K10_sharp2'] += 1
            if d['dcx'][2] != sharp2_pred(T, d):
                V('K10', 'DCX_2 detector != [IL3] sharp form (det=%s)' % d['dcx'][2])
            if sharp2_pred(T, d): C['census_sharp2'] += 1
    # ---- K11 (RM-m) box instance checks at every fired engine call
    for m in range(2, NR):
        case = d['case'][m]
        if case not in ('II-1', 'II-2', 'II-3'): continue
        mu = m - 1
        Chat = P.sub(T.Phi[m], P.pow(T.Phi[m-1], T.e[m-1]))
        calls = []
        if case in ('II-1', 'II-2'): calls.append(d['E0'][m-1])
        if case in ('II-2', 'II-3'): calls.append(d['E1'][m-1])
        for f in calls:
            if not f: continue
            lam = T.wlev(mu, f)
            v = T.read(mu, lam, f)
            if T.K[mu].is_zero(v): continue   # box needs the on-line read
            Q, Rr = P.divmod_monic(P.mul(f, Chat), T.Phi[mu])
            gmp1 = T.gam[mu+1]
            tag = 'K11_rm1' if mu == 1 else 'K11_rm%d' % mu
            if mu == 1 and T.e[0] == 1 and T.d0 >= 2: tag += '_corner'
            C[tag] += 1
            assert P.deg(Q) < P.deg(T.Phi[mu])
            if not Rr:
                V('K11', 'R=0 at engine level %d' % mu); continue
            if T.wlev(mu, Rr) < lam + gmp1:
                V('K11', 'w(R) < lam+gamma at level %d' % mu)
                continue
            smu_l, _ = eq12(lam, T.e[mu-1], T.h[mu-1])
            smu_g, _ = eq12(gmp1, T.e[mu-1], T.h[mu-1])
            epr = (smu_l + smu_g) // T.e[mu-1]
            if epr != 0 and T.z[mu] != T.K[mu].one(): C['K11_eps_vis'] += 1
            cmu = T.psi[mu][0]
            tau = T.K[mu].mul(T.K[mu].inv(T.eps(mu, gmp1)), cmu)
            expo = 0 if 'M5' in muts else epr
            expect = T.K[mu].mul(fpow(T.K[mu], T.z[mu], expo),
                                 T.K[mu].mul(v, tau))
            if T.read(mu, lam + gmp1, Rr) != expect:
                V('K11', 'R read clause fails at level %d (eps\'=%d)' % (mu, epr))
            if Q:
                C[tag + '_q'] += 1
                if T.wlev(mu, Q) < lam + gmp1 - T.wPhi[mu]:
                    V('K11', 'w(Q) clause fails at level %d' % mu)

def gamma_checks(T, ga, C, muts, viol):
    """K12 descent/rho/pi-shift (per gamma; S2 descent lemma + S6.4)."""
    n = T.n; NR = T.NR; P = T.P
    E = 1
    for e in T.e: E *= e
    def V(tagc, msg):
        viol.append('%s %s (%d): %s' % (T.name, tagc, ga, msg))
    C['K12_pi'] += 1
    lhs = T.tanch(ga+E, n)
    rhs = P.scal(T.R.pi_pow(1), T.tanch(ga, n))
    if lhs != rhs: V('K12', 'phi_{g+E} != pi phi_g')
    va, wa = T.val_top(T.tanch(ga, n))
    vE, wE = T.val_top(lhs)
    sgn = 1 if 'M6' in muts else -1
    rho = T.K[NR].one(); rho_b = T.K[NR].one()
    Pi = 1
    for j in range(1, NR):
        rho = T.K[NR].mul(rho, T.embed(fpow(T.K[j], T.z[j],
                                            sgn*T.l[j-1]*Pi), j, NR))
        rho_b = T.K[NR].mul(rho_b, T.embed(fpow(T.K[j], T.z[j],
                                               -T.l[j-1]*Pi), j, NR))
        Pi *= T.e[j-1]
    if 'M6' in muts and rho != rho_b: C['K12_rho_vis'] += 1
    C['K12_rho'] += 1
    if vE != T.K[NR].mul(rho, va): V('K12', 'rho monodromy fails')

# ---------------- instance driver ------------------------------------------
def build_tower(spec):
    R = Zp(spec['p']) if spec['ring'] == 'Zp' else Fpt(spec['p'])
    psis = []
    for ps in spec['psi']:
        psis.append(ps)
    name = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
    return Tower(name, R, spec['d0'], spec['Phi0'], spec['reads'], psis)

def window_reps(T, count=None):
    # constants descend to Z/E (S2 descent lemma): sample the smallest
    # in-window representative of EVERY residue class mod E = e_0...e_n
    E = 1
    for e in T.e: E *= e
    out = []
    for r0 in range(E):
        g = r0
        while not T.inW(g): g += E
        out.append(g)
    out.sort()
    return out[:count] if count else out

def run_instance(spec, muts=frozenset(), pairn=None, quiet=False):
    import collections
    t0 = time.time()
    T = build_tower(spec)
    C = collections.defaultdict(int)
    viol = []
    W1 = window_reps(T, pairn or spec['pairn'])
    # e_top = 1 two-way tie companion (S6.3; K15)
    T2 = None
    if T.e[T.n] == 1:
        spec2 = dict(spec); spec2 = {**spec, 'reads': spec['reads'][:-1],
                                     'psi': spec['psi'][:-1], 'id': spec['id']+'-tr'}
        T2 = build_tower(spec2)
    for ga in W1:
        gamma_checks(T, ga, C, muts, viol)
        for gb in W1:
            d, cst, _ = check_pair(T, ga, gb, C, muts=muts, viol=viol)
            deep_checks(T, ga, gb, d, cst, C, muts, viol)
            # K12c constants descend mod E (first partner only)
            if gb == W1[0]:
                E = 1
                for e in T.e: E *= e
                c2 = T.constants(ga+E, gb, mut=muts)
                C['K12_constdesc'] += 1
                if not (c2['delta'] == cst['delta'] and c2['S'] == cst['S']
                        and c2['D'] == cst['D']):
                    viol.append('%s K12c (%d,%d): constants move under +E' %
                                (T.name, ga, gb))
            # K15 two-way tie at e_top=1
            if T2 is not None:
                ba = T.split(ga)['beta'][T.n]; bb = T.split(gb)['beta'][T.n]
                C['K15_tie'] += 1
                cst2 = T2.constants(ba, bb)
                ok = (cst['delta'] == 0 and cst['S'][T.n] == 0 and
                      cst['D'][T.n] == d['dpl'][T.n] and
                      all(cst['D'][j] == cst2['D'][j] for j in range(1, T.n)) and
                      all(cst['S'][j] == cst2['S'][j] for j in range(0, T.n)))
                if not ok:
                    viol.append('%s K15 (%d,%d): constants tie fails' % (T.name, ga, gb))
                # value tie
                P2 = T2.P.mul(T2.tanch(ba, T2.n), T2.tanch(bb, T2.n))
                w2 = T2.wlev(T2.NR, P2)
                vC2 = T2.read(T2.NR, w2, P2)
                v2c, _ = T2.val_top(T2.tanch(ba+bb, T2.n))
                c2v = T2.K[T2.NR].mul(vC2, T2.K[T2.NR].inv(v2c))
                Ptop = T.P.mul(T.tanch(ga, T.n), T.tanch(gb, T.n))
                wt = T.wlev(T.NR, Ptop)
                vt = T.read(T.NR, wt, Ptop)
                vc, _ = T.val_top(T.tanch(ga+gb, T.n))
                c1v = T.K[T.NR].mul(vt, T.K[T.NR].inv(vc))
                C['K15_valtie'] += 1
                if c1v != T.embed(c2v, T.NR-1, T.NR):
                    viol.append('%s K15v (%d,%d): value tie fails' % (T.name, ga, gb))
    C['pairs'] = len(W1)**2
    C['Im_asserts'] = T.ct_Im; C['R123'] = T.ct_R123
    el = time.time() - t0
    if not quiet:
        E = 1
        for e in T.e: E *= e
        print('-- %s: %d reads (rung %d), E=%d, d0=%d, |W1|=%d, pairs=%d, %.1fs'
              % (T.name, T.NR, T.n, E, T.d0, len(W1), C['pairs'], el))
        cens = {k: v for k, v in sorted(C.items())
                if k.startswith('census') or k.startswith('CONJ')}
        print('   censuses: %s' % dict(cens))
        keyct = {k: v for k, v in sorted(C.items())
                 if k.startswith('K') and not k.startswith('K11_eps')}
        print('   checks:   %s' % dict(keyct))
        if viol:
            print('   VIOLATIONS (%d):' % len(viol))
            for v in viol[:12]: print('     ' + v)
    return T, C, viol

INSTANCES = [
 dict(id='I4A', ring='Zp', p=2, d0=1, Phi0=[0, 1],
      reads=[(2,1,1),(2,1,1),(1,1,2),(3,2,1)],
      psi=[[1,1],[1,1],[1,1,1],[('z',3,1),1]], pairn=12),
 dict(id='I4B', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(3,2,1),(2,1,1),(1,1,2),(2,1,1)],
      psi=[[1,1],[1,1],[1,0,1],[('z',3,1),1]], pairn=14),
 dict(id='I4C', ring='Fpt', p=2, d0=2, Phi0=[1, 1, 1],
      reads=[(2,1,1),(1,1,2),(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('X',1),1,1],[('z',2,1),1],[('z',2,1),1]], pairn=12),
 dict(id='I5A', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(3,2,1),(2,1,1),(1,1,2),(2,1,1),(1,1,1)],
      psi=[[1,1],[1,1],[1,0,1],[('z',3,1),1],[('z',3,1),1]], pairn=12),
 dict(id='I5A', ring='Fpt', p=3, d0=1, Phi0=[0, 1],
      reads=[(3,2,1),(2,1,1),(1,1,2),(2,1,1),(1,1,1)],
      psi=[[1,1],[1,1],[1,0,1],[('z',3,1),1],[('z',3,1),1]], pairn=10),
 dict(id='I5B', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(2,1,1),(1,1,1),(3,1,1),(1,1,2),(2,1,1)],
      psi=[[1,1],[1,1],[1,1],[1,0,1],[('z',4,1),1]], pairn=12),
 dict(id='I5B', ring='Fpt', p=3, d0=1, Phi0=[0, 1],
      reads=[(2,1,1),(1,1,1),(3,1,1),(1,1,2),(2,1,1)],
      psi=[[1,1],[1,1],[1,1],[1,0,1],[('z',4,1),1]], pairn=10),
 dict(id='I5C', ring='Fpt', p=2, d0=2, Phi0=[1, 1, 1],
      reads=[(1,1,2),(2,1,1),(2,1,1),(1,1,2),(2,1,1)],
      psi=[[('X',1),1,1],[('z',1,1),1],[('z',1,1),1],
           ('TRY', [[('z',1,1),1,1],[('z',1,3),1,1],[('z',1,5),1,1],
                    [('z',1,7),1,1],[('X',1),1,1],[('z',1,6),1,1]]),
           [('z',4,1),1]], pairn=8),
 dict(id='I6S', ring='Zp', p=3, d0=1, Phi0=[0, 1],
      reads=[(2,1,1),(1,1,1),(2,1,1),(1,1,2),(1,1,1),(2,1,1)],
      psi=[[1,1],[1,1],[1,1],[1,0,1],[('z',4,1),1],[('z',4,1),1]], pairn=6),
]

MUTATIONS = [
 ('M1', 'D_j drops the l_{j-1} S_j term (S0.3 recursion)'),
 ('M2', 'SHIFT check drops S_j (beta\'\' = B_j)'),
 ('M3', 'composed shift sign flip: l\'+l*wPhi for l\'-l*wPhi'),
 ('M4', 'law top exponent delta -> 1-delta'),
 ('M5', '(RM-m) read clause drops the z^{eps\'} carry factor'),
 ('M6', 'rho monodromy exponent sign flip'),
 ('M7', '(P-DS) E1 weight bound tightened by +1'),
]

def main():
    t00 = time.time()
    print('iterlawn_pe_reimpl -- ITERLAWN-PE round-1 FROM-NOTE reimplementation')
    print('(hostile execution leg on ITERLAWN_PROOF_2026-08-08.md @4df7fdb;'
          ' instance evidence only)')
    print()
    print('== FRESH-INSTANCE BATTERY (baseline, no mutations) ==')
    import collections
    TOT = collections.defaultdict(int); all_viol = []
    for spec in INSTANCES:
        T, C, viol = run_instance(spec)
        for k, v in C.items(): TOT[k] += v
        all_viol += viol
    print()
    print('== TOTALS ==')
    for k in sorted(TOT): print('  %-22s %d' % (k, TOT[k]))
    print('== BASELINE VIOLATIONS: %d ==' % len(all_viol))
    for v in all_viol: print('   ' + v)
    print()
    print('== MUTATION CONTROLS (subset: I4B@Zp, I4C@Fpt; catch = violations>0) ==')
    sub = [INSTANCES[1], INSTANCES[2]]   # I4B@Zp3 + I4C@Fpt2
    mut_ok = 0; mut_rows = []
    for flag, desc in MUTATIONS:
        nv = 0; vis = 0
        for spec in sub:
            T, C, viol = run_instance(spec, muts={flag}, pairn=8, quiet=True)
            nv += len(viol)
            if flag in ('M1', 'M2', 'M3'):
                W1 = window_reps(T, 8)
                for ga in W1:
                    for gb in W1:
                        cb = T.constants(ga, gb)
                        cm = T.constants(ga, gb, mut={flag})
                        if flag == 'M2':
                            if any(s != 0 for s in cb['S'][1:T.NR]): vis += 1
                        elif cb['S'] != cm['S'] or cb['D'] != cm['D']:
                            vis += 1
            elif flag == 'M4':
                vis += C['K7_vis']
            elif flag == 'M5':
                vis += C['K11_eps_vis']
            elif flag == 'M6':
                vis += C['K12_rho_vis']
            elif flag == 'M7':
                vis += C['K8_e1_weq']
        caught = nv > 0
        if caught and vis > 0: mut_ok += 1
        mut_rows.append((flag, desc, vis, nv, 'CAUGHT' if caught else 'MISSED'))
        print('  %-3s vis=%-5d viol=%-5d %-7s %s' % (flag, vis, nv,
              'CAUGHT' if caught else 'MISSED', desc))
    print()
    ok = (len(all_viol) == 0)
    print('== VERDICT: baseline violations = %d; mutations caught+visible = %d/%d;'
          ' elapsed %.1fs ==' % (len(all_viol), mut_ok, len(MUTATIONS),
                                 time.time() - t00))
    print('REIMPL VERDICT: %s' % ('CLEAN' if ok and mut_ok >= 4 else 'NOT CLEAN'))
    return 0 if ok and mut_ok >= 4 else 1

if __name__ == '__main__':
    sys.exit(main())
