#!/usr/bin/env python3
"""TAMEK battery — roots of random monic p-adic polynomials in a fixed tame extension K.

Two-commit seal protocol: commit 1 seals this runner UNRUN (predictions preregistered,
dump via --prereg); commit 2 appends the verdict from the artifacts.

Families:
  TK0    exact: brute-force #Hom(L,K) (root count of L's minimal polynomial in K via
         exact O_K arithmetic + recursive Hensel subdivision) == LEMMA TK-0's formula.
  TKQ    exact n=2 law (THEOREM TK-Q) vs Monte Carlo; and X in {0,2} only.
  N3     exact n=3 anchors (S3, menu x TK-0 x TK-3) vs Monte Carlo.
  DIP    the ram-quad dip E(3) < E(2) and recovery E(7) > E(3).
  LIM    mean-law consistency at the largest measured n (CONJ-MEAN limit values).
  SPLIT  the (2,2) letter separation (c=0 vs c=1), exact at n=2, persistent at n=7.
  LEQ    twist-blindness of (2,1) and (3,1) cells (equal means across twists).
  TEETH  T1 wrong-twist TK-0; T2 mass-blind mean; T3 letter-blind (2,2) mean;
         T4 tame-blind (shallow-band-root-free) mean. All must bite.

PRE-SEAL SMOKE DISCLOSURE: one --smoke pass (300 samples/cell, full grid) ran before
seal: all exact TK0 rows and all sufficiently-powered MC rows PASS; the 5 rows failing
at smoke are the DIP/SPLIT-n=7 power-limited rows (SE ~ 15x larger than the scoring
run's); teeth 4/4 bit at smoke. No full-sample run before seal. MC tolerances are
5-sigma bands (empirical SE); LIM bands are consistency bands max(5 sigma, 0.04*(1+E)),
labeled as such (finite-n vs limit, not identity claims).
"""
import argparse, json, math, os, random, sys, time
from fractions import Fraction
from multiprocessing import Pool

PREC = 64          # p-adic precision: work mod p^PREC
DEPTH_CAP = 30     # recursion depth cap for root subdivision
VMARGIN = 8        # precision safety margin (pi-digits at unramified level)

class Retry(Exception):
    pass

# ---------------------------------------------------------------- residue field F_Q
class FQ:
    """F_Q = F_p[t]/(mbar), elements = tuples of f ints mod p."""
    def __init__(self, p, f, mbar):
        self.p, self.f, self.mbar = p, f, tuple(mbar)  # mbar: monic deg f, coeffs low->high, len f+1
        self.zero = (0,)*f
        self.one = tuple([1]+[0]*(f-1)) if f >= 1 else ()
        self.elems = self._all()
        self.Q = p**f
    def _all(self):
        p, f = self.p, self.f
        out = []
        for k in range(p**f):
            e, kk = [], k
            for _ in range(f):
                e.append(kk % p); kk //= p
            out.append(tuple(e))
        return out
    def add(self, a, b): return tuple((x+y) % self.p for x, y in zip(a, b))
    def neg(self, a): return tuple((-x) % self.p for x in a)
    def mul(self, a, b):
        p, f, m = self.p, self.f, self.mbar
        prod = [0]*(2*f-1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i+j] = (prod[i+j] + x*y) % p
        for k in range(2*f-2, f-1, -1):
            c = prod[k]
            if c:
                prod[k] = 0
                for j in range(f):
                    prod[k-f+j] = (prod[k-f+j] - c*m[j]) % p
        return tuple(prod[:f])
    def pow(self, a, n):
        r, b = self.one, a
        while n:
            if n & 1: r = self.mul(r, b)
            b = self.mul(b, b); n >>= 1
        return r
    def is_gen(self, a):
        if a == self.zero: return False
        n = self.Q - 1
        for d in set(_prime_divs(n)):
            if self.pow(a, n//d) == self.one: return False
        return True
    def generator(self):
        for a in self.elems:
            if self.is_gen(a): return a
        raise RuntimeError("no generator")
    def poly_eval(self, coeffs, x):
        r = self.zero
        for c in reversed(coeffs):
            r = self.add(self.mul(r, x), c)
        return r

def _prime_divs(n):
    out, d = [], 2
    while d*d <= n:
        while n % d == 0:
            out.append(d); n //= d
        d += 1
    if n > 1: out.append(n)
    return out

IRRED = {  # monic irreducible over F_p, coeffs low->high (constant first), degree f
    (3,1): [0,1], (5,1): [0,1], (7,1): [0,1],
    (3,2): [1,0,1],            # t^2+1 irred mod 3
    (5,2): [2,0,1],            # t^2+2 irred mod 5
    (7,2): [1,0,1],            # t^2+1 irred mod 7 (-1 non-square mod 7)
    (3,3): [1,2,0,1],          # t^3+2t+1 irred mod 3
}

# ---------------------------------------------------------------- O_K arithmetic
class TameK:
    """K tame over Q_p: type (e,f,c). O_K = O_ur[beta]/(beta^e - u*p),
    O_ur = Z_p[t]/(m(t)) mod p^PREC, u = lift of gQ^c (gQ = fixed generator of F_Q^*).
    Elements: tuple of e components, each a tuple of f ints mod p^PREC."""
    def __init__(self, p, e, f, c):
        self.p, self.e, self.f, self.c = p, e, f, c
        self.q = p
        self.mod = p**PREC
        mlift = IRRED[(p, f)]
        self.m = tuple(mlift)                       # integer lift, monic deg f
        self.fq = FQ(p, f, [x % p for x in mlift])
        self.gQ = self.fq.generator()
        ubar = self.fq.pow(self.gQ, c)
        self.u = tuple(int(x) for x in ubar)        # lift of gQ^c into O_ur
        self.zero = tuple(tuple(0 for _ in range(f)) for _ in range(e))
        one_ur = tuple([1]+[0]*(f-1))
        self.one = tuple([one_ur] + [tuple([0]*f)]*(e-1))
    # --- O_ur ops
    def ur_add(self, a, b): return tuple((x+y) % self.mod for x, y in zip(a, b))
    def ur_sub(self, a, b): return tuple((x-y) % self.mod for x, y in zip(a, b))
    def ur_mul(self, a, b):
        f, M, m = self.f, self.mod, self.m
        prod = [0]*(2*f-1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i+j] = (prod[i+j] + x*y) % M
        for k in range(2*f-2, f-1, -1):
            cc = prod[k]
            if cc:
                prod[k] = 0
                for j in range(f):
                    prod[k-f+j] = (prod[k-f+j] - cc*m[j]) % M
        return tuple(prod[:f])
    def ur_vp(self, a):
        v = PREC
        for x in a:
            if x:
                w = 0
                while x % self.p == 0:
                    x //= self.p; w += 1
                if w < v: v = w
        return v
    def ur_divp(self, a, k):
        pk = self.p**k
        return tuple(x // pk for x in a)   # exact by construction (rep divisible)
    # --- O_K ops
    def add(self, z, w): return tuple(self.ur_add(a, b) for a, b in zip(z, w))
    def sub(self, z, w): return tuple(self.ur_sub(a, b) for a, b in zip(z, w))
    def mul(self, z, w):
        e = self.e
        comps = [tuple([0]*self.f) for _ in range(e)]
        up = tuple((x*self.p) % self.mod for x in self.u)
        for i, a in enumerate(z):
            if all(x == 0 for x in a): continue
            for j, b in enumerate(w):
                if all(x == 0 for x in b): continue
                t = self.ur_mul(a, b)
                k = i + j
                if k >= e:
                    t = self.ur_mul(t, up); k -= e
                comps[k] = self.ur_add(comps[k], t)
        return tuple(comps)
    def from_int(self, n):
        a = [n % self.mod] + [0]*(self.f-1)
        return tuple([tuple(a)] + [tuple([0]*self.f)]*(self.e-1))
    def vK(self, z):
        best = self.e * PREC
        for j, a in enumerate(z):
            v = self.ur_vp(a)
            if v < PREC:
                t = self.e*v + j
                if t < best: best = t
        return best
    def pi_div(self, z, k):
        """divide by beta^k (assumes vK(z) >= k)."""
        e = self.e
        for _ in range(k):
            # z/beta = (z1,...,z_{e-1}, z0/(u p)) : z0 component must be divisible by p
            z0 = z[0]
            z0 = self.ur_divp(z0, 1)
            z0 = self.ur_mul(z0, self.uinv())
            z = tuple(list(z[1:]) + [z0])
        return z
    def uinv(self):
        if not hasattr(self, "_uinv"):
            # invert u in O_ur by Hensel: find x with u*x=1; residue inverse then lift
            fq = self.fq
            ub = tuple(x % self.p for x in self.u)
            xb = next(y for y in fq.elems if fq.mul(ub, y) == fq.one)
            x = tuple(int(t) for t in xb)
            one = tuple([1]+[0]*(self.f-1))
            for _ in range(PREC.bit_length()+1):
                # x <- x*(2 - u*x)
                t = self.ur_sub(tuple([2]+[0]*(self.f-1)), self.ur_mul(self.u, x))
                x = self.ur_mul(x, t)
            self._uinv = x
        return self._uinv
    def residue(self, z):
        return tuple(x % self.p for x in z[0])
    def embed_res(self, r):
        """lift an F_Q element to O_K (integer-coefficient lift)."""
        return tuple([tuple(int(x) for x in r)] + [tuple([0]*self.f)]*(self.e-1))

# ---------------------------------------------------------------- root counting in O_K
def poly_taylor_shift(K, h, rhat):
    """Coefficients of h(rhat + y) by repeated synthetic division (exact)."""
    a = list(h)
    taylor = []
    while a:
        carry = a[-1]
        Q = []
        for i in range(len(a)-2, -1, -1):
            Q.append(carry)
            carry = K.add(a[i], K.mul(carry, rhat))
        Q.reverse()
        taylor.append(carry)   # remainder = next Taylor coefficient
        a = Q
    return taylor

def beta_elem(K):
    if K.e >= 2:
        comps = [tuple([0]*K.f) for _ in range(K.e)]
        comps[1] = tuple([1]+[0]*(K.f-1))
        return tuple(comps)
    # e = 1: uniformizer is u*p (equivalently p)
    return K.from_int(K.p)

def count_roots(K, h, depth=DEPTH_CAP):
    """# roots in O_K of polynomial h (list of O_K coefficients, constant-first).
    Exact recursive subdivision + Hensel; raises Retry on precision/depth exhaustion."""
    vmin = min(K.vK(c) for c in h)
    if vmin >= K.e*(PREC - VMARGIN):
        raise Retry("precision floor")
    if vmin > 0:
        h = [K.pi_div(c, vmin) for c in h]
    hbar = [K.fq.zero if K.vK(c) > 0 else K.residue(c) for c in h]
    while hbar and hbar[-1] == K.fq.zero:
        hbar.pop()
    if len(hbar) <= 1:
        return 0
    dbar = [tuple((i*x) % K.p for x in hbar[i]) for i in range(1, len(hbar))]
    total = 0
    for r in K.fq.elems:
        if K.fq.poly_eval(hbar, r) != K.fq.zero:
            continue
        if K.fq.poly_eval(dbar, r) != K.fq.zero:
            total += 1                     # Hensel: exactly one root in this disc
        else:
            if depth <= 0:
                raise Retry("depth cap")
            rhat = K.embed_res(r)
            taylor = poly_taylor_shift(K, h, rhat)
            beta = beta_elem(K)
            h2, bk = [], K.one
            for tk in taylor:
                h2.append(K.mul(tk, bk))
                bk = K.mul(bk, beta)
            total += count_roots(K, h2, depth-1)
    return total

# ---------------------------------------------------------------- TK-0 formula layer
def tk0_formula(p, K_type, L_type):
    """LEMMA TK-0: #Hom_F(L, K). K_type=(e,f,c), L_type=(e',f',a); letters in the
    canonical coordinates gQ (generator of F_{q^f}^*), g_{f'} = gQ^{(Q-1)/(q^{f'}-1)}."""
    e, f, c = K_type; ep, fp, a = L_type
    q = p
    if f % fp != 0 or e % ep != 0:
        return 0
    Q = q**f
    g = math.gcd(ep, Q-1)
    r = (Q-1)//(q**fp - 1)
    cnt = 0
    for j in range(fp):
        if (a*r*(q**j) - c) % g == 0:
            cnt += g
    return cnt

def n_aut(p, L_type):
    ep, fp, a = L_type
    return tk0_formula(p, (ep, fp, a), L_type)

def subfield_mass_sum(p, K_type):
    """Sigma_{F subset L subset K} q^{-v(disc(L/F))} as a Fraction (CONJ-MEAN, proj form)."""
    e, f, c = K_type
    q = p
    total = Fraction(0)
    for fp in [d for d in range(1, f+1) if f % d == 0]:
        for ep in [d for d in range(1, e+1) if e % d == 0]:
            g0 = math.gcd(ep, q**fp - 1)
            for a in range(g0):
                hom = tk0_formula(p, K_type, (ep, fp, a))
                if hom == 0:
                    continue
                aut = n_aut(p, (ep, fp, a))
                nsub = Fraction(hom, aut)
                assert nsub.denominator == 1, (K_type, (ep, fp, a), hom, aut)
                total += nsub * Fraction(1, q**(fp*(ep-1)))
    return total

# ---------------------------------------------------------------- exact small-n laws
def exact_mean_n2(p, K_type):
    """THEOREM TK-Q: E[X_K] at n=2 (monic), exact."""
    q = p
    e, f, c = K_type
    P = Fraction(q, 2*(q+1))                      # class of 1
    if f % 2 == 0:
        P += Fraction(q, 2*(q+1))                 # class of u
    if e % 2 == 0:
        Q = q**f
        r = (Q-1)//(q-1)
        for a in (0, 1):
            if (a*r - c) % math.gcd(2, Q-1) == 0:
                P += Fraction(1, 2*(q+1))
    return 2*P

def exact_mean_n3(p, K_type):
    """S3 exact n=3 anchors (menu rows x TK-0 x TK-3), monic."""
    q = p
    e, f, c = K_type
    Phi5 = q**4+q**3+q**2+q+1
    E = Fraction(q, q+1)
    # (1,2)-factors embed iff 2 | f  (#Hom = 2)
    if f % 2 == 0:
        E += 2*Fraction(q**3*(q**2+q+1), 2*(q+1)*Phi5)
    # (2,1)-factors: menu row q(q^3+q+1)/((q+1)Phi5), split evenly over 2 twists;
    # matching twist embeds with #Hom=2 iff K has a val-1/2 element of that class
    if e % 2 == 0:
        Q = q**f
        r = (Q-1)//(q-1)
        for a in (0, 1):
            if (a*r - c) % 2 == 0:
                E += 2*Fraction(1, 2)*Fraction(q*(q**3+q+1), (q+1)*Phi5)
    # (3,1)-factors: row (q^2+1)/Phi5; product #Hom x (1/g0) is g0-free
    if e % 3 == 0:
        E += Fraction(q**2+1, Phi5)
    # (1,3)-factors: menu row q^3(q+1)/(3 Phi5), #Hom = 3
    if f % 3 == 0:
        E += Fraction(q**3*(q+1), Phi5)
    return E

def limit_mean_monic(p, K_type):
    q = p
    return Fraction(q, q+1) * subfield_mass_sum(p, K_type)

# ---------------------------------------------------------------- L-poly construction
def minpoly_lift(fq, elem):
    """Monic integer lift of the minimal polynomial of elem over F_p."""
    conjs, x = [], elem
    while x not in conjs:
        conjs.append(x)
        x = fq.pow(x, fq.p)
    poly = [fq.one]                      # product of (X - conj), coeffs low->high in F_Q
    for cjs in conjs:
        newp = [fq.zero]*(len(poly)+1)
        for i, co in enumerate(poly):
            newp[i+1] = fq.add(newp[i+1], co)
            newp[i] = fq.add(newp[i], fq.mul(fq.neg(cjs), co))
        poly = newp
    ints = []
    for co in poly:
        assert all(v == 0 for v in co[1:]), "minpoly coefficient not in F_p"
        ints.append(int(co[0]))
    return ints                          # degree = len(conjs)

def build_L_poly(K, ep, fp, a):
    """Integer coefficients (low->high) of a monic poly P with F[x]/(P) = L(ep,fp,a),
    letters in K's canonical coordinates (g_{fp} = gQ^{(Q-1)/(q^{fp}-1)})."""
    p, f = K.p, K.f
    Q = p**f
    assert f % fp == 0
    gfp = K.fq.pow(K.gQ, (Q-1)//(p**fp - 1))
    w = K.fq.pow(gfp, a)
    m_ints = minpoly_lift(K.fq, w)
    fpp = len(m_ints) - 1
    assert fpp == fp, ("letter %d drops residue degree %d->%d" % (a, fp, fpp))
    # P(x) = p^{fp} * m'(x^{ep}/p) = sum_i c_i p^{fp-i} x^{ep*i}
    P = [0]*(ep*fp + 1)
    for i, ci in enumerate(m_ints):
        P[ep*i] = ci * p**(fp - i)
    return P

def brute_hom(K, ep, fp, a):
    if K.f % fp != 0:
        return 0
    P = build_L_poly(K, ep, fp, a)
    h = [K.from_int(cc) for cc in P]
    return count_roots(K, h)

# ---------------------------------------------------------------- MC engine
def mc_cell(args):
    (p, e, f, c, n, nsamp, seed) = args
    K = TameK(p, e, f, c)
    rng = random.Random(seed)
    hist, retries = {}, 0
    M = p**PREC
    got = 0
    while got < nsamp:
        coeffs = [rng.randrange(M) for _ in range(n)]
        h = [K.from_int(cc) for cc in coeffs] + [K.one]
        try:
            x = count_roots(K, h)
        except Retry:
            retries += 1
            if retries > nsamp//10 + 50:
                raise RuntimeError("excessive retries at %s" % (args,))
            continue
        hist[x] = hist.get(x, 0) + 1
        got += 1
    return {"cell": [p, e, f, c], "n": n, "nsamp": nsamp, "hist": hist,
            "retries": retries}

def hist_mean_se(rec):
    N = rec["nsamp"]
    mean = sum(int(k)*v for k, v in rec["hist"].items())/N
    var = sum((int(k)-mean)**2 * v for k, v in rec["hist"].items())/max(N-1, 1)
    return mean, math.sqrt(var/N)

# ---------------------------------------------------------------- grid
CELLS = [  # (p, e, f, c)
    (3,2,1,0),(3,2,1,1),(3,1,2,0),(3,1,3,0),(3,2,2,0),(3,2,2,1),(3,4,1,0),
    (5,2,1,0),(5,2,1,1),(5,3,1,0),(5,1,2,0),
    (7,3,1,0),(7,3,1,1),(7,3,1,2),(7,1,2,0),(7,2,1,0),
]
def degrees_for(p):  return list(range(2, 8)) if p == 3 else [2, 3, 6]
def samples_for(p):  return 150000 if p == 3 else (60000 if p == 5 else 40000)

TK0_L_TYPES = [(2,1,0),(2,1,1),(3,1,0),(3,1,1),(3,1,2),(4,1,0),(4,1,1),
               (1,2,1),(1,3,1),(2,2,1),(2,2,2)]

def tk0_roster_pairs():
    pairs = []
    for (p, e, f, c) in CELLS:
        for (ep, fp, a) in TK0_L_TYPES:
            if (p, fp) not in IRRED:  continue
            if ep % p == 0:  continue      # wild L: outside TK-0's perimeter
            if fp > f and fp % f != 0 and f % fp != 0:  pass
            if a >= math.gcd(ep, p**fp - 1) and ep > 1:  continue
            if ep == 1 and a != 1:  continue
            if ep > 1 and fp > 1 and a < 1:  continue
            pairs.append(((p, e, f, c), (ep, fp, a)))
    return pairs

# ---------------------------------------------------------------- predictions
def predictions():
    P = {}
    for cell in CELLS:
        p, e, f, c = cell
        key = "p%d_e%d_f%d_c%d" % cell
        P[key] = {
            "mean_n2_exact": str(exact_mean_n2(p, (e, f, c))),
            "mean_n3_exact": str(exact_mean_n3(p, (e, f, c))),
            "mass_sum_proj": str(subfield_mass_sum(p, (e, f, c))),
            "mean_limit_monic": str(limit_mean_monic(p, (e, f, c))),
        }
    P["_prereg_notes"] = [
        "P1 TK0: brute #Hom == TK-0 formula on the full roster incl. zero cases",
        "P2 TKQ: MC(n=2) within 5 sigma of mean_n2_exact at every cell; X in {0,2} only",
        "P3 N3: MC(n=3) within 5 sigma of mean_n3_exact at every cell",
        "P4 DIP: at p=3 (2,1) cells, E(2)-E(3) > 0 at 3.5 sigma joint; E(7) > E(3) at 2 sigma",
        "P5 LIM: |MC(n_max) - mean_limit_monic| < max(5 sigma, 0.04*(1+E)) at every cell (consistency band)",
        "P6 SPLIT: (2,2,c=0) minus (2,2,c=1) at p=3: exact 1/2 at n=2 (5 sigma); > 0.25 at n=7 (5 sigma)",
        "P7 LEQ: twist-partner cells ((2,1,0)vs(2,1,1) p=3,5; (3,1,c) p=7) have equal means, 5 sigma, all n",
        "P8 TEETH: T1 wrong-twist TK-0, T2 mass-blind, T3 letter-blind (2,2), T4 tame-blind all bite",
    ]
    return P

# ---------------------------------------------------------------- main battery
def run(smoke=False, workers=14):
    t0 = time.time()
    results = {"checks": [], "teeth": [], "mc": [], "prereg": predictions()}
    ok = lambda name, cond, info="": results["checks"].append(
        {"name": name, "pass": bool(cond), "info": str(info)}) or print(
        ("PASS " if cond else "FAIL ") + name + ("  " + str(info) if info else ""))

    # --- TK0 family (exact)
    mism1 = 0
    for (Kt, Lt) in tk0_roster_pairs():
        p = Kt[0]
        K = TameK(p, Kt[1], Kt[2], Kt[3])
        try:
            b = brute_hom(K, *Lt)
        except AssertionError as ex:
            continue   # letter drops residue degree: not a valid (ep,fp) letter rep
        frm = tk0_formula(p, (Kt[1], Kt[2], Kt[3]), Lt)
        ok("TK0 %s <- L%s" % (Kt, Lt), b == frm, "brute=%d formula=%d" % (b, frm))
        if tk0_formula(p, (Kt[1], Kt[2], (Kt[3]+1)), Lt) != b:
            mism1 += 1
    results["teeth"].append({"name": "T1 wrong-twist TK-0", "bites": mism1 > 0,
                             "mismatches": mism1})
    print("TOOTH T1 bites:", mism1 > 0, "(%d mismatches)" % mism1)

    # --- MC grid
    jobs = []
    for cell in CELLS:
        p = cell[0]
        for n in degrees_for(p):
            ns = 300 if smoke else samples_for(p)
            seed = ((cell[0]*1000003 + cell[1]*10007 + cell[2]*101 + cell[3])*100 + n) & 0xffffffff
            jobs.append((cell[0], cell[1], cell[2], cell[3], n, ns, seed))
    with Pool(workers) as pool:
        mcrecs = pool.map(mc_cell, jobs)
    results["mc"] = mcrecs
    def rec(cell, n):
        for r in mcrecs:
            if tuple(r["cell"]) == tuple(cell) and r["n"] == n:
                return r
        return None

    # --- TKQ + N3 + LIM per cell
    for cell in CELLS:
        p, e, f, c = cell
        r2 = rec(cell, 2)
        m2, s2 = hist_mean_se(r2)
        ex2 = float(exact_mean_n2(p, (e, f, c)))
        ok("TKQ mean n=2 %s" % (cell,), abs(m2-ex2) <= 5*s2 + 1e-12,
           "mc=%.4f exact=%.4f se=%.4f" % (m2, ex2, s2))
        ok("TKQ support {0,2} %s" % (cell,),
           set(int(k) for k in r2["hist"]) <= {0, 2}, str(r2["hist"]))
        r3 = rec(cell, 3)
        m3, s3 = hist_mean_se(r3)
        ex3 = float(exact_mean_n3(p, (e, f, c)))
        ok("N3 mean n=3 %s" % (cell,), abs(m3-ex3) <= 5*s3,
           "mc=%.4f exact=%.4f se=%.4f" % (m3, ex3, s3))
        nmax = max(degrees_for(p))
        rN = rec(cell, nmax)
        mN, sN = hist_mean_se(rN)
        lim = float(limit_mean_monic(p, (e, f, c)))
        band = max(5*sN, 0.04*(1+lim))
        ok("LIM mean n=%d %s" % (nmax, cell), abs(mN-lim) <= band,
           "mc=%.4f lim=%.4f band=%.4f" % (mN, lim, band))

    # --- DIP (p=3 ram quad cells)
    for cell in [(3,2,1,0),(3,2,1,1)]:
        m2, s2 = hist_mean_se(rec(cell, 2)); m3, s3 = hist_mean_se(rec(cell, 3))
        m7, s7 = hist_mean_se(rec(cell, 7))
        sj23 = math.hypot(s2, s3); sj37 = math.hypot(s3, s7)
        ok("DIP down %s" % (cell,), m2 - m3 > 3.5*sj23,
           "E2-E3=%.4f (pred %.4f) sj=%.4f" % (m2-m3, 7/121, sj23))
        ok("DIP recover %s" % (cell,), m7 - m3 > 2*sj37,
           "E7-E3=%.4f sj=%.4f" % (m7-m3, sj37))

    # --- SPLIT ((2,2) letters, p=3)
    a2, b2 = hist_mean_se(rec((3,2,2,0), 2)), hist_mean_se(rec((3,2,2,1), 2))
    d2, sd2 = a2[0]-b2[0], math.hypot(a2[1], b2[1])
    ok("SPLIT n=2", abs(d2 - 0.5) <= 5*sd2, "diff=%.4f pred=0.5 se=%.4f" % (d2, sd2))
    a7, b7 = hist_mean_se(rec((3,2,2,0), 7)), hist_mean_se(rec((3,2,2,1), 7))
    d7, sd7 = a7[0]-b7[0], math.hypot(a7[1], b7[1])
    ok("SPLIT n=7", d7 - 5*sd7 > 0.25, "diff=%.4f se=%.4f" % (d7, sd7))

    # --- LEQ twist partners
    partners = [((3,2,1,0),(3,2,1,1)), ((5,2,1,0),(5,2,1,1)),
                ((7,3,1,0),(7,3,1,1)), ((7,3,1,0),(7,3,1,2))]
    for (ca, cb) in partners:
        for n in sorted(set(degrees_for(ca[0]))):
            (ma, sa), (mb, sb) = hist_mean_se(rec(ca, n)), hist_mean_se(rec(cb, n))
            ok("LEQ %s=%s n=%d" % (ca, cb, n), abs(ma-mb) <= 5*math.hypot(sa, sb),
               "d=%.4f" % (ma-mb))

    # --- TEETH T2/T3/T4 (mutant means must be REJECTED where law is accepted)
    def tooth_mut(name, cell, n, mutant_val):
        r = rec(cell, n); m, s = hist_mean_se(r)
        bites = abs(m - mutant_val) > 5*s
        results["teeth"].append({"name": name, "bites": bool(bites),
                                 "cell": list(cell), "n": n,
                                 "mutant": mutant_val, "mc": m, "se": s})
        print("TOOTH %s bites: %s (mutant=%.4f mc=%.4f se=%.4f)" %
              (name, bites, mutant_val, m, s))
    p3 = 3
    nsub_21 = 2  # subfields of (2,1): F and K
    tooth_mut("T2 mass-blind", (3,2,1,0), 7, float(Fraction(p3, p3+1)*nsub_21))
    avg22 = (limit_mean_monic(3, (2,2,0)) + limit_mean_monic(3, (2,2,1)))/2
    tooth_mut("T3 letter-blind (2,2) c=0 n=2", (3,2,2,0), 2,
              float((exact_mean_n2(3, (2,2,0)) + exact_mean_n2(3, (2,2,1)))/2))
    tooth_mut("T4 tame-blind", (3,2,1,0), 2, float(Fraction(p3, p3+1)))

    # --- verdict
    nfail = sum(1 for cchk in results["checks"] if not cchk["pass"])
    nbite = sum(1 for t in results["teeth"] if t["bites"])
    results["summary"] = {"checks": len(results["checks"]), "fails": nfail,
                          "teeth": len(results["teeth"]), "bites": nbite,
                          "elapsed_s": round(time.time()-t0, 1), "smoke": smoke}
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "tamek_results.json" if not smoke else "tamek_smoke.json")
    with open(out, "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    print("SUMMARY:", results["summary"])
    return 0 if (nfail == 0 and nbite == len(results["teeth"])) else 1

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--prereg", action="store_true")
    ap.add_argument("--workers", type=int, default=14)
    args = ap.parse_args()
    if args.prereg:
        print(json.dumps(predictions(), indent=1))
        sys.exit(0)
    sys.exit(run(smoke=args.smoke, workers=args.workers))
