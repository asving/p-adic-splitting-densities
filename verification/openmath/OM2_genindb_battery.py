#!/usr/bin/env python3
"""OM-2 (GENIND.B inductive step, OUTLINE+CERTIFY) — the certification battery.

Companion to docs/openmath-campaign/OM-2_genind-b_2026-08-16.md (section 3).  Exact integer /
Fraction arithmetic throughout; every cell EXHAUSTIVE (the only sampling is the PARI oracle's
lift probes, seed-fixed).  Two coefficient rings at q in {2,3}:

    Zq  = Z / q^prec          (mixed characteristic, the corpus battery's ring)
    Fqt = F_q[t] / t^prec     (EQUAL characteristic — never machine-tested by the corpus:
                               GENIND-BOX-3/GENIND-BOX-6)

PART 1  (N-2a/N-2b/N-2c + CC-2):  the conservative cluster reader (m,d=1,N): five-case
        partition, locus laws, alpha ghost fibres, beta capped-window per-genre composition,
        CS criterion, recursion identity, both-characteristic cellwise equality.
PART 2  (N-1a/N-1b/N-1c + oracle): the level-0 frame transport at n in {3,4}: Hensel class
        bijection + counts, roundtrip, the composed verdict vs the PARI (e,f) oracle
        (Z_q lifts only; equal-char leg is count/composition only, disclosed).
PART 3  (N-3 + CC-3):  the landed RecursionLegs fields (leanfinal/Uniformity/ChapH/H71.lean,
        A-H.2 signature) on the TRUE exhaustive data at m in {2,3}; species constants.
PART 4  (CC-1 + F-1):  the multiset-cancellation defeat scan and the per-type collision
        exhibit.

Exit code 0 iff every check passes.  Run:  python3 OM2_genindb_battery.py  [--fast] [--no-oracle]
(the padic venv python is needed for the oracle leg: /workspace-vast/asving/envs/padic/bin/python)
"""

import sys, os, itertools, random
from fractions import Fraction
from functools import lru_cache

FAST = "--fast" in sys.argv
NO_ORACLE = "--no-oracle" in sys.argv

CHECKS = []          # (name, ok, detail)
def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok), detail))
    print(("  ok  " if ok else "  FAIL") + f"  {name}" + (f"  [{detail}]" if detail and not ok else ""))

# ----------------------------------------------------------------------------------
# PART 0 — truncated-DVR rings (elements are plain ints; ops take (q, prec))
# ----------------------------------------------------------------------------------
# Zq : element = int in [0, q^prec), pi = q.
# Fqt: element = packed int, slot i (16 bits) = coefficient of t^i in F_q; pi = t.

SLOT = 16
MASK = (1 << SLOT) - 1

class Ring:
    """A truncated DVR O/pi^prec with residue field F_q (q prime), kind in {'Zq','Fqt'}."""
    def __init__(self, kind, q, prec):
        self.kind, self.q, self.prec = kind, q, prec
        if kind == 'Zq':
            self.mod = q ** prec
    def renorm(self, x):
        if self.kind == 'Zq':
            return x % self.mod
        out, i = 0, 0
        while x and i < self.prec:
            c = (x >> (SLOT * i)) & MASK
            r = c % self.q
            if r != c:
                x += (r - c) << (SLOT * i)
            i += 1
        # truncate above prec
        return x & ((1 << (SLOT * self.prec)) - 1)
    def add(self, a, b):
        return self.renorm(a + b)
    def sub(self, a, b):
        if self.kind == 'Zq':
            return (a - b) % self.mod
        # slotwise subtraction: add (q - digit) of b
        nb = 0
        for i in range(self.prec):
            c = (b >> (SLOT * i)) & MASK
            if c:
                nb |= (self.q - c) << (SLOT * i)
        return self.renorm(a + nb)
    def mul(self, a, b):
        return self.renorm(a * b)
    def val(self, x):
        """pi-adic valuation, capped at prec (val(0) = prec)."""
        if x == 0:
            return self.prec
        if self.kind == 'Zq':
            v = 0
            while x % self.q == 0:
                x //= self.q; v += 1
                if v >= self.prec: break
            return v
        v = 0
        while ((x >> (SLOT * v)) & MASK) == 0:
            v += 1
            if v >= self.prec: break
        return v
    def shift_down(self, x, v):
        """x / pi^v (requires val >= v)."""
        if self.kind == 'Zq':
            assert x % (self.q ** v) == 0
            return x // (self.q ** v)
        assert self.val(x) >= v or x == 0
        return x >> (SLOT * v)
    def shift_up(self, x, v):
        if self.kind == 'Zq':
            return (x * self.q ** v) % self.mod
        return self.renorm(x << (SLOT * v))
    def res(self, x):
        """residue in F_q (int)."""
        return x % self.q if self.kind == 'Zq' else x & MASK
    def lift_res(self, r):
        return r % self.q
    def from_int(self, c):
        """embed an integer constant (e.g. a binomial coefficient)."""
        if self.kind == 'Zq':
            return c % self.mod
        return c % self.q          # integers map through the residue field in char p
    def trunc(self, x, m):
        """canonical truncation to precision m <= prec (zero digits >= m)."""
        if self.kind == 'Zq':
            return x % (self.q ** m)
        return x & ((1 << (SLOT * m)) - 1)
    def elements(self, m, val_ge=0):
        """all canonical elements of precision m (digits < m), with val >= val_ge."""
        if self.kind == 'Zq':
            step = self.q ** val_ge
            return range(0, self.q ** m, step) if val_ge == 0 else \
                   [c * step for c in range(self.q ** (m - val_ge))]
        outs = []
        for digs in itertools.product(range(self.q), repeat=max(m - val_ge, 0)):
            x = 0
            for i, c in enumerate(digs):
                x |= c << (SLOT * (i + val_ge))
            outs.append(x)
        return outs
    def to_int_lift(self, x, m):
        """for Zq: canonical integer lift of the precision-m class (for the PARI oracle)."""
        assert self.kind == 'Zq'
        return self.trunc(x, m)

# ----------------------------------------------------------------------------------
# F_q[y] helpers (residue-field polynomials; lists of ints mod q, index = degree)
# ----------------------------------------------------------------------------------
def fq_trim(a):
    while a and a[-1] == 0: a.pop()
    return a

def fq_mul(a, b, q):
    if not a or not b: return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return fq_trim(out)

def fq_add(a, b, q):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] = x
    for i, y in enumerate(b): out[i] = (out[i] + y) % q
    return fq_trim(out)

def fq_scal(c, a, q):
    return fq_trim([(c * x) % q for x in a])

def fq_divmod(a, b, q):
    """a = q*b + r over F_q, b nonzero."""
    a = a[:]; out = [0] * max(len(a) - len(b) + 1, 0)
    inv = pow(b[-1], q - 2, q)
    while len(a) >= len(b) and a:
        c = (a[-1] * inv) % q
        d = len(a) - len(b)
        out[d] = c
        for i, x in enumerate(b):
            a[d + i] = (a[d + i] - c * x) % q
        fq_trim(a)
    return fq_trim(out), a

def fq_gcdext(a, b, q):
    """(g, u, v) with u*a + v*b = g (monic gcd)."""
    r0, r1 = a[:], b[:]
    s0, s1 = [1], []
    t0, t1 = [], [1]
    while r1:
        qq, r = fq_divmod(r0, r1, q)
        r0, r1 = r1, r
        s0, s1 = s1, fq_add(s0, fq_scal(q - 1, fq_mul(qq, s1, q), q), q)
        t0, t1 = t1, fq_add(t0, fq_scal(q - 1, fq_mul(qq, t1, q), q), q)
    inv = pow(r0[-1], q - 2, q)
    return fq_scal(inv, r0, q), fq_scal(inv, s0, q), fq_scal(inv, t0, q)

@lru_cache(maxsize=None)
def fq_irreducibles(q, maxdeg):
    """monic irreducibles over F_q up to degree maxdeg, as tuples."""
    irr = []
    for d in range(1, maxdeg + 1):
        for tail in itertools.product(range(q), repeat=d):
            f = list(tail) + [1]
            ok = True
            for g in irr:
                if len(g) - 1 <= d // 2:
                    _, r = fq_divmod(f, list(g), q)
                    if not r: ok = False; break
                else:
                    break
            # ensure irr is degree-sorted (it is, by construction)
            if ok and d > 1:
                # also check degree-1..d//2 divisors thoroughly
                for g in irr:
                    if len(g) - 1 > d // 2: break
                    _, r = fq_divmod(f, list(g), q)
                    if not r: ok = False; break
            if ok:
                irr.append(tuple(f))
    return irr

def fq_factor(f, q):
    """f over F_q (unit lead) -> list of (irreducible tuple, multiplicity). deg f <= 8.
    Non-monic input is normalized monic first (same roots/factors/multiplicities)."""
    f = fq_trim(f[:])
    assert f and f[-1] != 0
    if f[-1] != 1:
        f = fq_scal(pow(f[-1], q - 2, q), f, q)
    out = []
    for g in fq_irreducibles(q, len(f) - 1):
        m = 0
        while len(f) >= len(g):
            qq, r = fq_divmod(f, list(g), q)
            if r: break
            f, m = qq, m + 1
        if m: out.append((g, m))
        if len(f) == 1: break
    assert len(f) == 1 and f[0] == 1, "factorization incomplete"
    return out

# ----------------------------------------------------------------------------------
# ring-level polynomial helpers (lists of ring elements, index = degree)
# ----------------------------------------------------------------------------------
def rpoly_mul(R, a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] = R.add(out[i + j], R.mul(x, y))
    return out

def rpoly_sub(R, a, b):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] = x
    for i, y in enumerate(b): out[i] = R.sub(out[i], y)
    return out

def rpoly_divmod_monic(R, a, b):
    """divide a by MONIC b over the ring (exact ring division, any precision)."""
    a = a[:]
    db = len(b) - 1
    assert b[-1] == R.from_int(1)
    out = [0] * max(len(a) - db, 0)
    for d in range(len(a) - 1, db - 1, -1):
        c = a[d]
        if c:
            out[d - db] = c
            for i in range(db + 1):
                a[d - db + i] = R.sub(a[d - db + i], R.mul(c, b[i]))
    while len(a) > 1 and a[-1] == 0: a.pop()
    return out, a

# ----------------------------------------------------------------------------------
# Hensel split at precision M: g monic over R, gbar = y^mu * cobar, cobar(0) != 0
# ----------------------------------------------------------------------------------
def hensel_split(R, g, mu, M, q):
    """return (h, k) with g = h*k mod pi^M, h monic degree mu, h == y^mu mod pi.
    gbar may have degree < deg g (non-unit-lead cofactor: the monic-factor form)."""
    deg = len(g) - 1
    gbar = [R.res(c) for c in g]
    hbar = [0] * mu + [1]
    kbar = fq_trim([(gbar[i + mu]) % q for i in range(len(gbar) - mu)])
    assert gbar[:mu] == [0] * mu or all(v == 0 for v in gbar[:mu]), "gbar not divisible by y^mu"
    assert kbar and kbar[0] != 0, "cofactor not coprime to y^mu"
    gg, uu, vv = fq_gcdext(hbar, kbar, q)
    assert gg == [1], "not coprime"
    # lift h,k over the ring
    h = [R.from_int(c) for c in hbar]
    k = [R.from_int(c) for c in kbar] + [0] * (deg - mu + 1 - len(kbar))
    for i in range(1, M):
        e = rpoly_sub(R, g, rpoly_mul(R, h, k))
        # delta_bar = (e / pi^i) mod pi
        delta = [0] * (deg + 1)
        bad = False
        for d_, c in enumerate(e):
            if c and R.val(c) < i: bad = True; break
            if c: delta[d_] = R.res(R.shift_down(c, i))
        assert not bad, "hensel: error term valuation too small"
        delta = fq_trim(delta)
        if not delta: continue
        # solve hbar*w + kbar*u = delta ;  u = vv*delta mod hbar ; w = (delta - kbar*u)/hbar
        u = fq_divmod(fq_mul(vv, delta, q), hbar, q)[1]
        w, rr = fq_divmod(fq_add(delta, fq_scal(q - 1, fq_mul(kbar, u, q), q), q), hbar, q)
        assert not rr, "hensel: bezout residue"
        for d_, c in enumerate(u):
            if c: h[d_] = R.add(h[d_], R.shift_up(R.from_int(c), i))
        for d_, c in enumerate(w):
            if d_ >= len(k): k += [0] * (d_ + 1 - len(k))
            if c: k[d_] = R.add(k[d_], R.shift_up(R.from_int(c), i))
    return h, k

# ----------------------------------------------------------------------------------
# the conservative cluster reader, d = 1
# state: tuple (a_0,...,a_{m-1}) canonical at precision W, val >= 1; f = x^m + sum a_j x^j
# returns ('U', tag) or ('D', sigma) with sigma a sorted tuple of (e,f) pairs.
# classify: also returns the depth-0 bucket for the census.
# ----------------------------------------------------------------------------------
BINOM = [[1]]
def binom(i, j):
    while len(BINOM) <= i:
        r = [1] + [BINOM[-1][k] + BINOM[-1][k + 1] for k in range(len(BINOM[-1]) - 1)] + [1]
        BINOM.append(r)
    return BINOM[i][j]

def lower_hull(pts):
    """lower convex hull of (x, y) points, sorted by x; returns vertex list."""
    pts = sorted(pts)
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # remove hull[-1] if p makes it non-convex (keep strictly convex lower hull)
            if (y2 - y1) * (p[0] - x1) >= (p[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(p)
    return hull

def depth0_data(RB, state, m, W, q):
    """polygon + residual data of a cluster state (d=1).
    RB: BIG-precision ring; coefficients canonical at precision W.
    Returns dict with keys: bucket in {'DRAIN','DEC','ALPHA','BETA','CS'},
    and for ALPHA: (k, z); for BETA: children [(mu, k, z)], pieces [(e,f)...];
    for DEC: pieces; for CS: cs blocks [(e,mu,gamma)] + children/pieces present."""
    a = list(state) + [RB.from_int(1)]
    vals = [RB.val(x) for x in a]
    if vals[0] >= W:
        return {'bucket': 'DRAIN'}
    pts = [(j, vals[j]) for j in range(m + 1) if vals[j] < W or j == m]
    hull = lower_hull(pts)
    # sides from hull vertices, left to right; slopes are positive drops
    sides = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        sides.append((x1, y1, x2, y2))
    children, pieces, csblocks = [], [], []
    for (x1, y1, x2, y2) in sides:
        ln = x2 - x1
        drop = y1 - y2
        import math
        gg = math.gcd(drop, ln)
        h_, e_ = drop // gg, ln // gg
        # residual polynomial over F_q at lattice points x1 + i*e_
        deg_r = ln // e_
        rc = []
        for i in range(deg_r + 1):
            j = x1 + i * e_
            vline = y1 - i * h_
            if j <= m and vals[j] >= vline and vals[j] == vline:
                rc.append(RB.res(RB.shift_down(a[j], vline)))
            elif j == m and vline == 0:
                rc.append(1)
            else:
                rc.append(0)
        assert rc[0] != 0 and rc[-1] != 0, "residual endpoints must be units"
        for (psi, mult) in fq_factor(rc, q):
            gpsi = len(psi) - 1
            if mult == 1:
                pieces.append((e_, gpsi))
            elif e_ == 1 and gpsi == 1:
                z = (q - psi[0]) % q          # root of psi = y + psi0
                assert z != 0, "residual root must be nonzero"
                children.append((mult, h_, z))  # (mu, slope k, root z)
            else:
                csblocks.append((e_, mult, gpsi))
    if csblocks:
        return {'bucket': 'CS', 'cs': csblocks, 'children': children, 'pieces': pieces}
    if not children:
        return {'bucket': 'DEC', 'pieces': pieces}
    if len(sides) == 1 and len(children) == 1 and not pieces and children[0][0] == m:
        mu, k, z = children[0]
        return {'bucket': 'ALPHA', 'k': k, 'z': z}
    return {'bucket': 'BETA', 'children': children, 'pieces': pieces}

def extract_child(RB, state, m, W, k, z, q):
    """recenter x -> pi^k(y+z), divide by content; return (child_state tuple @ window M, D, mu, ghost_data)
    The child is the full recentered frame BEFORE Hensel split (degree m)."""
    a = list(state) + [RB.from_int(1)]
    s = RB.shift_up(RB.lift_res(z), k)          # s = z_hat * pi^k
    spow = [RB.from_int(1)]
    for _ in range(m):
        spow.append(RB.mul(spow[-1], s))
    c = []
    for j in range(m + 1):
        acc = 0
        for i in range(j, m + 1):
            term = RB.mul(a[i], RB.from_int(binom(i, j)))
            term = RB.mul(term, spow[i - j])
            acc = RB.add(acc, term)
        c.append(RB.shift_up(acc, k * j))
    D = min(RB.val(x) for x in c)
    # the capped-window content identity (GENIND-3 [r3] display):
    Dpred = min(min(RB.val(a[j]), W) + j * k if j < m else j * k for j in range(m + 1))
    return c, D, Dpred

READ_CACHE = {}

def read_cluster(ringkind, q, state, m, W):
    """conservative recursive read; state canonical at precision W (tuple of ints)."""
    key = (ringkind, q, m, W, state)
    if key in READ_CACHE:
        return READ_CACHE[key]
    prec = W * (m + 1) + 4
    RB = Ring(ringkind, q, prec)
    if W <= 0:
        raise AssertionError("window must be >= 1")
    verdict = _read_cluster_work(RB, ringkind, q, state, m, W)
    READ_CACHE[key] = verdict
    return verdict

def _read_cluster_work(RB, ringkind, q, state, m, W):
    d0 = depth0_data(RB, state, m, W, q)
    b = d0['bucket']
    if b == 'DRAIN' or b == 'CS':
        return ('U', b)
    if b == 'DEC':
        return ('D', tuple(sorted(d0['pieces'])))
    if b == 'ALPHA':
        k, z = d0['k'], d0['z']
        c, D, Dpred = extract_child(RB, state, m, W, k, z, q)
        assert D == m * k and Dpred == m * k, f"alpha content {D} != mk {m*k}"
        M = W - m * k
        child = []
        for j in range(m):
            x = RB.shift_down(c[j], D)
            assert RB.val(x) >= 1 or RB.trunc(x, M) == 0, "alpha child not a cluster state"
            child.append(RB.trunc(x, M))
        assert RB.shift_down(c[m], D) == RB.from_int(1)
        sub = read_cluster(ringkind, q, tuple(child), m, M)
        return sub if sub[0] == 'U' else sub
    # BETA
    children, pieces = d0['children'], list(d0['pieces'])
    undec = False
    sigma = []
    for (mu, k, z) in children:
        c, D, Dpred = extract_child(RB, state, m, W, k, z, q)
        assert D == Dpred, f"content identity failed: {D} vs {Dpred}"
        M = W - D
        assert M >= 1, "child window must be >= 1"
        g = [RB.shift_down(x, D) for x in c]
        # monic-factor Hensel split: gbar = y^mu * cofactor
        h, _k2 = hensel_split(RB, g, mu, M, q)
        child = []
        for j in range(mu):
            x = h[j]
            child.append(RB.trunc(x, M))
            assert RB.val(x) >= 1 or RB.trunc(x, M) == 0, "beta child not a cluster state"
        sub = read_cluster(ringkind, q, tuple(child), mu, M)
        if sub[0] == 'U':
            undec = True
        else:
            sigma.extend(sub[1])
    if undec:
        return ('U', 'beta')
    sigma.extend(pieces)
    return ('D', tuple(sorted(sigma)))

# ----------------------------------------------------------------------------------
# the (m=2, d=2) cluster reader (for PART 2's n = 4 quadratic-square configs)
# K = F_{q^2} = F_q[w]/(Pbar); elements (c0, c1)
# state: (A0, A1) with A_j = (u_j, v_j) ring-element pairs (A_j = u + v x), Gauss val >= 1
# ----------------------------------------------------------------------------------
def k2_mul(a, b, pbar, q):
    (a0, a1), (b0, b1) = a, b
    # (a0 + a1 w)(b0 + b1 w) mod w^2 + p1 w + p0
    p0, p1 = pbar[0], pbar[1]
    c0 = a0 * b0
    c1 = a0 * b1 + a1 * b0
    c2 = a1 * b1
    return ((c0 - c2 * p0) % q, (c1 - c2 * p1) % q)

def k2_elements(q):
    return [(i, j) for i in range(q) for j in range(q)]

def read_cluster_d2(ringkind, q, state, W, pbar):
    """conservative read of the (2, d=2) cluster; state = ((u0,v0),(u1,v1)) canonical @ W."""
    key = (ringkind, q, 'd2', pbar, W, state)
    if key in READ_CACHE: return READ_CACHE[key]
    prec = 3 * W + 6
    RB = Ring(ringkind, q, prec)
    out = _read_d2_work(RB, ringkind, q, state, W, pbar)
    READ_CACHE[key] = out
    return out

def _gauss_val(RB, A, W):
    return min(RB.val(A[0]), RB.val(A[1]), W)

def _read_d2_work(RB, ringkind, q, state, W, pbar):
    A0, A1 = state
    v0, v1 = _gauss_val(RB, A0, W), _gauss_val(RB, A1, W)
    if v0 >= W:
        return ('U', 'DRAIN')
    # polygon on (0,v0),(1,v1),(2,0)
    if 2 * v1 < v0:                     # two sides, slopes v0-v1 and v1, both length 1
        return ('D', ((1, 2), (1, 2)))
    if v0 % 2 == 1:                     # one side, slope v0/2, e = 2 -> (2,2) piece
        return ('D', ((2, 2),))
    k = v0 // 2
    # residual over K: R(y) = y^2 + r1 y + r0
    r0 = (RB.res(RB.shift_down(A0[0], v0)), RB.res(RB.shift_down(A0[1], v0)))
    if v1 == k:
        r1 = (RB.res(RB.shift_down(A1[0], k)), RB.res(RB.shift_down(A1[1], k)))
    else:
        r1 = (0, 0)
    # roots of y^2 + r1 y + r0 in K
    roots = [zz for zz in k2_elements(q)
             if all((k2_mul(zz, zz, pbar, q)[i] + k2_mul(r1, zz, pbar, q)[i] + r0[i]) % q == 0
                    for i in (0, 1))]
    if len(roots) == 2:
        return ('D', ((1, 2), (1, 2)))
    if len(roots) == 0:
        return ('D', ((1, 4),))
    z = roots[0]
    # repeated iff (y - (-z))^2... check: y^2 + r1 y + r0 == (y - z')^2 with z' the root
    # (single root over a perfect field of a quadratic => repeated)
    if z == (0, 0):
        raise AssertionError("residual root 0 impossible on a hull side")
    # alpha-recenter: Phi' = Phi + zhat pi^k, redevelop, shear, recurse at W - 2k
    zc = (RB.shift_up(RB.lift_res(z[0]), k), RB.shift_up(RB.lift_res(z[1]), k))
    # Phi = x^2 + p1hat x + p0hat (canonical lift of pbar); Phi' adds zc
    p0h, p1h = RB.lift_res(pbar[0]), RB.lift_res(pbar[1])
    phi2 = [RB.add(p0h, zc[0]), RB.add(p1h, zc[1]), RB.from_int(1)]
    # f = Phi^2 + A1 Phi + A0 as a degree-4 poly over the ring
    phi = [p0h, p1h, RB.from_int(1)]
    f = rpoly_mul(RB, phi, phi)
    a1poly = [A1[0], A1[1]]
    f = [RB.add(x, y) for x, y in
         zip(f, rpoly_mul(RB, a1poly, phi) + [0] * 5)] if True else f
    f = f + [0] * (5 - len(f))
    f[0] = RB.add(f[0], A0[0]); f[1] = RB.add(f[1], A0[1])
    # redevelop wrt Phi': f = q1*Phi' + R0 ; q1 = q2*Phi' + R1 ; q2 == 1
    q1, R0 = rpoly_divmod_monic(RB, f, phi2)
    q2, R1 = rpoly_divmod_monic(RB, q1, phi2)
    assert len(q2) == 1 and q2[0] == RB.from_int(1)
    R0 += [0] * (2 - len(R0)); R1 += [0] * (2 - len(R1))
    # shear: A0' / pi^{2k}, A1' / pi^{k}
    M = W - 2 * k
    assert M >= 1
    nA0 = tuple(RB.trunc(RB.shift_down(x, 2 * k), M) for x in R0)
    nA1 = tuple(RB.trunc(RB.shift_down(x, k), M) for x in R1)
    assert _gauss_val(RB, nA0, M) >= 1 and _gauss_val(RB, nA1, M) >= 1, "d2 alpha child not a state"
    return read_cluster_d2(ringkind, q, (nA0, nA1), M, pbar)

# ----------------------------------------------------------------------------------
# PART 1 — the cluster census (N-2a/b/c + CC-2), both rings, cellwise equality
# ----------------------------------------------------------------------------------
def cluster_states(R, m, W):
    """all canonical states at window W (val >= 1 each coordinate)."""
    coords = R.elements(W, val_ge=1)
    return itertools.product(coords, repeat=m)

def clusterC(m): return m * (m - 1) // 2

def run_cell(ringkind, q, m, W):
    """exhaustive census of the (m, d=1, W) system; returns the census dict + checks."""
    prec = W * (m + 1) + 4
    RB = Ring(ringkind, q, prec)
    Q = q
    total = 0
    buckets = {'DRAIN': 0, 'DEC': 0, 'ALPHA': 0, 'BETA': 0, 'CS': 0}
    alpha_by_k = {}
    alpha_fibers = {}          # (k,z) -> {child_state: count}
    beta_genres = {}           # genre-key -> {'n':count, 'undec':count, 'fibers':{tuple(childstates):count}}
    cs_data = []
    undec = 0
    sigma_census = {}
    for st in cluster_states(RB, m, W):
        total += 1
        d0 = depth0_data(RB, st, m, W, q)
        b = d0['bucket']
        buckets[b] += 1
        verdict = read_cluster(ringkind, q, st, m, W)
        if verdict[0] == 'U': undec += 1
        else:
            sigma_census[verdict[1]] = sigma_census.get(verdict[1], 0) + 1
        if b == 'ALPHA':
            k, z = d0['k'], d0['z']
            alpha_by_k[k] = alpha_by_k.get(k, 0) + 1
            c, D, _ = extract_child(RB, st, m, W, k, z, q)
            M = W - m * k
            child = tuple(RB.trunc(RB.shift_down(x, D), M) for x in c[:m])
            alpha_fibers.setdefault((k, z), {}).setdefault(child, 0)
            alpha_fibers[(k, z)][child] += 1
        elif b == 'BETA':
            chs = tuple(sorted(d0['children']))
            childstates = []
            genre_windows = []
            for (mu, k, z) in sorted(d0['children']):
                c, D, Dp = extract_child(RB, st, m, W, k, z, q)
                assert D == Dp
                M = W - D
                g = [RB.shift_down(x, D) for x in c]
                h, _ = hensel_split(RB, g, mu, M, q)
                cst = tuple(RB.trunc(x, M) for x in h[:mu])
                childstates.append(((mu, M), cst))
                genre_windows.append((mu, k, M))
            gkey = (tuple(genre_windows), tuple(sorted(d0['pieces'])))
            rec = beta_genres.setdefault(gkey, {'n': 0, 'undec': 0, 'fibers': {}})
            rec['n'] += 1
            if verdict[0] == 'U': rec['undec'] += 1
            fk = tuple(cs for (_, cs) in childstates)
            rec['fibers'][fk] = rec['fibers'].get(fk, 0) + 1
        elif b == 'CS':
            cs_data.append(tuple(sorted(d0['cs'])))
    cell = f"{ringkind} q={q} m={m} N={W}"
    # (a) partition totality
    check(f"P1(a) partition total [{cell}]", sum(buckets.values()) == total == q ** (m * (W - 1)))
    # (b) drain count
    check(f"P1(b) drain count [{cell}]", buckets['DRAIN'] == Q ** ((m - 1) * (W - 1)))
    # (c) alpha locus law + window condition
    ok_c = True
    for k, cnt in alpha_by_k.items():
        if not (1 <= k and m * k <= W - 1): ok_c = False
        if cnt != (Q - 1) * Q ** (m * (W - 1) - k * m * (m + 1) // 2): ok_c = False
    for k in range(1, (W - 1) // m + 1):
        if W - m * k >= 1 and k not in alpha_by_k and m * k <= W - 1:
            ok_c = False        # every admissible k must be realized
    check(f"P1(c) alpha locus law + window [{cell}]", ok_c, str(alpha_by_k))
    # (d) alpha ghost fibres constant Q^{k c(m)}, onto
    ok_d = True
    for (k, z), fib in alpha_fibers.items():
        M = W - m * k
        want = Q ** (k * clusterC(m))
        if set(fib.values()) != {want}: ok_d = False
        if len(fib) != Q ** (m * (M - 1)): ok_d = False   # onto the full reduced window space
    check(f"P1(d) alpha fibres exact+onto [{cell}]", ok_d)
    # (e) recursion identity: undec = drain + sum_k (Q-1)Q^{k c(m)} u(W-mk) + beta-undec + CS
    upart = {}
    def u_of(mu, M):
        if (mu, M) not in upart:
            RB2 = Ring(ringkind, q, M * (mu + 1) + 4)
            cnt = 0
            for st2 in cluster_states(RB2, mu, M):
                if read_cluster(ringkind, q, st2, mu, M)[0] == 'U': cnt += 1
            upart[(mu, M)] = cnt
        return upart[(mu, M)]
    rhs = buckets['DRAIN'] + buckets['CS']
    for k in alpha_by_k:
        rhs += (Q - 1) * Q ** (k * clusterC(m)) * u_of(m, W - m * k)
    beta_undec_total = sum(rec['undec'] for rec in beta_genres.values())
    rhs += beta_undec_total
    check(f"P1(e) recursion identity [{cell}]", undec == rhs, f"{undec} vs {rhs}")
    # (f) beta per-genre composition: fibers constant + onto; undec = census*(prod T - prod(T-u))
    ok_f = True
    for gkey, rec in beta_genres.items():
        windows = gkey[0]
        Ts = [Q ** (mu * (M - 1)) for (mu, k, M) in windows]
        prodT = 1
        for T in Ts: prodT *= T
        if rec['n'] % prodT != 0: ok_f = False; continue
        census = rec['n'] // prodT
        if set(rec['fibers'].values()) != {census}: ok_f = False
        if len(rec['fibers']) != prodT: ok_f = False
        prodTu = 1
        for (mu, k, M), T in zip(windows, Ts):
            prodTu *= (T - u_of(mu, M))
        if rec['undec'] != census * (prodT - prodTu): ok_f = False
    check(f"P1(f) beta genre composition [{cell}] ({len(beta_genres)} genres)", ok_f)
    # (g) CS criterion
    if m <= 3:
        check(f"P1(g) zero CS below m=4 [{cell}]", buckets['CS'] == 0)
    else:
        ok_g = all(4 <= e * mu * gam <= m and (e, gam, mu) in {(2, 1, 2), (1, 2, 2)}
                   for blocks in cs_data for (e, mu, gam) in blocks) if m == 4 else True
        check(f"P1(g) CS criterion (eμγ=4 ⟹ two solutions) [{cell}]", ok_g)
    return {'total': total, 'buckets': buckets, 'alpha_by_k': alpha_by_k, 'undec': undec,
            'sigma': sigma_census,
            'beta': {gk: (rec['n'], rec['undec']) for gk, rec in beta_genres.items()}}

def hex3R_ref(q, M):
    """ChapG G.64 `hex3R` (the m=2 conservative complement / W-11 R(M)), verbatim."""
    if M <= 0: return 0
    if M == 1: return 1
    return q ** (M - 1) + ((M - 1) // 2) * ((q - 1) * q ** (M - 2))

def hex3U_ref(q, N):
    """ChapG G.66 `hex3U` (the cubic per-centre conservative complement), verbatim."""
    s = q ** (2 * N - 2)
    for k in range(1, (N - 1) // 3 + 1):
        s += (q - 1) * q ** (4 * k - 1) * ((q ** (N - 3 * k) - 1) * hex3R_ref(q, N - 3 * k))
    return s

def part1():
    print("\nPART 1 — the cluster grammar (N-2a/N-2b/N-2c + CC-2), both characteristics")
    plan = [(2, 2, range(1, 7)), (2, 3, range(1, 7)), (2, 4, range(1, 5)),
            (3, 2, range(1, 6)), (3, 3, range(1, 5)), (3, 4, range(1, 4))]
    if FAST:
        plan = [(2, 2, range(1, 5)), (2, 3, range(1, 5)), (2, 4, range(1, 4)),
                (3, 2, range(1, 4)), (3, 3, range(1, 4)), (3, 4, range(1, 4))]
    u_tables = {}
    for q, m, Ws in plan:
        for W in Ws:
            c1 = run_cell('Zq', q, m, W)
            c2 = run_cell('Fqt', q, m, W)
            same = (c1 == c2)
            check(f"P1(h) both-characteristics cellwise equality [q={q} m={m} N={W}]", same,
                  "" if same else "census differs")
            u_tables[(q, m, W)] = c1['undec']
            # (i) decorrelated tie to the LANDED ChapG arithmetic layer
            if m == 2:
                check(f"P1(i) tie u_2 = ChapG hex3R/uTwo closed form [q={q} N={W}]",
                      c1['undec'] == hex3R_ref(q, W), f"{c1['undec']} vs {hex3R_ref(q, W)}")
            if m == 3:
                check(f"P1(i) tie u_3 = ChapG hex3U [q={q} N={W}]",
                      c1['undec'] == hex3U_ref(q, W), f"{c1['undec']} vs {hex3U_ref(q, W)}")
    return u_tables

# ----------------------------------------------------------------------------------
# PART 2 — the level-0 frame transport (N-1a/b/c), n in {3,4}; PARI oracle at Zq
# ----------------------------------------------------------------------------------
def frame_read(ringkind, q, cls, n, N):
    """cls = tuple (a_0..a_{n-1}) canonical @ N; f = x^n + ... ; returns
    (verdict, factor_tuples, config) where factor_tuples identifies the Hensel factors mod pi^N."""
    prec = N * (n + 2) + 6
    RB = Ring(ringkind, q, prec)
    f = list(cls) + [RB.from_int(1)]
    fbar = [RB.res(c) for c in f]
    fac = fq_factor(fbar, q)
    # split off factors one at a time (largest first for stability)
    rem = f[:]
    parts = []        # (pbar tuple, mult, factor poly @ prec)
    for (pbar, mlt) in fac:
        target = [1]
        for _ in range(mlt): target = fq_mul(target, list(pbar), q)
        if len(target) - 1 == len(rem) - 1:
            parts.append((pbar, mlt, rem)); rem = [RB.from_int(1)]; break
        # hensel split rem = h*k with hbar = target (monic), kbar = rem_bar/target
        rembar = [RB.res(c) for c in rem]
        kbar, rr = fq_divmod(rembar, target, q)
        assert not rr
        h, k2 = hensel_split_general(RB, rem, target, kbar, q, N)
        parts.append((pbar, mlt, h))
        # make k2 monic-canonical: it is monic since rem and h are
        rem = k2
    assert len(rem) - 1 == 0
    verdict_undec = False
    sigma = []
    facts = []
    for (pbar, mlt, g) in parts:
        d_ = len(pbar) - 1
        facts.append(tuple(RB.trunc(c, N) for c in g))
        if mlt == 1:
            sigma.append((1, d_))
            continue
        if d_ == 1:
            r = (q - pbar[0]) % q
            rh = RB.lift_res(r)
            # recenter g(x + rh)
            mm = mlt
            a2 = []
            for j in range(mm + 1):
                acc = 0
                for i in range(j, mm + 1):
                    acc = RB.add(acc, RB.mul(RB.mul(g[i], RB.from_int(binom(i, j))),
                                             pow_ring(RB, rh, i - j)))
                a2.append(acc)
            st = tuple(RB.trunc(x, N) for x in a2[:mm])
            v = read_cluster(ringkind, q, st, mm, N)
        elif d_ == 2 and mlt == 2:
            # develop g wrt Phi = lift(pbar)
            phi = [RB.lift_res(pbar[0]), RB.lift_res(pbar[1]), RB.from_int(1)]
            q1, R0 = rpoly_divmod_monic(RB, g, phi)
            q2, R1 = rpoly_divmod_monic(RB, q1, phi)
            assert len(q2) == 1 and q2[0] == RB.from_int(1)
            R0 += [0] * (2 - len(R0)); R1 += [0] * (2 - len(R1))
            A0 = tuple(RB.trunc(x, N) for x in R0)
            A1 = tuple(RB.trunc(x, N) for x in R1)
            v = read_cluster_d2(ringkind, q, (A0, A1), N, (pbar[0], pbar[1]))
        else:
            raise AssertionError("unreachable cluster shape at n <= 4")
        if v[0] == 'U': verdict_undec = True
        else: sigma.extend(v[1])
    config = tuple(sorted((tuple(p), m_) for (p, m_, _) in parts))
    if verdict_undec:
        return ('U', None), tuple(facts), config
    return ('D', tuple(sorted(sigma))), tuple(facts), config

def pow_ring(R, x, e):
    out = R.from_int(1)
    for _ in range(e): out = R.mul(out, x)
    return out

def hensel_split_general(R, g, hbar, kbar, q, M):
    """g monic; split g = h*k mod pi^M with h == hbar (monic), k == kbar, coprime."""
    deg = len(g) - 1
    gg, uu, vv = fq_gcdext(hbar, kbar, q)
    assert gg == [1]
    h = [R.from_int(c) for c in hbar]
    k = [R.from_int(c) for c in kbar]
    for i in range(1, M):
        e = rpoly_sub(R, g, rpoly_mul(R, h, k))
        delta = [0] * (deg + 1)
        for d_, c in enumerate(e):
            if c:
                assert R.val(c) >= i, "precision loss in level-0 hensel"
                delta[d_] = R.res(R.shift_down(c, i))
        delta = fq_trim(delta)
        if not delta: continue
        u = fq_divmod(fq_mul(vv, delta, q), hbar, q)[1]
        w, rr = fq_divmod(fq_add(delta, fq_scal(q - 1, fq_mul(kbar, u, q), q), q), hbar, q)
        assert not rr
        for d_, c in enumerate(u):
            if c: h[d_] = R.add(h[d_], R.shift_up(R.from_int(c), i))
        for d_, c in enumerate(w):
            if d_ >= len(k): k += [0] * (d_ + 1 - len(k))
            if c: k[d_] = R.add(k[d_], R.shift_up(R.from_int(c), i))
    return h, k

def part2():
    print("\nPART 2 — the level-0 transport (N-1a/N-1b/N-1c) + the PARI oracle tie")
    oracle = None
    if not NO_ORACLE:
        try:
            sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
            # the user site-packages (cypari2 lives there) is not always on sys.path
            usersite = os.path.expanduser("~/.local/lib/python3.10/site-packages")
            if os.path.isdir(usersite) and usersite not in sys.path:
                sys.path.insert(0, usersite)
            import quartic_oracle as QO
            oracle = QO
        except Exception as e:
            print(f"  (oracle unavailable: {e}; oracle legs SKIPPED — count/composition legs still run)")
    plan = [(2, 2, [1, 2, 3]), (2, 3, [1, 2, 3]), (3, 2, [2, 3]), (3, 3, [2]),
            (4, 2, [2, 3]), (4, 3, [2])]
    if FAST:
        plan = [(2, 2, [2, 3]), (3, 2, [2]), (4, 2, [2])]
    rng = random.Random(20260816)
    for n, q, Ns in plan:
        for N in Ns:
            for ringkind in ('Zq', 'Fqt'):
                prec = N * (n + 2) + 6
                RB = Ring(ringkind, q, prec)
                coords = RB.elements(N, val_ge=0)
                strata = {}
                tup_seen = {}
                verdicts = {}
                total = 0
                for cls in itertools.product(coords, repeat=n):
                    total += 1
                    v, facts, config = frame_read(ringkind, q, cls, n, N)
                    verdicts[cls] = (v, config)
                    strata.setdefault(config, [0, 0])
                    strata[config][0] += 1
                    if v[0] == 'U': strata[config][1] += 1
                    tup_seen.setdefault(config, set()).add(facts)
                cell = f"{ringkind} q={q} n={n} N={N}"
                check(f"P2 total classes [{cell}]", total == q ** (n * N))
                # (i)+(ii): per residue-config the factor-tuple map is a bijection onto the
                # predicted product of factor class spaces
                ok_i = True
                for config, (cnt, und) in strata.items():
                    pred = 1
                    for (pbar, mlt) in config:
                        pred *= q ** ((len(pbar) - 1) * mlt * (N - 1))
                    if cnt != pred or len(tup_seen[config]) != pred:
                        ok_i = False
                check(f"P2(i,ii) stratum counts + Hensel class bijection [{cell}]", ok_i)
                # (iii): frame undecided count = composed count via cluster u-tables
                # (composition is by construction in frame_read; the content is (i,ii)+oracle;
                #  here we verify the per-stratum aggregation against the independently
                #  computed cluster tables)
                ok_iii = True
                for config, (cnt, und) in strata.items():
                    pred = 1
                    us = []
                    for (pbar, mlt) in config:
                        d_ = len(pbar) - 1
                        if mlt == 1: continue
                        T = q ** (d_ * mlt * (N - 1))
                        # cluster undecided count over the SAME ring kind
                        ucount = 0
                        if d_ == 1:
                            RB2 = Ring(ringkind, q, N * (mlt + 1) + 4)
                            for st in cluster_states(RB2, mlt, N):
                                if read_cluster(ringkind, q, st, mlt, N)[0] == 'U': ucount += 1
                        else:
                            RB2 = Ring(ringkind, q, 3 * N + 6)
                            celems = RB2.elements(N, val_ge=1)
                            for A0 in itertools.product(celems, repeat=2):
                                for A1 in itertools.product(celems, repeat=2):
                                    if read_cluster_d2(ringkind, q, (tuple(A0), tuple(A1)),
                                                       N, (pbar[0], pbar[1]))[0] == 'U':
                                        ucount += 1
                        us.append((T, ucount))
                    census = strata[config][0]
                    for (T, u) in us: census //= T
                    prodT, prodTu = 1, 1
                    for (T, u) in us: prodT *= T; prodTu *= (T - u)
                    if und != census * (prodT - prodTu): ok_iii = False
                check(f"P2(iii) stratum undecided = census*(ΠT − Π(T−u)) [{cell}]", ok_iii)
                # (v) F-2: the conservative/semantic gap at n = 2 against the LANDED law
                # (G.36 undecidedCount_two_eq: SEMANTIC undecided = q^N; the conservative
                #  reader gives q*hex3R(q,N); strict over-drain from N = 3 on)
                if n == 2:
                    und_total = sum(u_ for (_, u_) in strata.values())
                    cons_pred = q * hex3R_ref(q, N)
                    check(f"P2(v) n=2 conservative count = q*hex3R [{cell}]",
                          und_total == cons_pred, f"{und_total} vs {cons_pred}")
                    check(f"P2(v) n=2 semantic law bound: q^N <= conservative [{cell}]",
                          q ** N <= und_total)
                    check(f"P2(v) n=2 F-2 over-drain iff N >= 3 [{cell}]",
                          (und_total > q ** N) == (N >= 3),
                          f"cons={und_total} sem={q**N}")
                # (iv) oracle tie (Zq only)
                if ringkind == 'Zq' and oracle is not None:
                    dec_items = [(c, v) for c, (v, _) in verdicts.items() if v[0] == 'D']
                    und_items = [c for c, (v, _) in verdicts.items() if v[0] == 'U']
                    cap = 120 if (n == 4 and N >= 3) or q == 3 else len(dec_items)
                    rng.shuffle(dec_items)
                    ok_iv, tested = True, 0
                    for cls, v in dec_items[:cap]:
                        for trial in range(2):
                            lift = [int(RB.to_int_lift(c, N)) + q ** N * rng.randrange(0, 3)
                                    for c in cls] + [1]
                            got = tuple(sorted(tuple(x) for x in oracle.full_type(lift, q, prec=40)))
                            if got != tuple(sorted(v[1])):
                                ok_iv = False
                                print(f"    ORACLE MISMATCH {cell} cls={cls} reader={v[1]} pari={got}")
                        tested += 1
                    check(f"P2(iv) oracle σ-tie on reader-DECIDED [{cell}] ({tested} classes ×2 lifts)", ok_iv)
                    # ambiguity witnesses on UNDECIDED classes
                    capu = min(len(und_items), 60)
                    rng.shuffle(und_items)
                    wit = 0
                    for cls in und_items[:capu]:
                        seen = set()
                        for trial in range(6):
                            lift = [int(RB.to_int_lift(c, N)) + q ** N * rng.randrange(0, 8)
                                    for c in cls] + [1]
                            seen.add(tuple(sorted(tuple(x) for x in oracle.full_type(lift, q, prec=40))))
                            if len(seen) >= 2: break
                        if len(seen) >= 2: wit += 1
                    print(f"    (info) ambiguity witnesses on reader-UNDECIDED: {wit}/{capu} [{cell}]"
                          f"  (over-drained classes lack witnesses — conservative ⊋ semantic, F-2)")
                    # F-2 regression at (n,q,N) = (3,2,2): exactly these four reader-UNDECIDED
                    # classes are semantically DECIDED (hand proof in the OM-2 note §3; the
                    # oracle scan over all depth-3 lift extensions finds the single type
                    # ((1,1),(2,1)) — the mid-coefficient pins the polygon below the drain).
                    if (n, q, N) == (3, 2, 2):
                        known = [(0, 2, 0), (0, 2, 2), (1, 1, 1), (3, 1, 3)]
                        ok_f2 = True
                        for cls in known:
                            if verdicts[cls][0][0] != 'U': ok_f2 = False
                            seen = set()
                            for ds in itertools.product(range(8), repeat=3):
                                lift = [int(cls[i]) + q ** N * ds[i] for i in range(3)] + [1]
                                seen.add(tuple(sorted(tuple(x)
                                          for x in oracle.full_type(lift, q, prec=40))))
                                if len(seen) >= 2: break
                            if seen != {((1, 1), (2, 1))}: ok_f2 = False
                        check(f"P2(vi) F-2 over-drain witnesses at (3,2,2): 4 classes, "
                              f"single type ((1,1),(2,1))", ok_f2)

# ----------------------------------------------------------------------------------
# PART 3 — the RecursionLegs instantiation on TRUE data (N-3 + CC-3)
# ----------------------------------------------------------------------------------
def part3():
    print("\nPART 3 — RecursionLegs (H71, A-H.2 signature) instantiated by the true complements")
    plan = [(2, 2, 6), (2, 3, 5), (3, 2, 5), (3, 3, 4)]
    if FAST: plan = [(2, 2, 4), (3, 2, 4)]
    for q, m, Nmax in plan:
        Q = q
        c_struct = m * (m + 1) // 2
        check(f"P3 hmc: m < c at intended slope [q={q} m={m}]", m < c_struct)
        # exhaustive tables from the reader (ring Zq; PART 1 proved both rings equal)
        u, drain, alpha_mass, beta_mass, cs_mass, tot = {}, {}, {}, {}, {}, {}
        for W in range(1, Nmax + 1):
            RB = Ring('Zq', q, W * (m + 1) + 4)
            u[W] = drain[W] = alpha_mass[W] = beta_mass[W] = cs_mass[W] = 0
            tot[W] = q ** (m * (W - 1))
            for st in cluster_states(RB, m, W):
                d0 = depth0_data(RB, st, m, W, q)
                v = read_cluster('Zq', q, st, m, W)
                undec = (v[0] == 'U')
                if undec: u[W] += 1
                b = d0['bucket']
                if b == 'DRAIN': drain[W] += 1
                elif b == 'ALPHA' and undec: alpha_mass[W] += 1
                elif b == 'BETA' and undec: beta_mass[W] += 1
                elif b == 'CS': cs_mass[W] += 1
        # normalized legs
        uh = {W: Fraction(u[W], tot[W]) for W in u}
        headh = {W: Fraction(drain[W], tot[W]) for W in u}
        alphah = {W: Fraction(alpha_mass[W], tot[W]) for W in u}
        betah = {W: Fraction(beta_mass[W] + cs_mass[W], tot[W]) for W in u}
        # hsplit (equality), hhead (equality), hu0
        ok = all(uh[W] == headh[W] + alphah[W] + betah[W] for W in u)
        check(f"P3 hsplit as EQUALITY [q={q} m={m}]", ok)
        ok = all(headh[W] == Fraction(1, Q ** (W - 1)) for W in u)
        check(f"P3 hhead as EQUALITY q^-(N-1) [q={q} m={m}]", ok)
        # halpha: windowed sum with the structure slope c = m(m+1)/2 — EQUALITY expected
        ok = True
        for W in u:
            if W < 1: continue
            s = Fraction(0)
            k = 1
            while m * k < W:                    # window condition m*k <= W-1
                s += Fraction(Q - 1, Q ** (c_struct * k)) * uh[W - m * k]
                k += 1
            if alphah[W] != s: ok = False
        check(f"P3 halpha windowed, slope m(m+1)/2, EQUALITY [q={q} m={m}]", ok)
        # CC-3(i): the unwindowed alpha sum would consult u(0) — confirm the boundary case
        # arises (some W = m*k+... i.e. W where m*k = W is in range(n0) unwindowed):
        boundary_hit = any(W % m == 0 and W // m >= 1 for W in u)
        check(f"P3 CC-3(i) unwindowed form would read u(0) at some tested W [q={q} m={m}]",
              boundary_hit)
        # hbeta: find minimal K' at (B', c') = (0, 1): beta <= K' N^m Q^{-(N-1)} ... record
        needK = Fraction(0)
        for W in u:
            bound_unit = Fraction(W ** m, Q ** (W - 2)) if W >= 2 else Fraction(W ** m) * Q
            if bound_unit:
                needK = max(needK, betah[W] / bound_unit)
        check(f"P3 hbeta with (B',c')=(0,1), K'={float(needK):.4f} <= 1 [q={q} m={m}]",
              needK <= 1, f"K'={needK}")
        # species conclusion: RateSpecies Q K B c with (1,1,1) — u(N)/Q^{m(N-1)} <= N Q^{-(N-1)}
        ok = all(uh[W] <= Fraction(W, Q ** (W - 1)) for W in u)
        check(f"P3 RateSpecies (K,B,c)=(1,1,1) on true data [q={q} m={m}]", ok)
        if m == 2:
            # tie to the closed form u(M) = Q^{M-1} + floor((M-1)/2)(Q-1)Q^{M-2}
            ok = all(u[W] == Q ** (W - 1) + ((W - 1) // 2) * (Q - 1) * (Q ** (W - 2) if W >= 2 else 0)
                     for W in u)
            check(f"P3 m=2 closed-form tie (EFF.GENIND.150 / ChapH uTwo) [q={q}]", ok)
    # CC-3(ii): the intended slope satisfies hmc for all m >= 2; boundary c = m unreachable
    ok = all(m < m * (m + 1) // 2 for m in range(2, 13))
    check("P3 CC-3(ii) m < m(m+1)/2 for m=2..12 (A-H.2 boundary c=m unreachable)", ok)

# ----------------------------------------------------------------------------------
# PART 4 — CC-1: the multiset-cancellation defeat scan + the F-1 collision exhibit
# ----------------------------------------------------------------------------------
def types_of_degree(d):
    """all FactorizationType data of degree d: multisets of (e,f) with sum e*f = d."""
    if d == 0: return [()]
    out = set()
    for e in range(1, d + 1):
        for f in range(1, d // e + 1):
            for rest in types_of_degree(d - e * f):
                out.add(tuple(sorted(((e, f),) + rest)))
    return sorted(out)

def part4():
    print("\nPART 4 — CC-1 defeat scan (multiset cancellation) + the F-1 collision exhibit")
    # defeat: factor-A possible-type set TA (>=2 types, all same degree dA), TB likewise,
    # with ALL pairwise unions equal.  Multiset cancellation says infeasible.
    found = None
    for dA in range(1, 4):
        for dB in range(1, 4):
            TAs = types_of_degree(dA)
            TBs = types_of_degree(dB)
            for TA in itertools.combinations(TAs, 2):
                for TB in itertools.combinations(TBs, 2):
                    unions = {tuple(sorted(a + b)) for a in TA for b in TB}
                    if len(unions) == 1:
                        found = (TA, TB)
    check("P4 CC-1: no defeat of decided-composition (deg ≤ 3 exhaustive)", found is None,
          str(found))
    # F-1: the per-type collision — distinct combinations, same frame type
    split2 = ((1, 1), (1, 1))
    inert2 = ((1, 2),)
    u1 = tuple(sorted(split2 + inert2))
    u2 = tuple(sorted(inert2 + split2))
    coll = (u1 == u2)
    combos = {(a, b) for a in (split2, inert2) for b in (split2, inert2)}
    frame_types = {tuple(sorted(a + b)) for (a, b) in combos}
    check("P4 F-1 exhibit: 4 combinations, 3 frame types (per-type census NOT free)",
          coll and len(combos) == 4 and len(frame_types) == 3)

# ----------------------------------------------------------------------------------
def main():
    print("OM-2 GENIND.B battery — exact, exhaustive; q in {2,3}; rings Zq and Fqt")
    u_tables = part1()
    part2()
    part3()
    part4()
    bad = [c for c in CHECKS if not c[1]]
    print(f"\n==== {len(CHECKS)} checks, {len(CHECKS) - len(bad)} passed, {len(bad)} failed ====")
    if bad:
        for name, _, det in bad:
            print(f"  FAILED: {name}  {det}")
        sys.exit(1)
    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
