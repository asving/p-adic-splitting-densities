#!/usr/bin/env python3
"""GENIND passPE8 fresh-route runner (hostile verifier's instrument).

ROUTE (disclosed; differs from ALL NINE prior GENIND routes -- seal battery,
r2 supp, PE1..PE7 fresh legs: none used non-prime BASE q, an m=6 cluster,
an n=12 composite, or a symbolic parametric inclusion-exclusion):
  N1a RAW-EXHAUSTIVE conservative reads over F_q[[t]]/(t^N), q in {4,8,9}
      (FIRST non-prime base q in the arc), cells (2,1,N=2..4), plus q=4
      N=5,6 and (3,1,3) at q in {8,9}, (3,1,4) at q in {3,4}:
      five-species partition, DRAIN=Q^((m-1)(N-1)), ALPHA(k) locus law,
      ZERO beta/CS at m=2, ZERO CS at m=3 (criterion at non-prime q),
      and the S5.2 drain recursion u(N) tied cell-to-cell (both sides
      MEASURED independently; u_2 closed forms: u(2)=Q, u(3)=2Q^2-Q,
      u(4)=2Q^3-Q^2, u(5)=3Q^4-2Q^3, u(6)=3Q^5-2Q^4; u_3(3)=Q^4,
      u_3(4)=Q^6+(Q-1)Q^3 [alpha, child u_3(1)=1] + (Q-1)(Q-2)Q^3
      [the same-side BETA(2,1) genre at k=1, VISIBLE at N=4 (v(a_0)=3
      = N-1), its (2,1,1)-child draining: I-E term = census
      (Q-1)(Q-2) x Q^(3(N-1)-6) x u/T at u=T=1] = Q^6+(Q-1)^2 Q^3;
      derivation corrected pre-run: the first draft missed the beta
      term -- caught by hand-recount BEFORE the first launch).
  N1b PROFILE-EXHAUSTIVE first-step classification at (4,1,N=3,4,5),
      q in {4,8,9} (profiles (v_j, leading digit) x multiplicity
      q^(N-1-v_j) cover the FULL state space exactly; first-step
      classification depends only on the profile): partition, DRAIN law,
      ALPHA law, CS4-E(h)=(q-1)q^(4N-5h-3), CS4-F(k)=(q(q-1)/2)q^(4N-10k-4),
      CS keys confined to the S5.3 grammar.
  N2  n=12 PARI leg at p in {2,5}: TWO independent composite (2,2)-stages
      (E4(h=1) quartic clusters at centers 0 and 1) + an irreducible
      quartic pad in ONE degree-12 polynomial; factorpadic on the full
      degree-12 poly vs the union of the three quartics' factorpadic
      factor-sets (level-0 Hensel composition, W12-S2.1/Step 1, at a
      never-constructed configuration); sigma displayed via
      nfinit+idealprimedec per quartic (PARI, mechanism-free); an
      undecided-composition witness (two lifts of one window-3 f_A state
      with different sigma => the degree-12 window state is undecided:
      'some factor drains').
  N3  THE S5.2 INCLUSION-EXCLUSION, symbolic + at a live 3-child cell:
      (i) sympy: prod T_i - prod(T_i - u_i) == sum over nonempty S of
      (-1)^(|S|+1) prod_S u prod_Sc T, r = 2..8 (the parametric-r identity
      is the binomial expansion; displayed in the report);
      (ii) THE FIRST m=6 CLUSTER CONTACT: (6,1,8) over F_4[[t]], the
      same-side beta genre (2,2,2) (three distinct letters = all of
      F_4^x), a full fiber SECTION f = A*B*C (4,096 composite states,
      children (2,1,2) coords exhaustive): direct frame reads (fresh
      Hensel-split implementation) vs composed child verdicts state by
      state; #undecided == T^3 - (T-u)^3 = 16^3 - 12^3 = 2368 with
      u = u_2(2) = 4 measured at the standalone cell; injectivity of the
      section (4,096 distinct frames mod t^8).
  TEETH T1 (E4 exponent 5h -> 5h-1 must mismatch at q=4,8,9 N=3: 3 fires),
      T2 (I-E with u-1 must mismatch: 1 fire), T3 (perturbed degree-12
      product must break the factor-set match: 2 fires, one per prime).
      Expected fires: 6.

PREREGISTERED numeric predictions (computed from the note's closed forms
BEFORE the first run): u-values above; E4(1) at N=3: q=4: 3*4^4=768,
q=8: 7*8^4=28672, q=9: 8*9^4=52488; F4(1) first visible N=5:
q=4: 6*4^6=24576, q=8: 28*8^6, q=9: 36*9^6; ALPHA(1) at (2,1,4):
(Q-1)Q^3; m=6 section: 4096 states, 2368 undecided, 1728 decided all
sigma {(2,1)x3}. Smoke/instrument arc: disclosed in the report if any
run needed a code repair after first full launch.

Fresh code: shares NO code with genind_checks.py or any committed leg
(the read implements the note's S1 conventions -- ambient-window
conservative drain, exact hull with window-hidden points, residual
trichotomy; spec-sharing is inherent, code is new).
"""
import itertools, json, os, sys, time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
T0 = time.time()
CHECKS = 0
VIOL = []
TEETH_FIRED = 0

def ck(name, ok, detail=''):
    global CHECKS
    CHECKS += 1
    if not ok:
        VIOL.append((name, detail))
        print('VIOLATION', name, detail)

# ---------------- finite fields GF(q), q <= 9 ----------------
class GF:
    """elements are ints 0..q-1 = base-p digit strings (coeff vectors)."""
    MODULI = {2: (1,), 3: (1,), 4: (1, 1), 5: (1,), 8: (1, 1, 0),
              9: (1, 0)}  # non-leading coeffs of monic irred, low first
    PE = {2: (2, 1), 3: (3, 1), 4: (2, 2), 5: (5, 1), 8: (2, 3), 9: (3, 2)}

    def __init__(self, q):
        p, e = GF.PE[q]
        self.p, self.e, self.q = p, e, q
        mod = GF.MODULI[q]
        def dec(a):
            return [(a // p ** i) % p for i in range(e)]
        def enc(v):
            return sum((c % p) * p ** i for i, c in enumerate(v))
        self.add = [[enc([x + y for x, y in zip(dec(a), dec(b))])
                     for b in range(q)] for a in range(q)]
        mul = []
        for a in range(q):
            row = []
            for b in range(q):
                da, db = dec(a), dec(b)
                prod = [0] * (2 * e - 1)
                for i, x in enumerate(da):
                    for j, y in enumerate(db):
                        prod[i + j] = (prod[i + j] + x * y) % p
                for k in range(2 * e - 2, e - 1, -1):  # reduce
                    c = prod[k]
                    if c:
                        prod[k] = 0
                        for i, mc in enumerate(mod):
                            prod[k - e + i] = (prod[k - e + i] - c * mc) % p
                row.append(enc(prod))
            mul.append(row)
        self.mul = mul
        self.neg = [self.q and enc([(-x) % p for x in dec(a)]) for a in range(q)]
        self.inv = [0] * q
        for a in range(1, q):
            for b in range(1, q):
                if mul[a][b] == 1:
                    self.inv[a] = b

FIELDS = {}
def field(q):
    if q not in FIELDS:
        FIELDS[q] = GF(q)
    return FIELDS[q]

# ---------------- F_q[y] helpers (lists, low-first, over GF ints) -----
def pnorm(F, f):
    while f and f[-1] == 0:
        f = f[:-1]
    return f

def padd(F, f, g):
    n = max(len(f), len(g))
    return pnorm(F, [F.add[f[i] if i < len(f) else 0][g[i] if i < len(g) else 0]
                     for i in range(n)])

def pneg(F, f):
    return [F.neg[c] for c in f]

def pmul(F, f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] = F.add[out[i + j]][F.mul[a][b]]
    return pnorm(F, out)

def pdivmod(F, f, g):
    f = list(f); q = []
    dg, lg = len(g) - 1, g[-1]
    li = F.inv[lg]
    q = [0] * max(0, len(f) - dg)
    while len(f) - 1 >= dg and f:
        c = F.mul[f[-1]][li]
        k = len(f) - 1 - dg
        q[k] = c
        for i, b in enumerate(g):
            f[k + i] = F.add[f[k + i]][F.neg[F.mul[c][b]]]
        f = pnorm(F, f)
    return pnorm(F, q), f

def pgcd(F, f, g):
    f, g = pnorm(F, list(f)), pnorm(F, list(g))
    while g:
        f, g = g, pdivmod(F, f, g)[1]
    if f:
        li = F.inv[f[-1]]
        f = [F.mul[c][li] for c in f]
    return f

def pderiv(F, f):
    out = []
    for i in range(1, len(f)):
        c = 0
        for _ in range(i % F.p):
            c = F.add[c][f[i]]
        out.append(c)
    return pnorm(F, out)

def proots(F, f):
    """[(z, mult)] over F_q, plus rootless cofactor."""
    out = []
    cof = pnorm(F, list(f))
    for z in range(F.q):
        mult = 0
        while cof and len(cof) > 1:
            q2, r = pdivmod(F, cof, [F.neg[z], 1])
            if r:
                break
            cof = q2
            mult += 1
        if mult:
            out.append((z, mult))
    return out, cof

# monic irreducibles over F_q up to degree 3 (for cofactor factoring)
IRRCACHE = {}
def irreducibles(F, maxdeg):
    key = (F.q, maxdeg)
    if key in IRRCACHE:
        return IRRCACHE[key]
    irr = []
    for d in range(1, maxdeg + 1):
        for tup in itertools.product(range(F.q), repeat=d):
            f = list(tup) + [1]
            if any(pdivmod(F, f, g)[1] == [] for g in irr if len(g) - 1 <= d // 2):
                continue
            irr.append(f)
    IRRCACHE[key] = irr
    return irr

def pfactor_rootless(F, f):
    """factor a rootless separable poly into irreducible degrees."""
    degs = []
    f = pnorm(F, list(f))
    for g in irreducibles(F, (len(f) - 1) // 2 if len(f) > 1 else 0):
        while len(f) > 1:
            q2, r = pdivmod(F, f, g)
            if r:
                break
            f = q2
            degs.append(len(g) - 1)
    if len(f) > 1:
        degs.append(len(f) - 1)
    return degs

# ---------------- the ring F_q[[t]]/(t^W): tuples length W --------------
def rzero(W):
    return (0,) * W

def radd(F, a, b):
    return tuple(F.add[x][y] for x, y in zip(a, b))

def rneg(F, a):
    return tuple(F.neg[x] for x in a)

def rmul(F, a, b, W):
    out = [0] * W
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y and i + j < W:
                    out[i + j] = F.add[out[i + j]][F.mul[x][y]]
    return tuple(out)

def rval(a):
    for i, x in enumerate(a):
        if x:
            return i
    return None

def rmono(F, c, k, W):  # c * t^k
    v = [0] * W
    if k < W:
        v[k] = c
    return tuple(v)

# ---------------- polygon + conservative read (fresh implementation) ----
def lower_hull(pts):
    """pts sorted by x; lower convex hull as list of pts."""
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep if p makes hull[-1] strictly above chord hull[-2]->p
            if (y2 - y1) * (p[0] - x1) >= (p[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(p)
    return hull

from math import gcd as _gcd

def sides_of_frame(F, W, coeffs, m):
    """coeffs: list of m ring elements (a_0..a_{m-1}), monic frame.
    Returns [(j0,y0,j1,y1,e,h,g,res)] with res the residual poly over F."""
    pts = []
    for j, a in enumerate(coeffs):
        v = rval(a)
        if v is not None and v < W:
            pts.append((j, v))
    pts.append((m, 0))
    hull = lower_hull(pts)
    # walk hull segments from (j0=first) down to (m,0); keep descending ones
    sides = []
    for i in range(len(hull) - 1):
        (j0, y0), (j1, y1) = hull[i], hull[i + 1]
        if y0 <= y1:
            continue  # not descending (cannot happen on lower hull to (m,0))
        dh, dj = y0 - y1, j1 - j0
        g0 = _gcd(dh, dj)
        h, e = dh // g0, dj // g0
        gg = dj // e
        res = []
        for i2 in range(gg + 1):
            j = j0 + i2 * e
            y = y0 - i2 * h
            if j == m:
                res.append(1)
            else:
                v = rval(coeffs[j])
                res.append(coeffs[j][y] if (v is not None and v == y) else 0)
        sides.append((j0, y0, j1, y1, e, h, gg, res))
    return sides

def classify_step(F, W, coeffs, m):
    """One read step. Returns (kind, data):
      ('DRAIN',), ('DEC', pieces), ('ALPHA', k, z), ('BETA', children, pieces),
      ('CS', records). children: [(mu, k(=h, e=1 slope), z, j0)]."""
    if rval(coeffs[0]) is None or rval(coeffs[0]) >= W:
        return ('DRAIN', None)
    sides = sides_of_frame(F, W, coeffs, m)
    pieces, children, cs = [], [], []
    for (j0, y0, j1, y1, e, h, g, res) in sides:
        roots, cof = proots(F, res)
        for (z, mu) in roots:
            assert z != 0 or j0 > 0
            if mu == 1:
                pieces.append((e, 1))
            elif e == 1:
                children.append((mu, h, z, j0))
            else:
                cs.append((j0, j1, e, 1, mu, h))
        if len(cof) > 1:
            dC = pderiv(F, cof)
            if not dC:
                # char-p zero-derivative rootless cofactor: over a perfect
                # field this is psi^p with psi irreducible; at char 2 /
                # cofdeg 4 it is psi^2, deg psi = 2 (the F4 genre) --
                # instrument arc: run 1 mis-keyed this as (e,4,0,h)
                assert F.p == 2 and len(cof) - 1 == 4, 'p-power cofactor'
                cs.append((j0, j1, e, 2, 2, h))
            else:
                G = pgcd(F, cof, dC)
                if len(G) > 1:
                    cs.append((j0, j1, e, len(G) - 1, 2, h))
                else:
                    for dpi in pfactor_rootless(F, cof):
                        pieces.append((e, dpi))
    if cs:
        return ('CS', tuple(cs))
    if (len(sides) == 1 and sides[0][4] == 1 and len(children) == 1
            and children[0][0] == m and not pieces):
        return ('ALPHA', children[0][1], children[0][2])
    if children:
        return ('BETA', children, pieces)
    return ('DEC', tuple(sorted(pieces)))

def poly_taylor(F, coeffs, m, s, W):
    """f(x+s) for monic frame: returns new a_0..a_{m-1} (monic preserved)."""
    full = list(coeffs) + [tuple([1] + [0] * (W - 1))]
    # synthetic division repeatedly: f(x) = sum b_i (x-(-s))^i ... use Horner
    out = []
    work = list(full)
    for i in range(m + 1):
        # divide work by (x - s): remainder = coefficient i of f(x+s)? use
        # repeated synthetic division by root s: f(x) = q(x)(x-s)+r
        if not work:
            break
        rem = work[-1]
        newq = [work[-1]]
        for c in reversed(work[:-1]):
            rem = radd(F, c, rmul(F, rem, s, W))
            newq.append(rem)
        newq.reverse()
        out.append(newq[0])       # f_i coefficient of (x-s)^i
        work = newq[1:]
    return out[:m]

def ext_bezout(F, a, b):
    """monic-ish ext gcd: returns (g, u, v) with u*a+v*b = g."""
    r0, r1 = pnorm(F, list(a)), pnorm(F, list(b))
    s0, s1 = [1], []
    t0, t1 = [], [1]
    while r1:
        q, r = pdivmod(F, r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, padd(F, s0, pneg(F, pmul(F, q, s1)))
        t0, t1 = t1, padd(F, t0, pneg(F, pmul(F, q, t1)))
    return r0, s0, t0

def hensel_split(F, W, gcoeffs, factors0):
    """g monic deg n over ring (list of ring elts len n+1, top = 1);
    factors0: list of coprime monic polys over F (residual factors, as
    F[y] lists) with product = g mod t. Lift to mod t^W by iterated
    two-factor Hensel. Returns list of monic ring-coefficient polys."""
    if len(factors0) == 1:
        return [gcoeffs]
    A0 = factors0[0]
    B0 = [1]
    for f0 in factors0[1:]:
        B0 = pmul(F, A0 and B0, f0) if False else pmul(F, B0, f0)
    # two-factor lift g = A*B with A ≡ A0, B ≡ B0 mod t
    g1, u, v = ext_bezout(F, A0, B0)
    assert len(g1) == 1  # coprime
    ginv = F.inv[g1[0]]
    u = [F.mul[c][ginv] for c in u]
    v = [F.mul[c][ginv] for c in v]
    dA, dB = len(A0) - 1, len(B0) - 1
    A = [rmono(F, c, 0, W) for c in A0]
    B = [rmono(F, c, 0, W) for c in B0]
    for prec in range(1, W):
        # E = g - A*B, per t^prec digit
        AB = ring_pmul(F, A, B, W)
        E = [radd(F, gc, rneg(F, ab)) for gc, ab in zip(gcoeffs, AB)]
        Ed = [e[prec] if prec < W else 0 for e in E]  # F[y] poly, digit prec
        Ed = pnorm(F, Ed)
        if Ed:
            # delta_A = v*Ed mod A0, delta_B = u*Ed mod B0
            dAp = pdivmod(F, pmul(F, v, Ed), A0)[1]
            dBp = pdivmod(F, pmul(F, u, Ed), B0)[1]
            for i, c in enumerate(dAp):
                if i <= dA:
                    A[i] = radd(F, A[i], rmono(F, c, prec, W))
            for i, c in enumerate(dBp):
                if i <= dB:
                    B[i] = radd(F, B[i], rmono(F, c, prec, W))
    rest = hensel_split(F, W, B, factors0[1:])
    return [A] + rest

def ring_pmul(F, A, B, W):
    out = [rzero(W) for _ in range(len(A) + len(B) - 1)]
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            out[i + j] = radd(F, out[i + j], rmul(F, a, b, W))
    return out

def read_frame(F, W, coeffs, m, events=None, depth=0):
    """Full conservative read. Returns (verdict, sigma):
    verdict in {'UNDEC','DEC','CS'}; UNDEC = conservative drain (no CS on
    the path), CS = a CS event anywhere on the path. events: list to
    append the FIRST-step species key to (top frame only)."""
    assert depth < 40
    cur = list(coeffs)
    first = True
    it = 0
    while True:
        it += 1
        assert it <= 6 * W + 12
        kind = classify_step(F, W, cur, m)
        if first and events is not None:
            if kind[0] == 'ALPHA':
                events.append(('ALPHA', kind[1]))
            elif kind[0] == 'BETA':
                key = tuple(sorted(mu for (mu, k, z, j0) in kind[1]))
                events.append(('BETA', key))
            elif kind[0] == 'CS':
                events.append(('CS', kind[1]))
            else:
                events.append((kind[0],))
        first = False
        if kind[0] == 'DRAIN':
            return 'UNDEC', None
        if kind[0] == 'DEC':
            return 'DEC', kind[1]
        if kind[0] == 'CS':
            return 'CS', None
        if kind[0] == 'ALPHA':
            k, z = kind[1], kind[2]
            s = rmono(F, z, k, W)
            cur = poly_taylor(F, cur, m, s, W)
            continue
        # BETA: fracture via exact Hensel split of the scaled side frames.
        # Only same-side multi-children/one-side cases needed by this
        # runner's cells occur; handle the general one-side-at-slope-k,
        # k integer, e=1 case: scale by t^k and Hensel-split the side
        # residual factorization (children + simple pieces + cofactor).
        (kindname, children, pieces) = kind
        sides = sides_of_frame(F, W, cur, m)
        ck('read-beta-single-side', len(sides) == 1,
           'multi-side beta not needed by these cells')
        (j0, y0, j1, y1, e, h, g, res) = sides[0]
        assert e == 1 and j0 == 0 and j1 == m
        M = W - m * h  # scaled window: g_j = a_j t^{j-m*h*...}; min at j=0
        if M <= 0:
            return 'UNDEC', None
        # scaled frame: G_j = a_j / t^{(m-j)h}, truncated to t^M
        G = []
        for j in range(m):
            a = cur[j]
            sh = (m - j) * h
            G.append(tuple(list(a[sh:sh + M]) + [0] * max(0, M - (W - sh))))
        G.append(tuple([1] + [0] * (M - 1)))
        roots, cof = proots(F, res)
        f0s = []
        for (z, mu) in roots:
            f0s.append(pnorm(F, poly_pow_linear(F, z, mu)))
        if len(cof) > 1:
            f0s.append([F.mul[c][F.inv[cof[-1]]] for c in cof])
        facs = hensel_split(F, M, G, f0s)
        verdicts = []
        idx = 0
        for (z, mu) in roots:
            fac = facs[idx]; idx += 1
            if mu == 1:
                continue  # decided piece
            # recenter the child cluster at z: y -> y + z
            # (fac is the full monic factor: mu+1 coeffs; poly_taylor
            # takes the m-coefficient frame and supplies the leading 1)
            assert rval(fac[mu]) == 0 and fac[mu][0] == 1, 'non-monic factor'
            ch = poly_taylor(F, fac[:mu], mu, rmono(F, z, 0, M), M)
            v2, s2 = read_frame(F, M, ch, mu, None, depth + 1)
            verdicts.append((v2, s2))
        if any(v == 'CS' for v, _ in verdicts):
            return 'CS', None
        if any(v == 'UNDEC' for v, _ in verdicts):
            return 'UNDEC', None
        sig = list(pieces)  # classify_step already recorded simple-root
        # pieces AND separable-cofactor pieces; do not re-add them.
        for v2, s2 in verdicts:
            sig.extend(list(s2))
        return 'DEC', tuple(sorted(sig))

def poly_pow_linear(F, z, mu):
    f = [1]
    for _ in range(mu):
        f = pmul(F, f, [F.neg[z], 1])
    return f

# ================= LEG N1a: raw-exhaustive cells =================
def all_states(F, W, m):
    digits = list(itertools.product(range(F.q), repeat=W - 1))
    ringvals = [tuple([0] + list(d)) for d in digits]  # v >= 1
    return itertools.product(ringvals, repeat=m)

def run_raw_cell(q, m, N):
    F = field(q)
    tal = {}
    undec = 0
    for st in all_states(F, N, m):
        ev = []
        v, s = read_frame(F, N, list(st), m, ev)
        key = ev[0]
        kk = key if key[0] != 'CS' else ('CS', key[1])
        tal[kk] = tal.get(kk, 0) + 1
        if v == 'UNDEC':
            undec += 1
        ck('raw-no-CS-m%d' % m, v != 'CS', str(st))
    total = sum(tal.values())
    ck('raw-total-q%d-m%d-N%d' % (q, m, N), total == q ** (m * (N - 1)))
    ck('raw-drain-law', tal.get(('DRAIN',), 0) == q ** ((m - 1) * (N - 1)),
       'q%d m%d N%d got %d' % (q, m, N, tal.get(('DRAIN',), 0)))
    for k in range(1, N):
        if m * k <= N - 1:
            pred = (q - 1) * q ** (m * (N - 1) - k * m * (m + 1) // 2)
            ck('raw-alpha-law-k%d' % k, tal.get(('ALPHA', k), 0) == pred,
               'q%d m%d N%d got %d want %d'
               % (q, m, N, tal.get(('ALPHA', k), 0), pred))
    if m == 2:
        ck('raw-no-beta-m2',
           not any(k[0] == 'BETA' for k in tal), str(sorted(tal)))
    return tal, undec

U2 = {}   # measured u_2 per (q, N)
U3 = {}

def leg_N1a():
    print('== N1a raw-exhaustive, q in {3,4,8,9} ==')
    preds2 = {2: lambda Q: Q, 3: lambda Q: 2 * Q * Q - Q,
              4: lambda Q: 2 * Q ** 3 - Q ** 2,
              5: lambda Q: 3 * Q ** 4 - 2 * Q ** 3,
              6: lambda Q: 3 * Q ** 5 - 2 * Q ** 4}
    for q in (4, 8, 9):
        for N in (2, 3, 4):
            tal, u = run_raw_cell(q, 2, N)
            U2[(q, N)] = u
            ck('u2-closed-form-q%d-N%d' % (q, N), u == preds2[N](q),
               'got %d want %d' % (u, preds2[N](q)))
    for N in (5, 6):
        tal, u = run_raw_cell(4, 2, N)
        U2[(4, N)] = u
        ck('u2-closed-form-q4-N%d' % N, u == preds2[N](4),
           'got %d want %d' % (u, preds2[N](4)))
    # recursion tie (both sides measured): u(N) = Q^{N-1}+sum (Q-1)Q^k u(N-2k)
    for (q, N) in [(4, 4), (8, 4), (9, 4), (4, 5), (4, 6)]:
        rhs = q ** (N - 1)
        for k in range(1, N):
            if 2 * k > N - 1:
                break
            um = 1 if N - 2 * k == 1 else U2[(q, N - 2 * k)]
            rhs += (q - 1) * q ** k * um
        ck('u2-recursion-tie-q%d-N%d' % (q, N), U2[(q, N)] == rhs,
           'lhs %d rhs %d' % (U2[(q, N)], rhs))
    for q in (8, 9):
        tal, u = run_raw_cell(q, 3, 3)
        U3[(q, 3)] = u
        ck('u3-N3-q%d' % q, u == q ** 4, 'got %d want %d' % (u, q ** 4))
    for q in (3, 4):
        tal, u = run_raw_cell(q, 3, 4)
        U3[(q, 4)] = u
        pred = q ** 6 + (q - 1) ** 2 * q ** 3
        ck('u3-N4-q%d' % q, u == pred, 'got %d want %d' % (u, pred))
    print('   N1a done', time.time() - T0)

# ================= LEG N1b: profile-exhaustive (4,1,N) =================
def leg_N1b():
    global TEETH_FIRED
    print('== N1b profile-exhaustive (4,1,N), q in {4,8,9} ==')
    for q in (4, 8, 9):
        F = field(q)
        for N in (3, 4, 5):
            profs = [(None, 0, 1)]
            for v in range(1, N):
                for c in range(1, q):
                    profs.append((v, c, q ** (N - 1 - v)))
            tal = {}
            for combo in itertools.product(profs, repeat=4):
                mult = 1
                coeffs = []
                for (v, c, mu) in combo:
                    mult *= mu
                    coeffs.append(rmono(F, c, v, N) if v is not None
                                  else rzero(N))
                kind = classify_step(F, N, coeffs, 4)
                if kind[0] == 'CS':
                    recs = kind[1]
                    ck('cs-grammar-span', all(r[0] == 0 and r[1] == 4
                                              for r in recs), str(recs))
                    r = recs[0]
                    if r[2] == 2 and r[3] == 1 and r[4] == 2:
                        key = ('CS-E4', r[5])
                    elif r[2] == 1 and r[3] == 2:
                        key = ('CS-F4', r[5])
                    else:
                        key = ('CS-OTHER', r)
                elif kind[0] == 'ALPHA':
                    key = ('ALPHA', kind[1])
                elif kind[0] == 'BETA':
                    key = ('BETA', tuple(sorted(mu for (mu, k, z, j) in
                                                kind[1])))
                else:
                    key = (kind[0],)
                tal[key] = tal.get(key, 0) + mult
            total = sum(tal.values())
            ck('prof-total-q%d-N%d' % (q, N), total == q ** (4 * (N - 1)))
            ck('prof-drain', tal.get(('DRAIN',), 0) == q ** (3 * (N - 1)))
            ck('prof-no-cs-other',
               not any(k[0] == 'CS-OTHER' for k in tal), str(sorted(tal)))
            for k in range(1, N):
                if 4 * k <= N - 1:
                    pred = (q - 1) * q ** (4 * (N - 1) - 10 * k)
                    ck('prof-alpha-law', tal.get(('ALPHA', k), 0) == pred)
            for h in (1, 3):
                pred = ((q - 1) * q ** (4 * N - 5 * h - 3)
                        if (h % 2 == 1 and 2 * h <= N - 1) else 0)
                ck('prof-E4-law-q%d-N%d-h%d' % (q, N, h),
                   tal.get(('CS-E4', h), 0) == pred,
                   'got %d want %d' % (tal.get(('CS-E4', h), 0), pred))
            for k in (1,):
                pred = ((q * (q - 1) // 2) * q ** (4 * N - 10 * k - 4)
                        if 4 * k <= N - 1 else 0)
                ck('prof-F4-law-q%d-N%d-k%d' % (q, N, k),
                   tal.get(('CS-F4', k), 0) == pred,
                   'got %d want %d' % (tal.get(('CS-F4', k), 0), pred))
            if N == 3:  # TOOTH T1: corrupted exponent must mismatch
                bad = (q - 1) * q ** (4 * N - (5 * 1 - 1) - 3)
                if tal.get(('CS-E4', 1), 0) != bad:
                    TEETH_FIRED += 1
                else:
                    ck('T1-tooth-failed-to-fire', False, 'q%d' % q)
    print('   N1b done', time.time() - T0)

# ================= LEG N3: inclusion-exclusion =================
def leg_N3():
    global TEETH_FIRED
    print('== N3 I-E symbolic + m=6 section over F_4[[t]] ==')
    # (i) symbolic identity, exact multivariate polys as dicts
    def paddm(f, g):
        out = dict(f)
        for k, v in g.items():
            out[k] = out.get(k, 0) + v
            if out[k] == 0:
                del out[k]
        return out
    def pmulm(f, g):
        out = {}
        for k1, v1 in f.items():
            for k2, v2 in g.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                out[k] = out.get(k, 0) + v1 * v2
                if out[k] == 0:
                    del out[k]
        return out
    for r in range(2, 9):
        nv = 2 * r  # T_1..T_r, u_1..u_r
        def var(i):
            e = [0] * nv
            e[i] = 1
            return {tuple(e): 1}
        one = {tuple([0] * nv): 1}
        Ts = [var(i) for i in range(r)]
        us = [var(r + i) for i in range(r)]
        lhs = one
        for T in Ts:
            lhs = pmulm(lhs, T)
        rest = one
        for i in range(r):
            rest = pmulm(rest, paddm(Ts[i], {k: -v for k, v in us[i].items()}))
        lhs = paddm(lhs, {k: -v for k, v in rest.items()})
        rhs = {}
        for ssize in range(1, r + 1):
            for S in itertools.combinations(range(r), ssize):
                term = one
                for i in range(r):
                    term = pmulm(term, us[i] if i in S else Ts[i])
                sign = 1 if ssize % 2 == 1 else -1
                rhs = paddm(rhs, {k: sign * v for k, v in term.items()})
        ck('IE-symbolic-r%d' % r,
           paddm(lhs, {k: -v for k, v in rhs.items()}) == {})
    # bracket identity m=2..6 (c=1,3,6,10,15), mu=1..6, polynomial in Q
    def qp(e, c0=1):  # c0 * Q^e as dict-poly
        return {(e,): c0}
    for m in range(2, 7):
        c = m * (m - 1) // 2
        for mu in range(1, 7):
            lhs = {}
            def comps(s):
                if s == 0:
                    yield ()
                for k in range(1, s + 1):
                    for rest in comps(s - k):
                        yield (k,) + rest
            for comp in comps(mu):
                if not comp:
                    continue
                term = {(0,): 1}
                for k in comp:
                    term = pmulm(term, paddm(qp(c * k + 1), {(c * k,): -1}))
                lhs = paddm(lhs, term)
            rhs = paddm(qp((c + 1) * mu), {((c + 1) * mu - 1,): -1})
            ck('bracket-m%d-mu%d' % (m, mu),
               paddm(lhs, {k: -v for k, v in rhs.items()}) == {})
    # (ii) the m=6 section over F_4[[t]], W=8, letters = all of F_4^x
    F = field(4)
    W = 8
    letters = [1, 2, 3]
    u_meas = U2[(4, 2)]
    T = 4 ** 2
    seen = set()
    n_undec = n_dec = 0
    child_verdicts = {}
    for c1 in range(4):
        for c0 in range(4):
            S = [radd(F, rmono(F, c0, 1, 2), rzero(2)),
                 rmono(F, c1, 1, 2)]
            v, s = read_frame(F, 2, S, 2)
            child_verdicts[(c1, c0)] = v
    ck('child-cell-u', sum(1 for v in child_verdicts.values()
                           if v == 'UNDEC') == u_meas)
    for chs in itertools.product(range(4), repeat=6):
        (a1, a0, b1, b0, d1, d0) = chs
        polys = []
        for (z, c1, c0) in ((letters[0], a1, a0), (letters[1], b1, b0),
                            (letters[2], d1, d0)):
            # A(x) = (x - tz)^2 + t^2 c1 (x - tz) + t^3 c0
            lin = [rneg(F, rmono(F, z, 1, W)), rmono(F, 1, 0, W)]
            Apoly = ring_pmul(F, lin, lin, W)
            Apoly = [radd(F, Apoly[0], rmono(F, c0, 3, W)),
                     radd(F, Apoly[1], rzero(W)), Apoly[2]]
            corr = [rmul(F, rmono(F, c1, 2, W), lc, W) for lc in lin]
            Apoly = [radd(F, Apoly[0], corr[0]),
                     radd(F, Apoly[1], corr[1]), Apoly[2]]
            polys.append(Apoly)
        f = ring_pmul(F, ring_pmul(F, polys[0], polys[1], W), polys[2], W)
        frame = f[:6]
        seen.add(tuple(frame))
        v, s = read_frame(F, W, list(frame), 6)
        pred_undec = any(child_verdicts[(chs[2 * i], chs[2 * i + 1])]
                         == 'UNDEC' for i in range(3))
        ck('m6-composed-verdict', (v == 'UNDEC') == pred_undec,
           str(chs) + ' got ' + v)
        if v == 'UNDEC':
            n_undec += 1
        else:
            n_dec += 1
            ck('m6-decided-sigma', tuple(sorted(s)) ==
               ((2, 1), (2, 1), (2, 1)), str(s))
    ck('m6-section-injective', len(seen) == 4096, str(len(seen)))
    ck('m6-IE-count', n_undec == T ** 3 - (T - u_meas) ** 3,
       'got %d want %d' % (n_undec, T ** 3 - (T - u_meas) ** 3))
    if n_undec != T ** 3 - (T - (u_meas - 1)) ** 3:  # TOOTH T2
        TEETH_FIRED += 1
    else:
        ck('T2-tooth-failed-to-fire', False)
    print('   N3 done: undec %d dec %d' % (n_undec, n_dec), time.time() - T0)

# ================= LEG N2: n=12 two-CS-stage PARI leg =================
def leg_N2():
    global TEETH_FIRED
    print('== N2 n=12 two composite stages + pad, PARI, p in {2,5} ==')
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(2 ** 28)
    import random
    rng = random.Random(20260809)
    for p in (2, 5):
        pad = None  # search an irreducible monic quartic mod p
        for c1 in range(p):
            for c0 in range(1, p):
                cand = pari.Polrev([c0, c1, 0, 0, 1])
                if bool(pari.polisirreducible(cand * pari.Mod(1, p))):
                    pad = cand
                    break
            if pad is not None:
                break
        ck('pad-irreducible-mod-p', pad is not None and
           bool(pari.polisirreducible(pad * pari.Mod(1, p))))
        sig_seen = set()
        n_lifts = 15
        for it in range(n_lifts):
            def e4_quartic(center, seed):
                r = random.Random(seed)
                a3 = p * r.randrange(p ** 6)
                a2 = -2 * p + p ** 2 * r.randrange(p ** 6)
                a1 = p ** 2 * r.randrange(p ** 6)
                a0 = p ** 2 * (1 + p * r.randrange(p ** 6))
                x = pari('x')
                y = x - center
                return (y ** 4 + a3 * y ** 3 + a2 * y ** 2 + a1 * y + a0)
            fA = e4_quartic(0, (p, it, 'A'))
            fB = e4_quartic(1, (p, it, 'B'))
            f12 = fA * fB * pad
            ck('n12-disc-nonzero', pari.poldisc(f12) != 0)
            prec = 40
            facs12 = pari.factorpadic(f12, p, prec)
            parts = []
            for g in (fA, fB, pad):
                fp = pari.factorpadic(g, p, prec)
                for i in range(int(pari.matsize(fp)[0])):
                    parts.append(fp[0][i])
            ck('n12-factor-count',
               int(pari.matsize(facs12)[0]) == len(parts),
               'p%d it%d %d vs %d' % (p, it, int(pari.matsize(facs12)[0]),
                                      len(parts)))
            # match each degree-12 padic factor to one constructed part
            used = [False] * len(parts)
            allmatch = True
            for i in range(int(pari.matsize(facs12)[0])):
                h = facs12[0][i]
                hit = False
                for j, g in enumerate(parts):
                    if used[j] or pari.poldegree(g) != pari.poldegree(h):
                        continue
                    d = h - g
                    if d == 0 or min(
                        [prec] + [int(pari.valuation(c, p))
                                  for c in pari.Vec(d) if c != 0]) >= 15:
                        used[j] = True
                        hit = True
                        break
                allmatch = allmatch and hit
            ck('n12-factor-set-match', allmatch, 'p%d it%d' % (p, it))
            # sigma via nfinit+idealprimedec per rational irreducible factor
            sig = []
            for g in (fA, fB, pad):
                gf = pari.factor(g)
                for i in range(int(pari.matsize(gf)[0])):
                    gi = gf[0][i]
                    if pari.poldegree(gi) < 1:
                        continue
                    nf = pari.nfinit([gi, [p]])
                    for pr in pari.idealprimedec(nf, p):
                        sig.append((int(pr[2]), int(pr[3])))  # (e, f)
            sig = tuple(sorted(sig))
            ck('n12-sigma-degree', sum(e * f for (e, f) in sig) == 12,
               str(sig))
            sig_seen.add(sig)
        ck('n12-stage-variety', len(sig_seen) >= 3,
           'p%d saw %s' % (p, sorted(sig_seen)))
        print('   p=%d sigma multiset variety over %d lifts: %d shapes'
              % (p, n_lifts, len(sig_seen)))
        # undecided-composition witness: lifts of ONE window-3 f_A state
        # (base digits mod p^3 identical; grid over the first out-of-
        # window digits of a_0 and a_1) with >= 2 distinct sigma --
        # instrument arc: run 1 varied only a height-4 digit of a_0
        # (too deep at p=5) and pre-excused p=2; both repaired
        x = pari('x')
        wit = set()
        for d3 in range(p):
            for e3 in range(p):
                a0 = p ** 2 + p ** 3 * d3
                a1 = p ** 3 * e3
                fA = x ** 4 + (-2 * p) * x ** 2 + a1 * x + a0
                if pari.poldisc(fA) == 0:
                    continue
                nf_sigs = []
                gf = pari.factor(fA)
                for i in range(int(pari.matsize(gf)[0])):
                    gi = gf[0][i]
                    if pari.poldegree(gi) < 1:
                        continue
                    nf = pari.nfinit([gi, [p]])
                    for pr in pari.idealprimedec(nf, p):
                        nf_sigs.append((int(pr[2]), int(pr[3])))
                wit.add(tuple(sorted(nf_sigs)))
        ck('n12-undecided-witness', len(wit) > 1,
           'p%d window-3 E4 state sigma set: %s' % (p, sorted(wit)))
        print('   p=%d witness sigma set: %s' % (p, sorted(wit)))
        # TOOTH T3: perturb f12 mid-coefficient by p^10: match must break
        fA = e4_quartic(0, (p, 0, 'A'))
        fB = e4_quartic(1, (p, 0, 'B'))
        f12b = fA * fB * pad + p ** 10 * pari('x') ** 6
        facsb = pari.factorpadic(f12b, p, prec)
        parts = []
        for g in (fA, fB, pad):
            fp = pari.factorpadic(g, p, prec)
            for i in range(int(pari.matsize(fp)[0])):
                parts.append(fp[0][i])
        broke = int(pari.matsize(facsb)[0]) != len(parts)
        if not broke:
            used = [False] * len(parts)
            for i in range(int(pari.matsize(facsb)[0])):
                h = facsb[0][i]
                hit = False
                for j, g in enumerate(parts):
                    if used[j] or pari.poldegree(g) != pari.poldegree(h):
                        continue
                    d = h - g
                    if d == 0 or min(
                        [prec] + [int(pari.valuation(c, p))
                                  for c in pari.Vec(d) if c != 0]) >= 15:
                        used[j] = True
                        hit = True
                        break
                if not hit:
                    broke = True
        if broke:
            TEETH_FIRED += 1
        else:
            ck('T3-tooth-failed-to-fire', False, 'p%d' % p)
    print('   N2 done', time.time() - T0)

def main():
    leg_N1a()
    leg_N1b()
    leg_N3()
    leg_N2()
    out = {'checks': CHECKS, 'violations': VIOL, 'teeth_fired': TEETH_FIRED,
           'teeth_expected': 6, 'u2': {str(k): v for k, v in U2.items()},
           'u3': {str(k): v for k, v in U3.items()},
           'elapsed': round(time.time() - T0, 1)}
    with open(os.path.join(HERE, 'genind_pe8_fresh_results.json'), 'w') as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    ok = (not VIOL) and TEETH_FIRED == 6
    print('VERDICT: %s -- %d checks, %d violations, teeth %d/6, %.1f s'
          % ('GREEN' if ok else 'RED', CHECKS, len(VIOL), TEETH_FIRED,
             time.time() - T0))
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
