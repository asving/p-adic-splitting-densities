#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENH4 ANNEX R SUPPLEMENTARY LEG (post-ratification, CODEX F1-F5).

Supports the dated ANNEX R appended to GENH4_PROOF_2026-08-08.md after
the Codex ratification CHALLENGE (CODEX_GENH4RAT_2026-08-09.md).  The
heavy item is F2: ANNEX-LEMMA GENH4-7's "hidden" gloss pinned the
genre-F boundary-band digits that the sealed law_F frees (deep0 =
q^{k-1}); the corrected ANNEX-LEMMA GENH4-7' quantifies over the FREE
band digits.  The k >= 2 AND N >= 4k+3 slice (first live for
F-SPLTAIL) had ZERO machine exercise before this leg: every committed
F-SPLTAIL key is k = 1.  This leg exercises the first live cell
(q,N,k) = (2,11,2), SPLTAIL(5), 2w = 10 < N = 11, BOTH
characteristics.  Precedent: genh4annex_supp.py (ANNEX PE5 leg).
Nothing sealed is written.

PREREGISTERED PREDICTIONS (derived in ANNEX R BEFORE this run):

R1 (CODEX F1, the pre2 six-key partition): the committed
   genh4_checks_results.json pre2 row (Zp,2,11,pre=(1,2)) carries
   EXACTLY six keys: the four law-kind keys of P-3's display --
   E-RAM(21) = 32,768, E-UND = 32,768, G2(5,'2') = 65,536,
   RAM4(9) = 524,288 -- PLUS the non-law remainder
   VTX((0,10),(1,7),(4,0)) = 131,072 = 2^17 and L1TAIL = 262,144 =
   2^18, summing to 1,048,576 = 2^20 EXACTLY.  The two remainder
   counts are FORCED by the pre2 floored box (chain (1,2): floors
   v(B_j) >= 9,7,5,3; free digits 2+4+6+8 = 20): VTX = the
   v(B0) = 10 exact AND v(B1) = 7 exact stratum = 1*2^3*2^6*2^8;
   L1TAIL = the v(B0) >= 11 stratum = 2^{4+6+8}.
R2 (first-live geometry): the fresh S6-typed law at k = 2 has NO
   SPLTAIL key at N = 9, 10 and first realizes SPLTAIL (at w = 5
   only) at N = 11 = 4k+3; the committed fresh row consF
   (Zp,2,9,k2) has no SPLTAIL key; EVERY committed genre-F SPLTAIL
   key in qscout22_results.json + genh4_checks_results.json is
   k = 1 (rows 15/16/19 + feven: SPLTAIL(3) only).
R3 (law tie at the new cell): the SEALED runner's law_F(2,11,2)
   gives SPLTAIL(5) = 24,576 = (q^2-1) * 2^12 * deep0 with
   deep0 = 2 = q^{k-1}, tying the fresh S6 typing KEY-FOR-KEY on
   the full (2,11,2) table; per-psi node mass closes to 2^20; the
   OLD-gloss family (band digit PINNED zero) counts 12,288 = HALF
   the sealed leaf -- the gloss's family is a strict subfamily,
   mismatching the sealed law by exactly the deep0 factor.
R4 (floor enumeration, characteristic-blind digit layer): all
   24,576 leaf members enumerated; EVERY member satisfies the
   GENH4-7' floor (v(a0) >= 11 in-window, v(a1) >= 10, so
   u_state >= N = 11 > 10 = 2w); EXACTLY 12,288 (the band-nonzero
   half, v(a1) = 10) VIOLATE the old gloss's hypothesis
   "a1-positions <= N-1 all vanish" (v(a1) >= 11); ZERO violate
   GENH4-7'.
R5 (char 0 sigma, the substance): 96 constructed lifts (24 states:
   3 pin letters x 2 band values x 4 A1-completions; 4 lifts each,
   incl. the A0 = 0 corner and a u_lift = N = 11 lift) over the
   key phi = x^2 + 4x + 16 (v(p1) = 2 >= k, v(p0) = 4 = 2k exact,
   psi = y^2 + y + 1): every lift has disc != 0 and PARI sigma =
   {(1,2),(1,2)} == the F-SPLTAIL label -- in particular constant
   across BOTH values of the free band digit (the slice GENH4-7's
   gloss omitted).
R6 (char p sigma, first ever for F-SPLTAIL): the same 96 members
   transliterated to F_2[[t]] (phi = x^2 + t^2 x + t^4): each has
   disc != 0 (exact gcd(F, F') over F_2[t]) and EXACTLY 4 roots in
   F_4[[t]], 0 in F_2[[t]] (Panayi digit recursion; simple residue
   roots terminate by Hensel, F_2-digit roots are Frobenius-fixed)
   -- the {(1,2),(1,2)} read: two unramified conjugate quadratic
   factors, f = 2.
R7 (TOOTH, wrong-floor mutant): 2 mutant states (one per band
   value) breaking the v(a0) >= N floor at position 9 (u = 9 odd
   <= 2w = 10 -> RAM(9)): char 0 PARI sigma = {(2,2)} != the
   SPLTAIL label; char p root count 0 != 4.  Both must FIRE.

DISCLOSED design dry-run (pre-seal smoke): one full dry-run was
executed before the seal; it caught a branch explosion in the
first (BFS-pruning) root counter, replaced by the exact Panayi
recursion above; every other check was GREEN on the dry-run with
exactly the numbers preregistered above.  The verdict comes from
the sealed fresh run.

Exit 0 iff zero violations.  Artifacts: genh4annexr_supp_output.txt,
genh4annexr_supp_results.json.
"""
import ast
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
LOG = []
VIOL = []


def say(s):
    print(s)
    LOG.append(s)


def viol(tag, msg):
    VIOL.append((tag, msg))
    say('VIOLATION [%s] %s' % (tag, msg))


def md5f(path):
    with open(path, 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


PINS = {
    'genh4_checks.py': 'ee8024b7a500220a6408dab373d7432f',
    'genh4_checks_output.txt': '9e6ca9b3b83aa9902ddef379f72db741',
    'genh4_checks_results.json': 'cbcff562132f82e302d95a017318075c',
    'qscout22_checks.py': 'cb885663dd4ef6dfda9c28a67c1a076e',
    'qscout22_results.json': '6c2441a12cf52ffd43055de912a4affe',
    'genh4annex_supp.py': None,  # filled at run start (report only)
}

SIG_SPLTAIL = ((1, 2), (1, 2))
SIG_RAM_F = ((2, 2),)


# ===== the genre-F count law, typed fresh from S6.1/S6.3 (true cap) =
def law_F_fresh(q, N, k):
    A1all = list(range(2 * k + 1, N + k))
    A0all = list(range(4 * k + 1, N + k))
    comp = lambda m: 2 if m <= N - 1 else 1
    Q = q * q
    c11 = (Q - 1) * (Q - 2) // 2
    c2 = Q * (Q - 1) // 2
    out = {}

    def put(kk, v):
        if v:
            out[kk] = out.get(kk, 0) + v

    def rec(f1, f0, wt, H2):
        A1 = [s for s in A1all if s > f1]
        A0 = [s for s in A0all if s > f0]
        deep0 = q ** sum(comp(s) for s in A0 if s > N)
        for w in A1:
            if 2 * w < N:
                put((H2, 'SPLTAIL', (w,)), wt * (q ** comp(w) - 1)
                    * q ** sum(comp(s) for s in A1 if s > w) * deep0)
        put((H2, 'UND', ()), wt * deep0
            * q ** sum(comp(s) for s in A1 if 2 * s >= N))
        for u in A0:
            if u > N:
                continue
            nz0 = q ** sum(comp(s) for s in A0 if s > u)
            ex0 = q ** comp(u) - 1
            if u % 2 == 1:
                put((H2, 'RAM', (u,)), wt * ex0 * nz0
                    * q ** sum(comp(s) for s in A1 if 2 * s > u))
            for w in A1:
                if 2 * w < u:
                    put((H2, '2SIDED', (w, u - w)),
                        wt * (q ** comp(w) - 1) * ex0 * nz0
                        * q ** sum(comp(s) for s in A1 if s > w))
            if u % 2 == 0:
                dmu = u // 2
                on1 = q ** sum(comp(s) for s in A1 if s > dmu)
                if u == N:
                    put((H2, 'UND', ()),
                        wt * q ** comp(dmu) * ex0 * on1 * nz0)
                else:
                    put((H2, 'SPLITEQ', (dmu,)), wt * on1 * nz0 * c11)
                    put((H2, 'INERT', (dmu,)), wt * on1 * nz0 * c2)
                    rec(dmu, u, wt * (Q - 1), H2 + (dmu,))

    rec(2 * k, 4 * k, 1, ())
    return out


# ============================== integer polynomial helpers (char 0) =
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def gp_sigmas(polys, p):
    gp = os.path.expanduser('~/.local/bin/gp')
    if not os.path.exists(gp):
        gp = 'gp'
    fun = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sig(f, p) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
"""
    lines = [fun]
    for i, cs in enumerate(polys):
        expr = '+'.join('(%d)*x^%d' % (c, j) for j, c in enumerate(cs))
        lines.append('print("R %d ", sig(%s, %d))' % (i, expr, p))
    lines.append('quit')
    r = subprocess.run([gp, '-q'], input='\n'.join(lines).encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=1200)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:300])
    got = {}
    for line in r.stdout.decode().splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            nums = [int(x) for x in rest.replace('[', ' ')
                    .replace(']', ' ').replace(',', ' ').split()]
            got[int(idx)] = tuple(sorted(zip(nums[0::2], nums[1::2])))
    return [got[i] for i in range(len(polys))]


# =========================== F_4[[t]] arithmetic (char p leg) =======
# F_4 elements coded 0..3 with basis {1, y}, y^2 = y + 1 (psi's root).
F4MUL = [[0] * 4 for _ in range(4)]
for _a in range(4):
    for _b in range(4):
        a0, a1 = _a & 1, _a >> 1
        b0, b1 = _b & 1, _b >> 1
        c0 = (a0 * b0 + a1 * b1) & 1
        c1 = (a0 * b1 + a1 * b0 + a1 * b1) & 1
        F4MUL[_a][_b] = c0 | (c1 << 1)

PREC = 120


def sadd(a, b):
    return [x ^ y for x, y in zip(a, b)]


def sval(a):
    for i, x in enumerate(a):
        if x:
            return i
    return PREC


BINOM2 = [[1, 0, 0, 0, 0],
          [1, 1, 0, 0, 0],
          [1, 0, 1, 0, 0],
          [1, 1, 1, 1, 0],
          [1, 0, 0, 0, 1]]  # C(j,i) mod 2, j = row


def f4pow(a, e):
    r = 1
    for _ in range(e):
        r = F4MUL[r][a]
    return r


def count_roots(coeffs, digits, depth=0):
    """#roots of a separable poly in F_4[[t]] (digits = (0,1,2,3)) or
    F_2[[t]] (digits = (0,1)) by the Panayi digit recursion: normalize
    by the content t^m, reduce mod t to Fbar over F_4, then each
    SIMPLE residue root r in `digits` contributes exactly one Hensel
    root (Frobenius-fixed when the input has F_2 coefficients and
    r is in F_2), and each MULTIPLE residue root recurses on
    G(x) = F(r + t*x).  Terminates on separable inputs; depth guard
    asserts it."""
    if depth > 80:
        raise RuntimeError('Panayi depth > 80 (separability?)')
    m = min(sval(c) for c in coeffs)
    if m >= PREC - 85:
        raise RuntimeError('precision exhausted')
    coeffs = [c[m:] + [0] * m for c in coeffs]
    fbar = [c[0] for c in coeffs]
    dbar = [(fbar[i] if i % 2 else 0) for i in range(1, len(fbar))]
    total = 0
    for r in digits:
        fv = 0
        for c in reversed(fbar):
            fv = F4MUL[fv][r] ^ c
        if fv:
            continue
        dv = 0
        for c in reversed(dbar):
            dv = F4MUL[dv][r] ^ c
        if dv:
            total += 1  # simple residue root: unique Hensel lift
            continue
        # multiple residue root: recurse on F(r + t*x)
        G = []
        for i in range(len(coeffs)):
            gi = [0] * PREC
            for j in range(i, len(coeffs)):
                if BINOM2[j][i]:
                    gi = sadd(gi, [F4MUL[y][f4pow(r, j - i)]
                                   for y in coeffs[j]])
            G.append(([0] * i + gi)[:PREC])
        total += count_roots(G, digits, depth + 1)
    return total


def fp_disc_nonzero(coeffs):
    """Separability of the quartic over F_2(t): gcd(F, F') constant
    in x, computed by pseudo-remainder Euclid over F_2[t][x] (exact:
    inputs are finite F_2[t] polynomials; char 2: F' = c3 x^2 + c1).
    A nonconstant gcd would mean disc = 0."""
    def deg(p):
        d = -1
        for i, c in enumerate(p):
            if c % 2:
                d = i
        return d

    def trim(p):
        return [c % 2 for c in p[:deg(p) + 1]]

    def pm(a, b):
        if not a or not b:
            return []
        r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    r[i + j] ^= x & y
        return trim(r)

    def pxadd(a, b):
        n_ = max(len(a), len(b))
        return trim([(a[i] if i < len(a) else 0)
                     ^ (b[i] if i < len(b) else 0) for i in range(n_)])

    def xdeg(P):
        d = -1
        for i, c in enumerate(P):
            if deg(c) >= 0:
                d = i
        return d

    def xscale(P, c):
        return [pm(a, c) for a in P]

    def xsub(P, Q):
        n_ = max(len(P), len(Q))
        return [pxadd(P[i] if i < len(P) else [],
                      Q[i] if i < len(Q) else []) for i in range(n_)]

    def xshift(P, k):
        return [[]] * k + list(P)

    def prem(A, B):
        dB = xdeg(B)
        lB = B[dB]
        A = list(A)
        while xdeg(A) >= dB:
            dA = xdeg(A)
            lA = A[dA]
            A = xsub(xscale(A, lB), xshift(xscale(B, lA), dA - dB))
            A = A[:dA]  # leading term cancels exactly (char 2)
        return A

    F = [trim(c) for c in coeffs]
    A = [F[0], F[1], F[2], F[3], [1]]
    B = [F[1], [], F[3]]  # F' in char 2
    while True:
        dB = xdeg(B)
        if dB < 0:
            return False  # gcd nonconstant: disc = 0 (or F' = 0)
        if dB == 0:
            return True  # gcd constant in x: F separable
        A2 = prem(A, B)
        A, B = B, A2


# ===================== the (2,11,2) SPLTAIL(5) member constructor ===
# Key phi = x^2 + 4x + 16 (Zp) / x^2 + t^2 x + t^4 (F_2[[t]]):
# v(p1) = 2 >= k, v(p0) = 4 = 2k exact, psi = y^2 + y + 1 irreducible.
# Development F = phi^2 + A1*phi + A0, A1 = a1_c*x + a0_c,
# A0 = b1_c*x + b0_c.  Heights: alpha1 pos p -> p+2; alpha0 pos m -> m;
# beta1 pos p -> p+2; beta0 pos m -> m.  Window N = 11 (positions
# <= 10 in-window).  SPLTAIL(5) leaf: dv(A1) = 5 pinned (letter
# (alpha1@3, alpha0@5) != (0,0)); A0 hidden with the TRUE floor:
# beta0 in-window = 0, beta1 pos 7,8,9 = 0, beta1 pos 10 = b FREE
# (the boundary-band digit, height 12 = N+1).
PINS3 = [(1, 0), (0, 1), (1, 1)]
A1COMPS = [  # (alpha1 extra positions, alpha0 extra positions)
    ((), ()),
    ((), (7,)),
    ((6,), (9,)),
    ((9, 10), (6,)),
]
LIFTS = [  # (beta0 lift positions, beta1 lift positions, alpha0 lift)
    ((), (), ()),
    ((11,), (), ()),
    ((12,), (), ()),
    ((14,), (11,), (11,)),
]


def build_members():
    """Yield (tag, a1pos, a0pos, b1pos, b0pos) position tuples."""
    out = []
    for pi, (d1, d0) in enumerate(PINS3):
        for ci, (xa1, xa0) in enumerate(A1COMPS):
            for b in (0, 1):
                for li, (lb0, lb1, la0) in enumerate(LIFTS):
                    a1pos = tuple(sorted(((3,) if d1 else ())
                                         + tuple(xa1)))
                    a0pos = tuple(sorted(((5,) if d0 else ())
                                         + tuple(xa0) + tuple(la0)))
                    b1pos = tuple(sorted(((10,) if b else ())
                                         + tuple(lb1)))
                    b0pos = tuple(sorted(lb0))
                    out.append(('p%dc%db%dL%d' % (pi, ci, b, li),
                                a1pos, a0pos, b1pos, b0pos, b))
    return out


def z_poly(a1pos, a0pos, b1pos, b0pos):
    """Char-0 quartic coefficients (ascending, ints)."""
    phi = [16, 4, 1]
    A1 = [sum(2 ** m for m in a0pos), sum(2 ** p for p in a1pos)]
    A0 = [sum(2 ** m for m in b0pos), sum(2 ** p for p in b1pos)]
    F = padd(padd(pmul(phi, phi), pmul(A1, phi)), A0)
    return F + [0] * (5 - len(F))


def t_poly(a1pos, a0pos, b1pos, b0pos):
    """Char-p quartic coefficients: F_2[t] polys (bit lists)."""
    def tp(*poss):
        m = max(poss) if poss else -1
        return [1 if i in poss else 0 for i in range(m + 1)]

    def tpm(a, b):
        r = [0] * (len(a) + len(b) - 1) if a and b else []
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    r[i + j] ^= x & y
        return r

    def tpadd(a, b):
        n = max(len(a), len(b))
        return [(a[i] if i < len(a) else 0)
                ^ (b[i] if i < len(b) else 0) for i in range(n)]

    phi = [tp(4), tp(2), tp(0)]  # t^4 + t^2 x + x^2
    A1 = [tp(*a0pos), tp(*a1pos)]
    A0 = [tp(*b0pos), tp(*b1pos)]
    # F = phi^2 + A1 phi + A0 coefficientwise in x
    Fx = [[] for _ in range(5)]
    for i in range(3):
        for j in range(3):
            Fx[i + j] = tpadd(Fx[i + j], tpm(phi[i], phi[j]))
    for i in range(2):
        for j in range(3):
            Fx[i + j] = tpadd(Fx[i + j], tpm(A1[i], phi[j]))
    for i in range(2):
        Fx[i] = tpadd(Fx[i], A0[i])
    return Fx


def to_series(p):
    return [(p[i] if i < len(p) else 0) for i in range(PREC)]


def v2(n):
    if n == 0:
        return None
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def main():
    t0 = time.time()
    results = {'checks': {}}

    # ------------------------------------------------------- C0 pins
    npin = 0
    for fn, want in sorted(PINS.items()):
        have = md5f(os.path.join(HERE, fn))
        if want is None:
            say('C0 (report only): %s md5 %s' % (fn, have))
            continue
        npin += 1
        if have != want:
            viol('C0', '%s md5 %s != %s' % (fn, have, want))
    say('C0 pins: %d verified' % npin)
    results['checks']['C0-pins'] = npin

    import genh4_checks as GC
    if tuple(GC.LAW_KINDS) != ('RAM4', 'G2', 'FULL', 'SUB', 'E', 'F'):
        viol('C0', 'LAW_KINDS = %s' % (GC.LAW_KINDS,))

    # ------------------- C1 (R1): the pre2 six-key partition (F1)
    with open(os.path.join(HERE, 'genh4_checks_results.json')) as fh:
        g4rows = json.load(fh)['rows']
    pre2 = next(r for r in g4rows if r['row'].startswith('pre2'))
    keys = {ast.literal_eval(k): v for k, v in pre2['keys'].items()}
    law = {k: v for k, v in keys.items() if k[0] in GC.LAW_KINDS}
    nonlaw = {k: v for k, v in keys.items() if k[0] not in GC.LAW_KINDS}
    exp_law = {('E', (1, 2), 5, (), 'RAM', (21,)): 32768,
               ('E', (1, 2), 5, (), 'UND', ()): 32768,
               ('G2', (1, 2), (5, '2')): 65536,
               ('RAM4', (1, 2), (9,)): 524288}
    exp_nonlaw = {('VTX', (1, 2), ((0, 10), (1, 7), (4, 0))): 131072,
                  ('L1TAIL', (1, 2)): 262144}
    if law != exp_law:
        viol('C1', 'law-kind keys %s' % law)
    if nonlaw != exp_nonlaw:
        viol('C1', 'non-law keys %s' % nonlaw)
    if sum(keys.values()) != 2 ** 20 or pre2['members'] != 2 ** 20:
        viol('C1', 'partition sum %d != 2^20' % sum(keys.values()))
    # the floored-box forced counts (chain (1,2): floors 9,7,5,3):
    vtx = 1 * 2 ** 3 * 2 ** 6 * 2 ** 8   # B0@10 exact, B1@7 exact
    l1t = 2 ** (4 + 6 + 8)               # B0 in-window zero
    if (vtx, l1t) != (131072, 262144):
        viol('C1', 'box re-derivation %s' % ((vtx, l1t),))
    if sum(exp_law.values()) + vtx + l1t != 2 ** 20:
        viol('C1', 'law + remainder != 2^20')
    say('C1 (R1): pre2 row partitions 2^20 EXACTLY: 4 law-kind keys '
        '(sum %d) + VTX %d (=2^17, forced) + L1TAIL %d (=2^18, '
        'forced); remainder %d' % (sum(exp_law.values()), vtx, l1t,
                                   vtx + l1t))
    results['checks']['C1-pre2'] = len(keys)

    # ------------------------- C2 (R2): first-live geometry (F2)
    for N in (9, 10):
        spl = [k for k in law_F_fresh(2, N, 2) if k[1] == 'SPLTAIL']
        if spl:
            viol('C2', 'N=%d k=2 SPLTAIL %s (expected none)'
                 % (N, spl))
    spl11 = [k for k in law_F_fresh(2, 11, 2) if k[1] == 'SPLTAIL']
    if spl11 != [((), 'SPLTAIL', (5,))]:
        viol('C2', 'N=11 k=2 SPLTAIL keys %s' % spl11)
    row292 = next(r for r in g4rows if r['row'] == 'consF Zp q=2 N=9 k=2')
    if any('SPLTAIL' in k for k in row292['keys']):
        viol('C2', '(2,9,2) committed row has SPLTAIL')
    # every committed genre-F SPLTAIL key is k = 1:
    import re
    fspl = []
    with open(os.path.join(HERE, 'qscout22_results.json')) as fh:
        qrows = json.load(fh)['rows']
    for src, rr in [('q22', r) for r in qrows] + \
                   [('g4', r) for r in g4rows]:
        for kstr in rr.get('keys', {}):
            if 'SPLTAIL' in kstr and kstr.startswith("('F'"):
                mk = re.search(r'k=(\d+)', rr['row'])
                fspl.append((rr['row'], int(mk.group(1))))
    if not fspl or any(kv != 1 for _, kv in fspl):
        viol('C2', 'F-SPLTAIL k values %s' % fspl)
    say('C2 (R2): k=2 SPLTAIL empty at N=9,10, first live at N=11 '
        '(SPLTAIL(5) only); committed (2,9,2) has none; all %d '
        'committed F-SPLTAIL keys are k=1 (zero k>=2 exercise '
        'before this leg)' % len(fspl))
    results['checks']['C2-fspl-k1'] = len(fspl)

    # -------------------- C3 (R3): sealed-law tie at the new cell
    sealed = GC.law_F(2, 11, 2)
    fresh = law_F_fresh(2, 11, 2)
    if sealed != fresh:
        d = {k for k in set(sealed) | set(fresh)
             if sealed.get(k) != fresh.get(k)}
        viol('C3', '%d differing keys %s' % (len(d), sorted(d)[:4]))
    spl5 = sealed.get(((), 'SPLTAIL', (5,)))
    if spl5 != 24576 or spl5 != (2 ** 2 - 1 + 0) * 2 ** 12 * 2:
        viol('C3', 'SPLTAIL(5) = %s != 24576' % spl5)
    if sum(sealed.values()) != 2 ** 20:
        viol('C3', 'node mass %d != 2^20' % sum(sealed.values()))
    oldgloss = 3 * 2 ** 12  # band digit PINNED zero
    if oldgloss * 2 != spl5:
        viol('C3', 'old-gloss family %d != half of %d'
             % (oldgloss, spl5))
    say('C3 (R3): SEALED law_F(2,11,2) SPLTAIL(5) = %d = 3*2^12*2 '
        '(deep0 = 2 = q^(k-1)); fresh S6 typing ties the full table '
        'key-for-key (%d keys); node mass 2^20 exact; the OLD-gloss '
        '(band-pinned) family = %d = HALF: a strict subfamily, '
        'count-refuted' % (spl5, len(sealed), oldgloss))
    results['checks']['C3-keys'] = len(sealed)

    # --------------- C4 (R4): full leaf enumeration, floor layer
    n_tot = n_bandnz = n_oldviol = n_floorviol = 0
    for d1, d0 in PINS3:
        for freebits in range(2 ** 12):
            for b in (0, 1):
                n_tot += 1
                # alpha1 pos 4..8 (bits 0-4), alpha0 pos 6..10
                # (bits 5-9), alpha1 pos 9,10 (bits 10,11)
                a1v = (d1 << 3) | (((freebits >> 0) & 31) << 4) \
                    | (((freebits >> 10) & 3) << 9)
                a0v = (d0 << 5) | (((freebits >> 5) & 31) << 6)
                b1v = b << 10
                w = min((v2(a1v) or 99) + 2, v2(a0v) or 99)
                if w != 5:
                    viol('C4', 'dv(A1) = %s != 5' % w)
                va1 = v2(b1v) if b1v else 99
                if va1 < 11:
                    n_oldviol += 1  # violates the OLD hypothesis
                if b:
                    n_bandnz += 1
                u_state = min(99, va1 + 2)  # beta0 in-window zero
                if u_state < 11:
                    n_floorviol += 1
    if n_tot != 24576:
        viol('C4', 'enumerated %d != 24576' % n_tot)
    if n_bandnz != 12288 or n_oldviol != 12288:
        viol('C4', 'band-nonzero %d / old-hyp violations %d != 12288'
             % (n_bandnz, n_oldviol))
    if n_floorviol != 0:
        viol('C4', '%d members break the GENH4-7pr floor' % n_floorviol)
    say('C4 (R4): all %d leaf members enumerated: dv(A1) = 5 on all; '
        'GENH4-7pr floor (u_state >= 11 > 10 = 2w) holds on ALL; the '
        'band-nonzero HALF (%d) violates the OLD gloss hypothesis '
        '(v(a1) >= 11), 0 violate the corrected floor '
        '(characteristic-blind digit layer)' % (n_tot, n_bandnz))
    results['checks']['C4-members'] = n_tot

    # ------------------- C5 (R5): char-0 PARI sigma, band sweep
    members = build_members()
    polys, metas = [], []
    for tag, a1p, a0p, b1p, b0p, b in members:
        F = z_poly(a1p, a0p, b1p, b0p)
        b0v = sum(2 ** m for m in b0p)
        b1v = sum(2 ** p for p in b1p)
        if b0v == 0 and b1v == 0:
            u = None  # the A0 = 0 corner
        else:
            u = min(v2(b0v) if b0v else 99, (v2(b1v) or 99) + 2)
            if not u >= 11:
                viol('C5', '%s u_lift = %s < 11' % (tag, u))
        polys.append(F)
        metas.append((tag, u, b))
    sigs = gp_sigmas(polys, 2)
    nbad = 0
    per_band = {0: 0, 1: 0}
    for (tag, u, b), sg in zip(metas, sigs):
        if sg != SIG_SPLTAIL:
            nbad += 1
            viol('C5', '%s (u=%s): sigma %s != %s'
                 % (tag, u, sg, SIG_SPLTAIL))
        else:
            per_band[b] += 1
    say('C5 (R5): %d char-0 lifts (24 states x 4 lifts; %d band-zero '
        '+ %d band-NONZERO members incl. A0=0 corner and u=N=11 '
        'lifts): PARI sigma == {(1,2),(1,2)} on all (%d bad) -- the '
        'label is constant across the free band digit'
        % (len(polys), per_band[0], per_band[1], nbad))
    results['checks']['C5-lifts'] = len(polys)

    # ------------------------ C6 (R6): char-p root-count sigma
    ALLF4 = (0, 1, 2, 3)
    F2D = (0, 1)
    nbadp = 0
    for tag, a1p, a0p, b1p, b0p, b in members:
        Fx = t_poly(a1p, a0p, b1p, b0p)
        if not fp_disc_nonzero(Fx):
            viol('C6', '%s: disc = 0 over F_2(t)' % tag)
            continue
        cs = [to_series(c) for c in Fx]
        r4 = count_roots(cs, ALLF4)
        r2 = count_roots(cs, F2D)
        if (r4, r2) != (4, 0):
            nbadp += 1
            viol('C6', '%s: roots F4[[t]]=%d F2[[t]]=%d != (4,0)'
                 % (tag, r4, r2))
    say('C6 (R6): %d char-p (F_2[[t]]) members: disc != 0 (exact '
        'gcd) and EXACTLY 4 roots in F_4[[t]], 0 in F_2[[t]] on all '
        '(%d bad): two unramified conjugate quadratic pairs, the '
        '{(1,2),(1,2)} read -- FIRST char-p sigma contact for '
        'F-SPLTAIL' % (len(members), nbadp))
    results['checks']['C6-members'] = len(members)

    # --------------------- C7 (R7): the wrong-floor mutant TOOTH
    fired = 0
    mutant_polys, mutant_meta = [], []
    for b in (0, 1):
        a1p, a0p = (3,), (5,)   # pin (1,1)
        b1p = (10,) if b else ()
        b0p = (9,)              # BREAKS the floor: u = 9 odd <= 2w
        mutant_polys.append(z_poly(a1p, a0p, b1p, b0p))
        mutant_meta.append((b, t_poly(a1p, a0p, b1p, b0p)))
    msigs = gp_sigmas(mutant_polys, 2)
    for (b, Fx), sg in zip(mutant_meta, msigs):
        if sg != SIG_RAM_F:
            viol('C7', 'mutant b=%d: char-0 sigma %s != {(2,2)}'
                 % (b, sg))
        if sg != SIG_SPLTAIL:
            fired += 1
        cs = [to_series(c) for c in Fx]
        if not fp_disc_nonzero(Fx):
            viol('C7', 'mutant b=%d disc = 0' % b)
        r4 = count_roots(cs, ALLF4)
        if r4 != 0:
            viol('C7', 'mutant b=%d: %d F4-roots != 0 (RAM is '
                 'ramified)' % (b, r4))
        else:
            fired += 1
    if fired != 4:
        viol('C7', 'tooth fired %d/4' % fired)
    say('C7 (R7) TOOTH: 2 wrong-floor mutants (beta0 digit at '
        'position 9 < N: u = 9 odd <= 2w = 10 -> RAM(9)): char-0 '
        'PARI sigma = {(2,2)} != SPLTAIL label; char-p 0 roots in '
        'F_4[[t]] != 4: FIRED %d/4 -- the GENH4-7pr floor is '
        'load-bearing' % fired)
    results['checks']['C7-fired'] = fired

    # ---------------------------------------------------- verdict
    dt = time.time() - t0
    verdict = 'GREEN' if not VIOL else 'RED'
    say('VERDICT: %s (%d violations) %.1fs' % (verdict, len(VIOL), dt))
    results['verdict'] = verdict
    results['violations'] = len(VIOL)
    results['elapsed_s'] = round(dt, 1)
    with open(os.path.join(HERE, 'genh4annexr_supp_output.txt'),
              'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    with open(os.path.join(HERE, 'genh4annexr_supp_results.json'),
              'w') as fh:
        json.dump({k: (v if k != 'checks' else v)
                   for k, v in results.items()}, fh, indent=1,
                  sort_keys=True, default=repr)
    print('artifacts: %s %s'
          % (md5f(os.path.join(HERE, 'genh4annexr_supp_output.txt')),
             md5f(os.path.join(HERE, 'genh4annexr_supp_results.json'))))
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
