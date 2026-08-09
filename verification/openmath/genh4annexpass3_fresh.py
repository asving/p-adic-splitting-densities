#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENH4 ANNEX-PASS #3 FRESH LEG (hostile verifier; stack acceptance attempt).

Route chosen to differ from EVERY prior leg (PE5 leg: k=1 rows; R leg:
(2,11,2); pass-1 FR1-FR5: (2,15,3)/(3,11,2)/54-grid/(2,8,2)/(2,10,2)/
(2,9,2); pass-2: (2,7,2)/(2,12,2)/(3,13,2)/(3,10,1)/(2,14,2)/(4,11,2)
mixed-char W(F4)).  Three legs:

FL1 -- (q,N,k) = (2,19,4): the DEEPEST band ever (k-1 = 3 free band
  digits at heights 20/21/22), SPLTAIL(9), 2w = 18 < N = 19, first
  live k=4 cell (N = 4k+3).  phi = x^2 + 16x + 256 (v(p1)=4=k,
  v(p0)=8=2k, psi = y^2+y+1 irreducible over F_2).  3 pins x 4 band
  values x 3 lifts (u=N=19, deep u-cap, A0=0 corner) = 36 members +
  2 wrong-floor teeth (b0@17: RAM(17)).  EVERY member scored by TWO
  DECORRELATED PARI oracles: (a) the committed factorpadic route
  (GP_SIG verbatim), (b) a GLOBAL route (factor over Q +
  idealprimedec per global factor -- NO factorpadic call; the HE7
  dual-oracle precedent).  Valuation layer: u >= N on all; u <= m at
  band-nonzero.

FL2 -- (4,11,2) over F4[[t]]: the FIRST equal-characteristic
  non-prime-q exercise of consumed clause GENH4-7'(b) anywhere
  (pass-2's FC was mixed-char W(F4); the R leg's C6 was q=2).
  phi = x^2 + t^2 x + w*t^4 over F4 = F2(w), psi = y^2 + y + w
  irreducible over F4 (Tr_{F4/F2}(w) = 1); F16 = F4(Y), Y^2 = Y + w.
  INSTRUMENT IS FRESHLY WRITTEN HERE (generic GF(2^m)-tower Panayi
  root counter + fraction-free gcd separability over F16[t]); it
  shares NO code with genh4annexr_supp.count_roots (the char-p oracle
  every committed equal-char leg imported -- this leg exists to kill
  the shared-char-p-oracle blind spot).  Instrument self-tests T1-T3
  (known-answer: 4 split roots / unramified-quadratic pair / ramified
  x^2+t) must pass before any member is scored.  3 pins x 3 band
  values x 3 lifts = 27 members + 2 RAM(9) teeth.

FL3 -- (5,6,1): 2w = N = 6 (the (c')(ii) leg) at a FRESH odd q = 5,
  k = 1.  8 pin letters x (4 u=2w reads + 1 u=7 lift + 1 RAM(5)
  tooth) = 48 members, EVERY one scored by BOTH oracles (dual-oracle
  on the 2w=N geography, never done).  phi = x^2 + 5x + 25
  (psi = y^2+y+1 irreducible over F5: disc = -3 nonresidue).

PREREGISTERED PREDICTIONS (before any run):
  P1  FL1: 36/36 sigma = {(1,2),(1,2)} on BOTH oracles; the two
      oracles agree on 38/38; u >= 19 on every member, u <= m at
      every band-nonzero member; teeth 2/2 -> {(2,2)} both oracles.
  P2  FL2: self-tests T1-T3 exact; 27/27 members separable
      (gcd-trivial) with root counts (F16[[t]], F4[[t]]) = (4, 0)
      -> sigma = {(1,2),(1,2)} relative to F4((t)); teeth 2/2:
      separable, (0, 0) roots (RAM(9) is ramified).
  P3  FL3: oracle agreement 48/48; u=7 lifts 8/8 {(1,2),(1,2)};
      RAM(5) teeth 8/8 {(2,2)}; every u=6 read with d0 != S1^2/(4c)
      lands in {{(1,2),(1,2)}, {(1,4)}}; >= 1 inert {(1,4)} witness
      exists (R2.M2's count conclusion at q = 5); <= 1 degenerate
      digit per pin.

SMOKE RECORD: none at seal time (this docstring is sealed BEFORE the
first full run; any instrument repair will be disclosed here with the
pre-repair state kept on disk).
"""

import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = []
VIOL = []


def say(s):
    OUT.append(s)
    print(s)


def viol(tag, msg):
    VIOL.append((tag, msg))
    say('VIOLATION [%s] %s' % (tag, msg))


SIG_2S = ((1, 2), (1, 2))
SIG_RAM = ((2, 2),)
SIG_IN = ((1, 4),)


# ---------- integer x-poly helpers (independent re-type) ----------
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


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def quartic(phi, a1, a0, b1, b0):
    F = padd(padd(pmul(phi, phi), pmul([a0, a1], phi)), [b0, b1])
    return F + [0] * (5 - len(F))


# ---------- the two PARI oracles ----------
GP_BOTH = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sigfp(f, p) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, 300);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
siggl(f, p) = {
  my(d = poldisc(f), fa, acc = []);
  if (d == 0, return([[-1, -1]]));
  fa = factor(f);
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
      acc = concat(acc, [[1, 1]]),
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec, acc = concat(acc, [[dec[j].e, dec[j].f]]))));
  vecsort(acc)
}
"""


def gp_run(script):
    gp = os.path.expanduser('~/.local/bin/gp')
    if not os.path.exists(gp):
        gp = 'gp'
    r = subprocess.run([gp, '-q'], input=script.encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=1800)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:400])
    return r.stdout.decode()


def parse_pairs(rest):
    nums = [int(x) for x in rest.replace('[', ' ').replace(']', ' ')
            .replace(',', ' ').split()]
    return tuple(sorted(zip(nums[0::2], nums[1::2])))


def gp_dual(polys, p):
    lines = [GP_BOTH]
    for i, cs in enumerate(polys):
        expr = '+'.join('(%d)*x^%d' % (c, j) for j, c in enumerate(cs))
        lines.append('print("A %d ", sigfp(%s, %d))' % (i, expr, p))
        lines.append('print("B %d ", siggl(%s, %d))' % (i, expr, p))
    lines.append('quit')
    out = gp_run('\n'.join(lines))
    ga, gb = {}, {}
    for line in out.splitlines():
        if line.startswith('A ') or line.startswith('B '):
            idx, rest = line[2:].split(' ', 1)
            (ga if line[0] == 'A' else gb)[int(idx)] = parse_pairs(rest)
    return ([ga[i] for i in range(len(polys))],
            [gb[i] for i in range(len(polys))])


# ---------- FRESH GF(2^m)-tower + Panayi counter (FL2 instrument) ---
# F4: ints 0..3, bits (lo=1-part, hi=w-part), w^2 = w+1.
def f4mul(u, v):
    a, b = u & 1, (u >> 1) & 1
    c, d = v & 1, (v >> 1) & 1
    return ((a & c) ^ (b & d)) | ((((a & d) ^ (b & c)) ^ (b & d)) << 1)


# F16: pairs (al, be) = al + be*Y over F4, Y^2 = Y + w  (w = 2 in F4).
def f16mul(u, v):
    al, be = u
    ga, de = v
    bd = f4mul(be, de)
    return (f4mul(al, ga) ^ f4mul(bd, 2),
            f4mul(al, de) ^ f4mul(be, ga) ^ bd)


def f16add(u, v):
    return (u[0] ^ v[0], u[1] ^ v[1])


F16_ZERO = (0, 0)
F16_ONE = (1, 0)
F4_ELEMS = [(a, 0) for a in range(4)]
F16_ELEMS = [(a, b) for a in range(4) for b in range(4)]


# t-polys over F16: lists of F16 elements (index = t-power).
def tp_trim(p):
    while p and p[-1] == F16_ZERO:
        p.pop()
    return p


def tp_add(a, b):
    n = max(len(a), len(b))
    return tp_trim([f16add(a[i] if i < len(a) else F16_ZERO,
                           b[i] if i < len(b) else F16_ZERO)
                    for i in range(n)])


def tp_mul(a, b):
    if not a or not b:
        return []
    r = [F16_ZERO] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == F16_ZERO:
            continue
        for j, y in enumerate(b):
            r[i + j] = f16add(r[i + j], f16mul(x, y))
    return tp_trim(r)


def tp_scale(a, c):
    return tp_trim([f16mul(x, c) for x in a])


def tp_val(a):
    for i, x in enumerate(a):
        if x != F16_ZERO:
            return i
    return None


def tp_shift(a, k):
    return [F16_ZERO] * k + a


# x-polys: lists of t-polys (index = x-power).
def xp_trim(F):
    while F and not F[-1]:
        F.pop()
    return F


def xp_add(A, B):
    n = max(len(A), len(B))
    return xp_trim([tp_add(A[i] if i < len(A) else [],
                           B[i] if i < len(B) else [])
                    for i in range(n)])


def xp_mul(A, B):
    if not A or not B:
        return []
    r = [[] for _ in range(len(A) + len(B) - 1)]
    for i, a in enumerate(A):
        if not a:
            continue
        for j, b in enumerate(B):
            r[i + j] = tp_add(r[i + j], tp_mul(a, b))
    return xp_trim(r)


def xp_sub_x_to_r_plus_tx(F, r):
    """F(r + t*x) for r in F16 (as t-poly substitution)."""
    # powers of (r + t x): x-poly with t-poly coeffs
    base = [[r] if r != F16_ZERO else [], [F16_ZERO, F16_ONE]]
    base = xp_trim([c[:] for c in base])
    acc = [[F16_ONE]]  # 1
    out = []
    for c in F:  # coefficient of x^j, a t-poly
        if c:
            out = xp_add(out, [tp_mul(cc, c) for cc in acc])
        acc = xp_mul(acc, base)
    return xp_trim(out)


def xp_tval(F):
    vals = [tp_val(c) for c in F if c]
    vals = [v for v in vals if v is not None]
    return min(vals) if vals else None


def xp_tdiv(F, m):
    return [c[m:] if c else [] for c in F]


def nroots(F, digits, depth=0):
    """# roots of F in R[[t]], digits = residue-field elements of R.
    F separable (guarded by caller); depth-guarded Panayi recursion."""
    if depth > 90:
        viol('FL2', 'Panayi depth guard hit')
        return 0
    m = xp_tval(F)
    if m is None:
        viol('FL2', 'zero polynomial in nroots')
        return 0
    if m:
        F = xp_tdiv(F, m)
    fb = [(c[0] if c else F16_ZERO) for c in F]  # reduce mod t
    while fb and fb[-1] == F16_ZERO:
        fb.pop()
    if len(fb) <= 1:
        return 0  # nonzero constant: no root through any digit
    # formal derivative in char 2
    fbd = [fb[j] if j % 2 == 1 else F16_ZERO for j in range(1, len(fb))]

    def ev(poly, r):
        acc = F16_ZERO
        for c in reversed(poly):
            acc = f16add(f16mul(acc, r), c)
        return acc

    total = 0
    for r in digits:
        if ev(fb, r) != F16_ZERO:
            continue
        if ev(fbd, r) != F16_ZERO:
            total += 1  # simple residue root: Hensel, one root
        else:
            total += nroots(xp_sub_x_to_r_plus_tx(F, r), digits,
                            depth + 1)
    return total


def xp_deg(F):
    return len(xp_trim([c[:] for c in F])) - 1


def prem_chain_step(A, B):
    """Pseudo-remainder of A by B over F16[t][x] (char 2), i.e.
    lc(B)^h * A mod B up to nonzero t-poly scaling -- x-degree
    triviality of the gcd is scaling-invariant."""
    lb = B[-1]
    dB = xp_deg(B)
    R = [c[:] for c in A]
    while R and xp_deg(R) >= dB:
        dR = xp_deg(R)
        lr = R[-1]
        R = [tp_mul(c, lb) for c in R]
        S = [[] for _ in range(dR - dB)] + [tp_mul(c, lr) for c in B]
        R = xp_trim(xp_add(R, S))  # char 2: add = subtract
    return R


def separable(F):
    """gcd(F, F') trivial over F16(t)? Euclidean prem chain."""
    Fd = [F[j] if j % 2 == 1 else [] for j in range(1, len(F))]
    A, B = xp_trim([c[:] for c in F]), xp_trim([c[:] for c in Fd])
    while True:
        if not B:
            return False  # gcd = A of x-degree >= 1 (or F' = 0)
        if xp_deg(B) == 0:
            return True  # gcd is a unit
        A, B = B, prem_chain_step(A, B)


def f4_tp(pairs):
    """t-poly from [(coef_f4int, t-power), ...]."""
    if not pairs:
        return []
    n = max(k for _, k in pairs) + 1
    r = [F16_ZERO] * n
    for c, k in pairs:
        r[k] = f16add(r[k], (c, 0))
    return tp_trim(r)


def fl2_quartic(phi, a1, a0, b1, b0):
    """F = phi^2 + (a1 x + a0) phi + (b1 x + b0); coeffs = t-polys."""
    F = xp_mul(phi, phi)
    F = xp_add(F, xp_mul([a0, a1], phi))
    F = xp_add(F, [b0, b1])
    return F


def main():
    t0 = time.time()
    results = {'checks': {}}

    # ================= FL1: (2,19,4), the k=4 cell =================
    say('=== FL1: (2,19,4) k=4 SPLTAIL(9), 2w=18<19; dual PARI '
        'oracles ===')
    phi = [256, 16, 1]
    pins = ((1 << 5, 0), (0, 1 << 9), (1 << 5, 1 << 9))
    bands = (0, 1 << 16, (1 << 17) + (1 << 18),
             (1 << 16) + (1 << 17) + (1 << 18))
    lifts = (('uN', 1 << 19), ('deep', 1 << 23), ('corner', 0))
    polys, metas = [], []
    for pi, (a1, a0) in enumerate(pins):
        for bi, bd in enumerate(bands):
            for tag, b0 in lifts:
                b1 = bd
                u = min((vp(b1, 2) + 4) if b1 else 10 ** 9,
                        vp(b0, 2) if b0 else 10 ** 9)
                if u < 10 ** 9 and u < 19:
                    viol('FL1', 'floor: u=%d < N=19 (p%d b%d %s)'
                         % (u, pi, bi, tag))
                if bd and u < 10 ** 9:
                    m = vp(bd, 2) + 4
                    if u > m:
                        viol('FL1', 'cap: u=%d > m=%d (p%d b%d %s)'
                             % (u, m, pi, bi, tag))
                if bd == 0 and b0 == 0:
                    pass  # A0 = 0 corner: u = infinity, no u checks
                polys.append(quartic(phi, a1, a0, b1, b0))
                metas.append(('p%d-b%d-%s' % (pi, bi, tag), SIG_2S))
    teeth = [(quartic(phi, 1 << 5, 0, 0, 1 << 17), 'tooth-band0'),
             (quartic(phi, 0, 1 << 9, 1 << 16, 1 << 17), 'tooth-band1')]
    for tp_, tg in teeth:
        polys.append(tp_)
        metas.append((tg, SIG_RAM))
    sa, sb = gp_dual(polys, 2)
    nag = sum(1 for x, y in zip(sa, sb) if x == y)
    if nag != len(polys):
        viol('FL1', 'oracle disagreement: %d/%d' % (nag, len(polys)))
    bad = 0
    for (tag, exp), x in zip(metas, sa):
        if x != exp:
            bad += 1
            viol('FL1', '%s: sigma %s != expected %s' % (tag, x, exp))
    say('FL1: %d/%d sigma as predicted (36 members {(1,2),(1,2)} + '
        '2 teeth {(2,2)}); oracle agreement %d/%d; floors/caps clean'
        % (len(polys) - bad, len(polys), nag, len(polys)))
    results['checks']['FL1'] = {'n': len(polys), 'ok': len(polys) - bad,
                                'agree': nag}

    # ================= FL2: (4,11,2) over F4[[t]] =================
    say('=== FL2: (4,11,2) equal-char F4[[t]], FRESH instrument ===')
    # self-tests
    # T1: (x - t)(x - wt)(x - w^2 t)(x - t^2): 4 roots in F4[[t]]
    def lin(c, k):  # x - c*t^k = x + c*t^k (char 2)
        return [f4_tp([(c, k)]), [F16_ONE]]
    T1 = xp_mul(xp_mul(lin(1, 1), lin(2, 1)),
                xp_mul(lin(3, 1), lin(1, 2)))
    r16, r4 = nroots(T1, F16_ELEMS), nroots(T1, F4_ELEMS)
    if (r16, r4) != (4, 4):
        viol('FL2', 'T1: got (%d,%d) != (4,4)' % (r16, r4))
    # T2: (x^2 + x + w) * (x^2 + x + w*t): first factor has 2 roots in
    # F16 \ F4 (simple); second: residue x^2+x = x(x+1) both simple,
    # 2 roots in F4[[t]] (and F16[[t]]).  totals: F16 4, F4 2.
    T2 = xp_mul([f4_tp([(2, 0)]), [F16_ONE], [F16_ONE]],
                [f4_tp([(2, 1)]), [F16_ONE], [F16_ONE]])
    r16, r4 = nroots(T2, F16_ELEMS), nroots(T2, F4_ELEMS)
    if (r16, r4) != (4, 2):
        viol('FL2', 'T2: got (%d,%d) != (4,2)' % (r16, r4))
    # T3: x^2 + t (ramified): 0 roots in both
    T3 = [f4_tp([(1, 1)]), [], [F16_ONE]]
    r16, r4 = nroots(T3, F16_ELEMS), nroots(T3, F4_ELEMS)
    if (r16, r4) != (0, 0):
        viol('FL2', 'T3: got (%d,%d) != (0,0)' % (r16, r4))
    say('FL2 self-tests T1/T2/T3: exact')

    phi4 = [f4_tp([(2, 4)]), f4_tp([(1, 2)]), [F16_ONE]]
    pins4 = ((f4_tp([(1, 3)]), []), ([], f4_tp([(2, 5)])),
             (f4_tp([(1, 3)]), f4_tp([(2, 5)])))
    bands4 = ([], f4_tp([(1, 10)]), f4_tp([(2, 10)]))
    lifts4 = (('uN', f4_tp([(1, 11)])), ('deep', f4_tp([(2, 13)])),
              ('corner', []))
    nok, ntot = 0, 0
    for pi, (a1, a0) in enumerate(pins4):
        for bi, bd in enumerate(bands4):
            for tag, b0 in lifts4:
                ntot += 1
                F = fl2_quartic(phi4, a1, a0, bd, b0)
                sep = separable(F)
                r16 = nroots(F, F16_ELEMS)
                r4 = nroots(F, F4_ELEMS)
                if sep and (r16, r4) == (4, 0):
                    nok += 1
                else:
                    viol('FL2', 'p%d-b%d-%s: sep=%s roots=(%d,%d) != '
                         '(4,0)' % (pi, bi, tag, sep, r16, r4))
    say('FL2: %d/%d members separable with (F16,F4) roots = (4,0) -> '
        'relative sigma {(1,2),(1,2)} over F4((t)) [consumed clause '
        "GENH4-7'(b), first equal-char non-prime-q exercise]"
        % (nok, ntot))
    tok = 0
    for bi, bd in ((0, []), (1, f4_tp([(1, 10)]))):
        F = fl2_quartic(phi4, f4_tp([(1, 3)]), [], bd, f4_tp([(1, 9)]))
        sep = separable(F)
        r16 = nroots(F, F16_ELEMS)
        r4 = nroots(F, F4_ELEMS)
        if sep and (r16, r4) == (0, 0):
            tok += 1
        else:
            viol('FL2', 'tooth b%d: sep=%s roots=(%d,%d) != (0,0)'
                 % (bi, sep, r16, r4))
    say('FL2 teeth (wrong floor b0@9 -> RAM(9), ramified): %d/2 FIRED'
        % tok)
    results['checks']['FL2'] = {'members': nok, 'of': ntot,
                                'teeth': tok}

    # ================= FL3: (5,6,1), 2w = N, dual oracle ============
    say('=== FL3: (5,6,1) 2w=N=6, dual PARI oracles on the (c\')(ii) '
        'geography ===')
    phi5 = [25, 5, 1]
    pins5 = ((1, 0), (0, 1), (1, 1), (2, 1), (1, 2), (2, 0), (0, 3),
             (3, 2))
    polys, metas = [], []
    for pi, (d1, d0) in enumerate(pins5):
        a1, a0 = d1 * 25, d0 * 125
        for d in (1, 2, 3, 4):
            polys.append(quartic(phi5, a1, a0, 0, d * 5 ** 6))
            metas.append(('p%d-u6-d%d' % (pi, d), 'u6'))
        polys.append(quartic(phi5, a1, a0, 0, 5 ** 7))
        metas.append(('p%d-u7' % pi, 'u7'))
        polys.append(quartic(phi5, a1, a0, 0, 5 ** 5))
        metas.append(('p%d-ram' % pi, 'ram'))
    sa, sb = gp_dual(polys, 5)
    nag = sum(1 for x, y in zip(sa, sb) if x == y)
    if nag != len(polys):
        viol('FL3', 'oracle disagreement: %d/%d' % (nag, len(polys)))
    n7 = nram = nin = 0
    per_pin_odd = {}
    for (tag, kind), x in zip(metas, sa):
        if kind == 'u7':
            if x == SIG_2S:
                n7 += 1
            else:
                viol('FL3', '%s: %s != 2SIDED' % (tag, x))
        elif kind == 'ram':
            if x == SIG_RAM:
                nram += 1
            else:
                viol('FL3', '%s: %s != RAM' % (tag, x))
        else:
            if x == SIG_IN:
                nin += 1
            elif x != SIG_2S:
                pin = tag.split('-')[0]
                per_pin_odd[pin] = per_pin_odd.get(pin, 0) + 1
                say('FL3 note: %s reads %s (degenerate-digit slot)'
                    % (tag, x))
    for pin, c in per_pin_odd.items():
        if c > 1:
            viol('FL3', '%s: %d > 1 degenerate u6 reads' % (pin, c))
    if nin < 1:
        viol('FL3', 'NO inert witness at u = 2w (R2.M2 predicts >= 1)')
    say('FL3: oracle agreement %d/%d; u7 2SIDED %d/8; RAM teeth %d/8; '
        'inert {(1,4)} witnesses at u=2w: %d (>=1 predicted); '
        'degenerate reads: %s'
        % (nag, len(polys), n7, nram, nin, per_pin_odd or 'none'))
    results['checks']['FL3'] = {'n': len(polys), 'agree': nag,
                                'u7': n7, 'ram': nram, 'inert': nin,
                                'degenerate': per_pin_odd}

    # ---------------- verdict ----------------
    dt = time.time() - t0
    results['violations'] = VIOL
    results['elapsed_s'] = round(dt, 1)
    ok = not VIOL
    say('')
    say('VERDICT: %s (%d violations), %.1f s'
        % ('GREEN' if ok else 'RED', len(VIOL), dt))
    with open(os.path.join(HERE, 'genh4annexpass3_fresh_output.txt'),
              'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    with open(os.path.join(HERE, 'genh4annexpass3_fresh_results.json'),
              'w') as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
