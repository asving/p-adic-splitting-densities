#!/usr/bin/env python3
"""HE6 passPE4 fresh leg — the FIRST non-prime-q BASE oracle leg of the arc.

Every prior sigma leg of the HE6 arc (seal battery, he6r1, PE2 leg A, PE3
leg A) ran over a PRIME base (O = Z_p or F_p[[t]], F_Q = F_p); PE2 and PE3
both disclosed the non-prime-q BASE hole ("a q = p^k leg needs an
unramified-base oracle this pass did not build").  This leg builds it.

FRAME.  Base F = Q(w)/(w^2 - d) with p INERT (so the local base K_0 = the
unramified quadratic extension of Q_p, O = its valuation ring, residue field
F_Q = F_{p^2} — q NON-PRIME AT THE BASE).  Two frames: (d, p) = (-1, 3)
(F_9) and (2, 5) (F_25).  Z[w] is p-maximal in both (p ndivides disc).
v_P(a + b w) = min(v_p(a), v_p(b)); pi = p.
Stage: Phi' = x^2 - p over O — Eisenstein at P, so (e1, f1, h) = (2, 1, 1),
D' = 2, psi = T - 1, eta_theta = res(theta^2/pi) = 1 (all normalizer twists
are powers of eta = 1: twist-free frame), varpi = x (i0 = 1, a0 = 0), K =
F_Q = F_{p^2}.  mu = 4, deg f = 8, single side lambda = 5/2 (u = 5, l = 2),
pins (0,10)-(2,5)-(4,0):
    f = Phi'^4 + C2 * p^2 * x * Phi'^2 + C0 * p^5   (+ perturbation),
R_lambda(Z) = Z^2 + c2 Z + c0 with c2 = res(C2), c0 = res(C0) in F_{p^2}
(ADD-ON residues read per the S1 varpi-convention; the reader RE-DERIVES the
development, the hull and R_lambda from the raw expanded coefficients).

CONFIGS (per frame; 10 members each = base + 9 perturbations strictly above
the lambda-line, four of them with w-components so the base ring is
genuinely exercised):
  FROBSPLIT  R = (Z - s)(Z - s^p), s = wbar (a FROBENIUS PAIR over the PRIME
             field: R is IRREDUCIBLE over F_p but SPLIT over F_{p^2}; the
             base member has all-integer coefficients, so the same
             polynomial can be scored over BOTH bases).  d=-1,p=3: Z^2+1.
             d=2,p=5: Z^2+3.
  SPLITMIX   R = (Z - 1)(Z - wbar): one prime-field root, one genuinely
             F_{p^2}-root, not Frobenius-conjugate.
  INERT2     R = Z^2 + a Z + b irreducible over F_{p^2} (brute-verified
             rootless), first hit with b carrying a w-component.

ORACLE (gp, nf route over the base F — decorrelated from the arc's
factorpadic legs AND from PE3's rational-nf legs):
  nffactor(nf_F, f) over F; per factor g:  rnfequation(F, g) -> absolute
  polynomial over Q; nfinit([abs, [p]]); idealprimedec at p; every prime Q
  of M_g lies over the UNIQUE prime P of F above p, so the RELATIVE
  invariants are e(Q|P) = e(Q|p), f(Q|P) = f(Q|p)/2 (assert f(Q|p) even).
  sigma_rel(f) := multiset of (e(Q|P), f(Q|P)).
PRIME-BASE CONTROL: on the 5 all-integer FROBSPLIT members, also score
  sigma over Q_p via the PE3-style rational nf route (nfinit([g,[p]])).

PREREGISTERED PREDICTIONS (written before the full run):
  FP1  reader-derived outer data = intended on every member: single side
       (0,10)-(4,0), slope 5/2, R_lambda as constructed, disc f != 0
       (gcd(f, f') = 1 over F).
  FP2  sigma_rel = THEOREM HE6.A's dictionary on EVERY member, invariant
       under all perturbations: FROBSPLIT and SPLITMIX -> {(4,1),(4,1)}
       (e = e1*l = 4, f = f1*deg r = 1, two classes); INERT2 -> {(4,2)}.
       Sanity: sum of e*f_rel = 8 per member; no linear factor over F.
  FP3  exactness identities over the non-prime base (first of the arc):
       (flat, generic letter)  2 v_P(Res(f, Psi_{5/2, r3})) = 12 * 10 = 120
       with r3 a degree-3 irreducible over F_{p^2} (never divides a
       degree-2 residual);  (flat, non-slope height)
       2 v_P(Res(f, Psi_{3, Z-1})) = 2 * 10 = 20;  (strict at the labels)
       2 v_P(Res(f, Psi_{5/2, r})) > 40 for each split label Z - s (D''=4),
       > 80 for the INERT2 quadratic itself (D''=8).  Base members only.
  FP4  the two base fields DISAGREE on the same bytes: each all-integer
       FROBSPLIT member scores {(4,2)} over Q_p and {(4,1),(4,1)} over the
       unramified base (the unramified base change splits the f=2 factor).

TEETH (must fire or the leg is discarded):
  T-BASEFIELD  FP4's disagreement observed on all 5 control members (kills
               "the leg is a re-labeled prime-base computation" and kills a
               reader that consults the PRIME residue field: over F_p the
               FROBSPLIT residual is irreducible and would mispredict
               {(4,2)} for the base-F read).
  T-PLANTDICT  the planted dictionary {(8,1)} (single class) is refuted by
               the oracle on every FROBSPLIT/SPLITMIX member.
  T-BADPERT    a deliberately ON-LINE perturbation (dv = 5 at j = 2,
               changing R_lambda's middle coefficient) is CAUGHT by the
               reader (outer data differs from intended) — the
               strictly-above-line discipline is load-bearing.

SMOKE RECORD (disclosed): one FROBSPLIT base member + one INERT2 base
member (both p = 3 frame) were run once to validate the gp pipeline; the
first smoke attempt errored in the READER (it demanded the middle pin
(2,5) sit ON the line, too strict — FROBSPLIT's residual has trace 0, so
that pin legitimately sits ABOVE the line and R_lambda's Z-coefficient is
0 per the S1 convention); the reader was relaxed to the note's actual
convention before any oracle comparison. No PREDICTION (FP1-FP4) and no
tooth was changed at any point; the oracle outputs of the smoke
(M0 = [[4,1],[4,1]], C0 = [[4,2]], M1 = [[4,2]]) already matched FP2/FP4.
The full run is the first complete pass.
"""

import json
import subprocess
import sys
import time
from fractions import Fraction as Fr
from math import gcd, inf

VIOL = []


def viol(tag, msg):
    VIOL.append((tag, msg))
    print('VIOLATION [%s] %s' % (tag, msg))


# ---------------------------------------------------------------- base ring
# elements of Q(w), w^2 = d: pairs (a, b) of Fractions = a + b*w.

def badd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def bsub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def bmul(x, y, d):
    return (x[0] * y[0] + d * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def bdiv(x, y, d):
    n = y[0] * y[0] - d * y[1] * y[1]
    if n == 0:
        raise ZeroDivisionError
    inv = (y[0] / n, -y[1] / n)
    return bmul(x, inv, d)


BZERO = (Fr(0), Fr(0))
BONE = (Fr(1), Fr(0))


def vp_int(n, p):
    if n == 0:
        return inf
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_fr(x, p):
    if x == 0:
        return inf
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def vP(x, p):
    """P-adic valuation on Q(w) for p inert (Z[w] p-maximal)."""
    return min(vp_fr(Fr(x[0]), p), vp_fr(Fr(x[1]), p))


# ------------------------------------------------------- polynomials over F
# poly = list of base elements, index = degree in x.

def ptrim(f):
    while f and f[-1] == BZERO:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return ptrim([badd(f[i] if i < len(f) else BZERO,
                       g[i] if i < len(g) else BZERO) for i in range(n)])


def pmul(f, g, d):
    if not f or not g:
        return []
    out = [BZERO] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a == BZERO:
            continue
        for j, b in enumerate(g):
            out[i + j] = badd(out[i + j], bmul(a, b, d))
    return ptrim(out)


def pscal(c, f, d):
    return ptrim([bmul(c, a, d) for a in f])


def pdivmod(f, g, d):
    """g monic. returns (q, r)."""
    f = list(f)
    q = [BZERO] * max(1, len(f) - len(g) + 1)
    while len(f) >= len(g):
        c = f[-1]
        k = len(f) - len(g)
        q[k] = c
        for i in range(len(g)):
            f[k + i] = bsub(f[k + i], bmul(c, g[i], d))
        ptrim(f)
        if len(f) >= len(g) and f[-1] == BZERO:
            ptrim(f)
    return ptrim(q), ptrim(f)


def pgcd_deg(f, g, d):
    """degree of gcd over Q(w) (monic Euclid)."""
    f, g = list(f), list(g)
    while g:
        lead = g[-1]
        gm = [bdiv(c, lead, d) for c in g]
        _, r = pdivmod(f, gm, d)
        f, g = gm, r
    return len(f) - 1


def resultant(f, g, d):
    """Sylvester determinant over Q(w), exact."""
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0:
        return BZERO
    size = m + n
    rows = []
    for i in range(n):
        row = [BZERO] * size
        for j, c in enumerate(reversed(f)):
            row[i + j] = c
        rows.append(row)
    for i in range(m):
        row = [BZERO] * size
        for j, c in enumerate(reversed(g)):
            row[i + j] = c
        rows.append(row)
    det = BONE
    for col in range(size):
        piv = None
        for r in range(col, size):
            if rows[r][col] != BZERO:
                piv = r
                break
        if piv is None:
            return BZERO
        if piv != col:
            rows[col], rows[piv] = rows[piv], rows[col]
            det = bmul(det, (Fr(-1), Fr(0)), d)
        pv = rows[col][col]
        det = bmul(det, pv, d)
        for r in range(col + 1, size):
            if rows[r][col] == BZERO:
                continue
            fac = bdiv(rows[r][col], pv, d)
            for c2 in range(col, size):
                rows[r][c2] = bsub(rows[r][c2], bmul(fac, rows[col][c2], d))
    return det


# ------------------------------------------------------------ residue field
# F_{p^2} elements: pairs (a, b) of ints mod p, = a + b*wbar, wbar^2 = d.

def rmul(x, y, d, p):
    return ((x[0] * y[0] + d * x[1] * y[1]) % p,
            (x[0] * y[1] + x[1] * y[0]) % p)


def radd(x, y, p):
    return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)


def rall(p):
    return [(a, b) for a in range(p) for b in range(p)]


def res_of(x, p):
    """residue of a P-integral Q(w) element."""
    a, b = Fr(x[0]), Fr(x[1])
    ai = (a.numerator * pow(a.denominator, -1, p)) % p
    bi = (b.numerator * pow(b.denominator, -1, p)) % p
    return (ai, bi)


def quad_roots(c2, c0, d, p):
    """roots of Z^2 + c2 Z + c0 over F_{p^2}, brute."""
    out = []
    for z in rall(p):
        v = radd(radd(rmul(z, z, d, p), rmul(c2, z, d, p), p), c0, p)
        if v == (0, 0):
            out.append(z)
    return out


# ------------------------------------------------------------- construction
def lift(r, p):
    """lift an F_{p^2} element (a,b) to Z[w] as base element."""
    return (Fr(r[0]), Fr(r[1]))


def build_f(d, p, C2, C0, pert):
    """f = Phi'^4 + C2*p^2*x*Phi'^2 + C0*p^5 + pert; pert = list of
    (j, poly) added to A_j.  Returns expanded poly and the development."""
    Phi = [( Fr(-p), Fr(0)), BZERO, BONE]          # x^2 - p
    A = {j: [] for j in range(4)}
    A[2] = [BZERO, bmul(lift(C2, p), (Fr(p ** 2), Fr(0)), d)]   # C2 p^2 x
    A[0] = [bmul(lift(C0, p), (Fr(p ** 5), Fr(0)), d)]          # C0 p^5
    for j, term in pert:
        A[j] = padd(A[j], term)
    f = [BONE]
    for _ in range(4):
        f = pmul(f, Phi, d)
    for j in range(4):
        Pj = [BONE]
        for _ in range(j):
            Pj = pmul(Pj, Phi, d)
        f = padd(f, pmul(A[j], Pj, d))
    return f, A


# ------------------------------------------------------------------ reader
def reader(f, d, p):
    """From raw expanded f: Phi'-development, dv pins, hull check, and
    R_lambda over F_{p^2} per the S1 varpi-convention (eta = 1)."""
    Phi = [(Fr(-p), Fr(0)), BZERO, BONE]
    A = []
    g = list(f)
    for _ in range(5):
        g, r = pdivmod(g, Phi, d)
        A.append(r)
    if g:
        return None, 'development did not terminate at mu = 4'
    dv = []
    for j in range(5):
        best = inf
        for i, c in enumerate(A[j]):
            v = vP(c, p)
            if v is not inf:
                best = min(best, 2 * v + i)
        dv.append(best)
    if dv[4] != 0:
        return None, 'A_4 not a unit: %s' % dv
    # single side (0,10)-(4,0) of slope 5/2: pins on/above the line,
    # equality exactly at j in {0, 2, 4}
    line = {0: Fr(10), 1: Fr(15, 2), 2: Fr(5), 3: Fr(5, 2), 4: Fr(0)}
    for j in range(5):
        if dv[j] is inf:
            continue
        if Fr(dv[j]) < line[j]:
            return None, 'pin below line at j=%d: %s' % (j, dv[j])
    if dv[0] != 10:
        return None, 'left endpoint moved: %s' % dv
    # (the middle pin (2,5) may sit ABOVE the line: R_lambda's Z-coefficient
    # is then 0 per the S1 convention — e.g. FROBSPLIT's trace-0 residual)
    # R_lambda coefficients: t-th = res(A_{2t}(theta)/theta^{10-5t});
    # attaining slot i = (10-5t) mod 2, residue = res(a_i / p^{(k-i)/2}).
    coefs = []
    for t in range(3):
        if t == 2:
            coefs.append((1, 0))
            continue
        k = 10 - 5 * t
        i = k % 2
        Aj = A[2 * t]
        c = Aj[i] if i < len(Aj) else BZERO
        # pins on/above the line give 2 vP(c) + i >= k on the parity slot,
        # so the normalized element is P-integral; an above-line pin reduces
        # to (0,0) — exactly the S1 convention's zero coefficient.
        cc = bmul(c, (Fr(1, p ** ((k - i) // 2)), Fr(0)), d)
        coefs.append(res_of(cc, p))
    # separability of f over Q(w)
    fp = ptrim([bmul((Fr(i), Fr(0)), f[i], d) for i in range(1, len(f))])
    if pgcd_deg(f, fp, d) != 0:
        return None, 'disc f = 0'
    return {'dv': dv, 'R': coefs}, None


def dict_sigma(coefs, d, p):
    """THEOREM HE6.A dictionary from R_lambda = Z^2 + c2 Z + c0."""
    c0, c2 = coefs[0], coefs[1]
    roots = quad_roots(c2, c0, d, p)
    if len(roots) == 2:
        return ((4, 1), (4, 1))
    if len(roots) == 0:
        return ((4, 2),)
    return None  # repeated root — boxed, not built here


# --------------------------------------------------------------- gp oracle
def gp_run(script):
    r = subprocess.run(['gp', '-q'], input=script.encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=3600)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:400])
    return r.stdout.decode()


def gp_poly(f):
    """poly over Q(w) -> gp string in x with y = w."""
    terms = []
    for i, c in enumerate(f):
        a, b = Fr(c[0]), Fr(c[1])
        terms.append('((%d/%d)+(%d/%d)*y)*x^%d'
                     % (a.numerator, a.denominator,
                        b.numerator, b.denominator, i))
    return '+'.join(terms) or '0'


GP_REL = r"""
sigrel(fpol) = {
  my(fa = nffactor(BASE, fpol)[,1]~, out = List(), tot = 0);
  for (i = 1, #fa,
    my(g = fa[i]);
    if (poldegree(g) == 1, listput(out, [-1, -1]),
      my(ab = rnfequation(BASE, g), nf = nfinit([ab, [PP]]),
         dec = idealprimedec(nf, PP));
      for (j = 1, #dec,
        if (dec[j].f % 2 != 0, listput(out, [-9, -9]),
          listput(out, [dec[j].e, dec[j].f / 2]);
          tot += dec[j].e * dec[j].f / 2))));
  if (tot != 8, listput(out, [-8, tot]));
  vecsort(Vec(out))
}
sigq(f, p) = {
  my(fa = factor(f)[,1]~, out = List());
  for (i = 1, #fa,
    my(g = fa[i], nf, dec);
    if (poldegree(g) == 1, listput(out, [1,1]),
      nf = nfinit([g, [p]]);
      dec = idealprimedec(nf, p);
      for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
"""


def parse_sig(rest):
    rest = rest.strip()
    if rest == '[]':
        return ()
    return tuple(sorted(tuple(int(x) for x in pair.strip('[] ').split(','))
                        for pair in rest[1:-1].split('], [')))


# -------------------------------------------------------------- test frame
def perts(d, p):
    w = (Fr(0), Fr(1))
    one = BONE

    def m(c, k, deg):
        out = [BZERO] * (deg + 1)
        out[deg] = bmul(c, (Fr(p ** k), Fr(0)), d)
        return out
    return [
        ('P1', 0, m(one, 6, 0)), ('P2', 0, m(w, 6, 0)), ('P3', 0, m(w, 5, 1)),
        ('P4', 1, m(one, 4, 0)), ('P5', 1, m(w, 4, 1)),
        ('P6', 2, m(one, 3, 0)), ('P7', 2, m(w, 3, 1)),
        ('P8', 3, m(one, 2, 0)), ('P9', 3, m(w, 2, 1)),
    ]


def find_inert2(d, p):
    for b in rall(p):
        if b == (0, 0) or b[1] == 0:
            continue
        for a in rall(p):
            if not quad_roots(a, b, d, p):
                return a, b
    raise RuntimeError('no inert quadratic found')


def find_r3(d, p):
    """degree-3 irreducible over F_{p^2} with r(0) != 0 (rootless cubic)."""
    for a in rall(p):
        for b in rall(p):
            if b == (0, 0):
                continue
            ok = True
            for z in rall(p):
                v = radd(radd(rmul(rmul(z, z, d, p), z, d, p),
                              rmul(a, z, d, p), p), b, p)
                if v == (0, 0):
                    ok = False
                    break
            if ok:
                return a, b
    raise RuntimeError('no cubic found')


def build_psi(d, p, kappa_ul, rcoefs):
    """Psi_{kappa, r} per DEFINITION HE6-1 in this frame (eta = 1).
    kappa_ul = (u, l); rcoefs = [c_0, ..., c_{deg-1}] over F_{p^2}."""
    u, l = kappa_ul
    deg = len(rcoefs)
    Phi = [(Fr(-p), Fr(0)), BZERO, BONE]
    psi = [BONE]
    for _ in range(l * deg):
        psi = pmul(psi, Phi, d)
    for t in range(deg):
        c = rcoefs[t]
        if c == (0, 0):
            continue
        k = (deg - t) * u
        i = k % 2
        B = [BZERO] * (i + 1)
        B[i] = bmul(lift(c, p), (Fr(p ** ((k - i) // 2)), Fr(0)), d)
        Pt = [BONE]
        for _ in range(l * t):
            Pt = pmul(Pt, Phi, d)
        psi = padd(psi, pmul(B, Pt, d))
    return psi


# --------------------------------------------------------------------- run
def main():
    t0 = time.time()
    results = {'frames': [], 'violations': 0, 'teeth': {}}
    teeth = {'T-BASEFIELD': 0, 'T-PLANTDICT': 0, 'T-BADPERT': False}
    tot_pari = 0

    for (d, p) in [(-1, 3), (2, 5)]:
        w = (0, 1)
        # config residuals
        s = w
        sp = s
        for _ in range(p - 1):
            sp = rmul(sp, s, d, p)
        assert sp != s, 'w not moved by Frobenius?'
        tr = radd(s, sp, p)
        nm = rmul(s, sp, d, p)
        frob = {'c2': ((-tr[0]) % p, (-tr[1]) % p), 'c0': nm,
                'pred': ((4, 1), (4, 1))}
        mix_s1, mix_s2 = (1, 0), w
        mixtr = radd(mix_s1, mix_s2, p)
        splitmix = {'c2': ((-mixtr[0]) % p, (-mixtr[1]) % p),
                    'c0': rmul(mix_s1, mix_s2, d, p), 'pred': ((4, 1), (4, 1))}
        ia, ib = find_inert2(d, p)
        inert2 = {'c2': ia, 'c0': ib, 'pred': ((4, 2),)}
        configs = [('FROBSPLIT', frob), ('SPLITMIX', splitmix),
                   ('INERT2', inert2)]

        frame_rec = {'d': d, 'p': p, 'rows': []}
        print('== frame d=%d p=%d (base residue field F_%d) ==' % (d, p, p * p))

        gp_jobs = []      # (tag, kind, polystr)
        member_meta = []  # (config, pertname, is_int, pred)

        for cname, cfg in configs:
            C2 = (Fr(cfg['c2'][0]), Fr(cfg['c2'][1]))
            C0 = (Fr(cfg['c0'][0]), Fr(cfg['c0'][1]))
            plist = [('base', None, None)] + \
                [(nm_, j, term) for nm_, j, term in perts(d, p)]
            for nm_, j, term in plist:
                pert = [] if term is None else [(j, term)]
                f, _A = build_f(d, p, C2, C0, pert)
                rd, err = reader(f, d, p)
                if err:
                    viol('FP1', '%s/%s d=%d p=%d: %s' % (cname, nm_, d, p, err))
                    continue
                pred = dict_sigma(rd['R'], d, p)
                if pred != cfg['pred']:
                    viol('FP1', '%s/%s: reader residual mispredicts: %s vs %s'
                         % (cname, nm_, pred, cfg['pred']))
                is_int = all(c[1] == 0 for c in f)
                idx = len(member_meta)
                gp_jobs.append(('M%d' % idx, 'rel', gp_poly(f)))
                if cname == 'FROBSPLIT' and is_int:
                    gp_jobs.append(('C%d' % idx, 'q',
                                    '+'.join('(%d)*x^%d'
                                             % (Fr(c[0]).numerator, i)
                                             for i, c in enumerate(f))))
                member_meta.append((cname, nm_, is_int, cfg['pred']))

            # FP3 identities on the base member only
            f0, _ = build_f(d, p, C2, C0, [])
            r3a, r3b = find_r3(d, p)
            psi_gen = build_psi(d, p, (5, 2), [r3b, r3a, (0, 0)])
            R = resultant(f0, psi_gen, d)
            got = 2 * vP(R, p)
            if got != 120:
                viol('FP3', '%s flat generic: 2vP = %s != 120' % (cname, got))
            psi_h3 = build_psi(d, p, (3, 1), [(1, 0)])
            R = resultant(f0, psi_h3, d)
            got = 2 * vP(R, p)
            if got != 20:
                viol('FP3', '%s flat height-3: 2vP = %s != 20' % (cname, got))
            if cname in ('FROBSPLIT', 'SPLITMIX'):
                roots = quad_roots(cfg['c2'], cfg['c0'], d, p)
                for rt in roots:
                    psi_lab = build_psi(d, p, (5, 2), [((-rt[0]) % p,
                                                        (-rt[1]) % p)])
                    R = resultant(f0, psi_lab, d)
                    got = 2 * vP(R, p)
                    if not got > 40:
                        viol('FP3', '%s label %s: 2vP = %s not > 40'
                             % (cname, rt, got))
            else:
                psi_lab = build_psi(d, p, (5, 2), [cfg['c0'], cfg['c2']])
                R = resultant(f0, psi_lab, d)
                got = 2 * vP(R, p)
                if not got > 80:
                    viol('FP3', '%s inert label: 2vP = %s not > 80'
                         % (cname, got))

        # T-BADPERT: on-line perturbation at j=2 must be CAUGHT (p=3 only)
        if p == 3:
            C2 = (Fr(frob['c2'][0]), Fr(frob['c2'][1]))
            C0 = (Fr(frob['c0'][0]), Fr(frob['c0'][1]))
            bad = [(2, [BZERO, (Fr(p ** 2), Fr(0))])]  # dv 5: ON the line
            fb, _ = build_f(d, p, C2, C0, bad)
            rd, err = reader(fb, d, p)
            caught = bool(err) or dict_sigma(rd['R'], d, p) != frob['pred']
            teeth['T-BADPERT'] = teeth['T-BADPERT'] or caught
            if not caught:
                viol('T-BADPERT', 'on-line perturbation NOT caught')

        # ---- run gp batch for the frame
        script = ['BASE = nfinit(y^2 - (%d)); PP = %d;' % (d, p), GP_REL]
        for tag, kind, ps in gp_jobs:
            if kind == 'rel':
                script.append('print("%s ", sigrel(%s));' % (tag, ps))
            else:
                script.append('print("%s ", sigq(%s, %d));' % (tag, ps, p))
        script.append('quit')
        out = gp_run('\n'.join(script) + '\n')
        got = {}
        for line in out.splitlines():
            parts = line.strip().split(' ', 1)
            if len(parts) == 2 and (parts[0].startswith('M')
                                    or parts[0].startswith('C')):
                got[parts[0]] = parse_sig(parts[1])

        for idx, (cname, nm_, is_int, pred) in enumerate(member_meta):
            sig = got.get('M%d' % idx)
            tot_pari += 1
            if sig is None:
                viol('FP2', 'M%d (%s/%s): no oracle output' % (idx, cname, nm_))
                continue
            if any(x < 0 for pair in sig for x in pair):
                viol('FP2', 'M%d (%s/%s): oracle sanity flag %s'
                     % (idx, cname, nm_, sig))
                continue
            if sig != pred:
                viol('FP2', 'M%d (%s/%s): sigma_rel %s != predicted %s'
                     % (idx, cname, nm_, sig, pred))
            if pred == ((4, 1), (4, 1)) and sig != ((8, 1),):
                teeth['T-PLANTDICT'] += 1
            csig = got.get('C%d' % idx)
            if csig is not None:
                tot_pari += 1
                if csig != ((4, 2),):
                    viol('FP4', 'M%d control over Q_p: %s != {(4,2)}'
                         % (idx, csig))
                elif sig == ((4, 1), (4, 1)):
                    teeth['T-BASEFIELD'] += 1
            frame_rec['rows'].append({'m': idx, 'cfg': cname, 'pert': nm_,
                                      'int': is_int, 'sig': list(sig),
                                      'ctrl': list(csig) if csig else None})
        results['frames'].append(frame_rec)
        print('frame done: %d members scored' % len(member_meta))

    results['violations'] = len(VIOL)
    results['teeth'] = teeth
    results['pari_jobs'] = tot_pari
    results['secs'] = round(time.time() - t0, 1)
    ok_teeth = (teeth['T-BASEFIELD'] == 10 and teeth['T-PLANTDICT'] == 40
                and teeth['T-BADPERT'])
    print('TEETH: %s (BASEFIELD %d/10, PLANTDICT %d/40, BADPERT %s)'
          % ('all fired' if ok_teeth else 'INCOMPLETE',
             teeth['T-BASEFIELD'], teeth['T-PLANTDICT'], teeth['T-BADPERT']))
    print('TOTAL: %d PARI jobs, %d violations, %.1f s'
          % (tot_pari, len(VIOL), results['secs']))
    with open('he6_pe4_fresh_results.json', 'w') as fh:
        json.dump(results, fh, indent=1)
    print('VERDICT: %s' % ('GREEN' if not VIOL and ok_teeth else 'RED'))
    return 0 if not VIOL and ok_teeth else 1


if __name__ == '__main__':
    sys.exit(main())
