#!/usr/bin/env python3
"""GENHN passPE3 fresh instrument (hostile verifier, 2026-08-09).

FRESH ROUTE, disjoint from the sealed battery (no tower leaf rows),
PE1's legs ((1,3,2) sweeps + the four refuted (2,1,4) instances),
genhnr2_supp.py (outer-f1=1 genres (2,1,4)->(2,1,2) u2 in {5,7},
(2,1,4)->(1,2,2) over F4, 3-stage u3=21), and genhn_pe2_fresh.py
(outer-f1=2 genres, boundary u2 = e2D'h+1, Q=4 base change).

 FR1  FIRST e2 = 3 tower genre: (2,1,6)->(3,1,2) over Q2, u2 = 7
      (kappa2 = 7/3; node floor e2*D'h = 6 < 7, gcd(7,3)=1),
      Phi2 = (x^2-2)^3 - 8x (n-hat(7) = 8x), D2 = 6, K2 = F2.
   FR1-K: Phi2 irreducible, (e,f) = (6,1) BOTH routes;
      v_pr(Phi'(xi)) = 7 EXACT and v_pr(x) = 3 (nfeltval).
   FR1-S: composed slot lemma (ii) at e2 = 3: dv2(A(xi)) =
      min(6*v2(c) + 3a + 7b) EXACT vs nfeltval, 40 random legs
      (classes 3a+7b all distinct mod 6 at f1f2 = 1: no ties).
   FR1-D: T(b)'(iii) dictionary at n = 12 leaves (floor: dv2(Y2)
      > e2f2u2 = 21, so p0 > 42):
        RAM(43):    f = P2^2 + 64*Phi'            -> {(12,1)}
        RAM(43)b:   f = P2^2 + 4xPhi'*P2 + 64Phi' -> {(12,1)}
        INERT(44,22): f = P2^2 + 4xPhi'*P2 + 32Phi'^2 -> {(6,2)}
          (T^2+T+1 forced over K2 = F2)
        2SIDED(45,22): f = P2^2 + 4xPhi'*P2 + 128x -> {(6,1),(6,1)}
      each + one deep perturbation (+2^45 * rand poly, deg < 12);
      level-1 gate (side 7/3 over [0,6], dv(A0) = 14 exact, mids
      above) enforced; PARI sig BOTH routes; disc != 0.
 FR2  FIRST p = 3 tower sigma legs + FIRST f2 = 2 composed
      INERT/SPLIT with genuine eta2-letters (K2 = F9):
      genre (2,1,4)->(1,2,2) over Q3, u2 = 3, psi2 = T^2 + 1
      (irred /F3), Phi2 = (x^2-3)^2 + 27, D2 = 4.
   FR2-K: (e,f) = (2,2) both routes; v_pr(Phi'(xi)) = 3 EXACT.
   FR2-S: slot lemma at the WITHIN-CLASS branch (e2 = 1, f2 = 2 --
      slot classes NOT distinct mod 2): 30 random legs + 6
      constructed TIES (c*3^5*Phi' + c'*3^6*x, both height 13:
      digit res(c) + res(c')*eta2 can never vanish -- the
      eta2-independence physically at nfeltval level; first
      DIRECT nfeltval tie contact at f2 = 2).
   FR2-D: dictionary at n = 8 (floor dv2(Y2) > 6, p0 > 12):
        RAM(13):    C0 = 243*Phi'                  -> {(4,2)}
        RAM-tie(13): C0 = 243*Phi' + 729*x         -> {(4,2)}
        INERT(14):  C0 = 2*3^7 + 486*x*Phi' (digit 2+2*eta2;
          -d0 = 1+eta2 a NON-SQUARE in F9, either psi2-root)
                                                   -> {(2,4)}
        SPLITEQ(14): C0 = 486*x*Phi' (digit 2*eta2; -d0 = eta2
          = (1-eta2)^2 a SQUARE, either root)      -> {(2,2),(2,2)}
        2SIDED(15,7): C1 = 9*Phi', C0 = 729*Phi'   -> {(2,2),(2,2)}
      each + one deep perturbation (+3^30 * rand, deg < 8);
      level-1 gate (side 3 over [0,4], dv(A0) = 12 exact,
      residual (T^2+1)^... mids above); PARI both routes.
 FR3  [GENHN-TOW-1] item (6) probe at a SECOND u3 (23 vs the
      supp's single 21), chain (2,1,4)->(2,1,2)->..., Phi2A =
      (x^2-2)^2 - 4x, Phi3 = Phi2A^2 - 16x*Phi'
      (n2-hat(23) = 16x*Phi': 4*4+2*1+5*1 = 23, gcd(23,2)=1,
      23/2 > dv2(x^4) = 8).  DIAGNOSTIC NOTE: this Phi3's
      Phi'-development keeps its x-overflow carry UNCANCELLED
      (b=1 coefficient 16-16x != 0, dv 8 > side height 15/2) yet
      is ONE-SIDED of slope 5/2 with residual T^2+1 = psi2^2 --
      checked symbolically here; evidence that the box's witness
      sentence over-attributes one-sidedness to the exact carry
      cancellation (finding candidate), while the box's DERIVED
      GRAMMAR (ladder normalizers + iterated key) extends to a
      second instance.  Item (6) is BOXED (open): FR3 is evidence
      about the box text, not a proof obligation.
   FR3-K: Phi3 irreducible (e,f) = (8,1); v_pr(x)=4,
      v_pr(Phi')=10, v_pr(Phi2A)=23 -- the full intermediate
      ascent data at the new key (nfeltval).
   FR3-D: leaf f = Phi3^2 + 128*x*Phi'*Phi2A (dv3 = 93 odd
      > 2*46/... floor 2*dv3(Y3) > 92; Phi2A-coefficient of E0 at
      dv2 = 35 > 34.5 = the level-2 side height -- parse-gated at
      all three levels) -> RAM(93) -> {(16,1)}; + perturbation
      (+2^60 * rand, deg < 16); PARI both routes.
 TEETH (each must fire >= 1 else RED):
   T-SLOT-E3: wrong slot offset (u2+1 = 8 in FR1's formula) must
      mismatch nfeltval on >= 1 leg.
   T-DICT-F9: FR2 INERT prediction swapped to {(2,2),(2,2)} and
      SPLITEQ swapped to {(2,4)} must be REFUSED by PARI.
   T-FLOOR: FR1 below-floor member f = P2^2 + 2*Phi' (p0 = 13 <
      43: not realizable on the tower-node locus) -- the naive
      dictionary says {(12,1)}; fires iff PARI != {(12,1)}
      (if PARI coincides, disclosed as unfired and the tooth is
      dropped from the RED condition -- floor-violation need not
      change sigma, it voids the READ's warrant).

PREREGISTERED: every FR1/FR2/FR3 scored check EXACT; the three
teeth fire (T-FLOOR best-effort as displayed).  VERDICT GREEN iff
0 violations on scored checks and T-SLOT-E3 + T-DICT-F9 fire.

Independent: no imports from the sealed battery, the supp runner,
or the PE1/PE2 instruments; own polynomial engine + own gates;
PARI via gp subprocess (route 1 = global factor + nfinit +
idealprimedec; route 2 = factorpadic + per-factor lift).
"""
import random
import subprocess
import sys
import time

random.seed(20260809)
T0 = time.time()
VIOL = []
NCHK = {}
TEETH = {}


def say(s):
    print(s)
    sys.stdout.flush()


def chk(fam, ok, msg):
    NCHK[fam] = NCHK.get(fam, 0) + 1
    if not ok:
        VIOL.append('%s: %s' % (fam, msg))
        say('  VIOLATION %s: %s' % (fam, msg))


# ---------------- polynomial engine (Z[x], lists low->high) -----
def pstrip(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])


def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return pstrip(out)


def psca(c, f):
    return pstrip([c * a for a in f])


def pdivmod_monic(f, g):
    """f = q*g + r with g monic; exact over Z."""
    f = list(f)
    q = [0] * max(1, len(f) - len(g) + 1)
    while len(f) >= len(g):
        c = f[-1]
        d = len(f) - len(g)
        q[d] = c
        for i, a in enumerate(g):
            f[d + i] -= c * a
        pstrip(f)
        if not f:
            break
    return pstrip(q), pstrip(f)


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def dev(f, key, mu):
    """key-adic development: f = sum D[j] key^j, deg D[j] < deg key."""
    g, D = list(f), []
    for _ in range(mu):
        g, r = pdivmod_monic(g, key)
        D.append(r)
    return D, g


def dv_lin(c, p, xw, denom):
    """dv of a deg<2 coefficient c0 + c1 x on the ladder where
    dv(p) = denom, dv(x) = xw.  Exact (parities differ)."""
    vals = []
    if len(c) > 0 and c[0] != 0:
        vals.append(denom * vp(c[0], p))
    if len(c) > 1 and c[1] != 0:
        vals.append(denom * vp(c[1], p) + xw)
    return min(vals) if vals else None


def poly_str(f, var='x'):
    return '+'.join('(%d)*%s^%d' % (c, var, i)
                    for i, c in enumerate(f) if c) or '0'


# ---------------- gp plumbing ------------------------------------
GP_HDR = r"""
default(parisizemax, 2000000000);
sig1(f, p) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
        listput(out, [1, 1]),
        my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
ef1(g, p) = {
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  vecsort(vector(#dec, j, [dec[j].e, dec[j].f]))
}
sig2(f, p) = {
  my(F = factorpadic(f, p, 500), out = List());
  for (i = 1, matsize(F)[1],
    my(v = ef1(liftall(F[i, 1]), p));
    for (j = 1, #v, listput(out, v[j])));
  vecsort(Vec(out))
}
"""


def run_gp(lines):
    src = GP_HDR + '\n' + '\n'.join(lines) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=1800)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-300:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res.setdefault(parts[0], []).append(parts[1].strip())
    return res


def sig_parse(s):
    s = s.replace('[', '').replace(']', '')
    if not s:
        return []
    nums = [int(t) for t in s.split(',')]
    return sorted((nums[i], nums[i + 1]) for i in range(0, len(nums), 2))


# ================= FR1: e2 = 3 tower (2,1,6)->(3,1,2) /Q2 ========
PHI1 = [-2, 0, 1]                       # x^2 - 2
P2F1 = padd(pmul(pmul(PHI1, PHI1), PHI1), psca(-8, [0, 1]))
# Phi2 = (x^2-2)^3 - 8x


def fr1_slot_poly(coeffs):
    """A = sum c_{a,b} x^a Phi'^b, a<2, b<3 (c indexed [b][a])."""
    A = []
    pb = [1]
    for b in range(3):
        for a in range(2):
            c = coeffs[b][a]
            if c:
                A = padd(A, psca(c, pmul(pb, [0, 1] if a else [1])))
        pb = pmul(pb, PHI1)
    return A


def fr1_slot_min(coeffs):
    vals = []
    for b in range(3):
        for a in range(2):
            c = coeffs[b][a]
            if c:
                vals.append(6 * vp(c, 2) + 3 * a + 7 * b)
    return min(vals) if vals else None


def level1_gate(f, p, mu1, dvA0, slope_num, slope_den, key, xw, denom):
    """Phi'-development of f: dv(A0) exact = dvA0; mid pins weakly
    above the side dvA0 - j*slope; returns error or None."""
    D, g = dev(f, key, mu1)
    if g != [1]:
        return 'dev not monic'
    dvs = [dv_lin(c, p, xw, denom) for c in D]
    if dvs[0] != dvA0:
        return 'dv(A0) = %s want %d' % (dvs[0], dvA0)
    for j in range(1, mu1):
        if dvs[j] is not None and \
           slope_den * dvs[j] < slope_num * (mu1 - j):
            return 'pin j=%d at %s below side' % (j, dvs[j])
    return None


def fam_fr1(gp_jobs):
    say('== FR1: e2 = 3 tower genre (2,1,6)->(3,1,2) /Q2, u2 = 7 ==')
    # K legs
    gp_jobs.append(('FR1K-sig1', 'print("FR1K-sig1 ", sig1(%s, 2))'
                    % poly_str(P2F1)))
    gp_jobs.append(('FR1K-sig2', 'print("FR1K-sig2 ", sig2(%s, 2))'
                    % poly_str(P2F1)))
    gp_jobs.append(('FR1K-val',
                    'my(nf = nfinit([%s, [2]]), pr = idealprimedec(nf, 2)[1]);'
                    'print("FR1K-val ", [nfeltval(nf, Mod(%s, %s), pr),'
                    ' nfeltval(nf, Mod(x, %s), pr)])'
                    % (poly_str(P2F1), poly_str(PHI1),
                       poly_str(P2F1), poly_str(P2F1))))
    # S legs: 40 random + tooth
    slegs = []
    for k in range(40):
        coeffs = [[0, 0], [0, 0], [0, 0]]
        nz = 0
        while nz == 0:
            for b in range(3):
                for a in range(2):
                    if random.random() < 0.7:
                        u = random.choice([1, 3, 5, 7, -1, -3])
                        coeffs[b][a] = u * (2 ** random.randint(0, 5))
                        nz += 1
                    else:
                        coeffs[b][a] = 0
        A = fr1_slot_poly(coeffs)
        want = fr1_slot_min(coeffs)
        wrong = min(6 * vp(c, 2) + 3 * a + 8 * b
                    for b in range(3) for a in range(2)
                    if (c := coeffs[b][a]))
        slegs.append((k, want, wrong))
        gp_jobs.append(('FR1S-%d' % k,
                        'my(nf = nfinit([%s, [2]]), pr = idealprimedec(nf, 2)[1]);'
                        'print("FR1S-%d ", nfeltval(nf, Mod(%s, %s), pr))'
                        % (poly_str(P2F1), k, poly_str(A),
                           poly_str(P2F1))))
    # D legs
    C1 = pmul(psca(4, [0, 1]), PHI1)          # 4 x Phi', dv2 = 22
    members = [
        ('FR1D-RAM43', padd(pmul(P2F1, P2F1), psca(64, PHI1)),
         [(12, 1)]),
        ('FR1D-RAM43b', padd(padd(pmul(P2F1, P2F1),
                                  pmul(C1, P2F1)), psca(64, PHI1)),
         [(12, 1)]),
        ('FR1D-INERT', padd(padd(pmul(P2F1, P2F1), pmul(C1, P2F1)),
                            psca(32, pmul(PHI1, PHI1))),
         [(6, 2)]),
        ('FR1D-2SIDED', padd(padd(pmul(P2F1, P2F1), pmul(C1, P2F1)),
                             psca(128, [0, 1])),
         [(6, 1), (6, 1)]),
    ]
    out = []
    for tag, f, want in members:
        err = level1_gate(f, 2, 6, 14, 7, 3, PHI1, 1, 2)
        chk('FR1-D', err is None, '%s level-1 gate: %s' % (tag, err))
        out.append((tag, f, want))
        fp = list(f)
        pert = [random.randint(-3, 3) * (2 ** 45)
                for _ in range(12)]
        fp = padd(fp, pert)
        errp = level1_gate(fp, 2, 6, 14, 7, 3, PHI1, 1, 2)
        chk('FR1-D', errp is None, '%s-pert gate: %s' % (tag, errp))
        out.append((tag + '-pert', fp, want))
    for tag, f, want in out:
        gp_jobs.append((tag + '-r1', 'print("%s-r1 ", sig1(%s, 2))'
                        % (tag, poly_str(f))))
        gp_jobs.append((tag + '-r2', 'print("%s-r2 ", sig2(%s, 2))'
                        % (tag, poly_str(f))))
        gp_jobs.append((tag + '-disc',
                        'print("%s-disc ", poldisc(%s) != 0)'
                        % (tag, poly_str(f))))
    # T-FLOOR tooth member
    ffl = padd(pmul(P2F1, P2F1), psca(2, PHI1))
    gp_jobs.append(('FR1-TFLOOR', 'print("FR1-TFLOOR ", sig1(%s, 2))'
                    % poly_str(ffl)))
    return slegs, out


# ================= FR2: p = 3, f2 = 2 tower (2,1,4)->(1,2,2) =====
PHI1B = [-3, 0, 1]                      # x^2 - 3
P2F2 = padd(pmul(PHI1B, PHI1B), [27])   # Phi2 = (x^2-3)^2 + 27


def fr2_slot_poly(coeffs):
    """A = sum c_{a-part folded in} x^i Phi'^b, i<2, b<2."""
    A = []
    pb = [1]
    for b in range(2):
        for i in range(2):
            c = coeffs[b][i]
            if c:
                A = padd(A, psca(c, pmul(pb, [0, 1] if i else [1])))
        pb = pmul(pb, PHI1B)
    return A


def fr2_slot_min(coeffs):
    vals = []
    for b in range(2):
        for i in range(2):
            c = coeffs[b][i]
            if c:
                vals.append(2 * vp(c, 3) + i + 3 * b)
    return min(vals) if vals else None


def fam_fr2(gp_jobs):
    say('== FR2: p = 3 tower genre (2,1,4)->(1,2,2), K2 = F9 ==')
    gp_jobs.append(('FR2K-sig1', 'print("FR2K-sig1 ", sig1(%s, 3))'
                    % poly_str(P2F2)))
    gp_jobs.append(('FR2K-sig2', 'print("FR2K-sig2 ", sig2(%s, 3))'
                    % poly_str(P2F2)))
    gp_jobs.append(('FR2K-val',
                    'my(nf = nfinit([%s, [3]]), pr = idealprimedec(nf, 3)[1]);'
                    'print("FR2K-val ", [nfeltval(nf, Mod(%s, %s), pr),'
                    ' nfeltval(nf, Mod(x, %s), pr)])'
                    % (poly_str(P2F2), poly_str(PHI1B),
                       poly_str(P2F2), poly_str(P2F2))))
    slegs = []
    for k in range(30):
        coeffs = [[0, 0], [0, 0]]
        nz = 0
        while nz == 0:
            for b in range(2):
                for i in range(2):
                    if random.random() < 0.7:
                        u = random.choice([1, 2, 4, 5, -1, -2])
                        coeffs[b][i] = u * (3 ** random.randint(0, 5))
                        nz += 1
                    else:
                        coeffs[b][i] = 0
        A = fr2_slot_poly(coeffs)
        want = fr2_slot_min(coeffs)
        slegs.append(('FR2S-%d' % k, want))
        gp_jobs.append(('FR2S-%d' % k,
                        'my(nf = nfinit([%s, [3]]), pr = idealprimedec(nf, 3)[1]);'
                        'print("FR2S-%d ", nfeltval(nf, Mod(%s, %s), pr))'
                        % (poly_str(P2F2), k, poly_str(A),
                           poly_str(P2F2))))
    # 6 constructed within-class ties at height 13:
    # c*3^5*Phi' (b=1,i=0: 10+3) + c'*3^6*x (b=0,i=1: 12+1)
    for k, (c, cp) in enumerate([(1, 1), (1, 2), (2, 1), (2, 2),
                                 (1, -1), (-2, 1)]):
        A = padd(psca(c * 243, PHI1B), psca(cp * 729, [0, 1]))
        slegs.append(('FR2S-tie%d' % k, 13))
        gp_jobs.append(('FR2S-tie%d' % k,
                        'my(nf = nfinit([%s, [3]]), pr = idealprimedec(nf, 3)[1]);'
                        'print("FR2S-tie%d ", nfeltval(nf, Mod(%s, %s), pr))'
                        % (poly_str(P2F2), k, poly_str(A),
                           poly_str(P2F2))))
    # D legs
    xphi = pmul([0, 1], PHI1B)              # x*Phi'
    members = [
        ('FR2D-RAM13', padd(pmul(P2F2, P2F2), psca(243, PHI1B)),
         [(4, 2)]),
        ('FR2D-RAMtie', padd(pmul(P2F2, P2F2),
                             padd(psca(243, PHI1B), psca(729, [0, 1]))),
         [(4, 2)]),
        ('FR2D-INERT', padd(pmul(P2F2, P2F2),
                            padd([2 * 3 ** 7], psca(486, xphi))),
         [(2, 4)]),
        ('FR2D-SPLITEQ', padd(pmul(P2F2, P2F2), psca(486, xphi)),
         [(2, 2), (2, 2)]),
        ('FR2D-2SIDED', padd(padd(pmul(P2F2, P2F2),
                                  pmul(psca(9, PHI1B), P2F2)),
                             psca(729, PHI1B)),
         [(2, 2), (2, 2)]),
    ]
    out = []
    for tag, f, want in members:
        err = level1_gate(f, 3, 4, 12, 3, 1, PHI1B, 1, 2)
        chk('FR2-D', err is None, '%s level-1 gate: %s' % (tag, err))
        out.append((tag, f, want))
        fp = padd(list(f), [random.randint(-2, 2) * (3 ** 30)
                            for _ in range(8)])
        errp = level1_gate(fp, 3, 4, 12, 3, 1, PHI1B, 1, 2)
        chk('FR2-D', errp is None, '%s-pert gate: %s' % (tag, errp))
        out.append((tag + '-pert', fp, want))
    for tag, f, want in out:
        gp_jobs.append((tag + '-r1', 'print("%s-r1 ", sig1(%s, 3))'
                        % (tag, poly_str(f))))
        gp_jobs.append((tag + '-r2', 'print("%s-r2 ", sig2(%s, 3))'
                        % (tag, poly_str(f))))
        gp_jobs.append((tag + '-disc',
                        'print("%s-disc ", poldisc(%s) != 0)'
                        % (tag, poly_str(f))))
    return slegs, out


# ================= FR3: item (6) probe at u3 = 23 ================
P2A = padd(pmul(PHI1, PHI1), psca(-4, [0, 1]))   # (x^2-2)^2 - 4x
PHI3B = padd(pmul(P2A, P2A),
             psca(-16, pmul([0, 1], PHI1)))      # Phi2A^2 - 16xPhi'


def fam_fr3(gp_jobs):
    say('== FR3: item (6) probe, u3 = 23 (Phi3 = Phi2A^2 - 16xPhi\') ==')
    # symbolic: Phi'-development of Phi3 one-sided WITHOUT carry
    # cancellation
    D, g = dev(PHI3B, PHI1, 5)
    chk('FR3-sym', g == [], 'Phi3 dev leaves quotient %s' % g)
    dvs = [dv_lin(c, 2, 1, 2) for c in D]
    say('  Phi3 Phi\'-dev dv-pins: %s (b = 0..4)' % dvs)
    chk('FR3-sym', dvs[0] == 10 and dvs[4] == 0,
        'endpoint pins %s want (0:10, 4:0)' % dvs)
    chk('FR3-sym', dvs[1] is not None and dvs[1] == 8,
        'b=1 pin %s want 8 (UNCANCELLED carry, above side 15/2)'
        % dvs[1])
    chk('FR3-sym', 2 * dvs[1] > 15 and 2 * dvs[2] > 10,
        'mid pins above the side')
    # residual on side pins (0,10),(4,0): T^2 + res(32/2^5) = T^2+1
    chk('FR3-sym', D[0] == [32] and vp(32, 2) == 5,
        'constant coeff %s want 32 (res 1 -> residual T^2+1 = psi2^2)'
        % D[0])
    gp_jobs.append(('FR3K-sig1', 'print("FR3K-sig1 ", sig1(%s, 2))'
                    % poly_str(PHI3B)))
    gp_jobs.append(('FR3K-sig2', 'print("FR3K-sig2 ", sig2(%s, 2))'
                    % poly_str(PHI3B)))
    gp_jobs.append(('FR3K-val',
                    'my(nf = nfinit([%s, [2]]), pr = idealprimedec(nf, 2)[1]);'
                    'print("FR3K-val ", [nfeltval(nf, Mod(x, %s), pr),'
                    ' nfeltval(nf, Mod(%s, %s), pr),'
                    ' nfeltval(nf, Mod(%s, %s), pr)])'
                    % (poly_str(PHI3B), poly_str(PHI3B),
                       poly_str(PHI1), poly_str(PHI3B),
                       poly_str(P2A), poly_str(PHI3B))))
    # leaf: f = Phi3^2 + 128 x Phi' Phi2A  (dv3 = 93)
    E0 = psca(128, pmul(pmul([0, 1], PHI1), P2A))
    f = padd(pmul(PHI3B, PHI3B), E0)
    # level-1 gate: (2,1,8): side 5/2 over [0,8], dv(A0) = 20
    err = level1_gate(f, 2, 8, 20, 5, 2, PHI1, 1, 2)
    chk('FR3-D', err is None, 'leaf level-1 gate: %s' % err)
    # level-2 gate: Phi2A-development, side 23/2 over [0,4],
    # dv2(D0) = 46 exact, mids above (dv2 = 4v: p @ 4, x @ 2,
    # Phi' @ 5)
    D2, g2 = dev(f, P2A, 4)
    chk('FR3-D', g2 == [1], 'level-2 dev monic: %s' % g2)

    def dv2_a(c):
        """dv2 of deg<4 poly via Phi'-dev: slots x^i Phi'^b,
        heights 4*vp + 2i + 5b (exact: classes 0,2,5,7 mod 4
        distinct... 0,2,1,3 -- distinct)."""
        cd, _ = dev(c, PHI1, 2)
        vals = []
        for b in range(2):
            cc = cd[b] if b < len(cd) else []
            for i in range(2):
                if i < len(cc) and cc[i] != 0:
                    vals.append(4 * vp(cc[i], 2) + 2 * i + 5 * b)
        return min(vals) if vals else None
    d2 = [dv2_a(r) for r in D2]
    say('  leaf level-2 dv2(D): %s' % d2)
    chk('FR3-D', d2[0] == 46, 'dv2(D0) = %s want 46' % d2[0])
    for J in range(1, 4):
        chk('FR3-D', d2[J] is None or 2 * d2[J] > 23 * (4 - J),
            'level-2 pin J=%d at %s not above side' % (J, d2[J]))
    fp = padd(list(f), [random.randint(-3, 3) * (2 ** 60)
                        for _ in range(16)])
    for tag, ff in [('FR3D-RAM93', f), ('FR3D-RAM93-pert', fp)]:
        gp_jobs.append((tag + '-r1', 'print("%s-r1 ", sig1(%s, 2))'
                        % (tag, poly_str(ff))))
        gp_jobs.append((tag + '-r2', 'print("%s-r2 ", sig2(%s, 2))'
                        % (tag, poly_str(ff))))
        gp_jobs.append((tag + '-disc',
                        'print("%s-disc ", poldisc(%s) != 0)'
                        % (tag, poly_str(ff))))
    return f


def main():
    gp_jobs = []
    fr1_slegs, fr1_members = fam_fr1(gp_jobs)
    fr2_slegs, fr2_members = fam_fr2(gp_jobs)
    fam_fr3(gp_jobs)
    say('  %d gp jobs total' % len(gp_jobs))
    res = run_gp([j[1] for j in gp_jobs])

    def get(tag):
        v = res.get(tag)
        return v[0] if v else None

    # FR1-K
    chk('FR1-K', sig_parse(get('FR1K-sig1') or '') == [(6, 1)],
        'Phi2 sig1 %s want [(6,1)]' % get('FR1K-sig1'))
    chk('FR1-K', sig_parse(get('FR1K-sig2') or '') == [(6, 1)],
        'Phi2 sig2 %s want [(6,1)]' % get('FR1K-sig2'))
    chk('FR1-K', get('FR1K-val') == '[7, 3]',
        'v_pr(Phi\'(xi)), v_pr(x) = %s want [7, 3]' % get('FR1K-val'))
    # FR1-S + tooth
    tooth_slot = 0
    for k, want, wrong in fr1_slegs:
        got = get('FR1S-%d' % k)
        chk('FR1-S', got is not None and int(got) == want,
            'slot leg %d: nfeltval %s want %d' % (k, got, want))
        if got is not None and int(got) != wrong:
            tooth_slot += 1
    TEETH['T-SLOT-E3'] = tooth_slot
    chk('TEETH', tooth_slot >= 1,
        'T-SLOT-E3 never fired (wrong-offset formula never differed)')
    # FR1-D
    for tag, f, want in fr1_members:
        for rt in ('r1', 'r2'):
            got = get('%s-%s' % (tag, rt))
            chk('FR1-D', got is not None and
                sig_parse(got) == sorted(want),
                '%s %s: %s want %s' % (tag, rt, got, sorted(want)))
        chk('FR1-D', get('%s-disc' % tag) == '1',
            '%s disc != 0' % tag)
    # T-FLOOR
    tf = get('FR1-TFLOOR')
    fired = tf is not None and sig_parse(tf) != [(12, 1)]
    TEETH['T-FLOOR'] = 1 if fired else 0
    say('  T-FLOOR: below-floor member PARI = %s (naive dict '
        '{(12,1)}) -> %s' % (tf, 'FIRED' if fired else
                             'unfired (disclosed, non-RED)'))
    # FR2-K
    chk('FR2-K', sig_parse(get('FR2K-sig1') or '') == [(2, 2)],
        'Phi2 sig1 %s want [(2,2)]' % get('FR2K-sig1'))
    chk('FR2-K', sig_parse(get('FR2K-sig2') or '') == [(2, 2)],
        'Phi2 sig2 %s want [(2,2)]' % get('FR2K-sig2'))
    chk('FR2-K', get('FR2K-val') == '[3, 1]',
        'v_pr(Phi\'(xi)), v_pr(x) = %s want [3, 1]' % get('FR2K-val'))
    # FR2-S
    for tag, want in fr2_slegs:
        got = get(tag)
        chk('FR2-S', got is not None and int(got) == want,
            '%s: nfeltval %s want %d' % (tag, got, want))
    # FR2-D + T-DICT-F9
    for tag, f, want in fr2_members:
        for rt in ('r1', 'r2'):
            got = get('%s-%s' % (tag, rt))
            chk('FR2-D', got is not None and
                sig_parse(got) == sorted(want),
                '%s %s: %s want %s' % (tag, rt, got, sorted(want)))
        chk('FR2-D', get('%s-disc' % tag) == '1',
            '%s disc != 0' % tag)
    inert_got = get('FR2D-INERT-r1')
    spl_got = get('FR2D-SPLITEQ-r1')
    td = 0
    if inert_got and sig_parse(inert_got) != [(2, 2), (2, 2)]:
        td += 1
    if spl_got and sig_parse(spl_got) != [(2, 4)]:
        td += 1
    TEETH['T-DICT-F9'] = td
    chk('TEETH', td == 2,
        'T-DICT-F9: swapped predictions not both refused '
        '(INERT %s, SPLITEQ %s)' % (inert_got, spl_got))
    # FR3
    chk('FR3-K', sig_parse(get('FR3K-sig1') or '') == [(8, 1)],
        'Phi3 sig1 %s want [(8,1)]' % get('FR3K-sig1'))
    chk('FR3-K', sig_parse(get('FR3K-sig2') or '') == [(8, 1)],
        'Phi3 sig2 %s want [(8,1)]' % get('FR3K-sig2'))
    chk('FR3-K', get('FR3K-val') == '[4, 10, 23]',
        'ascent data (v_pr(x), v_pr(Phi\'), v_pr(Phi2A)) = %s '
        'want [4, 10, 23]' % get('FR3K-val'))
    for tag in ('FR3D-RAM93', 'FR3D-RAM93-pert'):
        for rt in ('r1', 'r2'):
            got = get('%s-%s' % (tag, rt))
            chk('FR3-D', got is not None and
                sig_parse(got) == [(16, 1)],
                '%s %s: %s want [(16,1)]' % (tag, rt, got))
        chk('FR3-D', get('%s-disc' % tag) == '1', '%s disc' % tag)

    say('  teeth: %s' % TEETH)
    total = sum(NCHK.values())
    ok = (not VIOL) and TEETH.get('T-SLOT-E3', 0) >= 1 \
        and TEETH.get('T-DICT-F9', 0) == 2
    say('=== VERDICT: %s -- checks %s (total %d), %d violations '
        '(%.1fs) ===' % ('GREEN' if ok else 'RED', NCHK, total,
                         len(VIOL), time.time() - T0))
    for v in VIOL[:40]:
        say('  ' + v)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
