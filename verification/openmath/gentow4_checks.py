#!/usr/bin/env python3
"""GENTOW-4 battery: PARTIAL INNER SIDES ([GENHN-TOW-1] item (4)).

The reader implements THEOREM GENTOW-4.A + COR GENTOW-4.C
(GENTOW4_PROOF_2026-08-09.md): per level-1 label class, develop f by
THE CLASS'S OWN composed key Phi2, take the slope->T2 INITIAL part
of the hull of the composed pins (j, dv2(C_j)) -- it spans [0, mu2*]
with right-endpoint height c_g (LEMMA HE6R1-2's projection) -- and
decide by the translation/scale-invariant trichotomy (S3(v)):
  two sides -> 2SIDED; one side, p0 - c_g odd (l2 = 2) -> RAM;
  one side, integer slope: residual quadratic (raw f-level residues,
  gamma_g-scaled -- root tests scale-invariant) irreducible -> INERT
  / split -> SPLIT / double root -> alpha-refine at Phi2 - s*n2hat.
Sibling classes (simple residual factors) price as (e1*l, f1*d_r).
sigma(f) = union over classes.

FAMILIES (all PARTIAL: e2f2mu2 < mu1; genres (2,1,5)/(2,1,6)/(2,1,7)):
 P1 (2,1,5)/Q2 n=10: inner (2,1,u2=5) side [1,5] (T+1)^2, sibling
    slope 3 len 1 LEFT.  Phi2 = Phi'^2-4x, E2=T2=10.  PE2P-0 = the
    passPE2 witness f = Phi'^5+4Phi'^4+32Phi'+64x, PARI
    {(2,1),(4,1),(4,1)} -- regression row, must reproduce EXACTLY.
 P2 (2,1,5)/Q2 n=10: inner (1,2,u2=3) side [1,5] (T^2+T+1)^2 K2=F4,
    sibling slope 4 len 1 LEFT.  Phi2 = Phi'^2-2x*Phi'-8, E2=6.
 P3 (2,1,5)/Q3 n=10: inner (2,1,u2=5) side [1,5] (T-s)^2, sibling
    slope 3 len 1 LEFT.  Phi2 = Phi'^2-9sx, E2=10.
 P5 (2,1,6)/Q3 n=12: ONE side [0,6] slope 5/2, MIXED residual
    (T+1)^2(T-1): repeated class key Phi'^2-18x, simple class key
    Phi'^2-9x.  Partial via the mixed side; empirical-tie family.
 P6 (2,1,7)/Q2 n=14: inner side [0,4] LEFTMOST, sibling slope 7/3
    len 3 RIGHT -> (6,1).  Phi2 = Phi'^2-4x; shallow-flank c_g.

PREREGISTERED PREDICTIONS (sealed before the first full run):
 P-1 parse gate: every member's level-1 hull + side residual digits
   = the family target (partial side, pure/mixed as designed).
 P-2 HEADLINE: every gated member DECIDED, sigma = PARI route 1
   exactly (route 2 on a subsample); PE2P-0 reproduces the witness.
 P-3 tie: mu2* = 2 = mu2 on every pure-side member; on P5, mu2* = 2
   at the (T+1)-class and 1 at the (T-1)-class (empirical tie; the
   mixed-side tie stays BOXED -- GENTOW4-BOX-1).
 P-4 c_g + floors: >T2 part spans [0, mu2*]; every hull slope there
   > T2 and every later side <= T2; block pins p_j - c_g clear the
   GENTOW-1(c) floors (mu2*-j)E2 + 1; c_g odd on >= 1 member.
 P-5 field-floor separator (per factor per prime, PARI nodev):
   class rows m*val(Phi2) > E2*pr.e, degrees summing to D2*mu2*;
   non-class rows = E2*pr.e on steeper/same flanks (P1/P2/P3/P5),
   < E2*pr.e on P6 (shallow); class rows m*val(Phi')= u2*pr.e.
 P-6 windows: decided reads invariant under 2 random p^N lifts
   (N = 14) on 3 members/family.
 P-7 refine: constructed double-root members (P1: (T+1)^2 at
   lam=11; P3: (T-s)^2 at lam=11) re-read at Phi2 - s*n2hat(lam):
   event pins die (both >T2 pins strictly above the lam-node),
   re-read decides, PARI-exact.
TEETH (all must fire):
 T-1 FULLREAD: the T(b)'(iii) monic reader (dev length mu2,
   quotient must be [1]) REFUSES every member.
 T-2 NOCG: mutant RAM test on p0 (f-level) parity instead of
   p0 - c_g: flips the RAM decision on every c_g-odd one-side
   member; every flip is PARI-killed (mutant sigma != PARI).
 T-3 SIBDROP: tower-class-only sigma != PARI on every member.
 T-4 WITHHOLD: psi2 withheld -> UNDETERMINED, no sigma emitted.
 T-5 WRONGKEY: P5 members read with the simple class's key in the
   repeated slot give mu2* != 2 (1 or the HE6R1-3 peel): the
   wrong-key block datum is wrong on every probe (label-keying is
   load-bearing).
 T-6 NOTWIST: dropping the eta2-cocycle correction (coh()) flips
   INERT/SPLIT on eta2 != 1 members (P5); every flip PARI-killed
   -- the S4-normalizer coherence is machine-load-bearing at
   partial sides (>= 3 flips required).

SMOKE DISCLOSURE (pre-seal, honest): the PE2P-0 mechanism was
hand-driven during composition (S1/S5 of the note: pins (28,16,5),
c_g = 5, 2SIDED, PARI {(2,1),(4,1),(4,1)}); family constants
(normalizer monomials, residual digit targets) were sanity-checked
by the same hand computation.  A pre-seal wiring smoke of the
assembled runner (PE2P-0 + 2 members/family + P7/T5 wiring) is run
before the seal commit; its fixes are disclosed HERE, above the
seal, and no prediction is changed by them:
  SMOKE FIXES (4, disclosed; the full pre-seal smoke then ran
  GREEN 1,731 checks / 0 violations):
  (1) zero Phi2-development coefficients crashed the hull walk
      (pins[j] = None); skip empty pins.
  (2) f2 = 2 double-root refine needed the two-flavor K2-digit
      lift (GENTOW-2's lift(s; m)); wired for P2.
  (3) THE REAL FINDING: the raw-slot quadratic test is WRONG at
      eta2 != 1 -- FAM-P5 (psi2 = T+1 over F3, eta2 = 2) flipped
      INERT<->SPLIT vs PARI on 12 smoke rows.  Mechanism (derived,
      then verified): at e2 = 2 the wrap Phi'^2 = eta2*n(u2)*(1+..)
      makes cross-height residue comparisons pick up
      eta2^((b_slot - b_N)/2); the coherent digits are
      delta_j = r_j * eta2^((b_j - B_j)/2), N_j = n2(cg)n2(lam)^(2-j).
      Fix = coh(); the defect is now the T-6 NOTWIST tooth.  q = 2
      families and eta2 = 1 rows were structurally blind to it.
  (4) the T-5 cross-key probe can hit key | f (SIB = the simple
      class's key exactly); wired the HE6R1-3 peel branch
      (status PEEL, sigma (e1e2, f1f2) + sub-read).
Post-seal repairs, if any, are re-disclosed here with a fresh
commit before re-run, never silently edited.

Artifacts: gentow4_checks_output.txt (committed at commit 2).
Provenance: poly/gp helpers copied from gentow1_checks.py (sealed
982abe7) and trimmed; the reader itself is NEW (this unit).
"""

import hashlib
import random
import subprocess
import sys
import time

random.seed(20260809)
T0 = time.time()
NCHK = 0
NVIO = 0
LOG = []


def say(s):
    print(s)
    sys.stdout.flush()
    LOG.append(s)


def chk(fam, ok, msg):
    global NCHK, NVIO
    NCHK += 1
    if not ok:
        NVIO += 1
        say('VIOLATION [%s] %s' % (fam, msg))
    return ok


# ---------- integer dense polys (ascending), from gentow1 ----------
def pstrip(f):
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0) +
                   (g[i] if i < len(g) else 0) for i in range(n)])


def pmul(f, g):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                r[i + j] += a * b
    return pstrip(r)


def psca(c, f):
    return pstrip([c * x for x in f])


def ppow(g, k):
    r = [1]
    for _ in range(k):
        r = pmul(r, g)
    return r


def pdivmod_monic(f, g):
    f = list(f)
    dg = len(g) - 1
    assert g[-1] == 1
    q = [0] * max(1, len(f) - dg)
    for i in range(len(f) - 1, dg - 1, -1):
        c = f[i]
        if c:
            q[i - dg] += c
            for j, gj in enumerate(g):
                f[i - dg + j] -= c * gj
    return pstrip(q), pstrip(f[:dg])


def dev(f, key, mu):
    g, D = list(f), []
    for _ in range(mu):
        g, r = pdivmod_monic(g, key)
        D.append(r)
    return D, g


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def poly_str(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


def pmod(f, q):
    return pstrip([c % q for c in f])


def lower_hull(pts):
    """pts: list (j, h) ints, j increasing. Lower hull vertices."""
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # drop hull[-1] if pt makes it non-convex (above chord)
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


# ---------------- families ----------------------------------------
PA = [-2, 0, 1]                          # x^2 - 2 over Q2
PB = [-3, 0, 1]                          # x^2 - 3 over Q3


class Fam:
    """Partial-side tower family.  f1 = 1, h = 1, e1 = 2 throughout.
    inner = (e2, f2, u2, psi2_c, mu2); sides = level-1 target hull
    [(J, height), ...] left->right; sib = list of sibling classes
    (l, d_r, (e,f)); PHI2 = the inner class's composed key."""

    def __init__(self, name, p, PHI1, mu1, inner, hull, PHI2,
                 sib_sigma, sig_ram, sig_2s, sig_inert):
        self.name, self.p, self.PHI1, self.mu1 = name, p, PHI1, mu1
        self.e1, self.h, self.f1 = 2, 1, 1
        self.Dp = 2
        (self.e2, self.f2, self.u2, self.psi2_c, self.mu2) = inner
        self.hull = hull                 # target level-1 hull
        self.PHI2 = PHI2
        self.D2 = self.Dp * self.e2 * self.f2
        self.E2 = self.e2 * self.f2 * self.u2
        self.m = self.e1 * self.e2       # dv2 = m * v
        self.n = self.Dp * mu1
        self.M = self.n // self.D2       # dev length (partial: > mu2)
        self.sib_sigma = sib_sigma       # sigma of non-inner classes
        self.sig_ram, self.sig_2s = sig_ram, sig_2s
        self.sig_inert = sig_inert

    def nhat(self, mth):
        """level-1 dv-height-m monomial x^i p^a, i < e1."""
        i = mth % 2
        a = (mth - i) // 2
        return [0] * i + [self.p ** a]

    def n2hat(self, mth):
        """dv2-height-m ladder monomial p^a x^i Phi'^b, i<e1, b<e2."""
        for b in range(self.e2):
            r = mth - b * self.u2
            if r < 0:
                continue
            # solve m*a + e2*i = r with 0 <= i < e1 = 2, a >= 0
            for i in range(2):
                rr = r - i * self.e2 * self.h
                if rr >= 0 and rr % self.m == 0:
                    return pmul([0] * i + [self.p ** (rr // self.m)],
                                ppow(self.PHI1, b))
        return None

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def slots(self, C):
        B, g = dev(list(C), self.PHI1, self.e2 * self.f2)
        assert g == [] or g == [0], 'slot overflow'
        out = {}
        for b, rb in enumerate(B):
            for a, c in enumerate(rb):
                if c:
                    out[(a, b)] = c
        return out

    def pin(self, C, key_e2f2=None):
        """(min dv2-height, K2 residue (s,t)) of C, deg < D2."""
        sl = self.slots(C)
        if not sl:
            return None, None
        best = min(self.m * vp(c, self.p) + self.w(a, b)
                   for (a, b), c in sl.items())
        r = [0, 0]
        bmin = None
        for (a, b), c in sl.items():
            if self.m * vp(c, self.p) + self.w(a, b) == best:
                rc = (c // self.p ** vp(c, self.p)) % self.p
                fl = 1 if (self.f2 == 2 and b % 2 == 1) else 0
                r[fl] = (r[fl] + rc) % self.p
                bmin = b
        return best, (r[0], r[1], bmin)


def k2_add(F, x, y):
    return ((x[0] + y[0]) % F.p, (x[1] + y[1]) % F.p)


def k2_mul(F, x, y):
    if F.f2 == 1:
        return ((x[0] * y[0]) % F.p, 0)
    c0, c1 = F.psi2_c[0], F.psi2_c[1]    # psi2 = T^2+c1*T+c0
    s = x[0] * y[0] - c0 * x[1] * y[1]
    t = x[0] * y[1] + x[1] * y[0] - c1 * x[1] * y[1]
    return (s % F.p, t % F.p)


def k2_elems(F):
    if F.f2 == 1:
        return [(s, 0) for s in range(F.p)]
    return [(s, t) for s in range(F.p) for t in range(F.p)]


# level-1 parse gate ------------------------------------------------
def level1_read(F, f):
    """-> (hull, sides) or (None, err).  sides: list of
    (Jl, Jr, slope_num, slope_den, digits) with digits the residue
    list on the side lattice (low J -> high J, in F_p)."""
    if len(f) - 1 != F.n or f[-1] != 1:
        return None, 'degree/monic'
    A, g = dev(list(f), F.PHI1, F.mu1)
    if g != [1]:
        return None, 'not monic in Phi-dev'
    pins = []
    for J, c in enumerate(A):
        vals = [F.e1 * vp(cc, F.p) + i * F.h
                for i, cc in enumerate(c) if cc]
        if vals:
            pins.append((J, min(vals)))
    pins.append((F.mu1, 0))
    hull = lower_hull(pins)
    pmap = dict(pins)
    sides = []
    for k in range(len(hull) - 1):
        (J1, y1), (J2, y2) = hull[k], hull[k + 1]
        num, den = y1 - y2, J2 - J1
        from math import gcd
        gg = gcd(num, den)
        num, den = num // gg, den // gg
        digits = []
        for t in range((J2 - J1) // den + 1):
            J = J1 + t * den
            ht = y1 - t * num
            if J == F.mu1:
                digits.append(1)
                continue
            if pmap.get(J) != ht:
                digits.append(0)
                continue
            # residue of A_J at height ht against nhat(ht)
            dsum = 0
            for i, cc in enumerate(A[J]):
                if cc and F.e1 * vp(cc, F.p) + i * F.h == ht:
                    dsum += (cc // F.p ** vp(cc, F.p))
            digits.append(dsum % F.p)
        sides.append((J1, J2, num, den, digits))
    return hull, sides


# composed per-class read (THEOREM GENTOW-4.A + COR GENTOW-4.C) -----
def composed_read(F, f, key, mu2_exp, psi2_known=True, depth=0,
                  eta2=1):
    """Read the (kappa2, psi2)-class of f through `key`.
    -> dict(status, mu2s, cg, pins, label, sig) ; sig None if
    undecided.  mu2_exp: predicted mu2* (tie check happens outside).
    """
    if not psi2_known:
        return {'status': 'UNDETERMINED-nopsi'}
    C, g = dev(list(f), key, F.M + 1)
    assert g == [] or g == [0], 'dev overflow'
    pins, res = {}, {}
    for j, Cj in enumerate(C):
        if not Cj:
            continue
        b, r = F.pin(Cj)
        if b is None:                    # zero coefficient
            continue
        pins[j], res[j] = b, (r[0], r[1])
        resb = res.setdefault('b', {})
        resb[j] = r[2]
    if 0 not in pins:                    # key | f: HE6R1-3 peel
        q1, r0 = pdivmod_monic(list(f), key)
        assert r0 in ([], [0]), 'missing pin without divisibility'
        ee, ff = F.e1 * F.e2, F.f1 * F.f2
        out = {'status': 'PEEL', 'mu2s': 'PEEL', 'cg': None,
               'pins': pins, 'key': key, 'label': 'tPEEL'}
        if mu2_exp - 1 >= 1:
            sub = composed_read(F, q1, key, mu2_exp - 1, True,
                                depth, eta2)
            out['sig'] = ([(ee, ff)] + sub['sig']) \
                if sub.get('sig') else None
        else:
            out['sig'] = [(ee, ff)]
        return out
    pts = sorted(pins.items())
    hull = lower_hull([(j, h) for j, h in pts])
    # initial >T2 segment
    T2 = F.E2
    mu2s, cg = 0, None
    for k in range(len(hull) - 1):
        (j1, y1), (j2, y2) = hull[k], hull[k + 1]
        slope_num, slope_den = y1 - y2, j2 - j1
        if slope_num > T2 * slope_den:
            mu2s, cg = j2, y2
        else:
            break
    if mu2s == 0:
        return {'status': 'NOSIDE', 'pins': pins}
    out = {'status': 'OK', 'mu2s': mu2s, 'cg': cg, 'pins': pins,
           'hull': hull, 'key': key}
    if mu2s == 1:
        out['label'] = 'tSIMPLE'
        out['sig'] = [(F.e1 * F.e2, F.f1 * F.f2)]
        return out
    if mu2s != 2:
        out['label'] = 'tDEEP'
        out['sig'] = None
        return out
    # trichotomy on [0, 2] (translation/scale-invariant form)
    p0, p2 = pins[0], cg
    p1 = pins.get(1)
    vertex1 = any(v == (1, p1) for v in hull) if p1 is not None \
        else False
    ee, ff = F.e1 * F.e2, F.f1 * F.f2
    if vertex1:
        out['label'] = 't2SIDED'
        out['sig'] = [(ee, ff), (ee, ff)]
        return out
    if (p0 - p2) % 2 == 1:
        out['label'] = 'tRAM'
        out['sig'] = [(2 * ee, ff)]
        return out
    lam = (p0 - p2) // 2

    def coh(j, height):
        """coherent digit: raw slot residue times the S4-cocycle
        unit eta2^((b_slot - b_N)/2), N_j = n2(cg) n2(lam)^(2-j)
        (LEMMA GENTOW-4.1(c)'s normalizer coherence; trivial at
        eta2 = 1 and at q = 2; f2 = 2 keeps eta2 symbolic)."""
        if pins.get(j) != height:
            return (0, 0)
        rj = res[j]
        if F.f2 == 2 or eta2 % F.p == 1:
            return rj
        bj = res['b'][j]
        Bj = (cg % 2) + (2 - j) * (lam % 2)
        assert (bj - Bj) % 2 == 0, 'odd b-gap at equal heights'
        u = pow(eta2, ((bj - Bj) // 2) % (F.p - 1), F.p)
        return ((rj[0] * u) % F.p, (rj[1] * u) % F.p)

    # residual r2*T^2 + r1*T + r0 (gamma_g-scaled; root tests OK)
    r2 = coh(2, cg)
    r1 = coh(1, p2 + lam) if p1 is not None else (0, 0)
    r0 = coh(0, p2 + 2 * lam)
    roots = [z for z in k2_elems(F)
             if k2_add(F, k2_add(F, k2_mul(F, r2, k2_mul(F, z, z)),
                                 k2_mul(F, r1, z)), r0) == (0, 0)]
    if len(roots) == 0:
        out['label'] = 'tINERT'
        out['sig'] = [(ee, 2 * ff)]
        return out
    if len(roots) == 2:
        out['label'] = 'tSPLIT'
        out['sig'] = [(ee, ff), (ee, ff)]
        return out
    # double root: alpha-refine at the composed key (S3(v) last row)
    if depth >= 3:
        out['label'] = 'tDBL-deep'
        out['sig'] = None
        return out
    s = roots[0]
    # roots of R^f = roots of R^fS (gamma_g scales, roots fixed):
    # s IS the block double root.  The event sits at BLOCK dv2-height
    # lam (the block rides the same dv2-ladder; only PINS translate),
    # so the refine lift sits at absolute height lam.
    if F.f2 == 1:
        w = psca(s[0], F.n2hat(lam))
    else:
        # two-flavor K2-digit lift (GENTOW-2's lift(s; m)), e2 = 1:
        # flavor 0 at (a, b=0), flavor 1 at (a', b=1), heights
        # 2v + a (+3b) = lam
        a = lam % 2
        w = psca(s[0] * F.p ** ((lam - a) // 2), [0] * a + [1])
        if s[1]:
            ap = (lam - 3) % 2
            w = padd(w, pmul(psca(s[1] * F.p ** ((lam - 3 - ap) // 2),
                                  [0] * ap + [1]), F.PHI1))
    key2 = padd(key, psca(-1, w))
    out2 = composed_read(F, f, key2, mu2_exp, True, depth + 1,
                         eta2)
    out['label'] = 'tDBL->' + out2.get('label', out2['status'])
    out['sig'] = out2.get('sig')
    out['refined'] = out2
    return out


# ---------------- the five families --------------------------------
F1 = Fam('FAM-P1', 2, PA, 5, (2, 1, 5, [1, 1], 2),
         [(0, 13), (1, 10), (5, 0)],
         padd(pmul(PA, PA), [0, -4]),
         [(2, 1)], [(8, 1)], [(4, 1), (4, 1)], [(4, 2)])
F2 = Fam('FAM-P2', 2, PA, 5, (1, 2, 3, [1, 1, 1], 2),
         [(0, 16), (1, 12), (5, 0)],
         padd(padd(pmul(PA, PA), pmul([0, -2], PA)), [-8]),
         [(2, 1)], [(4, 2)], [(2, 2), (2, 2)], [(2, 4)])
F3 = Fam('FAM-P3', 3, PB, 5, (2, 1, 5, [-1, 1], 2),   # psi2 = T-1
         [(0, 13), (1, 10), (5, 0)],
         padd(pmul(PB, PB), [0, -9]),
         [(2, 1)], [(8, 1)], [(4, 1), (4, 1)], [(4, 2)])
F5 = Fam('FAM-P5', 3, PB, 6, (2, 1, 5, [-2, 1], 2),   # psi2 = T+1
         [(0, 15), (6, 0)],
         padd(pmul(PB, PB), [0, -18]),
         [(4, 1)], [(8, 1)], [(4, 1), (4, 1)], [(4, 2)])
F5KEYSIMPLE = padd(pmul(PB, PB), [0, -9])             # T-1 class
F6 = Fam('FAM-P6', 2, PA, 7, (2, 1, 5, [1, 1], 2),
         [(0, 17), (4, 7), (7, 0)],
         padd(pmul(PA, PA), [0, -4]),
         [(6, 1)], [(8, 1)], [(4, 1), (4, 1)], [(4, 2)])
FAMS = [F1, F2, F3, F5, F6]
# inner-side spec per family: (Jl, Jr, num, den, digit pattern)
INNER = {'FAM-P1': (1, 5, 5, 2, [1, 0, 1]),
         'FAM-P2': (1, 5, 3, 1, [1, 0, 1, 0, 1]),
         'FAM-P3': (1, 5, 5, 2, [1, 1, 1]),
         'FAM-P5': (0, 6, 5, 2, [2, 2, 1, 1]),
         'FAM-P6': (0, 4, 5, 2, [1, 0, 1])}
SIBSIDE = {'FAM-P1': (0, 1, 3, 1), 'FAM-P2': (0, 1, 4, 1),
           'FAM-P3': (0, 1, 3, 1), 'FAM-P5': None,
           'FAM-P6': (4, 7, 7, 3)}


# ---------------- member constructions ------------------------------
def build_l1(F, Adict):
    f = ppow(F.PHI1, F.mu1)
    for J, A in Adict.items():
        f = padd(f, pmul(A, ppow(F.PHI1, J)))
    return f


def r1_members(F, k):
    """random level-1-digit members (non-product route)."""
    out = []
    ch = random.choice
    for _ in range(k):
        if F.name == 'FAM-P1':
            A = {0: padd(psca(ch([1, 3]), [0, 64]),
                         ch([[0], [128], [0, 256]])),
                 1: padd(psca(ch([1, 3]), [32]), ch([[0], [0, 64]])),
                 2: ch([[0], [16], [0, 16], [0, 32]]),
                 3: ch([[0], [8], [16], [0, 8]]),
                 4: ch([[0], [0, 2], [4], [8]])}
        elif F.name == 'FAM-P2':
            A = {0: psca(ch([1, 3]), [256]),
                 1: padd(psca(ch([1, 3]), [64]), ch([[0], [0, 128]])),
                 2: ch([[0], [32], [0, 64]]),
                 3: padd(psca(ch([1, 3]), [8]), ch([[0], [16], [0, 16]])),
                 4: ch([[0], [4], [0, 4], [8]])}
        elif F.name == 'FAM-P3':
            A = {0: padd(psca(ch([1, 2]), [0, 729]), ch([[0], [2187]])),
                 1: psca(ch([1, 4]), [243]),
                 2: ch([[0], [81], [0, 81]]),
                 3: psca(ch([1, 4]), [0, 9]),
                 4: ch([[0], [9], [0, 3]])}
        elif F.name == 'FAM-P5':
            A = {0: psca(ch([2, 5]), [0, 2187]),
                 1: ch([[0], [0, 729], [2187]]),
                 2: psca(ch([2, 5]), [243]),
                 3: ch([[0], [81]]),
                 4: psca(ch([1, 4]), [0, 9]),
                 5: ch([[0], [0, 3], [9]])}
        else:                            # FAM-P6
            A = {0: psca(ch([1, 3]), [0, 256]),
                 1: ch([[0], [0, 128]]),
                 2: ch([[0], [0, 64], [128]]),
                 3: ch([[0], [32]]),
                 4: psca(ch([1, 3]), [0, 8]),
                 5: ch([[0], [0, 4], [8]]),
                 6: ch([[0], [0, 2], [4]])}
        out.append(build_l1(F, A))
    return out


def tow_block(F, label):
    """steered full-side deg-2*D2 tower factor at the family key."""
    p, K = F.p, F.PHI2
    n2 = F.n2hat
    if label == 'RAND':                  # P2 (E2 = 6): random
        f = pmul(K, K)                   # in-budget composed digits
        FLR = {(0, 0, 0): 7, (0, 1, 0): 6, (0, 0, 1): 5,
               (0, 1, 1): 5, (1, 0, 0): 4, (1, 1, 0): 3,
               (1, 0, 1): 2, (1, 1, 1): 2}
        for (j, a, b), fl in FLR.items():
            v = fl + random.choice([0, 0, 1, 2])
            c = random.choice([0, 1, 1, 1]) * p ** v
            if c:
                mono = pmul([0] * a + [c],
                            pmul(ppow(F.PHI1, b), ppow(K, j)))
                f = padd(f, mono)
        return f
    if label == 'RAM':
        return padd(pmul(K, K), psca(random.choice([1, p + 1]),
                                     n2(2 * F.E2 + 1)))
    if label == 'INERT':
        if p == 2:
            return padd(padd(pmul(K, K), pmul(n2(11), K)), n2(22))
        return padd(pmul(K, K), n2(22))              # T^2+1 over F3
    if label == '2SIDED':
        return padd(padd(pmul(K, K), pmul(n2(11), K)), n2(23))
    if label == 'SPLIT':                             # q = 3 only
        return padd(pmul(K, K), psca(2, n2(22)))     # T^2-1
    if label == 'DBL':
        if p == 2:
            return padd(pmul(K, K), n2(22))          # (T+1)^2
        return padd(padd(pmul(K, K), pmul(n2(11), K)),
                    psca(1, n2(22)))                 # (T-1)^2 over F3
    raise ValueError(label)


def sib_block(F):
    if F.name in ('FAM-P1',):
        return padd(F.PHI1, random.choice([[0, -2], [8, -2]]))
    if F.name == 'FAM-P2':
        return padd(F.PHI1, [-4 * random.choice([1, 3])])
    if F.name == 'FAM-P3':
        return padd(F.PHI1, psca(-random.choice([1, 2]), [0, 3]))
    if F.name == 'FAM-P5':
        return padd(pmul(F.PHI1, F.PHI1),
                    psca(-random.choice([1, 4]), [0, 9]))
    return padd(ppow(F.PHI1, 3),
                psca(-random.choice([1, 3]), [0, 8]))  # FAM-P6


def r2_members(F, labels, per):
    out = []
    for lab in labels:
        for i in range(per):
            f = pmul(tow_block(F, lab), sib_block(F))
            if i % 2 == 1:               # perturbation: break the
                f = padd(f, [0, F.p ** 11])   # literal product
            out.append(f)
    return out


# ---------------- gp bridge ----------------------------------------
GP_HDR = r"""
default(parisizemax, 4000000000);
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
nodev6(f, p, P2, P1) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [dec[j].e, dec[j].f, dec[j].e * dec[j].f,
                      nfeltval(nf, Mod(P2, g), dec[j]),
                      nfeltval(nf, Mod(x, g), dec[j]),
                      nfeltval(nf, Mod(P1, g), dec[j])]))));
  Vec(out)
}
"""


def run_gp(lines):
    src = GP_HDR + '\n' + '\n'.join(lines) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True,
                         timeout=3600)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-300:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    return res


def sig_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    s = s.replace('+oo', '1000000000')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1])
                  for i in range(0, len(nums), 2))


def tup_parse(s, k):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    s = s.replace('+oo', '1000000000')
    nums = [int(t) for t in s.split()]
    return [nums[i:i + k] for i in range(0, len(nums), k)]


# ---------------- residual factorization over F_p (deg <= 4) -------
def res_factor(p, digs):
    """digs: residual coeffs low->high in F_p.  ->
    (roots as {s: mult}, leftover poly) with leftover root-free."""
    f = [d % p for d in digs]
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    roots = {}
    for s in range(p):
        while True:
            if sum(c * s ** i for i, c in enumerate(f)) % p != 0:
                break
            # synthetic division by (T - s)
            q2 = [0] * (len(f) - 1)
            carry = f[-1]
            for i in range(len(f) - 2, -1, -1):
                q2[i] = carry % p
                carry = (f[i] + carry * s) % p
            f = q2
            roots[s] = roots.get(s, 0) + 1
            if len(f) == 1:
                break
        if len(f) == 1:
            break
    return roots, f


# ---------------- the full per-member pipeline ----------------------
def read_member(F, f, withhold=False):
    """THEOREM GENTOW-4.A reader.  -> dict with status, sigma,
    per-class data.  Never consults family sigma menus."""
    hull, sides = level1_read(F, f)
    if hull is None:
        return {'status': 'GATE-' + sides}
    out = {'status': 'OK', 'hull': hull, 'classes': [],
           'sigma': [], 'tower': []}
    for (J1, J2, num, den, digits) in sides:
        if digits[0] % F.p == 0:
            return {'status': 'GATE-left-endpoint-zero'}
        if num <= F.Dp * F.h * den:
            return {'status': 'GATE-floor'}    # slope <= D'h
        roots, left = res_factor(F.p, digits)
        # leftover must be 1 or the P2 quartic (T^2+T+1)^2 pattern
        # or an irreducible quadratic (simple deg-2 factor)
        if len(left) == 5:
            if left != [1, 0, 1, 0, 1] or F.p != 2:
                return {'status': 'GATE-res-deg4-unrecognized'}
            if withhold:
                return {'status': 'UNDETERMINED-withheld'}
            r = composed_read(F, f, F.PHI2, 2)   # f2 = 2: symbolic
            out['classes'].append(('psi2=T2+T+1^2', r))
            out['tower'].append(r)
            if r.get('sig') is None:
                return {'status': 'UNDECIDED-tower', 'read': r}
            out['sigma'] += r['sig']
        elif len(left) == 3:
            # irreducible quadratic, simple (mult 1)
            out['sigma'].append((F.e1 * den, F.f1 * 2))
            out['classes'].append(('quad-simple', None))
        elif len(left) != 1:
            return {'status': 'GATE-res-unrecognized'}
        for s, m in sorted(roots.items()):
            if m == 1:
                out['sigma'].append((F.e1 * den, F.f1 * 1))
                out['classes'].append(('T-%d simple' % s, None))
            elif m == 2 and den * 1 >= 2:
                if withhold:
                    return {'status': 'UNDETERMINED-withheld'}
                key = padd(ppow(F.PHI1, den),
                           psca(-s, [0] * (num % 2) +
                                [F.p ** ((num - (num % 2)) // 2)]))
                r = composed_read(F, f, key, 2, eta2=s)
                out['classes'].append(('T-%d^2' % s, r))
                out['tower'].append(r)
                if r.get('sig') is None:
                    return {'status': 'UNDECIDED-tower', 'read': r}
                out['sigma'] += r['sig']
            else:
                return {'status': 'GATE-class-shape (s=%d,m=%d,den=%d)'
                        % (s, m, den)}
    out['sigma'] = sorted(out['sigma'])
    return out


# ---------------- battery ------------------------------------------
GP_JOBS, GP_META = [], {}


def q_sig(tag, F, f, route2=False):
    GP_JOBS.append('print("%s ", sig1(%s, %d))'
                   % (tag, poly_str(f), F.p))
    if route2:
        GP_JOBS.append('print("%s.r2 ", sig2(%s, %d))'
                       % (tag, poly_str(f), F.p))
    GP_JOBS.append('print("%s.d ", poldisc(%s) != 0)'
                   % (tag, poly_str(f)))


def q_node(tag, F, f, key):
    GP_JOBS.append('print("%s.nv ", nodev6(%s, %d, %s, %s))'
                   % (tag, poly_str(f), F.p, poly_str(key),
                      poly_str(F.PHI1)))


ROWS = []          # (tag, F, f, read, mutant_sig, key_used)
NOTWIST = {}       # tag -> cocycle-mutant sigma (T-6)


def process(F, members, kind):
    for idx, f in enumerate(members):
        tag = '%s.%s%d' % (F.name, kind, idx)
        rd = read_member(F, f)
        if rd['status'].startswith('GATE'):
            chk(F.name, False, '%s parse gate: %s' % (tag,
                                                      rd['status']))
            continue
        chk(F.name, rd['status'] == 'OK',
            '%s status %s' % (tag, rd['status']))
        if rd['status'] != 'OK':
            continue
        # P-1: hull matches the family target
        chk(F.name, rd['hull'] == F.hull,
            '%s hull %s != %s' % (tag, rd['hull'], F.hull))
        # P-3 + P-4 per tower class
        for r in rd['tower']:
            chk(F.name, r['mu2s'] == 2 or r['mu2s'] == 'PEEL',
                '%s mu2* = %s != 2' % (tag, r['mu2s']))
            if r['mu2s'] == 'PEEL':
                continue
            cg, pins = r['cg'], r['pins']
            for j in range(2):
                pj = pins.get(j)
                need = (2 - j) * F.E2 + 1
                chk(F.name, pj is None or pj - cg >= need,
                    '%s floor j=%d: %s - %d < %d'
                    % (tag, j, pj, cg, need))
        # T-1: the full-side monic reader refuses
        _, qq = dev(list(f), F.PHI2, 2)
        chk(F.name, qq != [1], '%s FULLREAD accepted a partial member'
            % tag)
        # T-2 mutant: parity on p0 instead of p0 - cg (one-side only)
        mut = None
        r0 = rd['tower'][0]
        if r0['label'] in ('tRAM', 'tINERT', 'tSPLIT') or \
                r0['label'].startswith('tDBL'):
            p0, cg = r0['pins'][0], r0['cg']
            if p0 % 2 == 1 and (p0 - cg) % 2 == 0:
                # mutant wrongly reads RAM
                base = list(rd['sigma'])
                for x in r0['sig']:
                    base.remove(x)
                mut = sorted(base + [(2 * F.e1 * F.e2,
                                      F.f1 * F.f2)])
            elif p0 % 2 == 0 and (p0 - cg) % 2 == 1:
                base = list(rd['sigma'])
                for x in r0['sig']:
                    base.remove(x)
                # mutant sees even p0: reads residual at integer
                # slope; commonest wrong verdict = non-RAM; emit
                # INERT as the representative wrong sigma
                mut = sorted(base + [(F.e1 * F.e2, 2 * F.f1 * F.f2)])
        ROWS.append((tag, F, f, rd, mut))
        q_sig(tag, F, f, route2=(idx % 8 == 0))
        q_node(tag, F, f, rd['tower'][0]['key'])


def main():
    say('GENTOW-4 battery, %s' % time.strftime('%Y-%m-%d %H:%M:%S'))
    say('runner md5: %s' % hashlib.md5(
        open(__file__, 'rb').read()).hexdigest())
    # members
    PE2P0 = padd(padd(padd(ppow(PA, 5), psca(4, ppow(PA, 4))),
                      psca(32, PA)), [0, 64])
    for F in FAMS:
        m_r1 = r1_members(F, 12)
        if F.name == 'FAM-P2':
            labels, per = ['RAND'], 12
        elif F.p == 2:
            labels, per = ['RAM', 'INERT', '2SIDED', 'DBL'], 3
        else:
            labels, per = ['RAM', 'INERT', '2SIDED', 'SPLIT',
                           'DBL'], 2
        m_r2 = r2_members(F, labels, per)
        if F.name == 'FAM-P1':
            m_r1 = [PE2P0] + m_r1
        process(F, m_r1, 'r1m')
        process(F, m_r2, 'r2m')
        say('%s: %d members queued' % (F.name, len(m_r1) + len(m_r2)))

    # T-4 WITHHOLD + T-5 WRONGKEY + P-6 windows on stored rows
    nwith, nwrong, nwin = 0, 0, 0
    ncgodd = 0
    for (tag, F, f, rd, mut) in ROWS:
        if rd['tower'] and rd['tower'][0]['cg'] % 2 == 1:
            ncgodd += 1
        if nwith < 10:
            r = read_member(F, f, withhold=True)
            chk(F.name, r['status'].startswith('UNDETERMINED'),
                '%s withhold leaked: %s' % (tag, r['status']))
            nwith += 1
        if F.name == 'FAM-P5':
            r = composed_read(F, f, F5KEYSIMPLE, 2, eta2=1)
            chk(F.name, r.get('mu2s') in (1, 'PEEL'),
                '%s WRONGKEY probe: mu2* = %s (want != 2)'
                % (tag, r.get('mu2s')))
            # S3(iv) consistency: simple class through its own key
            # ((4,1) as tSIMPLE, or as the HE6R1-3 peel when the
            # class factor IS the key: deg class = D2)
            ok41 = (r.get('mu2s') == 1 and r.get('sig') == [(4, 1)]) \
                or r.get('mu2s') == 'PEEL'
            chk(F.name, ok41,
                '%s simple-class read %s != (4,1)-content'
                % (tag, r.get('sig')))
            nwrong += 1
            # T-6 NOTWIST: drop the eta2-cocycle correction
            r0t = rd['tower'][0]
            if r0t['label'] in ('tINERT', 'tSPLIT'):
                rno = composed_read(F, f, r0t['key'], 2, eta2=1)
                if rno.get('sig') is not None and \
                        rno['label'] != r0t['label']:
                    base = list(rd['sigma'])
                    for xx in r0t['sig']:
                        base.remove(xx)
                    NOTWIST[tag] = sorted(base + rno['sig'])
        if nwin < 15 and tag[-1] in '0369:':
            for t in range(2):
                lift = padd(f, psca(F.p ** 14, [random.randint(0, 3)
                            for _ in range(F.n)]))
                rl = read_member(F, lift)
                chk(F.name, rl['status'] == 'OK' and
                    rl['sigma'] == rd['sigma'] and
                    [r['label'] for r in rl['tower']] ==
                    [r['label'] for r in rd['tower']],
                    '%s window lift changed the read' % tag)
            nwin += 1
    chk('ALL', ncgodd >= 1, 'P-4: no c_g-odd member found')
    say('c_g odd on %d rows; withhold %d; wrongkey %d; windows %d'
        % (ncgodd, nwith, nwrong, nwin))

    # PARI
    say('running gp (%d jobs)...' % len(GP_JOBS))
    res = run_gp(GP_JOBS)
    nmut = 0
    for (tag, F, f, rd, mut) in ROWS:
        if tag + '.d' in res:
            chk(F.name, res[tag + '.d'] == '1', '%s disc = 0' % tag)
        want = sorted(tuple(x) for x in rd['sigma'])
        got = sig_parse(res.get(tag, '')) if tag in res else None
        chk(F.name, got == want,
            '%s sigma %s != PARI %s' % (tag, want, got))
        if tag == 'FAM-P1.r1m0':
            chk(F.name, got == [(2, 1), (4, 1), (4, 1)],
                'PE2P-0 witness sigma changed: %s' % got)
        if tag + '.r2' in res:
            chk(F.name, sig_parse(res[tag + '.r2']) == want,
                '%s route-2 sigma mismatch' % tag)
        # T-3 SIBDROP: tower-only sigma must differ from PARI
        towsig = sorted(sum((r['sig'] for r in rd['tower']), []))
        chk(F.name, towsig != got,
            '%s SIBDROP: tower-only sigma equals PARI' % tag)
        # T-6 NOTWIST kills
        if tag in NOTWIST and NOTWIST[tag] != want:
            chk(F.name, NOTWIST[tag] != got,
                '%s NOTWIST mutant sigma agreed with PARI' % tag)
        # T-2 NOCG kills
        if mut is not None and mut != want:
            nmut += 1
            chk(F.name, sorted(mut) != got,
                '%s NOCG mutant sigma agreed with PARI' % tag)
        # P-5 field floor via nodev6 rows [e, f, ef, vP2, vx, vP1]
        if tag + '.nv' in res:
            rows = tup_parse(res[tag + '.nv'], 6)
            clsdeg = 0
            for (e_, f_, ef_, v2_, vx_, v1_) in rows:
                dv2q = F.m * v2_            # compare vs E2 * e_
                if dv2q > F.E2 * e_:
                    clsdeg += ef_
                    chk(F.name, F.m * v1_ == F.u2 * e_,
                        '%s class row vPhi1 %d*%d != %d*%d'
                        % (tag, F.m, v1_, F.u2, e_))
                    chk(F.name, F.e1 * vx_ == F.h * e_,
                        '%s class row vx' % tag)
                else:
                    if F.name == 'FAM-P6':
                        chk(F.name, dv2q < F.E2 * e_,
                            '%s shallow sib at E2' % tag)
                    else:
                        chk(F.name, dv2q == F.E2 * e_,
                            '%s companion row dv2(Phi2) %d != E2 %d '
                            '(e=%d)' % (tag, dv2q, F.E2 * e_, e_))
            # class degrees sum to D2 * mu2* -- ONLY when the family
            # key equals the class key actually read (P3/P5 keys are
            # digit-derived; nodev used F.PHI2) -- restrict to exact
            chk(F.name, clsdeg == F.D2 * 2,
                '%s class degree sum %d != %d'
                % (tag, clsdeg, F.D2 * 2))
    chk('ALL', nmut >= 5, 'T-2: only %d NOCG flips (want >= 5)' % nmut)
    say('NOCG flips PARI-killed: %d' % nmut)
    ntw = len([t for t in NOTWIST])
    chk('ALL', ntw >= 3,
        'T-6: only %d NOTWIST flips (want >= 3)' % ntw)
    say('NOTWIST (eta2-cocycle) flips: %d' % ntw)

    say('')
    say('TOTAL: %d checks, %d violations, %.1f s'
        % (NCHK, NVIO, time.time() - T0))
    say('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(LOG) + '\n')


if __name__ == '__main__':
    main()
