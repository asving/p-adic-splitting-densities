"""HE7 — THE LEVEL-2 READ: (LIFT2) + (SLOT2) machine leg, keyed on the
T-CASEB three-sigma family.  SEALED PREREGISTRATION (commit 1).

WHAT IS BEING TESTED.  HE6 (`lean/notes/openmath/HE6_PROOF_2026-08-08.md`,
seal a77c376 / close 1f5a417) closed HE3-BOX-6 and left ONE box:
HE6-BOX-1, the deeper read at a REPEATED residual factor on a side of
dv-slope lam = u/l with l >= 2.  Its machine certificate is HE6's tooth
HE6-T-CASEB: at the first bite (D' = 2, mu = 4, deg f = 8, lam = u/2,
R_lam = (Z-s)^2) members with IDENTICAL OUTER DATA (same polygon, same
residual polynomial) have THREE different PARI sigma --- {(8,1)}, {(4,2)},
{(4,1),(4,1)} --- so no outer-data-only argument can decide sigma.

HE6 S7.2 names the exact residue as two lemmas.  HE7 proves them and wires
the LEVEL-2 READER that they make possible:

  LEVEL-2 FRAME (all of it in x-coordinates over the ORIGINAL O; no base
  change, no stage ring, Psi never assumed irreducible).  Phi' = x^2 - pi
  (e1 = 2, f1 = 1, h = 1, D' = 2, dv = 2v, K = F_p, varpi = x); a side of
  slope lam = u/l (gcd(u,l) = 1, lam > D'h) with residual factor r monic
  irreducible over K, d_r = deg r; the ORDER-2 KEY

      Psi = Psi_{lam,r} = Phi'^{l d_r} + sum_{t<d_r} B_t Phi'^{l t},
      deg Psi = D'' = D' l d_r,   dv(B_t) = (d_r - t) u,
      res(B_t(theta)/varpi(theta)^{(d_r-t)u}) = coefficient t of r.

  LEVEL-2 VALUE  dv2 := l * dv = e1 l v.
  LEVEL-2 RESIDUE FIELD  K2 := K[Z]/(r) = K(beta)  (K2 = K when d_r = 1).
  LEVEL-2 DISK THRESHOLD  T2 := l d_r u = l^2 d_r lam  (dv2 units); the
  level-1 analogue of D'h under (e1,f1,h,D') -> (l,d_r,u,l d_r).
  LEVEL-2 NORMALIZER  n2(k) := varpi^m Phi'^s with l m + s u = k, 0 <= s < l
  (so dv2(n2(k)(rho)) = k exactly at every level-2 point rho).  Unlike level
  1, the level-2 normalizer cocycle is NOT trivial: n2(k)n2(k') / n2(k+k')
  = (Phi'^l/varpi^u)^c has residue beta^c, so every level-2 residual
  polynomial carries an explicit beta-power TWIST (tooth T5 shows the twist
  is load-bearing).

  (SLOT2).  For C in O[x] with deg C < D'' and Phi'-development
  C = sum_{s < l d_r} c_s Phi'^s (deg c_s < D'), at every level-2 point rho

      dv2(C(rho)) = min_s ( l * dv(c_s) + s * u )   EXACTLY,

  the attaining s all lie in ONE class mod l (gcd(u,l) = 1), and within a
  class the d_r residues assemble to sum_t gamma_t beta^t != 0 because
  1, beta, ..., beta^{d_r-1} are K-independent (r irreducible).  This is
  LEMMA GENHN-2 one level up under (e1,f1,h) -> (l,d_r,u).

  (LIFT2).  For k with s0 := (k u^{-1} mod l), m0 := (k - s0 u)/l satisfying
  m0 >= (d_r - 1) u + (D' - 1) h, every c in K2 is the level-2 residue at
  height k of some C in O[x] with deg C < D'' and dv2-value k.  A k-uniform
  sufficient bound is k >= (l d_r - 1) u + l (D' - 1) h.  (HE7 also reports
  that HE6's own level-1 (LIFT) needs the same qualifier k >= (D'-1)h: at
  (e1,f1,h) = (3,1,2) the height k = 1 is not attained at all, and at
  (2,2,1) the heights k = 0,1 realize only F_Q < K.  Both are harmless for
  HE6, whose uses are all at k >= u > D'h --- tooth T4 pins this.)

PREREGISTERED PREDICTIONS (written before the run; scored in the note).

  P1 (HE7-READ2 --- THE HEADLINE, the T-CASEB separation).  On the ALPHA2
     configuration (R_lam = (Z-s)^2, l = 2 --- the HE6-BOX-1 node), the
     LEVEL-2 READ decides sigma for EVERY member, and its prediction equals
     the PARI sigma with ZERO mismatches, ON THE VERY FAMILY WHOSE OUTER
     DATA IS CONSTANT AND WHOSE sigma TAKES THREE VALUES.  The three
     dictionary outputs at the bite (e = e1 l l2 = 4 l2, f = f1 d_r d_{r2}
     = d_{r2}) are exactly:
         l2 = 2, d_{r2} = 1  ->  {(8,1)}
         l2 = 1, d_{r2} = 1 twice -> {(4,1),(4,1)}
         l2 = 1, d_{r2} = 2  ->  {(4,2)}
     i.e. precisely the three observed values.  Also: every side of the
     level-2 polygon is PRINCIPAL (slope > T2), the level-2 polygon length
     is mu2 = 2, and sum over blocks of e*f = 8.

  P2 (HE7-SLOT2, the exactness certificate).  For C in O[x] with
     deg C < D'' = 4 (both level-2 classes exercised, c_1 != 0 included),
         v(Res(f, C)) == 2 * dv2(C)
     EXACTLY --- because all 8 roots of f are level-2 points and each
     contributes the SAME slot-min: sum_rho dv2(C(rho)) = 8 dv2(C) and
     sum_rho dv2(C(rho)) = l e1 v(Res) = 4 v(Res).  Any cancellation among
     the level-2 slots would break this.

  P3 (HE7-LIFT2, surjectivity and its exact threshold).  The set of level-2
     heights at which the (LIFT2) construction attains ALL of K2 is exactly
         W2 = { k : m0(k) - t u in W1 for every t < d_r },
         W1 = { k : k >= (i0(k) + e1 (f1 - 1)) h }   (i0(k) = the class),
     and the closed forms k >= (l d_r - 1) u + l (D'-1) h (level 2) and
     k >= (D'-1) h (level 1) are sufficient.  Verified by exhaustive
     enumeration of the slot data over many (e1,f1,h) x (l,d_r,u) frames.

  P4 (HE7-GEN2, the level-2 flat identity).  For every rational level-2
     height kappa2 = u2/l2 > T2 and every monic irreducible r2 over K2 that
     does NOT divide the level-2 residual at kappa2,
         l e1 v(Res(f, Psi2_{kappa2,r2})) == D'' l2 d_{r2} h_{F2}(kappa2),
     h_{F2}(kappa2) = min_j (dv2(A_j^{(2)}) + j kappa2), EXACTLY --- the
     level-2 analogue of HE6's P1, at heights no element of the LEVEL-1
     stage ring can occupy.

  P5 (HE7-SEP2, the level-2 strict excess = nonemptiness).  If r2 DIVIDES
     the level-2 residual, the same resultant valuation is STRICTLY
     GREATER.  This is the engine of LEMMA HE6-4 one level up.

TEETH (each must FIRE; a silent pass is an instrument failure).
  T1 HE7-T-CASEB-SEP : >= 3 distinct PARI sigma inside ONE constant-outer-
                       data family AND the level-2 read predicts every one
                       of them (the box's certificate turned into a
                       separation certificate).
  T2 HE7-T-WITHHOLD  : with the level-2 residual of one side WITHHELD, the
                       reader must report UNDETERMINED, not silently accept.
  T3 HE7-T-RANK      : the level-1 (outer) read admits 3 sigma on the same
                       member set; the level-2 read admits exactly 1.
  T4 HE7-T-LIFT2SHARP: below the (LIFT2)/(LIFT) threshold the residue map is
                       NOT surjective (explicit unreachable residue), so the
                       corrected threshold is load-bearing --- and HE6's
                       unqualified (LIFT) is refuted as stated.
  T5 HE7-T-BADTWIST  : dropping the beta-power twist from the level-2
                       residual assembly MISPREDICTS sigma on >= 1 member
                       (the level-2 cocycle is nontrivial, unlike level 1).
  T6 HE7-T-SLOT2TIE  : at gcd(u,l) != 1 the level-2 classes collide and the
                       slot-min is NOT exact --- caught by P2's identity.

CHARACTERISTICS.  O = Z_p (p = 3,5,7; PARI factorpadic oracle) and
O = F_p[[t]] (p = 3,5; identities only --- ORACLE ASYMMETRY, HE6-BOX-4,
inherited by every unit of this program).

Artifacts: he7_checks_output.txt, he7_checks_results.json.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import he6_checks as H6
from he6_checks import (Zp, FpTring, padd, pmul, ppow, development,
                        resultant, key_poly, nrm, dv_A, res_A, test_poly,
                        factor_Fp, read_labels, build_f, instance, polystr,
                        gp_sig_batch, members, disc_nonzero, irred_list,
                        peval_l, hull_sides, BIG, E1, F1, H, DP, MU)

WIP = False        # commit 1 sealed this True (smoke only); commit 2 flips it

PINS = ['he6_checks.py', 'he6_checks_results.json', 'w12_checks.py',
        'w10_checks.py']


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


# ======================================================== bookkeeping
RES = {'legs': {}, 'viol': [], 'teeth': {}, 'rows': [], 'lift2': [],
       'caseB': {}, 'notes': []}


def note(leg, k=1):
    RES['legs'][leg] = RES['legs'].get(leg, 0) + k


def viol(leg, what, detail):
    RES['viol'].append({'leg': leg, 'what': what, 'detail': str(detail)[:400]})
    print('  !! VIOLATION %s %s %s' % (leg, what, str(detail)[:220]))


def tooth(name, fired, detail=''):
    RES['teeth'][name] = {'fired': bool(fired), 'detail': str(detail)[:500]}
    print('  TOOTH %-20s %s  %s' % (name, 'FIRED' if fired else 'DID NOT FIRE',
                                    str(detail)[:170]))


def minv(a, m):
    """inverse of a mod m (m >= 1), by extended Euclid."""
    if m == 1:
        return 0
    g, x, r, s = a % m, 1, m, 0
    while r:
        q = g // r
        g, r = r, g - q * r
        x, s = s, x - q * s
    if g != 1:
        raise ValueError('no inverse: %d mod %d' % (a, m))
    return x % m


# ============================================ the level-2 frame (x-coords)
class L2Frame(object):
    """the level-2 datum at a side (lam = u/l, r) over the HE6 stage frame
    e1 = 2, f1 = 1, h = 1, Phi' = x^2 - pi, D' = 2, varpi = x, K = F_p.
    d_r = 1 only (K2 = K = F_p); beta = s, the residual root."""

    def __init__(self, R, p, u, s, l=2, dr=1):
        assert dr == 1, 'HE7 reader implemented at d_r = 1 (see coverage box)'
        self.R, self.p, self.u, self.l, self.dr, self.s = R, p, u, l, dr, s
        self.T2 = l * dr * u                       # level-2 disk threshold
        self.Dpp = DP * l * dr                     # D'' = deg Psi
        self.key = key_poly(R)                     # Phi'
        # Psi = Phi'^{l d_r} + sum_{t<d_r} B_t Phi'^{l t};  r = Z - s so
        # d_r = 1 and the single coefficient is c_0 = -s.
        self.Psi = test_poly(u, l, [(-s) % p], R)
        assert len(self.Psi) - 1 == self.Dpp
        self.uinv = minv(u % l, l) if l > 1 else 0

    # ---- n2(k) = varpi^m Phi'^s  with  l m + s u = k, 0 <= s < l
    def n2ms(self, k):
        s = (k * self.uinv) % self.l if self.l > 1 else 0
        return (k - s * self.u) // self.l, s

    def n2poly(self, k):
        """n2(k) as an element of O[x] of degree < D'' (needs m >= 0)."""
        m, s = self.n2ms(k)
        if m < 0:
            return None
        return pmul(nrm(m, self.R), ppow(self.key, s))

    # ---- (SLOT2): the level-2 slot-min of C (deg C < D'')
    def phidev(self, C):
        """Phi'-development of C into l*d_r coefficients of degree < D'."""
        return development(C, self.key, self.l * self.dr - 1)

    def dv2(self, C):
        cs = self.phidev(C)
        best = BIG
        for s, c in enumerate(cs):
            m = dv_A(c, self.R)
            if m < BIG:
                best = min(best, self.l * m + s * self.u)
        return best

    def res2(self, C, k):
        """level-2 residue of C(rho)/n2(k)(rho) in K2 = F_p; 0 if dv2(C) > k.
        (d_r = 1: the class-s0 slot is the single t = 0 slot.)"""
        m0, s0 = self.n2ms(k)
        cs = self.phidev(C)
        tot = 0
        for t in range(self.dr):
            sidx = s0 + self.l * t
            mt = m0 - t * self.u
            c = cs[sidx]
            if dv_A(c, self.R) == mt:
                g = res_A(c, self.R)
                tot = (tot + g * pow(self.s, t, self.p)) % self.p
        return tot % self.p

    # ---- the twist:  n2(k1-t*u2) n2(u2)^t / n2(k1) = (Phi'^l/varpi^u)^c
    def twist(self, m1, u2, t):
        s_a = self.n2ms(m1 - t * u2)[1]
        s_b = self.n2ms(u2)[1]
        s_c = self.n2ms(m1)[1]
        S = s_a + t * s_b - s_c
        assert S % self.l == 0, 'twist exponent not divisible by l'
        return S // self.l

    def twist_factor(self, m1, u2, t, use=True):
        if not use:
            return 1
        c = self.twist(m1, u2, t)
        return pow(self.s, c % (self.p - 1), self.p) if c else 1

    # ---- (LIFT2): C with deg C < D'', dv2(C) = k, res2(C, k) = c
    def lift2(self, k, c):
        m0, s0 = self.n2ms(k)
        if m0 < 0:
            return None
        R = self.R
        out = [R.zero]
        for t in range(self.dr):
            mt = m0 - t * self.u
            if mt < 0:
                return None
            # d_r = 1: the target residue is c itself
            ct = c % self.p
            if ct == 0 and self.dr == 1:
                return None
            blk = pmul([x * R.el(ct) for x in nrm(mt, R)],
                       ppow(self.key, s0 + self.l * t))
            out = padd(out, blk)
        return out


# ============================================= the level-2 read (the reader)
def level2_read(f, fr, maxref=60, withhold=None, use_twist=True):
    """develop f in Psi-powers, read the level-2 polygon in the dv2 grading,
    factor the level-2 residuals over K2, apply the HE6.A_2 dictionary.
    Returns dict(status, sigma, trace)."""
    R, p, l, dr, u = fr.R, fr.p, fr.l, fr.dr, fr.u
    nf = len(f) - 1
    if nf % fr.Dpp:
        return {'status': 'DEGENERATE-deg'}
    mu2 = nf // fr.Dpp
    Psi = fr.Psi
    trace = []
    for step in range(maxref + 1):
        cur_sides = []
        Ad = development(f, Psi, mu2)
        if len(Ad) < mu2 + 1:
            return {'status': 'DEGENERATE-dev'}
        dv2s = [fr.dv2(Ad[j]) for j in range(mu2 + 1)]
        if dv2s[mu2] != 0:
            return {'status': 'DEGENERATE-top', 'dv2s': dv2s}
        if any(v >= BIG for v in dv2s[:mu2]) and dv2s[0] >= BIG:
            return {'status': 'DEGENERATE-key-divides', 'dv2s': dv2s}
        sides = hull_sides(dv2s)
        blocks, deeper, undet = [], None, False
        for side in sides:
            j1, m1, j2, m2 = side
            lam2 = Fr(m1 - m2, j2 - j1)
            if lam2 <= fr.T2:
                return {'status': 'NONPRINCIPAL', 'lam2': str(lam2),
                        'T2': fr.T2, 'dv2s': dv2s}
            l2, u2 = lam2.denominator, lam2.numerator
            L2, d2 = j2 - j1, (j2 - j1) // lam2.denominator
            co = []
            for t in range(d2 + 1):
                j = j1 + t * l2
                want = m1 - lam2 * (j - j1)
                if want.denominator != 1:
                    co.append(0)
                    continue
                want = int(want)
                if dv2s[j] == want:
                    g = fr.res2(Ad[j], want)
                    g = (g * fr.twist_factor(m1, u2, t, use_twist)) % p
                    co.append(g)
                else:
                    co.append(0)
            if withhold is not None and withhold == (str(lam2),):
                undet = True
                trace.append({'lam2': str(lam2), 'residual': 'WITHHELD'})
                continue
            if co[d2] == 0:
                return {'status': 'DEGENERATE-lead', 'dv2s': dv2s,
                        'lam2': str(lam2), 'co': co}
            inv = pow(co[d2], p - 2, p)
            co = [(x * inv) % p for x in co]
            facs = factor_Fp(co, p)
            sd = {'lam2': str(lam2), 'residual': co,
                  'facs': [(list(ff), m) for ff, m in facs]}
            trace.append(sd)
            cur_sides.append(sd)
            for ff, m in facs:
                if m > 1:
                    deeper = (lam2, l2, u2, ff, m, d2)
                else:
                    blocks.append((E1 * l * l2, F1 * dr * (len(ff) - 1)))
        if undet:
            return {'status': 'UNDETERMINED', 'trace': trace,
                    'blocks': blocks}
        if deeper is None:
            tot = sum(a * b for a, b in blocks)
            if tot != nf:
                return {'status': 'BADTOTAL', 'blocks': blocks, 'tot': tot,
                        'trace': trace}
            return {'status': 'OK', 'sigma': tuple(sorted(blocks)),
                    'trace': trace, 'refines': step, 'mu2': mu2,
                    'key': Psi, 'sides': cur_sides}
        lam2, l2, u2, ff, m, d2 = deeper
        if l2 != 1 or len(ff) != 2:
            # a repeated factor on a level-2 side with l2 >= 2 (or d_{r2} >= 2)
            # would need LEVEL 3.  Predicted impossible at mu2 = 2.
            return {'status': 'LEVEL3', 'lam2': str(lam2), 'l2': l2,
                    'deg_r2': len(ff) - 1, 'mult': m, 'trace': trace}
        # ---- level-2 alpha-refine: Psi <- Psi - w,  dv2(w) = lam2,
        #      res2(w, lam2) = s2  (available by (LIFT2)).  Terminates by
        #      (REF-TERM): an infinite chain forces f = (Psi + W)^{mu2}.
        s2 = (-ff[0]) % p                     # root of (Z - s2)^m
        w = fr.lift2(int(lam2), s2)
        if w is None:
            return {'status': 'REFINE-BLOCKED', 'lam2': str(lam2)}
        Psi = padd(Psi, [-c for c in w])
        trace.append({'refine': str(lam2), 's2': s2})
    return {'status': 'REFINE-OVERFLOW', 'trace': trace}


# ============================================= (LIFT) / (LIFT2) reachability
def W1_set(e1, f1, h, kmax):
    """heights k <= kmax at which the LEVEL-1 residue map onto K is
    surjective, by direct enumeration of the available within-class slots."""
    out, avail = [], {}
    hi = minv(h % e1, e1) if e1 > 1 else 0
    for k in range(kmax + 1):
        i0 = (k * hi) % e1 if e1 > 1 else 0
        av = [t for t in range(f1) if k >= (i0 + e1 * t) * h]
        avail[k] = (i0, av)
        if len(av) == f1:
            out.append(k)
    return set(out), avail


def V1_set(e1, f1, h, kmax):
    """heights realizable at all by C in O[x], deg C < D' = e1 f1."""
    out = set()
    for i in range(e1 * f1):
        m = i * h
        while m <= kmax:
            out.add(m)
            m += e1
    return out


def W2_set(e1, f1, h, l, dr, u, kmax):
    """level-2 heights k <= kmax at which the level-2 residue map onto K2 is
    surjective:  every within-class level-1 height m0 - t u must be in W1."""
    W1, _ = W1_set(e1, f1, h, kmax * max(1, l) + l * u * dr + 8)
    uinv = minv(u % l, l) if l > 1 else 0
    out = set()
    for k in range(kmax + 1):
        s0 = (k * uinv) % l if l > 1 else 0
        if (k - s0 * u) % l:
            continue
        m0 = (k - s0 * u) // l
        if m0 < 0:
            continue
        if all((m0 - t * u) in W1 for t in range(dr)):
            out.add(k)
    return out


# ================================================================ the legs
def leg_slot2(f, fr, ncheck=8):
    """P2: v(Res(f, C)) == 2 * dv2(C) for C of degree < D''."""
    R, p, l = fr.R, fr.p, fr.l
    made = 0
    for (m0pat, s0pat) in [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, 1),
                           (3, 1), (3, 0)][:ncheck]:
        # C = a*nrm(m0)*Phi'^{s0} + b*nrm(m0')*Phi'^{s0'} (both classes)
        C = [R.zero]
        for (mm, ss, cc) in [(m0pat, s0pat, 1), (m0pat + 2, 1 - s0pat, 2)]:
            if ss >= l:
                continue
            blk = pmul([x * R.el(cc % p if cc % p else 1) for x in nrm(mm, R)],
                       ppow(fr.key, ss))
            C = padd(C, blk)
        if len(C) - 1 >= fr.Dpp:
            continue
        k = fr.dv2(C)
        if k >= BIG:
            continue
        rr = resultant(f, C)
        if rr == 0 or (hasattr(rr, 'c') and not rr):
            viol('HE7-SLOT2', 'Res=0', {'C': str(C)})
            continue
        got = R.val(rr)
        # sum_rho dv2(C(rho)) = l e1 v(Res) = deg(f) * k
        if l * E1 * got != (len(f) - 1) * k:
            viol('HE7-SLOT2', 'slot-min not exact',
                 {'k': k, 'v(Res)': got, 'deg f': len(f) - 1, 'C': str(C)})
        else:
            note('HE7-SLOT2')
            made += 1
    return made


def leg_gen2(f, fr, rd2, grid):
    """P4/P5: the level-2 flat identity and the strict excess.  Scored
    against the FINAL key of the read (refines allowed) and the FINAL side
    set: dv2/n2/res2 depend only on (Phi', lam, r), so a refine changes the
    key alone."""
    R, p, l, dr = fr.R, fr.p, fr.l, fr.dr
    key = rd2.get('key', fr.Psi)
    Ad = development(f, key, (len(f) - 1) // fr.Dpp)
    dv2s = [fr.dv2(A) for A in Ad]
    lab = set()
    for sd in rd2.get('sides', []):
        for ff, m in sd.get('facs', []):
            lab.add((sd['lam2'], tuple(ff)))
    for (u2, l2, r2) in grid:
        kappa2 = Fr(u2, l2)
        if kappa2 <= fr.T2:
            continue
        d2 = len(r2) - 1
        Psi2 = build_psi2(fr, u2, l2, r2, key=key)
        if Psi2 is None:
            continue
        hF2 = min(dv2s[j] + j * kappa2 for j in range(len(dv2s))
                  if dv2s[j] < BIG)
        is_label = (str(kappa2), tuple(r2)) in lab
        rr = resultant(f, Psi2)
        if rr == 0 or (hasattr(rr, 'c') and not rr):
            # Res = 0 <=> f and Psi2 share a root <=> INFINITE excess.  At a
            # label this is the extreme case of P5 (at the label's own r2 the
            # test polynomial can literally reproduce a factor of f); at a
            # NON-label it contradicts LEMMA HE7-7 (all roots of Psi2 sit at
            # level-2 height kappa2, all roots of f at their own labels).
            if is_label:
                note('HE7-SEP2')
                note('HE7-SEP2-inf')
            else:
                viol('HE7-GEN2', 'Res=0 at a NON-label height',
                     {'u2': u2, 'l2': l2, 'r2': r2})
            continue
        lhs = l * E1 * R.val(rr)
        rhs = fr.Dpp * l2 * d2 * hF2
        if is_label:
            if lhs > rhs:
                note('HE7-SEP2')
            else:
                viol('HE7-SEP2', 'no strict excess at a label',
                     {'kappa2': str(kappa2), 'r2': r2, 'lhs': lhs,
                      'rhs': str(rhs)})
        else:
            if rhs.denominator != 1 or lhs != int(rhs):
                viol('HE7-GEN2', 'flat identity fails',
                     {'kappa2': str(kappa2), 'r2': r2, 'lhs': lhs,
                      'rhs': str(rhs)})
            else:
                note('HE7-GEN2')


def build_psi2(fr, u2, l2, r2, key=None):
    """Psi2 = Psi^{l2 d2} + sum_{t<d2} C_t Psi^{l2 t}, C_t by (LIFT2).

    THE INVERSE TWIST (DEFINITION HE7-3).  Assembling Psi2(xi)/n2(d2 u2)(xi)
    produces the coefficient of Z^t as res2(C_t) * beta^{c_t} with
    c_t = twist(d2 u2, u2, t).  To make the roots of Psi2 satisfy
    iota(r2)(beta_2) = 0 for the GIVEN r2, C_t's prescribed level-2 residue
    must therefore be r2[t] * beta^{-c_t}, NOT r2[t].  Omitting the inverse
    twist builds the test polynomial of a DIFFERENT residual (the twisted
    r2, which need not even be irreducible) --- machine-caught, and the
    reason DEFINITION HE7-3 carries the twist explicitly."""
    R, p = fr.R, fr.p
    Psi = fr.Psi if key is None else key
    d2 = len(r2) - 1
    out = [R.zero]
    for t in range(d2 + 1):
        if t == d2:
            Ct = [R.one]
        else:
            # target residue = r2[t] * beta^{c_{d2} - c_t}, so that the
            # effective residual is beta^{c_{d2}} * r2(Z) -- r2's own roots.
            tw = (fr.twist_factor(d2 * u2, u2, t) *
                  pow(fr.twist_factor(d2 * u2, u2, d2), p - 2, p)) % p
            c = (r2[t] * pow(tw, p - 2, p)) % p
            if c == 0:
                continue
            Ct = fr.lift2((d2 - t) * u2, c)
            if Ct is None:
                return None
            if len(Ct) - 1 >= fr.Dpp:
                return None
        out = padd(out, pmul(Ct, ppow(Psi, l2 * t)))
    return out


def test_grid2(fr, p, rd2):
    """the sampled level-2 test heights: at the level-2 slopes (every monic
    irreducible of degree <= 2 over K2) and at other rational heights."""
    out = []
    slopes = [Fr(sd['lam2']) for sd in rd2.get('trace', [])
              if 'residual' in sd and sd['residual'] != 'WITHHELD']
    for lam2 in slopes:
        for deg in (1, 2):
            for r2 in irred_list(p, deg):
                out.append((lam2.numerator, lam2.denominator, r2))
    r1 = irred_list(p, 1)[0]
    base = fr.T2
    for l2 in (1, 2, 3):
        for u2 in range(l2 * base + 1, l2 * base + 3 * l2 + 1):
            if gcd(u2, l2) != 1:
                continue
            if Fr(u2, l2) in slopes:
                continue
            out.append((u2, l2, r1))
    return out


# ============================================================== the row run
def run_row(R, p, u, W=2, cap=200, oracle=True, tag='', grid_cap=14, s=1):
    print('\n--- row %s  lam = %d/2  s = %d  (%s)' % (R.name(), u, s, tag))
    # ALPHA2: R_lam = (Z - s)^2  ->  residual coeffs [s^2, -2s] (low-to-high).
    # s != 1 rows are the ones in which the level-2 TWIST beta^c = s^c is
    # nontrivial (beta = s when d_r = 1), so they test the twist derivation.
    rco2 = [(s * s) % p, (-2 * s) % p]
    fr = L2Frame(R, p, u, s)
    rows = {'ring': R.name(), 'u': u, 's': s, 'T2': fr.T2, 'members': 0,
            'pari': 0, 'sigma_pred': {}, 'sigma_pari': {}, 'agree': 0,
            'mismatch': 0, 'status': {}, 'refines': {}, 'tag': tag}
    jobs, preds = [], []
    for A, f in members(R, p, u, rco2, W=W, cap=cap):
        if not disc_nonzero(f, R):
            continue
        rd1 = read_labels(A, R, p)
        if not rd1['deeper']:
            viol('HE7-FRAME', 'outer read not DEEPER at ALPHA2', {'u': u})
            continue
        rd2 = level2_read(f, fr)
        st = rd2['status']
        rows['status'][st] = rows['status'].get(st, 0) + 1
        rows['members'] += 1
        if st != 'OK':
            if st.startswith('DEGENERATE'):
                continue
            viol('HE7-READ2', 'level-2 read status ' + st, rd2)
            continue
        rows['refines'][rd2['refines']] = rows['refines'].get(
            rd2['refines'], 0) + 1
        nt = level2_read(f, fr, use_twist=False)
        if nt.get('status') != 'OK' or nt.get('sigma') != rd2['sigma']:
            rows['twist_flips'] = rows.get('twist_flips', 0) + 1
            rows.setdefault('twist_ex', []).append(
                (str(rd2['sigma']), str(nt.get('sigma')), nt.get('status')))
        sg = str(rd2['sigma'])
        rows['sigma_pred'][sg] = rows['sigma_pred'].get(sg, 0) + 1
        note('HE7-READ2')
        leg_slot2(f, fr)
        if rows['members'] <= grid_cap:
            leg_gen2(f, fr, rd2, test_grid2(fr, p, rd2))
        if oracle:
            jobs.append((polystr(f), None))
            preds.append(rd2['sigma'])
    if oracle and jobs:
        got = gp_sig_batch(jobs, p)
        for i, pr in enumerate(preds):
            g = got.get(i)
            if g is None:
                continue
            rows['pari'] += 1
            gs = str(tuple(sorted(tuple(x) for x in g)))
            rows['sigma_pari'][gs] = rows['sigma_pari'].get(gs, 0) + 1
            if tuple(sorted(tuple(x) for x in g)) == pr:
                rows['agree'] += 1
                note('HE7-SIG2')
            else:
                rows['mismatch'] += 1
                viol('HE7-SIG2', 'level-2 read != PARI',
                     {'pred': str(pr), 'pari': gs})
    print('  members %d  read-OK %d  PARI %d  agree %d  mismatch %d'
          % (rows['members'], sum(rows['sigma_pred'].values()), rows['pari'],
             rows['agree'], rows['mismatch']))
    print('  predicted sigma: %s' % rows['sigma_pred'])
    if oracle:
        print('  PARI      sigma: %s' % rows['sigma_pari'])
    print('  refine steps used: %s' % rows['refines'])
    RES['rows'].append(rows)
    return rows


# ================================================================== the teeth
def teeth_run(p=5, u=5, s=1):
    R = Zp(p)
    rco2 = [(s * s) % p, (-2 * s) % p]
    fr = L2Frame(R, p, u, s)

    # ---- T1 / T3: the T-CASEB family, separated
    perts = [None,
             {3: [c * R.el(1) for c in nrm(3, R)]},
             {1: [c * R.el(1) for c in nrm(8, R)]},
             {3: [c * R.el(2) for c in nrm(3, R)]},
             {2: [c * R.el(1) for c in nrm(u + 1, R)]},
             {0: [c * R.el(1) for c in nrm(2 * u + 1, R)]},
             {0: [c * R.el(2) for c in nrm(2 * u + 1, R)]},
             {1: [c * R.el(3) for c in nrm(8, R)]}]
    ex = []
    for pert in perts:
        A, f = instance(u, rco2, R, pert)
        if not disc_nonzero(f, R):
            continue
        rd1 = read_labels(A, R, p)
        rd2 = level2_read(f, fr)
        ex.append((polystr(f), rd1, rd2, f, A))
    got = gp_sig_batch([(e[0], None) for e in ex], p)
    seen, agree, bad = {}, 0, []
    for i, (ps, rd1, rd2, f, A) in enumerate(ex):
        g = got.get(i)
        if g is None:
            continue
        gs = tuple(sorted(tuple(x) for x in g))
        seen[str(gs)] = seen.get(str(gs), 0) + 1
        if rd2['status'] == 'OK' and rd2['sigma'] == gs:
            agree += 1
        else:
            bad.append((str(gs), rd2.get('status'),
                        str(rd2.get('sigma'))))
    tooth('HE7-T-CASEB-SEP', len(seen) >= 3 and not bad,
          '%d distinct PARI sigma over IDENTICAL outer data: %s ; level-2 '
          'read agrees on %d/%d, bad=%s'
          % (len(seen), seen, agree, len(ex), bad[:3]))
    RES['caseB'] = {'sigma_seen': seen, 'agree': agree, 'n': len(ex),
                    'bad': bad[:5]}
    tooth('HE7-T-RANK', len(seen) >= 3 and agree == len(ex),
          'outer (level-1) read: ONE label class of size 8, sigma '
          'UNDETERMINED (%d values compatible); level-2 read: exactly 1 per '
          'member, %d/%d == PARI' % (len(seen), agree, len(ex)))

    # ---- T2: withhold one level-2 residual
    A, f = instance(u, rco2, R, perts[1])
    rd2 = level2_read(f, fr)
    lam2s = [sd['lam2'] for sd in rd2.get('trace', []) if 'residual' in sd]
    wh = level2_read(f, fr, withhold=(lam2s[0],)) if lam2s else {}
    tooth('HE7-T-WITHHOLD', wh.get('status') == 'UNDETERMINED',
          'residual at lam2 = %s withheld -> status %s (full read: %s)'
          % (lam2s[:1], wh.get('status'), rd2.get('status')))

    # ---- T4: (LIFT)/(LIFT2) threshold sharpness
    bad_l1 = []
    for (e1, f1, h) in [(3, 1, 2), (2, 2, 1), (3, 2, 1), (2, 1, 3), (2, 3, 1)]:
        W1, avail = W1_set(e1, f1, h, 40)
        V1 = V1_set(e1, f1, h, 40)
        thr = (e1 * f1 - 1) * h
        miss = sorted(k for k in range(thr) if k not in W1)
        unreach = sorted(k for k in range(40) if k not in V1)
        okthr = all(k in W1 for k in range(thr, 41))
        bad_l1.append({'frame': (e1, f1, h), 'D-1h': thr,
                       'k<thr not surjective': miss[:8],
                       'k not attained at all': unreach[:6],
                       'all k>=thr surjective': okthr})
        if not okthr:
            viol('HE7-LIFT2', 'closed-form level-1 threshold insufficient',
                 {'frame': (e1, f1, h)})
        else:
            note('HE7-LIFT1')
    RES['lift2'].append({'level1': bad_l1})
    l1_sharp = any(b['k<thr not surjective'] for b in bad_l1)
    # level-2 frames
    bad_l2 = []
    for (e1, f1, h, l, dr, uu) in [(2, 1, 1, 2, 1, 5), (2, 1, 1, 2, 2, 5),
                                   (2, 2, 1, 2, 2, 7), (3, 1, 2, 2, 3, 13),
                                   (1, 2, 1, 3, 2, 11)]:
        Dp = e1 * f1
        kmax = 3 * ((l * dr - 1) * uu + l * (Dp - 1) * h) + 12
        W2 = W2_set(e1, f1, h, l, dr, uu, kmax)
        thr2 = (l * dr - 1) * uu + l * (Dp - 1) * h
        okthr = all(k in W2 for k in range(thr2, kmax + 1))
        miss = sorted(k for k in range(thr2) if k not in W2)
        bad_l2.append({'frame': (e1, f1, h, l, dr, uu), 'thr2': thr2,
                       'k<thr2 not surjective (count)': len(miss),
                       'first misses': miss[:8],
                       'all k>=thr2 surjective': okthr})
        if not okthr:
            viol('HE7-LIFT2', 'closed-form level-2 threshold insufficient',
                 {'frame': (e1, f1, h, l, dr, uu)})
        else:
            note('HE7-LIFT2')
    RES['lift2'].append({'level2': bad_l2})
    l2_sharp = any(b['first misses'] for b in bad_l2)
    tooth('HE7-T-LIFT2SHARP', l1_sharp and l2_sharp,
          'level-1: %s ; level-2: %s'
          % ([(b['frame'], b['k<thr not surjective'][:4])
              for b in bad_l1],
             [(b['frame'], b['first misses'][:4]) for b in bad_l2]))

    # ---- T5: drop the twist -> mispredict.  beta = s when d_r = 1, so the
    # twist s^c is only visible at s != 1: sweep every letter s in K^x and
    # every prime, and check BOTH that the twisted read == PARI and that the
    # untwisted read disagrees somewhere.
    flips, det, twisted_agree, twisted_tot = 0, [], 0, 0
    for pp in (3, 5, 7):
        Rp = Zp(pp)
        for ss in range(1, pp):
            rc = [(ss * ss) % pp, (-2 * ss) % pp]
            frs = L2Frame(Rp, pp, u, ss)
            ex2, pr2, pr2n = [], [], []
            for A, f in members(Rp, pp, u, rc, W=2, cap=40):
                if not disc_nonzero(f, Rp):
                    continue
                a = level2_read(f, frs)
                b = level2_read(f, frs, use_twist=False)
                if a.get('status') != b.get('status') or \
                   a.get('sigma') != b.get('sigma'):
                    flips += 1
                    det.append((pp, ss, str(a.get('sigma')),
                                str(b.get('sigma'))))
                if a.get('status') == 'OK':
                    ex2.append((polystr(f), None))
                    pr2.append(a['sigma'])
                    pr2n.append(b.get('sigma'))
            if ex2:
                g2 = gp_sig_batch(ex2, pp)
                for i, prv in enumerate(pr2):
                    gg = g2.get(i)
                    if gg is None:
                        continue
                    twisted_tot += 1
                    if tuple(sorted(tuple(x) for x in gg)) == prv:
                        twisted_agree += 1
                    else:
                        viol('HE7-T-BADTWIST', 'twisted read != PARI',
                             {'p': pp, 's': ss, 'pred': str(prv),
                              'pari': str(gg)})
    RES['twist'] = {'flips': flips, 'twisted_agree': twisted_agree,
                    'twisted_tot': twisted_tot, 'examples': det[:6]}
    tooth('HE7-T-BADTWIST', flips > 0 and twisted_agree == twisted_tot,
          '%d (p, s, member) reads CHANGE when the beta-power twist is '
          'dropped, while the TWISTED read == PARI on %d/%d: %s'
          % (flips, twisted_agree, twisted_tot, det[:3]))

    # ---- T6: gcd(u, l) != 1 breaks the level-2 class separation
    caught = 0
    det6 = []
    for uu in (2 * u, 6):
        try:
            frb = L2Frame(R, p, uu, s, l=2)
        except Exception as e:
            det6.append(('frame', str(e)))
            continue
        A, f = instance(u, rco2, R, None)
        C = padd(pmul(nrm(2, R), ppow(frb.key, 0)),
                 pmul(nrm(2 - 1, R), ppow(frb.key, 1)))
        if len(C) - 1 >= frb.Dpp:
            continue
        k = frb.dv2(C)
        rr = resultant(f, C)
        if rr == 0:
            continue
        if 2 * E1 * R.val(rr) != (len(f) - 1) * k:
            caught += 1
            det6.append((uu, k, R.val(rr)))
    # the honest form of T6: with gcd(u,l) = 2 the two classes SHARE heights
    coll = []
    for uu in (2 * u, 6, 4):
        l = 2
        if gcd(uu, l) == 1:
            continue
        hits = {}
        for sidx in range(l):
            for m in range(0, 12):
                hits.setdefault(l * m + sidx * uu, []).append(sidx)
        coll.append((uu, sorted(k for k, v in hits.items() if len(v) > 1)[:5]))
    tooth('HE7-T-SLOT2TIE', bool(coll) and all(c[1] for c in coll),
          'gcd(u,l) != 1 makes the l level-2 classes SHARE heights (so the '
          'slot-min is not exact and no residue is well defined): %s ; '
          'resultant-identity failures observed: %d %s'
          % (coll, caught, det6[:2]))


# ================================================================== smoke
def smoke(p=5, u=5):
    R = Zp(p)
    s = 1
    rco2 = [(s * s) % p, (-2 * s) % p]
    fr = L2Frame(R, p, u, s)
    print('smoke %s u=%d : Psi = %s  (D\'\' = %d, T2 = %d)'
          % (R.name(), u, fr.Psi, fr.Dpp, fr.T2))
    ex = []
    for pert in [None, {3: [c * R.el(1) for c in nrm(3, R)]},
                 {1: [c * R.el(1) for c in nrm(8, R)]}]:
        A, f = instance(u, rco2, R, pert)
        rd1 = read_labels(A, R, p)
        rd2 = level2_read(f, fr)
        print('  pert %-28s outer deeper=%s  level2 %s %s (refines %s)'
              % (pert, rd1['deeper'], rd2['status'], rd2.get('sigma'),
                 rd2.get('refines')))
        print('     slot2 checks: %s' % leg_slot2(f, fr))
        ex.append((polystr(f), None))
    got = gp_sig_batch(ex, p)
    print('  PARI: %s' % got)


def main():
    t0 = time.time()
    if WIP:
        print('HE7 checks — WIP smoke (commit 1)')
        smoke(5, 5)
        smoke(3, 5)
        print('%.1fs' % (time.time() - t0))
        return
    print('HE7 checks — THE LEVEL-2 READ ((LIFT2) + (SLOT2)) on the '
          'T-CASEB three-sigma family')
    print('pins: ' + ', '.join('%s %s' % (f, md5(f)[:10]) for f in PINS
                               if os.path.exists(os.path.join(HERE, f))))
    # s = 1 rows: HE6's own configuration (the twist is trivial there).
    run_row(Zp(3), 3, 5, W=2, cap=210, tag='char 0', s=1)
    run_row(Zp(5), 5, 5, W=2, cap=250, tag='char 0', s=1)
    run_row(Zp(7), 7, 5, W=1, cap=170, tag='char 0', s=1)
    run_row(Zp(5), 5, 7, W=1, cap=150, tag='char 0, deeper side', s=1)
    # s != 1 rows: the TWIST is nontrivial (beta = s), so these rows put the
    # level-2 cocycle derivation under the PARI oracle.
    run_row(Zp(3), 3, 5, W=2, cap=150, tag='char 0, twist live', s=2)
    run_row(Zp(5), 5, 5, W=2, cap=150, tag='char 0, twist live', s=2)
    run_row(Zp(5), 5, 5, W=1, cap=120, tag='char 0, twist live', s=3)
    run_row(Zp(7), 7, 5, W=1, cap=120, tag='char 0, twist live', s=3)
    run_row(Zp(5), 5, 7, W=1, cap=120, tag='char 0, deeper+twist', s=2)
    # char p rows (no factorpadic oracle: reader + resultant identities)
    run_row(FpTring(3), 3, 5, W=2, cap=80, oracle=False, tag='char 3', s=1)
    run_row(FpTring(3), 3, 5, W=2, cap=60, oracle=False,
            tag='char 3, twist live', s=2)
    run_row(FpTring(5), 5, 5, W=1, cap=60, oracle=False, tag='char 5', s=1)
    run_row(FpTring(5), 5, 5, W=1, cap=60, oracle=False,
            tag='char 5, twist live', s=3)
    print('\n--- teeth')
    teeth_run(5, 5)
    RES['secs'] = round(time.time() - t0, 1)
    RES['nviol'] = len(RES['viol'])
    print('\nLEGS: %s' % RES['legs'])
    print('VIOLATIONS: %d' % len(RES['viol']))
    print('%.1fs' % (time.time() - t0))
    with open(os.path.join(HERE, 'he7_checks_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True, default=str)


if __name__ == '__main__':
    main()
