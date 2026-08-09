#!/usr/bin/env python3
"""GENHN r2 supp leg (F1 repair): LEMMA GENHN-T(b)' -- the corrected
tower-composition read (the Phi2-adic development of f ITSELF in the
composed slot basis) vs PARI, on the PE1 verifier's 4 refuted
instances (regression teeth) + fresh sweeps at TWO tower genres +
a 3-stage stretch.

CHARGE: GENHN passPE1 F1 refuted LEMMA GENHN-T(b)'s stage-algebra
inner read (division with Phi' = 0) at n = 8 tower leaves; the
corrected read develops f itself by the composed key Phi2 (division
in Z[x], no quotient), pins in the composed slot basis
{x^a Phi'^b} on the dv2 = e1e2*v ladder.  This runner is the FIRST
tower leaf-read coverage (the sealed battery had witness only,
disclosed at GENHN-BOX-3).

FAMILIES + PREREGISTERED PREDICTIONS (before first full run):
 SUPP-A0 (regression, the verifier's exact instances, fixed seeds):
   G in {Y^4+16Y+96, Y^4+16Y^3+32Y^2+96, Y^4+16Y^3+32Y^2+224},
   f = G(x^2-2), genre (2,1,4)->(2,1,2) at q=2, h=1, u2=5.
   P-A0.1: corrected pins (25,14)/(21,14)/(21,14), all tRAM,
     sigma {(8,1)}; PARI (both routes) = {(8,1)} on all 6 jobs
     (3 + 3 deep perturbations).
   P-A0.2: stage-shadow pins reproduce the PE1 hand values
     (21,14)/(28,14)/(30,14) with labels iRAM/iINERT/i2SIDED.
   TOOTH T-SHADOW: the stage-shadow sigma MISMATCHES PARI on the
     INERT and 2SIDED families (>= 1 each; PE1 showed 4).
   TOOTH T-LABEL: corrected pin != stage pin on the RAM family
     (25 vs 21 -- the count-law mispricing witness).
 SUPP-A1 (fresh sweep, genre (2,1,4)->(2,1,2)): u2 = 5 and u2 = 7
   families, swept g-coefficients on the tower-node locus + deep
   x-perturbations.  P-A1: every DECIDED corrected leaf matches
   PARI (route 1; route 2 on a subsample); UNDEC leaves reported
   as a diagnostic tail (conservative drain, not scored).
   Divergence tally stage-vs-corrected reported.
 SUPP-B (OTHER tower genre (2,1,4)->(1,2,2), first f2 = 2 tower):
   inner residual (T^2+T+1)^2 at kappa2 = 3, composed key
   Phi2 = Phi'^2 - 2x*Phi' - 8, composed (e,f) = (2,2), K2 = F4.
   P-B: every DECIDED corrected leaf matches PARI; dictionary
   {(4,2)} / {(2,2),(2,2)} / {(2,4)}.
 SUPP-C (3-stage stretch, n = 16): f = Phi3^2 + E1*Phi3 + E0 with
   Phi3 = Phi2^2 - 16*Phi' (u3 = 21), Phi2 = (x^2-2)^2 - 4x.
   P-C: constructed instances parse as 3-level chains and the
   corrected level-3 read matches PARI ({(16,1)} at odd pins;
   {(8,1),(8,1)} at the 2SIDED instance).  If a construction fails
   to parse it is DROPPED with disclosure (stretch leg).
VERDICT: GREEN iff 0 violations on scored checks AND both teeth
fire.  Written 2026-08-09 by the GENHN r2 repair unit; independent
of the sealed battery (no imports from it; sealed artifacts
untouched).
"""
import json
import random
import subprocess
import sys
import time

random.seed(20260809)
VIOL = []
NCHK = {}
OUT = []


def say(s):
    print(s)
    sys.stdout.flush()
    OUT.append(s)


def chk(fam, ok, msg):
    NCHK[fam] = NCHK.get(fam, 0) + 1
    if not ok:
        VIOL.append((fam, msg))
        say('  !! VIOLATION [%s] %s' % (fam, msg))


def v2(n):
    n = abs(n)
    assert n != 0
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


# ---------------- integer polynomials (lists, [c0, c1, ...]) -------
def pstrip(f):
    while f and f[-1] == 0:
        f = f[:-1]
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


def pdivmod_monic(f, g):
    """f, g int polys, g monic: f = q*g + r, deg r < deg g."""
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


PHI1 = [-2, 0, 1]                       # Phi' = x^2 - 2


def phi_dev(f, mu):
    """level-1 development: f = A_mu*Phi'^mu + ... + A_0."""
    A = []
    for _ in range(mu):
        f, r = pdivmod_monic(f, PHI1)
        A.append(r)
    A.append(f)
    return A                             # A[j] has deg <= 1


def dv_x(A):
    """dv = 2v of an x-poly at a root of Phi' (e1=2, f1=1, h=1):
    slot-min, EXACT by LEMMA GENHN-2."""
    cands = [2 * v2(c) + i for i, c in enumerate(A) if c]
    return min(cands) if cands else None


def level1_parse(f, mu, want_dvA0, want_absent, side_num, side_den):
    """check the tower-node grammar: monic, A_mu = 1, dv(A_0) exact,
    middle pins strictly above the side, residual multiplicity."""
    A = phi_dev(f, mu)
    if A[mu] != [1]:
        return None, 'A_mu != 1'
    dvs = [dv_x(a) for a in A[:mu]]
    if dvs[0] != want_dvA0:
        return None, 'dv(A0) = %s want %s' % (dvs[0], want_dvA0)
    for J in range(1, mu):
        need = side_num * (mu - J)      # side height * side_den
        if dvs[J] is not None and dvs[J] * side_den <= need \
                and (J in want_absent):
            return None, 'pin at J=%d not above side' % J
    return dvs, None


# --------- genre A: (2,1,4)->(2,1,2), inner e2=2 f2=1 --------------
def phi2_A(u2):
    """composed key Phi2 = Phi'^2 - n(u2), n(u2) = 2^((u2-1)/2) * x
    (dv-height u2 odd)."""
    base = pmul(PHI1, PHI1)
    n = [0, 2 ** ((u2 - 1) // 2)]
    return padd(base, [-c for c in n])


def comp_basis_A(C):
    """C deg <= 3 -> composed basis {1, x, Phi', xPhi'}:
    x^2 = Phi' + 2, x^3 = xPhi' + 2x."""
    C = list(C) + [0] * (4 - len(C))
    return {'1': C[0] + 2 * C[2], 'x': C[1] + 2 * C[3],
            'p': C[2], 'xp': C[3]}


def dv2_A(C, u2):
    """composed slot-min on the dv2 = 4v ladder; EXACT by
    GENHN-2' (classes 0/2/u2/u2+2 mod 4, all distinct, u2 odd)."""
    b = comp_basis_A(C)
    off = {'1': 0, 'x': 2, 'p': u2, 'xp': u2 + 2}
    cands = [4 * v2(c) + off[k] for k, c in b.items() if c]
    return min(cands) if cands else None


def read_A_true(f, u2):
    """corrected read: Phi2-development of f itself in Z[x]."""
    P2 = phi2_A(u2)
    q1, r1 = pdivmod_monic(f, P2)
    q2, r2 = pdivmod_monic(q1, P2)
    if q2 != [1]:
        return None
    u, w = dv2_A(r1, u2), dv2_A(r2, u2)
    return adjudicate_A(u, w)


def adjudicate_A(u, w):
    """mu2 = 2 dictionary at composed (e,f) = (4,1), K2 = F2, on the
    dv2-ladder.  u = dv2(C0), w = dv2(C1)."""
    if u is None:
        return (u, w, 'DRAIN', None)
    if w is None or u < 2 * w:
        if u % 2 == 1:
            return (u, w, 'tRAM', [(8, 1)])
        return (u, w, 'tEVEN', None)     # F2 square residual: undec
    if u == 2 * w:
        # residual T^2 + T + 1 over F2 (pin residues = 1): irreducible
        return (u, w, 'tINERT', [(4, 2)])
    return (u, w, 't2SIDED', [(4, 1), (4, 1)])


def read_A_stage(f, u2):
    """the REFUTED stage-algebra read (T(b) as sealed): level-1 dev,
    then R[Y]-division by the inner key with Phi' == 0 in R =
    O[x]/(Phi'); slots {1,x,Y,xY} at {0,2,u2,u2+2}."""
    A = phi_dev(f, 4)
    if A[4] != [1]:
        return None
    c = 2 ** ((u2 - 1) // 2)

    def rmul(a, b):                      # R = Z[x]/(x^2-2): (s, t)
        return (a[0] * b[0] + 2 * a[1] * b[1],
                a[0] * b[1] + a[1] * b[0])

    def to_r(p):
        p = list(p) + [0] * (2 - len(p))
        return (p[0], p[1])

    F = [to_r(a) for a in A[:4]] + [(1, 0)]
    K2 = [(0, -c), (0, 0), (1, 0)]       # Y^2 - c*x

    def rdiv(F):
        F = list(F)
        q = [(0, 0)] * max(1, len(F) - 2)
        for i in range(len(F) - 1, 1, -1):
            co = F[i]
            if co != (0, 0):
                q[i - 2] = (q[i - 2][0] + co[0], q[i - 2][1] + co[1])
                for j, gj in enumerate(K2):
                    m = rmul(co, gj)
                    F[i - 2 + j] = (F[i - 2 + j][0] - m[0],
                                    F[i - 2 + j][1] - m[1])
        return q, F[:2]

    q1, B0 = rdiv(F)
    q2, B1 = rdiv(q1)

    def dvB(B):
        cands = []
        for yi, rc in enumerate(B):
            for xi, cc in enumerate(rc):
                if cc:
                    cands.append(4 * v2(cc) + 2 * xi + u2 * yi)
        return min(cands) if cands else None
    u, w = dvB(B0), dvB(B1)
    lab = adjudicate_A(u, w)
    return (u, w, 'i' + lab[2][1:] if lab[2][0] == 't' else lab[2],
            lab[3])


# --------- genre B: (2,1,4)->(1,2,2), inner e2=1 f2=2, K2 = F4 -----
PHI2_B = padd(padd(pmul(PHI1, PHI1), pmul([0, -2], PHI1)), [-8])
# Phi2 = Phi'^2 - 2x*Phi' - 8  (canonical lift of psi2 = T^2+T+1 at
# kappa2 = 3: n(3) = 2x, n(6) = 8)


def f4_mul(a, b):
    """F4 = F2[eta2]/(eta2^2+eta2+1), elements (s, t) = s + t*eta2."""
    s = (a[0] & b[0]) ^ (a[1] & b[1])
    t = (a[0] & b[1]) ^ (a[1] & b[0]) ^ (a[1] & b[1])
    return (s, t)


def slots_B(C):
    """C deg <= 3 -> slots on dv2 = dv = 2v ladder: 1@0 (flavor 1),
    x@1 (1), Phi'@3 (eta2), xPhi'@4 (eta2).  Returns pin (min height)
    and its F4 residue (exact: 1/eta2 flavors F2-independent)."""
    C = list(C) + [0] * (4 - len(C))
    b = {'1': (C[0] + 2 * C[2], 0, (1, 0)),
         'x': (C[1] + 2 * C[3], 1, (1, 0)),
         'p': (C[2], 3, (0, 1)), 'xp': (C[3], 4, (0, 1))}
    best = None
    for k, (c, off, fl) in b.items():
        if c:
            d = 2 * v2(c) + off
            if best is None or d < best:
                best = d
    if best is None:
        return None, None
    r = (0, 0)
    for k, (c, off, fl) in b.items():
        if c and 2 * v2(c) + off == best:
            r = (r[0] ^ fl[0], r[1] ^ fl[1])
    return best, r


def read_B_true(f):
    """corrected read at the f2 = 2 tower genre."""
    q1, C0 = pdivmod_monic(f, PHI2_B)
    q2, C1 = pdivmod_monic(q1, PHI2_B)
    if q2 != [1]:
        return None
    u, ru = slots_B(C0)
    w, rw = slots_B(C1)
    return adjudicate_B(u, w, ru, rw)


def adjudicate_B(u, w, ru, rw):
    """mu2 = 2 dictionary at composed (e,f) = (2,2), K2 = F4,
    dv2 = 2v ladder."""
    if u is None:
        return (u, w, 'DRAIN', None)
    if w is None or u < 2 * w:
        if u % 2 == 1:
            return (u, w, 'tRAM', [(4, 2)])
        return (u, w, 'tEVEN', None)     # T^2 - r0: F4 square, undec
    if u == 2 * w:
        # residual T^2 + rw*T + ru over F4
        if rw == (0, 0):
            return (u, w, 'tDBL', None)
        roots = [z for z in [(0, 0), (1, 0), (0, 1), (1, 1)]
                 if (f4_mul(z, z)[0] ^ f4_mul(rw, z)[0] ^ ru[0],
                     f4_mul(z, z)[1] ^ f4_mul(rw, z)[1] ^ ru[1])
                 == (0, 0)]
        if not roots:
            return (u, w, 'tINERT', [(2, 4)])
        return (u, w, 'tSPLIT', [(2, 2), (2, 2)])
    return (u, w, 't2SIDED', [(2, 2), (2, 2)])


def read_B_stage(f):
    """stage-shadow read at genre B (R[Y] division, Phi' == 0)."""
    A = phi_dev(f, 4)
    if A[4] != [1]:
        return None

    def rmul(a, b):
        return (a[0] * b[0] + 2 * a[1] * b[1],
                a[0] * b[1] + a[1] * b[0])

    def to_r(p):
        p = list(p) + [0] * (2 - len(p))
        return (p[0], p[1])

    F = [to_r(a) for a in A[:4]] + [(1, 0)]
    K2 = [(-8, 0), (0, -2), (1, 0)]      # Y^2 - 2xY - 8

    def rdiv(F):
        F = list(F)
        q = [(0, 0)] * max(1, len(F) - 2)
        for i in range(len(F) - 1, 1, -1):
            co = F[i]
            if co != (0, 0):
                q[i - 2] = (q[i - 2][0] + co[0], q[i - 2][1] + co[1])
                for j, gj in enumerate(K2):
                    m = rmul(co, gj)
                    F[i - 2 + j] = (F[i - 2 + j][0] - m[0],
                                    F[i - 2 + j][1] - m[1])
        return q, F[:2]

    q1, B0 = rdiv(F)
    q2, B1 = rdiv(q1)

    def slotsR(B):
        cand = {}
        for yi, rc in enumerate(B):
            for xi, cc in enumerate(rc):
                if cc:
                    d = 2 * v2(cc) + xi + 3 * yi
                    fl = (1, 0) if yi == 0 else (0, 1)
                    cand.setdefault(d, []).append(fl)
        if not cand:
            return None, None
        best = min(cand)
        r = (0, 0)
        for fl in cand[best]:
            r = (r[0] ^ fl[0], r[1] ^ fl[1])
        return best, r
    u, ru = slotsR(B0)
    w, rw = slotsR(B1)
    lab = adjudicate_B(u, w, ru, rw)
    return lab


# --------------- 3-stage stretch (n = 16) --------------------------
PHI2_C = phi2_A(5)                       # (x^2-2)^2 - 4x
PHI3 = padd(pmul(PHI2_C, PHI2_C), pmul([-16], PHI1))
# Phi3 = Phi2^2 - 16*Phi'  (n2(21) = 16*Phi' at dv2 = 8*2+5 = 21)


def dv3_C(C):
    """slot-min on dv3 = 8v for deg <= 7 remainders in the composed
    basis {x^a Phi'^b Phi2^c}: heights 1@0 x@4 p@10 xp@14 P2@21
    xP2@25 pP2@31 xpP2@35 mod ... (u3 = 21 odd: all 8 distinct
    mod 8: 0,4,2,6,5,1,7,3)."""
    q, r0 = pdivmod_monic(list(C), PHI2_C)   # C = q*Phi2 + r0
    b0 = comp_basis_A(r0)
    b1 = comp_basis_A(q)                     # q deg <= 3
    off0 = {'1': 0, 'x': 4, 'p': 10, 'xp': 14}
    cands = [8 * v2(c) + off0[k] for k, c in b0.items() if c]
    cands += [8 * v2(c) + off0[k] + 21 for k, c in b1.items() if c]
    return min(cands) if cands else None


def read_C_true(f):
    q1, E0 = pdivmod_monic(f, PHI3)
    q2, E1 = pdivmod_monic(q1, PHI3)
    if q2 != [1]:
        return None
    u, w = dv3_C(E0), dv3_C(E1)
    if u is None:
        return (u, w, 'DRAIN', None)
    if w is None or u < 2 * w:
        if u % 2 == 1:
            return (u, w, 'tRAM', [(16, 1)])
        return (u, w, 'tEVEN', None)
    if u == 2 * w:
        return (u, w, 'tINERT', [(8, 2)])
    return (u, w, 't2SIDED', [(8, 1), (8, 1)])


# ---------------------------- PARI ---------------------------------
GP_PROG = r"""
sig1(f) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
        listput(out, [1, 1]),
        my(nf = nfinit([g, [2]]), dec = idealprimedec(nf, 2));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
ef2(g) = {
  my(nf = nfinit([g, [2]]), dec = idealprimedec(nf, 2));
  [dec[1].e, dec[1].f]
}
sig2(f) = {
  my(F = factorpadic(f, 2, 300));
  vecsort(vector(matsize(F)[1], i, ef2(liftall(F[i, 1]))))
}
"""


def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


def run_gp(jobs, route2_idx):
    lines = [GP_PROG]
    for i, f in enumerate(jobs):
        ps = polystr(f)
        lines.append('print("R %d ", poldisc(Pol(%s)) != 0, " ", '
                     'sig1(%s))' % (i, ps, ps))
        if i in route2_idx:
            lines.append('print("S %d ", sig2(%s))' % (i, ps))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=900)
    got, got2 = {}, {}
    for line in out.stdout.splitlines():
        if line.startswith('R '):
            parts = line[2:].split(' ', 2)
            sig = sorted(tuple(p) for p in json.loads(parts[2]))
            got[int(parts[0])] = (parts[1] == '1', sig)
        elif line.startswith('S '):
            parts = line[2:].split(' ', 1)
            got2[int(parts[0])] = sorted(
                tuple(p) for p in json.loads(parts[1]))
    if len(got) != len(jobs):
        say('  gp stderr tail: %s' % out.stderr[-400:])
    return got, got2


# ---------------------------- driver -------------------------------
def compose_A(G):
    """f = G(Phi') for quartic G (genre-A/B base construction)."""
    f, p = [], [1]
    for g in G:
        f = padd(f, [g * c for c in p])
        p = pmul(p, PHI1)
    return f


def rand_pert(deg, scale):
    return [scale * random.randint(0, 15) for _ in range(deg + 1)]


TEETH = {'T-SHADOW-INERT': 0, 'T-SHADOW-2SIDED': 0, 'T-LABEL': 0}


def main():
    t0 = time.time()
    say('=== GENHN r2 supp: corrected tower read T(b)\' vs PARI ===')
    jobs, meta = [], []           # meta: (fam, tag, pred, stage_lab)

    def add(fam, tag, f, true_lab, stage_lab):
        if true_lab is None:
            chk(fam, False, '%s: composed development not monic'
                % tag)
            return
        say('  %s %s: TRUE pins (%s,%s) %s -> %s | STAGE pins '
            '(%s,%s) %s -> %s'
            % (fam, tag, true_lab[0], true_lab[1], true_lab[2],
               true_lab[3], stage_lab[0], stage_lab[1], stage_lab[2],
               stage_lab[3]))
        jobs.append(f)
        meta.append((fam, tag, true_lab, stage_lab))

    # ---- SUPP-A0: the PE1 verifier's instances (regression) ----
    A0 = [('T-RAM', [96, 16, 0, 0, 1], (25, 14), (21, 14), 'iRAM'),
          ('T-INERT', [96, 0, 32, 16, 1], (21, 14), (28, 14),
           'iINERT'),
          ('T-2SIDED', [224, 0, 32, 16, 1], (21, 14), (30, 14),
           'i2SIDED')]
    for (tag, G, tpins, spins, slab) in A0:
        f = compose_A(G)
        tl = read_A_true(f, 5)
        sl = read_A_stage(f, 5)
        chk('SUPP-A0', (tl[0], tl[1]) == tpins,
            '%s TRUE pins %s want %s' % (tag, (tl[0], tl[1]), tpins))
        chk('SUPP-A0', (sl[0], sl[1]) == spins and sl[2] == slab,
            '%s STAGE read (%s,%s,%s) want %s %s'
            % (tag, sl[0], sl[1], sl[2], spins, slab))
        add('SUPP-A0', tag, f, tl, sl)
        fp = padd(f, rand_pert(7, 1024))
        add('SUPP-A0', tag + '-pert', fp, read_A_true(fp, 5),
            read_A_stage(fp, 5))

    # ---- SUPP-A1: fresh sweep at u2 = 5 and u2 = 7 ----
    for u2, g0s, s1, s2, s3 in [
            (5, [3, 5, 7, 9, 11, 13], 16, 8, 4),
            (7, [3, 5, 7, 11], 64, 16, 8)]:
        # v(g0) = u2 exactly (dv(A0) = 2*v(g0) = 2*u2); middle
        # floors strictly above the slope-u2/2 side.
        for k, odd in enumerate(g0s):
            g0 = (2 ** u2) * odd
            g1 = s1 * random.randint(0, 15) * (2 if u2 == 7 else 1)
            g2 = s2 * random.randint(0, 15) * (2 if u2 == 7 else 1)
            g3 = s3 * random.randint(0, 15)
            f = compose_A([g0, g1, g2, g3, 1])
            dvs, err = level1_parse(f, 4, 2 * u2, {1, 2, 3}, u2, 2)
            chk('SUPP-A1', err is None,
                'u2=%d #%d parse: %s' % (u2, k, err))
            tl = read_A_true(f, u2)
            sl = read_A_stage(f, u2)
            add('SUPP-A1', 'u2=%d#%d' % (u2, k), f, tl, sl)
            if k % 2 == 0:
                fp = padd(f, rand_pert(7, 2 ** (u2 + 2)))
                add('SUPP-A1', 'u2=%d#%d-pert' % (u2, k), fp,
                    read_A_true(fp, u2), read_A_stage(fp, u2))

    # ---- SUPP-B: the OTHER genre (2,1,4)->(1,2,2), K2 = F4 ----
    for k in range(10):
        g0 = 64 * (2 * random.randint(0, 7) + 1)
        g2 = 8 * (2 * random.randint(0, 7) + 1)
        g1 = 32 * random.randint(0, 15)
        g3 = 4 * random.randint(0, 15)
        f = compose_A([g0, g1, g2, g3, 1])
        dvs, err = level1_parse(f, 4, 12, {1, 3}, 3, 1)
        chk('SUPP-B', err is None, 'B#%d parse: %s' % (k, err))
        chk('SUPP-B', dvs is not None and dvs[2] == 6,
            'B#%d mid pin dv(A2) = %s want 6'
            % (k, dvs[2] if dvs else None))
        tl = read_B_true(f)
        sl = read_B_stage(f)
        add('SUPP-B', 'B#%d' % k, f, tl, sl)
        if k % 3 == 0:
            fp = padd(f, rand_pert(7, 512))
            add('SUPP-B', 'B#%d-pert' % k, fp, read_B_true(fp),
                read_B_stage(fp))

    # ---- SUPP-C: 3-stage stretch (n = 16) ----
    # [dev disclosure] first-draft instances (E0 = 4*Phi2 etc.)
    # FAILED the level-1 parse gate (leaf data below the outer
    # side: dv(A2) = 4 < 15) and were replaced BEFORE seal by
    # parse-gated ones; every 2-stage family was GREEN on run 1
    # unchanged.  The gates below are the honest tower-node
    # grammar: leaf data must clear EVERY lower level's floors.
    C_INST = [
        ('C-RAM85', padd(pmul(PHI3, PHI3), pmul([256], PHI2_C)),
         85, None),
        ('C-RAM93', padd(pmul(PHI3, PHI3), pmul([512], PHI2_C)),
         93, None),
        ('C-2SIDED', padd(padd(pmul(PHI3, PHI3),
                               pmul(pmul([512], PHI1), PHI3)),
                          pmul(pmul([0, 2 ** 18], PHI1), PHI2_C)),
         179, 82)]
    # (C-2SIDED E0 = 2^18 * x*Phi'*Phi2: dv3 = 8*18 + 14 + 21 = 179
    # -- the xPhi'*Phi2 composed slot; 179 > 2w = 164: t2SIDED.)
    for (tag, f, wu, ww) in C_INST:
        # level-1 gate: (2,1,8) node -- side slope 5/2 over [0,8],
        # dv(A0) = 20 exact, residual (T+1)^4 (mid pins above side)
        dvs, err = level1_parse(f, 8, 20, set(range(1, 8)), 5, 2)
        chk('SUPP-C', err is None, '%s level-1 parse: %s'
            % (tag, err))
        say('  SUPP-C %s level-1 dvs: %s' % (tag, dvs))
        # level-2 gate: Phi2-development, side slope 21/2 over
        # [0,4], dv2(D0) = 42 exact, residual (T-1)^2, mids above
        g, D = list(f), []
        for _ in range(4):
            g, r = pdivmod_monic(g, PHI2_C)
            D.append(r)
        chk('SUPP-C', g == [1], '%s level-2 dev monic' % tag)
        d2 = [dv2_A(r, 5) for r in D]
        chk('SUPP-C', d2[0] == 42,
            '%s dv2(D0) = %s want 42' % (tag, d2[0]))
        for J in range(1, 4):
            chk('SUPP-C', d2[J] is None or 2 * d2[J] > 21 * (4 - J),
                '%s level-2 pin J=%d at %s not above side'
                % (tag, J, d2[J]))
        say('  SUPP-C %s level-2 dv2(D): %s' % (tag, d2))
        tl = read_C_true(f)
        chk('SUPP-C', tl is not None and (tl[0], tl[1]) == (wu, ww),
            '%s level-3 pins %s want %s'
            % (tag, (tl[0], tl[1]) if tl else None, (wu, ww)))
        if tl is None or tl[3] is None:
            say('  SUPP-C %s: UNDEC/unparsed (%s) -- DROPPED '
                '(stretch leg, disclosed)' % (tag, tl))
            continue
        say('  SUPP-C %s: level-3 pins (%s,%s) %s -> %s'
            % (tag, tl[0], tl[1], tl[2], tl[3]))
        jobs.append(f)
        meta.append(('SUPP-C', tag, tl, (None, None, 'n/a', None)))

    # ---- PARI ----
    r2idx = set(range(0, len(jobs), 2)) | set(
        i for i, m in enumerate(meta) if m[0] in ('SUPP-A0',
                                                  'SUPP-C'))
    say('  %d gp jobs (route 1 all; route 2 on %d)'
        % (len(jobs), len(r2idx)))
    got, got2 = run_gp(jobs, r2idx)
    diag, npin_diff, nlab_diff = {}, 0, 0
    for i, (fam, tag, tl, sl) in enumerate(meta):
        if i not in got:
            chk(fam, False, 'missing gp answer %s' % tag)
            continue
        disc_ok, sig = got[i]
        chk(fam, disc_ok, '%s disc != 0' % tag)
        if tl[3] is None:
            key = tuple(sig)
            diag[key] = diag.get(key, 0) + 1
        else:
            chk(fam, sig == sorted(tl[3]),
                '%s corrected read vs PARI r1: got %s want %s'
                % (tag, sig, sorted(tl[3])))
            if i in got2:
                chk(fam, got2[i] == sorted(tl[3]),
                    '%s corrected read vs PARI r2 (factorpadic): '
                    'got %s want %s' % (tag, got2[i],
                                        sorted(tl[3])))
        if fam == 'SUPP-C':
            continue
        if (tl[0], tl[1]) != (sl[0], sl[1]):
            npin_diff += 1
            if tl[3] is not None and sl[2] in ('iRAM', 'tRAM') \
                    and tl[2] == 'tRAM':
                TEETH['T-LABEL'] += 1
        if sl[3] is not None and sl[3] != tl[3]:
            nlab_diff += 1
            if sl[2].endswith('INERT') and sig != sorted(sl[3]):
                TEETH['T-SHADOW-INERT'] += 1
            if sl[2].endswith('2SIDED') and sig != sorted(sl[3]):
                TEETH['T-SHADOW-2SIDED'] += 1
    say('  UNDEC diagnostic tail (unscored): %s' % diag)
    say('  stage-vs-corrected divergence: %d pin rows, %d sigma '
        'rows (of %d tower rows)' % (npin_diff, nlab_diff,
                                     len(meta)))
    for t, n in TEETH.items():
        chk('TEETH', n >= 1, 'tooth %s did not fire' % t)
        say('  tooth %s fired x%d' % (t, n))
    nv = len(VIOL)
    say('=== VERDICT: %s -- checks %s, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', NCHK, nv,
           time.time() - t0))
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    rc = main()
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
