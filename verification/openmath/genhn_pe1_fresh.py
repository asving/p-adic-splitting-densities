#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""genhn_pe1_fresh.py -- GENHN passPE1 FRESH-ROUTE verifier instrument.

HOSTILE PASS PE1 on GENHN_PROOF_2026-08-08.md (at the [r1]+[e2] state).
FULLY INDEPENDENT of the sealed battery: imports NOTHING from the
*_checks.py family; its own slot-min reader; PARI oracle via GLOBAL
factor + nfinit([g,[2]]) + idealprimedec (the GENH4-annexpass3 dual-
oracle route -- NO factorpadic anywhere).

Territory chosen where the sealed battery did NOT go (its disclosure
GENHN-BOX-3: every battery row has f1 = 1; towers witness-only):

FR-A  the genre (1,3,2) = E13(1) (mu=2, e1=1, f1=3, h=1, K = F8) over
      Z2 -- the FIRST f1 >= 2 STAGE ever machine-exercised, and the
      FIRST comp >= 2 band-census contact (E2's clause beyond GENH4's
      comp=1 instance).  Exhaustive per-key stage sweeps:
        N=7: whole decided stratum is the band pin m = N = 7
             (comp(7) = 2):   RAM(7) = (Q^2-1)*2^13 = 24,576,
             UND = 2^13 = 8,192.       [E2 census Q^comp - 1]
        N=8: pin m = 7 is a FULL slot (comp = 3 = f1):
             RAM(7) = (Q^3-1)*2^18 = 1,835,008, UND = 2^18.
                                        [re-based census |K|-1]
      TEETH: the swapped censuses (7 at N=7 band / 3 at N=8) must
      DISAGREE with observation, else the test has no teeth.
FR-B  PARI sigma at (1,3,2) -- GENHN.C's dictionary row
      {(2,3)} / {(1,3),(1,3)} / {(1,6)}, called "visibility-floored,
      no row -- S9 box" by the note (FIRST contact):
      band-RAM(7) members incl. OUT-OF-WINDOW perturbations (the
      eta-independence claim of GENHN-2 made physical), constructed
      INERT / SPLITEQ / 2SIDED / deep RAM(9), UND tail as diagnostic
      (predicted mixed).
FR-C  the refine transfer (GENHN.A(iv)) at f1 = 3, pointwise: alpha
      events at kappa = 4 with genuine K = F8 letters (s and s^2
      involve eta) -- recenter Phi' -> Phi' - s^.n(4), ACTUAL exact
      re-division, both pins must die into the floored node
      {dv(A0) > 8, dv(A1) > 4}; WRONG-LETTER control must FAIL.
      (The battery's GN-REFINE3 was f1 = 1 / prime-field letters.)
FR-D  tower composition (LEMMA GENHN-T(b)) at n = 8 with PARI sigma
      -- the battery had ONE tower witness and NO tower sigma leg.
      f(x) = G(x^2-2): outer stage (2,1,4) over Z2, inner (2,1,2)
      event at side (0,10)-(4,0), residual (y+1)^2.  Own symbolic
      division in R[Y], R = Z[x]/(x^2-2), inner reader on the
      dv2 = 4v-ladder; three inner leaves with HAND-DERIVED pins:
        G = Y^4 + 16Y + 96            inner-RAM(21)    -> {(8,1)}
        G = Y^4 + 16Y^3 + 32Y^2 + 96  inner-INERT      -> {(4,2)}
        G = Y^4 + 16Y^3 + 32Y^2 + 224 inner-2SIDED     -> {(4,1)x2}
      (inner kappa2 = 14 is the CARRY pin 8x from Y^4's re-division
      -- the composed law's carry bookkeeping is load-bearing here.)
      NOTE: a 3-stage tower needs mu1 >= e2f2mu2 >= 8, hence n >= 16
      (GENHN-T(a) applied twice) -- NOT constructible at n = 8/12.

PREREGISTERED: every expected value above is written before the run;
verdict = GREEN iff all scored checks pass, all teeth fire, and the
diagnostic tail is reported (not scored).
"""
import subprocess, sys, random, json, time
from fractions import Fraction

random.seed(20260809)
VIOL = []
NCHK = {'FR-A': 0, 'FR-B': 0, 'FR-C': 0, 'FR-D': 0, 'TEETH': 0}
LOG = []


def say(m):
    print(m)
    sys.stdout.flush()
    LOG.append(m)


def chk(fam, ok, tag):
    NCHK[fam] += 1
    if not ok:
        VIOL.append((fam, tag))
        say('  !! VIOLATION %s %s' % (fam, tag))


# ============ F8 arithmetic (eta^3 = eta + 1; bits 1,eta,eta^2) ====
def f8mul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1:
            r ^= a << i
    for i in (5, 4, 3):
        if (r >> i) & 1:
            r ^= (1 << i) ^ (1 << (i - 3)) ^ (1 << (i - 2))
    return r


def f8sq(a):
    return f8mul(a, a)


# ============ integer polys (little-endian lists) ==================
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


def pdivmod_monic(f, g):
    """f = q*g + r over Z, g monic."""
    f = list(f)
    dg = len(g) - 1
    assert g[-1] == 1
    q = [0] * max(1, len(f) - dg)
    for i in range(len(f) - 1, dg - 1, -1):
        c = f[i]
        if c:
            q[i - dg] = c
            for j, gj in enumerate(g):
                f[i - dg + j] -= c * gj
    r = f[:dg]
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return q, r


def v2(n):
    n = abs(n)
    if n == 0:
        return None
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def dv_e1eq1(A):
    """dv(A(theta)) slot-min at e1=1, h=1: min_i(v2(a_i) + i)."""
    best = None
    for i, c in enumerate(A):
        if c:
            d = v2(c) + i
            if best is None or d < best:
                best = d
    return best


PHI = [8, 4, 0, 1]                      # x^3 + 4x + 8 (psi = y^3+y+1)


def build_f(A1, A0):
    f = pmul(PHI, PHI)
    f = padd(f, pmul(A1, PHI))
    f = padd(f, A0)
    return f


# ============ FR-A: the (1,3,2) stage sweeps =======================
def slot_readable(digs, m, N):
    """digs[i][v] in {0,1}: coordinate a_{.,i} O-digit at height v.
    Readable F8 residue of the height-m slot (in-window comps only):
    comp t at coordinate i=t, O-height m - t (h = 1, e1 = 1)."""
    r = 0
    for t in range(3):
        vv = m - t
        if 0 <= vv <= N - 1 and digs[t].get(vv, 0):
            r ^= (1 << t)
    return r


def a_state_read(digs, N, mlo, mhi):
    """first m in [mlo, mhi] with readable slot != 0 (else None)."""
    for m in range(mlo, mhi + 1):
        if slot_readable(digs, m, N):
            return m
    return None


def adjudicate(u, w_read, N):
    """my own transcription of the mu=2 stage read + E1 trichotomy.
    u = readable dv(A0) (None = nothing readable), w_read = readable
    dv(A1).  Undercut floor at e1=1: N (coordinate a00's first
    out-of-window digit).  Conservative on anything ambiguous."""
    w_worst = N if w_read is None else min(w_read, N)
    if u is None or u > N:
        return 'UND'
    if u < N:
        if u % 2 == 1 and u <= 2 * w_worst:
            return 'RAM(%d)' % u
        if w_read is not None and u > 2 * w_read:
            return '2SIDED'
        return 'EVENT(%d)' % u          # residual read needed
    # u == N: the band trichotomy (E1, r3 form)
    if w_read is not None and N > 2 * w_read:
        return '2SIDED-band'
    if N % 2 == 1 and N <= 2 * w_worst:
        return 'RAM(%d)' % N
    return 'UND'


def sweep_132(N, expect, tooth_expect_wrong):
    say('[FR-A] (1,3,2) exhaustive stage sweep N=%d' % N)
    # A0 digit ranges (floors v(a0i) >= 7-i), window v <= N-1
    a0rng = [range(max(0, 7 - i), N) for i in range(3)]
    a1rng = [range(max(0, 4 - i), N) for i in range(3)]

    def states(rngs):
        # enumerate digit dicts per coordinate
        import itertools
        digsets = []
        for r in rngs:
            digsets.append(list(itertools.product([0, 1],
                                                  repeat=len(r))))
        for combo in itertools.product(*digsets):
            digs = []
            for i, r in enumerate(rngs):
                digs.append({v: b for v, b in zip(r, combo[i])})
            yield digs

    # classify A1 states by readable w
    wdist = {}
    for digs in states(a1rng):
        w = a_state_read(digs, N, 4, N + 2)
        wdist[w] = wdist.get(w, 0) + 1
    # classify A0 states by readable u
    udist = {}
    for digs in states(a0rng):
        u = a_state_read(digs, N, 7, N + 2)
        udist[u] = udist.get(u, 0) + 1
    obs = {}
    for u, cu in udist.items():
        for w, cw in wdist.items():
            verdict = adjudicate(u, w, N)
            obs[verdict] = obs.get(verdict, 0) + cu * cw
    say('  observed strata: %s' % obs)
    say('  expected strata: %s' % expect)
    chk('FR-A', obs == expect, 'N=%d partition' % N)
    # tooth: the WRONG census must disagree
    NCHK['TEETH'] += 1
    if obs.get('RAM(7)') == tooth_expect_wrong:
        VIOL.append(('TEETH', 'census tooth dead N=%d' % N))
        say('  !! TOOTH DEAD N=%d' % N)
    else:
        say('  tooth fires: wrong census %d != obs %d'
            % (tooth_expect_wrong, obs.get('RAM(7)')))
    return obs


# ============ FR-C: refine transfer at f1 = 3 ======================
def f8_lift_slot8(c):
    """A0 = exact lift of F8 element c at slot height 8."""
    return [256 * (c & 1), 128 * ((c >> 1) & 1), 64 * ((c >> 2) & 1)]


def refine_key(s):
    """Phi' - s^ * n(4), s^ = s0 + s1(x/2) + s2(x/2)^2 (times 16)."""
    w = [16 * (s & 1), 8 * ((s >> 1) & 1), 4 * ((s >> 2) & 1)]
    return [PHI[i] - (w[i] if i < 3 else 0) for i in range(4)]


def run_refine3():
    say('[FR-C] f1=3 refine transfer at kappa=4, K = F8 letters')
    a1vars = [[0], [32], [0, 0, 8]]
    tails = [[0], [0, 512]]
    n = 0
    for s in range(1, 8):
        c0 = f8sq(s)
        for A1 in a1vars:
            for tl in tails:
                A0 = padd(f8_lift_slot8(c0), tl)
                f = build_f(A1, A0)
                phi2 = refine_key(s)
                q1, r1 = pdivmod_monic(f, phi2)
                q2, r2 = pdivmod_monic(q1, phi2)
                chk('FR-C', q2 == [1], 'monic top s=%d' % s)
                d0, d1 = dv_e1eq1(r1), dv_e1eq1(r2)
                ok = (d0 is None or d0 > 8) and (d1 is None or d1 > 4)
                chk('FR-C', ok, 'pins die s=%d A1=%s tail=%s -> '
                    'dv=(%s,%s)' % (s, A1, tl, d0, d1))
                n += 1
        # wrong-letter control: s' != s must NOT kill the A0 pin
        sw = (s % 7) + 1
        if sw == s:
            sw = (sw % 7) + 1
        A0 = f8_lift_slot8(c0)
        f = build_f([0], A0)
        q1, r1 = pdivmod_monic(f, refine_key(sw))
        d0 = dv_e1eq1(r1)
        NCHK['TEETH'] += 1
        if d0 == 8:
            say('  wrong-letter control fires (s=%d s\'=%d pin '
                'survives at 8)' % (s, sw))
        else:
            VIOL.append(('TEETH', 'wrong-letter dead s=%d' % s))
            say('  !! wrong-letter control DEAD s=%d (dv=%s)'
                % (s, d0))
    say('  %d refine events transported' % n)


# ============ FR-D: tower composition ==============================
# R = Z[x]/(x^2-2): elements (a, b) = a + b*x.
def rmul(u, v):
    a, b = u
    c, d = v
    return (a * c + 2 * b * d, a * d + b * c)


def radd(u, v):
    return (u[0] + v[0], u[1] + v[1])


def rneg(u):
    return (-u[0], -u[1])


def dv2_R(u):
    a, b = u
    cands = []
    if a:
        cands.append(4 * v2(a))
    if b:
        cands.append(4 * v2(b) + 2)
    return min(cands) if cands else None


def ry_divmod(F, G):
    """F, G in R[Y] (lists of R-pairs), G monic (lead (1,0))."""
    F = list(F)
    dg = len(G) - 1
    assert G[-1] == (1, 0)
    Q = [(0, 0)] * max(1, len(F) - dg)
    for i in range(len(F) - 1, dg - 1, -1):
        c = F[i]
        if c != (0, 0):
            Q[i - dg] = c
            for j, gj in enumerate(G):
                F[i - dg + j] = radd(F[i - dg + j],
                                     rneg(rmul(c, gj)))
    Rr = F[:dg]
    return Q, Rr


def inner_read(G_coeffs):
    """G = Y^4 + g3Y^3 + g2Y^2 + g1Y + g0 over Z; inner division by
    Phi'' = Y^2 - 4x; pins on the dv2 = 4*v ladder; adjudicate the
    inner mu=2 system over K2 = F2."""
    F = [(g, 0) for g in G_coeffs]
    PHI2 = [(0, -4), (0, 0), (1, 0)]    # Y^2 - 4x
    q1, r1 = ry_divmod(F, PHI2)
    q2, r2 = ry_divmod(q1, PHI2)
    assert q2 == [(1, 0)]
    B0 = r1 + [(0, 0)] * (2 - len(r1))
    B1 = r2 + [(0, 0)] * (2 - len(r2))

    def dvB(B):
        cands = []
        d = dv2_R(B[0])
        if d is not None:
            cands.append(d)
        d = dv2_R(B[1])
        if d is not None:
            cands.append(d + 5)
        return min(cands) if cands else None
    u2, k2 = dvB(B0), dvB(B1)
    if u2 is None:
        return (u2, k2, 'DRAIN', None)
    if k2 is None or u2 < 2 * k2:
        if u2 % 2 == 1:
            return (u2, k2, 'iRAM', [(8, 1)])
        return (u2, k2, 'iEVEN-SIDE', None)     # would need residue
    if u2 == 2 * k2:
        # residues over F2 are 1: residual T^2+T+1, irreducible
        return (u2, k2, 'iINERT', [(4, 2)])
    return (u2, k2, 'i2SIDED', [(4, 1), (4, 1)])


def compose_tower(G):
    """f(x) = G(x^2 - 2) as an integer poly."""
    base = [-2, 0, 1]
    f = [0]
    p = [1]
    for g in G:
        f = padd(f, [g * c for c in p])
        p = pmul(p, base)
    return f


PHI2X = [4, -4, -4, 0, 1]               # (x^2-2)^2 - 4x in Z[x]


def inner_read_true(G):
    """the HONEST order-2 read: Phi2-adic development of f = G(x^2-2)
    itself in Z[x], pins in the COMPOSED slot basis {1, x, Phi', xPhi'}
    (classes 0/2/1/3 mod 4 on the dv2 = 4v ladder; x^2 = Phi' + 2,
    x^3 = xPhi' + 2x).  The stage-algebra read (inner_read) kills the
    Phi'-classes; this one keeps them."""
    f = compose_tower(G)
    q1, r1 = pdivmod_monic(f, PHI2X)
    q2, r2 = pdivmod_monic(q1, PHI2X)
    assert q2 == [1]

    def dv2c(C):
        C = list(C) + [0] * (4 - len(C))
        coords = {0: C[0] + 2 * C[2], 2: C[1] + 2 * C[3],
                  5: C[2], 7: C[3]}
        best = None
        for off, c in coords.items():
            if c:
                d = 4 * v2(c) + off
                if best is None or d < best:
                    best = d
        return best
    u2, k2 = dv2c(r1), dv2c(r2)
    if u2 is None:
        return (u2, k2, 'DRAIN', None)
    if k2 is None or u2 < 2 * k2:
        if u2 % 2 == 1:
            return (u2, k2, 'tRAM', [(8, 1)])
        return (u2, k2, 'tEVEN-SIDE', None)
    if u2 == 2 * k2:
        return (u2, k2, 'tINERT', [(4, 2)])
    return (u2, k2, 't2SIDED', [(4, 1), (4, 1)])


TOWERS = [
    # (tag, G, stage-algebra pins (hand), NOTE-frame composed sigma,
    #  TRUE composed-basis pins (hand))
    ('T-RAM', [96, 16, 0, 0, 1], (21, 14), [(8, 1)], (25, 14)),
    ('T-INERT', [96, 0, 32, 16, 1], (28, 14), [(4, 2)], (21, 14)),
    ('T-2SIDED', [224, 0, 32, 16, 1], (30, 14), [(4, 1), (4, 1)],
     (21, 14)),
]


# ============ PARI oracle (global route, NO factorpadic) ===========
GP_PROG = r"""
sig(f) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
        listput(out, [1, 1]),
        my(nf = nfinit([g, [2]]), dec = idealprimedec(nf, 2));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
"""


def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                    if c) or '0'


def run_gp(jobs):
    lines = [GP_PROG]
    for i, f in enumerate(jobs):
        lines.append('print("R %d ", poldisc(Pol(%s)) != 0, " ", '
                     'sig(%s))' % (i, polystr(f), polystr(f)))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=600)
    got = {}
    for line in out.stdout.splitlines():
        if line.startswith('R '):
            parts = line[2:].split(' ', 2)
            idx = int(parts[0])
            disc_ok = parts[1] == '1'
            sig = sorted(tuple(p) for p in json.loads(
                parts[2].replace('[', '[').replace(']', ']')))
            got[idx] = (disc_ok, [tuple(p) for p in sig])
    if out.returncode != 0 or len(got) != len(jobs):
        say('  gp stderr: %s' % out.stderr[-500:])
    return got


def rand_pert(deg, scale):
    return [scale * random.randint(0, 15) for _ in range(deg + 1)]


def main():
    t0 = time.time()
    say('=== GENHN passPE1 fresh route (independent instrument) ===')
    # ---- FR-A ----
    sweep_132(7, {'RAM(7)': 24576, 'UND': 8192}, 7 * 2 ** 13)
    sweep_132(8, {'RAM(7)': 1835008, 'UND': 262144}, 3 * 2 ** 18)
    # ---- FR-C ----
    run_refine3()
    # ---- FR-B jobs ----
    say('[FR-B] building PARI jobs at (1,3,2)')
    jobs, preds, tags = [], [], []

    def job(f, pred, tag):
        jobs.append(f)
        preds.append(pred)
        tags.append(tag)

    N = 7
    for (e1, e2) in [(1, 0), (0, 1), (1, 1)]:
        for k in range(6):
            A0 = [0, 64 * e1, 32 * e2 + 64 * random.randint(0, 1)]
            A1 = [16 * random.randint(0, 7),
                  8 * random.randint(0, 15),
                  4 * random.randint(0, 31)]
            f = build_f(A1, A0)
            job(f, [(2, 3)], 'bandRAM7 (%d,%d)#%d' % (e1, e2, k))
            if k < 2:
                fp = padd(f, rand_pert(5, 128))
                job(fp, [(2, 3)], 'bandRAM7-pert (%d,%d)#%d'
                    % (e1, e2, k))
    # constructed GENHN.C legs (exact stage leaves)
    for (A1, A0, pred, tag) in [
            ([16], [256], [(1, 6)], 'INERT T^2+T+1'),
            ([0, 8], [0, 0, 64], [(1, 6)], 'INERT T^2+eta T+eta^2'),
            ([16, 8], [0, 128], [(1, 3), (1, 3)], 'SPLITEQ (1)(eta)'),
            ([16], [512], [(1, 3), (1, 3)], '2SIDED(4,5)'),
            ([32], [512], [(2, 3)], 'RAM(9)')]:
        f = build_f(A1, A0)
        job(f, pred, tag)
        job(padd(f, rand_pert(5, 4096)), pred, tag + '-pert')
    ndiag0 = len(jobs)
    # UND diagnostic tail (NOT scored; predicted mixed)
    for k in range(4):
        A0 = [0, 0, 64 * random.randint(0, 1)]
        A1 = [16 * random.randint(0, 7), 8 * random.randint(0, 15),
              4 * random.randint(0, 31)]
        f = build_f(A1, A0)
        for j in range(3):
            job(padd(f, rand_pert(5, 128)), None, 'UND-diag#%d.%d'
                % (k, j))
    # ---- FR-D jobs ----
    say('[FR-D] tower composition: NOTE-frame read vs TRUE composed-'
        'basis read vs PARI')
    notepred = {}
    for (tag, G, pins, pred, tpins) in TOWERS:
        u2, k2, kind, comp = inner_read(G)
        tu2, tk2, tkind, tcomp = inner_read_true(G)
        say('  %s: NOTE-frame (stage algebra) pins (%s,%s) %s -> %s'
            % (tag, u2, k2, kind, comp))
        say('  %s: TRUE composed-basis pins (%s,%s) %s -> %s'
            % (tag, tu2, tk2, tkind, tcomp))
        chk('FR-D', (u2, k2) == pins, '%s note-frame pins vs hand'
            % tag)
        chk('FR-D', comp == pred, '%s note-frame composed dict' % tag)
        chk('FR-D', (tu2, tk2) == tpins, '%s TRUE pins vs hand' % tag)
        notepred[tag] = pred
        f = compose_tower(G)
        job(f, (pred, tcomp), tag)
        job(padd(f, rand_pert(7, 1024)), (pred, tcomp), tag + '-pert')
    # ---- run PARI ----
    say('  %d gp jobs (global nfinit/idealprimedec route)'
        % len(jobs))
    got = run_gp(jobs)
    diag = {}
    refuted = []
    for i, (pred, tag) in enumerate(zip(preds, tags)):
        if i not in got:
            chk('FR-B' if not tag.startswith('T-') else 'FR-D',
                False, 'missing gp answer %s' % tag)
            continue
        disc_ok, sig = got[i]
        if pred is None:
            key = tuple(sig) if disc_ok else 'disc0'
            diag[key] = diag.get(key, 0) + 1
            continue
        if tag.startswith('T-'):
            npred, tpred = pred
            chk('FR-D', disc_ok, '%s disc != 0' % tag)
            chk('FR-D', sig == sorted(tpred),
                '%s TRUE-read vs PARI: got %s want %s'
                % (tag, sig, sorted(tpred)))
            if sig != sorted(npred):
                refuted.append('%s: note-frame %s vs PARI %s'
                               % (tag, sorted(npred), sig))
            continue
        chk('FR-B', disc_ok, '%s disc != 0' % tag)
        chk('FR-B', sig == sorted(pred), '%s: got %s want %s'
            % (tag, sig, sorted(pred)))
    say('  UND diagnostic tail (unscored): %s' % diag)
    say('  NOTE-FRAME REFUTATION TALLY (GENHN-T(b) finding): %d '
        'instances' % len(refuted))
    for r in refuted:
        say('    REFUTED %s' % r)
    NCHK['TEETH'] += 1
    if len(diag) >= 2:
        say('  UND-mixedness tooth fires: %d distinct sigma'
            % len(diag))
    else:
        VIOL.append(('TEETH', 'UND tail NOT mixed: %s' % diag))
        say('  !! UND tail not mixed')
    # ---- verdict ----
    nv = len(VIOL)
    say('=== VERDICT: %s -- checks %s, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', NCHK, nv,
           time.time() - t0))
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
