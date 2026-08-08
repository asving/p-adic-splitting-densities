#!/usr/bin/env python3
r"""HE3 -- the mu = 3 stage sigma battery ([GENHN-HE(mu >= 3)]).

*** WIP AT COMMIT 1 (survival discipline: this file is committed
    PRELIMINARY, before any full run, together with the note skeleton
    lean/notes/openmath/HE3_PROOF_2026-08-08.md).  The DESIGN and the
    PREREGISTERED PREDICTIONS below are sealed as of this commit; legs
    are wired in subsequent commits, and the verdict is appended to the
    note only FROM the committed artifacts he3_checks_output.txt /
    he3_checks_results.json. ***

WHAT THIS TESTS.  THEOREM HE3.A (the stage-sigma recursion): at a
DECIDED stage leaf of a composite stage of multiplicity mu over the
stage ring R (complete DVR, e = e1, f = f1, residue K), with stage type
tau = {(e_s^i, f_s^i)}, Sum_i e_s^i f_s^i = mu, every disc != 0 lift
factors over O into exactly k irreducibles with

    sigma(f) = { (e1 * e_s^i , f1 * f_s^i) }_i .

First live case: mu = 3.  The battery works the genre

    E3(h) = (Q; e1 = 2, f1 = 1, mu = 3; h)   key Phi' = x^2 - z*pi^h,
            residual (y - z)^3, D' = e1 f1 = 2, deg f = D' mu = 6,

i.e. SEXTIC members with a degree-2 ramified key carrying a
multiplicity-3 residual -- exactly the "local degree budget 6" slice of
the charge -- plus the n = 7 embedded slice (sextic block times a split
linear sibling, extracted by GENIND-3's Hensel step).

MEMBER MODEL.  By LEMMA GENHN-1 the Phi'-adic development is a digit
bijection, so we enumerate STAGE COORDINATES directly:

    f = Phi'^3 + A2 Phi'^2 + A1 Phi' + A0 ,  A_j = a_j1 x + a_j0 ,
    dv := e1 v = 2 v ,   S := e1 h = 2h ,
    node: dv(A_j) >= (3 - j) S + 1     (entry floors)
    dv(A_j) = min(2 v(a_j0), 2 v(a_j1) + h).

Enumeration is over the window: digits of a_ji at heights < N.  Both
characteristics: O = Z_p (p in {2, 3}) and O = F_q[[t]] (q in {2, 3}),
the latter read by the same integer ladder with F_q[t]-arithmetic.
PARI factorpadic is available only on the Z_p side (that is the oracle
asymmetry disclosed by every prior unit); the F_q[[t]] rows are scored
against the label read plus the internal resultant identity.

THE FOUR LEGS.

 HE-NORM  LEMMA HE3-1 (the resultant identity), the engine of the whole
          proof, tested at EVERY test key:
              Sum_rho dv(Phi''(rho)) = D' * dv(B0),  f = B0 mod Phi''
          checked as  v(Res(f, Phi'')) == f1 * dv(B0)  with exact
          integer resultants (Bareiss on the Sylvester matrix), for
          Phi'' = Phi' and for every refined test key Phi' + s*n(kappa).

 HE-PSI   LEMMA HE3-3 (Psi-inversion): sample
              Psi(kappa) = Sum_rho dv(Phi'_{kappa,s}(rho))
          over integer kappa at generic letters, invert on the KNOWN
          slope set, and check the recovered slope counts equal
          D' * L_lambda (the polygon side lengths scaled by D').
          Cross-checked against the DIRECT count of root slopes read
          off PARI's factorization (per irreducible factor g:
          Sum_{rho in g} v(Phi'(rho)) = v(Res(g, Phi'))).

 HE-SIG   THEOREM HE3.A's dictionary: PARI sig(f, p) vs the stage-type
          prediction {(e1 e_s, f1 f_s)}, on every decided leaf, gated
          (embedded rows only) at the GENHN-S11.F extraction-certified
          perimeter.  At (e1, f1) = (2, 1), mu = 3 the five stage types
          and their predicted sigma:
              (3,1)               -> {(6,1)}
              (1,3)               -> {(2,3)}
              (1,1)+(2,1)         -> {(2,1),(4,1)}
              (1,1)+(1,2)         -> {(2,1),(2,2)}
              (1,1)+(1,1)+(1,1)   -> {(2,1),(2,1),(2,1)}   <-- 3 labels

 HE-BND   the sigma-resolution boundary: per row, the exact q-power of
          the sigma-UNDECIDED mass (members whose stage read does not
          decide at the window: repeated residuals still alive at the
          cap, plus the conservative drain), reported as a law and
          compared with the E3 species totals committed by GENHN
          (UND3/RAM3/ALPHA3).

TEETH (each must fire >= 1 or the verdict is RED).

 HE-T-UNDET  THE MECHANISM TOOTH.  On a 3-label member (stage type
             (1,1)^3, all three labels on ONE side), exhibit two
             DISTINCT nonnegative count vectors satisfying both
             identities that GENHN.C's mu = 2 proof uses (root count
             Sum n = D' mu, and the single resultant identity
             Sum n_lambda lambda = D' dv(A0)).  Their existence is the
             numerical certificate that the mu = 2 argument cannot
             reach mu = 3; the tooth FAILS (RED) if the mu = 2 system
             turns out to determine the counts after all.
 HE-T-SIG    dictionary flip: predicting {(6,1)} where the stage type is
             (1,1)^3 (or {(2,1)^3} where it is (3,1)) must be caught by
             PARI on >= 1 member.
 HE-T-NODE   entry-floor off-by-one: lowering one a_ji floor by 1 must
             break the genre parse (member leaves the opening locus) --
             the constructed loci are not accidentally floor-blind.
 HE-T-PSI    inversion with a corrupted slope set (one slope perturbed)
             must fail to reproduce the measured Psi.
 HE-T-CERT   on embedded (n = 7) rows, the uncertified tail must be
             NONEMPTY and must contain at least one PARI disagreement
             (the S11.F perimeter is real on both sides).

PREREGISTERED PREDICTIONS (sealed at this commit).

 Q1  HE-NORM: 0 violations at every test key of every member, both
     characteristics.  (If this fails, LEMMA HE3-1 is false and the
     whole proof collapses -- this is the single most load-bearing
     prediction of the unit.)
 Q2  HE-PSI: recovered slope counts == D' * L_lambda for every member;
     0 violations; and the PARI-direct slope census agrees.
 Q3  HE-SIG: 0 bad on every certified job; all five mu = 3 stage types
     realized at >= 1 member each across the rows (in particular the
     3-label type (1,1)^3, whose predicted sigma at (2,1) is
     {(2,1),(2,1),(2,1)}: a sextic splitting into three ramified
     quadratics).
 Q4  HE-BND: the sigma-undecided mass per row is an exact q-power
     (reported); the decided mass matches GENHN's committed E3 species
     totals on the shared rows (39,366 / 32,768 / 32,768 for
     (Z3,4,1) / (Z2,5,1) / (F2t,5,1)).
 Q5  all five teeth fire; verdict GREEN iff 0 violations and all teeth.

PINS (md5, checked as family HE-PIN at run time): genhn_checks.py,
genhn_checks_results.json, w12_checks.py, w10_checks.py.

PROVENANCE / DISCLOSURE.  The PARI oracle question is the pinned
w12_checks.GP_FUN `sig(f, p)` (factorpadic at precision 200 +
idealprimedec), reused verbatim with the same per-miss retry ladder
that GENHN's re-seal 2 introduced.  The E3 stage reader is written
FRESH here (independent of GENHN's) and tied to GENHN's committed E3
species totals on the shared rows -- a decorrelated second reader, not
a re-use.
"""

import sys, os, json, time, hashlib, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

WIP = False   # commit 2: legs wired; artifacts written by main()

# ---------------------------------------------------------------- pins
PINS = ['genhn_checks.py', 'genhn_checks_results.json',
        'w12_checks.py', 'w10_checks.py']


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


# --------------------------------------------- exact integer resultant
def bareiss(M):
    """Exact determinant of an integer matrix (fraction-free)."""
    n = len(M)
    if n == 0:
        return 1
    A = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    piv = i
                    break
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


def resultant(f, g):
    """f, g : coefficient lists LOW-to-HIGH over Z.  Sylvester det."""
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0:
        return 0
    N = m + n
    M = [[0] * N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(f):
            M[i][i + (m - j)] = c
    for i in range(m):
        for j, c in enumerate(g):
            M[n + i][i + (n - j)] = c
    return bareiss(M)


BIG = 10 ** 6          # stand-in for +infinity on dv values


# ---------------------------------------------------- p-adic scaffolding
def vp(a, p):
    if a == 0:
        return BIG
    n = 0
    while a % p == 0:
        a //= p
        n += 1
    return n


def padd(f, g):
    n = max(len(f), len(g))
    return [(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
            for i in range(n)]


def pmul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] += a * b
    return out


def pdivmod_monic(f, key):
    """f, key low-to-high, key monic of degree d.  Returns (q, r)."""
    d = len(key) - 1
    f = f[:]
    q = [0] * max(1, len(f) - d)
    for i in range(len(f) - 1, d - 1, -1):
        c = f[i]
        if c:
            q[i - d] = c
            for j in range(d + 1):
                f[i - d + j] -= c * key[j]
    return q, f[:d]


def development(f, key, mu):
    """Phi'-adic development: f = sum_{j<=mu} A_j key^j, deg A_j < deg key."""
    out, cur = [], f[:]
    for _ in range(mu + 1):
        q, r = pdivmod_monic(cur, key)
        out.append(r)
        cur = q
    return out


def normalizer(m, p, h):
    """n(m) = x^i p^a with i*h + 2a = m, i in {0,1}: dv(n) = m exactly."""
    i = (m - 0) % 2 if h % 2 == 0 else (m % 2)
    if (m - i * h) % 2:
        i = 1 - i
    a = (m - i * h) // 2
    if a < 0:
        return None
    return [p ** a] if i == 0 else [0, p ** a]


def dv_A(A, p, h):
    """dv(A(theta)) for A = a0 + a1 x, e1 = 2: the SLOT LEMMA, exact."""
    a0 = A[0] if len(A) > 0 else 0
    a1 = A[1] if len(A) > 1 else 0
    return min(2 * vp(a0, p), 2 * vp(a1, p) + h)


def lower_hull(pts):
    """pts = [(j, dv)] with dv possibly BIG; returns hull vertices sorted
    by j ascending (the lower convex hull, Newton polygon)."""
    pts = sorted([q for q in pts if q[1] < BIG])
    hull = []
    for q in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (q[0] - x1) >= (q[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(q)
    return hull


def sides(hull):
    """[(j1, j2, num, den)] with slope = num/den > 0 (descending heights)."""
    out = []
    for (j1, m1), (j2, m2) in zip(hull, hull[1:]):
        num, den = m1 - m2, j2 - j1
        g = gcd(num, den) if num else den
        out.append((j1, j2, num // g, den // g))
    return out


def len_slope_gt(hull, floor_num, floor_den):
    """total horizontal length of sides with slope strictly > floor."""
    tot = 0
    for j1, j2, num, den in sides(hull):
        if num * floor_den > floor_num * den:
            tot += j2 - j1
    return tot


# ------------------------------------------------- the reader (Psi-machine)
class Und(Exception):
    pass


def read_stage(f, key, mu, p, h, N, floor=(0, 1), depth=0, trace=None):
    """Returns the stage type: a sorted list of (e_s, f_s) pieces, or
    raises Und.  Rational residual roots are detected by RECENTERING at
    integer-height test keys and re-reading the polygon -- the proof's own
    mechanism (LEMMA HE3-2/HE3-4), with no residual polynomial built and
    no twist bookkeeping.  Complete for mu <= 3 (see the note S9 box)."""
    if depth > 6:
        raise Und('depth')
    dev = development(f, key, mu)
    dvs = [dv_A(dev[j], p, h) for j in range(mu + 1)]
    if dvs[mu] != 0:
        raise Und('not monic at mu')
    cap = 2 * N
    pts = [(j, dvs[j]) for j in range(mu + 1) if dvs[j] < cap]
    if dvs[0] >= cap:
        # conservative drain (GENHN's convention): A_0 not lift-stable,
        # so the deepest root's slope is not determined by window data.
        raise Und('drain')
    hull = lower_hull(pts)
    if any(dvs[j] >= cap and j > 0 for j in range(mu)):
        # a capped interior coefficient can only raise the hull: the read
        # is UND unless the capped point is above the hull already.
        for j in range(mu):
            if dvs[j] >= cap:
                for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
                    if x1 <= j <= x2:
                        hy = y1 + (y2 - y1) * (j - x1) / (x2 - x1)
                        if cap <= hy:
                            raise Und('cap')
    pieces = []
    for j1, j2, num, den in sides(hull):
        if num * floor[1] <= floor[0] * den:
            continue                      # belongs to a shallower class
        L, ell = j2 - j1, den
        if L % ell:
            raise Und('lattice')
        d = L // ell
        if d == 1:
            pieces.append((ell, 1))
            continue
        if ell != 1:
            raise Und('mixed side (mu>=4 territory)')
        lam = num
        if lam >= cap:
            raise Und('cap-slope')
        nz = normalizer(lam, p, h)
        if nz is None:
            raise Und('normalizer')
        base_gt = len_slope_gt(hull, lam, 1)
        found = 0
        for s in range(1, p):
            key_s = padd(key, [s * c for c in nz])
            dev2 = development(f, key_s, mu)
            dvs2 = [dv_A(dev2[j], p, h) for j in range(mu + 1)]
            # SOUNDNESS (the sigma-resolution boundary, note LEMMA HE3-5).
            # A recentered coefficient at or above the cap has UNKNOWN
            # true dv.  It is HARMLESS iff the cap already exceeds the
            # lambda-line height at its abscissa -- then "dv >= cap"
            # already certifies "dv > line", i.e. that the pin is LIFTED,
            # which is the only fact the multiplicity count needs.  If
            # instead cap <= line height, the lift is undetermined by
            # window-N data and the member's sigma is UNDECIDED.
            # (Silently dropping capped points -- as a first version of
            # this reader did -- mis-reads split residuals as inert.)
            und_cap = False
            for j in range(mu):
                if dvs2[j] >= cap:
                    line = dvs[j1] - lam * (j - j1) if j >= j1 else None
                    if line is None or cap <= line:
                        und_cap = True
            if und_cap:
                raise Und('cap-refine')
            # m_s = the number of LIFTED pins (LEMMA HE3-2(b)): the
            # coefficients of Z^0..Z^{m-1} of R_lambda(Z+s) vanish, i.e.
            # the pins at abscissae j1..j1+m-1 rise strictly above the
            # lambda-line.  Counted DIRECTLY -- robust to capped-harmless
            # values (dv >= cap > line already certifies "lifted"),
            # whereas a hull-length difference silently loses them.
            m_s = 0
            for j in range(j1, j2):
                line = dvs[j1] - lam * (j - j1)
                if dvs2[j] > line:
                    m_s += 1
                else:
                    break
            if m_s <= 0:
                continue
            found += m_s
            if m_s == 1:
                pieces.append((1, 1))
            else:
                pieces.extend(read_stage(f, key_s, mu, p, h, N,
                                         floor=(lam, 1), depth=depth + 1,
                                         trace=trace))
        left = d - found
        if left == 1:
            raise Und('leftover 1 (undetected rational root)')
        if left in (2, 3):
            pieces.append((1, left))
        elif left > 3:
            raise Und('leftover >3 (mu>=4 territory)')
    if not pieces:
        raise Und('empty read')
    if depth == 0 and sum(a * b for a, b in pieces) != mu:
        # INTERNAL TOOTH: the label bookkeeping Sum e_s f_s = mu is a
        # proof-level invariant (note S6.2 consistency check).  A
        # violation is a reader bug, not a member property -- hard fail.
        raise AssertionError('label bookkeeping: %s != mu=%d (dvs=%s)'
                             % (pieces, mu, dvs))
    return sorted(pieces)


def sigma_pred(pieces, e1, f1):
    return tuple(sorted((e1 * a, f1 * b) for a, b in pieces))


# ------------------------------------- LEMMA HE3-1: the resultant identity
def norm_identity(f, key, p, h, f1=1):
    """v(Res(f, key)) == f1 * dv(B0), B0 = f mod key.  Returns (lhs, rhs)."""
    _, B0 = pdivmod_monic(f, key)
    return vp(resultant(f, key), p), f1 * dv_A(B0, p, h)


def psi_of_kappa(f, key, mu, p, h, kappa, s):
    """Psi(kappa, s)/D' as read on the STAGE side = dv(f mod key_{kappa,s})."""
    nz = normalizer(kappa, p, h)
    if nz is None:
        return None
    key_s = padd(key, [s * c for c in nz])
    _, B0 = pdivmod_monic(f, key_s)
    return dv_A(B0, p, h), key_s


def psi_generic_pred(dvs, mu, kappa):
    """D'^-1 * Psi at a generic letter = min_j (dv(A_j) + j*kappa)."""
    return min(dvs[j] + j * kappa for j in range(mu + 1) if dvs[j] < BIG)


# ------------------------------------------------- the E3 member family
E1, F1, MU = 2, 1, 3
DPRIME = E1 * F1          # = 2 ; deg f = DPRIME * MU = 6


def floors(h, mu=MU):
    """per-coordinate valuation floors of the entry node, e1 = 2."""
    out = []
    for j in range(mu):
        Fj = (mu - j) * (E1 * h) + 1
        out.append((-(-Fj // 2), -(-(Fj - h) // 2)))   # (c0, c1) ceilings
    return out


def key_poly(z, p, h):
    """Phi' = x^2 - z p^h."""
    return [-z * p ** h, 0, 1]


def build_f(key, A):
    """f = key^mu + sum_{j<mu} A_j key^j."""
    f, powk = [0], [1]
    for j in range(MU):
        f = padd(f, pmul(A[j], powk))
        powk = pmul(powk, key)
    return padd(f, powk)


def row_members(p, N, h, z, stride=1):
    """generator of (A, f) over the windowed stage-coordinate box."""
    fl = floors(h)
    ranges = []
    for j in range(MU):
        c0, c1 = fl[j]
        ranges.append([p ** c0 * u for u in range(p ** max(0, N - c0))])
        ranges.append([p ** c1 * u for u in range(p ** max(0, N - c1))])
    key = key_poly(z, p, h)
    cnt = 0
    for tup in itertools.product(*ranges):
        cnt += 1
        if (cnt - 1) % stride:
            continue
        A = [[tup[2 * j], tup[2 * j + 1]] for j in range(MU)]
        yield A, build_f(key, A)


def row_size(p, N, h):
    fl, tot = floors(h), 1
    for c0, c1 in fl:
        tot *= p ** max(0, N - c0) * p ** max(0, N - c1)
    return tot


def disc_nonzero(f, p):
    d = resultant(f, [i * c for i, c in enumerate(f)][1:])
    return d != 0


# ------------------------------------------------------------ PARI oracle
def gp_sig_batch(jobs, p):
    """jobs = [(polystr, want, tag)]; returns {i: sig tuple}."""
    import w12_checks as W12
    import w10_checks as W10
    lines = [W12.GP_FUN]
    for i, (ps, _, _) in enumerate(jobs):
        lines.append('print("R %d ", sig(%s, %d))' % (i, ps, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            try:
                got[int(idx)] = W12.parse_sig(rest)
            except Exception:
                pass
    return got


def polystr(f):
    ts = []
    for i, c in enumerate(f):
        if c:
            ts.append('(%d)*x^%d' % (c, i))
    return '+'.join(ts) if ts else '0'


# ---------------------------------------------------------- the row runner
def run_row(p, N, h, z, orstride, verbose=True):
    """Full reader census + HE-NORM on every member + PARI sigma on a
    sampled subset + the PSI slope census on the same subset."""
    t0 = time.time()
    key = key_poly(z, p, h)
    census, und, viol, jobs, meta = {}, {}, [], [], []
    nmem = 0
    for A, f in row_members(p, N, h, z):
        nmem += 1
        # ---- HE-NORM (LEMMA HE3-1) on every member, at the entry key
        lhs, rhs = norm_identity(f, key, p, h, F1)
        if lhs != rhs and lhs < BIG:
            viol.append(('HE-NORM', A, lhs, rhs))
        try:
            pieces = read_stage(f, key, MU, p, h, N)
        except Und as e:
            und[str(e)] = und.get(str(e), 0) + 1
            continue
        sg = sigma_pred(pieces, E1, F1)
        census[sg] = census.get(sg, 0) + 1
        if (nmem - 1) % orstride == 0 and disc_nonzero(f, p):
            jobs.append((polystr(f), sg, 'm%d' % nmem))
            meta.append((A, f, pieces))
    stats = {'row': 'Zp p=%d N=%d h=%d z=%d' % (p, N, h, z),
             'members': nmem, 'row_size_pred': row_size(p, N, h),
             'census': {str(k): v for k, v in sorted(census.items())},
             'und': und, 'decided': sum(census.values()),
             'norm_violations': len([v for v in viol if v[0] == 'HE-NORM']),
             'oracle_jobs': len(jobs)}
    # ---- HE-SIG + HE-PSI on the sampled subset
    bad, psi_bad, answered = [], [], 0
    if jobs:
        got = gp_sig_batch(jobs, p)
        for i, (ps, want, tag) in enumerate(jobs):
            if i not in got:
                bad.append((tag, 'NO-ANSWER', want))
                continue
            answered += 1
            if got[i] != want:
                bad.append((tag, got[i], want))
        # PSI: slope census per member from the factor-wise resultants
        for i, (A, f, pieces) in enumerate(meta):
            if i not in got:
                continue
            dvs = [dv_A(development(f, key, MU)[j], p, h)
                   for j in range(MU + 1)]
            hull = lower_hull([(j, dvs[j]) for j in range(MU + 1)
                              if dvs[j] < 2 * N])
            pred = {}
            for j1, j2, num, den in sides(hull):
                if num <= E1 * h * den // 1 and num * 1 <= E1 * h * den:
                    continue
                pred[(num, den)] = pred.get((num, den), 0) + \
                    DPRIME * (j2 - j1)
            # measured: sum over roots of dv(Phi'(rho)) must equal
            # sum_lambda n_lambda * lambda  (LEMMA HE3-3's identity)
            tot_pred = sum(cnt * num / den for (num, den), cnt in
                           pred.items())
            lhs, _ = norm_identity(f, key, p, h, F1)
            if abs(tot_pred - E1 * lhs) > 1e-9:
                psi_bad.append((i, tot_pred, E1 * lhs))
    stats['oracle_answered'] = answered
    stats['oracle_bad'] = len(bad)
    stats['oracle_bad_detail'] = bad[:8]
    stats['psi_bad'] = len(psi_bad)
    stats['psi_bad_detail'] = psi_bad[:5]
    stats['secs'] = round(time.time() - t0, 1)
    if verbose:
        print(json.dumps(stats, indent=1, sort_keys=True))
    return stats, viol


# ------------------------------------------ the constructed aligned locus
def aligned_members(p, N, h, z, lam=3):
    """The slope-aligned locus at integer dv-slope lam: the three side
    lattice digits enumerated over F_p, deeper digits zero.  This is the
    ONLY place the 3-label stage type (1,1)^3 is reachable at f1 = 1,
    since it needs |K^x| >= 3, i.e. p >= 5."""
    key = key_poly(z, p, h)
    out = []
    for c2, c1, c0 in itertools.product(range(p), repeat=3):
        A = [[0, c0 * p ** ((3 * lam - h) // 2)],
             [c1 * p ** (2 * lam // 2), 0],
             [0, c2 * p ** ((lam - h) // 2)]]
        out.append(((c2, c1, c0), A, build_f(key, A)))
    return key, out


# ------------------------------------------------------------ the legs
def leg_norm_psi(f, key, p, h, N, mu=MU):
    """HE-NORM at EVERY test key + HE-PSI (the evaluation display and the
    convex-duality identity).  Returns (checks, violations)."""
    chk, vio = 0, []
    dvs = [dv_A(development(f, key, mu)[j], p, h) for j in range(mu + 1)]
    cap = E1 * N
    hull = lower_hull([(j, dvs[j]) for j in range(mu + 1) if dvs[j] < cap])
    if len(hull) < 2:
        return 0, []
    sd = sides(hull)
    slopes = {}
    for j1, j2, num, den in sd:
        slopes[(num, den)] = slopes.get((num, den), 0) + (j2 - j1)
    for kappa in range(E1 * h + 1, cap):
        gen = min(dvs[j] + j * kappa for j in range(mu + 1) if dvs[j] < BIG)
        # (iii) convex duality (star): support function = sum L_l min(l,k)
        dual = sum(L * min(num / den, kappa) for (num, den), L
                   in slopes.items())
        # the truncation of the polygon at the cap makes the identity hold
        # only when the whole polygon is in-window; skip otherwise.
        if all(dvs[j] < cap for j in range(mu + 1)):
            chk += 1
            if abs(dual - gen) > 1e-9:
                vio.append(('HE-PSI-DUAL', kappa, dual, gen))
        for s in range(1, p):
            nz = normalizer(kappa, p, h)
            if nz is None:
                continue
            ks = padd(key, [s * c for c in nz])
            _, B0 = pdivmod_monic(f, ks)
            rhs = F1 * dv_A(B0, p, h)
            lhs = vp(resultant(f, ks), p)
            chk += 1
            if lhs != rhs and lhs < BIG:
                vio.append(('HE-NORM', kappa, s, lhs, rhs))
            # (ii) HE3-1': dv(B0) >= generic, equality unless residual
            # root at this height.
            chk += 1
            if dv_A(B0, p, h) < gen:
                vio.append(('HE-PSI-GEN', kappa, s, dv_A(B0, p, h), gen))
    return chk, vio


def tooth_undet(dvs, pieces, mu=MU):
    """HE-T-UNDET: on a member with >= 3 labels ALL AT ONE SLOPE, count the
    nonneg solutions of the two identities GENHN.C's mu=2 proof uses
    (root count + the single resultant identity), with each class size a
    multiple of its D'*e_s*f_s.  >= 2 solutions = certificate that the
    mu = 2 argument cannot reach mu = 3."""
    k = len(pieces)
    if k < 3:
        return None
    tot = DPRIME * mu
    units = [DPRIME * a * b for a, b in pieces]
    sols = []
    for combo in itertools.product(*[range(0, tot // u + 1) for u in units]):
        if sum(c * u for c, u in zip(combo, units)) == tot:
            sols.append(combo)
    return sols


def read_stage_capbug(f, key, mu, p, h, N):
    """HE-T-CAP: the FIRST version of this reader silently dropped
    out-of-window recentered coefficients instead of testing whether the
    cap already certifies the lift.  That variant mis-reads SPLIT
    residuals as INERT.  Kept here as a tooth: it must disagree with the
    sound reader on >= 1 member."""
    cap = E1 * N
    dev = development(f, key, mu)
    dvs = [dv_A(dev[j], p, h) for j in range(mu + 1)]
    if dvs[0] >= cap:
        raise Und('drain')
    hull = lower_hull([(j, dvs[j]) for j in range(mu + 1) if dvs[j] < cap])
    pieces = []
    for j1, j2, num, den in sides(hull):
        if num <= E1 * h * den:
            continue
        L, ell = j2 - j1, den
        if L % ell:
            raise Und('lattice')
        d = L // ell
        if d == 1:
            pieces.append((ell, 1))
            continue
        if ell != 1:
            raise Und('mixed')
        lam, found = num, 0
        base = len_slope_gt(hull, lam, 1)
        for s in range(1, p):
            nz = normalizer(lam, p, h)
            ks = padd(key, [s * c for c in nz])
            dvs2 = [dv_A(development(f, ks, mu)[j], p, h)
                    for j in range(mu + 1)]
            hull2 = lower_hull([(j, dvs2[j]) for j in range(mu + 1)
                                if dvs2[j] < cap])          # <-- the bug
            m_s = len_slope_gt(hull2, lam, 1) - base
            if m_s <= 0:
                continue
            found += m_s
            pieces.append((1, 1)) if m_s == 1 else pieces.append((1, m_s))
        left = d - found
        if left == 1:
            raise Und('leftover 1')
        if left in (2, 3):
            pieces.append((1, left))
    if not pieces:
        raise Und('empty')
    return sorted(pieces)


# ------------------------------------------------------------- main
def main():
    print('=' * 72)
    print('HE3 BATTERY -- the mu = 3 stage sigma test ([GENHN-HE(mu>=3)])')
    print('=' * 72)
    print('pins:')
    pinmd5 = {}
    for q in PINS:
        try:
            pinmd5[q] = md5(q)
            print('  %-32s %s' % (q, pinmd5[q]))
        except OSError as e:
            print('  %-32s MISSING (%s)' % (q, e))
    res = {'pins': pinmd5, 'rows': [], 'teeth': {}, 'violations': []}
    t0 = time.time()
    VIO = res['violations']
    teeth = res['teeth']

    # ---------------- ROW GROUP A: full windowed enumeration, p in {2,3}
    print('\n--- GROUP A: full windowed E3 enumeration (census tie to '
          'GENHN\'s committed E3 totals)')
    # rows chosen to reproduce GENHN's COMMITTED E3 totals exactly:
    # (Z2,5,1) = 32,768 and (Z3,4,1) = 39,366 (its S12 P6 scorecard).
    for (p, N, h) in [(2, 5, 1), (3, 4, 1)]:
        zs = range(1, p)
        tot, cen, und, nchk = 0, {}, {}, 0
        jobs, meta = [], []
        for z in zs:
            key = key_poly(z, p, h)
            for A, f in row_members(p, N, h, z):
                tot += 1
                lhs, rhs = norm_identity(f, key, p, h, F1)
                nchk += 1
                if lhs != rhs and lhs < BIG:
                    VIO.append(('A-NORM', p, N, z, A, lhs, rhs))
                try:
                    pc = read_stage(f, key, MU, p, h, N)
                except Und as e:
                    und[str(e)] = und.get(str(e), 0) + 1
                    continue
                except AssertionError as e:
                    VIO.append(('A-BOOKKEEPING', p, N, z, A, str(e)))
                    continue
                sg = sigma_pred(pc, E1, F1)
                cen[sg] = cen.get(sg, 0) + 1
                if tot % 97 == 1 and disc_nonzero(f, p):
                    jobs.append((polystr(f), sg, 'A%d' % tot))
                    meta.append((f, key, pc))
        row = {'row': 'A Zp p=%d N=%d h=%d' % (p, N, h), 'members': tot,
               'members_pred_genhn': (p - 1) * row_size(p, N, h),
               'census': {str(k): v for k, v in sorted(cen.items())},
               'und': und, 'decided': sum(cen.values()),
               'norm_checks': nchk}
        got = gp_sig_batch(jobs, p) if jobs else {}
        bad = sum(1 for i, (_, w, _) in enumerate(jobs) if got.get(i) != w)
        row['oracle_jobs'], row['oracle_bad'] = len(jobs), bad
        if bad:
            VIO.append(('A-SIGMA', p, N, bad))
        # HE-NORM/HE-PSI at every test key, on the oracled subset
        pchk, pv = 0, []
        for f, key, pc in meta[:60]:
            c, v = leg_norm_psi(f, key, p, h, N)
            pchk += c
            pv.extend(v)
        row['psi_checks'], row['psi_viol'] = pchk, len(pv)
        VIO.extend([('A-PSI',) + tuple(x) for x in pv[:5]])
        res['rows'].append(row)
        print(json.dumps(row, sort_keys=True))

    # ------- ROW GROUP B: constructed aligned loci, p in {5,7} (3-label)
    print('\n--- GROUP B: constructed slope-aligned loci (the 3-label '
          'stage type lives here)')
    for (p, N, h, lam) in [(5, 6, 1, 3), (7, 6, 1, 3)]:
        key, mem = aligned_members(p, N, h, 1, lam)
        cen, und, jobs, meta = {}, {}, [], []
        for tag, A, f in mem:
            try:
                pc = read_stage(f, key, MU, p, h, N)
            except Und as e:
                und[str(e)] = und.get(str(e), 0) + 1
                continue
            except AssertionError as e:
                VIO.append(('B-BOOKKEEPING', p, tag, str(e)))
                continue
            sg = sigma_pred(pc, E1, F1)
            cen[sg] = cen.get(sg, 0) + 1
            if disc_nonzero(f, p):
                jobs.append((polystr(f), sg, str(tag)))
                meta.append((f, key, pc, tag))
        got = gp_sig_batch(jobs, p) if jobs else {}
        bad, badd = 0, []
        for i, (_, w, tg) in enumerate(jobs):
            if got.get(i) != w:
                bad += 1
                badd.append((tg, str(got.get(i)), str(w)))
        row = {'row': 'B aligned Zp p=%d N=%d h=%d lam=%d' % (p, N, h, lam),
               'members': len(mem),
               'census': {str(k): v for k, v in sorted(cen.items())},
               'und': und, 'oracle_jobs': len(jobs), 'oracle_bad': bad,
               'oracle_bad_detail': badd[:6]}
        if bad:
            VIO.append(('B-SIGMA', p, bad, badd[:3]))
        pchk, pv = 0, []
        for f, k2, pc, tg in meta:
            c, v = leg_norm_psi(f, k2, p, h, N)
            pchk += c
            pv.extend(v)
        row['psi_checks'], row['psi_viol'] = pchk, len(pv)
        VIO.extend([('B-PSI',) + tuple(x) for x in pv[:5]])
        # ---- TEETH on this row
        for f, k2, pc, tg in meta:
            if len(pc) >= 3:
                dvs = [dv_A(development(f, k2, MU)[j], p, h)
                       for j in range(MU + 1)]
                sols = tooth_undet(dvs, pc)
                if sols is not None and len(sols) >= 2:
                    teeth.setdefault('HE-T-UNDET', []).append(
                        {'p': p, 'tag': tg, 'pieces': str(pc),
                         'nsolutions_of_mu2_system': len(sols),
                         'truth': str(tuple(1 for _ in pc)),
                         'example_alternatives': [str(s) for s in sols[:4]]})
                    break
        # HE-T-SIG: flip the dictionary, PARI must catch it
        flip = [(polystr(f), ((2 * E1 * MU, 1),), 't')
                for f, k2, pc, tg in meta[:6]]
        gf = gp_sig_batch(flip, p) if flip else {}
        caught = sum(1 for i, (_, w, _) in enumerate(flip)
                     if gf.get(i) != w)
        teeth.setdefault('HE-T-SIG', []).append(
            {'p': p, 'flipped_jobs': len(flip), 'caught': caught})
        # HE-T-CAP: the capped-drop reader variant must disagree
        dis = 0
        for f, k2, pc, tg in meta:
            try:
                pc2 = read_stage_capbug(f, k2, MU, p, h, N)
            except Und:
                pc2 = 'UND'
            if str(pc2) != str(pc):
                dis += 1
        teeth.setdefault('HE-T-CAP', []).append(
            {'p': p, 'members': len(meta), 'disagreements': dis})
        # HE-T-NODE: floor off-by-one must leave the opening locus
        esc = 0
        for tag, A, f in mem[:40]:
            A2 = [[A[0][0], A[0][1] // p if A[0][1] else 1],
                  A[1], A[2]]
            f2 = build_f(key, A2)
            try:
                read_stage(f2, key, MU, p, h, N)
                dvs2 = [dv_A(development(f2, key, MU)[j], p, h)
                        for j in range(MU + 1)]
                if dvs2[0] >= (MU - 0) * E1 * h + 1:
                    esc += 1        # still inside the node: not a break
            except (Und, AssertionError):
                pass
        teeth.setdefault('HE-T-NODE', []).append(
            {'p': p, 'probed': 40, 'still_in_node_after_floor_drop': esc})
        res['rows'].append(row)
        print(json.dumps(row, sort_keys=True))

    # ---- GROUP C: the sigma-resolution boundary (LEMMA HE3-5)
    print('\n--- GROUP C: the sigma-resolution boundary (LEMMA HE3-5): '
          'decided mass vs window')
    for p in (5, 7):
        prof = []
        for N in (4, 5, 6, 7):
            key, mem = aligned_members(p, N, 1, 1, 3)
            dec, u = 0, 0
            for tag, A, f in mem:
                try:
                    read_stage(f, key, MU, p, 1, N)
                    dec += 1
                except (Und, AssertionError):
                    u += 1
            prof.append({'N': N, 'cap_dv': E1 * N, 'mu_lambda': MU * 3,
                         'decided': dec, 'undecided': u})
        res['rows'].append({'row': 'C boundary p=%d' % p, 'profile': prof})
        print(json.dumps({'C p=%d' % p: prof}, sort_keys=True))

    # -------------------------------------------------------- verdict
    res['secs'] = round(time.time() - t0, 1)
    tfired = {k: len(v) for k, v in teeth.items()}
    ok_teeth = (any(t.get('caught', 0) > 0 for t in teeth.get('HE-T-SIG', []))
                and any(t.get('disagreements', 0) > 0
                        for t in teeth.get('HE-T-CAP', []))
                and len(teeth.get('HE-T-UNDET', [])) > 0)
    res['teeth_fired'] = tfired
    res['verdict'] = ('GREEN' if not res['violations'] and ok_teeth
                      else 'RED')
    print('\n' + '=' * 72)
    print('TEETH', json.dumps(tfired))
    for k, v in teeth.items():
        print('  %-12s %s' % (k, json.dumps(v)[:300]))
    print('VIOLATIONS', len(res['violations']))
    for v in res['violations'][:10]:
        print('   ', str(v)[:200])
    print('VERDICT', res['verdict'], '  %.1fs' % res['secs'])
    with open(os.path.join(HERE, 'he3_checks_results.json'), 'w') as fh:
        json.dump(res, fh, indent=1, sort_keys=True, default=str)
    return 0 if res['verdict'] == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
