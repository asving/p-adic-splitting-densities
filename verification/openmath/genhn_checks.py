#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
genhn_checks.py -- SEALED BATTERY for GENHN_PROOF_2026-08-08.md
(the general composite-stage law: genre classification at n = 5, 6;
the (e1,f1)-re-based stage law at THREE genres beyond GENH4's two;
the mu = 3 stage; the first stage-TOWER witness at n = 8.)

TWO-COMMIT SEAL.  Commit 1 = this runner + the note with S11
preregistered; commit 2 = verdict appended FROM the committed
artifacts (genhn_checks_output.txt / genhn_checks_results.json).

DISCLOSED CONVENTIONS / SCOPING:
 * conservative tails everywhere (UND / UND3 exits; no sigma there).
 * fresh frame reader (this file) with FULL residual factorization
   (trial division over F_p, p in {2,3}) -- the pinned GENIND reader
   cannot parse n = 6 genres (its residual analysis is n <= 5); the
   two readers are compared event-for-event on the n = 5 rows.
 * embedded n = 5 stage rows are read through Newton root extraction
   + exact division + the PINNED QSCOUT22 reader (read22); law legs
   use genh4's law_E (pinned) AND this file's own law_Egen
   transcription (tied to law_E at e1 = 2 on a grid).
 * mu = 3 stage read = depth-0 species + alpha-chain only (stage-beta
   'S3BETA' and UND3 are conservative exits, no sigma) -- GENHN's
   displayed scoping; sigma at mu = 3 decided leaves is emitted as
   the [GENHN-HE(3)] PREDICTION and PARI-checked (corroboration of an
   OPEN box, labeled as such).
 * f-first n = 6 genres (F3/E13) are visibility-floored beyond every
   sweep window here (first visible N = 7): checked PREDICTED-ABSENT
   only (GENHN-BOX-3 coverage box).
 * n = 6 (Zp,2,5) 16.7M sweep DROPPED for runtime budget (disclosed);
   the (2,4)/(3,3) sweeps + constructed loci carry n = 6.
 * oracle legs mixed-characteristic (PARI) only, sampled by step.

FAMILIES (evidence class):
  GN-PIN    [NONE] md5 pins of 7 frozen artifacts
  GN-CLASS  [SAME] n=5/n=6 sweep genre classification: grammar at all
            depths, flagship tallies at preregistered entry-law
            values, visibility floors (incl. PREDICTED-ABSENT),
            genind-reader event tie on the n=5 rows
  GN-LAWTIE [SAME] law_Egen(e1=2) == pinned law_E on a (q,N,h) grid
  GN-FIB    [SAME] E3/E31 constructed loci: construction count ==
            entry law; development budgets + node floors pointwise
  GN-STAGE2 [SAME] the mu=2 stage law at THREE fresh genres:
            V1E2 (n=5; incl. the GENIND committed row 12,288),
            V4E2 (n=5; FIRST measurement, GENIND's law was
            derivation-only), E31 (n=6, e1=3): per-key counts ==
            (e1,f1)-re-based law x sibling fiber, both directions
  GN-E3     [SAME] the mu=3 stage (n=6): species partition, RAM3 /
            ALPHA3 / UND3 preregistered laws, alpha-chain
  GN-REFINE3[SAME] pointwise mu=3 refine transport: at every stage
            alpha event the recentering + re-division kills all
            three pins and lands in the floored node
  GN-TOWER  [SAME] criterion: zero stage-CS on every mu<=3 stage
            read; the n=8 constructed witness fires stage-CS
            (2,1,2)-inside-(2,1,4); min-n scan == 8
  GN-SIGMA  [IND]  PARI sigma vs dictionary on Zp rows (sampled):
            V1E2/V4E2 (composed with the split (1,1)) SCORED ONLY on
            the extraction-certified perimeter (cert_table_E /
            leaf_cert_E -- the smoke finding; uncertified deep tail
            emitted as measured diagnostics), E31
            ({(6,1)}/{(3,1)^2}/{(3,2)}, incl. WILD p=3 with e1=3,
            un-gated: full-side, no extraction), E3 depth-0-decided
            (un-gated; [GENHN-HE(3)] corroboration)
PROVENANCE (disclosed): drafted by the interrupted prior incarnation
of the GENHN composer; re-audited line-by-line as an UNTRUSTED draft
by the fresh continuation (2026-08-08) with the count laws, twist
corrections (E31 i1=2 wrap zinv; E3/tower wrap exponent g_t), node
floors, flagship volumes (12,288 / 8,192 / 512 / 4,374), and the
tower witness residual ((T-1)^4 over F_3; inner side rc=[1,1,1] =
(T-1)^2) re-derived by hand.  ADOPTED with two repairs: R1
(kp_factor_full irreducible table 4 -> 6, latent crash on legitimate
quintic/sextic irreducible residuals) and R2 (genre_name gains
V1E1Q/V4E1Q/FULLQ so the n=5 PREDICTED-ABSENT checks are real and
the tie-key seam vs cs_genre_key is closed).  SMOKE RECORD (wiring
only, artifacts not written; pre-seal, disclosed): smoke 1 post-
repair went RED with 6 GN-SIGMA mismatches, ALL at (Zp,2,5,1) V1E2
RAM(9) -- the discovery event for the extraction-certified sigma
perimeter (see cert_table_E below and note S11.F); the E31/E3
full-side legs were 0-bad.  A lift-perturbation probe confirmed the
RAM(5)/RAM(7)/RAM(9) certified/uncertified split exactly at the
derived floors.  Smoke 2 with the certification gate: GREEN --
1,081,425 checks, 0 violations, all 5 teeth fired, certified sigma
720/720, diagnostic tail 24 jobs / 6 mismatches (50.8s).  No full
row was run before seal; every full-battery prediction in S11 was
fixed before the first full run.

TEETH (each must fire >= 1 or the battery is RED):
  GN-T-LAT  law_Egen at E31 collapsed to ladder density 1 (class-0
            slots only) must mismatch every E31 row
  GN-T-CEN  INERT census q(q-1)/2 -> q(q-1) must mismatch every row
            realizing an INERT key
  GN-T-SIG  E31 RAM sigma {(6,1)} -> {(3,2)} must be caught by PARI
  GN-T-CRIT the grammar with the bound e*gam*mu >= 4 dropped to >= 3
            must reject a synthesized mu=3 e=gam=1 record on every
            sweep row that realizes a (3)-child
  GN-T-NODE the E3 construction with the a00 floor off by one (the
            GH-FEVEN bug class) must break the entry-law volume
"""

import sys, os, json, time, hashlib, itertools
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import genind_checks as G
import qscout22_checks as Q
import genh4_checks as H4
import w10_checks as W10
import w12_checks as W12

PINS = {
    'genind_checks.py': 'e7ca150b1b5cb13ad4f3350ac776aca2',
    'genh4_checks.py': 'ee8024b7a500220a6408dab373d7432f',
    'qscout22_checks.py': 'cb885663dd4ef6dfda9c28a67c1a076e',
    'w10_checks.py': 'a9c34244a3af19f5fa864375b494380b',
    'w12_checks.py': '7dc040d94fbbb1e8d20ac817b665d418',
    'genind_checks_results.json': '366f214322fee97c9669f0584696b3f6',
    'qscout22_results.json': '6c2441a12cf52ffd43055de912a4affe',
}

FAMILIES = ['GN-PIN', 'GN-CLASS', 'GN-LAWTIE', 'GN-FIB', 'GN-STAGE2',
            'GN-E3', 'GN-REFINE3', 'GN-TOWER', 'GN-SIGMA']
TEETH = ['GN-T-LAT', 'GN-T-CEN', 'GN-T-SIG', 'GN-T-CRIT', 'GN-T-NODE']
VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
LOG = []


def say(m):
    print(m)
    sys.stdout.flush()
    LOG.append(m)


def note(f, n=1):
    NCHK[f] += n


def viol(f, tag, d):
    VIOL[f].append((tag, d))
    say('  !! VIOLATION [%s/%s] %s' % (f, tag, d))


# ===================================================================
# F_p polynomial full factorization (trial division; p small, deg<=8)
# ===================================================================
def kp_monics(p, d):
    for tail in itertools.product(range(p), repeat=d):
        yield list(tail) + [1]


def kp_irreducibles(p, maxdeg):
    out = []
    for d in range(1, maxdeg + 1):
        for f in kp_monics(p, d):
            if all(G.kp_divmod(f, g, p)[1] for g in out
                   if len(g) - 1 <= d // 2):
                out.append(f)
    return out


_IRR = {}


def kp_factor_full(C, p):
    """monic C over F_p -> list of (irr poly tuple, mult).
    [audit repair R1] irreducible table to degree 6 (was 4): a
    legitimate irreducible quintic/sextic residual would have crashed
    the completeness assert.  (Window analysis says degree <= 4 on
    every row of THIS battery -- e=1 sides of length L need
    L*h <= W-1 <= 4 and child windows shrink -- but the reader
    should be honest for any row.)"""
    C = G.kp_trim(list(C))
    if p not in _IRR:
        _IRR[p] = kp_irreducibles(p, 6)
    out = []
    for g in _IRR[p]:
        if len(g) - 1 > len(C) - 1:
            break
        m = 0
        while len(C) - 1 >= len(g) - 1:
            qq, r = G.kp_divmod(C, g, p)
            if r:
                break
            C, m = qq, m + 1
        if m:
            out.append((tuple(g), m))
    assert len(C) - 1 == 0, 'incomplete factorization'
    return out


# ===================================================================
# THE FRESH FRAME READER (n <= 6; genind rings; full residuals)
# ===================================================================
def read6(R, W, coeffs, ctx, depth0=None):
    """conservative read; coeffs=[a0..a(m-1)] monic; ctx: p, cs, beta3.
    Returns (verdict, sigma)."""
    p = ctx['p']
    m = len(coeffs)
    it = 0
    first = True
    while True:
        it += 1
        assert it <= 6 * W + 12, 'read loop cap'
        if R.val(coeffs[0], W) is None:
            if first and depth0 is not None:
                depth0.append(('DRAIN',))
            return 'DRAIN', None
        sides = G.sides_of(R, W, coeffs, m)
        pieces, children, cs = [], [], []
        for (j0, y0, j1, y1, e, h, g, rc) in sides:
            for (fac, mu) in kp_factor_full(rc, p):
                gam = len(fac) - 1
                if mu == 1:
                    pieces.append((e, gam))
                elif e == 1 and gam == 1:
                    z = (-fac[0]) % p
                    assert z != 0 or j0 > 0, 'zero residual root'
                    children.append((mu, h, z, j0, y0))
                else:
                    cs.append((m, (j0, j1), e, gam, mu, h,
                               tuple((s[0], s[1], s[2], s[3])
                                     for s in sides)))
        is_alpha = (len(sides) == 1 and sides[0][4] == 1 and
                    len(children) == 1 and children[0][0] == m and
                    not pieces and not cs)
        if first and depth0 is not None:
            if cs:
                depth0.append(('CS', genre_name(m, cs[0])))
            elif is_alpha:
                depth0.append(('ALPHA', children[0][1]))
            elif children:
                depth0.append(('BETA',
                               tuple(sorted((c[0] for c in children),
                                            reverse=True)),
                               tuple(sorted(pieces))))
            else:
                depth0.append(('DEC',))
        first = False
        if children and max(c[0] for c in children) >= 3:
            ctx['beta3'] = ctx.get('beta3', 0) + 1
        if cs:
            ctx['cs'].extend(cs)
            return 'CS', None
        if not children:
            return 'DEC', tuple(sorted(pieces))
        if is_alpha:
            (mu, k, z, _, _) = children[0]
            s = R.mul(R.lift(z), R.pipw(k))
            full = list(coeffs) + [R.one()]
            coeffs = G.poly_shift(R, full, s)[:m]
            continue
        verdicts = []
        for (mu, k, z, j0, y0) in children:
            child, Wc = G.extract_child(R, W, coeffs, m, k, z, p)
            verdicts.append(read6(R, Wc, child, ctx))
        if any(v == 'CS' for v, _ in verdicts):
            return 'CS', None
        if any(v == 'DRAIN' for v, _ in verdicts):
            return 'DRAIN', None
        sig = list(pieces)
        for v2, s2 in verdicts:
            sig.extend(list(s2))
        return 'DEC', tuple(sorted(sig))


def genre_name(m, rec):
    (_, (j0, j1), e, gam, mu, h, sides) = rec
    if m == 4 and (j0, j1) == (0, 4):
        return ('E4', h) if e == 2 else ('F4', h)
    if m == 5 and (j0, j1) == (1, 5) and (e, gam, mu) == (2, 1, 2):
        return ('V1E2', h)
    if m == 5 and (j0, j1) == (0, 4) and (e, gam, mu) == (2, 1, 2):
        v4 = [s[3] for s in sides if (s[0], s[2]) == (0, 4)][0]
        return ('V4E2', v4, h)
    if m == 5 and (e, gam, mu) == (1, 2, 2):
        # [audit repair R2] the quadratic-residual n=5 genres, named
        # to match the pinned reader's cs_genre_key: without these the
        # PREDICTED-ABSENT checks were vacuous-by-construction and the
        # tie-key check had a latent mismatch seam.
        if (j0, j1) == (1, 5):
            return ('V1E1Q', h)
        if (j0, j1) == (0, 4):
            return ('V4E1Q', h)
        if (j0, j1) == (0, 5):
            return ('FULLQ', h)
    if m == 6 and (j0, j1) == (0, 6):
        key = {(2, 1, 3): 'E3', (3, 1, 2): 'E31',
               (1, 2, 3): 'F3', (1, 3, 2): 'E13',
               (2, 1, 2): 'E2X', (1, 2, 2): 'F2X'}.get((e, gam, mu))
        if key:
            return (key, h)
    return ('EMB', m, (j0, j1), e, gam, mu, h)


def grammar_ok(rec, n, N, loose=False):
    """structural genre grammar; the loose (GN-T-CRIT corrupt) variant
    drops the e*gam >= 2 clause and the >= 4 budget to >= 3, i.e. it
    would accept an order-1 (3)-child as a composite opening."""
    (m, (j0, j1), e, gam, mu, h, sides) = rec
    if loose:
        if mu < 2 or e * gam * mu < 3:
            return False
    elif mu < 2 or e * gam < 2 or e * gam * mu < 4:
        return False
    if e * gam * mu > m or m > n:
        return False
    if (j1 - j0) < e * gam * mu:
        return False
    return True


# ===================================================================
# law_Egen: the (e1, f1=1) re-based mu=2 stage law (own transcription)
# ===================================================================
def ceil_div(a, b):
    return -((-a) // b)


def slots_gen(q, N, h, e1, coord):
    """dv slot list for A_coord (coord in {1, 0}), e-first genre."""
    out = []
    for i in range(e1):
        if i == 0:
            fl = h + 1 if coord == 1 else 2 * h + 1
        else:
            fl = ceil_div(((2 - coord) * e1 - i) * h, e1)
        for v in range(fl, N):
            out.append(e1 * v + i * h)
    return sorted(out)


def law_Egen(q, N, h, e1, integer_only=False, inert_c=None):
    """per (center, entry letter): dict (H2, leaf, params) -> count."""
    A1all = slots_gen(q, N, h, e1, 1)
    A0all = slots_gen(q, N, h, e1, 0)
    if integer_only:
        A1all = [s for s in A1all if s % e1 == 0]
        A0all = [s for s in A0all if s % e1 == 0]
    cap = e1 * N
    c11 = (q - 1) * (q - 2) // 2
    c2 = q * (q - 1) // 2 if inert_c is None else inert_c
    out = {}

    def put(k, v):
        if v:
            out[k] = out.get(k, 0) + v

    def rec(f1, f0, wt, H2):
        A1 = [s for s in A1all if s > f1]
        A0 = [s for s in A0all if s > f0]
        deep0 = len([s for s in A0 if s >= cap])
        for dv1 in A1:
            if 2 * dv1 < cap:
                put((H2, 'SPLTAIL', (dv1,)), wt * (q - 1)
                    * q ** (deep0 + len([s for s in A1 if s > dv1])))
        put((H2, 'UND', ()),
            wt * q ** (deep0 + len([s for s in A1 if 2 * s >= cap])))
        for dv0 in A0:
            if dv0 >= cap:
                continue
            nz0 = len([s for s in A0 if s > dv0])
            if dv0 % 2 == 1:
                put((H2, 'RAM', (dv0,)), wt * (q - 1)
                    * q ** (nz0 + len([s for s in A1 if 2 * s > dv0])))
            for dv1 in A1:
                if 2 * dv1 < dv0:
                    put((H2, '2SIDED', (dv1, dv0 - dv1)),
                        wt * (q - 1) ** 2
                        * q ** (nz0 + len([s for s in A1 if s > dv1])))
            if dv0 % 2 == 0:
                dmu = dv0 // 2
                base = wt * q ** (nz0 + len([s for s in A1 if s > dmu]))
                put((H2, 'SPLITEQ', (dmu,)), base * c11)
                put((H2, 'INERT', (dmu,)), base * c2)
                rec(dmu, dv0, wt * (q - 1), H2 + (dmu,))

    rec(e1 * h, 2 * e1 * h, 1, ())
    if not integer_only and inert_c is None:
        assert sum(out.values()) == q ** (len(A1all) + len(A0all))
    return out


# ===================================================================
# W10-ring helpers (Newton, division, inverses)
# ===================================================================
def runit_inv(R, u):
    if R.kind == 'Zp':
        return pow(u % R.M, -1, R.M)
    K, N = R.K, R.N
    w = [K.zero()] * N
    i0 = K.inv(u[0])
    w[0] = i0
    for t in range(1, N):
        acc = K.zero()
        for i in range(1, t + 1):
            acc = K.add(acc, K.mul(u[i], w[t - i]))
        w[t] = K.neg(K.mul(i0, acc))
    return tuple(w)


def rdivpi(R, a, t):
    if R.kind == 'Zp':
        a = a % R.M
        assert a % (R.p ** t) == 0
        return a // R.p ** t
    assert all(R.K.is_zero(a[i]) for i in range(t))
    return a[t:] + (R.K.zero(),) * t


def peval(R, coeffs, x):
    """f(x), coeffs=[c0..], monic NOT included unless present."""
    acc = Q.rzero(R)
    for c in reversed(coeffs):
        acc = R.add(R.mul(acc, x), c)
    return acc


def newton_root(R, fc, dvf, rho0=None):
    """root of monic f (fc = [b0..b(m-1)] + implicit leading 1) on the
    simple integer-slope segment with v(f'(root)) = dvf; returns rho
    with f(rho) == 0 in R (exactly; see GENHN S11 prereg argument).
    [re-seal fix, disclosed] rho0 = basin start: Newton must begin
    where v(f'(rho)) = dvf already holds.  rho0 = 0 works for V1E2
    (f'(0) = b1 pinned at exactly 2h) but NOT for V4E2 (f'(0) = b1
    has v >= v4+(3h+1)/2 > 4*v4, or b1 = 0): the first full run
    crashed here; V4E2 rows now start at the split-side residual
    root -res(b4, v4)*pi^v4 (dominant balance x^4(x + b4))."""
    one = Q.rint(R, 1)
    full = list(fc) + [one]
    dfull = [R.mul(full[i], Q.rint(R, i)) for i in range(1, len(full))]
    rho = Q.rzero(R) if rho0 is None else rho0
    guard = 0
    lastv = -1
    while True:
        guard += 1
        assert guard <= 8 * R.N + 20, 'newton stall'
        fv = peval(R, full, rho)
        vf = R.val(fv)
        if vf is None:
            return rho
        assert vf > lastv, 'newton no progress'
        lastv = vf
        dfv = peval(R, dfull, rho)
        vd = R.val(dfv)
        assert vd is not None and vd <= dvf, 'newton derivative'
        u = rdivpi(R, dfv, vd)
        step = R.mul(rdivpi(R, fv, vd), runit_inv(R, u))
        rho = Q.rsub(R, rho, step)


def divide_linear(R, fc, rho):
    """f = (x - rho) * (x^{m-1} + c_{m-2} x^{m-2} + ... + c0) exactly;
    fc = [b0..b(m-1)] (+ implicit monic).  Asserts f(rho) = 0."""
    m = len(fc)
    one = Q.rint(R, 1)
    assert R.val(peval(R, list(fc) + [one], rho)) is None, \
        'nonzero remainder'
    cs = [Q.rzero(R)] * (m - 1)
    cs[m - 2] = R.add(fc[m - 1], rho)
    for j in range(m - 2, 0, -1):
        cs[j - 1] = R.add(fc[j], R.mul(rho, cs[j]))
    return cs


def poly_divmod_R(R, f, g):
    """f, g coefficient lists over R (g monic with literal leading
    one); returns (q, r)."""
    f = list(f)
    dg = len(g) - 1
    n = len(f) - 1
    if n < dg:
        return [], f
    qq = [Q.rzero(R)] * (n - dg + 1)
    for s in range(n - dg, -1, -1):
        c = f[s + dg]
        qq[s] = c
        for i in range(dg + 1):
            f[s + i] = Q.rsub(R, f[s + i], R.mul(c, g[i]))
    return qq, f[:dg]


def develop(R, fc, phi, mu):
    """phi-adic development of monic f (fc + implicit 1): returns
    [A0, A1, ..., A_{mu-1}] (each a coeff list of len deg(phi)) and
    the top quotient (must be [~1] for full-side genres)."""
    one = Q.rint(R, 1)
    cur = list(fc) + [one]
    out = []
    for _ in range(mu):
        cur, rem = poly_divmod_R(R, cur, phi)
        rem = rem + [Q.rzero(R)] * (len(phi) - 1 - len(rem))
        out.append(rem)
        # cur becomes the next dividend
    return out, cur


# ===================================================================
# dv + slot digits at pure e-first keys (W10 rings)
# ===================================================================
def dv_gen(R, h, e1, A):
    """A = coeff list (len e1 or e1*f1) at a pure e-first key:
    dv = min_i (e1*v(a_i) + i*h) or None."""
    best = None
    for i, a in enumerate(A):
        v = R.val(a)
        if v is None:
            continue
        c = e1 * v + i * h
        if best is None or c < best:
            best = c
    return best


def zpow(K, z, t):
    out = K.one()
    zi = K.inv(z)
    for _ in range(abs(t)):
        out = K.mul(out, z if t > 0 else zi)
    return out


# ===================================================================
# the E31 stage reader (mu=2, e1=3, K=F_q)
# ===================================================================
SIG_E31 = {'RAM': ((6, 1),), 'INERT': ((3, 2),),
           'SPLITEQ': ((3, 1), (3, 1)), '2SIDED': ((3, 1), (3, 1)),
           'SPLTAIL': ((3, 1), (3, 1)), 'UND': None}


def read_e31(R, K, q, h, z, fc, ctx):
    """order-2 read of the (3,1,2) stage; fc=[b0..b5]+monic.
    Returns (H2, leaf, params)."""
    N = R.N
    cap = 3 * N
    hinv = {1: 1, 2: 2}[h % 3]
    zinv = K.inv(z)
    phi = [K_neg_pi(R, K, z, h), Q.rzero(R), Q.rzero(R), Q.rint(R, 1)]
    H2 = []
    floor0, floor1 = 6 * h, 3 * h
    while True:
        A, top = develop(R, fc, phi, 2)
        A0, A1 = A[0], A[1]
        dv0 = dv_gen(R, h, 3, A0)
        dv1 = dv_gen(R, h, 3, A1)
        if dv1 is not None and dv1 >= cap:
            dv1 = None
        if dv0 is not None and dv0 >= cap:
            dv0 = None
        if dv1 is not None and dv1 <= floor1:
            viol('GN-STAGE2', 'floor1', 'E31 dv1 %d <= %d (H2=%s)'
                 % (dv1, floor1, H2))
        if dv0 is not None and dv0 <= floor0:
            viol('GN-STAGE2', 'floor0', 'E31 dv0 %d <= %d (H2=%s)'
                 % (dv0, floor0, H2))
        if dv0 is None:
            if dv1 is not None and 2 * dv1 < cap:
                return tuple(H2), 'SPLTAIL', (dv1,)
            return tuple(H2), 'UND', ()
        if dv1 is not None and dv0 > 2 * dv1:
            return tuple(H2), '2SIDED', (dv1, dv0 - dv1)
        if dv0 % 2 == 1:
            return tuple(H2), 'RAM', (dv0,)
        dmu = dv0 // 2
        i1 = (dmu * hinv) % 3
        pos1 = (dmu - i1 * h) // 3
        i0 = (dv0 * hinv) % 3
        pos0 = (dv0 - i0 * h) // 3
        if not (0 <= pos1 <= N - 1 and 0 <= pos0 <= N - 1):
            viol('GN-STAGE2', 'slot-dead', 'E31 dmu=%d' % dmu)
            return tuple(H2), 'UND', ()
        S1 = R.res(A1[i1], pos1)
        S0 = R.res(A0[i0], pos0)
        S0eff = K.mul(zinv, S0) if i1 == 2 else S0
        t, root = Q.quad_type(K, S1, S0eff)
        if t == '11':
            return tuple(H2), 'SPLITEQ', (dmu,)
        if t == '2':
            return tuple(H2), 'INERT', (dmu,)
        s = root
        assert not K.is_zero(s), 'zero refine letter'
        phi[i1] = Q.rsub(R, phi[i1],
                         R.mul(R.lift(s), Q.pipow(R, pos1)))
        H2.append(dmu)
        floor0, floor1 = dv0, dmu
        ctx['stage_steps'] = ctx.get('stage_steps', 0) + 1
        assert len(H2) < 4 * N, 'E31 runaway'


def K_neg_pi(R, K, z, h):
    """-z * pi^h in R."""
    return Q.rneg(R, R.mul(R.lift(z), Q.pipow(R, h)))


# ===================================================================
# the E3 stage reader (mu=3, e1=2: depth-0 species + alpha chain)
# ===================================================================
def slot_digit2(R, h, A, ht):
    """K-digit of A=[a0,a1] at doubled height ht (e1=2)."""
    if ht % 2 == 1:
        pos = (ht - h) // 2
        assert pos >= 0, 'slot below key'
        return R.res(A[1], pos)
    return R.res(A[0], ht // 2)


def read_e3(R, K, q, h, z, fc, ctx):
    """the mu=3 stage read: depth-0 species + alpha chain.
    Returns (H3, leaf, params, sigma_or_None)."""
    N = R.N
    cap = 2 * N
    zK = z
    phi = [K_neg_pi(R, K, z, h), Q.rzero(R), Q.rint(R, 1)]
    H3 = []
    S = 2 * h
    floors = [3 * S, 2 * S, S]
    while True:
        A, top = develop(R, fc, phi, 3)
        dv = [dv_gen(R, h, 2, A[j]) for j in range(3)]
        dv = [None if d is not None and d >= cap else d for d in dv]
        for j in range(3):
            if dv[j] is not None and dv[j] <= floors[j]:
                viol('GN-E3', 'floor', 'A%d dv %d <= %d (H3=%s)'
                     % (j, dv[j], floors[j], H3))
        if H3:
            note('GN-REFINE3', 3)      # three pins checked dead
        if dv[0] is None:
            return tuple(H3), 'UND3', (), None
        pts = [(j, dv[j]) for j in range(3) if dv[j] is not None]
        pts.append((3, 0))
        hv = G.hull_lower(pts)
        sigma = []
        alpha_root = None
        beta = False
        sides_keys = []
        for i in range(len(hv) - 1):
            (j0, y0), (j1, y1) = hv[i], hv[i + 1]
            dx, dy = j1 - j0, y0 - y1
            gg = gcd(dx, dy)
            e_s, kk, g = dx // gg, dy // gg, gg
            rc = []
            for t in range(g + 1):
                j = j0 + t * e_s
                ht = y0 - t * kk
                if j == 3:
                    c = K.one()
                else:
                    c = slot_digit2(R, h, A[j], ht)
                # wrap count: (i(m_t) + t*i(kk) - i(y0)) / 2
                g_t = ((ht % 2) + t * (kk % 2) - (y0 % 2)) // 2
                rc.append(K.mul(c, zpow(K, zK, g_t)))
            lead_inv = K.inv(rc[-1])
            rc = [K.mul(c, lead_inv) for c in rc]
            facs = kp_factor_full([int(c) for c in rc], q)
            skey = []
            for (fac, mu_s) in facs:
                gam_s = len(fac) - 1
                if mu_s == 1:
                    sigma.append((2 * e_s, gam_s))
                    skey.append(('P', e_s, gam_s))
                elif e_s * gam_s >= 2:
                    ctx['stage_cs'] = ctx.get('stage_cs', 0) + 1
                    viol('GN-TOWER', 'mu3-cs',
                         'stage-CS at mu=3: %s' % ((e_s, gam_s, mu_s),))
                    skey.append(('CS', e_s, gam_s, mu_s))
                else:
                    if (len(hv) == 2 and e_s == 1 and mu_s == 3):
                        alpha_root = (-fac[0]) % q
                        skey.append(('A',))
                    else:
                        beta = True
                        skey.append(('B', mu_s))
            sides_keys.append((j0, y0, j1, y1, tuple(skey)))
        if alpha_root is not None:
            kappa = (hv[0][1]) // 3
            s = alpha_root
            i1 = kappa % 2
            pos = (kappa - i1 * h) // 2
            phi[i1] = Q.rsub(R, phi[i1],
                             R.mul(R.lift(s), Q.pipow(R, pos)))
            H3.append(kappa)
            floors = [3 * kappa, 2 * kappa, kappa]
            assert len(H3) < 4 * N, 'E3 runaway'
            continue
        if beta:
            return tuple(H3), 'S3BETA', tuple(sides_keys), None
        return (tuple(H3), 'S3DEC', tuple(sides_keys),
                tuple(sorted(sigma)))


# ===================================================================
# constructions (W10 rings)
# ===================================================================
def kunits(K):
    return [e for e in K.elems() if not K.is_zero(e)]


def ef(R, m):
    return Q.elems_with_floor(R, m)


def padd(R, base, free):
    return R.add(base, free)


def gen_V1E2(R, K, q, N, h):
    for z in kunits(K):
        z2 = K.mul(z, z)
        m2z = K.neg(K.add(z, z))
        b1p = R.mul(R.lift(z2), Q.pipow(R, 2 * h))
        b3p = R.mul(R.lift(m2z), Q.pipow(R, h))
        for b0 in ef(R, (5 * h + 1) // 2):
            if R.val(b0) is None:
                continue
            for b1f in ef(R, 2 * h + 1):
                b1 = padd(R, b1p, b1f)
                for b2 in ef(R, (3 * h + 1) // 2):
                    for b3f in ef(R, h + 1):
                        b3 = padd(R, b3p, b3f)
                        for b4 in ef(R, (h + 1) // 2):
                            yield z, [b0, b1, b2, b3, b4]


def gen_V4E2(R, K, q, N, h, v4):
    for z in kunits(K):
        for u in kunits(K):
            zu2 = K.mul(K.mul(z, z), u)
            m2zu = K.neg(K.add(K.mul(z, u), K.mul(z, u)))
            b0p = R.mul(R.lift(zu2), Q.pipow(R, v4 + 2 * h))
            b2p = R.mul(R.lift(m2zu), Q.pipow(R, v4 + h))
            b4p = R.mul(R.lift(u), Q.pipow(R, v4))
            for b0f in ef(R, v4 + 2 * h + 1):
                b0 = padd(R, b0p, b0f)
                for b1 in ef(R, v4 + (3 * h + 1) // 2):
                    for b2f in ef(R, v4 + h + 1):
                        b2 = padd(R, b2p, b2f)
                        for b3 in ef(R, v4 + (h + 1) // 2):
                            for b4f in ef(R, v4 + 1):
                                b4 = padd(R, b4p, b4f)
                                yield z, [b0, b1, b2, b3, b4]


def gen_E31(R, K, q, N, h):
    z2p = lambda z: R.mul(R.lift(K.mul(z, z)), Q.pipow(R, 2 * h))
    m2zp = lambda z: R.mul(R.lift(K.neg(K.add(z, z))), Q.pipow(R, h))
    for z in kunits(K):
        b0p, b3p = z2p(z), m2zp(z)
        for b0f in ef(R, 2 * h + 1):
            b0 = padd(R, b0p, b0f)
            for b1 in ef(R, ceil_div(5 * h, 3)):
                for b2 in ef(R, ceil_div(4 * h, 3)):
                    for b3f in ef(R, h + 1):
                        b3 = padd(R, b3p, b3f)
                        for b4 in ef(R, ceil_div(2 * h, 3)):
                            for b5 in ef(R, ceil_div(h, 3)):
                                yield z, [b0, b1, b2, b3, b4, b5]


def gen_E3(R, K, q, N, h, corrupt_node=False):
    three = Q.rint(R, 3)
    for z in kunits(K):
        z3 = K.mul(K.mul(z, z), z)
        c0 = K.neg(z3)
        c2 = K.mul(K.add(K.add(z, z), z), z)         # 3z^2
        c4 = K.neg(K.add(K.add(z, z), z))            # -3z
        f0 = 3 * h + 1 - (1 if corrupt_node else 0)
        b0p = R.mul(R.lift(c0), Q.pipow(R, 3 * h))
        b2p = R.mul(R.lift(c2), Q.pipow(R, 2 * h))
        b4p = R.mul(R.lift(c4), Q.pipow(R, h))
        for b0f in ef(R, f0):
            b0 = padd(R, b0p, b0f)
            for b1 in ef(R, (5 * h + 1) // 2):
                for b2f in ef(R, 2 * h + 1):
                    b2 = padd(R, b2p, b2f)
                    for b3 in ef(R, (3 * h + 1) // 2):
                        for b4f in ef(R, h + 1):
                            b4 = padd(R, b4p, b4f)
                            for b5 in ef(R, (h + 1) // 2):
                                yield z, [b0, b1, b2, b3, b4, b5]


# ===================================================================
# extraction-certified sigma perimeter (V rows; the smoke finding)
# ===================================================================
# THE FINDING (smoke, disclosed): for EMBEDDED genres the stage block
# is only determined by the ambient window-N data mod the sibling
# Hensel loss: the split root is defined mod pi^(N - v(f'(rho))), so
# the extracted block's coefficients are exact only below explicit
# per-coefficient error floors.  Deep stage leaves that consult
# digits at or above those floors are (A0)-WEAK AT THE AMBIENT
# WINDOW: their sigma is not a function of the window data the sweep
# enumerates.  Smoke instance: (Zp,2,5,1) V1E2 RAM(9) reads the
# a01-digit at v-height 4 >= its floor 4 -> 6/~24 sampled jobs
# mismatched PARI ((4,1) claimed, (2,2) or (2,1)^2 true), while
# RAM(5)/RAM(7) (certified) were exact.  This is GENHN-3(a) at the
# composed read -- a sharpening of GENHN-BOX-4, NOT a dictionary
# failure: the un-extracted full-side legs (E31, E3) test the
# dictionary at every depth un-gated.  Below: the certified table
# (worst-case member; error floors from the exact E-recursion), the
# per-leaf consulted-digit gate, and diagnostic (non-scoring)
# emission of the uncertified tail.


def cert_table_E(genre, q, N, h, v4):
    """certified exact v-heights per stage coordinate/class for the
    EXTRACTED quartic block: {(coord, class) -> max certified height};
    coord 0/1 = A0/A1, class 0/1 = x^0/x^1 digit (dv even/odd).
    Derivation (S11): rho defined mod pi^L, L = N - v(f'(rho));
    (x-rho)(q-Q) = -delta*Q with v(Q_j) >= entry floors
    (2h,(3h+1)/2,h,(h+1)/2); solve triangularly from the top with the
    worst-case v(rho); then a11=q3, a10=q2+c, a01=q1+z*pi^h*q3,
    a00=q0+z*pi^h*a10+c."""
    if genre == 'V1E2':
        L = N - 2 * h
        vr = (h + 1) // 2
    else:
        L = N - 4 * v4
        vr = v4
    E3 = L
    E2 = min(L + (h + 1) // 2, vr + E3)
    E1 = min(L + h, vr + E2)
    E0 = min(L + (3 * h + 1) // 2, vr + E1)
    err = {(1, 1): E3, (1, 0): E2,
           (0, 1): min(E1, h + E3), (0, 0): min(E0, h + E2)}
    return {k: v - 1 for k, v in err.items()}


def leaf_cert_E(q, N, h, tab, kk):
    """True iff every digit the leaf decision consulted is certified
    exact (gate for sigma emission on extracted rows).  Consulted set
    per leaf per the read22 semantics; zero-reads taken from the
    ENTRY slot lists (a superset of the actually consulted set along
    refine chains -> sound)."""
    H2, leaf, params = kk[0], kk[1], kk[2]
    A1s = slots_gen(q, N, h, 2, 1)
    A0s = slots_gen(q, N, h, 2, 0)

    def ok(dv, coord):
        par = dv % 2
        return (dv - par * h) // 2 <= tab[(coord, par)]

    def zok(slots, below, coord):
        return all(ok(s, coord) for s in slots if s < below)

    reads = []
    for k in H2:
        reads += [(k, 1), (2 * k, 0)]
        if not (zok(A1s, k, 1) and zok(A0s, 2 * k, 0)):
            return False
    if leaf == 'RAM':
        u0 = params[0]
        reads.append((u0, 0))
        if not (zok(A0s, u0, 0) and zok(A1s, (u0 + 1) // 2, 1)):
            return False
    elif leaf in ('2SIDED', 'SPLTAIL'):
        w = params[0]
        reads.append((w, 1))
        # sigma needs w exact + u_true > 2w: zeros through 2w suffice
        if not (zok(A1s, w, 1) and zok(A0s, 2 * w + 1, 0)):
            return False
    elif leaf in ('SPLITEQ', 'INERT'):
        dmu = params[0]
        reads += [(dmu, 1), (2 * dmu, 0)]
        if not (zok(A1s, dmu, 1) and zok(A0s, 2 * dmu, 0)):
            return False
    else:
        return False
    return all(ok(dv, c) for dv, c in reads)


# ===================================================================
# comparison helper
# ===================================================================
def cmp_tab(fam, rowid, obs, exp):
    for k in sorted(set(obs) | set(exp), key=repr):
        note(fam)
        if obs.get(k) != exp.get(k):
            viol(fam, 'law', '%s %s: obs %s != exp %s'
                 % (rowid, k, obs.get(k), exp.get(k)))


def polystr(R, fc):
    """PARI polynomial string for monic f over Zp ring."""
    terms = ['x^%d' % len(fc)]
    for j in range(len(fc) - 1, -1, -1):
        c = fc[j] % R.M
        if c:
            terms.append('%d*x^%d' % (c, j))
    return '+'.join(terms)


# ===================================================================
# row runners
# ===================================================================
def frame_check(kind, q, N, fc, want, fam):
    """my fresh frame reader must classify fc's frame as genre want."""
    Rg = G.Zp(q, N) if kind == 'Zp' else G.Fqt(q, N)
    ctx = {'p': q, 'cs': []}
    d0 = []
    read6(Rg, N, list(fc), ctx, depth0=d0)
    note(fam)
    if d0[0] != ('CS', want):
        viol(fam, 'genre', '%s != CS %s' % (d0[0], want))


def run_v_row(kind, q, N, h, genre, v4=None, sink=None, step=1):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    gen = (gen_V1E2(R, K, q, N, h) if genre == 'V1E2'
           else gen_V4E2(R, K, q, N, h, v4))
    dvf = 2 * h if genre == 'V1E2' else 4 * v4
    want = ('V1E2', h) if genre == 'V1E2' else ('V4E2', v4, h)
    tab = cert_table_E(genre, q, N, h, v4)
    fcheck_step = 64 if q ** (4 * N) > 10 ** 7 else 16
    for z, fc in gen:
        if genre == 'V4E2':
            r0 = Q.rneg(R, R.mul(R.lift(R.res(fc[4], v4)),
                                 Q.pipow(R, v4)))
        else:
            r0 = None
        rho = newton_root(R, fc, dvf, rho0=r0)
        cs = divide_linear(R, fc, rho)
        key, _ = Q.read22(R, K, q, cs[3], cs[2], cs[1], cs[0])
        if not (key[0] == 'E' and key[1] == () and key[2] == h):
            viol('GN-STAGE2', 'escape', '%s -> %s' % (genre, key))
            continue
        kk = key[3:]
        obs[kk] = obs.get(kk, 0) + 1
        if tot % fcheck_step == 0:
            frame_check(kind, q, N, fc, want, 'GN-STAGE2')
        if sink is not None and kind == 'Zp' and tot % step == 0:
            sg = Q.SIG_E.get(key[4])
            if sg is not None:
                full = tuple(sorted(sg + ((1, 1),)))
                cert = leaf_cert_E(q, N, h, tab, kk)
                sink.append((polystr(R, fc), full,
                             '%s %s @p%d' % (genre, key[4], q), cert))
        tot += 1
    rowid = '%s %s q=%d N=%d h=%d' % (genre, kind, q, N, h)
    law = H4.law_E(q, N, h)
    if genre == 'V1E2':
        fib = q ** (N - (5 * h + 1) // 2) - 1
        mult = (q - 1) * fib
        exp_tot = (q - 1) * fib * q ** (4 * N - 5 * h - 3)
    else:
        fib = q ** (N - 5 * v4 - 1)
        mult = (q - 1) * (q - 1) * fib
        exp_tot = (q - 1) ** 2 * fib * q ** (4 * N - 5 * h - 3)
    exp = {k: mult * c for k, c in law.items()}
    cmp_tab('GN-STAGE2', rowid, obs, exp)
    note('GN-STAGE2')
    if tot != exp_tot:
        viol('GN-STAGE2', 'volume', '%s: %d != %d'
             % (rowid, tot, exp_tot))
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}


def run_e31_row(kind, q, N, h, sink=None, step=1, teeth=None):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    ctx = {}
    obs = {}
    tot = 0
    big = q ** (6 * N - 11) > 10 ** 5
    fcheck_step = 128 if big else 8
    for z, fc in gen_E31(R, K, q, N, h):
        kk = read_e31(R, K, q, h, z, fc, ctx)
        obs[kk] = obs.get(kk, 0) + 1
        if tot % fcheck_step == 0:
            frame_check(kind, q, N, fc, ('E31', h), 'GN-FIB')
        if sink is not None and kind == 'Zp' and tot % step == 0:
            sg = SIG_E31.get(kk[1])
            if sg is not None:
                sink.append((polystr(R, fc), tuple(sorted(sg)),
                             'E31 %s @p%d' % (kk[1], q), True))
        tot += 1
    rowid = 'E31 %s q=%d N=%d h=%d' % (kind, q, N, h)
    exp = {k: (q - 1) * c for k, c in law_Egen(q, N, h, 3).items()}
    cmp_tab('GN-STAGE2', rowid, obs, exp)
    note('GN-STAGE2')
    if tot != (q - 1) * q ** (6 * N - 11):
        viol('GN-STAGE2', 'volume', rowid)
    if teeth is not None:
        bad = {k: (q - 1) * c
               for k, c in law_Egen(q, N, h, 3,
                                    integer_only=True).items()}
        if bad != obs:
            FIRE['GN-T-LAT'] += 1
        else:
            viol('GN-STAGE2', 'tooth-dead', 'GN-T-LAT %s' % rowid)
        if any(k[1] == 'INERT' for k in obs):
            bad = {k: (q - 1) * c
                   for k, c in law_Egen(q, N, h, 3,
                                        inert_c=q * (q - 1)).items()}
            if bad != obs:
                FIRE['GN-T-CEN'] += 1
            else:
                viol('GN-STAGE2', 'tooth-dead', 'GN-T-CEN %s' % rowid)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}


def e3_slots(q, N, h, j):
    xs = [2 * v + h for v in range(((2 * (3 - j) - 1) * h + 1) // 2, N)]
    cs = [2 * v for v in range((3 - j) * h + 1, N)]
    return sorted(xs + cs)


def run_e3_row(kind, q, N, h, sink=None, step=1, tooth_node=False):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    ctx = {}
    obs = {}
    tot = 0
    for z, fc in gen_E3(R, K, q, N, h):
        kk = read_e3(R, K, q, h, z, fc, ctx)
        key = kk[:3]
        obs[key] = obs.get(key, 0) + 1
        if tot % 16 == 0:
            frame_check(kind, q, N, fc, ('E3', h), 'GN-FIB')
        if sink is not None and kind == 'Zp' and kk[3] is not None \
                and tot % step == 0:
            sink.append((polystr(R, fc), kk[3],
                         'E3 %s @p%d' % (key, q), True))
        tot += 1
    rowid = 'E3 %s q=%d N=%d h=%d' % (kind, q, N, h)
    note('GN-E3')
    vol = (q - 1) * q ** (6 * N - (21 * h + 9) // 2)
    if tot != vol:
        viol('GN-E3', 'volume', '%s: %d != %d' % (rowid, tot, vol))
    # preregistered laws: UND3 / RAM3(u0) / ALPHA3(kappa)
    s0, s1, s2 = (e3_slots(q, N, h, j) for j in (0, 1, 2))
    cap = 2 * N
    und3 = q ** (len([s for s in s0 if s >= cap])
                 + len(s1) + len(s2)) * (q - 1)
    note('GN-E3')
    if obs.get(((), 'UND3', ()), 0) != und3:
        viol('GN-E3', 'und3', '%s: %d != %d'
             % (rowid, obs.get(((), 'UND3', ()), 0), und3))
    for u0 in [s for s in s0 if s < cap and s % 3 != 0]:
        exp = (q - 1) * (q - 1) * q ** (
            len([s for s in s0 if s > u0])
            + len([s for s in s1 if s >= ceil_div(2 * u0, 3)])
            + len([s for s in s2 if s >= ceil_div(u0, 3)]))
        got = sum(v for k, v in obs.items()
                  if k[0] == () and k[1] == 'S3DEC'
                  and len(k[2]) == 1 and k[2][0][:4] == (0, u0, 3, 0)
                  and k[2][0][4] == (('P', 3, 1),))
        note('GN-E3')
        if got != exp:
            viol('GN-E3', 'ram3', '%s u0=%d: %d != %d'
                 % (rowid, u0, got, exp))
    for kap in range(2 * h + 1, N):
        if 3 * kap not in s0 or 3 * kap >= cap:
            continue
        exp = (q - 1) * (q - 1) * q ** (
            len([s for s in s0 if s > 3 * kap])
            + len([s for s in s1 if s > 2 * kap])
            + len([s for s in s2 if s > kap]))
        got = sum(v for k, v in obs.items()
                  if k[0][:1] == (kap,))
        note('GN-E3')
        if got != exp:
            viol('GN-E3', 'alpha3', '%s kappa=%d: %d != %d'
                 % (rowid, kap, got, exp))
    if tooth_node:
        ctx2 = {}
        tot2 = sum(1 for _ in gen_E3(R, K, q, N, h, corrupt_node=True))
        if tot2 != vol:
            FIRE['GN-T-NODE'] += 1
        else:
            viol('GN-E3', 'tooth-dead', 'GN-T-NODE %s' % rowid)
    say('  [%s] %d members, %d keys, stage_cs=%d (%.1fs)'
        % (rowid, tot, len(obs), ctx.get('stage_cs', 0),
           time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}


# ===================================================================
# GN-CLASS sweep rows
# ===================================================================
def gi_type(ev):
    t = ev[0]
    if t in ('CS', 'ALPHA', 'DEC', 'DRAIN'):
        return t
    return 'BETA'


def run_class_row(kind, q, N, m, expect, absent, tie=False):
    Rg = G.Zp(q, N) if kind == 'Zp' else G.Fqt(q, N)
    t1 = time.time()
    ctx = {'p': q, 'cs': []}
    tallies = {}
    verd = {'DEC': 0, 'DRAIN': 0, 'CS': 0}
    ncs_seen = 0
    tot = 0
    for st in G.iter_states(Rg, N, m):
        tot += 1
        d0 = []
        v, sig = read6(Rg, N, list(st), ctx, depth0=d0)
        verd[v] += 1
        if d0[0][0] == 'CS':
            tallies[d0[0][1]] = tallies.get(d0[0][1], 0) + 1
        while ncs_seen < len(ctx['cs']):
            rec = ctx['cs'][ncs_seen]
            ncs_seen += 1
            note('GN-CLASS')
            if not grammar_ok(rec, m, N):
                viol('GN-CLASS', 'grammar', '%s' % (rec,))
        if tie:
            gctx = {'p': q, 'cs_events': []}
            ev = []
            v2, s2 = G.read_cluster(Rg, N, list(st), gctx,
                                    top_events=ev)
            if (v, sig) != (v2, s2) or gi_type(d0[0]) != gi_type(ev[0]):
                viol('GN-CLASS', 'tie', '%s: %s vs %s / %s vs %s'
                     % (st, (v, sig), (v2, s2), d0[0], ev[0]))
            elif d0[0][0] in ('CS', 'ALPHA') and d0[0] != ev[0]:
                viol('GN-CLASS', 'tie-key', '%s: %s vs %s'
                     % (st, d0[0], ev[0]))
            note('GN-CLASS')
    rowid = 'CLASS %s q=%d N=%d n=%d' % (kind, q, N, m)
    for k, v in expect.items():
        note('GN-CLASS')
        if tallies.get(k, 0) != v:
            viol('GN-CLASS', 'flagship', '%s %s: %d != %d'
                 % (rowid, k, tallies.get(k, 0), v))
    for name in absent:
        note('GN-CLASS')
        if any(k[0] == name for k in tallies):
            viol('GN-CLASS', 'visibility', '%s: %s present' %
                 (rowid, name))
    # GN-T-CRIT: the loosened grammar must accept what the real one
    # rejects, on rows realizing a (3)-child (mu=3 e=gam=1 events)
    if ctx.get('beta3'):
        fake = (m, (0, 3), 1, 1, 3, 1, ())
        if grammar_ok(fake, m, N, loose=True) and \
                not grammar_ok(fake, m, N):
            FIRE['GN-T-CRIT'] += 1
        else:
            viol('GN-CLASS', 'tooth-dead', 'GN-T-CRIT %s' % rowid)
    say('  [%s] %d states DEC/DRAIN/CS %d/%d/%d, %d CS events, '
        'depth0 CS %s (%.1fs)'
        % (rowid, tot, verd['DEC'], verd['DRAIN'], verd['CS'],
           len(ctx['cs']),
           {repr(k): v for k, v in sorted(tallies.items(), key=repr)},
           time.time() - t1))
    return {'row': rowid, 'states': tot, 'verdicts': verd,
            'cs_depth0': {repr(k): v for k, v in tallies.items()}}


# ===================================================================
# GN-TOWER
# ===================================================================
def pmul(R, a, b):
    out = [Q.rzero(R)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = R.add(out[i + j], R.mul(x, y))
    return out


def padd_list(R, a, b):
    n = max(len(a), len(b))
    a = a + [Q.rzero(R)] * (n - len(a))
    b = b + [Q.rzero(R)] * (n - len(b))
    return [R.add(x, y) for x, y in zip(a, b)]


def run_tower():
    t1 = time.time()
    q, N, h, z = 3, 6, 1, 1
    R = W10.ZpWin(q, N)
    K = R.K
    phi = [K_neg_pi(R, K, z, h), Q.rzero(R), Q.rint(R, 1)]
    A2 = [Q.rzero(R), Q.pipow(R, 2)]          # 9x: dv = 2*2+1 = 5
    A0 = [Q.pipow(R, 5), Q.rzero(R)]          # 3^5: dv = 10
    f = pmul(R, pmul(R, phi, phi), pmul(R, phi, phi))
    f = padd_list(R, f, pmul(R, A2, pmul(R, phi, phi)))
    f = padd_list(R, f, A0)
    assert R.val(Q.rsub(R, f[8], Q.rint(R, 1))) is None, 'monic'
    fc = f[:8]
    # (a) the frame parses as the (2,1,4) genre at n = 8
    Rg = G.Zp(q, N)
    ctx = {'p': q, 'cs': []}
    d0 = []
    read6(Rg, N, list(fc), ctx, depth0=d0)
    note('GN-TOWER')
    if d0[0] != ('CS', ('EMB', 8, (0, 8), 2, 1, 4, 1)):
        viol('GN-TOWER', 'frame', 'witness frame -> %s' % (d0[0],))
    note('GN-TOWER')
    if not all(grammar_ok(rec, 8, N) for rec in ctx['cs']):
        viol('GN-TOWER', 'frame-grammar', '%s' % (ctx['cs'],))
    # (b) the mu = 4 stage read hits a stage-CS (2,1,2) event
    A, top = develop(R, fc, phi, 4)
    dvs = [dv_gen(R, h, 2, A[j]) for j in range(4)]
    note('GN-TOWER')
    if dvs != [10, None, 5, None]:
        viol('GN-TOWER', 'stage-dv', '%s' % (dvs,))
    pts = [(j, dvs[j]) for j in range(4) if dvs[j] is not None]
    pts.append((4, 0))
    hv = G.hull_lower(pts)
    note('GN-TOWER')
    if hv != [(0, 10), (4, 0)]:
        viol('GN-TOWER', 'stage-hull', '%s' % (hv,))
    (j0, y0), (j1, y1) = hv[0], hv[1]
    dx, dy = j1 - j0, y0 - y1
    gg = gcd(dx, dy)
    e_s, kk, g = dx // gg, dy // gg, gg
    note('GN-TOWER')
    if (e_s, g) != (2, 2):
        viol('GN-TOWER', 'stage-side', '%s' % ((e_s, kk, g),))
    rc = []
    for t in range(g + 1):
        j = j0 + t * e_s
        ht = y0 - t * kk
        c = K.one() if j == 4 else slot_digit2(R, h, A[j], ht)
        g_t = ((ht % 2) + t * (kk % 2) - (y0 % 2)) // 2
        rc.append(K.mul(c, zpow(K, z, g_t)))
    lead_inv = K.inv(rc[-1])
    rc = [K.mul(c, lead_inv) for c in rc]
    facs = kp_factor_full([int(c) for c in rc], q)
    note('GN-TOWER')
    tower_fired = any(mu_s >= 2 and e_s * (len(fac) - 1) >= 2
                      for fac, mu_s in facs)
    if not tower_fired:
        viol('GN-TOWER', 'no-tower', 'residual %s facs %s'
             % (rc, facs))
    else:
        say('  [TOWER] witness fires: inner stage residual %s = '
            'repeated (mu_s=2) on the e_s=2 side -- the (2,1,2) '
            'opening INSIDE the (2,1,4) stage at n=8' % (facs,))
    # (c) the minimal-n scan
    best = None
    for e1 in range(1, 9):
        for f1 in range(1, 9):
            for mu in range(4, 9):
                if e1 * f1 >= 2 and e1 * f1 * mu <= 12:
                    n0 = e1 * f1 * mu
                    if best is None or n0 < best:
                        best = n0
    note('GN-TOWER')
    if best != 8:
        viol('GN-TOWER', 'min-n', '%s' % best)
    say('  [TOWER] min tower degree = %s; witness frame + stage read '
        'complete (%.1fs)' % (best, time.time() - t1))
    return {'witness_dvs': dvs, 'min_n': best}


# ===================================================================
# GN-SIGMA (PARI)
# ===================================================================
GP_SIGP = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sigp(f, p, prec) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, prec);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
"""


def run_oracle(jobs, rowid, p, flip_e31=False):
    """jobs = (polystr, want, tag, cert).  cert=True jobs SCORE
    (mismatch = violation); cert=False jobs (beyond the extraction-
    certified perimeter -- see cert_table_E) are DIAGNOSTIC ONLY:
    their mismatch count is measured and reported, never scored."""
    if not jobs:
        return {'row': rowid, 'scored': 0}
    t1 = time.time()
    lines = [W12.GP_FUN]
    for i, (ps, want, tag, cert) in enumerate(jobs):
        lines.append('print("R %d ", sig(%s, %d))' % (i, ps, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = W12.parse_sig(rest)
    # [re-seal fix 2, disclosed] retry ladder for gp misses: on rare
    # inputs the pinned sig's factorpadic precision 200 makes
    # idealprimedec fail ('precision too low in get_norm'; run 2 hit
    # 4/20,800, every one confirming its prediction on retry); the
    # REPL skips those lines.  Retry each missing job individually at
    # precisions 50/100/400 -- same independent PARI question, only
    # the working precision changes.  Misses after the ladder still
    # count as violations below.
    nretry = 0
    missing = [i for i in range(len(jobs)) if i not in got]
    for i in missing:
        for prec in (50, 100, 400):
            alt = (GP_SIGP + 'print("R %d ", sigp(%s, %d, %d))\nquit\n'
                   % (i, jobs[i][0], p, prec))
            out2 = W10.gp_run(alt)
            done = False
            for line in out2.splitlines():
                if line.startswith('R %d ' % i):
                    got[i] = W12.parse_sig(line.split(' ', 2)[2])
                    done = True
            if done:
                nretry += 1
                break
    if nretry:
        say('  [oracle %s] %d gp precision misses recovered by the '
            'retry ladder' % (rowid, nretry))
    ncert = sum(1 for j in jobs if j[3])
    note('GN-SIGMA', ncert)
    if len(got) != len(jobs):
        viol('GN-SIGMA', 'truncated', '%s: %d/%d'
             % (rowid, len(got), len(jobs)))
    nbad = 0
    ndiag = ndiag_bad = 0
    fr_c = fr_a = 0
    for i, (ps, want, tag, cert) in enumerate(jobs):
        gv = got.get(i)
        if not cert:
            ndiag += 1
            if gv != tuple(sorted(want)):
                ndiag_bad += 1
            continue
        if gv != tuple(sorted(want)):
            nbad += 1
            if nbad < 6:
                viol('GN-SIGMA', 'sigma', '%s %s: %s != %s'
                     % (rowid, tag, gv, tuple(sorted(want))))
        if flip_e31 and tag.startswith('E31 RAM'):
            fr_a += 1
            if gv != ((3, 2),):
                fr_c += 1
    if flip_e31 and fr_a:
        if fr_c == fr_a:
            FIRE['GN-T-SIG'] += 1
        else:
            viol('GN-SIGMA', 'tooth-dead', 'GN-T-SIG %s' % rowid)
    say('  [oracle %s] %d certified scored, %d bad; %d diagnostic '
        '(uncertified tail), %d diag-mismatch; E31-RAM flip %d/%d '
        '(%.1fs)' % (rowid, ncert, nbad, ndiag, ndiag_bad,
                     fr_c, fr_a, time.time() - t1))
    return {'row': rowid, 'scored': ncert, 'bad': nbad,
            'diag': ndiag, 'diag_bad': ndiag_bad}


# ===================================================================
# main
# ===================================================================
def main(smoke=False):
    t0 = time.time()
    say('=== GENHN battery (%s) ===' % ('SMOKE' if smoke else 'FULL'))
    results = {'smoke': smoke, 'rows': [], 'oracle': []}
    # GN-PIN
    for fn, want in sorted(PINS.items()):
        path = os.path.join(HERE, fn)
        md5 = hashlib.md5(open(path, 'rb').read()).hexdigest()
        note('GN-PIN')
        if md5 != want:
            viol('GN-PIN', 'md5', '%s: %s != %s' % (fn, md5, want))
    say('[GN-PIN] %d pins checked' % len(PINS))
    # GN-LAWTIE
    for (q, N, h) in [(2, 5, 1), (2, 6, 1), (2, 7, 3), (3, 5, 1),
                      (5, 4, 1)]:
        note('GN-LAWTIE')
        if law_Egen(q, N, h, 2) != H4.law_E(q, N, h):
            viol('GN-LAWTIE', 'e1=2', '(%d,%d,%d)' % (q, N, h))
    say('[GN-LAWTIE] law_Egen(e1=2) == law_E on 5 grid points')
    # GN-CLASS
    exp_n5 = lambda q, N: {('V1E2', 1):
                           (q - 1) * q ** (4 * N - 8)
                           * (q ** (N - 3) - 1)}
    abs_n5 = ['V4E2', 'V1E1Q', 'V4E1Q', 'FULLQ']
    exp_n6_24 = {('E3', 1): 512, ('E31', 1): 8192}
    exp_n6_33 = {('E31', 1): 4374}
    abs_n6 = ['F3', 'E13', 'F2X']
    rows = [('Zp', 2, 5, 5, exp_n5(2, 5), abs_n5, True),
            ('Zp', 2, 4, 6, exp_n6_24, abs_n6 + ['E2X'], False)]
    if not smoke:
        rows += [('Fqt', 2, 5, 5, exp_n5(2, 5), abs_n5, True),
                 ('Fqt', 2, 4, 6, exp_n6_24, abs_n6 + ['E2X'], False),
                 ('Zp', 3, 3, 6, exp_n6_33, abs_n6 + ['E3'], False),
                 ('Fqt', 3, 3, 6, exp_n6_33, abs_n6 + ['E3'], False)]
    for (kind, q, N, m, exp, ab, tie) in rows:
        results['rows'].append(run_class_row(kind, q, N, m, exp, ab,
                                             tie=tie))
    # GN-STAGE2: V rows
    sink_v = []
    vrows = [('Zp', 2, 5, 1, 'V1E2', None, 1)]
    if not smoke:
        vrows += [('Zp', 2, 6, 1, 'V1E2', None, 64),
                  ('Zp', 3, 4, 1, 'V1E2', None, 8),
                  ('Fqt', 2, 6, 1, 'V1E2', None, 1),
                  ('Zp', 2, 8, 3, 'V4E2', 1, 32),
                  ('Fqt', 2, 8, 3, 'V4E2', 1, 1)]
    for (kind, q, N, h, genre, v4, step) in vrows:
        results['rows'].append(
            run_v_row(kind, q, N, h, genre, v4=v4, sink=sink_v,
                      step=step))
    # GN-STAGE2: E31 rows
    sink_e31 = []
    erows = [('Zp', 2, 4, 1, 8, True)]
    if not smoke:
        erows += [('Zp', 2, 5, 1, 128, False),
                  ('Zp', 3, 3, 1, 2, True),
                  ('Fqt', 2, 5, 1, 1, False)]
    for (kind, q, N, h, step, teeth) in erows:
        results['rows'].append(
            run_e31_row(kind, q, N, h, sink=sink_e31, step=step,
                        teeth=(True if teeth else None)))
    # GN-E3 rows
    sink_e3 = []
    e3rows = [('Zp', 3, 4, 1, 4, True)]
    if not smoke:
        e3rows += [('Zp', 2, 5, 1, 16, False),
                   ('Fqt', 2, 5, 1, 1, False)]
    for (kind, q, N, h, step, tn) in e3rows:
        results['rows'].append(
            run_e3_row(kind, q, N, h, sink=sink_e3, step=step,
                       tooth_node=tn))
    # GN-TOWER
    results['tower'] = run_tower()
    # GN-SIGMA
    if smoke:
        sink_v = sink_v[::16]
        sink_e31 = sink_e31[::4]

    # (oracle jobs carry their own p in the tag suffix; split by p)
    def by_p(sink):
        outs = {}
        for job in sink:
            pp = int(job[2].rsplit('@p', 1)[1])
            outs.setdefault(pp, []).append(job)
        return outs
    for pp, jobs in sorted(by_p(sink_v).items()):
        results['oracle'].append(run_oracle(jobs, 'V p=%d' % pp, pp))
    for pp, jobs in sorted(by_p(sink_e31).items()):
        results['oracle'].append(run_oracle(jobs, 'E31 p=%d' % pp, pp,
                                            flip_e31=True))
    for pp, jobs in sorted(by_p(sink_e3).items()):
        results['oracle'].append(run_oracle(jobs, 'E3 p=%d' % pp, pp))
    # verdict
    nv = sum(len(v) for v in VIOL.values())
    dead = [t for t in TEETH if FIRE[t] == 0]
    for t in dead:
        say('  !! DEAD TOOTH %s' % t)
    ok = (nv == 0 and not dead)
    say('=== VERDICT: %s -- %d checks, %d violations, teeth %s '
        '(%.1fs) ==='
        % ('GREEN' if ok else 'RED', sum(NCHK.values()), nv,
           {t: FIRE[t] for t in TEETH}, time.time() - t0))
    results['checks'] = dict(NCHK)
    results['violations'] = {f: v for f, v in VIOL.items() if v}
    results['teeth'] = dict(FIRE)
    results['elapsed_s'] = round(time.time() - t0, 1)
    results['verdict'] = 'GREEN' if ok else 'RED'
    if not smoke:
        with open(os.path.join(HERE, 'genhn_checks_results.json'),
                  'w') as f:
            json.dump(results, f, indent=1, sort_keys=True)
        with open(os.path.join(HERE, 'genhn_checks_output.txt'),
                  'w') as f:
            f.write('\n'.join(LOG) + '\n')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv[1:]))
