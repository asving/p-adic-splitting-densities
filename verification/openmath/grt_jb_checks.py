#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_jb_checks.py -- J-B TREE-JUNCTION runner (the machine leg of
lean/notes/openmath/GRTJB_PROOF_2026-08-08.md; two-commit seal).

Computes BOTH SIDES of every JB equality (note sections 2-5) on the sealed
weld-probe roster (16 towers), the 5 concrete QO shapes (fresh extraction),
and the 4 fresh d0 >= 2 shapes (engine_ext standing rule).  Legs:
  harness side = iterlawn_pe_reimpl (committed, verbatim import);
  print side   = grt_weld_probe.GmnLeg (sealed fresh GMN transcription,
                 verbatim import -- NO new print transcription here);
  fresh side   = this runner's OWN schoolbook division-with-remainder, its
                 OWN lower-hull/vertex geometry (Fractions), its OWN
                 L-NORM/tree walker implemented from the [RMG] note text,
                 and fresh Bezout/weight integers -- decorrelated from both
                 engines' internals (PolyO.dev is NEVER the checked leg).

========================= PREREGISTERED FAMILIES ==============================
EXT-GATE engine_ext standing rule: check_pins() + agreement_gate() re-run
        in-unit, counts reported.                     PREDICT: 0 new viols.
JB-DEV  note TH JB-DEV(i)+(iii)(VAL): the Phi_q-development recomputed by
        FRESH schoolbook division == both engines' digit lists at every
        shared level q of every tower; per-digit weight tie
        wlev(q, A_i) == vgen(q+1, A_i).               PREDICT: 0.
JB-KEYEQ note TH JB-DEV(ii): byte-equality census Phi_q^har vs
        phi_{q+1}^cls; TH-BASE (q = 1 byte-equal) on every tower; census
        counts disclosed (the probe F1 pattern).      PREDICT: 0
        (TH-BASE violations; census reported, not gated).
JB-SHEAR note TH JB-VTX(a)+(d): pointwise H(f) == Sigma_q(U(f)); the four
        min/read ties min U = vgen(q+1,f) (Lemma shape 1 through a SECOND
        development), min H = wlev(q+1,f) = vgen(q+2,f).  PREDICT: 0.
JB-VTX  note TH JB-VTX(b)+(c): fresh lower hulls both frames, vertex
        bijection at same abscissas, per-side slope law s -> e_q*s + h_q,
        lengths preserved.                            PREDICT: 0.
JB-ID   note TH JB-TREE(ii): (ID-(i+1)) exact in O[x] (fresh arithmetic);
        the key's own dev has digits {C_k at e_i k, 1 at P_i}; the PRINT
        key's own dev is grid-supported and shear-constant (one-sided);
        byte tie on byte-equal junctions.             PREDICT: 0.
JB-TREE note TH JB-TREE(i): FRESH from-note E1-priority tree walk on
        f*Chat_m (T-scope(m), g_m = 1 rows): exact signed reassembly
        f*Chat = R0 + Q*Phi_m; R0/Q == the FRESH canonical divmod by the
        harness key AND by the print key where byte-equal; R-leaves
        reduced; termination under the step cap.      PREDICT: 0.
JB-LINE note TH JB-TREE(iii): on sampled walk edges the fresh line deltas
        hit the LED-Lambda lambda_E quanta (promotion +q_{i+1}, exit
        -w_m Phi_m, correction-L 0, pi-junk >= E_m, Y-junk >= Gamma_0);
        on sampled reduced cells line(C) == wlev(m, C) == vgen(m+1, C).
                                                      PREDICT: 0.
JB-EPS  note LEMMA JB-EPS: t(V+V') - t(V) - t(V') == eps' ==
        (s+s'-s'')/e (all-fresh integers) and the field form
        eps(V+V') == eps(V)*eps(V')*z^{-eps'}.        PREDICT: 0.
JB-CM   c_m := eps_m(gamma_{m+1})*R_{m,gamma}(Chat_m) == psi_{m,0} and
        embed_{K_{m+1}}(c_m) == -z_{m+1} (g_m = 1 rows).  PREDICT: 0.
JB-CREAD note TH JB-CREAD on the scored stratum: (VD-m) MACHINE-EVALUATED
        at f and at R; where both hold and v != 0:
        rho_m(R) == c_m * rho_m(f) and w_m(R) == lambda + gamma_{m+1}.
        v = 0 rows: census + rho_m(f) == 0 where (VD-m) at f holds.
        (VD-m)-failing rows: boundary census (JA-BOX-2 geography).
        PREDICT: 0 scored violations; censuses disclosed.
JB-QO   the 5 concrete shapes: extraction completes; families above.
                                                      PREDICT: 0.
JB-D0   the 4 fresh d0 >= 2 shapes: engine_ext certificate + committed
        gate; families above.                         PREDICT: 0.
TW-JB   W-2 clause-3 chamber re-instantiation: on every tower with a
        nontrivial transport ledger, rebuild (T2, G2) on the transported
        psi ledger and re-run JB-DEV/JB-SHEAR/JB-VTX/JB-TREE/JB-CREAD
        inside the chamber.        PREDICT: 0 scored (censuses separate).
MJB-DEV  teeth: a pi-garbled key must break the fresh-dev digit tie on
        each designated row.                          PREDICT: caught.
MJB-VTX  teeth: the UNSHEARED identification (hull of (i, w_q(A_i))
        against the print hull) must FAIL on each designated row (the
        T-F 7,472-violation genre).                   PREDICT: caught.
MJB-TREE teeth: one pi-corrupted correction digit must break the signed
        reassembly on each designated row.            PREDICT: caught.
MJB-CREAD teeth: the spurious-carry reading rho(R) = z^{eps'}*c_m*rho(f)
        must FAIL on each designated row (a scored sample with
        z_m^{eps'} != 1).                             PREDICT: caught.

BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest): a reduced-roster smoke
(T2A/T2B/T3A/T3E/I4B + QO/d0 legs) ran during construction to (i) shake
down runner-local code and (ii) pre-verify teeth visibility and fix the
DESIGNATED row lists sealed below.  Sealed predictions are the note's
displayed laws, not smoke-fitted: JB-CREAD/TW-JB predictions are 0 AS
QUANTIFIED (scored-where-(VD-m)-holds-and-v-nonzero), which is the
theorem's own displayed conditionality.  SMOKE RECORD: (i) the reduced
smoke (T2A/T2B/T3A/T3E/I4B + QO/d0 + chamber legs) ran ALL LAW FAMILIES
GREEN, 2,319 samples, 0 violations, first complete run -- no law-side
repair was needed; (ii) a full-roster teeth-visibility probe (law
families green there too, 0 violations, small pools) fixed the sealed
designations: MJB-CREAD visible on T2A/T2D/T2G/T3A/T3D/T3E/I4B
(designated triple T2A/T2D/T3D); MJB-TREE catchable on every roster row
except T2C/I4C (designated T2A/T3E/I4B; the probe also showed the m=1
2-sample form missed T3E, so mjb_tree scans all eligible m with 3
samples -- a TEETH-side repair only); (iii) two guard fixes during
construction (psi_{i,k} = 0 skip at i = 0; none else) -- engines
untouched.  I4C has NO eligible (g_m = 1, T-scope) reduction level:
tree/cread rows are honestly absent there (the note's scope fence).
Deterministic; exact arithmetic; no RNG.
Deterministic; exact arithmetic; no RNG.  Outputs:
grt_jb_checks_output.txt (tee'd by caller), grt_jb_checks_results.json.
"""
import sys, os, json, time, collections
from math import gcd
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_w2_checks as GW2
import grt_ja_checks as GJA
import engine_ext as EE
import grb_order2_check as GRB

VIOL = []
COUNTS = collections.defaultdict(int)
RES = {'towers': {}, 'keyeq': {}, 'tree': {}, 'cread': {}, 'tw': {},
       'qo': {}, 'd0': {}, 'mut': {}, 'families': {}}

def note(fam, n=1):
    COUNTS[fam] += n

def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))
    print('  VIOLATION [%s] %s: %s' % (fam, tag, str(msg)[:200]))

# --------------------------------------------------------- fresh helpers
def fresh_bez(e, h):
    l = GWP.modinv_ell(h, e)
    return l, (1 - l*h)//e

def s_geo(V, e, h):
    """geometric eq12 abscissa (no ell): smallest x in [0,e) with
    integer ordinate on {e*y + x*h = V}."""
    for x in range(e):
        if (V - x*h) % e == 0:
            return x
    raise AssertionError('no integer point')

def w0(R, f):
    vs = [R.val(c) for c in f if not R.is_zero(c)]
    return min(vs) if vs else None

def pi_div(R, a, w):
    """a / pi^w for a single coefficient (exact; val(a) >= w)."""
    if w == 0 or R.is_zero(a):
        return a
    if isinstance(R, ITL.Zp):
        q, r = divmod(a, R.p**w)
        assert r == 0, 'pi_div not exact'
        return q
    assert all(c == 0 for c in a[:w]), 'pi_div not exact (Fpt)'
    return tuple(a[w:])

def poly_pi_div(R, f, w):
    return tuple(pi_div(R, c, w) for c in f)

def fresh_divmod(R, f, Phi):
    """FRESH schoolbook division by the monic Phi: f = Q*Phi + rem,
    deg rem < deg Phi.  Only R.add/mul/neg -- no PolyO call."""
    f = list(f); d = len(Phi) - 1
    assert Phi[-1] == R.one()
    if len(f) - 1 < d:
        return (), tuple(f)
    Q = [R.zero()]*(len(f) - d)
    for i in range(len(f) - 1, d - 1, -1):
        c = f[i]
        if R.is_zero(c):
            continue
        Q[i - d] = c
        for j in range(d + 1):
            f[i - d + j] = R.add(f[i - d + j], R.neg(R.mul(c, Phi[j])))
    while f and R.is_zero(f[-1]): f.pop()
    while Q and R.is_zero(Q[-1]): Q.pop()
    return tuple(Q), tuple(f)

def fresh_dev(R, f, Phi):
    """FRESH development digit list [A_0, A_1, ...] by iterated fresh
    division."""
    out = []
    cur = tuple(f)
    while cur:
        cur, rem = fresh_divmod(R, cur, Phi)
        out.append(rem)
    return out

def lower_hull(pts):
    """fresh monotone-chain LOWER hull of {(x, y)}; returns vertex list
    (strict turns only), x strictly increasing."""
    pts = sorted(pts)
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep p only if turn at hull[-1] is strictly convex (lower)
            if (y2 - y1)*(p[0] - x2) >= (p[1] - y2)*(x2 - x1):
                hull.pop()
            else:
                break
        hull.append(p)
    return hull

def hull_sides(verts):
    """[(slope Fraction, x0, x1)] between consecutive vertices."""
    return [(Fraction(verts[k+1][1] - verts[k][1],
                      verts[k+1][0] - verts[k][0]),
             verts[k][0], verts[k+1][0]) for k in range(len(verts) - 1)]

# ===================== section-2/3 families (DEV / KEYEQ / SHEAR / VTX) ======
def qcap_of(T, G):
    """levels q for which the dictionary ties are in scope: keys shared
    strictly below q (first-divergence perimeter)."""
    return min(T.n, GJA.shared_upto(T, G) + 1)

def jb_dev(T, G, tag, pool, fam='JB-DEV'):
    L = GJA.shared_upto(T, G)
    for q in range(0, qcap_of(T, G) + 1):
        key = tuple(T.Phi[q])
        for f in pool:
            if not f:
                continue
            note(fam)
            dvF = [tuple(a) for a in fresh_dev(T.R, f, key)]
            dvI = [tuple(a) for a in T.P.dev(f, key)]
            if dvF != dvI:
                viol(fam, tag, 'fresh dev != engine dev at q=%d' % q)
                continue
            if q >= 1 and tuple(G.phi[q + 1]) == key:
                dvG = [tuple(a) for a in G.P.dev(f, G.phi[q + 1])]
                if dvF != dvG:
                    viol(fam, tag, 'fresh dev != print dev at q=%d' % q)
            for i, A in enumerate(dvF):
                if A and G.vgen(q + 1, A) != T.wlev(q, A):
                    viol(fam, tag, 'digit weight tie fails q=%d i=%d'
                         % (q, i))

def jb_keyeq(T, G, tag):
    """byte census + TH-BASE."""
    cen = {}
    for q in range(1, T.n + 1):
        cen[q] = (tuple(T.Phi[q]) == tuple(G.phi[q + 1]))
    note('JB-KEYEQ')
    if T.n >= 1 and not cen.get(1, True):
        viol('JB-KEYEQ', tag, 'TH-BASE fails: q=1 junction not byte-equal')
    RES['keyeq'][tag] = {str(q): bool(v) for q, v in cen.items()}
    return cen

def frames_of(T, G, q, f):
    dv = fresh_dev(T.R, f, tuple(T.Phi[q]))
    U, H = [], []
    for i, A in enumerate(dv):
        if not A:
            continue
        U.append((i, G.vgen(q + 1, A) + i*G.vkey[q + 1]))
        H.append((i, T.e[q]*T.wlev(q, A) + i*T.gam[q + 1]))
    return dv, U, H

def jb_shear_vtx(T, G, tag, pool, fams=('JB-SHEAR', 'JB-VTX')):
    fsh, fvx = fams
    L = GJA.shared_upto(T, G)
    for q in range(0, qcap_of(T, G) + 1):
        e, h = T.e[q], T.h[q]
        for f in pool:
            if not f:
                continue
            note(fsh); note(fvx)
            dv, U, H = frames_of(T, G, q, f)
            if not U:
                continue
            # (a) pointwise shear
            sh = [(i, e*u + h*i) for (i, u) in U]
            if sh != H:
                viol(fsh, tag, 'pointwise shear fails at q=%d' % q)
                continue
            # (d) min/read ties
            minU = min(u for _, u in U)
            minH = min(y for _, y in H)
            if minH != T.wlev(q + 1, f):
                viol(fsh, tag, 'min H != wlev(q+1) at q=%d' % q)
            if q <= L:
                if minU != G.vgen(q + 1, f):
                    viol(fsh, tag, 'Lemma-shape min tie fails q=%d' % q)
                if q + 1 <= G.RANK and minH != G.vgen(q + 2, f):
                    viol(fsh, tag, 'min H != vgen(q+2) at q=%d' % q)
            # (b) vertex-for-vertex through the shear
            vU = lower_hull(U)
            vH = lower_hull(H)
            if vH != [(x, e*y + h*x) for (x, y) in vU]:
                viol(fvx, tag, 'vertex bijection fails at q=%d' % q)
                continue
            # (c) per-side slope/length translation
            sU, sH = hull_sides(vU), hull_sides(vH)
            for (su, x0, x1), (sy, y0, y1) in zip(sU, sH):
                if not (x0 == y0 and x1 == y1 and sy == e*su + h):
                    viol(fvx, tag, 'slope/length law fails at q=%d' % q)

# ------------------------------------------------------------------- teeth
MJBDEV_DESIGNATED = ['T2A', 'T3A', 'I4B']
MJBVTX_DESIGNATED = ['T2A', 'T2C', 'T3D']
MJBTREE_DESIGNATED = ['T2A', 'T3E', 'I4B']
MJBCREAD_DESIGNATED = ['T2A', 'T2D', 'T3D']

def mjb_dev(T, tag):
    """pi-garbled key must change the development."""
    note('MJB-DEV')
    q = 1 if T.n >= 1 else 0
    key = list(T.Phi[q])
    j0 = (len(key) - 1)//2
    key[j0] = T.R.add(key[j0], T.R.pi_pow(1))
    caught = False
    for f in GJA.sample_pool(T, small=True)[:6]:
        if not f:
            continue
        if fresh_dev(T.R, f, tuple(key)) != fresh_dev(T.R, f,
                                                      tuple(T.Phi[q])):
            caught = True
            break
    if not caught:
        viol('MJB-DEV', tag, 'garbled key NOT caught')
    return caught

def mjb_vtx(T, G, tag, pool):
    """the UNSHEARED identification must fail somewhere on the row."""
    note('MJB-VTX')
    for q in range(0, qcap_of(T, G) + 1):
        for f in pool:
            if not f:
                continue
            dv, U, H = frames_of(T, G, q, f)
            if not U:
                continue
            W = [(i, T.wlev(q, A)) for i, A in enumerate(dv) if A]
            if lower_hull(W) != lower_hull(U):
                return True
    viol('MJB-VTX', tag, 'unsheared identification never caught on row')
    return False

# ===================== section-4 machinery (fresh from the [RMG] note) =======
def lift0(T, c):
    """K_0 element -> O[x] poly, standard digit lifts (P-lift)."""
    return T.P.canon([T.R.liftk(int(x)) for x in c])

def corr_digit(T, i, k):
    """C_k^{(i)} per [RMG] S2.2: realize_i(eps^{-1} psi_{i,k}, beta) for
    i >= 1; lift(psi_{0,k}) * pi^{(g_0-k) h_0} at i = 0."""
    if i == 0:
        base = lift0(T, T.psi[0][k])
        return tuple(T.P.scal(T.R.pi_pow((T.g[0] - k)*T.h[0]), base))
    beta = (T.g[i] - k)*T.gam[i + 1]
    Ki = T.K[i]
    tau = Ki.mul(Ki.inv(T.eps(i, beta)), T.psi[i][k])
    return tuple(T.realize(i, tau, beta))

def cells_of(T, poly, lvl):
    """reduced-cell decomposition of poly (deg < deg Phi_lvl): list of
    (b, jvec) with jvec of length lvl; FRESH developments."""
    if not poly:
        return []
    if lvl == 0:
        return [(tuple(poly), ())]
    out = []
    for j, A in enumerate(fresh_dev(T.R, poly, tuple(T.Phi[lvl - 1]))):
        if A:
            for b, jv in cells_of(T, A, lvl - 1):
                out.append((b, jv + (j,)))
    return out

def lnorm_split(T, b, c, tag):
    """[RMG] L-NORM: b*c = pi^w lift(bbar cbar) + pi^{w+1} Xhat
    + pi^w Phi_0 Yhat; returns [(typ, poly, dj0)], zero children dropped;
    exactness self-checked."""
    R, P = T.R, T.P
    wb, wc = w0(R, b), w0(R, c)
    w = wb + wc
    prod = tuple(P.mul(b, c))
    Phat = poly_pi_div(R, prod, w)
    Y0, r = fresh_divmod(R, Phat, tuple(T.Phi[0]))
    Lbar = P.canon([R.liftk(R.res(cc, 0)) for cc in r])
    if not Lbar:
        viol('JB-TREE', tag, 'L-NORM L-child vanished (L-NORM(a) breach)')
    Xhat = poly_pi_div(R, P.sub(r, Lbar), 1)
    Lp = tuple(P.scal(R.pi_pow(w), Lbar))
    Xp = tuple(P.scal(R.pi_pow(w + 1), Xhat))
    Yp = tuple(P.scal(R.pi_pow(w), Y0))
    recon = P.add(P.add(Lp, Xp), P.mul(Yp, T.Phi[0]))
    if tuple(recon) != prod:
        viol('JB-TREE', tag, 'L-NORM split not exact')
    out = []
    for typ, pp in (('L', Lp), ('X', Xp), ('Y', Yp)):
        if pp:
            out.append((typ, pp, 1 if typ == 'Y' else 0))
    return out

def tscope(T, m):
    return T.d0 == 1 or all(T.e[i] >= 2 for i in range(m))

def elig_ms(T):
    return [m for m in range(1, T.n + 1) if T.g[m] == 1 and tscope(T, m)]

def chat_of(T, m):
    Phi_up = tuple(T.Phi[m + 1]) if m + 1 <= T.n else tuple(GWP.top_lift(T))
    return tuple(T.P.sub(Phi_up, T.P.pow(T.Phi[m], T.e[m])))

def walk_tree(T, m, f, Chat, tag, cap=60000, mut_corr=False):
    """FRESH E1-priority walk on the initial cells of f*Chat; returns
    (leaves, exits, edges) or None on cap."""
    Pl = [T.e[l]*T.g[l] for l in range(m)]
    corr = {}
    for i in range(m):
        rows = []
        for k in range(T.g[i]):
            if T.K[i].is_zero(T.psi[i][k]):
                continue
            cd = corr_digit(T, i, k)
            if mut_corr and not rows:      # teeth: pi-corrupt one digit
                cd = tuple(T.P.scal(T.R.pi_pow(1), cd))
            rows.append((k, cells_of(T, cd, i)))
        corr[i] = rows
    stack = []
    for bx, jx in cells_of(T, f, m):
        for cD, jD in cells_of(T, Chat, m):
            jj = tuple(jx[l] + jD[l] for l in range(m))
            for typ, bb, dj0 in lnorm_split(T, bx, cD, tag):
                j2 = (jj[0] + dj0,) + jj[1:] if dj0 else jj
                stack.append((1, bb, j2))
    leaves, exits, edges = [], [], []
    steps = 0
    while stack:
        steps += 1
        if steps > cap:
            return None
        sgn, b, j = stack.pop()
        i = next((l for l in range(m) if j[l] >= Pl[l]), None)
        if i is None:
            leaves.append((sgn, b, j))
            continue
        if i <= m - 2:
            j2 = list(j); j2[i] -= Pl[i]; j2[i + 1] += 1
            stack.append((sgn, b, tuple(j2)))
            if len(edges) < 4000:
                edges.append(('P', i, (b, j), (b, tuple(j2))))
        else:
            j2 = list(j); j2[m - 1] -= Pl[m - 1]
            exits.append((sgn, b, tuple(j2)))
            if len(edges) < 4000:
                edges.append(('E', m - 1, (b, j), (b, tuple(j2))))
        for k, dcells in corr[i]:
            for cd, ad in dcells:
                for typ, bb, dj0 in lnorm_split(T, b, cd, tag):
                    j2 = list(j)
                    j2[i] -= Pl[i] - T.e[i]*k
                    for l in range(i):
                        j2[l] += ad[l]
                    j2[0] += dj0
                    stack.append((-sgn, bb, tuple(j2)))
                    if len(edges) < 4000:
                        edges.append(('C' + typ, i, (b, j), (bb, tuple(j2))))
    return leaves, exits, edges

def cellpoly(T, b, j):
    out = tuple(b)
    for l, jl in enumerate(j):
        out = tuple(T.P.mul(out, T.P.pow(T.Phi[l], jl)))
    return out

def signed_sum(T, items):
    acc = ()
    for sgn, b, j in items:
        cp = cellpoly(T, b, j)
        acc = tuple(T.P.add(acc, cp if sgn > 0 else T.P.neg(cp)))
    return acc

def jb_tree(T, G, tag, m, fpool, fam='JB-TREE'):
    Chat = chat_of(T, m)
    Phim = tuple(T.Phi[m])
    byteeq = (tuple(G.phi[m + 1]) == Phim)
    Pl = [T.e[l]*T.g[l] for l in range(m)]
    walks = []
    for f in fpool:
        note(fam)
        wk = walk_tree(T, m, f, Chat, tag)
        if wk is None:
            viol(fam, tag, 'tree cap hit on in-scope row m=%d' % m)
            continue
        leaves, exits, edges = wk
        for sgn, b, j in leaves:
            if any(j[l] > Pl[l] - 1 for l in range(m)):
                viol(fam, tag, 'non-reduced R-leaf m=%d' % m)
                break
        fC = tuple(T.P.mul(f, Chat))
        R0 = signed_sum(T, leaves)
        Qp = signed_sum(T, exits)
        if tuple(T.P.add(R0, T.P.mul(Qp, Phim))) != fC:
            viol(fam, tag, 'signed reassembly fails m=%d' % m)
            continue
        Qf, Rf = fresh_divmod(T.R, fC, Phim)
        if R0 != Rf or Qp != Qf:
            viol(fam, tag, 'tree != canonical division (harness key) m=%d'
                 % m)
        if byteeq:
            Qg, Rg = fresh_divmod(T.R, fC, tuple(G.phi[m + 1]))
            if R0 != Rg or Qp != Qg:
                viol(fam, tag, 'tree != print-key division m=%d' % m)
        walks.append((f, leaves, exits, edges))
    RES['tree'].setdefault(tag, {})[str(m)] = {
        'byteeq': bool(byteeq), 'walks': len(walks)}
    return walks

def jb_line(T, G, tag, m, walks, fam='JB-LINE'):
    """LED-Lambda lambda_E face quanta, fresh; leaf line == wlev == vgen."""
    def prod_e(a, b2):
        r = 1
        for t in range(a, b2):
            r *= T.e[t]
        return r
    Em = prod_e(0, m)
    Gam = [T.gam[l + 1]*prod_e(l + 1, m) for l in range(m)]
    qq = [None] + [T.h[l]*prod_e(l + 1, m) for l in range(1, m)]
    wmPhi = T.e[m - 1]*T.g[m - 1]*T.gam[m]
    G0 = Gam[0]

    def line(b, j):
        return Em*w0(T.R, b) + sum(j[l]*Gam[l] for l in range(m))

    okline = qcap_of(T, G) >= m
    for f, leaves, exits, edges in walks:
        for ed in edges[:400]:
            typ, i, (bp, jp), (bc, jc) = ed
            note(fam)
            d = line(bc, jc) - line(bp, jp)
            if typ == 'P':
                if d != qq[i + 1]:
                    viol(fam, tag, 'promotion quantum fails i=%d m=%d'
                         % (i, m))
            elif typ == 'E':
                if d != -wmPhi:
                    viol(fam, tag, 'exit quantum fails m=%d' % m)
            elif typ == 'CL':
                if d != 0:
                    viol(fam, tag, 'correction-L not line-null i=%d m=%d'
                         % (i, m))
            elif typ == 'CX':
                if d < Em:
                    viol(fam, tag, 'pi-junk floor fails i=%d m=%d' % (i, m))
            elif typ == 'CY':
                if d < G0:
                    viol(fam, tag, 'Y-junk floor fails i=%d m=%d' % (i, m))
        for sgn, b, j in leaves[:60]:
            note(fam)
            cp = cellpoly(T, b, j)
            ln = line(b, j)
            if T.wlev(m, cp) != ln:
                viol(fam, tag, 'leaf line != wlev m=%d' % m)
            elif okline and G.vgen(m + 1, cp) != ln:
                viol(fam, tag, 'leaf line != vgen m=%d' % m)

def jb_id(T, G, tag, fam='JB-ID'):
    for i in range(0, T.n):
        note(fam)
        Pi = T.e[i]*T.g[i]
        Phi_up = tuple(T.Phi[i + 1]) if i + 1 <= T.n \
            else tuple(GWP.top_lift(T))
        acc = tuple(T.P.pow(T.Phi[i], Pi))
        for k in range(T.g[i]):
            if T.K[i].is_zero(T.psi[i][k]):
                continue
            acc = tuple(T.P.add(acc, T.P.mul(corr_digit(T, i, k),
                                             T.P.pow(T.Phi[i], T.e[i]*k))))
        if acc != Phi_up:
            viol(fam, tag, '(ID-(i+1)) fails at i=%d' % i)
            continue
        # the key's own development = the identity's digit list
        dv = fresh_dev(T.R, Phi_up, tuple(T.Phi[i]))
        for j, A in enumerate(dv):
            expect = None
            if j == Pi:
                expect = (T.R.one(),)
            elif j % T.e[i] == 0 and j//T.e[i] < T.g[i]:
                k = j//T.e[i]
                if not T.K[i].is_zero(T.psi[i][k]):
                    expect = corr_digit(T, i, k)
            got = tuple(A) if A else ()
            if (expect or ()) != got:
                viol(fam, tag, 'key dev digit mismatch i=%d j=%d' % (i, j))
        # print leg: the print key's own dev is grid-supported,
        # shear-constant (one-sided) -- print-internal, own chain
        r = i + 2
        if r <= G.RANK + 1:
            e_, h_, f_ = G.e[r - 1], G.h[r - 1], G.f[r - 1]
            dvp = fresh_dev(T.R, tuple(G.phi[r]), tuple(G.phi[r - 1]))
            vals = set()
            for j, A in enumerate(dvp):
                if not A:
                    continue
                if not (j == e_*f_ or (j % e_ == 0 and j//e_ < f_)):
                    viol(fam, tag, 'print key dev off-grid i=%d j=%d'
                         % (i, j))
                    continue
                u = G.vgen(r - 1, A) + j*G.vkey[r - 1]
                vals.add(e_*u + h_*j)
            if len(vals) != 1:
                viol(fam, tag, 'print key dev not shear-constant i=%d' % i)

def mjb_tree(T, G, tag, ms, pool):
    note('MJB-TREE')
    for m in ms:
        Chat = chat_of(T, m)
        dPh = len(T.Phi[m]) - 1
        for f in [f for f in pool if f and T.P.deg(f) < dPh][:3]:
            wk = walk_tree(T, m, f, Chat, tag, mut_corr=True)
            if wk is None:
                return True
            leaves, exits, edges = wk
            fC = tuple(T.P.mul(f, Chat))
            R0 = signed_sum(T, leaves)
            Qp = signed_sum(T, exits)
            if tuple(T.P.add(R0, T.P.mul(Qp, tuple(T.Phi[m])))) != fC:
                return True
    viol('MJB-TREE', tag, 'corrupted correction digit NOT caught')
    return False

# ===================== section-5 families (EPS / CM / CREAD) =================
def jb_eps(T, tag, fam='JB-EPS'):
    for m in range(1, T.n + 1):
        e, h = T.e[m - 1], T.h[m - 1]
        l, _ = fresh_bez(e, h)
        K = T.K[m]

        def tt(V):
            s = s_geo(V, e, h)
            assert (l*V - s) % e == 0
            return (l*V - s)//e

        Vs = list(range(0, min(3*e*h + 5, 25)))
        for V in Vs[::2]:
            for Vp in Vs[::3]:
                note(fam)
                s1, s2 = s_geo(V, e, h), s_geo(Vp, e, h)
                s3 = s_geo(V + Vp, e, h)
                ep = (s1 + s2)//e
                if s1 + s2 - s3 != e*ep:
                    viol(fam, tag, 'carry integer identity fails m=%d' % m)
                    continue
                if tt(V + Vp) - tt(V) - tt(Vp) != ep:
                    viol(fam, tag, 't-cocycle identity fails m=%d' % m)
                lhs = T.eps(m, V + Vp)
                rhs = K.mul(K.mul(T.eps(m, V), T.eps(m, Vp)),
                            ITL.fpow(K, T.z[m], -ep))
                if lhs != rhs:
                    viol(fam, tag, 'eps cocycle field form fails m=%d' % m)

def jb_cm(T, tag, m, fam='JB-CM'):
    note(fam)
    K = T.K[m]
    Chat = chat_of(T, m)
    gam1 = T.gam[m + 1]
    tau = T.read(m, gam1, Chat)
    cm = K.mul(T.eps(m, gam1), tau)
    if cm != T.psi[m][0]:
        viol(fam, tag, 'c_m != psi_{m,0} at m=%d' % m)
        return None
    K1 = T.K[m + 1]
    if T.embed(cm, m, m + 1) != K1.neg(T.z[m + 1]):
        viol(fam, tag, 'embed(c_m) != -z_{m+1} at m=%d' % m)
    return cm

def vd_eval(T, G, m, A):
    """MACHINE-EVALUATE (VD-m) at A: returns (holds, rho, beta, v);
    (None, ...) if the print evaluator asserts out (boundary)."""
    beta = T.wlev(m, A)
    v = T.read(m, beta, A)
    K = T.K[m]
    try:
        sup = G._support(m, A)
        s0 = sup[3]
        num = s0 - T.l[m - 1]*beta
        assert num % T.e[m - 1] == 0
        tau = num//T.e[m - 1]
        Rc = G.rres(m, A)
    except AssertionError:
        return None, None, beta, v
    acc, zp = K.zero(), K.one()
    for cc in Rc:
        acc = K.add(acc, K.mul(K.from_base(cc), zp))
        zp = K.mul(zp, T.z[m])
    rho = K.mul(ITL.fpow(K, T.z[m], tau), acc)
    return (rho == K.mul(T.eps(m, beta), v)), rho, beta, v

def jb_cread(T, G, tag, m, fpool, cm, fam='JB-CREAD'):
    """TH JB-CREAD end-to-end; returns (scored, boundary, v0, teethhits)."""
    K = T.K[m]
    e, h = T.e[m - 1], T.h[m - 1]
    gam1 = T.gam[m + 1]
    Chat = chat_of(T, m)
    Phim = tuple(T.Phi[m])
    sc = bd = v0c = th = 0
    for f in fpool:
        note(fam)
        lam = T.wlev(m, f)
        fC = tuple(T.P.mul(f, Chat))
        _, Rr = fresh_divmod(T.R, fC, Phim)
        if not Rr:
            COUNTS['JB-CREAD-RZERO'] += 1
            continue
        ep = (s_geo(lam, e, h) + s_geo(gam1, e, h))//e
        vdf, rho_f, _, v = vd_eval(T, G, m, f)
        if K.is_zero(v):
            v0c += 1
            if vdf and not K.is_zero(rho_f):
                viol(fam, tag, 'v=0 but rho_f != 0 at m=%d' % m)
            continue
        if vdf is None or not vdf:
            bd += 1
            continue
        vdR, rho_R, _, _ = vd_eval(T, G, m, Rr)
        if vdR is None or not vdR:
            bd += 1
            continue
        sc += 1
        if T.wlev(m, Rr) != lam + gam1:
            viol(fam, tag, 'w_m(R) != lambda + gamma at m=%d' % m)
            continue
        want = K.mul(cm, rho_f)
        if rho_R != want:
            viol(fam, tag, 'rho(R) != c_m rho(f) at m=%d' % m)
            continue
        # MJB-CREAD material: the spurious-carry reading must differ
        if ep >= 1 and ITL.fpow(K, T.z[m], ep) != K.one():
            if K.mul(ITL.fpow(K, T.z[m], ep), want) != rho_R:
                th += 1
    COUNTS['JB-CREAD-SCORED'] += sc
    COUNTS['JB-CREAD-BOUNDARY'] += bd
    COUNTS['JB-CREAD-V0'] += v0c
    return sc, bd, v0c, th

# ================================ drivers ====================================
def run_tower_families(T, G, tag, small=False, twfam=None):
    fm = (lambda f: twfam if twfam else f)
    pool = GJA.sample_pool(T, small=small)
    jb_dev(T, G, tag, pool, fam=fm('JB-DEV'))
    if not twfam:
        jb_keyeq(T, G, tag)
    jb_shear_vtx(T, G, tag, pool, fams=(fm('JB-SHEAR'), fm('JB-VTX')))
    jb_id(T, G, tag, fam=fm('JB-ID'))
    jb_eps(T, tag, fam=fm('JB-EPS'))
    stats = {'scored': 0, 'boundary': 0, 'v0': 0, 'teeth': 0, 'trees': 0}
    for m in elig_ms(T):
        if m > qcap_of(T, G):
            COUNTS['JB-TREE-OFFPERIM'] += 1
            continue
        dPh = len(T.Phi[m]) - 1
        fpool = [f for f in pool if f and T.P.deg(f) < dPh]
        fpool = fpool[:(2 if small else 3)]
        if not fpool:
            continue
        walks = jb_tree(T, G, tag, m, fpool, fam=fm('JB-TREE'))
        jb_line(T, G, tag, m, walks, fam=fm('JB-LINE'))
        cm = jb_cm(T, tag, m, fam=fm('JB-CM'))
        if cm is not None:
            sc, bd, v0c, th = jb_cread(T, G, tag, m, fpool, cm,
                                       fam=fm('JB-CREAD'))
            stats['scored'] += sc; stats['boundary'] += bd
            stats['v0'] += v0c; stats['teeth'] += th
        stats['trees'] += len(walks)
    RES['cread'][tag] = stats
    return stats

def tw_leg(T, spec, tag):
    Gf, ledger, fails = GW2.transport_leg(T, tag)
    if fails or Gf is None:
        viol('TW-JB', tag, 'transport failed: %s' % fails)
        return
    if not ledger or all(x[1] in ('1', repr(Gf.Kc[0].one())) for x in ledger):
        pass  # trivial ledgers still re-run (cheap, uniform)
    psi_specs = [[('RAW', c) for c in Gf.psis[j + 1]] for j in range(T.NR)]
    R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
    try:
        T2 = GWP.SpecTower(tag + '/tw', R2, spec['d0'], spec['Phi0'],
                           spec['reads'], psi_specs)
        G2 = GWP.gmn_from_tower(T2)
    except AssertionError as ex:
        viol('TW-JB', tag, 'chamber build failed: %s' % ex)
        return
    note('TW-JB')
    v0 = len(VIOL)
    st = run_tower_families(T2, G2, tag + '/tw', small=True, twfam='TW-JB')
    RES['tw'][tag] = {'ledger': [list(x) for x in ledger], 'cread': st,
                      'new_viol': len(VIOL) - v0}

def qo_leg():
    for name, p, fc in GWP.QO_SHAPES:
        tag = 'QO:%s/Q%d' % (name, p)
        R = ITL.Zp(p)
        leg, levels, status = GWP.qo_extract(R, fc)
        note('JB-QO')
        if status != 'complete':
            viol('JB-QO', tag, 'extraction did not complete: %s' % status)
            continue
        reads = [(e, h, len(psi) - 1) for (e, h, psi) in levels]
        psi_specs = [[('RAW', c) for c in psi] for (e, h, psi) in levels]
        try:
            T = GWP.SpecTower(tag, ITL.Zp(p), 1, [0, 1], reads, psi_specs)
            G = GWP.gmn_from_tower(T)
            v0 = len(VIOL)
            run_tower_families(T, G, tag, small=True)
            RES['qo'][tag] = {'new_viol': len(VIOL) - v0}
        except AssertionError as ex:
            viol('JB-QO', tag, 'extracted-type tower failed: %s' % ex)

def d0_leg():
    for spec in GJA.D0_SPECS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        note('JB-D0')
        F = GRB.mk_field_base(spec['p'], [0, 1])
        A = [((c % spec['p']),) for c in spec['Phi0']]
        try:
            cert = EE.irr_certificate(F, A)
            if not cert['irreducible']:
                viol('JB-D0', tag, 'engine_ext says phibar REDUCIBLE')
        except (AssertionError, ValueError) as ex:
            viol('JB-D0', tag, 'engine_ext certificate failed: %s' % ex)
        try:
            T = ITL.build_tower(spec)
        except AssertionError as ex:
            viol('JB-D0', tag, 'committed tower build failed: %s' % ex)
            continue
        G = GWP.gmn_from_tower(T)
        v0 = len(VIOL)
        run_tower_families(T, G, tag, small=True)
        RES['d0'][tag] = {'new_viol': len(VIOL) - v0}

def teeth(built, smoke=False):
    """MJB families on the designated rows (towers rebuilt fresh).
    In smoke mode, MJB-CREAD designated rows outside the reduced roster
    have no cread stats and are skipped (full runs always cover them)."""
    for tid in MJBDEV_DESIGNATED:
        T, G = built[tid]
        if not mjb_dev(T, tid):
            pass
    for tid in MJBVTX_DESIGNATED:
        T, G = built[tid]
        mjb_vtx(T, G, tid, GJA.sample_pool(T, small=True)[:8])
    for tid in MJBTREE_DESIGNATED:
        T, G = built[tid]
        ms = [m for m in elig_ms(T) if m <= qcap_of(T, G)]
        if not ms:
            viol('MJB-TREE', tid, 'designated row has no eligible m')
            continue
        mjb_tree(T, G, tid, ms, GJA.sample_pool(T, small=True))
    for tid in MJBCREAD_DESIGNATED:
        tag = '%s,p=%s,%s' % t3key(tid)
        if smoke and tag not in RES['cread']:
            continue
        note('MJB-CREAD')
        st = RES['cread'].get(tag, {})
        if st.get('teeth', 0) < 1:
            viol('MJB-CREAD', tid,
                 'designated row: no scored sample with z^{eps prime} != 1')

def t3key(tid):
    spec = next(s for s in GWP.TOWERS if s['id'] == tid)
    return (spec['ring'], str(spec['p']), tid)

def main(smoke=False):
    t0 = time.time()
    print('grt_jb_checks.py -- J-B tree-junction runner%s'
          % (' [SMOKE]' if smoke else ''))
    # EXT-GATE (standing rule)
    v0 = len(EE.VIOL)
    EE.check_pins()
    gate_new = EE.agreement_gate(full=False)
    note('EXT-GATE')
    if gate_new or len(EE.VIOL) > v0:
        viol('EXT-GATE', 'engine_ext', '%d new violations'
             % (len(EE.VIOL) - v0))
    print('  [%6.1fs] EXT-GATE done (new: %d)'
          % (time.time() - t0, len(EE.VIOL) - v0))
    roster = GWP.TOWERS if not smoke else \
        [s for s in GWP.TOWERS if s['id'] in
         ('T2A', 'T2B', 'T3A', 'T3E', 'I4B')]
    built = {}
    for spec in roster:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        tA = time.time()
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        built[spec['id']] = (T, G)
        st = run_tower_families(T, G, tag, small=smoke)
        tw_leg(T, spec, tag)
        print('  [%6.1fs] %-16s done (%.1fs; trees %d, cread sc/bd/v0 '
              '%d/%d/%d, teeth %d)'
              % (time.time() - t0, tag, time.time() - tA, st['trees'],
                 st['scored'], st['boundary'], st['v0'], st['teeth']))
    qo_leg()
    print('  [%6.1fs] QO leg done' % (time.time() - t0))
    d0_leg()
    print('  [%6.1fs] d0>=2 leg done' % (time.time() - t0))
    des = set(MJBDEV_DESIGNATED) | set(MJBVTX_DESIGNATED) | \
        set(MJBTREE_DESIGNATED)
    for tid in sorted(des):
        if tid not in built:
            spec = next(s for s in GWP.TOWERS if s['id'] == tid)
            T = ITL.build_tower(spec)
            built[tid] = (T, GWP.gmn_from_tower(T))
    teeth(built, smoke=smoke)
    print('  [%6.1fs] teeth done' % (time.time() - t0))
    print()
    print('=' * 78)
    print('PREDICTED vs OBSERVED (violation counts; samples in parentheses)')
    print('=' * 78)
    fams = [
        ('EXT-GATE', 'engine_ext pins + agreement gate re-run',    '0'),
        ('JB-DEV',   'fresh dev == both engines + digit weights',  '0'),
        ('JB-KEYEQ', 'byte census + TH-BASE',                      '0'),
        ('JB-SHEAR', 'pointwise shear + min/read ties',            '0'),
        ('JB-VTX',   'vertex bijection + slope/length law',        '0'),
        ('JB-ID',    '(ID) exact + key dev digits + print grid',   '0'),
        ('JB-TREE',  'tree == canonical division (both keys)',     '0'),
        ('JB-LINE',  'lambda_E quanta + line == wlev == vgen',     '0'),
        ('JB-EPS',   'eps-cocycle collapse (int + field)',         '0'),
        ('JB-CM',    'c_m = psi_{m,0} = -z_{m+1}',                 '0'),
        ('JB-CREAD', 'rho(R) = c_m rho(f) (scored stratum)',       '0'),
        ('JB-QO',    'concrete shapes',                            '0'),
        ('JB-D0',    'fresh d0>=2 shapes via engine_ext',          '0'),
        ('TW-JB',    'transported-chamber re-instantiation',       '0'),
        ('MJB-DEV',  'teeth: garbled key caught',                  '0'),
        ('MJB-VTX',  'teeth: unsheared identification caught',     '0'),
        ('MJB-TREE', 'teeth: corrupted correction caught',         '0'),
        ('MJB-CREAD', 'teeth: spurious carry caught',              '0'),
    ]
    all_ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        nsm = COUNTS.get(fam, 0)
        verdict = 'GREEN' if obs == 0 else 'RED'
        if obs > 0:
            all_ok = False
        print('%-10s %-45s pred %-4s obs %5d (%6d)  %s'
              % (fam, desc, pred, obs, nsm, verdict))
    print('-' * 78)
    print('JB-CREAD censuses: scored %d | boundary %d | v=0 %d | R=0 %d | '
          'off-perimeter tree rows %d'
          % (COUNTS.get('JB-CREAD-SCORED', 0),
             COUNTS.get('JB-CREAD-BOUNDARY', 0),
             COUNTS.get('JB-CREAD-V0', 0),
             COUNTS.get('JB-CREAD-RZERO', 0),
             COUNTS.get('JB-TREE-OFFPERIM', 0)))
    print('byte census (JB-KEYEQ): %s'
          % json.dumps(RES['keyeq'], sort_keys=True))
    if VIOL:
        print('%d VIOLATIONS (first 40):' % len(VIOL))
        for v in VIOL[:40]:
            print('  ', v)
    RES['families'] = {fam: {'pred': pred,
                             'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0)}
                       for fam, desc, pred in fams}
    RES['violations'] = [list(v) for v in VIOL]
    RES['censuses'] = {k: COUNTS[k] for k in COUNTS if '-' in k and
                       k.split('-')[-1] in ('SCORED', 'BOUNDARY', 'V0',
                                            'RZERO', 'OFFPERIM')}
    RES['elapsed_s'] = round(time.time() - t0, 1)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_jb_checks_results.json')
    if not smoke:
        with open(out, 'w') as fh:
            json.dump(RES, fh, indent=1, default=repr)
    print('TOTAL samples: %d   elapsed %.1fs%s'
          % (sum(COUNTS.values()), time.time() - t0,
             '   JSON: ' + out if not smoke else '   (smoke: no json)'))
    print()
    print('J-B TREE-JUNCTION VERDICT (LAW-KEYED):')
    print('  expansion/polygon (JB-DEV/KEYEQ/SHEAR/VTX): %s'
          % ('GREEN' if not any(v[0] in ('JB-DEV', 'JB-KEYEQ', 'JB-SHEAR',
                                         'JB-VTX') for v in VIOL) else 'RED'))
    print('  tree/division (JB-ID/TREE/LINE): %s'
          % ('GREEN' if not any(v[0] in ('JB-ID', 'JB-TREE', 'JB-LINE')
                                for v in VIOL) else 'RED'))
    print('  (C-READ) transport (JB-EPS/CM/CREAD): %s'
          % ('GREEN' if not any(v[0] in ('JB-EPS', 'JB-CM', 'JB-CREAD')
                                for v in VIOL) else 'RED'))
    print('  chamber (TW-JB): %s'
          % ('GREEN' if not any(v[0] == 'TW-JB' for v in VIOL) else 'RED'))
    print('  teeth: %s' % ('CAUGHT' if not any(v[0].startswith('MJB')
                                               for v in VIOL)
                           else 'NO TEETH'))
    return 0 if all_ok else 1

if __name__ == '__main__':
    sys.exit(main(smoke=('--smoke' in sys.argv)))
