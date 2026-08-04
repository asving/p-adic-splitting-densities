#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_ja_checks.py -- J-A DICTIONARY runner (the machine leg of
lean/notes/openmath/GRTJA_PROOF_2026-08-08.md; two-commit seal).

Computes BOTH SIDES of every J-A equality (note sections 2-4) on the sealed
weld-probe roster (16 towers), the 5 concrete wild polynomials (fresh QO
extraction), and 4 FRESH d0 >= 2 shapes (d0 = 3 root keys + a p = 5 row,
certified through engine_ext per its standing rule).  Legs:
  harness side = iterlawn_pe_reimpl (committed, verbatim import);
  print side   = grt_weld_probe.GmnLeg (sealed fresh GMN transcription,
                 verbatim import -- NO new print transcription here);
  fresh side   = this runner's own integers/geometry (fresh modular-inverse
                 Bezout, geometric lattice scans, fresh weight chains) --
                 decorrelated from BOTH engines' internals.

========================= PREREGISTERED FAMILIES ==============================
EXT-GATE engine_ext standing rule honored: check_pins() + agreement_gate()
        re-run in-unit.                       PREDICT: 0 new violations.
JA-PIN  note THEOREM JA-PIN clauses 2-7 re-verified by FRESH legs on every
        level of every tower/QO/d0-shape: gcd(e,h)=1, e,h,g >= 1, psi monic
        irreducible (fresh no-root scan, deg <= 3) with psi(0) != 0, fresh
        weight chain == committed gam/wPhi == GmnLeg vnext/vkey (P-index),
        fresh Bezout (0 <= l < e) == committed T.l.        PREDICT: 0.
CK-VAL  note THEOREM JA-VAL: T.wlev(m, A) == G.vgen(m+1, A) for the whole
        sample pool at every SHARED-KEY level m (0..shared+1).  PREDICT: 0.
CK-EPS  note THEOREM JA-EPS: committed T.eps(m, V) == z_m^{-t_m(V)} with
        t_m(V) = (l*V - s_geo(V))/e computed from FRESH integers + geometric
        scan; plus the W2-L2 k-grid covariance eps(V)*z^{T_u} == z^{A*k},
        u = V + k*W_m, A = l*g*gamma fresh.                PREDICT: 0.
ORB-EPS note section-4(iii): eps_m(V)*z^{t + kappa*V} == z^{kappa*V - t + t}
        i.e. the kappa-shifted twist satisfies eps*z^{t_kappa} = z^{kappa*V},
        kappa in {1,2}.                                    PREDICT: 0.
CK-GRID note THEOREM JA-GRID (a)+(c): geometric brute scan (NO ell, NO eq12)
        for the T-side initial point == eq12 == l*V mod e; carry
        s(V)+s(V')-s(V+V') = e*delta, delta in {0,1}, delta == [s+s' >= e]
        (both sides computed independently).               PREDICT: 0.
CK-RES1 note (VD-1) = W2-L3, both sides fresh at m = 1:
        z1^{tau1(A)} * R_1(A)(z1) == eps_1(beta) * R_1v(A).  PREDICT: 0.
CK-RES  note THEOREM JA-RES per-slot law at m >= 2 (shared-key levels):
        proviso (VD-(m-1)) MACHINE-EVALUATED at every on-line digit; where
        it holds the sample is SCORED: print c_i == z_{m-1}^{-i*A_{m-1}}
        * harness C_i at EVERY attained abscissa (A_{m-1} from the fresh
        integer chain).  Proviso-failing samples are BOUNDARY (recorded
        with counts, not scored -- note JA-BOX-2).
        PREDICT: 0 scored violations; boundary census disclosed.
CK-VDM  note COROLLARY JA-VDIND forward direction: scored sample with the
        ABSOLUTE character trivial (z_{m-1}^{i*A_{m-1}} = 1 at every
        attained i)  ==>  (VD-m) evaluated identity holds.  PREDICT: 0.
CK-BPREF the JA-BOX-1 census (positive control): scored samples where the
        per-slot gauge is SLOT-DEPENDENT refute the blueprint's
        "slot-independent c" display.  PREDICT: >= 1 refuting sample on
        EACH designated row (BPREF_DESIGNATED; visibility pre-verified in
        the build-phase smoke, sealed below).
ORB-RES note section-4 orbit action, machine leg (W-2 section 4.3 had none):
        shifting ell_{m-2} by kappa*e_{m-2} AFTER key construction rescales
        rres(m, A) coefficientwise: c_j -> z_{m-1}^{-kappa*u0} *
        (z_{m-1}^{kappa*h})^j * c_j (h = level-m grid height, u0 = initial
        attained ordinate), kappa in {1,2}.                PREDICT: 0.
TW-INST note section-4 last bullet: J-A transports by RE-INSTANTIATION --
        the W-2 clause-3 transported ledger rebuilt as its own class-pin
        instance (SpecTower on RAW transported psis + its own GmnLeg), and
        the field-dependent families (JA-PIN/CK-VAL/CK-RES1/CK-RES/CK-VDM)
        re-run inside it.  NO cross-key operator equality is claimed (the
        MacLane representative caveat, note section 4(i)).  PREDICT: 0
        scored violations (boundary census disclosed separately).
JA-QO   the 5 concrete shapes: fresh extraction completes; PARI full-type
        tie; families above on the extracted towers.       PREDICT: 0.
JA-D0   the 4 fresh d0 >= 2 shapes: engine_ext double-leg certificate for
        the root key reduction (division + Frobenius) AND the committed
        tower's own no-root gate; families above; PARI (e,f) tie on the
        Zp top lifts.                                      PREDICT: 0.
MJ-EPS  teeth: the REFUTED Def-3.15 P-reading eps (l*s - l'*u; MutHTower,
        the N-1 garbled-prime genre) breaks CK-EPS on EACH designated row
        MJEPS_DESIGNATED.                                  PREDICT: caught.
MJ-VAL  teeth: the UNSHEARED valuation (drop the e-factor; the T-F
        7,472-violation genre) differs from wlev on EACH designated row
        MJVAL_DESIGNATED.                                  PREDICT: caught.
MJ-GRID teeth: the garbled grid s := l'*V mod e differs from the geometric
        scan on EACH designated row MJGRID_DESIGNATED.     PREDICT: caught.

BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest): a reduced-roster smoke
(T2A/T2B/T3A/T3E/I4B + the QO/d0 legs, reduced pools) ran during
construction.  It (i) fixed two runner-local bugs (tuple-vs-list memo keys;
1-read extracted towers break the committed window/split machinery, so the
pool builder guards NR = 1 and adds the top lift -- engines untouched);
(ii) pre-verified teeth visibility (MJ-EPS 3/3, MJ-VAL 2/2, MJ-GRID 2/2
designated rows caught) and the CK-BPREF designations: T2A/T3A/T3E FIRE;
T2B and T3B were checked and CANNOT fire (their z-letters have order 2 and
attained slots are spaced e = 2, so the gauge character is constant on
every attained set) -- the sealed designation is the confirmed triple;
(iii) confirmed the proviso machinery: I4B produced boundary rows (the
known W-2 collapse-boundary tower), all other smoked rows scored fully.
Smoke verdict: ALL families GREEN (4,409 samples).  Sealed predictions
above are the note's displayed laws, not smoke-fitted: CK-RES/CK-VDM/
TW-INST predictions are 0 AS QUANTIFIED (scored-where-proviso-holds),
which is the theorem's own displayed conditionality.
Deterministic; exact arithmetic; no RNG.  Outputs:
grt_ja_checks_output.txt (tee'd by caller), grt_ja_checks_results.json.
"""
import sys, os, json, time, collections
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_w2_checks as GW2
import engine_ext as EE
import grb_order2_check as GRB

VIOL = []
COUNTS = collections.defaultdict(int)
RES = {'towers': {}, 'qo': {}, 'd0': {}, 'tw': {}, 'boundary': {},
       'bpref': {}, 'mut': {}, 'families': {}}

def note(fam, n=1):
    COUNTS[fam] += n

def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))

# --------------------------------------------------------- fresh helpers
def fresh_bez(e, h):
    """fresh normalized Bezout: 0 <= l < e, l*h ~= 1 mod e (l = 0 at e = 1);
    l' = (1 - l*h)//e  so  l*h + l'*e = 1."""
    l = GWP.modinv_ell(h, e)
    return l, (1 - l*h)//e

def geo_split(V, e, h):
    """GEOMETRIC leg (no ell, no eq12): smallest nonneg abscissa x on the
    line {e*y + x*h = V} with integer ordinate; returns (s, u)."""
    for x in range(e):
        if (V - x*h) % e == 0:
            return x, (V - x*h)//e
    raise AssertionError('no integer point (gcd violated?)')

def fresh_weights(T):
    """fresh gamma/wPhi chains from the reads alone."""
    NR = T.NR
    gam = [None]*(NR+1); wPhi = [0]*(NR+1)
    gam[1] = T.h[0]
    wPhi[1] = T.e[0]*T.g[0]*gam[1]
    for j in range(1, NR):
        gam[j+1] = T.e[j]*wPhi[j] + T.h[j]
        wPhi[j+1] = T.e[j]*T.g[j]*gam[j+1]
    return gam, wPhi

def fresh_A(T, m):
    """A_m = l_{m-1} g_{m-1} gamma_m, all-fresh integers (m >= 1)."""
    gam, _ = fresh_weights(T)
    lf, _ = fresh_bez(T.e[m-1], T.h[m-1])
    return lf*T.g[m-1]*gam[m]

def shared_upto(T, G):
    """max L >= 0 with Phi_q == phi_{q+1} byte-for-byte for all 1 <= q <= L."""
    L = 0
    for q in range(1, T.n + 1):
        if tuple(T.Phi[q]) == tuple(G.phi[q+1]):
            L = q
        else:
            break
    return L

def sample_pool(T, small=False):
    """deterministic sample polynomials: anchors + one anchor product +
    lifts + realize outputs + a pi-shift."""
    P = T.P
    pool = []
    if T.NR >= 2:            # ITL.split/window_reps need >= 2 reads
        W1 = ITL.window_reps(T, 3 if small else 4)
        for ga in W1:
            for r in range(0, T.n + 1):
                pool.append(tuple(T.tanch(ga, r)))
        if len(W1) >= 2:
            pool.append(tuple(P.mul(T.tanch(W1[0], T.n), T.tanch(W1[-1], T.n))))
            pool.append(tuple(P.mul(T.tanch(W1[0], T.n), T.tanch(W1[1], T.n))))
            pool.append(tuple(P.mul(T.tanch(W1[-1], T.n), T.tanch(W1[-1], T.n))))
    else:                    # 1-read towers (QO extractions): monomial pool
        for a in range(0, 2):
            for b in range(0, 3):
                pool.append(tuple(P.scal(T.R.pi_pow(a), P.pow(T.Phi[0], b))))
    for m in range(T.n + 1):
        pool.append(tuple(T.Phi[m]))
    pool.append(tuple(GWP.top_lift(T)))
    for m in range(1, T.NR):
        Wm = T.e[m-1]*T.g[m-1]*T.gam[m]
        K = T.K[m]
        taus = [K.one(), T.z[m]] if not small else [T.z[m]]
        for db in range(0, 2 if small else 3):
            for t_ in taus:
                try:
                    pool.append(tuple(T.realize(m, t_, Wm + db)))
                except AssertionError:
                    pass
    pool.append(tuple(P.scal(T.R.pi_pow(1), pool[0])))
    out, seen = [], set()
    for f in pool:
        if f and f not in seen:
            seen.add(f); out.append(f)
    return out

# ============================ family checks ==================================
def ja_pin(T, G, tag):
    """THEOREM JA-PIN clauses 2-7, fresh legs."""
    gam_f, wPhi_f = fresh_weights(T)
    for j in range(T.NR):
        note('JA-PIN')
        e, h, g = T.e[j], T.h[j], T.g[j]
        ok = (e >= 1 and h >= 1 and g >= 1 and gcd(e, h) == 1)
        if not ok:
            viol('JA-PIN', tag, 'read datum fails at j=%d' % j); continue
        lf, lpf = fresh_bez(e, h)
        if not (lf == T.l[j] and lpf == T.lp[j] and 0 <= lf < max(e, 1) + 1):
            viol('JA-PIN', tag, 'Bezout pin fails at j=%d' % j)
        psi = T.psi[j]; Kj = T.K[j]
        if psi[-1] != Kj.one() or Kj.is_zero(psi[0]) or len(psi) != g + 1:
            viol('JA-PIN', tag, 'psi monic/psi(0)/deg fails at j=%d' % j)
        if g >= 2:
            if g > 3:
                viol('JA-PIN', tag, 'irreducibility scan capped (g=%d)' % g)
            else:  # deg 2/3: no-root scan suffices over a field
                for a in Kj.elems():
                    v = Kj.zero()
                    for c in reversed(psi):
                        v = Kj.add(Kj.mul(v, a), c)
                    if Kj.is_zero(v):
                        viol('JA-PIN', tag, 'psi_%d has a root' % j); break
        # weight chain: fresh == committed == GmnLeg (P-index clause 7)
        if gam_f[j+1] != T.gam[j+1] or wPhi_f[j+1] != T.wPhi[j+1]:
            viol('JA-PIN', tag, 'fresh weight chain != committed at j=%d' % j)
        if G.vnext[j+1] != gam_f[j+1] or G.vkey[j+2] != wPhi_f[j+1]:
            viol('JA-PIN', tag, 'GmnLeg vnext/vkey != fresh chain at j=%d' % j)

def ck_val(T, G, tag, pool, fam='CK-VAL'):
    cap = min(T.NR, shared_upto(T, G) + 1)
    for A in pool:
        for m in range(0, cap + 1):
            if m > T.NR:
                continue
            note(fam)
            try:
                wh = T.wlev(m, tuple(A))
                vg = G.vgen(m + 1, list(A))
            except AssertionError as ex:
                viol(fam, tag, 'val eval failed m=%d: %s' % (m, ex)); continue
            if wh != vg:
                viol(fam, tag, 'w_%d = %s != v_%d = %s' % (m, wh, m+1, vg))

def ck_eps(T, tag):
    for m in range(1, T.NR):
        e, h = T.e[m-1], T.h[m-1]
        lf, _ = fresh_bez(e, h)
        gam_f, _ = fresh_weights(T)
        Wm = T.e[m-1]*T.g[m-1]*gam_f[m]
        Af = lf*T.g[m-1]*gam_f[m]
        K = T.K[m]
        for V in range(0, 2*Wm + 2*e + 3):
            s, u = geo_split(V, e, h)
            num = lf*V - s
            if num % e != 0:
                viol('CK-EPS', tag, 't not integral m=%d V=%d' % (m, V))
                continue
            t = num // e
            note('CK-EPS')
            if T.eps(m, V) != ITL.fpow(K, T.z[m], -t):
                viol('CK-EPS', tag, 'eps != z^-t at m=%d V=%d' % (m, V))
            for k in (1, 2, 3):        # W2-L2 k-grid covariance
                uu = V + k*Wm
                Tk = (lf*uu - s)
                if Tk % e != 0:
                    viol('CK-EPS', tag, 'T_u not integral m=%d V=%d k=%d'
                         % (m, V, k)); continue
                lhs = K.mul(T.eps(m, V), ITL.fpow(K, T.z[m], Tk // e))
                if lhs != ITL.fpow(K, T.z[m], Af*k):
                    viol('CK-EPS', tag, 'k-grid covariance fails m=%d V=%d k=%d'
                         % (m, V, k))
            for kap in (1, 2):         # ORB-EPS: t_kappa = t + kappa*V
                note('ORB-EPS')
                lhs = K.mul(T.eps(m, V), ITL.fpow(K, T.z[m], t + kap*V))
                if lhs != ITL.fpow(K, T.z[m], kap*V):
                    viol('ORB-EPS', tag, 'orbit eps fails m=%d V=%d kap=%d'
                         % (m, V, kap))

def ck_grid(T, tag):
    for j in range(T.NR):
        e, h = T.e[j], T.h[j]
        lf, _ = fresh_bez(e, h)
        Vcap = 3*e*h + 2*e + 3
        for V in range(0, Vcap):
            note('CK-GRID')
            s, u = geo_split(V, e, h)
            s2, u2 = ITL.eq12(V, e, h)
            if not (s == s2 == (lf*V) % e and u == u2):
                viol('CK-GRID', tag, 'initial point mismatch j=%d V=%d' % (j, V))
        for V in range(0, 2*e + 2):
            for Vp in range(0, 2*e + 2):
                note('CK-GRID')
                s, _ = geo_split(V, e, h)
                sp, _ = geo_split(Vp, e, h)
                ss, _ = geo_split(V + Vp, e, h)
                d = s + sp - ss
                if d not in (0, e*1) or (d == e) != (s + sp >= e):
                    viol('CK-GRID', tag, 'carry clause fails j=%d (%d,%d)'
                         % (j, V, Vp))

def vd_eval(T, G, q, A):
    """(VD-q) evaluated identity at A (q >= 1): returns True/False, or None
    on a degenerate evaluation (off-grid integrality)."""
    At = tuple(A)
    Kq = T.K[q]
    try:
        beta = T.wlev(q, At)
        if beta is None:
            return None
        _, _, _, ssub, _, _ = G._support(q, list(At))
        Rl = G.rres(q, list(At))
        rd = T.read(q, beta, At)
    except AssertionError:
        return None
    num = ssub - T.l[q-1]*beta
    if num % T.e[q-1] != 0:
        return None
    tau = num // T.e[q-1]
    pv = Kq.zero()
    for jj, cc in enumerate(Rl):
        pv = Kq.add(pv, Kq.mul(Kq.from_base(cc), ITL.fpow(Kq, T.z[q], jj)))
    lhs = Kq.mul(ITL.fpow(Kq, T.z[q], tau), pv)
    rhs = Kq.mul(T.eps(q, beta), rd)
    return lhs == rhs

def ck_res1(T, G, tag, pool, fam='CK-RES1'):
    for A in pool:
        note(fam)
        r = vd_eval(T, G, 1, A)
        if r is None:
            viol(fam, tag, 'VD-1 degenerate evaluation (unexpected)')
        elif r is False:
            viol(fam, tag, 'VD-1 fails on a pool sample')

def ck_res(T, G, tag, pool, fams=('CK-RES', 'CK-VDM', 'CK-BPREF')):
    """per-slot law + VDIND forward + blueprint-refutation census.
    Returns (scored, boundary, bpref_hits)."""
    FR, FV, FB = fams
    capm = min(T.NR, shared_upto(T, G) + 1)
    scored = boundary = bpref = 0
    for A in pool:
        for m in range(2, capm + 1):
            At = tuple(A)
            e = T.e[m-1]
            Km1 = T.K[m-1]
            try:
                beta = T.wlev(m, At)
                Cs = T.read_coeffs(m, beta, At)
                dv, pts, att, s0, s1, _ = G._support(m, list(At))
                Rl = G.rres(m, list(At))
            except AssertionError as ex:
                note(FR)
                viol(FR, tag, 'res eval failed m=%d: %s' % (m, ex))
                continue
            s_eq, _ = ITL.eq12(beta, e, T.h[m-1])
            # proviso: VD-(m-1) at every attained digit
            prov = True
            for i in att:
                pr = vd_eval(T, G, m-1, dv[i])
                if pr is not True:
                    prov = False
                    break
            if not prov:
                boundary += 1
                note('CK-RES-BOUNDARY')
                continue
            scored += 1
            note(FR)
            Af = fresh_A(T, m-1)      # A_{m-1}, fresh integers
            ok = True
            gauges = []
            for i in att:
                if (i - s0) % e != 0 or (i - s_eq) % e != 0:
                    ok = False; break
                c_prn = Rl[(i - s0)//e]
                C_har = Cs.get((i - s_eq)//e)
                if C_har is None:
                    ok = False; break
                want = Km1.mul(ITL.fpow(Km1, T.z[m-1], -i*Af), C_har)
                gauges.append(ITL.fpow(Km1, T.z[m-1], -i*Af))
                if c_prn != want:
                    ok = False; break
            if not ok:
                viol(FR, tag, 'per-slot law fails m=%d (scored sample)' % m)
                continue
            # CK-VDM: absolute character trivial ==> VD-m
            note(FV)
            triv = all(ITL.fpow(Km1, T.z[m-1], i*Af) == Km1.one() for i in att)
            if triv:
                r = vd_eval(T, G, m, At)
                if r is not True:
                    viol(FV, tag, 'VDIND forward fails m=%d' % m)
            # CK-BPREF: slot-DEPENDENT gauge refutes the blueprint display
            if len(set(gauges)) > 1:
                bpref += 1
                note(FB)
    return scored, boundary, bpref

def orb_res(T, G, tag, pool):
    """ORB-RES: ell-shift rescaling law on fixed keys."""
    capm = min(T.NR, shared_upto(T, G) + 1)
    for A in pool[:8]:
        for m in range(2, capm + 1):
            A_l = list(A)
            try:
                dv, pts, att, s0, s1, _ = G._support(m, A_l)
                Rl = G.rres(m, A_l)
            except AssertionError:
                continue
            u0 = pts[s0]
            hgt = G.h[m]              # level-m grid height = h_{m-1}^har
            Km1 = T.K[m-1]
            for kap in (1, 2):
                note('ORB-RES')
                old = G.ell[m-1]
                G.ell[m-1] = old + kap*G.e[m-1]
                try:
                    Rl2 = G.rres(m, A_l)
                except AssertionError as ex:
                    viol('ORB-RES', tag, 'shifted rres failed m=%d: %s' % (m, ex))
                    Rl2 = None
                finally:
                    G.ell[m-1] = old
                if Rl2 is None:
                    continue
                if len(Rl2) != len(Rl):
                    viol('ORB-RES', tag, 'length change m=%d kap=%d' % (m, kap))
                    continue
                base = ITL.fpow(Km1, T.z[m-1], -kap*u0)
                stepc = ITL.fpow(Km1, T.z[m-1], kap*hgt)
                fac = base
                bad = False
                for jj in range(len(Rl)):
                    if Rl2[jj] != Km1.mul(fac, Rl[jj]):
                        bad = True; break
                    fac = Km1.mul(fac, stepc)
                if bad:
                    viol('ORB-RES', tag, 'orbit rescale law fails m=%d kap=%d'
                         % (m, kap))

# ------------------------------------------------------------ tower drivers
def run_families(T, G, tag, small=False, fam_map=None):
    """the field-dependent + integer families on one (T, G) instance."""
    fm = fam_map or {}
    pool = sample_pool(T, small=small)
    ja_pin(T, G, tag)
    ck_val(T, G, tag, pool, fam=fm.get('CK-VAL', 'CK-VAL'))
    ck_eps(T, tag)
    ck_grid(T, tag)
    ck_res1(T, G, tag, pool, fam=fm.get('CK-RES1', 'CK-RES1'))
    sc, bd, bp = ck_res(T, G, tag, pool,
                        fams=(fm.get('CK-RES', 'CK-RES'),
                              fm.get('CK-VDM', 'CK-VDM'),
                              fm.get('CK-BPREF', 'CK-BPREF')))
    orb_res(T, G, tag, pool)
    RES['boundary'][tag] = {'scored': sc, 'boundary': bd, 'bpref': bp}
    return sc, bd, bp

def tw_inst(T, spec, tag):
    """re-instantiation in the W-2 transported chamber (note section 4)."""
    Gf, ledger, fails = GW2.transport_leg(T, tag)
    note('TW-INST')
    if fails or Gf is None:
        viol('TW-INST', tag, 'transport failed: %s' % fails)
        return
    psi_specs = [[('RAW', c) for c in Gf.psis[j+1]] for j in range(T.NR)]
    R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
    v0 = len(VIOL)
    try:
        T2 = GWP.SpecTower(tag + '/twinst', R2, spec['d0'], spec['Phi0'],
                           spec['reads'], psi_specs)
        G2 = GWP.gmn_from_tower(T2)
        pool2 = sample_pool(T2, small=True)
        ja_pin(T2, G2, tag + '/tw')
        ck_val(T2, G2, tag + '/tw', pool2, fam='TW-INST')
        ck_res1(T2, G2, tag + '/tw', pool2, fam='TW-INST')
        sc, bd, bp = ck_res(T2, G2, tag + '/tw', pool2,
                            fams=('TW-INST', 'TW-INST', 'TW-INST-BPREF'))
        RES['tw'][tag] = {'ledger': ledger, 'scored': sc, 'boundary': bd}
    except AssertionError as ex:
        viol('TW-INST', tag, 'transported instance build failed: %s' % ex)
        return
    # re-tag JA-PIN violations raised inside the transported instance
    for k in range(v0, len(VIOL)):
        f, tg, msg = VIOL[k]
        if f == 'JA-PIN':
            VIOL[k] = ('TW-INST', tg, '[JA-PIN] %s' % msg)

def qo_leg(pari):
    for name, p, fc in GWP.QO_SHAPES:
        tag = 'QO:%s/Q%d' % (name, p)
        R = ITL.Zp(p)
        leg, levels, status = GWP.qo_extract(R, fc)
        note('JA-QO')
        rec = {'status': status}
        if status != 'complete':
            viol('JA-QO', tag, 'extraction did not complete: %s' % status)
            RES['qo'][tag] = rec
            continue
        E = 1; F_ = 1
        for (e, h, psi) in levels:
            E *= e; F_ *= (len(psi) - 1)
        if pari is not None:
            ft = GWP.pari_fulltype(pari, fc, p)
            rec['pari_full'] = str(ft)
            deg = len(fc) - 1
            if (E*F_ == deg and ft != ((E, F_),)) or \
               (E*F_ != deg and (E, F_) not in ft):
                viol('JA-QO', tag, 'extracted (%d,%d) vs PARI %s' % (E, F_, ft))
        reads = [(e, h, len(psi)-1) for (e, h, psi) in levels]
        psi_specs = [[('RAW', c) for c in psi] for (e, h, psi) in levels]
        try:
            T = GWP.SpecTower(tag, ITL.Zp(p), 1, [0, 1], reads, psi_specs)
            G = GWP.gmn_from_tower(T)
            run_families(T, G, tag, small=True)
        except AssertionError as ex:
            viol('JA-QO', tag, 'extracted-type tower failed: %s' % ex)
        RES['qo'][tag] = rec

D0_SPECS = [
 dict(id='JD5A', ring='Zp', p=5, d0=2, Phi0=[2, 0, 1],
      reads=[(2,1,1),(2,1,1)], psi=[[('X',1),1],[('z',1,1),1]], pairn=4),
 dict(id='JD3A', ring='Zp', p=2, d0=3, Phi0=[1, 1, 0, 1],
      reads=[(2,1,1),(2,1,1)], psi=[[('X',1),1],[('z',1,1),1]], pairn=4),
 dict(id='JD3B', ring='Zp', p=3, d0=3, Phi0=[1, 2, 0, 1],
      reads=[(3,1,1),(2,1,1)], psi=[[('X',1),1],[('z',1,1),1]], pairn=4),
 dict(id='JD3C', ring='Fpt', p=2, d0=3, Phi0=[1, 1, 0, 1],
      reads=[(2,1,2),(2,1,1)], psi=[[1,1,1],[('z',1,1),1]], pairn=4),
]

def d0_leg(pari):
    for spec in D0_SPECS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        note('JA-D0')
        # engine_ext double-leg certificate for the root-key reduction
        F = GRB.mk_field_base(spec['p'], [0, 1])
        A = [((c % spec['p']),) for c in spec['Phi0']]
        try:
            cert = EE.irr_certificate(F, A)
            if not cert['irreducible']:
                viol('JA-D0', tag, 'engine_ext says phibar REDUCIBLE')
        except (AssertionError, ValueError) as ex:
            viol('JA-D0', tag, 'engine_ext certificate failed: %s' % ex)
        try:
            T = ITL.build_tower(spec)     # the committed no-root gate leg
        except AssertionError as ex:
            viol('JA-D0', tag, 'committed tower build failed: %s' % ex)
            continue
        G = GWP.gmn_from_tower(T)
        run_families(T, G, tag, small=True)
        tw_inst(T, spec, tag)
        if spec['ring'] == 'Zp' and pari is not None:
            E = 1; F_ = T.d0
            for (e, h, g) in spec['reads']:
                E *= e; F_ *= g
            GWP.pari_ef(pari, GWP.top_lift(T), spec['p'], E, F_, tag, 'har')
            while GWP.VIOL:
                f, tg, dd = GWP.VIOL.pop()
                viol('JA-D0', tag, '[PARI/%s] %s' % (f, dd))
        RES['d0'][tag] = {'ok': True}

# ------------------------------------------------------------------- teeth
MJEPS_DESIGNATED = ['T2A', 'T2B', 'T2D']
MJVAL_DESIGNATED = ['T2A', 'T2C']
MJGRID_DESIGNATED = ['T2A', 'T2B']
BPREF_DESIGNATED = ['T2A', 'T3A', 'T3E']

def vgen_unsh(G, k, g):
    """the UNSHEARED (garbled) valuation: drop the e-factor."""
    g = G.P.canon(list(g))
    if not g:
        return None
    if k == 1:
        return min(G.R.val(c) for c in g if not G.R.is_zero(c))
    dv = G.P.dev(g, G.phi[k-1])
    return min(vgen_unsh(G, k-1, a) + i*G.vnext[k-1]
               for i, a in enumerate(dv) if a)

def teeth():
    for tid in MJEPS_DESIGNATED:
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s/MJ' % (spec['ring'], spec['p'], spec['id'])
        R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
        TH = GWP.MutHTower(tag, R2, spec['d0'], spec['Phi0'], spec['reads'],
                           [ps for ps in spec['psi']])
        caught = 0
        for m in range(1, TH.NR):
            e, h = TH.e[m-1], TH.h[m-1]
            lf, _ = fresh_bez(e, h)
            K = TH.K[m]
            for V in range(0, 3*e*h + 2*e + 3):
                s, _ = geo_split(V, e, h)
                t = (lf*V - s)//e
                if TH.eps(m, V) != ITL.fpow(K, TH.z[m], -t):
                    caught += 1
        note('MJ-EPS')
        RES['mut'][tag + '/eps'] = caught
        if caught == 0:
            viol('MJ-EPS', tag, 'P-reading eps NOT caught (no teeth)')
    for tid in MJVAL_DESIGNATED:
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s/MJ' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        pool = sample_pool(T, small=True)
        cap = min(T.NR, shared_upto(T, G) + 1)
        caught = 0
        for A in pool:
            for m in range(0, cap + 1):
                try:
                    if vgen_unsh(G, m+1, list(A)) != T.wlev(m, tuple(A)):
                        caught += 1
                except AssertionError:
                    caught += 1
        note('MJ-VAL')
        RES['mut'][tag + '/val'] = caught
        if caught == 0:
            viol('MJ-VAL', tag, 'unsheared valuation NOT caught (no teeth)')
    for tid in MJGRID_DESIGNATED:
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s/MJ' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        caught = 0
        for j in range(T.NR):
            e, h = T.e[j], T.h[j]
            _, lpf = fresh_bez(e, h)
            for V in range(0, 3*e*h + 2*e + 3):
                s, _ = geo_split(V, e, h)
                if (lpf*V) % e != s:
                    caught += 1
        note('MJ-GRID')
        RES['mut'][tag + '/grid'] = caught
        if caught == 0:
            viol('MJ-GRID', tag, 'garbled grid NOT caught (no teeth)')

# ================================== main =====================================
def main(smoke=False):
    t0 = time.time()
    print('grt_ja_checks -- J-A dictionary runner (GRTJA_PROOF machine leg)')
    print('harness: iterlawn_pe_reimpl (committed); print: grt_weld_probe.GmnLeg')
    print('(sealed); fresh legs: this runner\'s own integers/geometry')
    print()
    # EXT-GATE (engine_ext standing rule)
    v0 = len(EE.VIOL)
    EE.check_pins()
    gate_new = EE.agreement_gate(full=False)
    note('EXT-GATE', 1)
    if gate_new or len(EE.VIOL) > v0:
        viol('EXT-GATE', 'engine_ext', '%d new violations' % (len(EE.VIOL)-v0))
    print('  [%6.1fs] EXT-GATE done (new violations: %d)'
          % (time.time()-t0, len(EE.VIOL)-v0))
    pari = GWP.pari_init()
    roster = GWP.TOWERS if not smoke else \
        [s for s in GWP.TOWERS if s['id'] in ('T2A', 'T2B', 'T3A', 'T3E', 'I4B')]
    for spec in roster:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        tA = time.time()
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        sc, bd, bp = run_families(T, G, tag, small=smoke)
        if spec['id'] in BPREF_DESIGNATED and bp == 0:
            viol('CK-BPREF', tag, 'designated row has NO refuting sample')
        tw_inst(T, spec, tag)
        print('  [%6.1fs] %-16s done (%.1fs; scored %d, boundary %d, bpref %d)'
              % (time.time()-t0, tag, time.time()-tA, sc, bd, bp))
    qo_leg(pari)
    print('  [%6.1fs] QO leg done' % (time.time()-t0))
    d0_leg(pari)
    print('  [%6.1fs] d0>=2 leg done' % (time.time()-t0))
    teeth()
    print('  [%6.1fs] teeth done' % (time.time()-t0))
    print()
    print('=' * 78)
    print('PREDICTED vs OBSERVED (violation counts; samples in parentheses)')
    print('=' * 78)
    fams = [
        ('EXT-GATE', 'engine_ext pins + agreement gate re-run',   '0'),
        ('JA-PIN',   'class-pin clauses 2-7, fresh legs',         '0'),
        ('CK-VAL',   'JA-VAL: wlev == vgen (shared levels)',      '0'),
        ('CK-EPS',   'JA-EPS: eps == z^-t fresh + k-grid',        '0'),
        ('ORB-EPS',  'orbit eps covariance',                      '0'),
        ('CK-GRID',  'JA-GRID: geometric == eq12 + carry',        '0'),
        ('CK-RES1',  'VD-1 both sides (m=1)',                     '0'),
        ('CK-RES',   'per-slot law (scored where proviso holds)', '0'),
        ('CK-VDM',   'VDIND forward (absolute character)',        '0'),
        ('CK-BPREF', 'JA-BOX-1 census (designated rows fire)',    '>=1/row'),
        ('ORB-RES',  'ell-shift rescale law, fixed keys',         '0'),
        ('TW-INST',  'transported-chamber re-instantiation',      '0'),
        ('JA-QO',    'concrete shapes: extraction + PARI + fams', '0'),
        ('JA-D0',    'fresh d0>=2 shapes via engine_ext + PARI',  '0'),
        ('MJ-EPS',   'teeth: P-reading eps caught',               '0'),
        ('MJ-VAL',   'teeth: unsheared valuation caught',         '0'),
        ('MJ-GRID',  'teeth: garbled grid caught',                '0'),
    ]
    all_ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        nsm = COUNTS.get(fam, 0)
        verdict = 'GREEN' if obs == 0 else 'RED'
        if obs > 0:
            all_ok = False
        print('%-9s %-46s pred %-7s obs %5d (%6d)  %s'
              % (fam, desc, pred, obs, nsm, verdict))
    print('-' * 78)
    nb = COUNTS.get('CK-RES-BOUNDARY', 0)
    nbp = COUNTS.get('CK-BPREF', 0)
    print('CK-RES boundary census (proviso-failing, recorded not scored): %d' % nb)
    print('CK-BPREF refuting samples (blueprint slot-independent form): %d' % nbp)
    if VIOL:
        print('%d VIOLATIONS (first 40):' % len(VIOL))
        for v in VIOL[:40]:
            print('  ', v)
    RES['families'] = {fam: {'pred': pred,
                             'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0)}
                       for fam, desc, pred in fams}
    RES['violations'] = [list(v) for v in VIOL]
    RES['boundary_total'] = nb
    RES['bpref_total'] = nbp
    RES['elapsed_s'] = round(time.time() - t0, 1)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_ja_checks_results.json')
    if not smoke:
        with open(out, 'w') as fh:
            json.dump(RES, fh, indent=1, default=repr)
    print('TOTAL samples: %d   elapsed %.1fs%s'
          % (sum(COUNTS.values()), time.time()-t0,
             '   JSON: ' + out if not smoke else '   (smoke: no json)'))
    print()
    print('J-A DICTIONARY VERDICT (LAW-KEYED):')
    print('  JA-PIN + operator equalities (JA-*/CK-*): %s'
          % ('ALL GREEN' if not any(v[0].startswith(('JA', 'CK', 'ORB'))
                                    for v in VIOL) else 'RED'))
    print('  transport (TW-INST): %s'
          % ('GREEN' if not any(v[0] == 'TW-INST' for v in VIOL) else 'RED'))
    print('  teeth: %s' % ('CAUGHT' if not any(v[0].startswith('MJ')
                                               for v in VIOL) else 'NO TEETH'))
    return 0 if all_ok else 1

if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
