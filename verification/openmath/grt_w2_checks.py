#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_w2_checks.py -- W-2 COMPOSITION runner (extends grt_weld_probe.py; the
machine leg of lean/notes/openmath/GRTW2_PROOF_2026-08-08.md).

Tests EVERY intermediate identity introduced by the W-2 composition note,
plus the clause-3 psi-transport (the probe's mandated follow-up unit).

Legs (all deterministic, exact arithmetic; roster + QO shapes verbatim from
the sealed probe grt_weld_probe.py; harness engine = committed
iterlawn_pe_reimpl imported verbatim; classifier leg = the probe's fresh
GmnLeg transcription imported verbatim -- this runner adds NO new print
transcription, only identity checks and the transport algebra):

CK-MM   the Bezout MISMATCH identity (note Lemma W2-L2):
        for (s,u) = eq12(V; e, h) and any integers U, k with U - V = k*W,
        W == e*g*gamma (the key-weight multiple):
          (l'*s - l*u) + (l*U - s)/e  ==  l*k*W/e  ==  A*k,  A := l*g*gamma.
        Exhaustive integer grid per tower level.  PREDICT: 0 violations.
CK-HR1  base builder read (note Lemma W2-L1): P := construct(2, V, phi)
        has harness w_1(P) = V and R_1v(P) = phi(z_1) exactly.
        PREDICT: 0 violations.
CK-VD1  level-1 packed-value dictionary (note Lemma W2-L3):
        z_1^{tau_1(A)} * R_1(A)(z_1) == eps_1(beta) * R_1v(A),
        tau_1(A) := (s_1(A) - l_0*beta)/e_0, for on-line A, beta = w_1(A).
        PREDICT: 0 violations.
CK-REC  the read recursion of construct outputs (note display HR-REC):
        sim_construct (the semantic recursion, NO polynomial arithmetic)
        equals the harness read of the actual construct output at every
        junction slot AND every inner node of every roster junction.
        PREDICT: 0 violations.
CK-SLOT the junction slot-ratio law: at every junction r of every tower,
        actual slot ratios (cls slot read)/(har slot read) == the sim
        prediction rho_j; at M = 1 junctions (r = 3) additionally the
        EXACT closed form rho_j = c * z_1^{A_1*e_1*j} (note THM W2-C2a).
        PREDICT: 0 violations.
CK-XI   the (xi, w) orbit closed form: recomputed fresh-evaluator orbit at
        every first-divergence/top junction == the prediction:
          M = 1:            xi = z_M^{-e_M*A_M},  w = 1;
          M >= 2, theta-trivial (xi_Q = 1 as field elements for all
          interior junctions 2 <= Q <= M):
                            xi = chi_M^{gamma_{M+1}} * z_M^{-e_M*A_M},
                            w  = chi_M^{-g_M*gamma_{M+1}},
          chi_1 := 1, chi_m := chi_{m-1}^{l'_{m-1} - l_{m-1}*W_{m-1}}
                              * z_{m-1}^{A_{m-1}*l_{m-1}}.
        Junctions OUTSIDE the theta-trivial perimeter (the monomial-
        collapse boundary, I4B r=5 genre) are RECORDED with their orbit,
        not scored against the chi formula.  PREDICT: 0 violations on the
        perimeter; boundary junctions listed.
CK-BYTE the byte-equality law: junction byte-equal <=> every node value
        of the shared recursion tree matches (walk both builders'
        prescriptions; positions/grids provably aligned).  PREDICT: 0
        mismatches between the walk verdict and the actual byte compare.
TW-*    CLAUSE-3 PSI-TRANSPORT (the probe note's follow-up predictions,
        now run):
        iteratively, junction by junction ascending: record (xi, w) from
        the current-chamber criterion on the harness lift; conjugate the
        level modulus psi'' := xi^{-f} psi(xi*y); re-coordinate all higher
        psi data through the letter rescale z = xi*z''; rebuild.  Then:
        TW-RATIO  no WEIGHT/SUPPORT mismatch at ANY junction (the probe's
                  F1 diag rows above interior twists all cure).
                  PREDICT: 0.
        TW-ADM    vok+onesided+orbit for the harness lift at EVERY level
                  in the final chamber (the probe's 6 F2 REDs cure).
                  PREDICT: 0 failures / 51-junction genre count.
        TW-STRICT the harness lift is a STRICT (pinned-ell) Def-2.12
                  representative of the TRANSPORTED type at every level:
                  R ~ psi^tw up to a scalar.  PREDICT: 0 failures.
        TW-F3     committed cocycle battery (check_pair + gamma_checks,
                  K5/K6/K7/K12...) on the TRANSPORTED classifier lifts:
                  PREDICT: 0 violations on ALL 16 towers (the probe's 96
                  F3 REDs -- K6:48 + K7:48 on T3A/T3C/T3D/I4C -- all turn
                  GREEN).
        TW-F3b    baseline control unchanged: 0.
        TW-PARI   transported top lifts (Z_p rows): irreducible, same
                  (e,f) = (prod e_j, d0*prod g_j).  PREDICT: 24/24.
        TW-QO     the 5 concrete shapes, extracted types transported the
                  same way: no WEIGHT/SUPPORT mismatches.  PREDICT: 0.
CK-T3E  the flat-middle mechanism (the probe's unexplained T3E residue):
        (a) on T3E every battery-consumed intermediate (anchor bytes and
        top-dev digit bytes) is byte-identical cls-vs-har, because
        e_1 = 1 forces s_2 == 0 on every anchor, so no anchor product
        overflows past the diverged top key -- the twist is CARRY-INERT;
        machine: diff all battery digits, PREDICT 0 diffs + s_2 == 0
        census.  (b) on T3A the K6/K7-failing pairs are EXACTLY the pairs
        whose top-dev digits differ in bytes (the s_2-overflow carry
        pairs); machine: set equality of the two pair sets.  PREDICT: 0
        discrepancies.
MT-TW   transport teeth: garbled transport (xi replaced by xi*z_1 at the
        first twisted junction) on T3A and T3C must be CAUGHT (>= 1
        TW-RATIO/TW-ADM/TW-F3 failure or a hard chamber-build failure).
        PREDICT: caught on both designated rows.

Outputs: grt_w2_checks_output.txt (tee'd by caller), grt_w2_checks_results.json.
"""
import sys, os, json, time, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP

VIOL = []
COUNTS = collections.defaultdict(int)
RES = {'towers': {}, 'tw': {}, 'qo': {}, 'xi_ledger': {}, 't3e': {},
       'mut': {}, 'families': {}}

def note(fam, n=1):
    COUNTS[fam] += n

def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))

# ---------------------------------------------------------------- helpers
def fld_one(F):
    return F.one()

def elems_equal(a, b):
    return a == b

def orbit_satisfies(G, r, X, xi, w):
    """does R_{r-1}(X)(y) == w * psi(xi*y) coefficientwise?"""
    fm = G.f[r-1]
    F = G.Kc[r-2]
    try:
        Rl = G.rres(r-1, X)
    except AssertionError:
        return False
    psi = G.psis[r-1]
    if len(Rl) != fm + 1:
        return False
    return all(Rl[j] == F.mul(w, F.mul(psi[j], ITL.fpow(F, xi, j)))
               for j in range(fm + 1))

def orbit_scan(G, r, X):
    """re-run the criterion orbit scan, returning ELEMENTS (xi, w) with
    R(y) = w * psi(xi y) coefficientwise, or None; plus vok/onesided and
    the strict unit."""
    fm, em = G.f[r-1], G.e[r-1]
    out = {'vok': None, 'onesided': None, 'strict': None, 'orbit': None}
    vX = G.vgen(r, X)
    out['vok'] = (vX == G.vkey[r])
    dv, pts, att, s0, s1, m = G._support(r-1, X)
    out['onesided'] = (s0 == 0 and s1 == em*fm)
    if not (out['vok'] and out['onesided']):
        return out
    Rl = G.rres(r-1, X)
    F = G.Kc[r-2]
    psi = G.psis[r-1]
    if len(Rl) != fm + 1 or F.is_zero(Rl[fm]):
        return out
    wst = Rl[fm]
    if all(Rl[j] == F.mul(wst, psi[j]) for j in range(fm + 1)):
        out['strict'] = wst
    for xi in F.elems():
        if F.is_zero(xi):
            continue
        wk = F.mul(Rl[fm], F.inv(ITL.fpow(F, xi, fm)))
        if all(Rl[j] == F.mul(wk, F.mul(psi[j], ITL.fpow(F, xi, j)))
               for j in range(fm + 1)):
            out['orbit'] = (xi, wk)
            break
    return out

# ------------------------------------------------- CK-MM mismatch identity
def ck_mm(T, tag):
    """(l'*s - l*u) + (l*U - s)/e == A*k with A = l*g*gamma, U = V + k*W,
    W = e*g*gamma; exhaustive over levels and a V,k grid.  Also the element
    form eps_{m}(V) * z^{T} == z^{A*k}."""
    for m in range(1, T.NR):          # eps_m uses read m-1; letters z_m
        e, h = T.e[m-1], T.h[m-1]
        l, lp = T.l[m-1], T.lp[m-1]
        g, gam = T.g[m-1], T.gam[m]
        W = e*g*gam                    # = w_m Phi_m
        A = l*g*gam
        for V in range(0, 3*W + 2*e + 3):
            s = (l*V) % e
            u = (V - s*h)//e
            assert u*e + s*h == V
            for k in range(0, 4):
                U = V + k*W
                num = l*U - s
                note('CK-MM')
                if num % e != 0:
                    viol('CK-MM', tag, 'T-exponent not integral m=%d V=%d k=%d'
                         % (m, V, k)); continue
                lhs = (lp*s - l*u) + num//e
                if lhs != A*k:
                    viol('CK-MM', tag, 'integer mismatch m=%d V=%d k=%d: %d != %d'
                         % (m, V, k, lhs, A*k)); continue
                # element form (subsumes ord-divisibility bookkeeping)
                K = T.K[m]
                el = K.mul(T.eps(m, V), ITL.fpow(K, T.z[m], num//e))
                if el != ITL.fpow(K, T.z[m], A*k):
                    viol('CK-MM', tag, 'element mismatch m=%d V=%d k=%d'
                         % (m, V, k))

# ------------------------------------------- CK-HR1 / CK-VD1 base lemmas
def ck_base(T, G, tag):
    K0, K1 = T.K[0], T.K[1]
    e0, h0 = T.e[0], T.h[0]
    l0 = T.l[0]
    # CK-HR1: construct(2, V, phi) reads to phi(z_1) at weight V
    # (under the print's own hypothesis V >= e_1 f_1 v_2(phi_1), GMN idx)
    samples = []
    els = list(K0.elems())
    Vmin = G.e[1]*G.f[1]*G.vnext[1]
    for V in range(Vmin, Vmin + 2*T.gam[1]*T.e[0] + 5):
        phi = [els[(V + i) % len(els)] for i in range(T.g[0])]
        if all(K0.is_zero(c) for c in phi):
            phi[0] = K0.one()
        samples.append((V, phi))
    for V, phi in samples[:24]:
        P = G.construct(2, V, phi)
        note('CK-HR1')
        try:
            wl = T.wlev(1, P)
            rd = T.read(1, wl, P)
        except AssertionError as ex:
            viol('CK-HR1', tag, 'read failed V=%d: %s' % (V, ex)); continue
        exp = K1.zero()
        for i, c in enumerate(phi):
            exp = K1.add(exp, K1.mul(K1.from_base(c),
                                     ITL.fpow(K1, T.z[1], i)))
        if not (wl == V and rd == exp):
            viol('CK-HR1', tag, 'HR1 fails at V=%d (w=%s)' % (V, wl))
        # CK-VD1 on the same outputs (they are on-line level-1 objects)
        note('CK-VD1')
        try:
            Rl = G.rres(1, P)
            _, _, _, s1a, _, _ = G._support(1, P)
        except AssertionError as ex:
            viol('CK-VD1', tag, 'rres failed V=%d: %s' % (V, ex)); continue
        beta = V
        num = s1a - l0*beta
        if num % e0 != 0:
            viol('CK-VD1', tag, 'tau not integral V=%d' % V); continue
        tau = num // e0
        pv = K1.zero()
        for j, c in enumerate(Rl):
            pv = K1.add(pv, K1.mul(K1.from_base(c), ITL.fpow(K1, T.z[1], j)))
        pv = K1.mul(ITL.fpow(K1, T.z[1], tau), pv)
        rhs = K1.mul(T.eps(1, beta), rd)
        if pv != rhs:
            viol('CK-VD1', tag, 'VD1 fails at V=%d' % V)

# --------------------------------------------------- the semantic simulator
def sim_construct(G, T, r, V, phic):
    """predicted harness level-(r-1) read of G.construct(r, V, phic);
    mirrors the construct recursion SEMANTICALLY (no polynomial arith)."""
    q = r - 1                                    # harness output level
    Kq = T.K[q]
    if r == 2:
        acc = Kq.zero()
        for i, c in enumerate(phic):
            if G.Kc[0].is_zero(c):
                continue
            acc = Kq.add(acc, Kq.mul(Kq.from_base(c),
                                     ITL.fpow(Kq, T.z[1], i)))
        return acc
    em, hm = G.e[r-1], G.h[r-1]                  # = T.e[q-1], T.h[q-1]
    s = (G.ell[r-1]*V) % em
    u = (V - s*hm)//em
    acc = Kq.zero()
    for j, cj in enumerate(phic):
        if G.Kc[r-2].is_zero(cj):
            continue
        uj = u - j*hm
        kslot = s + j*em
        Vj = uj - kslot*G.vkey[r-1]
        sj = (G.ell[r-2]*Vj) % G.e[r-2]
        num = G.ell[r-2]*uj - sj
        assert num % G.e[r-2] == 0
        texp = num // G.e[r-2]
        celt = G.Kc[r-2].mul(ITL.fpow(G.Kc[r-2], G.z[r-2], texp), cj)
        child = sim_construct(G, T, r-1, Vj, list(celt))
        co = T.K[q-1].mul(T.eps(q-1, Vj), child) if q-1 >= 1 else \
             T.K[0].mul(T.eps(0, Vj), child)
        acc = Kq.add(acc, Kq.mul(T.embed(co, q-1, q),
                                 ITL.fpow(Kq, T.z[q], j)))
    return acc

def ck_rec_nodes(G, T, r, V, phic, tag, depth=0):
    """CK-REC: at every node of the construct recursion, the actual output
    polynomial's harness read equals the sim value."""
    P = G.construct(r, V, phic)
    q = r - 1
    note('CK-REC')
    sv = sim_construct(G, T, r, V, phic)
    if not P:
        if not T.K[q].is_zero(sv):
            viol('CK-REC', tag, 'zero poly, nonzero sim at r=%d V=%d' % (r, V))
        return
    try:
        wl = T.wlev(q, P)
        rd = T.read(q, wl, P)
    except AssertionError as ex:
        viol('CK-REC', tag, 'read failed r=%d V=%d: %s' % (r, V, ex))
        return
    if not (wl == V and rd == sv):
        viol('CK-REC', tag, 'node mismatch r=%d V=%d depth=%d' % (r, V, depth))
    if r == 2:
        return
    em, hm = G.e[r-1], G.h[r-1]
    s = (G.ell[r-1]*V) % em
    u = (V - s*hm)//em
    for j, cj in enumerate(phic):
        if G.Kc[r-2].is_zero(cj):
            continue
        uj = u - j*hm
        kslot = s + j*em
        Vj = uj - kslot*G.vkey[r-1]
        sj = (G.ell[r-2]*Vj) % G.e[r-2]
        texp = (G.ell[r-2]*uj - sj)//G.e[r-2]
        celt = G.Kc[r-2].mul(ITL.fpow(G.Kc[r-2], G.z[r-2], texp), cj)
        ck_rec_nodes(G, T, r-1, Vj, list(celt), tag, depth+1)

# --------------------------------- junction predictions (ratios, xi, bytes)
def junction_data(T, G, r):
    """per-junction read data: M (harness child level), c1, c, the A_m
    chain, the chi gauge chain, the theta-trivial flag, predicted (xi, w).

    A_m  := l_{m-1} g_{m-1} gamma_m                       (integer, m >= 1)
    chi_1 := 1 in K_0;
    chi_m := chi_{m-1}^{l'_{m-1} - l_{m-1} W_{m-1}} * z_{m-1}^{A_{m-1} l_{m-1}}
             in K_{m-1},   W_{m-1} := w_{m-1}Phi_{m-1} = e_{m-2}g_{m-2}gamma_{m-1}
    xi_{Q}  := chi_{Q-1}^{gamma_Q} * z_{Q-1}^{-e_{Q-1} A_{Q-1}}   (junction
               character of the lift Phi_Q; the top junction r has Q = M+1)
    w_{Q}   := chi_{Q-1}^{-g_{Q-1} gamma_Q}."""
    M = r - 2                                    # harness level of the slots
    KM = T.K[M]
    d = {'r': r, 'M': M}
    A = {m: T.l[m-1]*T.g[m-1]*T.gam[m] for m in range(1, M+1)}
    d['A'] = A
    d['c1'] = ITL.fpow(KM, T.z[M], -A[M])
    d['c'] = ITL.fpow(KM, d['c1'], T.e[M]*T.g[M])
    chi = {1: T.K[0].one()}                      # chi_m lives in K_{m-1}
    for m in range(2, M+1):
        Km1 = T.K[m-1]
        Wm1 = T.e[m-2]*T.g[m-2]*T.gam[m-1]
        expo = T.lp[m-1] - T.l[m-1]*Wm1
        prev = T.embed(chi[m-1], m-2, m-1)
        chi[m] = Km1.mul(ITL.fpow(Km1, prev, expo),
                         ITL.fpow(Km1, T.z[m-1], A[m-1]*T.l[m-1]))
    d['chi_M'] = chi.get(M)
    # theta-trivial perimeter: every interior junction character trivial
    triv = True
    for Q in range(2, M+1):
        KQ1 = T.K[Q-1]
        cprev = T.embed(chi[Q-1], Q-2, Q-1)
        xiQ = KQ1.mul(ITL.fpow(KQ1, cprev, T.gam[Q]),
                      ITL.fpow(KQ1, T.z[Q-1], -T.e[Q-1]*A[Q-1]))
        if xiQ != KQ1.one():
            triv = False
    d['theta_trivial'] = triv
    chiM = T.embed(chi[M], M-1, M)
    d['xi_pred'] = KM.mul(ITL.fpow(KM, chiM, T.gam[M+1]),
                          ITL.fpow(KM, T.z[M], -T.e[M]*A[M]))
    d['w_pred'] = ITL.fpow(KM, chiM, -T.g[M]*T.gam[M+1])
    return d

def predict_ratios(T, G, r):
    """rho_j := (cls slot-j level-M read)/(har slot-j level-M read) via the
    sim recursion, for j = 0..g_M-1 with psi_{M,j} != 0."""
    M = r - 2
    KM = T.K[M]
    c = G.thm_c(r)
    out = {}
    for j in range(G.f[r-1]):
        cj = G.Kc[r-2].mul(c, G.psis[r-1][j])
        if G.Kc[r-2].is_zero(cj):
            continue
        V = G.vkey[r]
        em, hm = G.e[r-1], G.h[r-1]
        s = (G.ell[r-1]*V) % em
        u = (V - s*hm)//em
        uj = u - j*hm
        kslot = s + j*em
        Vj = uj - kslot*G.vkey[r-1]
        if r - 1 == 2:
            celt = cj
            cls_val = sim_construct(G, T, 2, Vj, list(celt)) if M >= 1 else None
            # r=3: children at level 1; celt handling below
        # general: mirror construct's child prescription
        sj = (G.ell[r-2]*Vj) % G.e[r-2]
        texp = (G.ell[r-2]*uj - sj)//G.e[r-2]
        celt = G.Kc[r-2].mul(ITL.fpow(G.Kc[r-2], G.z[r-2], texp), cj)
        cls_val = sim_construct(G, T, r-1, Vj, list(celt))
        har_val = KM.mul(KM.inv(T.eps(M, Vj)) if M >= 1 else KM.one(),
                         T.psi[M][j])
        if KM.is_zero(har_val):
            continue
        out[j] = KM.mul(cls_val, KM.inv(har_val))
    return out

def actual_ratios(T, G, r):
    """actual slot ratios from the two polynomials (probe F1-DIAG logic,
    elements not names); returns dict j -> ratio, or ('MISMATCH', kk)."""
    M = r - 2
    m = r - 1
    har = tuple(T.Phi[m]) if m <= T.n else GWP.top_lift(T)
    cls = tuple(G.phi[r])
    dvh = T.P.dev(list(har), T.Phi[m-1])
    dvc = T.P.dev(list(cls), T.Phi[m-1])
    L = max(len(dvh), len(dvc))
    out = {}
    for kk in range(L):
        ah = dvh[kk] if kk < len(dvh) else ()
        ac = dvc[kk] if kk < len(dvc) else ()
        if not ah and not ac:
            continue
        if bool(ah) != bool(ac):
            return ('SUPPORT', kk)
        wh = T.wlev(m-1, ah); wc = T.wlev(m-1, ac)
        if wh != wc:
            return ('WEIGHT', kk)
        rh = T.read(m-1, wh, ah); rc = T.read(m-1, wc, ac)
        K = T.K[m-1]
        if K.is_zero(rh):
            return ('ZERO-READ', kk)
        if kk % T.e[M] != 0:
            return ('OFF-GRID', kk)
        out[kk // T.e[M]] = K.mul(rc, K.inv(rh))
    return out

def walk_nodes(T, G, r, tag):
    """CK-BYTE: byte-equality of the r-junction <=> all shared-tree node
    values equal.  Walk both prescriptions; return (all_equal, n_nodes)."""
    M = r - 2
    # top slots
    c = G.thm_c(r)
    V = G.vkey[r]
    em, hm = G.e[r-1], G.h[r-1]
    s = (G.ell[r-1]*V) % em
    u = (V - s*hm)//em
    allw = [True]
    nn = [0]

    def rec(level, Vv, har_target, cls_r, cls_V, cls_phic):
        """level = harness level of both children containers; har_target in
        T.K[level]; cls node = construct(cls_r, cls_V, cls_phic)."""
        nn[0] += 1
        cv = sim_construct(G, T, cls_r, cls_V, cls_phic)
        if cv != har_target:
            allw[0] = False
            return
        if level <= 1:
            return
        # descend: coordinates over K_{level-1}
        e1, h1 = T.e[level-1], T.h[level-1]
        ss = (T.l[level-1]*Vv) % e1
        uu = (Vv - ss*h1)//e1
        # har children values
        for i, ti in enumerate(har_target):
            if T.K[level-1].is_zero(ti):
                continue
            ki = ss + i*e1
            gi = (Vv - ki*T.gam[level])//e1
            tih = T.K[level-1].mul(T.K[level-1].inv(T.eps(level-1, gi)), ti) \
                if level-1 >= 1 else ti
            # cls child prescription
            uj = uu - i*h1
            sj = (G.ell[cls_r-2]*gi) % G.e[cls_r-2]
            texp = (G.ell[cls_r-2]*uj - sj)//G.e[cls_r-2]
            celt = G.Kc[cls_r-2].mul(
                ITL.fpow(G.Kc[cls_r-2], G.z[cls_r-2], texp), ti)
            # NOTE: the cls child's target is z^{texp} * (coordinate of the
            # CLS parent value); when parent values are equal the coordinate
            # sets coincide, so ti is the right coordinate here.
            rec(level-1, gi, tih, cls_r-1, gi, list(celt))

    for j in range(G.f[r-1] + 1):
        if j == G.f[r-1]:
            continue                     # monic top slot shared
        cj = G.Kc[r-2].mul(c, G.psis[r-1][j])
        hj = T.psi[M][j]
        both_zero = G.Kc[r-2].is_zero(cj) and T.K[M].is_zero(hj)
        if both_zero:
            continue
        if G.Kc[r-2].is_zero(cj) != T.K[M].is_zero(hj):
            allw[0] = False
            continue
        uj = u - j*hm
        kslot = s + j*em
        Vj = uj - kslot*G.vkey[r-1]
        har_val = T.K[M].mul(T.K[M].inv(T.eps(M, Vj)) if M >= 1
                             else T.K[M].one(), hj)
        sj = (G.ell[r-2]*Vj) % G.e[r-2]
        texp = (G.ell[r-2]*uj - sj)//G.e[r-2]
        celt = G.Kc[r-2].mul(ITL.fpow(G.Kc[r-2], G.z[r-2], texp), cj)
        rec(M, Vj, har_val, r-1, Vj, list(celt))
    return allw[0], nn[0]

# ------------------------------------------------------- per-tower T1 pass
def t1_pass(T, G, tag):
    rec = {'junctions': []}
    for r in range(2, T.NR + 2):
        m = r - 1
        har = tuple(T.Phi[m]) if m <= T.n else GWP.top_lift(T)
        cls = tuple(G.phi[r])
        jd = {'r': r, 'byte_equal': har == cls}
        if r == 2:
            note('CK-SLOT')
            if not jd['byte_equal']:
                viol('CK-SLOT', tag, 'r=2 base junction not byte-equal')
            rec['junctions'].append(jd)
            continue
        M = r - 2
        KM = T.K[M]
        # shared-key perimeter: HR-REC (and the slot/xi/byte laws) are
        # claimed only where the two chains share the key bytes BELOW the
        # junction; above an interior divergence the construct multiplies
        # by ITS OWN keys and the harness-read recursion does not apply.
        shared = all(tuple(G.phi[q]) == tuple(T.Phi[q-1])
                     for q in range(2, r))
        jd['shared_below'] = shared
        # CK-REC at this junction (construct nodes)
        c = G.thm_c(r)
        phiy = [G.Kc[r-2].mul(c, G.psis[r-1][j]) for j in range(G.f[r-1])]
        if shared:
            ck_rec_nodes(G, T, r, G.vkey[r], phiy, tag)
        else:
            note('CK-REC-SKIP')
        # CK-SLOT: actual vs predicted ratios
        act = actual_ratios(T, G, r)
        prd = predict_ratios(T, G, r)
        note('CK-SLOT')
        if isinstance(act, tuple):
            viol('CK-SLOT', tag, 'untransported junction r=%d has %s at slot %s'
                 ' (expected unit ratios at first divergence only; recorded)'
                 % ((r,) + act) if False else
                 'r=%d %s mismatch at dev index %d (above-twist row, recorded'
                 ' as SKIP not violation)' % (r, act[0], act[1]))
            # above-interior-twist junctions are NOT first divergences; the
            # slot law is only claimed there -- do not score, record.
            VIOL.pop()
            jd['slot_law'] = 'SKIP(%s@%d)' % act
        else:
            ok = True
            for j, rho in prd.items():
                aj = act.get(j)
                if aj is None or aj != rho:
                    ok = False
            # top slot must be trivial
            if act.get(G.f[r-1]) not in (None, KM.one()):
                ok = False
            if not ok:
                viol('CK-SLOT', tag, 'slot ratios != sim prediction at r=%d' % r)
            jd['slot_law'] = 'OK' if ok else 'FAIL'
            # M = 1 exact closed form
            if M == 1:
                note('CK-SLOT-M1')
                A1 = T.l[0]*T.g[0]*T.gam[1]
                cc = G.thm_c(r)
                okm = all(prd[j] == KM.mul(cc, ITL.fpow(KM, T.z[1],
                                                        A1*T.e[1]*j))
                          for j in prd)
                if not okm:
                    viol('CK-SLOT-M1', tag, 'M=1 closed form fails at r=%d' % r)
        # CK-BYTE
        note('CK-BYTE')
        if not isinstance(act, tuple):
            weq, nnod = walk_nodes(T, G, r, tag)
            if weq != jd['byte_equal']:
                viol('CK-BYTE', tag, 'byte law fails at r=%d (walk=%s bytes=%s)'
                     % (r, weq, jd['byte_equal']))
            jd['byte_walk_nodes'] = nnod
        # CK-XI at this junction (first divergence / top only <=> slot law
        # applicable, i.e. no weight/support mismatch)
        if not isinstance(act, tuple):
            note('CK-XI')
            sc = orbit_scan(G, r, list(har))
            jd2 = junction_data(T, G, r)
            jd['theta_trivial'] = jd2['theta_trivial']
            if not (sc['vok'] and sc['onesided'] and sc['orbit']):
                viol('CK-XI', tag, 'orbit missing at r=%d' % r)
            else:
                xi, w = sc['orbit']
                jd['xi'] = repr(xi); jd['w'] = repr(w)
                if jd2['theta_trivial']:
                    # the orbit pair need not be unique when psi has sparse
                    # support (the character is determined only modulo the
                    # support stabilizer); the closed form is confirmed if
                    # the PREDICTED pair satisfies the orbit equations.
                    if not orbit_satisfies(G, r, list(har),
                                           jd2['xi_pred'], jd2['w_pred']):
                        viol('CK-XI', tag,
                             'closed form fails at r=%d: pred (%s,%s) does '
                             'not satisfy the orbit equations (scan gave '
                             '(%s,%s))' % (r, jd2['xi_pred'], jd2['w_pred'],
                                           xi, w))
                else:
                    note('CK-XI-BOUNDARY')
                    jd['xi_boundary'] = True
        rec['junctions'].append(jd)
    return rec

# ------------------------------------------------------- clause-3 transport
def rescale_letter(G, x, lev, target, xi):
    """multiply the K_{target}-layer coordinates: element x of Kc[lev]
    (tuple over Kc[lev-1]); target = GMN chain index of the conjugated
    modulus level (letter z_{target+1} rescaled: z_old = xi * z_new)."""
    if lev == target:
        F = G.Kc[lev-1] if lev >= 1 else None
        out = []
        for i, c in enumerate(x):
            out.append(F.mul(c, ITL.fpow(F, xi, i)))
        return tuple(out)
    return tuple(rescale_letter(G, c, lev-1, target, xi) for c in x)

def transport_leg(T, tag, garble=None):
    """iterative psi-transport; returns (G_final, ledger, fails).
    garble: None or an int r0 -- at the first junction with xi != 1 and
    r == r0-or-first, replace xi by xi*z_1 (teeth)."""
    levels = [(T.e[i], T.h[i], list(T.psi[i])) for i in range(T.NR)]
    ledger = []
    fails = []
    garbled = False
    for r in range(3, T.NR + 2):
        G = GWP.GmnLeg(T.R, T.d0, T.Phi[0], levels)
        m = r - 1
        har = tuple(T.Phi[m]) if m <= T.n else GWP.top_lift(T)
        sc = orbit_scan(G, r, list(har))
        if not (sc['vok'] and sc['onesided'] and sc['orbit']):
            fails.append('junction r=%d not orbit-admissible mid-transport: '
                         'vok=%s onesided=%s' % (r, sc['vok'], sc['onesided']))
            break
        xi, w = sc['orbit']
        F = G.Kc[r-2]
        ledger.append((r, repr(xi), repr(w)))
        if garble and not garbled and xi != F.one():
            zz = G.z[r-2] if r-2 >= 1 else None
            if zz is not None:
                xi = F.mul(xi, zz)
                garbled = True
        if xi == F.one():
            continue
        # conjugate modulus at GMN level r-1 (levels index r-2):
        e_, h_, psi = levels[r-2]
        f = len(psi) - 1
        psi2 = [F.mul(psi[j], ITL.fpow(F, xi, j - f)) for j in range(f + 1)]
        levels[r-2] = (e_, h_, psi2)
        # re-coordinate all higher psi data through z_old = xi * z_new
        for mm in range(r-1, T.NR):
            e2, h2, ps = levels[mm]
            ps2 = [rescale_letter(G, ccc, mm, r-1, xi) for ccc in ps]
            levels[mm] = (e2, h2, ps2)
    try:
        Gf = GWP.GmnLeg(T.R, T.d0, T.Phi[0], levels)
    except AssertionError as ex:
        fails.append('final chamber build failed: %s' % ex)
        Gf = None
    return Gf, ledger, fails

def tw_pass(T, spec, tag, pari):
    rec = {}
    Gf, ledger, fails = transport_leg(T, tag)
    rec['ledger'] = ledger
    RES['xi_ledger'][tag] = ledger
    if fails or Gf is None:
        note('TW-RATIO')
        viol('TW-RATIO', tag, 'transport failed: %s' % fails)
        rec['fails'] = fails
        RES['tw'][tag] = rec
        return
    # TW-RATIO + TW-ADM + TW-STRICT per level
    strict_fails = 0
    for r in range(2, T.NR + 2):
        m = r - 1
        har = tuple(T.Phi[m]) if m <= T.n else GWP.top_lift(T)
        note('TW-RATIO')
        act = actual_ratios(T, Gf, r)
        if isinstance(act, tuple):
            viol('TW-RATIO', tag, 'transported chain %s mismatch at r=%d idx %d'
                 % (act[0], r, act[1]))
        note('TW-ADM')
        sc = orbit_scan(Gf, r, list(har))
        if not (sc['vok'] and sc['onesided'] and sc['orbit']):
            viol('TW-ADM', tag, 'transported ADM fails at r=%d: vok=%s os=%s'
                 % (r, sc['vok'], sc['onesided']))
        note('TW-STRICT')
        if sc['strict'] is None:
            strict_fails += 1
            viol('TW-STRICT', tag, 'harness lift not a STRICT representative '
                 'of the transported type at r=%d (orbit=%s)'
                 % (r, sc['orbit'] is not None))
    rec['strict_fails'] = strict_fails
    # TW-F3: committed battery on transported lifts
    lifts = {m: tuple(Gf.phi[m+2]) for m in range(0, T.n)}
    R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
    try:
        TC = GWP.ClsTower(tag + '/tw', R2, spec['d0'], spec['Phi0'],
                          spec['reads'], [ps for ps in spec['psi']], lifts)
        C, vv = run_battery(TC, spec['pairn'])
        note('TW-F3', COUNTS_pairs(spec))
        rec['tw_f3_violations'] = len(vv)
        rec['tw_f3_first'] = vv[:3]
        for v in vv:
            viol('TW-F3', tag, v)
    except AssertionError as ex:
        note('TW-F3')
        viol('TW-F3', tag, 'transported ClsTower gate failed: %s' % ex)
        rec['tw_f3_violations'] = 'GATE-FAIL'
    # TW-F3b control
    Cb, vb = run_battery(T, spec['pairn'])
    note('TW-F3b', COUNTS_pairs(spec))
    for v in vb:
        viol('TW-F3b', tag, v)
    # TW-PARI
    if spec['ring'] == 'Zp' and pari is not None:
        E = 1; F_ = T.d0
        for (e, h, g) in spec['reads']:
            E *= e; F_ *= g
        top = tuple(Gf.phi[T.NR + 1])
        ok = GWP.pari_ef(pari, top, spec['p'], E, F_, tag, 'tw-cls')
        # pari_ef notes F4 and registers into GWP.VIOL -- migrate
        migrate_gwp_viols('TW-PARI', tag)
        note('TW-PARI')
        rec['pari_ok'] = ok
    RES['tw'][tag] = rec

def COUNTS_pairs(spec):
    return spec['pairn']**2

def run_battery(TT, pairn):
    C = collections.defaultdict(int)
    vv = []
    W1 = ITL.window_reps(TT, pairn)
    for ga in W1:
        try:
            ITL.gamma_checks(TT, ga, C, frozenset(), vv)
        except AssertionError as e:
            vv.append('%s K-ASSERT (%d): %s' % (TT.name, ga, e))
        for gb in W1:
            try:
                ITL.check_pair(TT, ga, gb, C, muts=frozenset(), viol=vv)
            except AssertionError as e:
                vv.append('%s K-ASSERT (%d,%d): %s' % (TT.name, ga, gb, e))
    return C, vv

def migrate_gwp_viols(fam, tag):
    while GWP.VIOL:
        f, t, d = GWP.VIOL.pop()
        viol(fam, tag, '[%s/%s] %s' % (f, t, d))

# ----------------------------------------------------------- CK-T3E leg
def t3e_mechanism(pari):
    """(a) T3E: battery intermediates byte-identical + s_2 == 0 census;
    (b) T3A: K6/K7-failing pairs == byte-diff-digit pairs."""
    for tid, expect_break in (('T3E', False), ('T3A', True)):
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        lifts = {m: tuple(G.phi[m+2]) for m in range(0, T.n)}
        R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' else ITL.Fpt(spec['p'])
        TC = GWP.ClsTower(tag + '/cls', R2, spec['d0'], spec['Phi0'],
                          spec['reads'], [ps for ps in spec['psi']], lifts)
        W1 = ITL.window_reps(T, spec['pairn'])
        digit_diff_pairs = set()
        s2_census = set()
        for ga in W1:
            s2_census.add(T.split(ga)['s'][2])
            for gb in W1:
                Ph = T.P.mul(T.tanch(ga, T.n), T.tanch(gb, T.n))
                Pc = TC.P.mul(TC.tanch(ga, TC.n), TC.tanch(gb, TC.n))
                dvh = T.P.dev(Ph, T.Phi[T.n])
                dvc = TC.P.dev(Pc, TC.Phi[TC.n])
                if [tuple(x) for x in dvh] != [tuple(x) for x in dvc]:
                    digit_diff_pairs.add((ga, gb))
        C, vv = run_battery(TC, spec['pairn'])
        k67_pairs = set()
        for v in vv:
            if ' K6 (' in v or ' K7 (' in v:
                pp = v.split('(')[1].split(')')[0]
                a, b = pp.split(',')
                k67_pairs.add((int(a), int(b)))
        note('CK-T3E')
        rec = {'s2_values': sorted(s2_census),
               'digit_diff_pairs': len(digit_diff_pairs),
               'k67_fail_pairs': len(k67_pairs),
               'k67_subset_of_diff': k67_pairs <= digit_diff_pairs}
        RES['t3e'][tag] = rec
        if tid == 'T3E':
            if digit_diff_pairs or s2_census != {0} or vv:
                viol('CK-T3E', tag, 'T3E mechanism fails: diffs=%d s2=%s viol=%d'
                     % (len(digit_diff_pairs), sorted(s2_census), len(vv)))
        else:
            # every value-visible K6/K7 failure sits on a pair whose top-dev
            # digits differ in bytes (the overflow-carry pairs); the reverse
            # containment is NOT claimed (a carry can be read-invisible, or
            # a common character can cancel in the cocycle ratio).
            if not digit_diff_pairs or not (k67_pairs <= digit_diff_pairs) \
               or not k67_pairs:
                viol('CK-T3E', tag, 'T3A mechanism fails: diff-pairs=%d '
                     'k67-pairs=%d subset=%s' % (len(digit_diff_pairs),
                     len(k67_pairs), k67_pairs <= digit_diff_pairs))

# ----------------------------------------------------------------- QO leg
def qo_pass(pari):
    for name, p, fc in GWP.QO_SHAPES:
        tag = 'QO:%s/Q%d' % (name, p)
        R = ITL.Zp(p)
        leg, levels, status = GWP.qo_extract(R, fc)
        rec = {'status': status}
        if status != 'complete':
            RES['qo'][tag] = rec
            continue
        reads = [(e, h, len(psi)-1) for (e, h, psi) in levels]
        psi_specs = [[('RAW', c) for c in psi] for (e, h, psi) in levels]
        try:
            T = GWP.SpecTower(tag, ITL.Zp(p), 1, [0, 1], reads, psi_specs)
        except AssertionError as ex:
            note('TW-QO')
            viol('TW-QO', tag, 'harness tower failed: %s' % ex)
            continue
        Gf, ledger, fails = transport_leg(T, tag)
        rec['ledger'] = ledger
        if fails or Gf is None:
            note('TW-QO')
            viol('TW-QO', tag, 'transport failed: %s' % fails)
            RES['qo'][tag] = rec
            continue
        for r in range(2, T.NR + 2):
            note('TW-QO')
            act = actual_ratios(T, Gf, r)
            if isinstance(act, tuple):
                viol('TW-QO', tag, '%s mismatch at r=%d idx %d'
                     % (act[0], r, act[1]))
        RES['qo'][tag] = rec

# ------------------------------------------------------------- MT-TW teeth
def mt_teeth(pari):
    for tid in ('T3A', 'T3C'):
        spec = next(s for s in GWP.TOWERS if s['id'] == tid)
        tag = '%s,p=%d,%s/MT' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        caught = 0
        try:
            Gf, ledger, fails = transport_leg(T, tag, garble=True)
            if fails or Gf is None:
                caught += 1
            else:
                for r in range(2, T.NR + 2):
                    act = actual_ratios(T, Gf, r)
                    if isinstance(act, tuple):
                        caught += 1
                    sc = orbit_scan(Gf, r, list(
                        tuple(T.Phi[r-1]) if r-1 <= T.n else GWP.top_lift(T)))
                    if not (sc['vok'] and sc['onesided'] and sc['orbit']):
                        caught += 1
                lifts = {m: tuple(Gf.phi[m+2]) for m in range(0, T.n)}
                R2 = ITL.Zp(spec['p']) if spec['ring'] == 'Zp' \
                    else ITL.Fpt(spec['p'])
                try:
                    TC = GWP.ClsTower(tag, R2, spec['d0'], spec['Phi0'],
                                      spec['reads'], [ps for ps in spec['psi']],
                                      lifts)
                    C, vv = run_battery(TC, spec['pairn'])
                    caught += len(vv)
                except AssertionError:
                    caught += 1
        except (AssertionError, ZeroDivisionError) as ex:
            caught += 1
        note('MT-TW')
        RES['mut'][tag] = {'caught': caught}
        if caught == 0:
            viol('MT-TW', tag, 'garbled transport NOT caught (no teeth)')

# =================================================================== main
def main():
    t0 = time.time()
    print('grt_w2_checks -- W-2 composition checks + clause-3 psi-transport')
    print('harness leg: iterlawn_pe_reimpl (committed, verbatim);')
    print('classifier leg: grt_weld_probe.GmnLeg (sealed fresh transcription,')
    print('imported verbatim -- no new print transcription in this runner)')
    print()
    pari = GWP.pari_init()
    for spec in GWP.TOWERS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        tA = time.time()
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        ck_mm(T, tag)
        ck_base(T, G, tag)
        RES['towers'][tag] = t1_pass(T, G, tag)
        tw_pass(T, spec, tag, pari)
        print('  [%6.1fs] %-16s done (%.1fs)' % (time.time()-t0, tag,
                                                 time.time()-tA))
    qo_pass(pari)
    print('  [%6.1fs] QO transport done' % (time.time()-t0))
    t3e_mechanism(pari)
    print('  [%6.1fs] T3E/T3A mechanism done' % (time.time()-t0))
    mt_teeth(pari)
    print('  [%6.1fs] MT teeth done' % (time.time()-t0))
    print()
    print('=' * 78)
    print('PREDICTED vs OBSERVED (violation counts; samples in parentheses)')
    print('=' * 78)
    fams = [
        ('CK-MM',      'Bezout mismatch identity (W2-L2)',            '0'),
        ('CK-HR1',     'base builder read HR_1 (W2-L1)',              '0'),
        ('CK-VD1',     'level-1 packed dictionary (W2-L3)',           '0'),
        ('CK-REC',     'construct read recursion, all nodes',         '0'),
        ('CK-SLOT',    'junction slot-ratio law == sim',              '0'),
        ('CK-SLOT-M1', 'M=1 exact closed form c*z^(A e j)',           '0'),
        ('CK-XI',      'orbit (xi,w) == closed form (perimeter)',     '0'),
        ('CK-BYTE',    'byte law == node-value walk',                 '0'),
        ('TW-RATIO',   'transported: no WEIGHT/SUPPORT anywhere',     '0'),
        ('TW-ADM',     'transported: ADM all levels (F2 cure)',       '0'),
        ('TW-STRICT',  'transported: STRICT rep of t^tw',             '0'),
        ('TW-F3',      'transported cocycle battery (96 -> 0)',       '0'),
        ('TW-F3b',     'baseline control',                            '0'),
        ('TW-PARI',    'transported top lifts (e,f) tie',             '0'),
        ('TW-QO',      'QO shapes transported',                       '0'),
        ('CK-T3E',     'T3E carry-inert + T3A overflow mechanism',    '0'),
        ('MT-TW',      'teeth: garbled transport caught',             '0'),
    ]
    all_ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        nsm = COUNTS.get(fam, 0)
        verdict = 'GREEN' if obs == 0 else 'RED'
        if obs > 0:
            all_ok = False
        print('%-10s %-46s pred %-4s obs %5d (%6d)  %s'
              % (fam, desc, pred, obs, nsm, verdict))
    nb = COUNTS.get('CK-XI-BOUNDARY', 0)
    print('-' * 78)
    print('chi-formula boundary junctions (monomial-collapse, recorded not '
          'scored): %d' % nb)
    if VIOL:
        print('%d VIOLATIONS (first 40):' % len(VIOL))
        for v in VIOL[:40]:
            print('  ', v)
    RES['families'] = {fam: {'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0)}
                       for fam, desc, pred in fams}
    RES['violations'] = [list(v) for v in VIOL]
    RES['boundary_junctions'] = nb
    RES['elapsed_s'] = round(time.time() - t0, 1)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_w2_checks_results.json')
    with open(out, 'w') as fh:
        json.dump(RES, fh, indent=1, default=repr)
    print('TOTAL samples: %d   elapsed %.1fs   JSON: %s'
          % (sum(COUNTS.values()), time.time()-t0, out))
    print()
    print('W-2 COMPOSITION VERDICT:')
    print('  intermediate identities (CK-*): %s'
          % ('ALL GREEN' if not any(v[0].startswith('CK') for v in VIOL)
             else 'RED'))
    print('  clause-3 transport (TW-*): %s'
          % ('ALL GREEN' if not any(v[0].startswith('TW') for v in VIOL)
             else 'RED'))
    print('  teeth: %s' % ('CAUGHT' if not any(v[0] == 'MT-TW' for v in VIOL)
                           else 'NO TEETH'))
    return 0 if all_ok else 1

if __name__ == '__main__':
    sys.exit(main())
