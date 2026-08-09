"""HE7 ANNEX-PASS-2 fresh route (hostile verifier leg; disjoint from all
prior stack routes: F-1 leg 96 n=16 mixed-node members / R leg 79 n=16
level-3 members / pass-1 K3=F_p2 96 + 44,328 symbolic).

FOUR LEGS, decorrelating on FOUR new axes at once: new PRIME (p in
{3,11}; every stack leg ran p in {5,7}), new DEGREE (n = 24, mu3 = 3;
every stack leg ran n = 16), DUAL ORACLE (PARI factorpadic — ROUND4,
local — against the single shared pari_sigma16 = global factor +
nfinit p-maximal + idealprimedec that ALL THREE stack legs import; plus
a NON-PARI sympy exact-discriminant parity check), and depth (the first
i = 3 / level-4 symbolic coverage; pass-1's Q0 stopped at i = 2).

W0 (EXACT, no oracle): ANNEX-DEF HE7-2' / ANNEX-LEMMA R1-a at i = 3.
   Exponent-vector arithmetic over the letters (varpi, Phi', Psi, Psi2)
   for the 4-level tower (l1,u1) = (2,5), (l2,u2) = (2, u2),
   (l3,u3) = (2, u3): verify (a) the value identity of n4(k) at
   level-4 weights (8, 20, 2u2, u3); (b) the R1.1 cocycle recursion at
   i = 3 with carry c3 in {0,1}; (c) R1-b's theta_t telescoping
   theta_t = prod_j tau_3(m0-(j+1)u3, u3) and the (R1.2) monomial
   identity, both as exact vector identities; (d) theta_t's
   letter-monomial decomposition Lam2^e2 Lam1^e1 exists (R1-a(iii) at
   i = 3, the first two-letter WITHIN-CLASS unit coverage anywhere);
   (e) W0b: the paper-walk instance (l3 = 1 tower, u2 = 21, u3 = 43,
   m0 = 86): theta_1 == Lam2 * Lam1 exactly.

W1 (DUAL ORACLE on the committed annex-leg members): deterministically
   re-generate the ANNEX F-1 leg's 96 members (rng 20260809, the
   committed loop order) and the ANNEX R leg's 79 members (same), and
   score each by (o1) the shared pari_sigma16, (o2) factorpadic factor
   count + degree multiset + per-factor tame disc-parity (all e even
   and p odd here, so v_p(poldisc F) == f mod 2, index-independent),
   (o3) sympy EXACT poldisc parity of the full member (non-PARI):
   v_p(disc f) == sum_i f_i (e_i - 1) mod 2. Also recount the R leg's
   deep-letter counter with the tooth reader disabled (pass-1 M-1:
   expect 47 corrected-chain, 102 total shared).

W2 (n = 24, p in {3, 11}, mu3 = 3 — level 3 at a NEW degree, with the
   first machine contact of MIXED LEVEL-3 NODES, i.e. ANNEX-LEMMA
   HE7-13' COMPOSED WITH ANNEX-DEF HE7-2' one level up): members
   f = Psi2^3 + A2 Psi2^2 + A1 Psi2 + A0 at the (2,1,1) frame, ladder
   mu = 12 -> mu2 = 6 (residual (Z-s2)^3, jump l2*deg r2 = 2) ->
   mu3 = 3, read forward. Kinds: M2X forced (Z-c)^2(Z-d) (mixed
   level-3 node: refine c-class per its own thread, d-class decided at
   the CURRENT key = the R-a route one level up; parked side at the
   refined slope must persist with residual (Z-(d-c)) EXACTLY =
   HE7-13'(c) at level 3); M2C forced (Z-c)^3 (pure: the lam side must
   NOT survive the refine = HE7-13 as displayed at level 3); M2S random
   separable cubics; M1 l3 = 3 single side (p = 11 only; e = 24);
   M3 two sides (separable residuals). sigma scored by o1 AND o2 AND
   o3 member-by-member. TOOTH T-DEEP: the deep letter dropped
   (s2-multiplier only) must flip at least one sigma.

PREREGISTERED: W0 all identities exact, 0 violations; W1 279 checks...
   (96+79 members x 3 oracles) all agree, M-1 recount 47/102; W2 sigma
   == o1 == o2-consistent == o3-parity on every member, sum ef = 24,
   >= 1 mixed-node member with the parked side EXACT at every re-read,
   >= 1 pure member losing the lam side, T-DEEP >= 1 flip.
Scale-down rule: if PARI nfinit at deg 24 stalls, drop to factorpadic
   + parity only for the stalling cells and DISCLOSE the split.
Budget: smoke (2 members/leg) then full, detached, ~10 min cap.
"""
import sys
import os
import json
import time
import random
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from he7_pe3_probe12 import (Fr12, padd, pneg, pmul, pdivmod,
                             development, vp, gcdi, disc_nonzero, BIG)
import he7_pe3_probe12 as probe_mod
import he7annex_supp as annex_mod
import he7rannex_supp as rannex_mod
from he7annex_supp import (pari_sigma16, fp_monic, fp_factor_full,
                           build16, target_cres)
from he7rannex_supp import Fr3, build_member, read_level3

pari = probe_mod.pari

RES = {'checks': {}, 'viol': [], 'secs': 0, 'legs': {}}


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


# ===================================================================
# W0: exact exponent-vector arithmetic at i = 3 (level 4)
# letters order: (varpi, Phi', Psi, Psi2); tower (2,5),(2,u2),(l3,u3)
# ===================================================================

def V2(k):
    s = k % 2
    return ((k - 5 * s) // 2, s, 0, 0)


def V3(k, u2):
    s2 = k % 2
    m2 = (k - s2 * u2) // 2
    v = V2(m2)
    return (v[0], v[1], s2, 0)


def V4(k, u2, u3, l3):
    if l3 == 1:
        return V3(k, u2)
    s3 = k % 2
    m3 = (k - s3 * u3) // 2
    v = V3(m3, u2)
    return (v[0], v[1], v[2], s3)


def vadd(*vs):
    return tuple(sum(x) for x in zip(*vs))


def vscale(c, v):
    return tuple(c * x for x in v)


def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def w4val(v, u2, u3, l3):
    """value of the monomial at level-4 points, in w4 units."""
    wts = ((4, 10, u2, u3) if l3 == 1 else (8, 20, 2 * u2, u3))
    return sum(a * w for a, w in zip(v, wts))


def lam_vectors(u2, u3, l3):
    L1 = (-5, 2, 0, 0)
    L2 = vsub((0, 0, 2, 0), V2(u2))
    L3 = vsub((0, 0, 0, 2), V3(u3, u2)) if l3 == 2 else None
    return L1, L2, L3


def letter_decompose(v, u2, u3, l3):
    """write v as Lam3^e3 Lam2^e2 Lam1^e1 (integer exponents) or None;
    the R1-a(iii) claim: cocycle values ARE letter monomials."""
    L1, L2, L3 = lam_vectors(u2, u3, l3)
    e3 = 0
    if l3 == 2:
        if v[3] % 2:
            return None
        e3 = v[3] // 2
        v = vsub(v, vscale(e3, L3))
    elif v[3] != 0:
        return None
    if v[2] % 2:
        return None
    e2 = v[2] // 2
    v = vsub(v, vscale(e2, L2))
    if v[1] % 2:
        return None
    e1 = v[1] // 2
    v = vsub(v, vscale(e1, L1))
    if any(v):
        return None
    return e3, e2, e1


def tau3(a, b, u2):
    return vsub(vadd(V3(a, u2), V3(b, u2)), V3(a + b, u2))


def tau4(a, b, u2, u3, l3):
    return vsub(vadd(V4(a, u2, u3, l3), V4(b, u2, u3, l3)),
                V4(a + b, u2, u3, l3))


def leg_W0():
    n = 0
    for u2 in (21, 23):
        T3 = 2 * u2
        for u3 in (4 * u2 + 1, 4 * u2 + 3, 4 * u2 + 9):
            l3 = 2      # node condition u3/2 > T3 <=> u3 > 4u2  OK
            L1, L2, L3 = lam_vectors(u2, u3, l3)
            # letters have w4-value 0
            for L in (L1, L2, L3):
                if w4val(L, u2, u3, l3) != 0:
                    viol('W0 letter value != 0', {'u2': u2, 'u3': u3})
            # (a) value identity + (b) R1.1 at i = 3
            for a in range(-60, 61):
                va = V4(a, u2, u3, l3)
                if w4val(va, u2, u3, l3) != a:
                    viol('W0 value identity', {'k': a, 'u2': u2,
                                               'u3': u3})
                n += 1
                for b in range(-30, 31, 7):
                    s3a, s3b, s3ab = a % 2, b % 2, (a + b) % 2
                    c3 = (s3a + s3b - s3ab) // 2
                    if c3 not in (0, 1):
                        viol('W0 carry', {'a': a, 'b': b})
                    m3 = lambda k: (k - (k % 2) * u3) // 2
                    rhs = vadd(vscale(c3, L3),
                               tau3(m3(a), m3(b), u2),
                               tau3(m3(a) + m3(b), c3 * u3, u2))
                    if tau4(a, b, u2, u3, l3) != rhs:
                        viol('W0 R1.1 i=3', {'a': a, 'b': b, 'u2': u2,
                                             'u3': u3})
                    n += 1
            # (c)+(d): theta_t telescoping + (R1.2) + letter monomial,
            # at the level-4 read: n_i = n3, u_i = u3, m0 = m3(k)
            for k in range(8 * u2, 8 * u2 + 40):
                s0 = k % 2
                m0 = (k - s0 * u3) // 2
                for t in range(0, 4):
                    th = vsub(vadd(V3(m0 - t * u3, u2),
                                   vscale(t, V3(u3, u2))),
                              V3(m0, u2))
                    tel = (0, 0, 0, 0)
                    for j in range(t):
                        tel = vadd(tel, tau3(m0 - (j + 1) * u3, u3, u2))
                    if th != tel:
                        viol('W0 telescoping', {'k': k, 't': t})
                    if w4val(th, u2, u3, l3) != 0:
                        viol('W0 theta value != 0', {'k': k, 't': t})
                    dec = letter_decompose(th, u2, u3, l3)
                    if dec is None:
                        viol('W0 theta not letter monomial',
                             {'k': k, 't': t})
                    elif dec[1] or dec[0]:
                        note('W0-theta-multiletter')
                    # (R1.2): Phi3^{s0+2t}/n4(k) ==
                    #   (-V3(m0-t u3)) + t*Lam3 + theta_t
                    lhs = vsub((0, 0, 0, s0 + 2 * t),
                               V4(k, u2, u3, l3))
                    rhs = vadd(vscale(-1, V3(m0 - t * u3, u2)),
                               vscale(t, L3), th)
                    if lhs != rhs:
                        viol('W0 R1.2', {'k': k, 't': t})
                    n += 3
    # W0b: the paper walk (l3 = 1 tower): theta_1 at m0=86, u3=43,
    # u2=21 equals Lam2 * Lam1 exactly
    u2, u3, l3 = 21, 43, 1
    L1, L2, _ = lam_vectors(u2, u3, l3)
    th1 = vsub(vadd(V3(86 - 43, u2), V3(43, u2)), V3(86, u2))
    if th1 != vadd(L1, L2):
        viol('W0b paper walk theta_1 != Lam2*Lam1', {'got': th1})
    else:
        note('W0b-paperwalk-exact')
    n += 1
    RES['legs']['W0'] = {'exact_checks': n}
    print('W0: %d exact checks, multiletter thetas %d'
          % (n, RES['checks'].get('W0-theta-multiletter', 0)))


# ===================================================================
# The three oracles
# ===================================================================

def pari_fx(f):
    return pari('+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f)
                         if c))


def sigma_factorpadic(f, p, prec=400):
    """oracle-2: PARI factorpadic (ROUND4, local — decorrelated from
    the shared global-factor + idealprimedec route). Returns sorted
    list of (deg, v_p(poldisc factor))."""
    fac = pari.factorpadic(pari_fx(f), p, prec)
    out = []
    for i in range(int(pari.matsize(fac)[0])):
        F, mult = fac[i, 0], int(fac[i, 1])
        if mult != 1:
            viol('o2 repeated local factor', {'p': p})
        d = int(pari.poldegree(F))
        dsc = pari.poldisc(F)
        vd = int(pari.valuation(dsc, p)) if dsc != 0 else BIG
        out.append((d, vd))
    return sorted(out)


def o2_consistent(sig, o2, p):
    """degree multiset + tame disc-parity vs the predicted sigma.
    Valid here: p odd, every predicted e even (=> v_p(poldisc F) ==
    f mod 2, index-independent), p never divides e (tame)."""
    degs_pred = sorted(e * ff for e, ff in sig)
    degs_meas = sorted(d for d, _ in o2)
    if degs_pred != degs_meas:
        return 'degrees'
    for e, ff in sig:
        if e % 2 or e % p == 0:
            # wild (p | e) or odd-e factor: the tame disc-parity leg
            # is invalid; degree-multiset check above still binds.
            note('o2-wild-degreeonly')
            return 'ok-degrees-only'
    from collections import defaultdict
    par_pred = defaultdict(list)
    for e, ff in sig:
        par_pred[e * ff].append(ff % 2)
    par_meas = defaultdict(list)
    lbound = defaultdict(list)
    for d, vd in o2:
        par_meas[d].append(vd % 2)
        lbound[d].append(vd)
    for d in par_pred:
        if sorted(par_pred[d]) != sorted(par_meas[d]):
            return 'parity'
        fe = min(ff * (e - 1) for e, ff in sig if e * ff == d)
        if any(v < fe for v in lbound[d]):
            return 'lowerbound'
    return 'ok'


_SYMPY = None


def o3_disc_parity(f, p, sig):
    """oracle-3 (NON-PARI): sympy exact discriminant of the member;
    tame => v_p(disc f) == sum f_i (e_i - 1) mod 2."""
    global _SYMPY
    if _SYMPY is None:
        import sympy
        _SYMPY = sympy
    if any(e % p == 0 for e, ff in sig):
        note('o3-wild-skip')
        return 'ok-wild-skipped'
    x = _SYMPY.symbols('x')
    poly = _SYMPY.Poly(list(reversed(f)), x, domain='ZZ')
    dsc = int(poly.discriminant())
    if dsc == 0:
        return 'disc0'
    want = sum(ff * (e - 1) for e, ff in sig) % 2
    return 'ok' if vp(dsc, p) % 2 == want else 'parity'


# ===================================================================
# W1: dual+triple oracle on the two committed annex legs' members
# (deterministic re-generation, committed loop order, rng 20260809)
# ===================================================================

def leg_W1():
    t0 = time.time()
    # --- ANNEX F-1 leg: 96 members -------------------------------
    rng = random.Random(20260809)
    n = agree = 0
    cellrows = []
    for p in (5, 7):
        for s in (1, 2):
            for lam2 in (11, 12):
                fr = Fr12(p, 5, s)
                jobs = []
                for a0, b0 in ((1, 2), (1, 3), (2, 3)):
                    for _ in range(2):
                        jobs.append(('A', a0, b0))
                for a0, b0 in ((1, 3), (2, 1)):
                    for _ in range(2):
                        jobs.append(('B', a0, b0))
                for a0 in (1, 2):
                    jobs.append(('C', a0, 0))
                hist = {}
                for kind, a0, b0 in jobs:
                    f = build16(fr, lam2, target_cres(kind, a0, b0, p),
                                rng)
                    if not disc_nonzero(f):
                        continue
                    sig = pari_sigma16(f, p)
                    o2 = sigma_factorpadic(f, p)
                    st2 = o2_consistent(sig, o2, p)
                    st3 = o3_disc_parity(f, p, sig)
                    n += 1
                    if st2.startswith('ok') and st3.startswith('ok'):
                        agree += 1
                        note('W1-F1-triple-agree')
                    else:
                        viol('W1 F-1 oracle disagreement',
                             {'p': p, 's': s, 'lam2': lam2,
                              'kind': kind, 'o2': st2, 'o3': st3,
                              'sig': sig})
                    hist[str(sig)] = hist.get(str(sig), 0) + 1
                cellrows.append({'p': p, 's': s, 'lam2': lam2,
                                 'sig': hist})
    # committed aggregate comparison
    com = json.load(open(os.path.join(HERE,
                                      'he7annex_supp_results.json')))
    okrows = 0
    for mine, theirs in zip(cellrows, com['rows']):
        if mine['sig'] == theirs['sig'] and \
                sum(mine['sig'].values()) == theirs['members']:
            okrows += 1
        else:
            viol('W1 F-1 committed-row mismatch',
                 {'mine': mine, 'theirs': {'sig': theirs['sig']}})
    print('W1 F-1: %d members, triple-oracle agree %d, committed rows '
          'matched %d/8' % (n, agree, okrows))
    RES['legs']['W1_F1'] = {'members': n, 'agree': agree,
                            'rows_matched': okrows}
    # --- ANNEX R leg: 79 members + the M-1 recount ----------------
    rng = random.Random(20260809)
    rows_com = json.load(open(os.path.join(
        HERE, 'he7rannex_supp_results.json')))['rows']
    rannex_mod.RES['checks'] = {}
    rannex_mod.RES['viol'] = []
    n = agree = sigok = 0
    fs = []
    for p in (5, 7):
        for s in (2, 3):
            for u2 in (21, 23):
                for s2 in (1, 2):
                    fr = Fr12(p, 5, s)
                    f3 = Fr3(fr, u2, s2)
                    for kind in ['K1', 'K2', 'K2', 'K2R', 'K3']:
                        f, A0, A1 = build_member(f3, kind, rng)
                        if len(f) != 17 or not disc_nonzero(f):
                            note('W1-R-discard')
                            continue
                        fs.append((f3, f, p, kind))
    # corrected-chain-only reads first: the M-1 recount
    for f3, f, p, kind in fs:
        out = read_level3(f3, f)
        if isinstance(out, str):
            viol('W1 R corrected read failed', {'kind': kind})
            continue
        sig = tuple(sorted(out[0]))
        row = rows_com[n]
        if list(map(list, sig)) == row['sigma'] and row['p'] == p \
                and row['kind'] == kind:
            sigok += 1
        else:
            viol('W1 R committed-row mismatch',
                 {'i': n, 'mine': sig, 'theirs': row['sigma']})
        o1 = pari_sigma16(f, p)
        o2 = sigma_factorpadic(f, p)
        st2 = o2_consistent(sig, o2, p)
        st3 = o3_disc_parity(f, p, sig)
        n += 1
        if o1 == sig and st2.startswith('ok') and \
                st3.startswith('ok'):
            agree += 1
            note('W1-R-triple-agree')
        else:
            viol('W1 R oracle disagreement',
                 {'i': n, 'kind': kind, 'o1': o1, 'o2': st2,
                  'o3': st3, 'sig': sig})
    deep_corr = rannex_mod.RES['checks'].get('deep-letter-fired', 0)
    ref_corr = rannex_mod.RES['checks'].get('refine3', 0)
    # now the tooth reader re-reads (the shared-counter half)
    for f3, f, p, kind in fs:
        read_level3(f3, f, naive_twist=True)
    deep_tot = rannex_mod.RES['checks'].get('deep-letter-fired', 0)
    print('W1 R: %d members, committed sigma matched %d, triple-oracle '
          'agree %d; M-1 recount: corrected %d + tooth %d = total %d '
          '(committed record said 102); corrected refines %d'
          % (n, sigok, agree, deep_corr, deep_tot - deep_corr,
               deep_tot, ref_corr))
    RES['legs']['W1_R'] = {
        'members': n, 'sig_matched': sigok, 'agree': agree,
        'deep_corrected': deep_corr, 'deep_total': deep_tot,
        'refines_corrected': ref_corr}
    if deep_corr == 102:
        viol('M-1 refuted: corrected chain alone fires 102', {})
    print('W1 secs %.1f' % (time.time() - t0))


# ===================================================================
# W2: n = 24, mu3 = 3, p in {3, 11} — mixed LEVEL-3 nodes
# (ANNEX-LEMMA HE7-13' composed with ANNEX-DEF HE7-2', one level up)
# ===================================================================

BIN6 = [1, 6, 15, 20, 15, 6, 1]


def read1_24(fr, f):
    p = fr.p
    A = development(f, fr.Phi, 13)
    ys = [fr.dv1(a) if a else BIG for a in A[:12]] + [0]
    pins = [(j, ys[j]) for j in range(13) if ys[j] < BIG]
    h = rannex_mod.hull_of(pins)
    if len(h) != 2 or h[0] != (0, 30) or h[1] != (12, 0):
        return False
    csr = []
    for t in range(7):
        y = 30 - 5 * t
        csr.append(fr.res1(A[2 * t], y) if ys[2 * t] == y else 0)
    want = fp_monic([BIN6[t] * pow((-fr.s) % p, 6 - t, p) % p
                     for t in range(7)], p)
    return fp_monic(csr, p) == want


def read2_24(fr, f, u2, s2):
    p = fr.p
    A = development(f, fr.Psi0, 7)
    ys = [fr.dv2(a) if a else BIG for a in A[:6]] + [0]
    if ys[0] >= BIG:
        return 'peel'
    pins = [(j, ys[j]) for j in range(7) if ys[j] < BIG]
    h = rannex_mod.hull_of(pins)
    if len(h) != 2 or h[0] != (0, 3 * u2) or h[1] != (6, 0):
        return 'shape'
    csr = []
    for t in range(4):
        j, y = 2 * t, (3 - t) * u2
        raw = fr.res2(A[j], y) if (j < 6 and ys[j] == y) else \
            (1 if j == 6 else 0)
        dl = (y % 2) + t * (u2 % 2) - ((3 * u2) % 2)
        if dl % 2:
            return 'parity'
        csr.append((raw * pow(fr.s, (dl // 2) % (p - 1), p)) % p)
    want = fp_monic([pow((-s2) % p, 3, p), (3 * s2 * s2) % p,
                     (-3 * s2) % p, 1], p)
    return 'ok' if fp_monic(csr, p) == want else 'res'


def inv_twist_raws(f3, lam, target, nslots):
    """inverse-twist the target residual (R1-c's mechanism, one level
    up at mu3 = nslots): raw_t so the twisted monic read == target."""
    p = f3.p
    tws = []
    for t in range(nslots + 1):
        tw = f3.twist3(nslots * lam - t * lam, t, lam, nslots * lam)
        if tw is None:
            return None
        tws.append(tw[0])
    inv = lambda x: pow(x, p - 2, p)
    return [(target[t] % p) * tws[nslots] % p * inv(tws[t]) % p
            for t in range(nslots)]


def build24(f3, target, lam, rng):
    """f = Psi2^3 + sum A_t Psi2^t, single side slope lam (l3 = 1),
    twisted monic residual == target (monic cubic, low-first len 4)."""
    key = f3.key0
    raws = inv_twist_raws(f3, lam, target, 3)
    if raws is None:
        return None
    As = [f3.lift3((3 - t) * lam, raws[t]) if raws[t] else []
          for t in range(3)]
    for _ in range(2):
        gg = rng.randrange(f3.p)
        if gg and As[0]:
            As[0] = padd(As[0], f3.lift3(f3.dv3(As[0]) + 1 +
                                         rng.randrange(3), gg))
    k2 = pmul(key, key)
    f = padd(pmul(k2, key), pmul(As[2], k2))
    f = padd(f, pmul(As[1], key))
    return padd(f, As[0])


def build24_M1(f3, c, u3, rng):
    """single side l3 = 3 (slope u3/3), residual (Z - c): e = 24."""
    p = f3.p
    tw0 = f3.twist3(u3, 0, u3, u3)
    tw1 = f3.twist3(0, 1, u3, u3)
    if tw0 is None or tw1 is None:
        return None
    raw0 = ((-c) % p) * tw1[0] % p * pow(tw0[0], p - 2, p) % p
    A0 = f3.lift3(u3, raw0)
    key = f3.key0
    return padd(pmul(pmul(key, key), key), A0)


def build24_M3(f3, rng):
    """two sides: length 1 at lam_a, length 2 at lam_b (separable)."""
    p = f3.p
    lb = 2 * f3.u2 + rng.choice([2, 4])
    la = lb + 1 + rng.randrange(3)
    A1 = f3.lift3(2 * lb, rng.randrange(1, p))
    A0 = f3.lift3(la + 2 * lb, rng.randrange(1, p))
    key = f3.key0
    return padd(padd(pmul(pmul(key, key), key), pmul(A1, key)), A0)


def read3_24(f3, f, naive=False, cap=12):
    """level-3 read at mu3 = 3 with the per-class parked discipline of
    ANNEX-LEMMA HE7-13' (transferred per S6(iii)/R1.2): simple factors
    decided at the CURRENT key; repeated linear class refined; at every
    re-read, sides at slope <= floor must be EXACTLY the parked
    companions (clause (c)); pure refines must leave NO side at the
    refined slope (LEMMA HE7-13 as displayed, level 3)."""
    p = f3.p
    key = list(f3.key0)
    g = list(f)
    letters = []
    parked = {}
    floor = None                     # (num, den) of last refined slope
    nref = 0
    while True:
        st, sides = rannex_mod.sides3(f3, g, key)
        if st == 'peel':
            q, r = pdivmod(g, key)
            if r:
                return 'peelfail'
            letters.append((8, 1))
            g = q
            if len(g) == 1:
                return (letters, nref)
            continue
        if st != 'ok':
            return st
        refine = None
        for S in sides:
            sl = (S['u3'], S['l3'])
            below = floor is not None and \
                S['u3'] * floor[1] <= floor[0] * S['l3']
            if below:
                if naive:
                    continue
                want = parked.get(sl)
                if want is None or S['L'] != want[0] or \
                        S['cs'] != want[1]:
                    viol('W2 parked side mismatch',
                         {'slope': sl, 'L': S['L'],
                          'cs': S['cs'], 'want': want})
                    return 'parkfail'
                note('W2-parked-persist')
                continue
            col = S['cs_naive'] if naive else S['cs']
            fac = fp_factor_full(list(col), p)
            for poly, m in sorted(fac.items()):
                d = len(poly) - 1
                if m == 1:
                    letters.append((8 * S['l3'], d))
                elif d == 1 and S['l3'] == 1:
                    if refine is not None:
                        return 'tworefines'
                    comps = [(q2, m2) for q2, m2 in sorted(fac.items())
                             if q2 != poly]
                    refine = (S['u3'], (-poly[0]) % p, m, comps)
                else:
                    viol('W2 unexpected level-4 node', {'m': m, 'd': d})
                    return 'L4'
        if refine is None:
            return (letters, nref)
        nref += 1
        if nref > cap:
            return 'refcap'
        lam, root, mult, comps = refine
        if not naive:
            if comps:
                if len(comps) != 1 or comps[0][1] != 1 or \
                        len(comps[0][0]) != 2:
                    viol('W2 unexpected companion shape',
                         {'comps': comps})
                    return 'compfail'
                d0 = (-comps[0][0][0]) % p
                tr = (d0 - root) % p
                if tr == 0:
                    return 'transzero'
                parked[(lam, 1)] = (1, ((-tr) % p, 1))
                note('W2-mixed-parked')
            else:
                note('W2-pure-refine')   # lam side must NOT reappear
        w = f3.lift3(lam, root)
        if f3.dv3(w) != lam or f3.res3(w, lam) != root:
            return 'lift3contract'
        key = padd(key, pneg(w))
        floor = (lam, 1)


def process24(fr, f3, kind, rng, oracle1=True):
    p = f3.p
    if kind == 'M2X':
        cs2 = [(1, 2), (2, 1)] if p == 3 else \
            [(c, d) for c in range(1, p) for d in range(1, p) if c != d]
        c, d = rng.choice(cs2)
        t = [(-c) % p, 1]
        tgt = pmul(pmul(t, t), [(-d) % p, 1])
        f = build24(f3, [x % p for x in tgt], 2 * f3.u2 +
                    rng.choice([2, 4]), rng)
    elif kind == 'M2C':
        c = rng.randrange(1, p)
        t = [(-c) % p, 1]
        tgt = pmul(pmul(t, t), t)
        f = build24(f3, [x % p for x in tgt], 2 * f3.u2 +
                    rng.choice([2, 4]), rng)
    elif kind == 'M2S':
        tgt = [rng.randrange(1, p), rng.randrange(p), rng.randrange(p),
               1]
        f = build24(f3, tgt, 2 * f3.u2 + rng.choice([2, 4]), rng)
    elif kind == 'M1':
        u3 = 6 * f3.u2 + rng.choice([1, 5])
        while u3 % 3 == 0:
            u3 += 2
        f = build24_M1(f3, rng.randrange(1, p), u3, rng)
    else:
        f = build24_M3(f3, rng)
    if f is None or len(f) != 25:
        viol('W2 build failed', {'kind': kind})
        return None
    if not disc_nonzero(f):
        note('W2-disc0-discard')
        return None
    if not read1_24(fr, f):
        viol('W2 level-1 node', {'kind': kind})
        return None
    st2 = read2_24(fr, f, f3.u2, f3.s2)
    if st2 != 'ok':
        viol('W2 level-2 node ' + st2, {'kind': kind})
        return None
    note('W2-ladder')
    out = read3_24(f3, f)
    if isinstance(out, str):
        viol('W2 level-3 read ' + out, {'kind': kind})
        return None
    letters, nref = out
    sig = tuple(sorted(letters))
    if sum(e * ff for e, ff in sig) != 24:
        viol('W2 sum ef != 24', {'sig': sig, 'kind': kind})
        return None
    rec = {'kind': kind, 'p': p, 's': fr.s, 'u2': f3.u2, 's2': f3.s2,
           'sigma': list(sig), 'nref': nref}
    t0 = time.time()
    if oracle1:
        o1 = pari_sigma16(f, p)
        rec['o1_ok'] = (o1 == sig)
        if o1 != sig:
            viol('W2 o1 sigma mismatch', {'read': sig, 'pari': o1,
                                          'kind': kind})
        else:
            note('W2-o1-agree')
    o2 = sigma_factorpadic(f, p)
    st = o2_consistent(sig, o2, p)
    rec['o2'] = st
    if not st.startswith('ok'):
        viol('W2 o2 inconsistent', {'st': st, 'o2': o2, 'sig': sig})
    else:
        note('W2-o2-agree')
    st3 = o3_disc_parity(f, p, sig)
    rec['o3'] = st3
    if not st3.startswith('ok'):
        viol('W2 o3 parity', {'st': st3, 'sig': sig})
    else:
        note('W2-o3-agree')
    rec['oracle_secs'] = round(time.time() - t0, 2)
    outn = read3_24(f3, f, naive=True)
    sign = tuple(sorted(outn[0])) if not isinstance(outn, str) \
        else ('ERR', outn)
    rec['naive_flip'] = (sign != sig)
    if rec['naive_flip']:
        note('W2-deep-flip')
    return rec


def leg_W2(smoke=False):
    t0 = time.time()
    rows = []
    grid = []
    for u2 in (21, 23):
        for s2 in (1, 2):
            grid.append((3, 2, u2, s2,
                         ['M2X', 'M2X', 'M2C', 'M2S', 'M2S', 'M3']))
    for s in (2, 7):
        for s2 in (1, 3):
            grid.append((11, s, 21, s2,
                         ['M2X', 'M2X', 'M2C', 'M2S', 'M3', 'M1']))
    rng = random.Random(20260809)
    for (p, s, u2, s2, kinds) in grid:
        fr = Fr12(p, 5, s)
        f3 = Fr3(fr, u2, s2)
        for kind in kinds:
            rec = process24(fr, f3, kind, rng)
            if rec is None:
                continue
            rows.append(rec)
            if smoke and len(rows) >= 4:
                break
        if smoke and len(rows) >= 4:
            break
    n = len(rows)
    from collections import Counter
    sigs = Counter(str(tuple(map(tuple, r['sigma']))) for r in rows)
    flips = sum(1 for r in rows if r['naive_flip'])
    print('W2: %d members, o1 %d, o2 %d, o3 %d, deep flips %d, '
          'mixed-parked %d, parked-persist %d, pure-refine %d, %.1f s'
          % (n, RES['checks'].get('W2-o1-agree', 0),
             RES['checks'].get('W2-o2-agree', 0),
             RES['checks'].get('W2-o3-agree', 0), flips,
             RES['checks'].get('W2-mixed-parked', 0),
             RES['checks'].get('W2-parked-persist', 0),
             RES['checks'].get('W2-pure-refine', 0),
             time.time() - t0))
    print('W2 sigma genres:', dict(sigs))
    RES['legs']['W2'] = {'members': n, 'flips': flips,
                         'sigmas': dict(sigs), 'rows': rows}


def main():
    smoke = '--smoke' in sys.argv
    t0 = time.time()
    leg_W0()
    if not smoke:
        leg_W1()
    leg_W2(smoke=smoke)
    RES['secs'] = round(time.time() - t0, 1)
    ok = (not RES['viol']
          and RES['checks'].get('W2-deep-flip', 0) >= 1
          and RES['checks'].get('W2-mixed-parked', 0) >= 1
          and RES['checks'].get('W2-pure-refine', 0) >= 1
          and RES['checks'].get('W0b-paperwalk-exact', 0) == 1)
    if not smoke:
        ok = ok and \
            RES['legs']['W1_F1']['agree'] == \
            RES['legs']['W1_F1']['members'] == 96 and \
            RES['legs']['W1_F1']['rows_matched'] == 8 and \
            RES['legs']['W1_R']['agree'] == \
            RES['legs']['W1_R']['members'] == 79 and \
            RES['legs']['W1_R']['sig_matched'] == 79
    verdict = 'GREEN' if ok else 'RED'
    RES['verdict'] = verdict
    print('checks:', json.dumps(RES['checks'], sort_keys=True))
    print('VERDICT %s — %.1f s, %d violations'
          % (verdict, RES['secs'], len(RES['viol'])))
    if not smoke:
        with open(os.path.join(HERE,
                               'he7annexpass2_fresh_results.json'),
                  'w') as fh:
            json.dump(RES, fh, indent=1, sort_keys=True)
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
