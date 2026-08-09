#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""HE6R1 passPE2 FRESH ROUTE — the non-prime-q leg (disjoint from the seal
battery, PE1's p=11/13 leg A and PE1's peel-compose leg B).

CHARGE (from the PE2 verifier prompt): run the PE1-disclosed never-run
candidate — an ell = 1 repeated-irreducible-residual family over a
NON-PRIME residue field K = F_{p^2} (f1 = 2, e1 = 1), i.e. K2 = F_{p^4}.
Everything the sealed battery ran had f1 = 1 (K = F_p); this leg is the
first machine contact of the widened box's ell = 1 branch at f1 >= 2.

FRAME (built from first principles by the verifier, NOT from the sealed
reader; the level-2 residual and the sigma dictionary are DERIVED here and
scored against PARI, so a construction error and a dictionary error alike
surface as mismatches):
    e1 = 1, f1 = 2, h = 1, Phi' = x^2 - c*p^2 with c a QNR mod p,
    D' = 2, dv = v, D'h = 2, varpi-normalizer = p (letter eta = res(x/p),
    eta^2 = c, K = F_{p^2} = F_p[w]/(w^2-c)).
    ell = 1, lambda = 3 > D'h; r in K[Z] monic irreducible, deg 2,
    r(0) != 0  ==>  D'' = 4, K2 = F_{p^4} = K[beta]/(r), T2 = 2*lambda = 6.
    Psi = Phi'^2 + B1*Phi' + B0, B_t realizing r's coefficients at slot
    heights (2-t)*lambda via  a*p^m + b*p^(m-1)*x  |-> a + b*eta.
    Members deg 8, mu2 = 2 (block = everything, R_lambda = r^2, mu = 4).

FAMILIES (per (p, r) frame):
  A0  f = Psi^2 + C0,          dv2(C0) = 14 (lambda2 = 7, ell2 = 1, gam1 = 0)
  A1  f = Psi^2 + C1*Psi + C0, dv2(C1) = 7 on-line (gam1 != 0), dv2(C0) = 14
  B   f = Psi^2 + C0,          dv2(C0) = 13 (lambda2 = 13/2, ell2 = 2)
  P   f = Psi*(Psi + C1),      Psi | f — the peel stratum (LEMMA HE6R1-3 at
                               f1 = 2: prediction e(Psi) = e1*ell = 1,
                               f(Psi) = f1*d_r = 4), cofactor block (1,4)

PREDICTED sigma (derived from the composed dictionary e = e1*ell*ell2,
f = f1*d_r*deg r2, by factoring R(Z) = Z^2 + gam1*Z + gam0 over K2 = F_{p^4},
gam_j the level-2 residues of C_j read off the construction):
  A0/A1: R irreducible -> {(1,8)}; two distinct roots -> {(1,4),(1,4)};
         double root -> ALPHA-REFINE stratum, SET ASIDE with count
         (this leg scores the un-refined read only; PE1 leg B covered
         peel-compose-refine at f1 = 1).
  B:     {(2,4)} unconditionally (deg R = 1).
  P:     {(1,4),(1,4)}, plus a DIRECT nfinit check on Psi itself.

ORACLE: PARI/gp — factor f over Q, nfinit([g,[p]]) + idealprimedec per
rational factor, multiset of (e,f). poldisc != 0 asserted per member. EXACT
integer arithmetic throughout (no floats).

Preregistration: the predictions above were fixed before the first gp call
of this leg (this docstring is the preregistration; no smoke run of this
runner preceded it — its first execution is the recorded one, with the
debug trail, if one is needed, disclosed in the report).
"""
import json, subprocess, sys, time

# ---------------- exact finite-field towers F_p -> F_{p^2} -> F_{p^4} ----
class F:  # F_{p^2}[beta]/(r) elements as ((a,b),(c,d)): (a+bw) + (c+dw)beta
    pass

def k_mul(x, y, p, c):      # F_{p^2} = F_p[w]/(w^2 - c): (a,b)*(a',b')
    a, b = x; A, B = y
    return ((a*A + c*b*B) % p, (a*B + b*A) % p)

def k_add(x, y, p):
    return ((x[0]+y[0]) % p, (x[1]+y[1]) % p)

def k_neg(x, p):
    return ((-x[0]) % p, (-x[1]) % p)

def k2_add(x, y, p):
    return (k_add(x[0], y[0], p), k_add(x[1], y[1], p))

def k2_mul(x, y, p, c, r1, r0):
    # (u0 + u1 b)(v0 + v1 b) = u0v0 + (u0v1+u1v0) b + u1v1 b^2,
    # b^2 = -r1 b - r0
    u0, u1 = x; v0, v1 = y
    w0 = k_mul(u0, v0, p, c); w1 = k_add(k_mul(u0, v1, p, c),
                                         k_mul(u1, v0, p, c), p)
    w2 = k_mul(u1, v1, p, c)
    w0 = k_add(w0, k_mul(w2, k_neg(r0, p), p, c), p)
    w1 = k_add(w1, k_mul(w2, k_neg(r1, p), p, c), p)
    return (w0, w1)

def k2_zero():
    return (((0, 0)), ((0, 0)))

def k2_is_zero(x):
    return x[0] == (0, 0) and x[1] == (0, 0)

def k2_elems(p):
    for a in range(p):
        for b in range(p):
            for cc in range(p):
                for d in range(p):
                    yield ((a, b), (cc, d))

def quad_roots_k2(gam1, gam0, p, c, r1, r0):
    """roots of Z^2 + gam1 Z + gam0 over F_{p^4}, by exhaustive search."""
    roots = []
    for z in k2_elems(p):
        v = k2_add(k2_add(k2_mul(z, z, p, c, r1, r0),
                          k2_mul(gam1, z, p, c, r1, r0), p), gam0, p)
        if k2_is_zero(v):
            roots.append(z)
    return roots

def find_r(p, c, want_r1_nonzero):
    """monic irreducible quadratic r = Z^2 + r1 Z + r0 over F_{p^2},
    r0 != 0; irreducible <=> no root in F_{p^2}."""
    K = [(a, b) for a in range(p) for b in range(p)]
    for r1 in K:
        if want_r1_nonzero and r1 == (0, 0):
            continue
        if (not want_r1_nonzero) and r1 != (0, 0):
            continue
        for r0 in K:
            if r0 == (0, 0):
                continue
            ok = True
            for z in K:
                v = k_add(k_add(k_mul(z, z, p, c), k_mul(r1, z, p, c), p),
                          r0, p)
                if v == (0, 0):
                    ok = False
                    break
            if ok:
                return r1, r0
    raise RuntimeError('no irreducible r found')

# ---------------- integer polynomials (dense lists, low degree first) ----
def pmul(f, g):
    out = [0]*(len(f)+len(g)-1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i+j] += a*b
    return out

def padd(f, g):
    n = max(len(f), len(g)); out = [0]*n
    for i, a in enumerate(f):
        out[i] += a
    for i, b in enumerate(g):
        out[i] += b
    return out

def slot_poly(pair, m, p):
    """K-element (a,b) realized at height m:  a*p^m + b*p^(m-1)*x
    (residue a + b*eta at a (T1)/(T2) point of v = h = 1)."""
    a, b = pair
    return [a*p**m, b*p**(m-1)]

def build_C(res0, res1, m, lam, p):
    """C = c0 + c1*Phi' with level-2 residue res0 + res1*beta at dv2 = m:
    c0 at slot height m, c1 at slot height m - lam."""
    Phi = PHI
    c0 = slot_poly(res0, m, p)
    c1 = slot_poly(res1, m - lam, p)
    return padd(c0, pmul(c1, Phi))

def polstr(f):
    return '+'.join('(%d)*x^%d' % (a, i) for i, a in enumerate(f)
                    if a != 0) or '0'

# ---------------- PARI oracle ----------------
def pari_sigma(members, p):
    """members: list of integer polys (low-first). returns list of sorted
    (e,f) multisets + disc-nonzero flags, via one gp process."""
    lines = ['default(parisize, "512M");']
    for i, f in enumerate(members):
        pol = polstr(f).replace('x', 'y')  # avoid priority issues? keep x
        pol = polstr(f)
        lines.append(
            'f=%s; d=poldisc(f); '
            'if(d==0, print("M%d DISC0"), '
            'fa=factor(f); s=[]; '
            'for(k=1, matsize(fa)[1], g=fa[k,1]; '
            ' K=nfinit([g,[%d]]); pr=idealprimedec(K,%d); '
            ' for(t=1, length(pr), s=concat(s,[[pr[t].e, pr[t].f]]))); '
            'print("M%d ", s))' % (pol, i, p, p, i))
    lines.append('quit')
    out = subprocess.run(['gp', '-q'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=1200)
    res = {}
    for ln in out.stdout.splitlines():
        ln = ln.strip()
        if not ln.startswith('M'):
            continue
        tag, rest = ln.split(' ', 1)
        idx = int(tag[1:])
        if rest.strip() == 'DISC0':
            res[idx] = 'DISC0'
            continue
        pairs = []
        s = rest.replace('[', ' ').replace(']', ' ').replace(',', ' ')
        nums = [int(t) for t in s.split()]
        for k in range(0, len(nums), 2):
            pairs.append((nums[k], nums[k+1]))
        res[idx] = tuple(sorted(pairs))
    if len(res) != len(members):
        sys.stderr.write(out.stdout[-2000:] + '\n' + out.stderr[-2000:])
        raise RuntimeError('gp returned %d of %d' % (len(res), len(members)))
    return [res[i] for i in range(len(members))]

# ---------------- the leg ----------------
VIOL = []
REC = {'frames': [], 'viol': VIOL}

def run_frame(p, c, want_r1_nonzero, sample_cap):
    global PHI
    lam = 3
    r1, r0 = find_r(p, c, want_r1_nonzero)
    PHI = [-c*p**2, 0, 1]                      # x^2 - c p^2
    B1 = slot_poly(r1, lam, p)                 # residue r1 at height lam
    B0 = slot_poly(r0, 2*lam, p)               # residue r0 at height 2lam
    Psi = padd(padd(pmul(PHI, PHI), pmul(B1, PHI)), B0)
    frame = {'p': p, 'c': c, 'r1': r1, 'r0': r0, 'lam': lam,
             'Psi': polstr(Psi), 'families': {}}
    print('== FRAME p=%d c=%d K=F_%d r=Z^2+%sZ+%s K2=F_%d Psi=%s' %
          (p, c, p*p, r1, r0, p**4, polstr(Psi)))
    Kel = [(a, b) for a in range(p) for b in range(p)]
    K2el = [(x, y) for x in Kel for y in Kel]

    def K2nz(cap):
        got = 0
        for z in K2el:
            if z == ((0, 0), (0, 0)):
                continue
            yield z
            got += 1
            if got >= cap:
                return

    # ---- family A0: gam1 = 0, gam0 ranges over K2^x (capped)
    members, preds, kinds = [], [], []
    refine_set_aside = 0
    for g0 in K2nz(sample_cap):
        C0 = build_C(g0[0], g0[1], 14, lam, p)
        f = padd(pmul(Psi, Psi), C0)
        roots = quad_roots_k2(k2_zero(), g0, p, c, r1, r0)
        # prediction from the derived residual R = Z^2 + gam0
        if len(roots) == 0:
            pred = ((1, 8),)
        elif len(roots) == 2:
            pred = ((1, 4), (1, 4))
        else:
            refine_set_aside += 1
            continue
        members.append(f); preds.append(pred); kinds.append('A0')
    # ---- family A1: two fixed gam1 != 0, gam0 over K2^x (capped)
    gam1_list = [(( (1,0) ), ((0,0))), (((0,1)), ((1,0)))]  # 1 ; w + beta
    for g1 in gam1_list:
        C1 = build_C(g1[0], g1[1], 7, lam, p)
        for g0 in K2nz(sample_cap // 2):
            C0 = build_C(g0[0], g0[1], 14, lam, p)
            f = padd(padd(pmul(Psi, Psi), pmul(C1, Psi)), C0)
            roots = quad_roots_k2(g1, g0, p, c, r1, r0)
            if len(roots) == 0:
                pred = ((1, 8),)
            elif len(roots) == 2:
                pred = ((1, 4), (1, 4))
            else:
                refine_set_aside += 1
                continue
            members.append(f); preds.append(pred); kinds.append('A1')
    # ---- family B: lambda2 = 13/2
    for g0 in K2nz(sample_cap // 4):
        C0 = build_C(g0[0], g0[1], 13, lam, p)
        f = padd(pmul(Psi, Psi), C0)
        members.append(f); preds.append(((2, 4),)); kinds.append('B')
    # ---- family P: Psi | f (peel), cofactor Psi + C1 at m1 = 7
    for g1 in K2nz(6):
        C1 = build_C(g1[0], g1[1], 7, lam, p)
        f = pmul(Psi, padd(Psi, C1))
        members.append(f); preds.append(((1, 4), (1, 4))); kinds.append('P')
    # ---- direct HE6R1-3 check on Psi itself
    members.append(Psi); preds.append(((1, 4),)); kinds.append('PSI')

    got = pari_sigma(members, p)
    agree = mism = disc0 = 0
    for f, pred, kind, sg in zip(members, preds, kinds, got):
        if sg == 'DISC0':
            disc0 += 1
            VIOL.append({'frame': (p, r1, r0), 'kind': kind,
                         'f': polstr(f), 'why': 'DISC0'})
            continue
        if sg == pred:
            agree += 1
        else:
            mism += 1
            VIOL.append({'frame': (p, r1, r0), 'kind': kind, 'pred': pred,
                         'pari': sg, 'f': polstr(f)})
    kc = {}
    for k in kinds:
        kc[k] = kc.get(k, 0) + 1
    print('   members %d (%s)  refine-set-aside %d  PARI agree %d '
          'mismatch %d disc0 %d' % (len(members), kc, refine_set_aside,
                                    agree, mism, disc0))
    frame['families'] = kc
    frame['refine_set_aside'] = refine_set_aside
    frame['agree'] = agree; frame['mismatch'] = mism; frame['disc0'] = disc0
    REC['frames'].append(frame)

def main():
    t0 = time.time()
    # QNR: 2 mod 3 (squares {0,1}); 2 mod 5 (squares {0,1,4});
    run_frame(3, 2, False, 80)   # r1 = 0 genre, F_9 base, full gam0 sweep
    run_frame(3, 2, True, 80)    # r1 != 0 genre (c1 LIVE analogue)
    run_frame(5, 2, True, 48)    # F_25 base, sampled
    REC['secs'] = round(time.time() - t0, 1)
    REC['violations'] = len(VIOL)
    print('TOTAL violations:', len(VIOL), ' secs:', REC['secs'])
    with open('he6r1_pe2_fresh_results.json', 'w') as fh:
        json.dump(REC, fh, indent=1, default=str)

if __name__ == '__main__':
    main()
