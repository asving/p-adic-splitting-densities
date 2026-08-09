#!/usr/bin/env python3
"""HE6R1 passPE3 FRESH ROUTE — the ell2 = 3 genre (level-2 denominator 3)
plus two-sided level-2 polygons at mu2 = 3, with BOTH PARI oracles.

Disjoint from: the seal battery (p in {3,5,7}, mu2 = 2, ell2 in {1,2}),
PE1's legs (p = 11/13 same frame; peel-compose-refine at mu2 = 3), and
PE2's leg (non-prime-q base f1 = 2, ell2 in {1,2}).  NOTHING in the
program has run ell2 = 3, nor a multiplicity-3 repeated residual factor
(R_lambda = r^3), nor a mixed two-sided level-2 polygon on the widened
box's ell = 1 branch.  Construction and predictions are derived BY THIS
VERIFIER from first principles (Newton polygons + the sigma dictionary
e = e1*ell*ell2, f = f1*d_r*deg r2); the sealed reader is NOT imported.

FRAME (as in the recon's rows): (e1, f1, h) = (2, 1, 1), Phi' = x^2 - p,
varpi = x, D' = 2; level-1 label lambda = 3 (ell = 1), r = Z^2 + aZ + b
irreducible over F_p; Psi = Phi'^2 + a*x*p*Phi' + b*p^3 (degree D'' = 4);
T2 = d_r*lambda = 6.  Base polynomials have R_lambda = r^3 (m = 3,
mu = 6, n = 12, mu2 = 3).

FAMILY C3 (the ell2 = 3 genre): f = Psi^3 - E + P, dv2(E) = u2 with
u2 in {19, 20} (lambda2 = u2/3 > 6, gcd(u2,3) = 1), P strictly above the
level-2 line (dv2(x^i p^k) > u2(3-j)/3 at Psi-degree j).  Level-2 polygon:
single side (3,0)-(0,u2), slope u2/3, ell2 = 3, R2 linear (nonzero root).
  PREREGISTERED FR-P1: sigma = {(6,2)} — ONE prime, e = e1*ell*ell2 = 6,
  f = f1*d_r*1 = 2 — on EVERY member, by BOTH oracles (idealprimedec
  (e,f) per prime; factorpadic returns a single degree-12 local factor).
  Independent leg (no HE7 cite): v(Psi(theta)) = u2/6 forces 6 | e at
  u2 = 19 (2|e and 3|e at u2 = 20 via v(Phi'(theta)) = 3/2), and
  beta = res(Phi'/x^3) a root of r forces F_{p^2} in the residue field,
  so (e,f) = (6,2) is the only shape with ef <= 12.  p = 3 is the WILD
  corner (3 | e = 6): the polygon dictionary is characteristic-blind and
  is here machine-tested at wild ramification for the first time in this
  program's ell = 1 branch.

FAMILY TS (two-sided level-2 polygon): f = (Psi - E1)(Psi^2 - E2) + P,
dv2(E1) = 8 (an integer lambda2a = 8 > 6), dv2(E2) = 13 (lambda2b = 13/2,
ell2 = 2).  Development pins (3,0), (2,8), (1,13), (0,21): the pin (2,8)
lies strictly above the hull (line (3,0)-(1,13) has 13/2 < 8 at j = 2),
so P2(f) = side 13/2 of length 2 + side 8 of length 1.
  PREREGISTERED FR-P2: sigma = {(4,2), (2,2)} on every member — the 13/2
  side gives e = 2*1*2 = 4, f = 2; the 8 side gives e = 2, f = 2;
  factorpadic degree multiset {8, 4}.

SELF-TOOTH FR-P3: the planted dictionary "treat the three-fold r^3 as
three separable blocks" (sigma = {(2,2),(2,2),(2,2)}) must be refuted by
PARI on every C3 member tested (it shares no (6,2) prime).

Frames: C3 at (p, u2, r) = (3, 19, Z^2+1), (5, 19, Z^2+2), (7, 20, Z^2+Z+3),
(5, 20, Z^2+Z+1); TS at (3, Z^2+1), (5, Z^2+2).  Members: c-sweep over the
E-coefficients plus a perturbation sweep (delta, i, k, j) strictly above
the line(s); disc = 0 members skipped with count (asserted disclosed).

Written and preregistered BEFORE the first gp call of this run.
"""
import json, subprocess, sys, time

# ---------------------------------------------------------------- polys
# poly = list of ints, low-first


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def ppow(a, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, a)
    return out


def pscale(a, c):
    return [c * x for x in a]


def polstr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'


# ------------------------------------------------------------- gp oracle
def gp_batch(scripts):
    out = subprocess.run(['gp', '-q'],
                         input='default(parisize,"1024M");\n'
                               + '\n'.join(scripts) + '\nquit\n',
                         capture_output=True, text=True, timeout=2400)
    if out.returncode != 0 and not out.stdout:
        raise RuntimeError('gp failed: ' + out.stderr[:500])
    return out.stdout


def oracle_both(members, p):
    """BOTH oracles per member: (A) factor over Q + nfinit +
    idealprimedec -> multiset of (e,f); (B) factorpadic -> multiset of
    local factor degrees. Returns dict idx -> (sigma, degs) or 'DISC0'."""
    lines = []
    for i, f in enumerate(members):
        pol = polstr(f)
        lines.append(
            'f=%s; d=poldisc(f); '
            'if(d==0, print("M%d DISC0"), '
            'fa=factor(f); s=[]; '
            'for(k=1, matsize(fa)[1], g=fa[k,1]; '
            ' K=nfinit([g,[%d]]); pr=idealprimedec(K,%d); '
            ' for(t=1, length(pr), s=concat(s,[[pr[t].e, pr[t].f]]))); '
            'fp=factorpadic(f,%d,60); ds=[]; '
            'for(k=1, matsize(fp)[1], ds=concat(ds,[poldegree(fp[k,1])])); '
            'print("M%d ", s, " | ", ds))' % (pol, i, p, p, p, i))
    txt = gp_batch(lines)
    res = {}
    for ln in txt.splitlines():
        ln = ln.strip()
        if not ln.startswith('M'):
            continue
        tag, rest = ln.split(' ', 1)
        idx = int(tag[1:])
        if rest.strip() == 'DISC0':
            res[idx] = 'DISC0'
            continue
        sig_s, deg_s = rest.split('|')
        clean = lambda s: [int(t) for t in
                           s.replace('[', ' ').replace(']', ' ')
                            .replace(',', ' ').split()]
        nums = clean(sig_s)
        sigma = tuple(sorted((nums[t], nums[t + 1])
                             for t in range(0, len(nums), 2)))
        degs = tuple(sorted(clean(deg_s)))
        res[idx] = (sigma, degs)
    return res


# ------------------------------------------------------------ the frames
def mk_psi(p, a, b):
    """Psi = (x^2-p)^2 + a*x*p*(x^2-p) + b*p^3 (monic, degree 4)."""
    Phi = [-p, 0, 1]
    return padd(padd(ppow(Phi, 2), pscale(pmul([0, p], Phi), a)),
                [b * p**3])


def mono(i, k, p, coef):
    """coef * x^i * p^k as a poly; dv2 = i + 2k."""
    out = [0] * i + [coef * p**k]
    return out


def c3_members(p, u2, a, b, cap):
    """FAMILY C3: Psi^3 - E + P, dv2(E) = u2, P strictly above the line."""
    Psi = mk_psi(p, a, b)
    base3 = ppow(Psi, 3)
    # E choices at dv2 = u2 (deg < 4)
    if u2 % 2 == 1:
        Es = [(1, (u2 - 1) // 2), (3, (u2 - 3) // 2)]     # x*p^..., x^3*p^...
    else:
        Es = [(0, u2 // 2), (2, (u2 - 2) // 2)]
    # perturbations strictly above the line u2*(3-j)/3 at Psi-degree j
    perts = [None]
    for j in (0, 1, 2):
        bound = u2 * (3 - j) / 3.0
        for (i, k) in ((0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1),
                       (2, 1), (3, 1), (0, 2), (1, 2), (2, 2), (3, 2),
                       (1, 6), (0, 7), (3, 6), (2, 7), (1, 9), (0, 10),
                       (3, 9), (2, 10), (1, 12), (3, 11)):
            dv2 = i + 2 * k
            if bound < dv2 <= bound + 4:
                perts.append((j, i, k))
    out = []
    for (ei, ek) in Es:
        for c in range(1, p):
            f0 = padd(base3, mono(ei, ek, p, -c))
            for pt in perts:
                if pt is None:
                    out.append(f0)
                else:
                    (j, i, k) = pt
                    for d in (1, p - 1):
                        f = padd(f0, pmul(mono(i, k, p, d), ppow(Psi, j)))
                        out.append(f)
                if len(out) >= cap:
                    return out
    return out


def ts_members(p, a, b, cap):
    """FAMILY TS: (Psi - E1)(Psi^2 - E2) + P; dv2(E1) = 8, dv2(E2) = 13."""
    Psi = mk_psi(p, a, b)
    out = []
    # E1 at dv2 = 8: x^0*p^4 or x^2*p^3 ; E2 at dv2 = 13: x*p^6 or x^3*p^5
    for (i1, k1) in ((0, 4), (2, 3)):
        for (i2, k2) in ((1, 6), (3, 5)):
            for c1 in range(1, p):
                for c2 in range(1, p):
                    fA = padd(Psi, mono(i1, k1, p, -c1))
                    fB = padd(ppow(Psi, 2), mono(i2, k2, p, -c2))
                    f0 = pmul(fA, fB)
                    out.append(f0)
                    # perturbations strictly above the hull:
                    # j=2: >13/2 -> dv2>=7; j=1: >13 -> >=14; j=0: >21 -> >=22
                    for (j, i, k) in ((2, 1, 3), (2, 3, 2), (1, 0, 7),
                                      (1, 2, 6), (0, 1, 11), (0, 0, 11)):
                        f = padd(f0, pmul(mono(i, k, p, 1), ppow(Psi, j)))
                        out.append(f)
                    if len(out) >= cap:
                        return out
    return out


# ------------------------------------------------------------------ main
def main():
    t0 = time.time()
    RES = {'legs': {}, 'viol': [], 'rows': []}
    C3 = [(3, 19, 1, 0, 1), (5, 19, 2, 0, 2), (7, 20, 3, 1, 3),
          (5, 20, 1, 1, 1)]           # (p, u2, r-coeffs a?, ...) see below
    # r = Z^2 + aZ + b irreducible over F_p:
    #   p=3: Z^2+1 (a=0,b=1); p=5: Z^2+2 (a=0,b=2) and Z^2+Z+1 (a=1,b=1);
    #   p=7: Z^2+Z+3 (a=1,b=3)
    frames_c3 = [(3, 19, 0, 1), (5, 19, 0, 2), (7, 20, 1, 3), (5, 20, 1, 1)]
    frames_ts = [(3, 0, 1), (5, 0, 2)]
    tot = {'members': 0, 'pari': 0, 'agree': 0, 'disc0': 0}
    tooth_refuted = 0
    tooth_tested = 0
    for (p, u2, a, b) in frames_c3:
        mem = c3_members(p, u2, a, b, cap=40)
        want_sig = ((6, 2),)
        want_deg = (12,)
        got = oracle_both(mem, p)
        n_ok = n_bad = n_d0 = 0
        for i in range(len(mem)):
            r = got.get(i)
            if r is None:
                RES['viol'].append({'leg': 'PE3-ORACLE', 'frame': (p, u2),
                                    'i': i, 'what': 'no oracle line'})
                continue
            if r == 'DISC0':
                n_d0 += 1
                continue
            sigma, degs = r
            tot['pari'] += 1
            if sigma == want_sig and degs == want_deg:
                n_ok += 1
            else:
                n_bad += 1
                RES['viol'].append({'leg': 'PE3-C3', 'frame': (p, u2),
                                    'i': i, 'sigma': str(sigma),
                                    'degs': str(degs),
                                    'f': polstr(mem[i])})
            # self-tooth on the first 2 clean members per frame
            if tooth_tested < 8 and i < 2:
                tooth_tested += 1
                planted = ((2, 2), (2, 2), (2, 2))
                if sigma != planted:
                    tooth_refuted += 1
        tot['members'] += len(mem)
        tot['agree'] += n_ok
        tot['disc0'] += n_d0
        row = {'family': 'C3', 'p': p, 'u2': u2, 'r': 'Z^2+%dZ+%d' % (a, b),
               'members': len(mem), 'ok': n_ok, 'bad': n_bad, 'disc0': n_d0}
        RES['rows'].append(row)
        print('C3 p=%d u2=%d r=Z^2+%dZ+%d: members %d ok %d bad %d disc0 %d'
              % (p, u2, a, b, len(mem), n_ok, n_bad, n_d0))
    for (p, a, b) in frames_ts:
        mem = ts_members(p, a, b, cap=42)
        want_sig = ((2, 2), (4, 2))
        want_deg = (4, 8)
        got = oracle_both(mem, p)
        n_ok = n_bad = n_d0 = 0
        for i in range(len(mem)):
            r = got.get(i)
            if r is None:
                RES['viol'].append({'leg': 'PE3-ORACLE', 'frame': (p, 'TS'),
                                    'i': i, 'what': 'no oracle line'})
                continue
            if r == 'DISC0':
                n_d0 += 1
                continue
            sigma, degs = r
            tot['pari'] += 1
            if sigma == want_sig and degs == want_deg:
                n_ok += 1
            else:
                n_bad += 1
                RES['viol'].append({'leg': 'PE3-TS', 'frame': (p,),
                                    'i': i, 'sigma': str(sigma),
                                    'degs': str(degs),
                                    'f': polstr(mem[i])})
        tot['members'] += len(mem)
        tot['agree'] += n_ok
        tot['disc0'] += n_d0
        row = {'family': 'TS', 'p': p, 'r': 'Z^2+%dZ+%d' % (a, b),
               'members': len(mem), 'ok': n_ok, 'bad': n_bad, 'disc0': n_d0}
        RES['rows'].append(row)
        print('TS p=%d r=Z^2+%dZ+%d: members %d ok %d bad %d disc0 %d'
              % (p, a, b, len(mem), n_ok, n_bad, n_d0))
    RES['totals'] = tot
    RES['tooth'] = {'tested': tooth_tested, 'refuted': tooth_refuted}
    RES['secs'] = round(time.time() - t0, 1)
    RES['violations'] = len(RES['viol'])
    print('TOTALS', json.dumps(tot), 'tooth', json.dumps(RES['tooth']),
          'violations', len(RES['viol']), 'secs', RES['secs'])
    with open(__file__.replace('.py', '_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, default=str)


if __name__ == '__main__':
    main()
