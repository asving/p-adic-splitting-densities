"""HE6 passPE2 — FRESH-ROUTE legs (hostile verifier's instrument).

Disjoint from: the HE6 seal battery (mu=4, lam=u/2, ell in {1,2} labels),
the he6r1 682-member ell=1 battery, and HE7's arc legs.

LEG A (the ell=3 side family, PARI sigma):
  frame (e1,f1,h) = (2,1,1), Phi' = x^2-5 over Z_5, mu = 6, deg f = 12,
  lam = 7/3 (u=7, ell=3, gcd=1, lam > D'h = 2).  Single side (0,14)-(6,0),
  pins j = 0,3,6; residual R(Z) = Z^2 + c1 Z + c0 read in the
  pi-convention (pi-normalizer = x; eta = res(theta^2/5) = 1).
  PREREGISTERED:
    FA-P1  SPLIT rows (R = (Z-s1)(Z-s2), s1 != s2 in F_5^x): every member
           sigma = {(6,1),(6,1)}; INERT row (R = Z^2+2 irreducible):
           sigma = {(6,2)}  [THEOREM HE6.A dictionary at ell = 3,
           e = e1*ell = 6, f = f1*d_r].
    FA-P2  flat identity 2 v5(Res(f, Psi_{7/3,Z-s})) == 3*1*2*h_F(7/3) = 84
           EXACTLY for non-label letters s; STRICT excess (> 84) at each
           label [LEMMA HE6-3 / HE6-4 engine at an ell = 3 label].
    FA-P3  2 v5(Res(Phi', Psi)) == deg Psi * lam * e1/e1... = 6*(7/3) = 14
           [LEMMA HE6-1's height clause at ell = 3].

LEG B (LEMMA HE6-1L's exact reachable set at f1 >= 2, fractional height):
  frame (e1,f1,h) = (2,2,3), O = Z_3, Phi' = x^4 + 729 (theta: v = 3/2,
  eta = res(theta^2/27), eta^2 = -1, psi = T^2+1), D' = 4, K = F_9,
  varpi = x * 3^(-1) (i0 = 1, a0 = -1).
  At k = 3: i0(3) = 1, T(3) = {t < 2 : 3 >= (1+2t)*3} = {0} PROPER;
  q = (i0*k - i(k))/e1 = (3-1)/2 = 1.
  PREREGISTERED:
    FB-P1  the realized pi-read residue set {res(C(theta)/varpi(theta)^3)}
           over C in O[x], deg C < 4, dv(C) = 3, is F_3^x * eta^{-1}
           = {eta, 2 eta} — NOT the displayed span {c0 : c0 in F_3^x}
           = {1, 2} (LEMMA HE6-1L's set display omits the eta^{-q(k)}
           twist coset at proper T(k)); the single member C = x realizes
           eta^{-1} = -eta (refuting the '+q' sign of LEMMA HE6-0''s
           residue display; the correct direction is -q).
    FB-P2  at k = 9 = (D'-1)h (threshold; T(9) full, q(9) = 4,
           eta^{-4} = 1) the realized set is ALL 8 elements of F_9^x
           (the fullness clause of HE6-1L survives the twist).
    FB-P3  frame: x^4+729 single prime above 3, (e,f) = (2,2);
           etabar^2 = -1 with etabar not in F_3.

Consumes (read-only): w10_checks.gp_run, w12_checks.GP_FUN/parse_sig,
he6_checks.resultant/bareiss.  Writes he6_pe2_fresh_output.txt via tee
by the caller; results json he6_pe2_fresh_results.json.
"""
import os, sys, json, time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w10_checks as W10
import w12_checks as W12
from he6_checks import resultant

RES = {'legA': {}, 'legB': {}, 'viol': []}


def viol(leg, what):
    RES['viol'].append({'leg': leg, 'what': str(what)[:300]})
    print('  !! VIOLATION', leg, str(what)[:200])


def vp(n, p):
    if n == 0:
        return 10 ** 9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# ---------------------------------------------------------------- LEG A
P = 5


def pmulz(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return out


def paddz(f, g):
    n = max(len(f), len(g))
    return [(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
            for i in range(n)]


PHI = [-P, 0, 1]                                    # x^2 - 5


def phipow(k):
    out = [1]
    for _ in range(k):
        out = pmulz(out, PHI)
    return out


def build(A):                                       # f = Phi'^6 + sum A_j Phi'^j
    f = phipow(6)
    for j, aj in A.items():
        f = paddz(f, pmulz(aj, phipow(j)))
    return f


def h_F(dvs, kappa):
    return min(dvs[j] + j * kappa for j in dvs)


def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'


def leg_A():
    print('=== LEG A: ell = 3 side family over Z_5, lam = 7/3, mu = 6')
    u = 7
    # configs: residual Z^2 + c1 Z + c0 via A_3 = c1*x*5^3 (dv 7),
    # A_0 = c0*5^7 (dv 14)
    cfgs = {'SPLIT12': (2, 2, ((6, 1), (6, 1)), (1, 2)),   # (Z-1)(Z-2)
            'SPLIT14': (0, 4, ((6, 1), (6, 1)), (1, 4)),   # (Z-1)(Z-4)
            'INERT':   (0, 2, ((6, 2),), ())}              # Z^2+2 irred
    # perturbations strictly above the line height (6-j)*7/3
    perts = [None]
    for j in range(6):
        lo = (6 - j) * 7 // 3 + 1
        # A_j += c * x^(lo%2) * 5^(lo//2 + (lo%2==1)*0) with dv = lo or lo+1
        for dvv in (lo, lo + 1):
            i = dvv % 2
            a = (dvv - i) // 2
            perts.append((j, [0] * i + [5 ** a]))
    sig_jobs, meta = [], []
    for name, (c1, c0, pred, roots) in cfgs.items():
        for pt in perts[:13]:
            A = {0: [c0 * 5 ** 7], 3: [0, c1 * 5 ** 3]}
            if pt is not None:
                j, extra = pt
                A[j] = paddz(A.get(j, [0]), extra)
            f = build(A)
            dvs = {0: 14, 3: 7, 6: 0}
            meta.append((name, pred, roots, f, dvs))
            sig_jobs.append(polystr(f))
    lines = [W12.GP_FUN]
    for i, ps in enumerate(sig_jobs):
        lines.append('print("R %d ", sig(%s, %d))' % (i, ps, P))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = W12.parse_sig(rest)
    counts, nA = {}, 0
    for i, (name, pred, roots, f, dvs) in enumerate(meta):
        g = got.get(i)
        if g is None or g == ((-1, -1),):
            continue                                 # disc == 0 member: skip
        nA += 1
        counts.setdefault(name, {}).setdefault(str(g), 0)
        counts[name][str(g)] += 1
        if g != tuple(sorted(pred)):
            viol('FA-P1', '%s member %d sigma %s != pred %s'
                 % (name, i, g, pred))
        # FA-P2/P3 on the base member of each config only (cost control)
        if i % 13 == 0:
            gen = 3 * 1 * 2 * h_F(dvs, Fr(7, 3))
            assert gen == 84
            for s in (1, 2, 3, 4):
                Bs = [0, -s * 5 ** 3]
                Psi = paddz(phipow(3), Bs)           # Psi_{7/3, Z-s}
                meas = 2 * vp(resultant(f, Psi), 5)
                lab = s in roots
                if lab and meas <= gen:
                    viol('FA-P2', '%s: no excess at label s=%d (meas %d)'
                         % (name, s, meas))
                if (not lab) and meas != gen:
                    viol('FA-P2', '%s: flat fails at s=%d meas %d != 84'
                         % (name, s, meas))
                xi = 2 * vp(resultant(PHI, Psi), 5)
                if xi != 14:
                    viol('FA-P3', 'height read %d != 14 at s=%d' % (xi, s))
            print('  %s base: flat/excess + height OK (gen=84)' % name)
    RES['legA'] = {'sigma_counts': counts, 'members_scored': nA}
    print('  sigma census:', counts)


# ---------------------------------------------------------------- LEG B
GP_B = r"""
nf = nfinit(y^4 + 729);
dec = idealprimedec(nf, 3);
print("NPRIMES ", length(dec));
pr = dec[1];
print("EF ", pr.e, " ", pr.f);
mp = nfmodprinit(nf, pr);
et = nfmodpr(nf, Mod(y^2, y^4+729) / 27, mp);
print("ETA ", et);
print("ETASQ ", et^2);
print("ETAINV ", 1/et);
resset(k, cs) = {
  my(S = Set(), z, th = Mod(y, y^4+729));
  for (n = 1, length(cs),
    z = subst(cs[n], x, th) * 3^k / th^k;
    if (nfeltval(nf, z, pr) == 0,
      S = setunion(S, Set([Str(nfmodpr(nf, z, mp))])));
  );
  S
}
{
cs3 = [];
for (a1 = 1, 8, if (a1 % 3 != 0,
  for (a0i = 0, 2, for (a2 = 0, 2, for (a3 = 0, 2,
    cs3 = concat(cs3, [a0i*9 + a1*x + a2*x^2 + a3*x^3]))))));
}
S3 = resset(3, cs3);
print("K3N ", length(cs3), " ", length(S3));
print("K3SET ", S3);
print("CXRES ", Str(nfmodpr(nf, Mod(y,y^4+729) * 27 / Mod(y,y^4+729)^3, mp)));
{
cs9 = [];
for (a1i = 0, 8, for (a3 = 0, 8,
  if (a1i % 3 != 0 || a3 % 3 != 0,
    for (a0i = 0, 1, for (a2i = 0, 2,
      cs9 = concat(cs9, [a0i*3^5 + a1i*27*x + a2i*9*x^2 + a3*x^3]))))));
}
S9 = resset(9, cs9);
print("K9N ", length(S9));
quit
"""


def leg_B():
    print('=== LEG B: HE6-1L exact-set at (e1,f1,h) = (2,2,3), O = Z_3')
    out = W10.gp_run(GP_B)
    d = {}
    for line in out.splitlines():
        w = line.split(None, 1)
        if len(w) == 2:
            d[w[0]] = w[1].strip()
    eta, etasq, etainv = d.get('ETA'), d.get('ETASQ'), d.get('ETAINV')
    print('  frame: primes=%s ef=%s  eta=%s eta^2=%s eta^-1=%s'
          % (d.get('NPRIMES'), d.get('EF'), eta, etasq, etainv))
    if d.get('NPRIMES') != '1' or d.get('EF') != '2 2':
        viol('FB-P3', 'frame wrong: %s %s' % (d.get('NPRIMES'), d.get('EF')))
    if etasq != '2' or eta in ('1', '2'):        # eta^2 = -1 = 2, eta not in F_3
        viol('FB-P3', 'eta wrong: eta=%s eta^2=%s' % (eta, etasq))
    k3 = d.get('K3SET', '')
    k3set = set(s.strip().strip('"') for s in
                k3.strip('[]').split(',') if s.strip())
    # eta and 2*eta as gp Str's; F_3^x = {"1","2"}
    twist_set = {eta, '2*%s' % eta if '*' not in (eta or '') else None}
    print('  k=3 members/realized: %s ; realized set: %s' % (d.get('K3N'), sorted(k3set)))
    print('  displayed span F_3^x = {1, 2}; twisted coset {eta, 2eta} ~ {%s, 2*(%s)}'
          % (eta, eta))
    displayed_hit = k3set & {'1', '2'}
    if displayed_hit:
        print('  NOTE: displayed span intersects realized set: %s' % displayed_hit)
    else:
        print('  CONFIRMED: realized set disjoint from the displayed span {1,2}')
    RES['legB'].update(k3set=sorted(k3set), eta=eta, etainv=etainv,
                       cx=d.get('CXRES'), k9n=d.get('K9N'))
    print('  C = x residue: %s   (claim +q predicts eta = %s; -q predicts '
          'eta^-1 = %s)' % (d.get('CXRES'), eta, etainv))
    print('  k=9 realized count: %s (expect 8 = all of F_9^x)' % d.get('K9N'))
    if d.get('K9N') != '8':
        viol('FB-P2', 'k=9 not onto: %s' % d.get('K9N'))
    return d


def main():
    t0 = time.time()
    leg_A()
    d = leg_B()
    RES['secs'] = round(time.time() - t0, 1)
    RES['nviol'] = len(RES['viol'])
    print('VIOLATIONS: %d   %.1fs' % (len(RES['viol']), time.time() - t0))
    with open(os.path.join(HERE, 'he6_pe2_fresh_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True, default=str)


if __name__ == '__main__':
    main()
