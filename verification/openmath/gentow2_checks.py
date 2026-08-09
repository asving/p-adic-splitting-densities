#!/usr/bin/env python3
"""GENTOW-2 battery: [GENHN-TOW-1] item (6)(alpha) — THEOREM
GENTOW2-A (FGMN Thm 6.3 + Cor 6.4 instance) checked at the 5
committed witnesses + 2 NEW depth-3 witnesses at other (e_i,f_i)
profiles, on TWO decorrelated oracles:
  A-route: exact integer arithmetic (pin tables, one-sidedness,
    on-side residual support, Sylvester/Bareiss resultant v2's);
  B-route: PARI/gp (factor + idealprimedec sig1, factorpadic sig2,
    nfeltval intermediate values at a prime above 2).

WITNESSES (profile = (e1,f1,e2,f2,e3,f3); Phi' = x^2-2 throughout):
 W1 (committed, r3 box): Phi3a = Phi2^2 - 16*Phi', Phi2=(x^2-2)^2-4x,
    profile (2,1,2,1,2,1), u2=5, u3=21.
 W2 (committed, PE3 F-1/FR3 uncancelled carry): Phi3b = Phi2^2-16x*Phi',
    same profile, u3=23.
 W3/W4/W5 (committed, SUPP-C leaves, n=16): f = Phi3a^2 + E1*Phi3a + E0,
    (E1,E0) = (0,256*Phi2) / (0,512*Phi2) / (512x, 2^18*x*Phi'*Phi2).
 N1 (NEW, f2=2 profile (2,1,1,2,2,1)): Phi2b = Phi'^2-2x*Phi'-8
    (u2=3, psi2=T^2+T+1), Phi3c = Phi2b^2 - 64x (u3=13, e3=2, f3=1).
 N2 (NEW, f3=2 profile (2,1,2,1,1,2) — the PE3-R1 machine-unwitnessed
    f3>=2 branch): Phi3d = Phi2^2 - 2x*Phi'*Phi2 - 32x (u3=11, e3=1,
    psi3 = y^2+y+1 over F2).

PREREGISTERED PREDICTIONS (sealed before first full run):
 P-W1: Phi'-pins {0:10, 2:7, 4:0} (1,3 absent); one side (4,0)-(0,10)
   slope 5/2 = kappa2; on-side J={0,4} = 2*supp(psi2^2), psi2=y+1;
   Phi2-pins {0:21, 2:0}, side slope 21/2, on-side {0,2}; resultant
   v2: (x,Phi',Phi2) = (4,10,21); PARI sig1=sig2=[(8,1)]; nfeltval
   (x,Phi',Phi2) = (4,10,21).
 P-W2: Phi'-pins {0:10, 1:8, 2:7, 4:0}; side (4,0)-(0,10), on-side
   {0,4}; Phi2-pins {0:23, 2:0}; resultant (4,10,23); PARI [(8,1)];
   nfeltval (4,10,23)  [= the FR3 committed triple].
 P-W3/4/5: PARI sig2 {(16,1)}/{(16,1)}/{(8,1),(8,1)}; resultant v2
   (Res(f,Phi'), Res(f,Phi2), Res(f,Phi3a)) = (20,42,85)/(20,42,93)/
   (20,42,179); W3/W4 nfeltval (x,Phi',Phi2) = (8,20,42).
 P-N1: Phi'-pins {0:12, 1:11, 2:6, 3:4, 4:0}; one side (4,0)-(0,12)
   slope 3 = kappa2; on-side J={0,2,4} = supp(psi2^2)=y^4+y^2+1
   (e2=1); Phi2b-pins {0:13, 2:0} slope 13/2; resultant (x,Phi',Phi2b)
   = (4,12,26); PARI [(4,2)]; nfeltval (2,6,13).
 P-N2: Phi'-pins {0:10, 1:10, 2:6, 3:3, 4:0}; one side (4,0)-(0,10)
   slope 5/2; on-side {0,4}; Phi2-pins {0:22, 1:11, 2:0} ALL on side
   slope 11 (residual y^2+y+1 = psi3, the f3=2 read); resultant
   (4,10,22); PARI [(4,2)]; nfeltval (2,5,11).
 TOOTH-T1 (floor breach = (beta) load-bearing): Phi3t1 = Phi2^2
   - 2*Phi'*Phi2 - 16x (u3=9 < 10 = e2f2u2): the Phi'-development is
   NOT one-sided (pin (3,2) strictly below the (0,*)-(4,0) chord) —
   the A-route checker must FLAG it.
 TOOTH-T2 (reducible residual): Phi3t2 = Phi2^2 - 64x (u3=26 even,
   e3=1, R = y^2+1 = (y+1)^2 reducible): PARI must give TWO factors
   [(4,1),(4,1)] — key-hood needs Lemma 5.3's irreducibility, the
   polygon side alone does not certify.
VERDICT: GREEN iff 0 violations on scored checks AND both teeth fire.
Written 2026-08-09 by GENTOW-2 (BOX-CLOSURE campaign); independent of
genhnr2_supp.py (no imports; committed artifacts untouched).
"""
import json
import subprocess
import sys

VIOL = []
NCHK = [0]
TEETH = {}


def say(s):
    print(s)
    sys.stdout.flush()


def chk(ok, msg):
    NCHK[0] += 1
    if not ok:
        VIOL.append(msg)
        say('  VIOLATION: %s' % msg)


def v2(n):
    n = abs(n)
    if n == 0:
        return None
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def padd(f, g):
    r = [0] * max(len(f), len(g))
    for i, c in enumerate(f):
        r[i] += c
    for i, c in enumerate(g):
        r[i] += c
    while r and r[-1] == 0:
        r.pop()
    return r


def pmul(f, g):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            r[i + j] += a * b
    while r and r[-1] == 0:
        r.pop()
    return r


def pdivmod_monic(f, g):
    f = list(f)
    q = [0] * max(1, len(f) - len(g) + 1)
    while len(f) >= len(g) and any(f):
        c = f[-1]
        d = len(f) - len(g)
        q[d] = c
        for i, b in enumerate(g):
            f[i + d] -= c * b
        while f and f[-1] == 0:
            f.pop()
    while q and q[-1] == 0:
        q.pop()
    return q, f


def bareiss_det(M):
    M = [row[:] for row in M]
    n = len(M)
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k]:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[-1][-1]


def resultant(f, g):
    m, n = len(f) - 1, len(g) - 1
    N = m + n
    M = [[0] * N for _ in range(N)]
    for i in range(n):
        for j, c in enumerate(reversed(f)):
            M[i][i + j] = c
    for i in range(m):
        for j, c in enumerate(reversed(g)):
            M[n + i][i + j] = c
    return bareiss_det(M)


PHI1 = [-2, 0, 1]                                   # Phi' = x^2 - 2


def dv1(a, e1=2, h=1):
    """dv1 of a coefficient poly (any deg), profile e1=2,h=1."""
    vals = [e1 * v2(c) + i * h for i, c in enumerate(a) if c]
    return min(vals) if vals else None


def phi_pins(f, phi, dvfun):
    """pins (j, dv(a_j)) of the phi-expansion of f."""
    pins = {}
    j = 0
    while any(f):
        f, r = pdivmod_monic(f, phi)
        d = dvfun(r)
        if d is not None:
            pins[j] = d
        j += 1
    return pins


def side_check(pins, ell, h0):
    """side = chord (0,h0)-(ell,0). Returns (one_sided, onside_set)."""
    if pins.get(ell) != 0 or pins.get(0) != h0:
        return False, set()
    onside = set()
    for j, m in pins.items():
        lhs, rhs = m * ell, h0 * (ell - j)     # m >= h0*(ell-j)/ell
        if lhs < rhs:
            return False, set()
        if lhs == rhs:
            onside.add(j)
    return True, onside


def dv2_W(a, u2=5, e1e2=4, e2h=2):
    """dv2 of a deg<=3 coefficient in basis {x^i Phi'^b}, W profile."""
    q, r = pdivmod_monic(list(a), PHI1)
    vals = [e1e2 * v2(c) + i * e2h for i, c in enumerate(r) if c]
    vals += [e1e2 * v2(c) + i * e2h + u2 for i, c in enumerate(q) if c]
    return min(vals) if vals else None


def dv2_N1(a):
    return dv2_W(a, u2=3, e1e2=2, e2h=1)


X = [0, 1]
PHI2 = padd(pmul(PHI1, PHI1), [0, -4])              # (x^2-2)^2 - 4x
PHI2B = padd(padd(pmul(PHI1, PHI1), pmul([0, -2], PHI1)), [-8])
PHI3A = padd(pmul(PHI2, PHI2), pmul([-16], PHI1))
PHI3B = padd(pmul(PHI2, PHI2), pmul([0, -16], PHI1))
PHI3C = padd(pmul(PHI2B, PHI2B), [0, -64])
PHI3D = padd(padd(pmul(PHI2, PHI2),
                  pmul(pmul([0, -2], PHI1), PHI2)), [0, -32])
PHI3T1 = padd(padd(pmul(PHI2, PHI2),
                   pmul(pmul([-2], PHI1), PHI2)), [0, -16])
PHI3T2 = padd(pmul(PHI2, PHI2), [0, -64])
W3 = padd(pmul(PHI3A, PHI3A), pmul([256], PHI2))
W4 = padd(pmul(PHI3A, PHI3A), pmul([512], PHI2))
W5 = padd(padd(pmul(PHI3A, PHI3A), pmul(pmul([0, 512], PHI3A), [1])),
          pmul(pmul([0, 2 ** 18], PHI1), PHI2))

# (name, poly, phi2, dv2fun, pins1-pred, ell, h0, onside1, pins2-pred,
#  ell2, h02, onside2, res-pred (x,Phi',phi2), sig, nfeltval-pred)
WITNESSES = [
    ('W1', PHI3A, PHI2, dv2_W, {0: 10, 2: 7, 4: 0}, 4, 10, {0, 4},
     {0: 21, 2: 0}, 2, 21, {0, 2}, (4, 10, 21), [(8, 1)], (4, 10, 21)),
    ('W2', PHI3B, PHI2, dv2_W, {0: 10, 1: 8, 2: 7, 4: 0}, 4, 10, {0, 4},
     {0: 23, 2: 0}, 2, 23, {0, 2}, (4, 10, 23), [(8, 1)], (4, 10, 23)),
    ('N1', PHI3C, PHI2B, dv2_N1, {0: 12, 1: 11, 2: 6, 3: 4, 4: 0}, 4, 12,
     {0, 2, 4}, {0: 13, 2: 0}, 2, 13, {0, 2}, (4, 12, 26), [(4, 2)],
     (2, 6, 13)),
    ('N2', PHI3D, PHI2, dv2_W, {0: 10, 1: 10, 2: 6, 3: 3, 4: 0}, 4, 10,
     {0, 4}, {0: 22, 1: 11, 2: 0}, 2, 22, {0, 1, 2}, (4, 10, 22),
     [(4, 2)], (2, 5, 11)),
]
LEAVES = [('W3', W3, (20, 42, 85), [(16, 1)], (8, 20, 42)),
          ('W4', W4, (20, 42, 93), [(16, 1)], (8, 20, 42)),
          ('W5', W5, (20, 42, 179), [(8, 1), (8, 1)], None)]


def polystr(f):
    return '+'.join('(%d)*x^%d' % (c, i)
                    for i, c in enumerate(f) if c) or '0'


GP_PROG = r"""
sig2(f) = {
  my(F = factorpadic(f, 2, 400), out = List());
  for (i = 1, matsize(F)[1],
    my(g = liftall(F[i,1]), nf = nfinit([g,[2]]),
       dec = idealprimedec(nf, 2));
    for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f])));
  vecsort(Vec(out))
}
trip(f, p1, p2) = {
  my(nf = nfinit([f,[2]]), dec = idealprimedec(nf, 2));
  if (#dec != 1, return ([-1]));
  my(pr = dec[1]);
  [nfeltval(nf, Mod(x, f), pr), nfeltval(nf, Mod(p1, f), pr),
   nfeltval(nf, Mod(p2, f), pr), pr.e, pr.f]
}
"""


def run_gp(jobs):
    lines = [GP_PROG]
    for i, (f, p2poly, wanttrip) in enumerate(jobs):
        ps = polystr(f)
        lines.append('print("S %d ", sig2(Pol(%s)))' % (i, ps))
        if wanttrip:
            lines.append('print("T %d ", trip(Pol(%s), Pol(%s), Pol(%s)))'
                         % (i, ps, polystr(PHI1), polystr(p2poly)))
    lines.append('quit')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines),
                         capture_output=True, text=True, timeout=1200)
    sig, trip = {}, {}
    for line in out.stdout.splitlines():
        if line.startswith('S '):
            k, rest = line[2:].split(' ', 1)
            sig[int(k)] = sorted(tuple(t) for t in json.loads(rest))
        elif line.startswith('T '):
            k, rest = line[2:].split(' ', 1)
            trip[int(k)] = json.loads(rest)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-300:])
    return sig, trip


def main():
    say('== GENTOW-2 battery (A-route exact + B-route PARI) ==')
    gp_jobs = []
    for (tag, f, p2, dvf, pp1, ell, h0, on1, pp2, ell2, h02, on2,
         res, sig, tripp) in WITNESSES:
        say('-- %s --' % tag)
        pins1 = phi_pins(list(f), PHI1, dv1)
        chk(pins1 == pp1, '%s Phi-pins %s != pred %s' % (tag, pins1, pp1))
        os1, J1 = side_check(pins1, ell, h0)
        chk(os1, '%s Phi\'-dev NOT one-sided' % tag)
        chk(J1 == on1, '%s on-side %s != pred %s (psi2-power support)'
            % (tag, sorted(J1), sorted(on1)))
        pins2 = phi_pins(list(f), p2, dvf)
        chk(pins2 == pp2, '%s Phi2-pins %s != pred %s' % (tag, pins2, pp2))
        os2, J2 = side_check(pins2, ell2, h02)
        chk(os2 and J2 == on2, '%s Phi2-dev side/support %s %s'
            % (tag, os2, sorted(J2)))
        rv = (v2(resultant(f, X)), v2(resultant(f, PHI1)),
              v2(resultant(f, p2)))
        chk(rv == res, '%s resultant v2 %s != pred %s' % (tag, rv, res))
        say('  A-route: pins/side/support/resultants OK (%s, %s, %s)'
            % (pins1, sorted(J1), rv))
        gp_jobs.append((f, p2, True))
    for tag, f, res, sig, tripp in LEAVES:
        say('-- %s (leaf) --' % tag)
        rv = (v2(resultant(f, PHI1)), v2(resultant(f, PHI2)),
              v2(resultant(f, PHI3A)))
        chk(rv == res, '%s resultant v2 %s != pred %s' % (tag, rv, res))
        say('  A-route resultants: %s' % (rv,))
        gp_jobs.append((f, PHI2, tripp is not None))
    # teeth (A-route tooth T1, B-route tooth T2)
    pinsT1 = phi_pins(list(PHI3T1), PHI1, dv1)
    osT1, _ = side_check(pinsT1, 4, pinsT1.get(0))
    TEETH['T1'] = not osT1
    say('-- TOOTH T1: pins %s -> one_sided=%s (must be False)'
        % (pinsT1, osT1))
    gp_jobs.append((PHI3T2, PHI2, False))
    say('== B-route (PARI/gp): %d jobs ==' % len(gp_jobs))
    sigs, trips = run_gp(gp_jobs)
    allw = WITNESSES + [(t, f, None, None, None, None, None, None, None,
                         None, None, None, None, s, tr)
                        for (t, f, _, s, tr) in LEAVES]
    for i, row in enumerate(allw):
        tag, sig, tripp = row[0], row[13], row[14]
        chk(sigs.get(i) == sorted(map(tuple, sig)),
            '%s PARI sig2 %s != pred %s' % (tag, sigs.get(i), sig))
        if tripp:
            got = trips.get(i, [-1])
            chk(tuple(got[:3]) == tuple(tripp),
                '%s nfeltval %s != pred %s' % (tag, got[:3], tripp))
            say('  %s PARI: sig %s, nfeltval(x,Phi\',Phi2)=%s (e,f)=%s'
                % (tag, sigs.get(i), got[:3], got[3:]))
        else:
            say('  %s PARI: sig %s' % (tag, sigs.get(i)))
    t2 = sigs.get(len(gp_jobs) - 1)
    TEETH['T2'] = (t2 == [(4, 1), (4, 1)])
    say('-- TOOTH T2: sig %s (must be [(4,1),(4,1)])' % t2)
    say('== VERDICT ==')
    say('checks: %d, violations: %d, teeth: %s'
        % (NCHK[0], len(VIOL), TEETH))
    green = not VIOL and all(TEETH.values())
    say('GENTOW2 battery: %s' % ('GREEN' if green else 'RED'))
    return 0 if green else 1


if __name__ == '__main__':
    sys.exit(main())
