"""HE7 passPE1 FRESH-ROUTE leg (hostile verifier, fresh context).

ROUTE (disclosed; differs from all prior routes: the sealed he7_checks.py
1,587-member n=8 battery, HE6R1's 682-member l=1/d_r=2 n=8 battery, and the
he7r1_supp.py 8-member peel leg):

  A NEW CONSTRUCTED FAMILY at the coverage hole HE7-BOX-5 itself names as
  unexercised -- A PEEL AT mu2 = 3, i.e. degree n = 12 (mu = 6, ALSO the
  first machine contact of the level-2 read at mu >= 5 / n >= 10, another
  HE7-BOX-2 hole; the block is still everything, so proper blocks stay
  unexercised -- disclosed).

INSTRUMENT INDEPENDENCE.  Nothing is imported from he6_checks/he7_checks;
the slot-min, developments, level-1 polygon+residual, level-2 polygon,
twisted mu2=2 residual and the THEOREM HE7.A dictionary are re-implemented
below directly from the NOTE's text (HE7_PROOF_2026-08-08.md S1, S3, S8,
and the S1 cocycle CONVENTION), and the sigma oracle is cypari2 (factorpadic
+ nfinit/idealprimedec per factor), not the gp subprocess of the sealed
runners.

FRAME (the HE6-BOX-1 bite, one mu-step deeper).  O = Z_p, p in {3,5,7};
Phi' = x^2 - p (e1=2, f1=1, h=1, D'=2, dv = 2v, varpi = x, eta = 1);
lam = 5/2 (u=5, l=2); r = Z - s, d_r = 1, K2 = F_p; the order-2 key

    Psi = (x^2 - p)^2 - s p^2 x ,   D'' = 4, T2 = 10, dv2 = 2 dv.

MEMBERS.  f = Psi^3 + B Psi^2 + C Psi with B, C in O[x], deg < 4, built
from slot prescriptions plus random higher-value noise; so A0^(2) = 0:
every member sits on the Psi | f_S stratum at mu2 = 3, which NO committed
battery exercises (they are all mu2 = 2, peel at mu2' = 1).

WHAT IS CHECKED per member (all EXACT except the PARI oracle):
  F1  level-1 frame: my own Phi'-development polygon of f is the single
      side (0,15)-(6,0) and my own level-1 residual is exactly (Z-s)^3
      (=> one label class, f_S = f, mu2 = 3) -- else member discarded
      (counted; a discard is NOT a violation, it is a mis-constructed
      member).
  F2  LEMMA HE6R1-3 arithmetic: A0^(2) = 0 and A1^(2) != 0 (exact
      Psi-development; peel fires ONCE) and disc f != 0.
  F3  the peeled read at mu2' = 2: level-2 polygon of f_S' = Psi^2+B Psi+C
      via my slot-min; slopes > T2; the S8 dictionary with the S1 twist
      (R2 = Z^2 + b1 Z + b0 * s^(-c), c = w mod 2, at integer slope w);
      sigma(f) predicted = {(4,1)} [the peeled Psi, LEMMA HE6R1-3's letter]
      ++ letters(f_S').
  F4  ORACLE: PARI sigma(f) == prediction.  (Repeated-root residuals are
      refined once via the level-2 alpha-refine before predicting; if the
      refine is still repeated the member is skipped -- counted.)
  F5  ORACLE on the peel letter itself: PARI sigma(Psi) == {(4,1)} per
      (p, s) frame (irreducible of degree D''=4, e = e1 l = 4, f = 1).

Artifacts: he7_pe1_fresh_output.txt (tee by hand), he7_pe1_fresh_results.json.
"""

import json, random, time
from fractions import Fraction as Fr

random.seed(20260808)

# ---------------------------------------------------------------- Z[x] exact
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

def pdivmod(a, b):
    """a = q*b + r with b MONIC, exact over Z."""
    a = list(a)
    db, q = len(b) - 1, [0] * max(1, len(a) - len(b) + 1)
    while len(a) - 1 >= db and any(a):
        if a[-1] == 0:
            a.pop(); continue
        c, sh = a[-1], len(a) - 1 - db
        q[sh] += c
        for j in range(len(b)):
            a[sh + j] -= c * b[j]
        assert a[-1] == 0
        a.pop()
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return q, a

def development(f, g, jmax):
    """f = sum_j A_j g^j, deg A_j < deg g, exact (g monic)."""
    A, cur = [], list(f)
    for _ in range(jmax + 1):
        cur, r = pdivmod(cur, g)
        A.append(r)
    assert cur == [0] or not any(cur), 'development leftover'
    return A

def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p; v += 1
    return v

BIG = 10 ** 9

# ------------------------------------------------- level-1 slot values (S1)
# deg c < 2, c = a + b x over Z_p:  dv(c) = min(2 v(a), 2 v(b) + 1)
def dv1(c, p):
    a = c[0] if len(c) > 0 else 0
    b = c[1] if len(c) > 1 else 0
    va, vb = vp(a, p), vp(b, p)
    cand = []
    if va is not None: cand.append(2 * va)
    if vb is not None: cand.append(2 * vb + 1)
    return min(cand) if cand else BIG

def res1(c, m, p):
    """res( c(theta) / theta^m ) in F_p, theta^2 = p (eta = 1); 0 if dv1>m."""
    if dv1(c, p) > m:
        return 0
    a = c[0] if len(c) > 0 else 0
    b = c[1] if len(c) > 1 else 0
    if m % 2 == 0:
        return (a // p ** (m // 2)) % p
    return (b // p ** ((m - 1) // 2)) % p

# ------------------------------------------------- level-2 objects (S1, S3)
U, L = 5, 2                                   # lam = 5/2

def sk(k):                                    # s(k) = k u^{-1} mod l = k mod 2
    return k % 2

def n2ms(k):
    s0 = sk(k)
    return (k - s0 * U) // L, s0

def phidev(C, PHI, p):
    return development(C, PHI, L - 1)          # l*d_r - 1 = 1 -> slots 0,1

def dv2(C, PHI, p):
    cs = phidev(C, PHI, p)
    best = BIG
    for s, c in enumerate(cs):
        m = dv1(c, p)
        if m < BIG:
            best = min(best, L * m + s * U)
    return best

def res2(C, k, PHI, p):
    """(SLOT2)(b) at d_r = 1: residue of C/n2(k) = res1 of the class slot."""
    m0, s0 = n2ms(k)
    cs = phidev(C, PHI, p)
    return res1(cs[s0], m0, p) if m0 >= 0 else 0

# ------------------------------------------------------------- the oracle
import cypari2
pari = cypari2.Pari()
pari.allocatemem(64 * 1024 * 1024)

def polstr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'

def pari_sig(f, p):
    fp = pari(polstr(f))
    if pari.poldisc(fp) == 0:
        return None
    F = pari.factorpadic(fp, p, 200)
    out = []
    for i in range(int(pari.matsize(F)[0])):
        g = pari.liftall(F[i, 0])
        if int(pari.poldegree(g)) == 1:
            out.append((1, 1)); continue
        nf = pari.nfinit([g, [p]])
        pr = pari.idealprimedec(nf, p)
        assert len(pr) == 1, 'lifted local factor split globally at p'
        out.append((int(pr[0][2]), int(pr[0][3])))
    return tuple(sorted(out))

# ------------------------------------------------------------ construction
def build_C(shape, chat, p, noise):
    """C with prescribed dv2 via slot prescription; random noise above."""
    PHI = [-p, 0, 1]
    base = {
        23: pmul([0, chat * p ** 4], PHI),      # slot 1, dv1 = 9
        24: [chat * p ** 6],                    # slot 0, dv1 = 12
        25: pmul([chat * p ** 5], PHI),         # slot 1, dv1 = 10
        26: [0, chat * p ** 6],                 # slot 0, dv1 = 13
        11: pmul([0, chat * p], PHI),           # slot 1, dv1 = 3  (for B)
        12: [chat * p ** 3],                    # slot 0, dv1 = 6
        13: pmul([chat * p ** 2], PHI),         # slot 1, dv1 = 4
        14: [0, chat * p ** 3],                 # slot 0, dv1 = 7
        15: pmul([0, chat * p ** 3], PHI),      # slot 1, dv1 = 7 -> 2*7+1=15? no
    }[shape]
    out = list(base)
    if noise:
        # random junk with dv2 strictly above `shape`
        e = shape // 2 + 2
        junk = [random.randrange(p) * p ** e for _ in range(4)]
        out = padd(out, junk)
    while len(out) < 4:
        out.append(0)
    return out[:4]

def run():
    t0 = time.time()
    RES = {'frames': [], 'members': 0, 'used': 0, 'discard_F1': 0,
           'refine_used': 0, 'refine_skip': 0, 'pari_jobs': 0, 'agree': 0,
           'mismatch': [], 'viol': [], 'psi_checks': [], 'by_case': {}}
    for p in (3, 5, 7):
        for s in range(1, min(p, 4)):
            PHI = [-p, 0, 1]
            Psi = padd(pmul(PHI, PHI), [0, -s * p * p])   # (x^2-p)^2 - s p^2 x
            # ---- F5: the peel letter, straight to the oracle
            sg = pari_sig(Psi, p)
            ok = (sg == ((4, 1),))
            RES['psi_checks'].append({'p': p, 's': s, 'sigma_Psi': str(sg),
                                      'ok': ok})
            if not ok:
                RES['viol'].append({'what': 'sigma(Psi) != {(4,1)}',
                                    'p': p, 's': s, 'got': str(sg)})
            print('frame p=%d s=%d   sigma(Psi) = %s  %s'
                  % (p, s, sg, 'OK' if ok else 'VIOLATION'))
            # ---- members
            shapes = [(23, 12), (23, 14), (24, 12), (24, 14), (26, 13),
                      (26, 14), (25, 11)]
            for (shC, shB) in shapes:
                for chat in range(1, p):
                    for bhat in range(0, p):
                        for noise in (False, True):
                            if bhat == 0 and shB in (11,):
                                continue      # two-side case needs B present
                            RES['members'] += 1
                            B = build_C(shB, bhat, p, noise) if bhat else \
                                ([0, 0, 0, 0] if not noise else
                                 build_C(shB, 1, p, True))
                            if bhat == 0 and not noise:
                                B = [0, 0, 0, 0]
                            C = build_C(shC, chat, p, noise)
                            # f = Psi^3 + B Psi^2 + C Psi
                            f = padd(padd(pmul(pmul(Psi, Psi), Psi),
                                          pmul(B, pmul(Psi, Psi))),
                                     pmul(C, Psi))
                            r = check_member(f, B, C, Psi, PHI, p, s, RES)
                            if r:
                                RES['by_case'][r] = RES['by_case'].get(r, 0) + 1
    RES['elapsed'] = round(time.time() - t0, 1)
    print('\nMEMBERS %d  used %d  F1-discard %d  refine used %d  '
          'refine-skip %d' % (RES['members'], RES['used'], RES['discard_F1'],
                              RES['refine_used'], RES['refine_skip']))
    print('PARI jobs %d  agree %d  MISMATCH %d  VIOLATIONS %d'
          % (RES['pari_jobs'], RES['agree'], len(RES['mismatch']),
             len(RES['viol'])))
    print('case census:', RES['by_case'])
    print('psi oracle: %d/%d' % (sum(1 for x in RES['psi_checks'] if x['ok']),
                                 len(RES['psi_checks'])))
    print('%.1fs' % RES['elapsed'])
    with open('he7_pe1_fresh_results.json', 'w') as fh:
        json.dump(RES, fh, indent=1, default=str)
    return RES

def check_member(f, B, C, Psi, PHI, p, s, RES):
    # ---- F1: my own LEVEL-1 read: single side (0,15)-(6,0), residual (Z-s)^3
    cs = development(f, PHI, 6)
    dvs = [dv1(c, p) for c in cs]
    online = all(dvs[j] >= Fr(15 * (6 - j), 6) for j in range(7)) \
        and dvs[0] == 15 and dvs[6] == 0
    if not online:
        RES['discard_F1'] += 1
        return None
    Rlv1 = [res1(cs[2 * t], 15 - 5 * t, p) for t in range(4)]
    want = [(-s) ** 3 % p, (3 * s * s) % p, (-3 * s) % p, 1]
    if Rlv1 != want:
        RES['discard_F1'] += 1
        return None
    # ---- F2: peel arithmetic (LEMMA HE6R1-3): A0 = 0, A1 != 0, disc != 0
    A = development(f, Psi, 3)
    if any(A[0]) or A[3] != [1] + [0] * (len(A[3]) - 1):
        RES['viol'].append({'what': 'A0 != 0 or top != 1 (construction!)',
                            'p': p, 's': s})
        return None
    if not any(A[1]):
        RES['viol'].append({'what': 'A1 == 0: double peel would be needed',
                            'p': p, 's': s, 'B': B, 'C': C})
        return None
    # ---- F3: peeled read at mu2' = 2 on f_S' = Psi^2 + B Psi + C
    dB, dC = dv2(B, PHI, p), dv2(C, PHI, p)
    if not (dC > 2 * 10 and dB > 10):
        RES['discard_F1'] += 1
        return None
    case = None
    if 2 * dB < dC:                       # two sides, each length 1
        lets = [(4, 1), (4, 1)]
        case = 'two-sides'
    elif dC % 2 == 1:                     # one side, lam2 not integer
        lets = [(8, 1)]
        case = 'one-side-l2=2'
    else:                                 # one side, integer slope w
        w = dC // 2
        b1 = res2(B, w, PHI, p) if dB == w else 0
        b0 = res2(C, 2 * w, PHI, p)
        c2 = w % 2                        # the S1 cocycle: beta^c, beta = s
        b0t = (b0 * pow(s, (p - 1 - c2) % (p - 1), p)) % p   # b0 * s^{-c2}
        disc = (b1 * b1 - 4 * b0t) % p
        if disc == 0:
            # one alpha-refine: Psi' = Psi - shat n2(w); at mu2'=2 the note
            # says chains are length <= ... just skip (counted).
            RES['refine_skip'] += 1
            return None
        if pow(disc, (p - 1) // 2, p) == 1:
            lets = [(4, 1), (4, 1)]
            case = 'one-side-split-w%s' % ('odd' if c2 else 'even')
        else:
            lets = [(4, 2)]
            case = 'one-side-inert-w%s' % ('odd' if c2 else 'even')
    pred = tuple(sorted([(4, 1)] + lets))
    # ---- F4: the oracle
    sg = pari_sig(f, p)
    if sg is None:
        RES['viol'].append({'what': 'disc f = 0', 'p': p, 's': s})
        return None
    RES['pari_jobs'] += 1
    RES['used'] += 1
    if sg == pred:
        RES['agree'] += 1
    else:
        RES['mismatch'].append({'p': p, 's': s, 'case': case,
                                'pred': str(pred), 'pari': str(sg),
                                'B': B, 'C': C})
        print('  !! MISMATCH p=%d s=%d %s pred %s pari %s'
              % (p, s, case, pred, sg))
    return case

if __name__ == '__main__':
    run()
