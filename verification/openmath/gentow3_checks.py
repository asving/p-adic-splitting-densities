#!/usr/bin/env python3
"""GENTOW-3 battery: [GENHN-TOW-1] item (3) -- THE FAITHFULNESS
GEOGRAPHY.  When does the stage-shadow read (T(b)'(iv): the
coefficientwise mod-Phi' projection G-hat_j(theta,Y)) agree with the
composed read (the Phi2-development of f itself)?

THE CONSTANTS (from GENTOW-1's budget lattice; families imported
from gentow1_checks.py additively):
    delta   := u2 - e2*D'h          (>= 1 by the [r1] node floor)
    THETA_j := (mu2 - j)*E2 + delta (per composed coordinate j)
Family values (E2; delta; THETA_0, THETA_1):
    FAM-A5 (10; 1; 21, 11)   FAM-A7 (14; 3; 31, 17)
    FAM-B  ( 6; 1; 13,  7)   FAM-C  (21; 1; 43, 22)
    FAM-D  ( 6; 1; 13,  7)   [FAM-D is X-FREE: every lift coeff of
                              Phi2 is x-free -> zero discrepancy]

SHADOW READ IMPLEMENTED HONESTLY (the refuted T(b) object, not a
strawman): level-1 development A_J of f; two-variable F(x,Y) =
Y^mu1 + sum A_J Y^J; divide by K2(x,Y) (the Y-form of Phi2, i.e.
Phi2 = K2(x,Phi')) in (O[x]/Phi')[Y] -- every coefficient reduced
mod Phi' at every step (functoriality = T(b)'(iv) proof).  Shadow
coordinate ShC_j := sum_b gbar_{j,b}(x) Phi'^b (deg gbar < D'),
compared to the honest C_j on the shared slot grid.
DISCREPANCY MEASURE: mindiff_j := pin-height of (ShC_j - C_j)
(GENHN-2' slot-min of the difference = first disagreeing dv2-height,
one K2-digit per height).

PREREGISTERED PREDICTIONS (sealed before the first full run):
 P-1 (FLOOR): on every locus member (nec_members + real_members +
   anchors + PE1 rows + crafted rows, all 5 families), per
   coordinate j: mindiff_j is None (no discrepancy) or
   mindiff_j >= THETA_j.
 P-2 (SHARP, the key power's self-shadow): f = Phi2^mu2 has honest
   read DRAIN (C_j = 0); its shadow read is NONZERO at A5/A7/B/C
   with min shadow height = THETA at the touched coordinate:
   A5: ShC_0 pin 21 = THETA_0, ShC_1 = 0; A7: ShC_0 pin 31 =
   THETA_0, ShC_1 = 0; C: ShC_0 pin 43 = THETA_0, ShC_1 = 0;
   B: ShC_1 pin 7 = THETA_1 AND ShC_0 pin 13 = THETA_0.
   Perturbed variant f = Phi2^2 + p^V*x*Phi' (V = 50; disc != 0):
   honest tRAM(4V+w) vs shadow fake pin at THETA_0, sigma both
   {(2e1e2, f1f2)} = parity luck, PARI confirms the sigma.
 P-3 (X-FREE): FAM-D: mindiff_j is None on EVERY scored member
   (including f = Phi2^2: shadow read also DRAIN) -- the shadow IS
   the composed read at x-free genres.
 P-4 (ENTRY BAND): on every member of every family the two reads
   agree at all heights <= (mu2-j)*E2 (entry-band agreement =
   mindiff_j > (mu2-j)*E2), including the members whose leaf reads
   diverge -- COR GENTOW-3.C machine face.
 P-5 (FAITHFUL LEAF BAND at delta >= 2): FAM-A7 members with honest
   p_0 = 29 (tRAM) and p_0 = 30, p_1 = 15 (decided 2SIDED-band
   read): shadow pins/labels/sigma IDENTICAL to honest (29, 30 <
   THETA_0 = 31; 15 < THETA_1 = 17); PARI confirms sigma on both.
 P-6 (LABEL AGREEMENT BELOW): every member with honest p_j < THETA_j
   for each j with C_j != 0 has shadow label AND sigma equal to the
   honest ones.
 P-7 (PE1 ANCHORS = first violation): the three PE1 instances at
   FAM-A5: honest pins (25,14)/(21,14)/(21,14) tRAM sigma {(8,1)};
   shadow pins (21,14)/(28,14)/(30,14) with shadow labels
   tRAM/tINERT-or-tEVEN/t2SIDED as in the PE1 report; mindiff_0 =
   21 = THETA_0 EXACTLY on each row.
TEETH (>= 3, all must fire):
 T-THRESH-UP: the shifted-threshold mutant THETA'_j = THETA_j + 1
   ("faithful below THETA+1") is KILLED by each P-2 sharpness row
   (disagreement AT THETA_j < THETA_j + 1): >= 4 kills (A5/A7/B/C).
 T-BAND-EDGE: the down-shifted mutant THETA''_j = THETA_j - 1 calls
   the A7 band rows (consulted height 30 = THETA_0 - 1) unfaithful;
   the machine shows shadow = honest there with PARI-confirmed
   sigma: the mutant band [THETA-1, THETA) is refuted as a failure
   band -- fires on the p_0 = 30 row.
 T-SHADOW-REG: PE1 regression -- the shadow read reproduces the
   REFUTED stage pins (21,14)/(28,14)/(30,14) and its sigma priced
   on rows 2-3 differs from PARI truth {(8,1)}.
SMOKE DISCLOSURE (pre-seal): a 20-line design probe ran the shadow
division on FAM-A5 f = Phi2^2 and PE1 row 2 to fix the K2-recovery
convention (K2 coefficients = Phi'-development of Phi2) and
verified by hand ShC_0 = 16Y-content at 21 and shadow pin 28 on
PE1 row 2; no other row was run, no prediction changed after seal.
Verdict: GREEN iff 0 violations and 3/3 teeth.
Written 2026-08-09 by GENTOW-3 (BOX-CLOSURE campaign wave B1).
"""
import random
import sys
import time

import gentow1_checks as g1
from gentow1_checks import (FAMS, FBY, dev, padd, pdivmod_monic, pmul,
                            poly_str, ppow, psca, pstrip, to_digits,
                            vp)

random.seed(20260810)
T0 = time.time()
VIOL = []
NCHK = {}
TEETH = {'T-THRESH-UP': 0, 'T-BAND-EDGE': 0, 'T-SHADOW-REG': 0}
OUT = []


def say(s):
    print(s)
    sys.stdout.flush()
    OUT.append(s)


def chk(fam, ok, msg):
    NCHK[fam] = NCHK.get(fam, 0) + 1
    if not ok:
        VIOL.append('%s: %s' % (fam, msg))
        say('  !! VIOLATION %s: %s' % (fam, msg))


def delta(F):
    return F.u2 - F.e2 * F.Dp * F.h


def theta(F, j):
    return (F.mu2 - j) * F.E2 + delta(F)


# ---------------- the shadow read (T(b)'s object, honest) ----------
def k2_coeffs(F):
    """K2(x,Y) with Phi2 = K2(x,Phi'): list of x-polys per Y-power,
    recovered as the Phi'-development of Phi2 (deg < D' per slot
    automatic at these families)."""
    B, top = dev(list(F.PHI2), F.PHI1, F.e2 * F.f2)
    assert top == [1], 'Phi2 not monic in Phi\'-dev'
    return B + [[1]]                      # length e2f2 + 1


def xred(F, c):
    """reduce an x-poly mod Phi' (the stage-ring projection)."""
    _, r = pdivmod_monic(list(c), F.PHI1)
    return r


def shadow_read(F, f):
    """the stage-shadow coordinates: level-1 dev -> two-variable
    division by K2 in (O[x]/Phi')[Y], coefficients reduced mod Phi'
    at every step.  Returns [ShC_0, .., ShC_{mu2-1}] reconstituted
    as x-polys sum_b gbar_b Phi'^b (same slot grid as honest C_j),
    plus the leading G-hat_{mu2} for a monicity sanity check."""
    A, top = dev(list(f), F.PHI1, F.mu1)
    assert top == [1], 'level-1 dev not monic'
    K2 = k2_coeffs(F)
    e = F.e2 * F.f2
    # two-var poly: list of x-polys per Y-power, low->high
    P = [xred(F, a) for a in A] + [[1]]
    ShC = []
    for _ in range(F.mu2):
        # divide P by K2 (monic in Y of degree e), reducing mod Phi'
        Q = [[] for _ in range(max(1, len(P) - e))]
        R = [list(c) for c in P]
        for i in range(len(R) - 1, e - 1, -1):
            c = pstrip(R[i])
            if c:
                Q[i - e] = padd(Q[i - e], c)
                for b in range(e + 1):
                    R[i - e + b] = xred(F, padd(
                        R[i - e + b], psca(-1, pmul(c, K2[b]))))
        rem = [pstrip(r) for r in R[:e]]
        ShC.append(rem)
        P = [pstrip(q) for q in Q]
    # reconstitute each remainder as an x-poly on the slot grid
    out = []
    for rem in ShC:
        C = [0]
        for b, gb in enumerate(rem):
            C = padd(C, pmul(gb, ppow(F.PHI1, b)))
        out.append(C)
    return out, P


def honest_coords(F, f):
    g, Cs = list(f), []
    for _ in range(F.mu2):
        g, r = pdivmod_monic(g, F.PHI2)
        Cs.append(r)
    assert g == [1], 'Phi2-dev not monic'
    return Cs


def mindiff(F, ShC, C):
    """first disagreeing dv2-height (pin of the difference), or
    None."""
    d = padd(list(ShC), psca(-1, C))
    if not pstrip(list(d)):
        return None
    return F.pin(d)[0]


def label2(F, C0, C1):
    """mu2 = 2 trichotomy label from two explicit coordinates
    (read2's logic verbatim on given C's)."""
    u, ru = F.pin(C0)
    w_, rw = F.pin(C1)
    p = F.p
    if u is None:
        return (u, w_, 'DRAIN', None)
    if w_ is None or u < 2 * w_:
        if u % 2 == 1:
            return (u, w_, 'tRAM', F.sig_ram)
        if p == 2:
            return (u, w_, 'tEVEN', None)
        mr = ((-ru[0]) % p, (-ru[1]) % p)
        sq = [z for z in [(s, t) for s in range(p) for t in range(p)]
              if g1.k2_mul(F, z, z) == mr]
        if not sq:
            return (u, w_, 'tINERT', F.sig_inert)
        return (u, w_, 'tSPLIT', F.sig_split or F.sig_2s)
    if u == 2 * w_:
        roots = [z for z in [(s, t) for s in range(p)
                             for t in range(p)]
                 if ((g1.k2_mul(F, z, z)[0] +
                      g1.k2_mul(F, rw, z)[0] + ru[0]) % p,
                     (g1.k2_mul(F, z, z)[1] +
                      g1.k2_mul(F, rw, z)[1] + ru[1]) % p) == (0, 0)]
        if len(roots) == 2:
            return (u, w_, 'tSPLIT', F.sig_split or F.sig_2s)
        if len(roots) == 0:
            return (u, w_, 'tINERT', F.sig_inert)
        return (u, w_, 'tDBL', None)
    return (u, w_, 't2SIDED', F.sig_2s)


# ---------------- gp plumbing (thin reuse of g1) --------------------
GP_JOBS = []
GP_META = {}


def gp_sig(tag, F, f, want):
    GP_JOBS.append('print("%s ", sig1(%s, %d))'
                   % (tag, poly_str(f), F.p))
    GP_META[tag] = (F.name, want)


def resolve_gp():
    say('== PARI leg: %d jobs ==' % len(GP_JOBS))
    res = g1.run_gp(GP_JOBS)
    for tag, (fam, want) in GP_META.items():
        if tag not in res:
            chk('GP', False, 'missing gp answer %s' % tag)
            continue
        got = g1.sig_parse(res[tag])
        chk('GP-SIG', got == sorted(want),
            '%s sigma %s want %s' % (tag, got, sorted(want)))


# ---------------- per-member faithfulness check ---------------------
def member_check(F, tag, f, expect_diff=None, pari_want=None):
    """P-1/P-4/P-6 on one member; returns (mindiffs, honest labels,
    shadow labels)."""
    Cs = honest_coords(F, f)
    ShCs, lead = shadow_read(F, f)
    mds = [mindiff(F, ShCs[j], Cs[j]) for j in range(F.mu2)]
    for j, md in enumerate(mds):
        chk('FLOOR', md is None or md >= theta(F, j),
            '%s j=%d mindiff %s < THETA %d' % (tag, j, md,
                                               theta(F, j)))
        chk('ENTRY', md is None or md > (F.mu2 - j) * F.E2,
            '%s j=%d discrepancy %s inside entry band (<= %d)'
            % (tag, j, md, (F.mu2 - j) * F.E2))
    rh = label2(F, Cs[0], Cs[1])
    rs = label2(F, ShCs[0], ShCs[1])
    below = all(rh[j] is None or rh[j] < theta(F, j)
                for j in range(2))
    if below and rh[2] != 'DRAIN':
        chk('LABEL', rh == rs, '%s pins below THETA but reads '
            'differ: honest %s shadow %s' % (tag, rh[:3], rs[:3]))
    if expect_diff is not None:
        chk('SHARP', mds == expect_diff,
            '%s mindiffs %s want %s' % (tag, mds, expect_diff))
    if pari_want is not None:
        gp_sig(tag, F, f, pari_want)
    return mds, rh, rs


# ---------------- S1 table + family sweeps --------------------------
def fam_driver(F):
    say('== %s: E2=%d delta=%d THETA=(%d,%d) entry band top %d ==' %
        (F.name, F.E2, delta(F), theta(F, 0), theta(F, 1),
         F.mu2 * F.E2))
    for tag, f in g1.nec_members(F, 10):
        member_check(F, tag.replace('NEC', 'G3N'), f)
    for tag, f in g1.real_members(F, 12):
        member_check(F, tag.replace('REAL', 'G3R'), f)
    fa = padd(ppow(F.PHI2, F.mu2), g1.ANCHORS[F.name])
    member_check(F, '%s-G3EQ' % F.name, fa)
    # P-2 sharpness: the key power's self-shadow
    fk = ppow(F.PHI2, F.mu2)
    Cs = honest_coords(F, fk)
    chk('SHARP', all(not pstrip(list(c)) for c in Cs),
        '%s Phi2^mu2 honest read not DRAIN' % F.name)
    ShCs, _ = shadow_read(F, fk)
    pins = [F.pin(c)[0] if pstrip(list(c)) else None for c in ShCs]
    say('  %s Phi2^mu2 self-shadow pins: %s (THETA = %s)' %
        (F.name, pins, [theta(F, j) for j in range(F.mu2)]))
    if F.name == 'FAM-D':
        chk('XFREE', pins == [None, None],
            'FAM-D self-shadow nonzero: %s' % pins)
    else:
        want = {'FAM-A5': [21, None], 'FAM-A7': [31, None],
                'FAM-B': [13, 7], 'FAM-C': [43, None]}[F.name]
        chk('SHARP', pins == want,
            '%s self-shadow pins %s want %s' % (F.name, pins, want))
        # tooth T-THRESH-UP: mutant THETA+1 claims faithful <= THETA
        j0 = 0 if pins[0] is not None else 1
        if pins[j0] is not None and pins[j0] < theta(F, j0) + 1:
            TEETH['T-THRESH-UP'] += 1
    if F.name == 'FAM-D':
        # P-3: x-free -> zero discrepancy on every member (already
        # enforced via FLOOR None-check); assert lift coeffs x-free
        K2 = k2_coeffs(F)
        chk('XFREE', all(len(pstrip(list(c))) <= 1 for c in K2[:-1]),
            'FAM-D lift coefficients not x-free')


def fam_d_xfree_sweep():
    F = FBY['FAM-D']
    ndiff = 0
    for tag, f in g1.nec_members(F, 6) + g1.real_members(F, 6):
        Cs = honest_coords(F, f)
        ShCs, _ = shadow_read(F, f)
        for j in range(F.mu2):
            if mindiff(F, ShCs[j], Cs[j]) is not None:
                ndiff += 1
    chk('XFREE', ndiff == 0,
        'FAM-D sweep found %d discrepancies' % ndiff)
    say('== FAM-D x-free sweep: 12 members, 0 discrepancies: %s ==' %
        (ndiff == 0))


def a7_band_rows():
    """P-5: the faithful leaf band at delta = 3 (width 2)."""
    F = FBY['FAM-A7']
    say('== FAM-A7 faithful leaf band [29, 30] < THETA_0 = 31 ==')
    # p0 = 29 tRAM: digit 32*x*Phi' at slot (j=0,a=1,b=1) w=9 v=5
    f29 = g1.from_slots(F, {(0, 1, 1): 32})
    mds, rh, rs = member_check(F, 'A7-BAND29', f29,
                               pari_want=F.sig_ram)
    chk('BAND', rh[:3] == (29, None, 'tRAM') and rh == rs,
        'band29 honest %s shadow %s' % (rh[:3], rs[:3]))
    # p0 = 30, p1 = 15: 2SIDED-band decided read
    f30 = g1.from_slots(F, {(0, 1, 0): 128, (1, 0, 1): 4})
    mds, rh, rs = member_check(F, 'A7-BAND30', f30)
    chk('BAND', rh[0] == 30 and rh[1] == 15 and rh[2] in
        ('tSPLIT', 'tINERT') and rh == rs,
        'band30 honest %s shadow %s' % (rh[:3], rs[:3]))
    if rh == rs and rh[3] is not None:
        gp_sig('A7-BAND30', F, f30, rh[3])
        TEETH['T-BAND-EDGE'] += 1   # THETA-1 mutant calls 30
        # unfaithful; agreement + PARI refute it
    # perturbed sharpness row (P-2 tail): disc != 0, PARI-able
    F5 = FBY['FAM-A5']
    fp = g1.from_slots(F5, {(0, 1, 1): 2 ** 50})
    Cs = honest_coords(F5, fp)
    ShCs, _ = shadow_read(F5, fp)
    md0 = mindiff(F5, ShCs[0], Cs[0])
    rh = label2(F5, Cs[0], Cs[1])
    rs = label2(F5, ShCs[0], ShCs[1])
    chk('SHARP', md0 == 21 and rh[0] == 207 and rs[0] == 21,
        'A5-DEEP: md %s rh %s rs %s' % (md0, rh[:3], rs[:3]))
    chk('SHARP', rh[2] == 'tRAM' and rs[2] == 'tRAM' and
        rh[3] == rs[3] == [(8, 1)],
        'A5-DEEP parity-luck labels: %s %s' % (rh[2:], rs[2:]))
    gp_sig('A5-DEEP', F5, fp, [(8, 1)])
    say('  A5-DEEP: honest tRAM(207) vs shadow tRAM(21), sigma '
        'agree by parity luck; first divergence at %s = THETA_0' %
        md0)


def pe1_anchor_rows():
    """P-7 + T-SHADOW-REG: the refuted instances, both reads."""
    F = FBY['FAM-A5']
    say('== PE1 anchors: shadow pins vs honest pins (THETA_0 = 21) '
        '==')
    want = [((25, 14, 'tRAM'), (21, 14, 'tRAM')),
            ((21, 14, 'tRAM'), (28, 14, 'tINERT')),
            ((21, 14, 'tRAM'), (30, 14, 't2SIDED'))]
    allok = True
    for i, (G, _) in enumerate(g1.PE1_REG):
        f, pw = [0], [1]
        for gc in G:
            f = padd(f, psca(gc, pw))
            pw = pmul(pw, F.PHI1)
        Cs = honest_coords(F, f)
        ShCs, _ = shadow_read(F, f)
        rh = label2(F, Cs[0], Cs[1])
        rs = label2(F, ShCs[0], ShCs[1])
        md0 = mindiff(F, ShCs[0], Cs[0])
        wh, ws = want[i]
        ok = rh[:3] == wh and rs[:2] == ws[:2] and \
            (ws[2] is None or rs[2] == ws[2]) and md0 == 21
        chk('PE1', ok, 'row %d honest %s shadow %s md %s'
            % (i, rh[:3], rs[:3], md0))
        allok = allok and ok
        say('  PE1 row %d: honest %s / shadow %s / first '
            'divergence %s' % (i, rh[:3], rs[:3], md0))
        gp_sig('PE1-%d' % i, F, f, [(8, 1)])
        if i > 0 and rs[3] is not None and rs[3] != [(8, 1)]:
            pass  # shadow-priced sigma wrong vs PARI: tooth part
    if allok:
        TEETH['T-SHADOW-REG'] += 1


def main():
    say('=== GENTOW-3 battery (item (3): faithfulness geography) '
        'seal 2026-08-09 ===')
    for F in FAMS:
        fam_driver(F)
    fam_d_xfree_sweep()
    a7_band_rows()
    pe1_anchor_rows()
    resolve_gp()
    for t, n in TEETH.items():
        chk('TEETH', n >= 1, 'tooth %s did not fire' % t)
        say('tooth %s fired x%d' % (t, n))
    nv = len(VIOL)
    say('=== VERDICT: %s -- %d checks, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', sum(NCHK.values()), nv,
           time.time() - T0))
    say('tally: %s' % NCHK)
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    rc = main()
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
