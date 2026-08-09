#!/usr/bin/env python3
"""GENTOW-6 battery: the box-residue unit (GENTOW6_PROOF_2026-08-09).

Three legs, importing the sealed B1/B2 batteries additively (no
edit): gentow1_checks (families A5/A7/B/C/D + slot algebra),
gentow3_checks (the shadow read), gentow4_checks (partial-side
families + composed_read + gp bridge).

LEG-1 (TIE, LEMMA GENTOW-6.1): on FAM-P5's geography (side [0,6]
slope 5/2 over Q3, residual degree 3, roots in {1,2}), constructed
product members realize residual multiplicity profiles (m_{T-1},
m_{T-2}) in {(1,2),(2,1),(0,3),(3,0)}; the tie mu2*(r) = m_r is
MEASURED per class (level-1 res_factor vs composed_read at the
class key), and PARI nodev6 class-degree sums give the decorrelated
deg f_S = D2*m_r leg.

LEG-2 (BLOCK, LEMMA GENTOW-6.2 + COR 6.2C): on non-perturbed product
rows the block factor f_S is known exactly; check its one-side
polygon + residual psi^{mu2*} (monic), the GENTOW-1(a) budget floors
at (mu2*, E2), node floors with the RAM-anchor sharpness, and the
COR 4.C projection p_j(f) - c_g = p_j(f_S) on the >T2 initial hull.

LEG-3 (CERT, THEOREM GENTOW-6.3): self-shadow of Phi2^2. CERT-TOP
rows (regime 2, 2*i_{t*} >= D'): the certificate slot (a*,b*) of
ShC_{j*} carries valuation-2a_{t*} digit at height THETA_{j*} = the
pin. Rows: A5/A7/B/C (B1 families) + NEW GENRES GEN-R2X (e1=3,
u2=11, cert at a*=1: first e1=3 certificate), GEN-P3/GEN-P3b (p=3:
first odd-p certificates). Regime-4 rows: FAM-E (e1=3, u2=7,
i_0=1, no overflowing pair): self-shadow EXACTLY zero; plus the
E-ENTRY row (entry digit x^2 with a+i_0 >= D'): shadow diverges at
height >= THETA_0 = 29 and flips the label, honest read PARI-true.

PREREGISTERED PREDICTIONS (sealed before the full run; smoke
disclosed below):
 P-1 TIE-MEASURE: every constructed row, every root s of the
   den>=2 side: composed mu2*(s) == m_s (res_factor multiplicity);
   all four profiles realized; no PEEL on perturbed rows.
 P-2 TIE-PARI: on the subsampled rows, nodev6 at key_s: rows with
   dv2(key_s) > E2*e sum ef to D2*m_s, for EACH class s; poldisc
   != 0 on every constructed row.
 P-3 TIE-SIGMA: (1,2)-profile rows fully decided by the GENTOW-4.A
   reader; sigma == PARI sig1.
 P-4 BLOCK-POLY: each block factor: single side slope 5/2 from
   (0, M_C*5/2) to (M_C, 0), residual digits == psi2^{mu2*} exactly
   (monic; res_factor gives {s: mu2*}, leftover [1]).
 P-5 BLOCK-BUDGET: every composed digit of f_S at its own key
   clears floor6(mu2*, j, a, b); node floors p_j^S >= (mu2*-j)*E2+1
   for every j < mu2*; the RAM-anchored block has p_0^S ==
   mu2**E2 + 1 EXACTLY (sharpness).
 P-6 BLOCK-PROJ: p_j(f) - c_g == p_j(f_S) at every composed
   coordinate j <= mu2* whose f-pin lies on the >T2 initial hull.
 P-7 CERT-TOP (7 rows): slot (a*,b*) of ShC_{j*}(Phi2^2) nonzero,
   vp == 2a_{t*} (A5:4 A7:6 B:2 C:6 R2X:6 P3:4 P3b:4), slot height
   == THETA_{j*} == pin(ShC_{j*}) (21/31/7/43/49/21/21); B also has
   ShC_0 pin 13 = THETA_0 and slot grid {(0,1):4-unit,(1,0):8-unit};
   A5/A7/C have ShC_1 = 0; R2X/P3/P3b ShC_1 zero-or->=THETA_1.
 P-8 EXACT: FAM-E self-shadow ShC_0 = ShC_1 = 0 (regime 4);
   FAM-D (x-free) reproduction: self-shadow zero (B1 import).
 P-9 E-ENTRY: fE = Phi2^2 + 4x^2*Phi2 + 16*Phi': honest read
   tRAM(31), sigma [(12,1)] == PARI; mindiff_0 not None and
   >= THETA_0 = 29; shadow label != tRAM (hand trace: the entry
   overflow's Phi'-kill exactly cancels the C_0 digit -- shadow
   ShC_0 = 0, DRAIN, divergence displayed at 31).
TEETH (all must fire):
 T-TIE-CONST: mutant "mu2* == family mu2 = 2 at every class" is
   killed on >= 4 rows ((1,2)/(0,3)/(3,0) profiles) with the PARI
   degree leg contradicting D2*2 on the subsample.
 T-CERT-V: mutant "cert valuation = 2a_{t*} + 1" killed on all 7
   cert rows.
 T-ODDP: mutant "attainment needs p = 2" killed by GEN-P3/GEN-P3b
   (cert digit unit != 0 mod 3).
 T-SHEXACT: mutant "regime-4 genre => every member faithful" killed
   by the E-ENTRY row (label flip, honest PARI-confirmed).
SMOKE DISCLOSURE (pre-seal, honest): a wiring smoke of each leg ran
before the seal; its fixes are disclosed here and no prediction was
changed after the seal beyond them:
  (1) LEG-1 key construction copied read_member's digit-derived key
      (Phi'^2 - s*9x over Q3); smoke fixed a sign slip (psca(-s)).
  (2) LEG-2's block polygon reader needed the deg-flexible dev
      length M_C = deg/D' (level1_read hard-asserts deg == F.n).
  (3) LEG-3 slot heights verified against F.w before sealing the
      THETA table; FAM-B's two-slot grid {(0,1),(1,0)} confirmed.
  (4) composed_read(mu2_exp=3) returns label tDEEP sig None at
      mu2* = 3: the tie leg accepts it (mu2s is what is scored).
  (5) smoke run 1 (0.3s, 401 checks): 1 violation -- the
      UNPERTURBED B2-reproduction row P5R.r2m1 drew sib_block =
      the simple key exactly (Phi'^2 - 9x, c=1), so key | f and
      the composed read PEELs (no j=0 pin; GENTOW-4's own battery
      routes this through the HE6R1-3 peel).  Fix: the
      reproduction rows get the same height-46 perturbation as
      the constructed rows (invisible to every consulted datum).
      All other legs were green in smoke; cert digits observed
      16/64/4/64/64/324/81 (v as predicted).
Verdict: GREEN iff 0 violations and 4/4 teeth.
Written 2026-08-09 by GENTOW-6 (BOX-CLOSURE campaign residue wave).
"""
import random
import sys
import time

import gentow1_checks as g1
import gentow3_checks as g3
import gentow4_checks as g4
from gentow4_checks import (dev, padd, pdivmod_monic, pmul, poly_str,
                            ppow, psca, pstrip, vp)

random.seed(20260811)
T0 = time.time()
VIOL = []
NCHK = 0
TEETH = {'T-TIE-CONST': 0, 'T-CERT-V': 0, 'T-ODDP': 0,
         'T-SHEXACT': 0}
OUT = []


def say(s):
    print(s)
    sys.stdout.flush()
    OUT.append(s)


def chk(fam, ok, msg):
    global NCHK
    NCHK += 1
    if not ok:
        VIOL.append('%s: %s' % (fam, msg))
        say('  !! VIOLATION %s: %s' % (fam, msg))
    return ok


# =================== LEG-1: the multiplicity tie ====================
F5 = g4.F5                    # FAM-P5 geography: Q3, side slope 5/2
KEY = {1: g4.F5KEYSIMPLE,     # s=1: Phi'^2 - 9x
       2: F5.PHI2}            # s=2: Phi'^2 - 18x (psi2 = T+1 = T-2)
PERT = [0, 3 ** 11]           # dv2-height 46 > all consulted data


def block_at(s, k, anchor=None):
    """deg-4k factor on the s-class locus: key^k + in-budget tail."""
    K = KEY[s]
    f = ppow(K, k)
    if anchor == 'RAM':       # p_0 = k*E2 + 1 exactly (sharp node)
        return padd(f, psca(random.choice([1, 2]),
                            F5.n2hat(k * F5.E2 + 1)))
    # random in-budget composed digits (floors + 0..2 slack)
    for j in range(k):
        for a in range(2):
            for b in range(2):
                fl = floor6(F5, k, j, a, b)
                c = random.choice([0, 1, 1, 2]) * 3 ** (
                    fl + random.choice([0, 0, 1]))
                if c:
                    f = padd(f, pmul([0] * a + [c],
                                     pmul(ppow(F5.PHI1, b),
                                          ppow(K, j))))
    if f == ppow(K, k):       # guarantee key does not divide
        f = padd(f, psca(3 ** floor6(F5, k, 0, 0, 1), F5.PHI1))
    return f


def floor6(F, mu, j, a, b):
    """GENTOW-1(a) budget floor at block multiplicity mu."""
    num = (mu - j) * F.E2 - F.w(a, b)
    if num <= 0:
        return 0
    fl = -((-num) // F.m)
    if num % F.m == 0:
        fl += 1
    return fl


def block_polygon(F, fS):
    """deg-flexible level-1 polygon of a block factor.
    -> (hull, sides) as in level1_read, no degree gate."""
    MC = (len(fS) - 1) // F.Dp
    A, top = dev(list(fS), F.PHI1, MC)
    assert top == [1], 'block not monic in Phi-dev'
    pins = []
    for J, c in enumerate(A):
        vals = [F.e1 * vp(cc, F.p) + i * F.h
                for i, cc in enumerate(c) if cc]
        if vals:
            pins.append((J, min(vals)))
    pins.append((MC, 0))
    hull = g4.lower_hull(pins)
    pmap = dict(pins)
    sides = []
    from math import gcd
    for k in range(len(hull) - 1):
        (J1, y1), (J2, y2) = hull[k], hull[k + 1]
        num, den = y1 - y2, J2 - J1
        gg = gcd(num, den)
        num, den = num // gg, den // gg
        digits = []
        for t in range((J2 - J1) // den + 1):
            J = J1 + t * den
            ht = y1 - t * num
            if J == MC:
                digits.append(1)
                continue
            if pmap.get(J) != ht:
                digits.append(0)
                continue
            dsum = 0
            for i, cc in enumerate(A[J]):
                if cc and F.e1 * vp(cc, F.p) + i * F.h == ht:
                    dsum += (cc // F.p ** vp(cc, F.p))
            digits.append(dsum % F.p)
        sides.append((J1, J2, num, den, digits))
    return hull, sides


GP_JOBS, GP_META = [], {}


def tie_row(tag, f, profile, blocks=None):
    """LEG-1 (+LEG-2 when blocks given, non-perturbed rows).
    profile: dict s -> m_s (the DESIGNED profile; measured must
    match res_factor AND composed_read)."""
    hull, sides = g4.level1_read(F5, f)
    if not chk('TIE', hull is not None, '%s parse: %s' % (tag, sides)):
        return
    got = {}
    reads = {}
    for (J1, J2, num, den, digits) in sides:
        if den < 2:
            continue
        roots, left = g4.res_factor(F5.p, digits)
        chk('TIE', len(left) == 1, '%s leftover %s' % (tag, left))
        for s, m in roots.items():
            got[s] = m
            r = g4.composed_read(F5, f, KEY[s], m, eta2=s)
            reads[s] = r
            chk('TIE', r.get('mu2s') == m,
                '%s class s=%d: mu2* %s != m_r %d'
                % (tag, s, r.get('mu2s'), m))
            if m != 2 and r.get('mu2s') == m:
                TEETH['T-TIE-CONST'] += 1
    chk('TIE', got == {s: m for s, m in profile.items() if m},
        '%s measured profile %s != designed %s'
        % (tag, got, profile))
    return got, reads


def q_sig(tag, f, want=None):
    GP_JOBS.append('print("%s ", sig1(%s, 3))' % (tag, poly_str(f)))
    GP_JOBS.append('print("%s.d ", poldisc(%s) != 0)'
                   % (tag, poly_str(f)))
    if want is not None:
        GP_META[tag] = want


def q_node(tag, f, s, m):
    GP_JOBS.append('print("%s.nv%d ", nodev6(%s, 3, %s, %s))'
                   % (tag, s, poly_str(f), poly_str(KEY[s]),
                      poly_str(F5.PHI1)))
    GP_META['%s.nv%d' % (tag, s)] = ('NODE', s, m)


def block_leg(tag, fS, s, m, ram_anchor=False):
    """LEG-2 on a known block factor fS (class s, multiplicity m)."""
    MC = (len(fS) - 1) // F5.Dp
    hull, sides = block_polygon(F5, fS)
    kap_top = MC * 5 // 2
    chk('BLOCK', hull == [(0, kap_top), (MC, 0)] and len(sides) == 1,
        '%s polygon %s not the single side to (%d,0)'
        % (tag, hull, MC))
    if len(sides) == 1:
        (J1, J2, num, den, digits) = sides[0]
        chk('BLOCK', (num, den) == (5, 2),
            '%s slope %d/%d != 5/2' % (tag, num, den))
        roots, left = g4.res_factor(F5.p, digits)
        chk('BLOCK', roots == {s: m} and len(left) == 1 and
            left[0] % 3 == 1,
            '%s residual %s x %s != psi^%d monic (s=%d)'
            % (tag, roots, left, m, s))
    # budget floors on the composed digits of fS at its own key
    C, top = dev(list(fS), KEY[s], m)
    chk('BLOCK', top == [1], '%s block dev not monic' % tag)
    nslots = 0
    for j, Cj in enumerate(C):
        sl = F5.slots(Cj)
        for (a, b), c in sl.items():
            nslots += 1
            chk('BLOCK', vp(c, 3) >= floor6(F5, m, j, a, b),
                '%s digit (%d,%d,%d) v=%s < floor %d'
                % (tag, j, a, b, vp(c, 3), floor6(F5, m, j, a, b)))
        pj = F5.pin(Cj)[0] if sl else None
        need = (m - j) * F5.E2 + 1
        chk('BLOCK', pj is None or pj >= need,
            '%s node floor j=%d: %s < %d' % (tag, j, pj, need))
        if j == 0 and ram_anchor:
            chk('BLOCK', pj == m * F5.E2 + 1,
                '%s RAM anchor p_0 %s != %d (sharp)'
                % (tag, pj, m * F5.E2 + 1))
    return nslots


def proj_leg(tag, f, fS, s, m):
    """LEG-2 (P-6): p_j(f) - c_g == p_j(fS) on the >T2 initial
    hull."""
    r = g4.composed_read(F5, f, KEY[s], m, eta2=s)
    if not chk('PROJ', r.get('mu2s') == m,
               '%s composed mu2* %s != %d' % (tag, r.get('mu2s'), m)):
        return
    cg, pins, hull = r['cg'], r['pins'], r['hull']
    C, _ = dev(list(fS), KEY[s], m)
    for j in range(m):
        pj = pins.get(j)
        if pj is None:
            continue
        # on the >T2 initial hull segment?
        on = False
        for k in range(len(hull) - 1):
            (j1, y1), (j2, y2) = hull[k], hull[k + 1]
            if j1 <= j <= j2 and (y1 - y2) > F5.E2 * (j2 - j1):
                if (y1 - pj) * (j2 - j1) == (j - j1) * (y1 - y2):
                    on = True
        if not on:
            continue
        sl = F5.slots(C[j])
        pjS = F5.pin(C[j])[0] if sl else None
        chk('PROJ', pjS == pj - cg,
            '%s j=%d: p_j - c_g = %d != block pin %s'
            % (tag, j, pj - cg, pjS))


def leg12():
    say('== LEG-1/LEG-2: the tie + the block layer (FAM-P5 geo) ==')
    profiles = [({1: 1, 2: 2}, '21'), ({1: 2, 2: 1}, '12'),
                ({1: 0, 2: 3}, '03'), ({1: 3, 2: 0}, '30')]
    seen = set()
    rowid = 0
    for (prof, pname) in profiles:
        for rep in range(3):
            blocks = [(s, m, block_at(s, m, 'RAM' if rep == 0 else
                                      None))
                      for s, m in prof.items() if m]
            f = [1]
            for (_, _, B) in blocks:
                f = pmul(f, B)
            tagb = 'P5X.%s.%d' % (pname, rep)
            # LEG-2 on the exact (non-perturbed) product
            for (s, m, B) in blocks:
                block_leg('%s.blk%d' % (tagb, s), B, s, m,
                          ram_anchor=(rep == 0))
                proj_leg('%s.prj%d' % (tagb, s), f, B, s, m)
            # LEG-1 on the perturbed row (key never divides f)
            fp = padd(f, PERT)
            res = tie_row(tagb, fp, prof)
            if res:
                seen.add(pname)
            q_sig(tagb, fp)
            if rep == 0:
                for s, m in prof.items():
                    if m:
                        q_node(tagb, fp, s, m)
            # P-3: (1,2) rows fully decided -> sigma vs PARI
            if pname == '21' and res:
                _, reads = res
                s1 = reads.get(1, {}).get('sig')
                s2 = reads.get(2, {}).get('sig')
                chk('TIE', s1 is not None and s2 is not None,
                    '%s (1,2)-profile row not fully decided' % tagb)
                if s1 is not None and s2 is not None:
                    GP_META[tagb] = ('SIG', sorted(s1 + s2))
            rowid += 1
    chk('TIE', seen == {'21', '12', '03', '30'},
        'profiles realized: %s' % sorted(seen))
    # existing-battery reproduction rows (B2 constructors, additive)
    for i, f in enumerate(g4.r1_members(F5, 4)):
        tie_row('P5R.r1m%d' % i, padd(f, PERT), {1: 1, 2: 2})
    for i, f in enumerate(g4.r2_members(F5, ['RAM', 'INERT'], 1)):
        tie_row('P5R.r2m%d' % i, padd(f, PERT), {1: 1, 2: 2})


# =================== LEG-3: the attainment certificate ==============
PE = [-2, 0, 0, 1]                        # x^3 - 2 over Q2 (e1 = 3)
FAM_E = g1.Fam('FAM-E', 2, PE, 1, 3, 2, 1, 2, 7,
               padd(pmul(PE, PE), [0, -4]), [1, 1],
               [(12, 1)], [(6, 1), (6, 1)], [(6, 2)])
GEN_R2X = g1.Fam('GEN-R2X', 2, PE, 1, 3, 2, 1, 2, 11,
                 padd(pmul(PE, PE), [0, 0, -8]), [1, 1],
                 [(12, 1)], [(6, 1), (6, 1)], [(6, 2)])
GEN_P3 = g1.Fam('GEN-P3', 3, g1.PB, 1, 2, 2, 1, 2, 5,
                padd(pmul(g1.PB, g1.PB), [0, -18]), [1, 1],
                [(8, 1)], [(4, 1), (4, 1)], [(4, 2)])
GEN_P3B = g1.Fam('GEN-P3b', 3, g1.PB, 1, 2, 2, 1, 2, 5,
                 padd(pmul(g1.PB, g1.PB), [0, -9]), [1, 1],
                 [(8, 1)], [(4, 1), (4, 1)], [(4, 2)])
# rows: (F, j*, (a*,b*), v* = 2a_{t*}, THETA_{j*})
CERT = [(g1.FBY['FAM-A5'], 0, (0, 1), 4, 21),
        (g1.FBY['FAM-A7'], 0, (0, 1), 6, 31),
        (g1.FBY['FAM-B'], 1, (0, 1), 2, 7),
        (g1.FBY['FAM-C'], 0, (0, 1), 6, 43),
        (GEN_R2X, 0, (1, 1), 6, 49),
        (GEN_P3, 0, (0, 1), 4, 21),
        (GEN_P3B, 0, (0, 1), 4, 21)]


def cert_leg():
    say('== LEG-3: CERT-TOP self-shadow rows ==')
    for (F, js, ab, vst, TH) in CERT:
        tag = F.name
        chk('CERT', g3.theta(F, js) == TH,
            '%s THETA_%d = %d != table %d'
            % (tag, js, g3.theta(F, js), TH))
        fk = ppow(F.PHI2, F.mu2)
        Cs = g3.honest_coords(F, fk)
        chk('CERT', all(not pstrip(list(c)) for c in Cs),
            '%s honest self-read not DRAIN' % tag)
        ShCs, _ = g3.shadow_read(F, fk)
        sl = F.slots(ShCs[js])
        c = sl.get(ab, 0)
        v = vp(c, F.p)
        chk('CERT', c != 0 and v == vst,
            '%s cert slot %s digit %s v=%s != %d'
            % (tag, ab, c, v, vst))
        if c != 0 and v == vst:
            TEETH['T-CERT-V'] += 1
        if c != 0:
            ht = F.m * v + F.w(*ab)
            chk('CERT', ht == TH,
                '%s cert height %d != THETA %d' % (tag, ht, TH))
            unit = (c // F.p ** v) % F.p
            chk('CERT', unit != 0, '%s unit 0 mod p' % tag)
            if F.p == 3 and unit != 0:
                TEETH['T-ODDP'] += 1
        pin0 = F.pin(ShCs[js])[0]
        chk('CERT', pin0 == TH,
            '%s ShC_%d pin %s != THETA %d (attainment ON the '
            'floor)' % (tag, js, pin0, TH))
        # companion coordinate
        oth = 1 - js
        po = F.pin(ShCs[oth])[0] if pstrip(list(ShCs[oth])) else None
        if F.name == 'FAM-B':
            chk('CERT', po == 13, 'FAM-B ShC_0 pin %s != 13' % po)
            chk('CERT', set(sl) == {(0, 1), (1, 0)} and
                vp(sl[(1, 0)], 2) == 3,
                'FAM-B ShC_1 grid %s != 4Phi\'+8x shape' % sl)
        elif F.name in ('FAM-A5', 'FAM-A7', 'FAM-C'):
            chk('CERT', po is None,
                '%s ShC_1 nonzero pin %s' % (tag, po))
        else:
            chk('CERT', po is None or po >= g3.theta(F, oth),
                '%s ShC_%d pin %s < THETA %d'
                % (tag, oth, po, g3.theta(F, oth)))
        say('  %s: cert slot %s digit %d (v=%d) at height %d = '
            'THETA_%d; pins (%s, %s)'
            % (tag, ab, c, v, TH, js,
               F.pin(ShCs[0])[0] if pstrip(list(ShCs[0])) else None,
               po if js == 0 else F.pin(ShCs[1])[0]))


def exact_leg():
    say('== LEG-3: regime-4 exactness + E-ENTRY ==')
    for F in (FAM_E, g1.FBY['FAM-D']):
        fk = ppow(F.PHI2, F.mu2)
        ShCs, _ = g3.shadow_read(F, fk)
        chk('EXACT', all(not pstrip(list(c)) for c in ShCs),
            '%s self-shadow nonzero: %s'
            % (F.name, [F.pin(c)[0] if pstrip(list(c)) else None
                        for c in ShCs]))
        say('  %s: self-shadow identically zero' % F.name)
    # the E-ENTRY row
    F = FAM_E
    fE = padd(padd(ppow(F.PHI2, 2), pmul([0, 0, 4], F.PHI2)),
              psca(16, F.PHI1))
    Cs = g3.honest_coords(F, fE)
    ShCs, _ = g3.shadow_read(F, fE)
    rh = g3.label2(F, Cs[0], Cs[1])
    rs = g3.label2(F, ShCs[0], ShCs[1])
    md0 = g3.mindiff(F, ShCs[0], Cs[0])
    chk('ENTRY', rh[:3] == (31, 16, 'tRAM'),
        'E-ENTRY honest %s != tRAM(31,16)' % (rh[:3],))
    chk('ENTRY', md0 is not None and md0 >= 29,
        'E-ENTRY mindiff_0 %s (want not-None >= 29)' % md0)
    chk('ENTRY', rs[2] != 'tRAM',
        'E-ENTRY shadow label %s did not flip' % rs[2])
    if rh[:3] == (31, 16, 'tRAM') and rs[2] != 'tRAM' and \
            md0 is not None and md0 >= 29:
        TEETH['T-SHEXACT'] += 1
    say('  E-ENTRY: honest %s / shadow %s / first divergence %s '
        '(THETA_0 = 29)' % (rh[:3], rs[:3], md0))
    GP_JOBS.append('print("EENTRY ", sig1(%s, 2))' % poly_str(fE))
    GP_JOBS.append('print("EENTRY.d ", poldisc(%s) != 0)'
                   % poly_str(fE))
    GP_META['EENTRY'] = ('SIG', [(12, 1)])
    # new-genre gates: keys irreducible with the right (e,f)
    for F2, ef in ((FAM_E, (6, 1)), (GEN_R2X, (6, 1)),
                   (GEN_P3, (4, 1)), (GEN_P3B, (4, 1))):
        GP_JOBS.append('print("KEY%s ", sig1(%s, %d))'
                       % (F2.name, poly_str(F2.PHI2), F2.p))
        GP_META['KEY%s' % F2.name] = ('SIG', [ef])


def resolve_gp():
    say('== PARI leg: %d jobs ==' % len(GP_JOBS))
    res = g4.run_gp(GP_JOBS)
    for tag, want in GP_META.items():
        if tag not in res:
            chk('GP', False, 'missing gp answer %s' % tag)
            continue
        if want[0] == 'SIG':
            got = g4.sig_parse(res[tag])
            chk('GP-SIG', got == sorted(want[1]),
                '%s sigma %s != want %s' % (tag, got,
                                            sorted(want[1])))
        elif want[0] == 'NODE':
            _, s, m = want
            rows = g4.tup_parse(res[tag], 6)
            clsdeg = sum(ef_ for (e_, f_, ef_, v2_, vx_, v1_) in
                         rows if F5.m * v2_ > F5.E2 * e_)
            chk('GP-NODE', clsdeg == F5.D2 * m,
                '%s class degree sum %d != D2*m_r = %d'
                % (tag, clsdeg, F5.D2 * m))
            if m != 2 and clsdeg == F5.D2 * m:
                TEETH['T-TIE-CONST'] += 1
    for tag in [t for t in res if t.endswith('.d')]:
        chk('GP-DISC', res[tag] == '1', '%s disc = 0' % tag)


def main():
    say('=== GENTOW-6 battery (tie / block / attainment) seal '
        '2026-08-09 ===')
    leg12()
    cert_leg()
    exact_leg()
    resolve_gp()
    for t, n in TEETH.items():
        chk('TEETH', n >= (2 if t == 'T-ODDP' else 1),
            'tooth %s fired only x%d' % (t, n))
        say('tooth %s fired x%d' % (t, n))
    nv = len(VIOL)
    say('=== VERDICT: %s -- %d checks, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', NCHK, nv,
           time.time() - T0))
    return 0 if nv == 0 else 1


if __name__ == '__main__':
    rc = main()
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
