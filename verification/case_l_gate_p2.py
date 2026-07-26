#!/usr/bin/env python3
"""case_l_gate_p2.py — SEALED Case-L gate census at p = 2 (3-move joint history).

Predictions preregistered in CASE_L_SEALED_PREDICTIONS_2026-07-26.md (committed
BEFORE this script existed).  This script is the CENSUS: it enumerates/samples,
factorizes by genuine division, measures, and reports PASS/FAIL per sealed
prediction with exact counts.  It never adjusts a prediction; FAIL is a valid
outcome; the exact-zero falsifiers F1-F4 are one-hit kills, checked
member-by-member.

Config (sealed S0): p = 2, N = 12 (mod 4096), n = 9 monic.  Root stratum =
R0-pattern: a_b = R0dig(b)*2^(8-b) + 2^(9-b)*U_b, R0 = psi0^4 = z^8+z^4+1
(digit 1 at b in {0,4,8}), U_b uniform mod 2^(3+b); Monte-Carlo M = 10^6
members (63 free base digits — full enumeration impossible), seed 20260726.
History H: nu0 = root read side [0,8] slope 1, psi0 = z^2+z+1, key
Phi0 = x^2+2x+4; nu1 = side [1,4] slope 7/3 (beta-probe, s0 = 1), cell
d = dig(B1)@7 in F4*; nu2 = tail read, frame-2 slot-0 hull point predicted at
v 29/3 (stage 29), cell u = dig(c02)@5.

Frame 1 (deg-2 key): f = sum_j B_j*Phi0^j by the CLOSED-FORM synthetic
recurrence q_i = g_{i+2} - c1*q_{i+1} - c0*q_{i+2} for x^2 + c1*x + c0
[sign B: (c1,c0) = (2,4); sign A control: (-2,-4)], verified on subsamples
against genuine subtract-multiples polydiv by the literal Phi0 AND by full
reconstruction.  w(B) = min(v(b_c), v(b_x)+1); F4 digit of B at m:
eps_c = 1 iff v(b_c) = m, eps_x = 1 iff v(b_x) = m-1; code = 2*eps_x + eps_c.

Frame 2: Phi1(d) = Phi0^3 + 64*d_x*x + 128*d_c — the D.5/(S6b) standard-lift
realizer of the cell digit d at v 7 (wrong-tau keys tau' != d and tau' = 0 are
probed on a subsample as the naive/stage-28 discriminant control).
f = C1*Phi1 + C0 (genuine division, closed form verified vs literal polydiv);
C0 = c00 + c01*Phi0 + c02*Phi0^2; v1(C0) = min(w(c00), w(c01)+7/3,
w(c02)+14/3) — the three terms are distinct mod 1 (thirds), so NO ties;
stage := 3*v1(C0); rung table (sealed S4): 28 dead, 29 emitted via c02.

Cap stability: every member is reclassified mod 2^11 (cap 11); all sealed
buckets read digit levels <= 10, one full level of margin — the classification
tuple must be IDENTICAL member-by-member.

Sealed verdicts: P1-P4 (masses/partition), B1-B4 (beta strip), PD0-PD2, PD4
(displacement), C-WS (control family); falsifiers F1-F4 exact-zero one-hit,
F5-F8 4-sigma binomial bands on M = 10^6.

Run:  python3 case_l_gate_p2.py
      (all tables -> results/case_l_gate_p2_output.txt; summary on stdout)
"""
import os
import random
import sys
import time
from math import sqrt

P, N, NCAP2 = 2, 12, 11
M2, M2C = 1 << N, 1 << NCAP2     # 4096, 2048
MSAMP = 1_000_000
SEED = 20260726
NSUB = 2000                      # literal-division verification subsample
NPROBE = 2000                    # wrong-tau probe subsample (nu1-cell members)
OUTPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'results', 'case_l_gate_p2_output.txt')


def vtable(mod, ncap):
    vt = [0] * mod
    vt[0] = ncap
    for y in range(1, mod):
        vt[y] = 0 if y & 1 else min(vt[y >> 1] + 1, ncap)
    return vt


VT12 = vtable(M2, N)
VT11 = vtable(M2C, NCAP2)
F4N = ['0', '1', 'zb', 'zb+1']   # code = 2*eps_x + eps_c
R0DIG = [1, 0, 0, 0, 1, 0, 0, 0, 1]   # R0 = z^8 + z^4 + 1


def sample_member(rng):
    """One root-stratum member mod 2^12: [a0..a8] per the sealed protocol."""
    return [((R0DIG[b] << (8 - b)) + (rng.getrandbits(3 + b) << (9 - b)))
            & (M2 - 1) for b in range(9)]


def wdig(bc, bx, vt, ncap):
    """w = min(v(bc), v(bx)+1) capped, and the F4 digit code at w (0 if lump)."""
    vc, vx = vt[bc], vt[bx] + 1
    w = vc if vc < vx else vx
    if w > ncap:
        w = ncap
    ec = 1 if (vc == w and w < ncap) else 0
    ex = 1 if vt[bx] == w - 1 else 0
    return w, 2 * ex + ec


def polydiv(f, d, mod):
    """Genuine long division (subtract multiples of literal divisor d, monic)."""
    f = list(f)
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % mod
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % mod
    return q, [x % mod for x in f[:dd]]


def polymul(A, B, mod):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % mod
    return R


def dev_quad(g, c1, c0, mod):
    """Closed-form division of g (low->high, len>=3) by x^2 + c1*x + c0:
    q_i = g_{i+2} - c1*q_{i+1} - c0*q_{i+2}; r_x = g1 - c1*q0 - c0*q1;
    r_c = g0 - c0*q0.  Returns (q, (r_c, r_x))."""
    k = len(g) - 1
    q = [0] * (k - 1)
    q[k - 2] = g[k] % mod
    if k >= 3:
        q[k - 3] = (g[k - 1] - c1 * q[k - 2]) % mod
    for i in range(k - 4, -1, -1):
        q[i] = (g[i + 2] - c1 * q[i + 1] - c0 * q[i + 2]) % mod
    rx = (g[1] - c1 * q[0] - (c0 * q[1] if k >= 3 else 0)) % mod
    rc = (g[0] - c0 * q[0]) % mod
    return q, (rc, rx)


def phi0_tower(a, mod, c1=2, c0=4):
    """Iterated closed-form division by Phi0: [a0..a8] + monic x^9 ->
    B pairs [(b0c,b0x), ..., (b4c,b4x)] with f = sum B_j Phi0^j."""
    g = list(a) + [1]
    B = []
    for _ in range(4):
        g, r = dev_quad(g, c1, c0, mod)
        B.append(r)
    B.append((g[0] % mod, g[1] % mod))
    return B


def dev_monic_closed(f, d, mod):
    """Closed-form synthetic division by a general monic d (low->high):
    q_i = f_{i+dd} - sum_t d_{dd-t}*q_{i+t}; r_j = f_j - sum_i q_i*d_{j-i}."""
    dd = len(d) - 1
    nq = len(f) - dd
    q = [0] * nq
    for i in range(nq - 1, -1, -1):
        s = f[i + dd]
        for t in range(1, nq - i):
            s -= d[dd - t] * q[i + t]
        q[i] = s % mod
    r = []
    for j in range(dd):
        s = f[j]
        for i in range(min(j, nq - 1) + 1):
            s -= q[i] * d[j - i]
        r.append(s % mod)
    return q, r


PHI0 = [4, 2, 1]
PHI0CUBED = polymul(polymul(PHI0, PHI0, M2), PHI0, M2)   # (x^2+2x+4)^3 mod 4096


def phi1_of(dcode, mod):
    """The (S6b)/D.5 standard-lift realizer for cell digit d (code 2*dx+dc):
    Phi1 = Phi0^3 + 64*d_x*x + 128*d_c (monic degree 6)."""
    ph = [c % mod for c in PHI0CUBED]
    ph[0] = (ph[0] + 128 * (dcode & 1)) % mod
    ph[1] = (ph[1] + 64 * (dcode >> 1)) % mod
    return ph


def classify(a, mod, vt, ncap):
    """Full genuine-division classification of one root-stratum member.
    Returns a dict: cls in {'WS','NU1','DEEP','OTHER'}, all sealed observables.
    NU1 emission = frame-1 hull side [1,4] slope 7/3: vertex at slot 1 needs
    w(B1) = 7 with left slope w(B0)-7 > 7/3 (so w(B0) >= 10) and slots 2,3
    strictly above the line (>14/3, >7/3).  WS emission = single side [0,4]
    slope 9/4: w(B0) = 9 with slots 1,2,3 strictly above the chord.  The
    falsifier counters recheck the beta clauses from the raw B0 data."""
    B = phi0_tower(a, mod)
    w0, g0 = wdig(B[0][0], B[0][1], vt, ncap)
    w1, g1 = wdig(B[1][0], B[1][1], vt, ncap)
    w2, _ = wdig(B[2][0], B[2][1], vt, ncap)
    w3, _ = wdig(B[3][0], B[3][1], vt, ncap)
    w4, g4 = wdig(B[4][0], B[4][1], vt, ncap)
    r = {'w0': w0, 'w1': w1, 'w2': w2, 'w3': w3, 'w4': w4, 'g4': g4,
         'floor_ok': w0 >= 9 and w1 >= 7 and w2 >= 5 and w3 >= 3
                     and w4 == 0 and g4 == 1}
    if not r['floor_ok']:
        r['cls'] = 'OTHER'
        return r
    if w0 == 9:                       # beta pair alive -> [0,4] slope 9/4
        r['cls'], r['u0'] = 'WS', g0  # hull side: 7>27/4? floors already checked
        r['g1info'] = g1 if w1 == 7 else 0   # would-be d under the no-beta theory
        return r
    if w1 == 7:                       # w0 >= 10: [1,4] slope 7/3 emission
        r['cls'] = 'NU1'
        d = g1
        r['d'] = d
        # beta-clause member-by-member recheck from raw B0 (F1/F4/B2):
        b0c, b0x = B[0]
        r['pair9_alive'] = ((b0c >> 9) & 1) or ((b0x >> 8) & 1)
        r['b3bucket'] = 10 if w0 == 10 else 11        # B3: 10 exact vs >= 11
        ec10 = 1 if vt[b0c] == 10 else 0
        ex10 = 1 if vt[b0x] == 9 else 0
        r['digB0at10'] = 2 * ex10 + ec10              # info (B3 free digit)
        # F3 / PD2 occupancy: raw digits of B1 at base labels (2,7),(3,6):
        b1c, b1x = B[1]
        r['B1pair'] = ((b1c >> 7) & 1, (b1x >> 6) & 1)        # (level7 c, level6 x)
        r['F3'] = r['B1pair'] != (d & 1, d >> 1)
        # frame 2: divide by the realizer Phi1(d), expand C0 and C1 Phi0-adically
        ph1 = phi1_of(d, mod)
        C1, C0 = dev_monic_closed(list(a) + [1], ph1, mod)
        q01, c00 = dev_quad(C0, 2, 4, mod)
        c02, c01 = dev_quad(q01, 2, 4, mod)           # q01 deg 3 -> c02 pair
        c02 = (c02[0], c02[1])
        wc00, _ = wdig(c00[0], c00[1], vt, ncap)
        wc01, _ = wdig(c01[0], c01[1], vt, ncap)
        wc02, gu = wdig(c02[0], c02[1], vt, ncap)
        s0, s1, s2 = 3 * wc00, 3 * wc01 + 7, 3 * wc02 + 14
        stage = min(s0, s1, s2)
        r['stage'] = stage
        r['stagebucket'] = min(stage, 33)
        r['u'] = gu if stage == 29 else 0
        r['wc00_ok'] = wc00 >= 10                     # sealed floor F2(0),F2(1)
        r['c01pair'] = ((c01[0] >> 7) & 1, (c01[1] >> 6) & 1)  # frame-2 (2,7),(3,6)
        # inherited vertex (info, not sealed): v1(C1) = 7/3
        qc1, c10 = dev_quad(C1, 2, 4, mod)
        wc11, _ = wdig(qc1[0], 0, vt, ncap)           # c11 = scalar (deg C1 = 3)
        wc10, _ = wdig(c10[0], c10[1], vt, ncap)
        r['c1_inh'] = (vt[qc1[0]] == 0 and wc10 >= 3)
        return r
    r['cls'] = 'DEEP'                 # w0 >= 10 and w1 >= 8
    return r


def verification_pass(out):
    """Closed forms vs genuine literal division on NSUB fresh members:
    (1) phi0_tower sign B (2,4) vs iterated polydiv by literal [4,2,1], plus
        full reconstruction sum B_j Phi0^j == f;  sign A (-2,-4) mismatches;
    (2) for NU1 members: dev_monic_closed vs polydiv by the literal Phi1(d),
        reconstruction C1*Phi1 + C0 == f, and the c0j expansion vs polydiv."""
    rng = random.Random(SEED + 1)
    misB = misA = recbad = 0
    n1 = mis1 = rec1bad = misc = 0
    for _ in range(NSUB):
        a = sample_member(rng)
        f = list(a) + [1]
        g, Bs = f, []
        for _ in range(4):
            g, rr = polydiv(g, PHI0, M2)
            Bs.append((rr[0], rr[1]))
        Bs.append((g[0], g[1]))
        cB = phi0_tower(a, M2)
        cA = phi0_tower(a, M2, -2 % M2, -4 % M2)
        misB += cB != Bs
        misA += cA != Bs
        # reconstruction via Horner: (((B4*Phi0+B3)*Phi0+B2)*Phi0+B1)*Phi0+B0
        acc = [cB[4][0], cB[4][1]]
        for j in (3, 2, 1, 0):
            acc = polymul(acc, PHI0, M2)
            acc[0] = (acc[0] + cB[j][0]) % M2
            acc[1] = (acc[1] + cB[j][1]) % M2
        recbad += acc != f
        r = classify(a, M2, VT12, N)
        if r['cls'] == 'NU1':
            n1 += 1
            ph1 = phi1_of(r['d'], M2)
            qL, rL = polydiv(f, ph1, M2)
            qC, rC = dev_monic_closed(f, ph1, M2)
            mis1 += (qL, rL) != (qC, rC)
            rec = polymul(qC, ph1, M2)
            for j, c in enumerate(rC):
                rec[j] = (rec[j] + c) % M2
            rec1bad += rec != f
            q01L, c00L = polydiv(rC, PHI0, M2)
            c02L, c01L = polydiv(q01L, PHI0, M2)
            q01C, c00C = dev_quad(rC, 2, 4, M2)
            c02C, c01C = dev_quad(q01C, 2, 4, M2)
            misc += (q01L, c00L) != (q01C, list(c00C)) or \
                    (c02L, c01L) != (list(c02C), list(c01C))
    out.append(f'\n== CLOSED-FORM VERIFICATION ({NSUB} fresh members, genuine '
               f'subtract-multiples division by the LITERAL divisors):')
    out.append(f'  Phi0 tower, sign B (c1,c0)=(2,4):  mismatches {misB} of {NSUB}; '
               f'reconstruction failures {recbad}')
    out.append(f'  Phi0 tower, sign A (c1,c0)=(-2,-4): mismatches {misA} of {NSUB}')
    out.append(f'  Phi1(d) division on {n1} NU1 members: closed-vs-literal '
               f'mismatches {mis1}; reconstruction failures {rec1bad}; '
               f'c0j-expansion mismatches {misc}')
    return dict(nsub=NSUB, misB=misB, misA=misA, recbad=recbad,
                n1=n1, mis1=mis1, rec1bad=rec1bad, misc=misc)


def captuple(r):
    """The sealed classification tuple (everything any verdict consumes)."""
    if r['cls'] == 'WS':
        return ('WS', r['u0'])
    if r['cls'] == 'NU1':
        return ('NU1', r['d'], r['b3bucket'], r['digB0at10'], r['stagebucket'],
                r['u'], r['pair9_alive'], r['F3'], r['c01pair'], r['wc00_ok'])
    return (r['cls'],)


def census():
    """The Monte-Carlo census: MSAMP root-stratum members, genuine-division
    classification mod 2^12, member-identical re-classification mod 2^11,
    wrong-tau probe on the first NPROBE NU1 members."""
    rng = random.Random(SEED)
    c = dict(n=MSAMP, ws=[0] * 4, ws_g1alive=0, nu1=[0] * 4, deep=0, other=0,
             other_ex=[], F1=0, F2=0, F2_ex=[], F3=0, F3_ex=[], F4=0,
             b3=[[0, 0] for _ in range(4)],           # per d: [w0==10, w0>=11]
             digB0at10=[[0] * 4 for _ in range(4)],
             stages=[{} for _ in range(4)],           # per d: stagebucket hist
             joint=[[0] * 4 for _ in range(4)],       # (d, u) counts, stage 29
             c01pairs=[{} for _ in range(4)],         # per d: frame-2 pair hist
             wc00bad=0, c1inh_bad=0, lt28=0,
             b4bad=0, w0bad=0, w1bad=0, w4bad=0,
             capbad=0, cap_ex=[],
             probe=[[0, 0] for _ in range(4)])        # per tau': [n, stage28 hits]
    nprobed = 0
    for i in range(MSAMP):
        a = sample_member(rng)
        r = classify(a, M2, VT12, N)
        # cap stability: reclassify the truncated member mod 2^11
        a11 = [x & (M2C - 1) for x in a]
        r11 = classify(a11, M2C, VT11, NCAP2)
        if captuple(r) != captuple(r11):
            c['capbad'] += 1
            if len(c['cap_ex']) < 3:
                c['cap_ex'].append((a, captuple(r), captuple(r11)))
        cls = r['cls']
        if cls == 'OTHER':
            c['other'] += 1
            c['b4bad'] += r['w2'] < 5 or r['w3'] < 3      # B4 one-hit member form
            c['w0bad'] += r['w0'] < 9
            c['w1bad'] += r['w1'] < 7
            c['w4bad'] += r['w4'] != 0 or r['g4'] != 1
            if len(c['other_ex']) < 5:
                c['other_ex'].append((a, {k: r[k] for k in
                                          ('w0', 'w1', 'w2', 'w3', 'w4', 'g4')}))
        elif cls == 'WS':
            c['ws'][r['u0']] += 1
            c['ws_g1alive'] += r['g1info'] != 0
        elif cls == 'DEEP':
            c['deep'] += 1
        else:                                         # NU1, cell d
            d = r['d']
            c['nu1'][d] += 1
            if r['w0'] < 10:
                c['F1'] += 1                          # one-hit kill (B1)
            if r['pair9_alive']:
                c['F4'] += 1                          # one-hit kill (B2/C-WS)
            c['b3'][d][0 if r['b3bucket'] == 10 else 1] += 1
            c['digB0at10'][d][r['digB0at10']] += 1
            sb = r['stagebucket']
            c['stages'][d][sb] = c['stages'][d].get(sb, 0) + 1
            if r['stage'] == 28:
                c['F2'] += 1                          # one-hit kill (PD0/C-WW)
                if len(c['F2_ex']) < 5:
                    c['F2_ex'].append(a)
            if r['stage'] < 28:
                c['lt28'] += 1
            if r['stage'] == 29:
                c['joint'][d][r['u']] += 1
            if r['F3']:
                c['F3'] += 1                          # one-hit kill (PD2)
                if len(c['F3_ex']) < 5:
                    c['F3_ex'].append((a, r['B1pair'], d))
            cp = r['c01pair']
            c['c01pairs'][d][cp] = c['c01pairs'][d].get(cp, 0) + 1
            c['wc00bad'] += not r['wc00_ok']
            c['c1inh_bad'] += not r['c1_inh']
            if nprobed < NPROBE:                      # wrong-tau discriminant
                nprobed += 1
                f = list(a) + [1]
                for tau in range(4):
                    if tau == d:
                        continue
                    _, C0w = dev_monic_closed(f, phi1_of(tau, M2), M2)
                    q01w, c00w = dev_quad(C0w, 2, 4, M2)
                    c02w, c01w = dev_quad(q01w, 2, 4, M2)
                    st = min(3 * wdig(c00w[0], c00w[1], VT12, N)[0],
                             3 * wdig(c01w[0], c01w[1], VT12, N)[0] + 7,
                             3 * wdig(c02w[0], c02w[1], VT12, N)[0] + 14)
                    c['probe'][tau][0] += 1
                    c['probe'][tau][1] += st == 28
    c['nprobed'] = nprobed
    return c


def band(k, n, q):
    """4-sigma binomial band: returns (ok, expected, sigmas-off)."""
    exp = n * q
    sd = sqrt(n * q * (1 - q)) or 1.0
    return abs(k - exp) <= 4 * sd, exp, (k - exp) / sd


def bline(label, k, n, q, qname):
    ok, exp, sig = band(k, n, q)
    return ok, (f'  {label}: {k} of {n} (frac {k / n:.6f}); sealed {qname} '
                f'-> expected {exp:.1f}, {sig:+.2f} sigma'
                + ('' if ok else '   <-- OUTSIDE 4-sigma BAND'))


def evaluate(c, out):
    v, n = {}, c['n']
    nu1tot = sum(c['nu1'][1:])
    wstot = sum(c['ws'][1:])
    deep = c['deep']
    out.append(f"\n== EMISSION PARTITION (M = {n} root-stratum members): "
               f"WS [0,4]-slope-9/4: {wstot}; NU1 [1,4]-slope-7/3: {nu1tot}; "
               f"DEEP (both dead): {deep}; OTHER (floor violations): {c['other']}"
               f" (w0<9: {c['w0bad']}, w1<7: {c['w1bad']}, w2<5/w3<3 [B4]: "
               f"{c['b4bad']}, w4 bad: {c['w4bad']}); ws[dig=0]: {c['ws'][0]}, "
               f"nu1[d=0]: {c['nu1'][0]}")
    v['B4'] = c['b4bad'] == 0 and c['w0bad'] == 0 and c['w1bad'] == 0 \
        and c['w4bad'] == 0 and c['other'] == 0
    ok4 = []
    for lab, k, q, qn in (('WS total', wstot, 3 / 4, '3/4'),
                          ('NU1 total (P2)', nu1tot, 3 / 16, '3/16'),
                          ('DEEP', deep, 1 / 16, '1/16')):
        o, s = bline(lab, k, n, q, qn)
        ok4.append(o)
        out.append(s)
    v['P2'] = ok4[1]
    v['P4'] = all(ok4) and c['other'] == 0
    out.append('\n== C-WS control family (beta pair alive at ((0,9),(1,8))):')
    okws = []
    for u0 in (1, 2, 3):
        o, s = bline(f'u0-cell {F4N[u0]}', c['ws'][u0], n, 1 / 4, '1/4')
        okws.append(o)
        out.append(s)
    out.append(f"  [info] WS members with dig(B1)@7 alive (the rev-4/5 would-be "
               f"d-cells): {c['ws_g1alive']} of {wstot} "
               f"({c['ws_g1alive'] / max(wstot, 1):.4f}; free digit -> 3/4)")
    v['C-WS'] = all(okws) and ok4[0] and c['F4'] == 0
    out.append('\n== NU1 cells (per d): P1 masses, B3 splits, stage ladder:')
    okp1, okb3, okpd1, okpd4 = [], [], [], []
    for d in (1, 2, 3):
        cn = c['nu1'][d]
        o, s = bline(f'P1 d-cell {F4N[d]}', cn, n, 1 / 16, '1/16')
        okp1.append(o)
        out.append(s)
        o, s = bline(f'  B3 w(B0)=10 | d={F4N[d]}', c['b3'][d][0], cn, 3 / 4, '3/4')
        okb3.append(o)
        out.append(s)
        o, s = bline(f'  B3 w(B0)>=11 | d={F4N[d]}', c['b3'][d][1], cn, 1 / 4, '1/4')
        okb3.append(o)
        out.append(s)
        out.append(f"    [info] dig(B0)@10 hist (codes 0..3): {c['digB0at10'][d]}")
        st = c['stages'][d]
        out.append(f'    stage hist (3*v1(C0), 33 = lump >= 33): '
                   f'{dict(sorted(st.items()))}; <28: {0}')
        s29 = st.get(29, 0)
        o, s = bline(f'  PD1 stage-29 | d={F4N[d]}', s29, cn, 3 / 4, '3/4')
        okpd1.append(o)
        out.append(s)
        for u in (1, 2, 3):
            o, s = bline(f'    u-cell {F4N[u]} | d={F4N[d]}', c['joint'][d][u],
                         cn, 1 / 4, '1/4')
            okpd1.append(o)
            out.append(s)
        o, s = bline(f'  PD4 deeper (stage>=30) | d={F4N[d]}', cn - s29, cn,
                     1 / 4, '1/4')
        okpd4.append(o)
        out.append(s)
        out.append(f"    c01 raw digit pair at frame-2 labels (2,7),(3,6) "
                   f"[(lvl7 of c01c, lvl6 of c01x)]: {c['c01pairs'][d]}")
    v['P1'] = v['F5'] = all(okp1)
    v['B3'] = all(okb3)
    v['PD1'] = all(okpd1)
    v['PD4'] = all(okpd4)
    out.append('\n== P3 joint (d,u) cells (sealed 1/64 each, d indep u):')
    okp3 = []
    for d in (1, 2, 3):
        for u in (1, 2, 3):
            o, s = bline(f'({F4N[d]},{F4N[u]})', c['joint'][d][u], n,
                         1 / 64, '1/64')
            okp3.append(o)
            out.append(s)
    v['P3'] = v['F7'] = all(okp3) and all(okpd1)
    v['F6'] = all(okp1) and all(okpd1) and all(okp3)
    out.append('\n== EXACT-ZERO FALSIFIERS (one hit kills the gate):')
    out.append(f"  F1 (NU1 member with w(B0) < 10, =B1):        {c['F1']}")
    out.append(f"  F2 (NU1 member at stage 28, =PD0/C-WW):      {c['F2']}"
               + (f'  examples {c["F2_ex"]}' if c['F2_ex'] else ''))
    out.append(f"  F3 (B1 digits at (2,7),(3,6) differ from d): {c['F3']}"
               + (f'  examples {c["F3_ex"]}' if c['F3_ex'] else ''))
    out.append(f"  F4 ([1,4] emission with beta pair alive):    {c['F4']}")
    out.append('  [reading note] F3/PD2 occupancy is graded on the digits of B1 '
               '(frame 1, where nu1 pinned the labels (2,7),(3,6)); the frame-2 '
               'referent of the same labels, the c01 pair (printed per cell '
               'above), is the D.8-carry exhibit: the realizer division '
               'transports d and the naive labels come back CANCELLED — '
               'constancy per cell is required, its value is reported verbatim.')
    out.append(f"  [info] stage < 28 (floor break, would kill PD1): {c['lt28']}; "
               f"w(c00) < 10: {c['wc00bad']}; C1 vertex (1,7/3) not inherited: "
               f"{c['c1inh_bad']}")
    v['B1'] = v['F1'] = c['F1'] == 0
    v['B2'] = c['F4'] == 0
    v['F4'] = c['F4'] == 0
    v['PD0'] = v['F2'] = c['F2'] == 0 and c['lt28'] == 0
    v['F3'] = c['F3'] == 0
    v['PD2'] = c['F3'] == 0 and all(okpd1)   # nominal count 2 = the one F4 u-digit
    v['F8'] = all(okws) and ok4[0]
    out.append('\n== WRONG-TAU DISCRIMINANT PROBE (first '
               f"{c['nprobed']} NU1 members; realizer replaced by tau' != d; "
               'theory: stage 28 on every member — the naive line-staircase '
               'reading; NOT sealed, control exhibit):')
    for tau in range(4):
        np_, hits = c['probe'][tau]
        if np_:
            out.append(f"  tau' = {F4N[tau]:4s}: probed {np_}, stage-28 hits "
                       f"{hits} ({hits / np_:.4f})")
    return v


def main():
    t0 = time.time()
    os.makedirs(os.path.dirname(OUTPATH), exist_ok=True)
    out = ['SEALED CASE-L GATE CENSUS, p = 2 (predictions: '
           'CASE_L_SEALED_PREDICTIONS_2026-07-26.md, committed before this '
           'script existed)',
           f'n = 9 monic, N = {N} (mod {M2}), root stratum = R0-pattern '
           f'(R0 = z^8+z^4+1), M = {MSAMP}, seed {SEED}',
           f'history: nu0 side [0,8] slope 1 / Phi0 = x^2+2x+4; nu1 side [1,4] '
           f'slope 7/3 (beta-probe); nu2 tail read at stage 29',
           f'Phi1(d) = Phi0^3 + 64*d_x*x + 128*d_c; Phi0^3 mod {M2} = '
           f'{PHI0CUBED}']
    info = verification_pass(out)
    t1 = time.time()
    c = census()
    t2 = time.time()
    out.append(f'\n(census {t2 - t1:.0f}s for {MSAMP} members incl. per-member '
               f'cap-11 reclassification)')
    v = evaluate(c, out)
    out.append(f"\n== CAP STABILITY: members whose sealed classification tuple "
               f"differs between mod 2^{N} and mod 2^{NCAP2}: {c['capbad']}"
               + (f"  examples {c['cap_ex']}" if c['cap_ex'] else ''))
    order = ['P1', 'P2', 'P3', 'P4', 'B1', 'B2', 'B3', 'B4', 'PD0', 'PD1',
             'PD2', 'PD4', 'C-WS', 'F1', 'F2', 'F3', 'F4', 'F5', 'F6', 'F7',
             'F8']
    summary = ['=' * 72,
               f"SUMMARY — SEALED CASE-L GATE p=2 (M = {MSAMP}, NU1 total "
               f"{sum(c['nu1'][1:])}, WS total {sum(c['ws'][1:])}, DEEP "
               f"{c['deep']}, OTHER {c['other']}):",
               'closed forms: Phi0-tower sign B mismatches '
               f"{info['misB']}/{info['nsub']}, sign A {info['misA']}/"
               f"{info['nsub']}, reconstruction fails {info['recbad']}; "
               f"Phi1 division mismatches {info['mis1']}/{info['n1']}, "
               f"reconstruction fails {info['rec1bad']}, expansion "
               f"mismatches {info['misc']}"]
    summary += [f"{k}: {'PASS' if v[k] else 'FAIL'}" for k in order]
    summary += [f"cap stability: {c['capbad']} differing members; wall time "
                f'{time.time() - t0:.0f}s', '=' * 72]
    out.extend(summary)
    with open(OUTPATH, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    print('\n'.join(summary))
    return 0


if __name__ == '__main__':
    sys.exit(main())
