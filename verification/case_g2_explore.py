#!/usr/bin/env python3
"""case_g2_explore.py — EXPLORATORY census of the ORDER-2 INTERIOR of Case G.
RAW DATA ONLY: no pass/fail gates are pre-registered; nothing here is a proof.
(Extends the committed case_g_gate.py one level down the phi2-tower. DO NOT COMMIT.)

Setting (n = 4, p = 2, N = 10; all arithmetic mod 2^10 = 1024):
  Case-G stratum: monic quartics f = x^4 + a3 x^3 + a2 x^2 + a1 x + a0 with
    v(a3) >= 1, v(a2) >= 2, v(a1) >= 2, v(a0) = 2 EXACT with a0/4 odd  (v = v_2).
  Order-2 key: phi2 = x^2 - 2.
  phi2-development: f = phi2^2 + B1*phi2 + B0, deg B_i <= 1, each B_i recorded as
    its (x-coeff, const) pair.
  LEVEL-1 WEIGHT (doubled integer scale), for b = b1*x + b0 with deg <= 1:
    w1(b) := min(2*v2(b0), 2*v2(b1) + 1), +infinity capped at 2N = 20.
    (2*v2(b0) is even, 2*v2(b1)+1 odd, so below the cap exactly one slot achieves
    the min: the const slot iff w1 is even, the x slot iff w1 is odd.)

FREE-DIGIT CAP (stated, per spec): the cap IS NEEDED — the uncapped stratum mod 2^10
has 2^(9+8+8+7) = 2^32 members. Each coefficient keeps its 6 lowest FREE digits:
    a3 = 2*t3, a2 = 4*t2, a1 = 4*t1, a0 = 4*(2s+1) = 8s + 4,
    with t3, t2, t1, s in [0, 2^6)
(digit windows: a3 heights 1..6, a2 heights 2..7, a1 heights 2..7, a0 heights 3..8
with the height-2 digit of a0 forced to 1; all higher digits 0). Enumerated members:
2^24 = 16777216. Every sub-stratum condition probed below reads digits at heights
<= 5, well inside the cap window; a full re-census at cap 5 is run and compared
cell-by-cell as a cap-stability record (raw). Deep tail cells of the tables (large
w1 values) ARE cap-truncation-biased (e.g. a coefficient with all capped digits 0
reports v = N); that bias is recorded, not corrected.

Development closed form (used in the bulk loops for speed; VERIFIED member-by-member
against genuine two-step polynomial division — develop_polydiv, the same two-division
routine as case_g_gate.py — on (a) the FULL cap-4 stratum, 2^16 members x all 4 keys,
(b) a stride-4999 slice of the cap-6 stratum x all 4 keys, (c) 500 seeded-random
points of the FULL box x all 4 keys; plus reconstruction f == phi^2 + B1*phi + B0
mod 2^N at all the same points):
  dividing f twice by the monic key phi = x^2 - alpha*x - beta gives
    c1 = a3 + alpha,  d2 = a2 + beta + alpha*c1,
    B1 = ( a3 + 2*alpha ,  d2 + beta )                      as (x-coeff, const),
    B0 = ( a1 + beta*c1 + alpha*d2 ,  a0 + beta*d2 )        as (x-coeff, const).
  Base key phi2 = x^2 - 2: (alpha, beta) = (0, 2).
  Recentered key phi2' = phi2 - t, t = tau1*x + tau0: (alpha, beta) = (tau1, 2+tau0).

REPORTS (all raw):
 (1) joint distribution of (w1(B1), w1(B0)) on the stratum (table folded at 14;
     uncapped marginals also printed).
 (2) per value W0 of w1(B0): the LEADING w1-digit data of B0 — which slot achieves
     the min (const iff W0 even, x iff W0 odd) and the mod-2 digit of the achieving
     coordinate at its valuation (coordinate >> v, & 1).
 (3) RECENTERING PROBE on {w1(B0) = 6 exact AND w1(B1) >= 4}: re-develop f at
     phi2' = phi2 - t for t in {4, 2x, 2x+4} (w1(t) printed per candidate); per
     candidate the joint (w1(B1'), w1(B0')) table; FLAG = does the candidate give
     w1(B0') >= 8 uniformly (strict rise).
 (4) the same probe on the CONTROL {w1(B0) = 5 exact AND w1(B1) >= 4} (odd W0; the
     "same probe" is read as keeping the w1(B1) >= 4 leg — the plain w1(B0)=5 count
     is also reported in (5)).
 (5) member counts and exact masses of every sub-stratum touched (fractions of the
     capped stratum, and absolute box mass via the stratum's nominal mass 2^-8).

Run:  python3 case_g2_explore.py            (full: cap 6 + cap-5 stability; ~1-2 min)
      python3 case_g2_explore.py --quick    (cap 4 + cap-3 stability; seconds)
"""
import random
import sys
import time
from collections import Counter
from fractions import Fraction as Frac

N = 10                     # working precision: everything mod 2^N
M = 1 << N
MASK = M - 1
WCAP = 2 * N               # +infinity cap for w1 (doubled scale)
TABCAP = 14                # display fold for joint tables (per spec)

# recentering candidates: (label, tau1, tau0) with t = tau1*x + tau0
CANDS = [('t = 4', 0, 4), ('t = 2x', 2, 0), ('t = 2x + 4', 2, 4)]
# phi2' = phi2 - t = x^2 - tau1*x - (2 + tau0)  ->  (alpha, beta) = (tau1, 2 + tau0)
CAND_AB = [(tau1, 2 + tau0) for _, tau1, tau0 in CANDS]
ALL_KEYS = [(0, 2)] + CAND_AB          # base key first


# --------------------------------------------------------------- p-adic helpers

def vp2(x, cap=N):
    """2-adic valuation of the residue x mod 2^cap; v(0) reported as cap."""
    if x == 0:
        return cap
    v = (x & -x).bit_length() - 1
    return v if v < cap else cap


def w1_pair(bx, bc):
    """w1 of b = bx*x + bc (doubled scale), capped at 2N."""
    return min(2 * vp2(bc), 2 * vp2(bx) + 1, WCAP)


def polydiv(f, d, Mod):
    """f, d coefficient lists (low->high), d monic. (q, r) with f = q*d + r mod Mod."""
    f = list(f)
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % Mod
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % Mod
    return q, [x % Mod for x in f[:dd]]


def polymul(A, B, Mod):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % Mod
    return R


def develop_polydiv(coeffs, phi, Mod):
    """GENUINE two-division phi-development (same routine as case_g_gate.develop):
    f = phi^2 + B1*phi + B0; returns ((B1.x, B1.c), (B0.x, B0.c))."""
    c3, c2, c1, c0 = coeffs
    q1, r0 = polydiv([c0, c1, c2, c3, 1], phi, Mod)
    q2, r1 = polydiv(q1, phi, Mod)
    assert q2 == [1]
    return (r1[1], r1[0]), (r0[1], r0[0])


def develop_closed(a3, a2, a1, a0, alpha, beta):
    """Closed form of the same development for phi = x^2 - alpha*x - beta (mod 2^N)."""
    c1 = a3 + alpha
    d2 = a2 + beta + alpha * c1
    return ((a3 + 2 * alpha) % M, (d2 + beta) % M), \
           ((a1 + beta * c1 + alpha * d2) % M, (a0 + beta * d2) % M)


# --------------------------------------------------------------- verification

def check_one(f4):
    """closed form == genuine polydiv development, all 4 keys, + reconstruction."""
    a3, a2, a1, a0 = (x % M for x in f4)
    for alpha, beta in ALL_KEYS:
        phi = [(-beta) % M, (-alpha) % M, 1]
        gd = develop_polydiv((a3, a2, a1, a0), phi, M)
        cf = develop_closed(a3, a2, a1, a0, alpha, beta)
        assert gd == cf, ('closed-form mismatch', f4, alpha, beta, gd, cf)
        (b1x, b1c), (b0x, b0c) = cf
        lhs = polymul(phi, phi, M)
        tt = polymul([b1c, b1x], phi, M)
        b0l = (b0c, b0x)
        rec = [(lhs[i] + (tt[i] if i < len(tt) else 0)
                + (b0l[i] if i < 2 else 0)) % M for i in range(5)]
        assert rec == [a0, a1, a2, a3, 1], ('reconstruction failure', f4, alpha, beta)


def verify(capmain):
    """(a) full cap-4 stratum; (b) strided capmain stratum; (c) 500 random box pts."""
    n_a = 0
    Tc = 1 << 4
    for t3 in range(Tc):
        for t2 in range(Tc):
            for t1 in range(Tc):
                for s in range(Tc):
                    check_one((2 * t3, 4 * t2, 4 * t1, 8 * s + 4))
                    n_a += 1
    n_b = 0
    T = 1 << capmain
    tot = T ** 4
    for i in range(0, tot, 4999):
        s = i & (T - 1)
        t1 = (i >> capmain) & (T - 1)
        t2 = (i >> 2 * capmain) & (T - 1)
        t3 = (i >> 3 * capmain) & (T - 1)
        check_one((2 * t3, 4 * t2, 4 * t1, 8 * s + 4))
        n_b += 1
    rng = random.Random(20260724)
    n_c = 0
    for _ in range(500):
        check_one(tuple(rng.randrange(M) for _ in range(4)))
        n_c += 1
    return n_a, n_b, n_c


# --------------------------------------------------------------- the census

def census(capfree):
    """One full pass over the capped stratum. Returns:
      joint  : flat 21x21, idx = w1(B1)*21 + w1(B0)      (base development)
      lead   : flat 21x4, idx = W0*4 + slot*2 + digit    (slot 0=const, 1=x)
      tbl6   : per candidate, flat 21x21 (w1(B1'), w1(B0')) on {W0=6 & w1(B1)>=4}
      tbl5   : same on the control {W0=5 & w1(B1)>=4}
      n6, n5 : the two probe sub-stratum counts;  total = (2^capfree)^4."""
    T = 1 << capfree
    vt = [0] * M
    vt[0] = N
    for x in range(1, M):
        vt[x] = (x & -x).bit_length() - 1
    vt2 = [2 * v for v in vt]            # const-slot weight (20 for coordinate 0)
    vtx = [2 * v + 1 for v in vt]        # x-slot weight (21 for coordinate 0)
    joint = [0] * (21 * 21)
    lead = [0] * (21 * 4)
    tbl6 = [[0] * (21 * 21) for _ in CANDS]
    tbl5 = [[0] * (21 * 21) for _ in CANDS]
    n6 = n5 = 0
    for t3 in range(T):
        a3 = 2 * t3
        wb1x = vtx[a3]
        ta3 = (2 * a3) & MASK
        for t2 in range(T):
            a2 = 4 * t2
            b1c = (a2 + 4) & MASK
            w1B1 = wb1x if wb1x < vt2[b1c] else vt2[b1c]
            if w1B1 > WCAP:
                w1B1 = WCAP
            row = w1B1 * 21
            ge4 = w1B1 >= 4
            Kc = (2 * a2 + 8) & MASK               # base B0.c = 8s + Kc
            cst = []                               # candidate hoists (per t3,t2)
            for ci in range(3):
                alpha, beta = CAND_AB[ci]
                c1 = a3 + alpha
                d2 = a2 + beta + alpha * c1
                b1xp = (a3 + 2 * alpha) & MASK
                b1cp = (d2 + beta) & MASK
                wB1p = vtx[b1xp] if vtx[b1xp] < vt2[b1cp] else vt2[b1cp]
                if wB1p > WCAP:
                    wB1p = WCAP
                cst.append((wB1p * 21, (beta * c1 + alpha * d2) & MASK,
                            (4 + beta * d2) & MASK, tbl6[ci], tbl5[ci]))
            for t1 in range(T):
                a1 = 4 * t1
                b0x = (a1 + ta3) & MASK            # base B0.x (s-independent)
                wx = vtx[b0x]
                xdig = 2 + ((b0x >> (wx >> 1)) & 1) if b0x else 0   # unused if b0x=0
                cst1 = [(rowp, vtx[(a1 + K1) & MASK], K0, t6, t5)
                        for (rowp, K1, K0, t6, t5) in cst]
                for s8 in range(0, 8 * T, 8):
                    b0c = (s8 + Kc) & MASK
                    vc2 = vt2[b0c]
                    if vc2 < wx:                   # const slot achieves (even w1)
                        w0 = vc2
                        lead[w0 * 4 + ((b0c >> (vc2 >> 1)) & 1)] += 1
                    else:                          # x slot achieves (odd w1)
                        w0 = wx
                        lead[w0 * 4 + xdig] += 1
                    joint[row + w0] += 1
                    if ge4:
                        if w0 == 6:
                            n6 += 1
                            for rowp, wxp, K0, t6, t5 in cst1:
                                b0cp = (s8 + K0) & MASK
                                v2p = vt2[b0cp]
                                w0p = v2p if v2p < wxp else \
                                    (wxp if wxp <= WCAP else WCAP)
                                t6[rowp + w0p] += 1
                        elif w0 == 5:
                            n5 += 1
                            for rowp, wxp, K0, t6, t5 in cst1:
                                b0cp = (s8 + K0) & MASK
                                v2p = vt2[b0cp]
                                w0p = v2p if v2p < wxp else \
                                    (wxp if wxp <= WCAP else WCAP)
                                t5[rowp + w0p] += 1
    return dict(joint=joint, lead=lead, tbl6=tbl6, tbl5=tbl5,
                n6=n6, n5=n5, total=T ** 4)


# --------------------------------------------------------------- reporting

def lab(v):
    return f'>={TABCAP}' if v == TABCAP else str(v)


def fold_joint(tbl):
    d = Counter()
    for r in range(21):
        base = r * 21
        for c in range(21):
            n = tbl[base + c]
            if n:
                d[(min(r, TABCAP), min(c, TABCAP))] += n
    return d


def print_joint(tbl, rowname, colname, indent='    '):
    d = fold_joint(tbl)
    if not d:
        print(indent + '(empty)')
        return
    rows = sorted({r for r, _ in d})
    cols = sorted({c for _, c in d})
    print(f'{indent}rows = {rowname} (down); cols = {colname} (across); '
          f'entries = member counts; >= {TABCAP} folded into the {TABCAP} line')
    print(indent + ' ' * 6 + ''.join(f'{lab(c):>9}' for c in cols))
    for r in rows:
        print(indent + f'{lab(r):<6}'
              + ''.join(f'{d.get((r, c), 0):>9}' for c in cols))


def marg(tbl, axis):
    m = Counter()
    for r in range(21):
        for c in range(21):
            n = tbl[r * 21 + c]
            if n:
                m[(r, c)[axis]] += n
    return dict(sorted(m.items()))


def report_probe(tblset, count, sub_name):
    for (labl, tau1, tau0), tbl in zip(CANDS, tblset):
        tot = sum(tbl)
        assert tot == count, (sub_name, labl, tot, count)
        m0 = marg(tbl, 1)
        mn, mx = min(m0), max(m0)
        ge8 = sum(n for w, n in m0.items() if w >= 8)
        print(f'\n  candidate {labl}  (w1(t) = {w1_pair(tau1, tau0)}) '
              f'on {sub_name} ({count} members):')
        print_joint(tbl, "w1(B1')", "w1(B0')")
        print(f"    w1(B0') marginal (uncapped): {m0}")
        print(f"    w1(B0') attained min {mn}, max {mx}; "
              f"fraction >= 8: {ge8}/{tot} = {Frac(ge8, tot) if tot else '-'}")
        print(f"    STRICT-RISE FLAG (w1(B0') >= 8 uniformly): "
              f"{'YES' if mn >= 8 else 'no'}")


def mass_str(cnt, total):
    fr = Frac(cnt, total)
    ab = fr * Frac(1, 256)
    def p2(x):
        return (x.numerator == 1 and (x.denominator & (x.denominator - 1)) == 0)
    tail = f' = 2^-{x.denominator.bit_length() - 1}' if p2(x := ab) else ''
    return (f'count {cnt}; fraction of capped stratum {fr}; '
            f'absolute box mass {fr} * 2^-8 = {ab}{tail}')


# --------------------------------------------------------------- main

def main(argv):
    quick = '--quick' in argv
    capmain, capchk = (4, 3) if quick else (6, 5)
    t_start = time.time()
    print('=' * 78)
    print('CASE G2 EXPLORE — ORDER-2 INTERIOR of Case G (n = 4, p = 2) — RAW CENSUS')
    print('=' * 78)
    print(f'N = {N} (all arithmetic mod 2^{N} = {M}); '
          f'w1(b1*x + b0) = min(2*v2(b0), 2*v2(b1)+1), inf-capped at 2N = {WCAP}.')
    print('Stratum: v(a3)>=1, v(a2)>=2, v(a1)>=2, v(a0)=2 exact (a0/4 odd); '
          'key phi2 = x^2 - 2.')
    print(f'FREE-DIGIT CAP: {capmain} free digits per coefficient '
          f'(NEEDED: uncapped stratum mod 2^{N} has 2^32 members).')
    print(f'  a3 = 2*t3, a2 = 4*t2, a1 = 4*t1, a0 = 8*s + 4;  '
          f't3,t2,t1,s in [0, 2^{capmain})  ->  2^{4 * capmain} members.')
    print('\nRecentering candidates (phi2\' = phi2 - t = x^2 - tau1*x - (2 + tau0)):')
    for (labl, tau1, tau0), (alpha, beta) in zip(CANDS, CAND_AB):
        print(f'  {labl:10s}: w1(t) = {w1_pair(tau1, tau0)};   '
              f'phi2\' = x^2 - {alpha}*x - {beta}')

    print('\nVERIFICATION (closed-form development == genuine two-step polydiv, '
          'all 4 keys,\n  + reconstruction f == phi^2 + B1*phi + B0 mod 2^N):')
    n_a, n_b, n_c = verify(capmain)
    print(f'  (a) FULL cap-4 stratum: {n_a} members x 4 keys — all OK')
    print(f'  (b) stride-4999 slice of the cap-{capmain} stratum: {n_b} members '
          f'x 4 keys — all OK')
    print(f'  (c) 500 seeded-random points of the full box: {n_c} members '
          f'x 4 keys — all OK')

    print(f'\nMain census at cap {capmain} ...', flush=True)
    r = census(capmain)
    total = r['total']
    joint, lead = r['joint'], r['lead']
    assert sum(joint) == total
    # internal consistency: probe counts vs the joint table columns
    chk6 = sum(joint[rr * 21 + 6] for rr in range(4, 21))
    chk5 = sum(joint[rr * 21 + 5] for rr in range(4, 21))
    assert chk6 == r['n6'] and chk5 == r['n5'], (chk6, r['n6'], chk5, r['n5'])
    print(f'  done in {time.time() - t_start:.1f}s; {total} members; '
          f'probe counts consistent with the joint table (col 6 rows>=4: {chk6}; '
          f'col 5 rows>=4: {chk5})')

    # ---------------- (1)
    print('\n' + '-' * 78)
    print('(1) JOINT DISTRIBUTION of (w1(B1), w1(B0)) on the capped stratum:')
    print_joint(joint, 'w1(B1)', 'w1(B0)', indent='  ')
    print(f'  w1(B1) marginal (uncapped): {marg(joint, 0)}')
    print(f'  w1(B0) marginal (uncapped): {marg(joint, 1)}')

    # ---------------- (2)
    print('\n' + '-' * 78)
    print('(2) LEADING w1-DIGIT DATA of B0 per W0 = w1(B0):')
    print('    achieving slot: const iff 2*v2(B0.const) = W0 (W0 even), '
          'x iff 2*v2(B0.x)+1 = W0 (W0 odd);')
    print('    digit = mod-2 digit of the achieving coordinate at its valuation '
          '(coordinate >> v & 1).')
    print(f'    {"W0":>4} {"count":>10} {"const,dig0":>11} {"const,dig1":>11} '
          f'{"x,dig0":>9} {"x,dig1":>9}')
    for w0 in range(21):
        row = lead[w0 * 4: w0 * 4 + 4]
        tot = sum(row)
        if tot == 0:
            continue
        print(f'    {w0:>4} {tot:>10} {row[0]:>11} {row[1]:>11} '
              f'{row[2]:>9} {row[3]:>9}')

    # ---------------- (3)
    print('\n' + '-' * 78)
    print('(3) RECENTERING PROBE on {w1(B0) = 6 exact AND w1(B1) >= 4} '
          f'({r["n6"]} members):')
    print('    re-development at phi2\' = phi2 - t; per candidate the joint '
          '(w1(B1\'), w1(B0\')).')
    report_probe(r['tbl6'], r['n6'], '{w1(B0)=6 & w1(B1)>=4}')

    # ---------------- (4)
    print('\n' + '-' * 78)
    print('(4) CONTROL: the same probe on {w1(B0) = 5 exact AND w1(B1) >= 4} '
          f'({r["n5"]} members; odd W0):')
    report_probe(r['tbl5'], r['n5'], '{w1(B0)=5 & w1(B1)>=4}')

    # ---------------- (5)
    print('\n' + '-' * 78)
    print(f'(5) MEMBER COUNTS AND EXACT MASSES (capped stratum total '
          f'2^{4 * capmain} = {total}; stratum nominal box mass 2^-8):')
    print(f'  full capped stratum: {mass_str(total, total)}')
    mB0 = marg(joint, 1)
    for w0v, cnt in mB0.items():
        print(f'  {{w1(B0) = {w0v}}}: {mass_str(cnt, total)}')
    print(f'  probe   {{w1(B0)=6 exact & w1(B1)>=4}}: {mass_str(r["n6"], total)}')
    print(f'  control {{w1(B0)=5 exact & w1(B1)>=4}}: {mass_str(r["n5"], total)}')

    # ---------------- cap-stability record
    print('\n' + '-' * 78)
    print(f'CAP-STABILITY RECORD (full re-census at cap {capchk}; scale factor '
          f'{(1 << (capmain - capchk)) ** 4} per cell):')
    r2 = census(capchk)
    total2 = r2['total']
    scale = total // total2
    same6 = Frac(r['n6'], total) == Frac(r2['n6'], total2)
    same5 = Frac(r['n5'], total) == Frac(r2['n5'], total2)
    print(f'  probe   fraction: cap{capmain} {Frac(r["n6"], total)} vs '
          f'cap{capchk} {Frac(r2["n6"], total2)}  '
          f'[{"EQUAL" if same6 else "DIFFERENT"}]')
    print(f'  control fraction: cap{capmain} {Frac(r["n5"], total)} vs '
          f'cap{capchk} {Frac(r2["n5"], total2)}  '
          f'[{"EQUAL" if same5 else "DIFFERENT"}]')
    diffs = [(i // 21, i % 21, joint[i], scale * r2['joint'][i])
             for i in range(21 * 21) if joint[i] != scale * r2['joint'][i]]
    if diffs:
        mm = sum(abs(a - b) for _, _, a, b in diffs)
        print(f'  joint-table cells with cap{capmain} != {scale} * cap{capchk}: '
              f'{len(diffs)} cells; min w1(B1) among them '
              f'{min(d[0] for d in diffs)}, min w1(B0) among them '
              f'{min(d[1] for d in diffs)}; total |count diff| {mm} '
              f'(cap-truncation tail, recorded raw)')
    else:
        print('  joint-table cells: ALL cells scale exactly')
    for nm, key in (('probe', 'tbl6'), ('control', 'tbl5')):
        for ci, (labl, _, _) in enumerate(CANDS):
            t6a, t6b = r[key][ci], r2[key][ci]
            nd = sum(1 for i in range(21 * 21) if t6a[i] != scale * t6b[i])
            print(f'  {nm} candidate {labl}: cells with cap{capmain} != '
                  f'{scale} * cap{capchk}: {nd}')

    print(f'\ntotal wall time {time.time() - t_start:.1f}s')
    print('END OF RAW CENSUS (exploratory; no verdicts).')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
