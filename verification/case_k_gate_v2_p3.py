#!/usr/bin/env python3
"""case_k_gate_v2_p3.py — SEALED Case-K v2 gate census at p = 3 (FRESH SUB', F9).

Predictions preregistered in CASE_K_SEALED_PREDICTIONS_V2_2026-07-26.md (committed
BEFORE this script was written or run).  This script is the CENSUS: it compares the
data against Q1..Q6 and reports PASS/FAIL with exact counts; it never adjusts a
prediction; a FAIL is a valid outcome to report verbatim.

Configuration (mod 3^12; v = v_3): parent stratum EXACTLY as v1 (case_k_gate_p3.py):
monic quartics a3 = 9*t3, a2 = 18 + 27*t2, a1 = 81*t1, a0 = 81 + 243*s, each slot
keeping its lowest `cap` free base-3 digits.  Key Phi = x^2 + 9; development
f = Phi^2 + B1*Phi + B0 via the closed form for phi = x^2 - alpha*x - beta:
  c1 = a3 + alpha; d2 = a2 + beta + alpha*c1; B1 = (a3 + 2*alpha, d2 + beta);
  B0 = (a1 + beta*c1 + alpha*d2, a0 + beta*d2)   [pairs are (x-coeff, const)].
Base key (alpha, beta) = (0, -9).  Recentered key Phi' = Phi - t, t = tau1*x + tau0,
implemented as (alpha, beta) = (tau1, tau0 - 9) ["sign B"]; the alternative
(tau1, -9 - tau0) ["sign A"] is tested against genuine polynomial division by the
LITERAL Phi - t on >= 1000 members (as in v1); the winner is reported.
w(B) = min(v(b0), v(b1)+1) cap 12; F9 = F3[zb]/(zb^2+1); the digit of B = b1*x + b0
at m = w(B) is eps_x*zb + eps_c (code 3*eps_x + eps_c), eps_c = digit_m(b0) if
v(b0) = m else 0, eps_x = digit_{m-1}(b1) if v(b1) = m - 1 else 0.

FRESH SUB' = {w(B0) = 8 exact, w(B1) = 4 exact}; cells (d1, d0) in F9* x F9* (64).
Weight-4 candidates t = 27*c1*x + 81*c0, (c1,c0) in {0,1,2}^2 \\ {(0,0)}, digit
tau = c1*zb + c0; wrong-weight controls t = 27 (w3), t = 243 (w5); Q6 lift pairs
(t vs t + 243):  27x vs 27x+243,  and  27x+81 vs 27x+81+243.

CAP JUSTIFICATION (heights through 10 with margin): the deepest bucket any
prediction reads is w(B0') >= 10 (Q3 'deeper'); w(B0') = min(v(b0c'), v(b0x')+1)
with b0c' = 243*s + const and b0x' = 81*t1 + const inside a (t3,t2)-block, so
height 10 needs v(s + k) and v(t1 + k') resolved through level 5.  cap = 6 frees
base-3 digits 0..5 of every slot, resolving both EXACTLY through 5: all heights
<= 10 are exact and the only unresolved lump is >= 11, which no prediction reads.
The deepest digit actually read (the Q3 fresh digit at height 9 resp. 8) sits at
slot-digit level 4 — one full free level of margin under the cap.  The B1' side is
block-exact mod 3^12 (t3, t2 enter with all their digits; no truncation).
Cap-stability: full re-census at cap 5 (heights <= 9 exact + a >= 10 lump — still
exact for every Q1..Q6 bucket); verdicts and mass fractions must agree.

Run:  python3 case_k_gate_v2_p3.py
      (all tables -> results/case_k_gate_v2_p3_output.txt; short summary on stdout)
"""
import os
import random
import sys
import time
from fractions import Fraction as Frac

P, N = 3, 12
M = P ** N                       # 531441
NW = N + 1
CAP_MAIN, CAP_CHK = 6, 5
OUTPATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'results', 'case_k_gate_v2_p3_output.txt')

VT = [0] * M                     # v_3 of the residue, capped at N (v(0) = N)
LD = [0] * M                     # leading digit at height VT[y] (0 for y = 0)
VT[0] = N
for y in range(1, M):
    if y % 3:
        VT[y], LD[y] = 0, y % 3
    else:
        VT[y], LD[y] = min(VT[y // 3] + 1, N), LD[y // 3]

F9N = ['0', '1', '2', 'zb', 'zb+1', 'zb+2', '2zb', '2zb+1', '2zb+2']


def f9add(a, b):
    return 3 * ((a // 3 + b // 3) % 3) + (a % 3 + b % 3) % 3


def f9mul(a, b):
    ax, ac, bx, bc = a // 3, a % 3, b // 3, b % 3
    return 3 * ((ax * bc + ac * bx) % 3) + (ac * bc + 2 * ax * bx) % 3


def r2_at(tau, d1, d0):          # R2(tau) = tau^2 + d1*tau + d0 in F9
    return f9add(f9add(f9mul(tau, tau), f9mul(d1, tau)), d0)


def r2p_at(tau, d1):             # R2'(tau) = 2*tau + d1 in F9
    return f9add(f9add(tau, tau), d1)


# keys: (label, tau1, tau0, kind, taucode); base, 8 weight-4 candidates, 2
# wrong-weight controls, 2 lifts (t + 243).  Phi' = Phi - t <-> (tau1, tau0-9).
ALLKEYS = [('t=0 (base)', 0, 0, 'base', 0)]
for c1 in range(3):
    for c0 in range(3):
        if c1 or c0:
            ALLKEYS.append((f't=27x*{c1}+81*{c0} (tau={F9N[3 * c1 + c0]})',
                            27 * c1, 81 * c0, 'w4', 3 * c1 + c0))
ALLKEYS += [('t=27 (w3 ctrl)', 0, 27, 'ctrl3', None),
            ('t=243 (w5 ctrl)', 0, 243, 'ctrl5', None),
            ('t=27x+243 (lift of k3)', 27, 243, 'lift', 3),
            ('t=27x+81+243 (lift of k4)', 27, 324, 'lift', 4)]
NK = len(ALLKEYS)                # 13
LIFTPAIRS = [(3, 11), (4, 12)]   # (original k, lifted k = original + 243)


def polydiv(f, d):
    f = list(f)
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % M
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % M
    return q, [x % M for x in f[:dd]]


def polymul(A, B):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % M
    return R


def develop_polydiv(coefs, phi):
    c3, c2, c1, c0 = coefs
    q1, r0 = polydiv([c0, c1, c2, c3, 1], phi)
    q2, r1 = polydiv(q1, phi)
    assert q2 == [1]
    return (r1[1], r1[0]), (r0[1], r0[0])


def develop_closed(a3, a2, a1, a0, al, be):
    c1 = a3 + al
    d2 = a2 + be + al * c1
    return ((a3 + 2 * al) % M, (d2 + be) % M), \
           ((a1 + be * c1 + al * d2) % M, (a0 + be * d2) % M)


def coeffs(t3, t2, t1, s):
    return ((9 * t3) % M, (18 + 27 * t2) % M, (81 * t1) % M, (81 + 243 * s) % M)


def sign_check():
    """Genuine division by the LITERAL polynomial Phi - t vs the closed form under
    both sign options, on 1000 stratum members + 200 random box points, all 13 keys.
    Also reconstruction f == (Phi-t)^2 + B1'*(Phi-t) + B0' mod 3^N under sign B."""
    rng = random.Random(20260726)
    mem = [coeffs(*(rng.randrange(3 ** 6) for _ in range(4))) for _ in range(1000)]
    mem += [tuple(rng.randrange(M) for _ in range(4)) for _ in range(200)]
    misA = misB = recbad = napp = 0
    for f in mem:
        a3, a2, a1, a0 = f
        for lab, tau1, tau0, kind, tc in ALLKEYS:
            phi = [(9 - tau0) % M, (-tau1) % M, 1]        # literal Phi - t
            gd = develop_polydiv(f, phi)
            cB = develop_closed(a3, a2, a1, a0, tau1 % M, (tau0 - 9) % M)
            if gd != cB:
                misB += 1
            if tau0 % M != (-tau0) % M:                   # sign A distinguishable
                napp += 1
                cA = develop_closed(a3, a2, a1, a0, tau1 % M, (-9 - tau0) % M)
                if gd != cA:
                    misA += 1
            (b1x, b1c), (b0x, b0c) = cB
            rec = [x % M for x in polymul(phi, phi)]
            t2_ = polymul([b1c, b1x], phi)
            for i, cc in enumerate(t2_):
                rec[i] = (rec[i] + cc) % M
            rec[0] = (rec[0] + b0c) % M
            rec[1] = (rec[1] + b0x) % M
            if rec != [a0, a1, a2, a3, 1]:
                recbad += 1
    return len(mem), misB, misA, napp, recbad


def census(cap):
    """Full pass over the capped stratum.  With alpha = 0 for the base key the
    x-side data (b1x, kx) depend only on t3 and the const side (b1c, kc) only on
    t2, so the base valuation histograms are precomputed per slot; SUB' probe
    tables via (base-cat x key-class) histogram products exactly as v1 (t1- and
    s-slots independent within a (t3,t2)-block).  Returns per-(cell,key) tables
    T0[(w(B0'),dig(B0'))], T1[(w(B1'),dig(B1'))]."""
    T = 3 ** cap
    X81 = [(81 * t1) % M for t1 in range(T)]
    S243 = [(243 * s) % M for s in range(T)]
    vt, ld = VT, LD
    albase, bebase = 0, (-9) % M
    PR3 = []                     # per t3: (a3, vt/ld of b1x, kxb, sparse hx)
    for t3 in range(T):
        a3 = (9 * t3) % M
        c1b = (a3 + albase) % M
        b1x = (a3 + 2 * albase) % M
        kxb = (bebase * c1b + albase * 0) % M
        h = [0] * NW
        for x in X81:
            h[min(vt[(x + kxb) % M] + 1, N)] += 1
        PR3.append((a3, vt[b1x], ld[b1x], kxb,
                    [(i, n) for i, n in enumerate(h) if n]))
    PR2 = []                     # per t2: (a2, vt/ld of b1c, kcb, sparse hc)
    for t2 in range(T):
        a2 = (18 + 27 * t2) % M
        d2b = (a2 + bebase) % M
        b1c = (d2b + bebase) % M
        kcb = (81 + bebase * d2b) % M
        h = [0] * NW
        for sv in S243:
            h[vt[(sv + kcb) % M]] += 1
        PR2.append((a2, vt[b1c], ld[b1c], kcb,
                    [(i, n) for i, n in enumerate(h) if n]))
    joint = [0] * (NW * NW)
    cellmass = [0] * 64
    T0 = [[0] * (NW * 9) for _ in range(64 * NK)]
    T1 = [[0] * (NW * 9) for _ in range(64 * NK)]
    n_sub = 0
    for t3 in range(T):
        a3, v1x, l1x, kxb, hxs = PR3[t3]
        v1x1 = min(v1x + 1, N)
        for t2 in range(T):
            a2, v1c, l1c, kcb, hcs = PR2[t2]
            w1b = v1c if v1c < v1x1 else v1x1
            row = w1b * NW
            for vx1, nx in hxs:
                for vc, nc in hcs:
                    joint[row + (vc if vc < vx1 else vx1)] += nx * nc
            if w1b != 4:
                continue
            ec = l1c if v1c == 4 else 0
            ex = l1x if v1x == 3 else 0
            d1 = 3 * ex + ec
            assert d1 == 3 * ((t3 // 3) % 3) + ((t2 // 3) % 3) and d1 != 0
            blk = []
            for lab, tau1, tau0, kind, tc in ALLKEYS:
                al, be = tau1 % M, (tau0 - 9) % M
                c1 = (a3 + al) % M
                d2 = (a2 + be + al * c1) % M
                b1x, b1c = (a3 + 2 * al) % M, (d2 + be) % M
                w1 = min(vt[b1c], vt[b1x] + 1, N)
                ecb = ld[b1c] if (vt[b1c] == w1 and w1 < N) else 0
                exb = ld[b1x] if vt[b1x] == w1 - 1 else 0
                blk.append((w1, 3 * exb + ecb,
                            (be * c1 + al * d2) % M, (81 + be * d2) % M))
            assert blk[0][0] == 4 and blk[0][1] == d1 \
                and blk[0][2] == kxb and blk[0][3] == kcb
            elx, els = [], []
            for t1 in range(t3 % 27, T, 27):
                y0 = (X81[t1] + kxb) % M
                assert vt[y0] >= 7
                elx.append((ld[y0] if vt[y0] == 7 else 0, X81[t1]))
            for s in range(t2 % 27, T, 27):
                y0 = (S243[s] + kcb) % M
                assert vt[y0] >= 8
                els.append((ld[y0] if vt[y0] == 8 else 0, S243[s]))
            for k in range(NK):
                w1k, d1k, kx, kc = blk[k]
                hxk, hck = {}, {}
                for bx, xv in elx:
                    y = (xv + kx) % M
                    key = (bx, vt[y], ld[y])
                    hxk[key] = hxk.get(key, 0) + 1
                for bc, sv in els:
                    y = (sv + kc) % M
                    key = (bc, vt[y], ld[y])
                    hck[key] = hck.get(key, 0) + 1
                w1off = w1k * 9 + d1k
                for (bx, vx, dx), nx in hxk.items():
                    for (bc, vc, dc), ns in hck.items():
                        d0 = 3 * bx + bc
                        if d0 == 0:
                            continue
                        cnt = nx * ns
                        cell = (d1 - 1) * 8 + (d0 - 1)
                        w0 = min(vc, vx + 1, N)
                        ecd = dc if (vc == w0 and w0 < N) else 0
                        exd = dx if vx == w0 - 1 else 0
                        idx = cell * NK + k
                        T0[idx][w0 * 9 + 3 * exd + ecd] += cnt
                        T1[idx][w1off] += cnt
                        if k == 0:
                            n_sub += cnt
                            cellmass[cell] += cnt
                            assert w0 == 8 and 3 * exd + ecd == d0
    assert sum(joint) == T ** 4 and joint[4 * NW + 8] == n_sub == sum(cellmass)
    return dict(cap=cap, total=T ** 4, joint=joint, n_sub=n_sub,
                cellmass=cellmass, T0=T0, T1=T1)


def dist(tab):
    return {(i // 9, i % 9): n for i, n in enumerate(tab) if n}


def dstr(d):
    return '{' + ', '.join(f'(w={w},dig={F9N[g]}):{n}'
                           for (w, g), n in sorted(d.items())) + '}'


def tr0(d):                      # Q6 truncation for B0': w ^ 9, digit only at 8
    o = {}
    for (w, g), n in d.items():
        kk = (min(w, 9), g if w == 8 else 0)
        o[kk] = o.get(kk, 0) + n
    return o


def tr1(d):                      # Q6 truncation for B1': w ^ 5, digit only at 4
    o = {}
    for (w, g), n in d.items():
        kk = (min(w, 5), g if w == 4 else 0)
        o[kk] = o.get(kk, 0) + n
    return o


def evaluate(r, out):
    """Compare census r against Q1..Q6.  Appends detail lines to out; returns
    (verdicts dict of bools, info dict of counts)."""
    v, cm, total = {}, r['cellmass'], r['total']
    T0, T1 = r['T0'], r['T1']
    out.append(f"\n== Q1 (cell structure) — SUB' count {r['n_sub']} of {total}, "
               f"fraction {Frac(r['n_sub'], total)}; per-cell counts (rows d1, cols d0):")
    out.append('      ' + ''.join(f'{F9N[d0]:>9}' for d0 in range(1, 9)))
    for d1 in range(1, 9):
        out.append(f'{F9N[d1]:<6}' + ''.join(f'{cm[(d1 - 1) * 8 + (d0 - 1)]:>9}'
                                             for d0 in range(1, 9)))
    v['Q1'] = len(set(cm)) == 1 and cm[0] > 0
    out.append(f"Q1: all 64 cells non-empty with equal masses: "
               f"{'YES' if v['Q1'] else 'NO'} (min {min(cm)}, max {max(cm)}); "
               f"equal masses on the full 8x8 grid make (d1,d0) exactly a product "
               f"measure, so d1 indep d0.")
    bad2, n_r2z, n_rpz, n_both = [], 0, 0, 0
    for d1 in range(1, 9):
        for d0 in range(1, 9):
            cell = (d1 - 1) * 8 + (d0 - 1)
            for k in range(1, 9):
                tau = ALLKEYS[k][4]
                r2, rp = r2_at(tau, d1, d0), r2p_at(tau, d1)
                n_r2z += r2 == 0
                n_rpz += rp == 0
                n_both += r2 == 0 and rp == 0
                t0, t1 = dist(T0[cell * NK + k]), dist(T1[cell * NK + k])
                ok0 = (set(t0) == {(8, r2)}) if r2 else all(w >= 9 for w, _ in t0)
                ok1 = (set(t1) == {(4, rp)}) if rp else all(w >= 5 for w, _ in t1)
                if not (ok0 and ok1):
                    bad2.append((d1, d0, k, r2, rp, t0, t1))
    v['Q2'] = not bad2
    out.append(f'\n== Q2 (conditioned substitution law, member-by-member): 512 '
               f'(cell,tau) combos; R2(tau)=0 on {n_r2z}, 2tau+d1=0 on {n_rpz}, '
               f'both on {n_both}; violations: {len(bad2)}')
    for d1, d0, k, r2, rp, t0, t1 in bad2[:20]:
        out.append(f'  DEVIATION cell (d1={F9N[d1]}, d0={F9N[d0]}) cand '
                   f'{ALLKEYS[k][0]} R2(tau)={F9N[r2]} 2tau+d1={F9N[rp]}: '
                   f'T0={dstr(t0)} T1={dstr(t1)}')
    if len(bad2) > 20:
        out.append(f'  ... plus {len(bad2) - 20} more')
    bad3 = []
    out.append('\n== Q3 (fresh-digit genericity at the died heights) '
               '[fractions of the cell]:')
    for d1 in range(1, 9):
        for d0 in range(1, 9):
            cell = (d1 - 1) * 8 + (d0 - 1)
            tot = cm[cell]
            for k in range(1, 9):
                tau = ALLKEYS[k][4]
                r2, rp = r2_at(tau, d1, d0), r2p_at(tau, d1)
                if r2 and rp:
                    continue
                if tot == 0:
                    bad3.append((d1, d0, tau))
                    continue
                line = f'  cell (d1={F9N[d1]}, d0={F9N[d0]}) tau={F9N[tau]}:'
                ok = True
                if r2 == 0:
                    t0 = dist(T0[cell * NK + k])
                    f9 = Frac(sum(n for (w, _), n in t0.items() if w == 9), tot)
                    f10 = Frac(sum(n for (w, _), n in t0.items() if w >= 10), tot)
                    line += f" w(B0')=9 frac {f9}, >=10 frac {f10};"
                    ok = ok and f9 == Frac(8, 9) and f10 == Frac(1, 9)
                if rp == 0:
                    t1 = dist(T1[cell * NK + k])
                    g5 = Frac(sum(n for (w, _), n in t1.items() if w == 5), tot)
                    g6 = Frac(sum(n for (w, _), n in t1.items() if w >= 6), tot)
                    line += f" w(B1')=5 frac {g5}, >=6 frac {g6}"
                    ok = ok and g5 == Frac(8, 9) and g6 == Frac(1, 9)
                if not ok:
                    line += '   <-- DEVIATION'
                    bad3.append((d1, d0, tau))
                out.append(line)
    v['Q3'] = not bad3
    out.append(f'Q3: affected combos {n_r2z} (B0\'-died) + {n_rpz} (B1\'-died), '
               f'overlap {n_both}; deviations: {len(bad3)}')
    bad4, br_total = [], 0
    for cell in range(64):
        for k in range(1, 9):
            t0, t1 = dist(T0[cell * NK + k]), dist(T1[cell * NK + k])
            if all(w >= 9 for w, _ in t0) and all(w >= 5 for w, _ in t1):
                br_total += 1
    out.append(f'\n== Q4 (discriminating selection on the 8 cells d0 = d1^2): '
               f'both-rise (cell,cand) combos over ALL 512: {br_total} '
               f'(context; the 8 matched combos below are the prediction):')
    for d1 in range(1, 9):
        d0 = f9mul(d1, d1)
        cell = (d1 - 1) * 8 + (d0 - 1)
        okc, msg = True, ''
        for k in range(1, 9):
            tau = ALLKEYS[k][4]
            r2, rp = r2_at(tau, d1, d0), r2p_at(tau, d1)
            t0, t1 = dist(T0[cell * NK + k]), dist(T1[cell * NK + k])
            br = all(w >= 9 for w, _ in t0) and all(w >= 5 for w, _ in t1)
            keep = (set(t0) == {(8, r2)}) or (set(t1) == {(4, rp)})
            if tau == d1:
                okc = okc and br
                msg = f'matched tau=d1={F9N[tau]} both-rise on all members: {br}'
            else:
                okc = okc and (not br) and keep
        if not okc:
            bad4.append((d1, d0))
        out.append(f'  cell (d1={F9N[d1]}, d0=d1^2={F9N[d0]}): {msg}; other 7 '
                   f'candidates non-both-rise with an exact-weight Q2 clause: '
                   f"{'YES' if okc else 'NO  <-- DEVIATION'}")
    v['Q4'] = not bad4
    a0d = [0] * (NW * 9)
    for cell in range(64):
        for i, n in enumerate(T0[cell * NK + 9]):
            a0d[i] += n
    a0d = dist(a0d)
    n_ge8 = sum(n for (w, _), n in a0d.items() if w >= 8)
    out.append(f"\n== Q5 control t=27 (weight 3): aggregated (w(B0'),dig(B0')) = "
               f"{dstr(a0d)}; members with w(B0')>=8: {n_ge8} (MUST be 0)")
    bad243 = [(d1, d0) for d1 in range(1, 9) for d0 in range(1, 9)
              if not (set(dist(T0[((d1 - 1) * 8 + d0 - 1) * NK + 10])) == {(8, d0)}
                      and set(dist(T1[((d1 - 1) * 8 + d0 - 1) * NK + 10]))
                      == {(4, d1)})]
    v['Q5'] = n_ge8 == 0 and not bad243
    out.append(f'   control t=243 (weight 5): cells NOT keeping (8,d0) and (4,d1) '
               f'unchanged: {len(bad243)} of 64'
               + (f' — first: {bad243[:5]}' if bad243 else ''))
    td_total = fd_total = nscope = 0
    out.append("\n== Q6 (lift independence WITH SCOPE; truncation: w(B0') cap 9, "
               "w(B1') cap 5, digits kept only at exact heights 8 resp. 4):")
    for a, b in LIFTPAIRS:
        tau = ALLKEYS[a][4]
        td, fd0, fd1, sc = [], [], [], []
        for cell in range(64):
            d1c, d0c = cell // 8 + 1, cell % 8 + 1
            da0, db0 = dist(T0[cell * NK + a]), dist(T0[cell * NK + b])
            da1, db1 = dist(T1[cell * NK + a]), dist(T1[cell * NK + b])
            if tr0(da0) != tr0(db0):
                td.append((cell, 'T0'))
            if tr1(da1) != tr1(db1):
                td.append((cell, 'T1'))
            if da0 != db0:
                fd0.append(cell)
                dk = [kk for kk in set(da0) | set(db0)
                      if da0.get(kk, 0) != db0.get(kk, 0)]
                if r2_at(tau, d1c, d0c) != 0 or any(w < 9 for w, _ in dk):
                    sc.append((cell, 'T0'))
            if da1 != db1:
                fd1.append(cell)
                dk = [kk for kk in set(da1) | set(db1)
                      if da1.get(kk, 0) != db1.get(kk, 0)]
                if r2p_at(tau, d1c) != 0 or any(w < 5 for w, _ in dk):
                    sc.append((cell, 'T1'))
        td_total += len(td)
        fd_total += len(fd0) + len(fd1)
        nscope += len(sc)
        out.append(f'  pair {ALLKEYS[a][0]} vs {ALLKEYS[b][0]}: TRUNCATED-table '
                   f'diffs {len(td)} cells (MUST be 0); full-table diffs: T0 on '
                   f'{len(fd0)} cells '
                   f'{[(F9N[c // 8 + 1], F9N[c % 8 + 1]) for c in fd0]}, T1 on '
                   f'{len(fd1)} cells '
                   f'{[(F9N[c // 8 + 1], F9N[c % 8 + 1]) for c in fd1]}; '
                   f'out-of-scope diffs {len(sc)}')
        for which, tabs, cs in (('T0', T0, fd0), ('T1', T1, fd1)):
            if cs:
                c = cs[0]
                da, db = dist(tabs[c * NK + a]), dist(tabs[c * NK + b])
                diff = {kk: (da.get(kk, 0), db.get(kk, 0))
                        for kk in sorted(set(da) | set(db))
                        if da.get(kk, 0) != db.get(kk, 0)}
                out.append(f'    example {which} diff, cell (d1={F9N[c // 8 + 1]}, '
                           f'd0={F9N[c % 8 + 1]}), (orig,lift) at differing '
                           'entries: '
                           + ', '.join(f'(w={w},dig={F9N[g]}):{x}/{y}'
                                       for (w, g), (x, y) in sorted(diff.items())))
    v['Q6'] = td_total == 0 and nscope == 0
    out.append(f'  Q6 verdict basis: truncated-diff cells {td_total} of 128 (both '
               f'pairs, both tables); full-diff cells {fd_total}; out-of-scope '
               f'diffs {nscope}')
    info = dict(cmin=min(cm), cmax=max(cm), n_r2z=n_r2z, n_rpz=n_rpz,
                n_both=n_both, nbad2=len(bad2), nbad3=len(bad3),
                nbad4=len(bad4), br_total=br_total, n_ge8=n_ge8,
                nbad243=len(bad243), tdiffs=td_total, fdiffs=fd_total,
                nscope=nscope)
    return v, info


def pjoint(tbl, out):
    rows = sorted({i // NW for i, n in enumerate(tbl) if n})
    cols = sorted({i % NW for i, n in enumerate(tbl) if n})
    out.append('      ' + ''.join(f'{c:>13}' for c in cols))
    for rr in rows:
        out.append(f'{rr:<6}' + ''.join(f'{tbl[rr * NW + c]:>13}' for c in cols))


def main():
    t_start = time.time()
    os.makedirs(os.path.dirname(OUTPATH), exist_ok=True)
    out = ['SEALED CASE-K v2 GATE CENSUS, p = 3 (predictions: '
           'CASE_K_SEALED_PREDICTIONS_V2_2026-07-26.md)',
           f'N = {N}, mod 3^{N} = {M}; caps: main {CAP_MAIN} '
           f'(3^{4 * CAP_MAIN} members), stability {CAP_CHK}.',
           "SUB' = {w(B0) = 8 exact, w(B1) = 4 exact}; keys (Phi' = Phi - t; "
           '(alpha,beta) = (tau1, tau0 - 9)):']
    for lab, tau1, tau0, kind, tc in ALLKEYS:
        out.append(f'  {lab:34s} kind={kind:5s} '
                   + (f'tau={F9N[tc]}' if tc is not None else ''))
    nm, misB, misA, napp, recbad = sign_check()
    out.append(f'\n== SIGN CHECK ({nm} members x {NK} keys, genuine polydiv by '
               f'the literal Phi - t):')
    out.append(f'  sign B (tau1, tau0-9):  mismatches {misB} of {nm * NK}; '
               f'reconstruction failures {recbad}')
    out.append(f'  sign A (tau1, -9-tau0): mismatches {misA} of {napp} '
               f'sign-distinguishable (tau0 != -tau0) cases')
    t0 = time.time()
    r = census(CAP_MAIN)
    tc_main = time.time() - t0
    out.append(f'\n== BASE JOINT (w(B1) rows, w(B0) cols) at cap {CAP_MAIN} '
               f"({r['total']} members; census {tc_main:.0f}s):")
    pjoint(r['joint'], out)
    verd, info = evaluate(r, out)
    t0 = time.time()
    r2 = census(CAP_CHK)
    tc_chk = time.time() - t0
    out2 = []
    verd2, _ = evaluate(r2, out2)
    out.append(f'\n== CAP-STABILITY RE-CENSUS at cap {CAP_CHK} '
               f"({r2['total']} members; census {tc_chk:.0f}s):")
    out.extend(out2)
    scale = r['total'] // r2['total']
    fr_eq = (Frac(r['n_sub'], r['total']) == Frac(r2['n_sub'], r2['total'])
             and all(Frac(a, r['total']) == Frac(b, r2['total'])
                     for a, b in zip(r['cellmass'], r2['cellmass'])))
    ndj = sum(1 for i in range(NW * NW) if r['joint'][i] != scale * r2['joint'][i])
    ndt = sum(1 for i in range(64 * NK)
              if any(a != scale * b for a, b in zip(r['T0'][i], r2['T0'][i]))
              or any(a != scale * b for a, b in zip(r['T1'][i], r2['T1'][i])))
    same_verd = verd == verd2
    out.append(f'\nCAP STABILITY: verdict dicts identical: {same_verd}; '
               f"SUB' + cell fractions equal: {fr_eq}; base-joint cells with "
               f'cap{CAP_MAIN} != {scale}*cap{CAP_CHK}: {ndj} (cap-truncation '
               f'tail); (cell,key) probe tables not scaling exactly: {ndt} of '
               f'{64 * NK}')
    summary = [
        '=' * 72,
        f"SUMMARY — SEALED CASE-K v2 GATE p=3 (cap {CAP_MAIN}, {r['total']} "
        f"members, SUB' {r['n_sub']}, {r['n_sub'] // 64} per cell):",
        f'sign: (tau1, tau0-9) matches genuine division by Phi - t '
        f'({misB} mismatches / {nm * NK}, {recbad} reconstruction failures); '
        f'(tau1, -9-tau0) mismatches {misA}/{napp} distinguishable',
        f"Q1 {'PASS' if verd['Q1'] else 'FAIL'} — 64 cells, counts min "
        f"{info['cmin']} max {info['cmax']}",
        f"Q2 {'PASS' if verd['Q2'] else 'FAIL'} — 512 (cell,tau) combos "
        f"(R2(tau)=0: {info['n_r2z']}, 2tau+d1=0: {info['n_rpz']}, both: "
        f"{info['n_both']}); violations {info['nbad2']}",
        f"Q3 {'PASS' if verd['Q3'] else 'FAIL'} — 8/9 vs 1/9 fresh-digit splits; "
        f"deviations {info['nbad3']} of "
        f"{info['n_r2z'] + info['n_rpz']} died clauses",
        f"Q4 {'PASS' if verd['Q4'] else 'FAIL'} — unique both-rise at tau=d1 on "
        f"the 8 cells d0=d1^2 (violating cells {info['nbad4']}; both-rise combos "
        f"overall {info['br_total']})",
        f"Q5 {'PASS' if verd['Q5'] else 'FAIL'} — t=27: members with w(B0')>=8: "
        f"{info['n_ge8']}; t=243: cells changed: {info['nbad243']} of 64",
        f"Q6 {'PASS' if verd['Q6'] else 'FAIL'} — truncated-table diff cells "
        f"{info['tdiffs']} of 128; full-diff cells {info['fdiffs']}, out-of-scope "
        f"{info['nscope']}",
        f'cap stability (cap {CAP_CHK}): verdicts identical: {same_verd}; '
        f'fractions equal: {fr_eq}',
        f'total wall time {time.time() - t_start:.0f}s '
        f'(census {tc_main:.0f}s + {tc_chk:.0f}s)',
        '=' * 72,
    ]
    out.extend(summary)
    with open(OUTPATH, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    print('\n'.join(summary))
    return 0


if __name__ == '__main__':
    sys.exit(main())
