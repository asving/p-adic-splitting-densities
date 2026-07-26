#!/usr/bin/env python3
"""case_k_gate_p3.py — SEALED Case-K gate census at p = 3 (F9 level-2 recentering).

Predictions preregistered in CASE_K_SEALED_PREDICTIONS_2026-07-25.md (committed
BEFORE this script was written or run). This script is the CENSUS: it compares the
data against P1..P6 and reports PASS/FAIL with exact counts; it never adjusts a
prediction.

Configuration (mod 3^12; v = v_3): parent stratum on monic quartics
  v(a3) >= 2, digit_2(a2) = 2 (v = 2 exact), v(a1) >= 4, digit_4(a0) = 1 (v = 4 exact)
  parametrized a3 = 9*t3, a2 = 18 + 27*t2, a1 = 81*t1, a0 = 81 + 243*s with each of
  t3,t2,t1,s keeping its lowest `cap` free base-3 digits (main cap 4 -> 3^16 members;
  cap-stability re-census at cap 3).
Key Phi = x^2 + 9; development f = Phi^2 + B1*Phi + B0 via the closed form for
phi = x^2 - alpha*x - beta:
  c1 = a3 + alpha; d2 = a2 + beta + alpha*c1; B1 = (a3 + 2*alpha, d2 + beta);
  B0 = (a1 + beta*c1 + alpha*d2, a0 + beta*d2)   [pairs are (x-coeff, const)].
Base key: (alpha, beta) = (0, -9).  Recentered key Phi' = Phi - t, t = tau1*x + tau0:
implemented as (alpha, beta) = (tau1, tau0 - 9) ["sign B"]; the offered alternative
(tau1, -9 - tau0) ["sign A"] is tested against genuine polynomial division by the
literal Phi - t on >= 1000 members and the winner is reported.
w(B) = min(v(b0), v(b1)+1) cap 12.  F9 = F3[zb]/(zb^2+1); the digit of B = b1*x + b0
at m = w(B) is eps_x*zb + eps_c (code 3*eps_x + eps_c), eps_c = digit_m(b0) if
v(b0) = m else 0, eps_x = digit_{m-1}(b1) if v(b1) = m - 1 else 0.
SUB = {w(B0) = 6 exact, w(B1) = 3 exact}; cells (d1, d0) in F9* x F9* (64 cells).
Candidates: t = 9*c1*x + 27*c0, (c1,c0) in {0,1,2}^2 \\ {(0,0)} (weight 3, digit
tau = c1*zb + c0); controls t = 9 (weight 2), t = 81 (weight 4); lift-independence
re-runs t=9x as t=9x+81 and t=9x+27 as t=9x+27+243.

Run:  python3 case_k_gate_p3.py > results/case_k_gate_p3_output.txt
      (full tables to stdout; <= 20-line verdict summary duplicated on stderr)
"""
import random
import sys
import time
from fractions import Fraction as Frac

P, N = 3, 12
M = P ** N                       # 531441
NW = N + 1
CAP_MAIN, CAP_CHK = 4, 3

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


def mult(tau, d1, d0):           # multiplicity of tau as root of R2
    if r2_at(tau, d1, d0):
        return 0
    return 2 if r2p_at(tau, d1) == 0 else 1


# keys: (label, tau1, tau0, kind, taucode); base first, then 8 weight-3 candidates,
# 2 wrong-weight controls, 2 lifts.  Phi' = Phi - t  <->  (alpha,beta)=(tau1,tau0-9).
ALLKEYS = [('t=0 (base)', 0, 0, 'base', 0)]
for c1 in range(3):
    for c0 in range(3):
        if c1 or c0:
            ALLKEYS.append((f't=9x*{c1}+27*{c0} (tau={F9N[3*c1+c0]})',
                            9 * c1, 27 * c0, 'w3', 3 * c1 + c0))
ALLKEYS += [('t=9 (w2 ctrl)', 0, 9, 'ctrl2', None),
            ('t=81 (w4 ctrl)', 0, 81, 'ctrl4', None),
            ('t=9x+81 (lift of k3)', 9, 81, 'lift', 3),
            ('t=9x+27+243 (lift of k4)', 9, 270, 'lift', 4)]
NK = len(ALLKEYS)                # 13
LIFTPAIRS = [(3, 11), (4, 12)]   # (original k, lifted k)


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
    """Full pass over the capped stratum.  Base (w(B1), w(B0)) joint via the
    valuation-histogram factorization (t1- and s-slots are independent within a
    (t3,t2)-block); SUB probe tables via (base-cat x key-class) histogram products.
    Returns per-(cell,key) joint tables T0[(w(B0'),dig(B0'))], T1[(w(B1'),dig(B1'))]."""
    T = 3 ** cap
    X81 = [(81 * t1) % M for t1 in range(T)]
    S243 = [(243 * s) % M for s in range(T)]
    joint = [0] * (NW * NW)
    cellmass = [0] * 64
    T0 = [[0] * (NW * 9) for _ in range(64 * NK)]
    T1 = [[0] * (NW * 9) for _ in range(64 * NK)]
    n_sub = 0
    vt, ld = VT, LD
    for t3 in range(T):
        a3 = (9 * t3) % M
        for t2 in range(T):
            a2 = (18 + 27 * t2) % M
            blk = []
            for lab, tau1, tau0, kind, tc in ALLKEYS:
                al, be = tau1 % M, (tau0 - 9) % M
                c1 = (a3 + al) % M
                d2 = (a2 + be + al * c1) % M
                b1x, b1c = (a3 + 2 * al) % M, (d2 + be) % M
                w1 = min(vt[b1c], vt[b1x] + 1, N)
                ec = ld[b1c] if (vt[b1c] == w1 and w1 < N) else 0
                ex = ld[b1x] if vt[b1x] == w1 - 1 else 0
                blk.append((w1, 3 * ex + ec,
                            (be * c1 + al * d2) % M, (81 + be * d2) % M))
            w1b, d1, kxb, kcb = blk[0]
            hx = [0] * NW
            for x in X81:
                hx[min(vt[(x + kxb) % M] + 1, N)] += 1
            hc = [0] * NW
            for sv in S243:
                hc[vt[(sv + kcb) % M]] += 1
            row = w1b * NW
            for vx1 in range(NW):
                nx = hx[vx1]
                if nx:
                    for vc in range(NW):
                        nc = hc[vc]
                        if nc:
                            joint[row + (vc if vc < vx1 else vx1)] += nx * nc
            if w1b != 3:
                continue
            assert d1 == 3 * (t3 % 3) + (t2 % 3) and d1 != 0
            elx, els = [], []
            for t1 in range(t3 % 3, T, 3):
                y0 = (X81[t1] + kxb) % M
                assert vt[y0] >= 5
                elx.append((ld[y0] if vt[y0] == 5 else 0, X81[t1]))
            for s in range(t2 % 3, T, 3):
                y0 = (S243[s] + kcb) % M
                assert vt[y0] >= 6
                els.append((ld[y0] if vt[y0] == 6 else 0, S243[s]))
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
                        ec = dc if (vc == w0 and w0 < N) else 0
                        ex = dx if vx == w0 - 1 else 0
                        idx = cell * NK + k
                        T0[idx][w0 * 9 + 3 * ex + ec] += cnt
                        T1[idx][w1off] += cnt
                        if k == 0:
                            n_sub += cnt
                            cellmass[cell] += cnt
                            assert w0 == 6 and 3 * ex + ec == d0
    assert sum(joint) == T ** 4 and joint[3 * NW + 6] == n_sub == sum(cellmass)
    return dict(cap=cap, total=T ** 4, joint=joint, n_sub=n_sub,
                cellmass=cellmass, T0=T0, T1=T1)


def dist(tab):
    return {(i // 9, i % 9): n for i, n in enumerate(tab) if n}


def dstr(d):
    return '{' + ', '.join(f'(w={w},dig={F9N[g]}):{n}'
                           for (w, g), n in sorted(d.items())) + '}'


def evaluate(r, out):
    """Compare census r against P1..P6.  Appends detail lines to out; returns the
    verdicts dict."""
    v, cm, total = {}, r['cellmass'], r['total']
    T0, T1 = r['T0'], r['T1']
    out.append(f"\n== P1 (cell structure) — SUB count {r['n_sub']} of {total}, "
               f"fraction {Frac(r['n_sub'], total)}; per-cell counts (rows d1, cols d0):")
    out.append('      ' + ''.join(f'{F9N[d0]:>9}' for d0 in range(1, 9)))
    for d1 in range(1, 9):
        out.append(f'{F9N[d1]:<6}' + ''.join(f'{cm[(d1 - 1) * 8 + (d0 - 1)]:>9}'
                                             for d0 in range(1, 9)))
    v['P1'] = len(set(cm)) == 1 and cm[0] > 0
    out.append(f"P1: equal masses {'YES' if v['P1'] else 'NO'} "
               f"(min {min(cm)}, max {max(cm)}); equal masses on the full 8x8 grid "
               f"make (d1,d0) exactly a product measure, so d1 indep d0.")
    bad2, nmu = [], [0, 0, 0]
    for d1 in range(1, 9):
        for d0 in range(1, 9):
            cell = (d1 - 1) * 8 + (d0 - 1)
            for k in range(1, 9):
                tau = ALLKEYS[k][4]
                mu = mult(tau, d1, d0)
                nmu[mu] += 1
                t0, t1 = dist(T0[cell * NK + k]), dist(T1[cell * NK + k])
                if mu == 0:
                    ok = (set(t0) == {(6, r2_at(tau, d1, d0))}
                          and set(t1) == {(3, r2p_at(tau, d1))})
                elif mu == 1:
                    dp = r2p_at(tau, d1)
                    ok = (all(w >= 7 for w, _ in t0) and dp != 0
                          and set(t1) == {(3, dp)})
                else:
                    ok = (all(w >= 7 for w, _ in t0)
                          and all(w >= 4 for w, _ in t1))
                if not ok:
                    bad2.append((d1, d0, k, mu, t0, t1))
    v['P2'] = not bad2
    out.append(f'\n== P2 (substitution law): combos by mu: mu=0 {nmu[0]}, '
               f'mu=1 {nmu[1]}, mu=2 {nmu[2]} (of 512); violations: {len(bad2)}')
    if bad2:
        out.append(f'  deviation structure: all mu=0: '
                   f'{all(b[3] == 0 for b in bad2)}; all tau = d1 (i.e. '
                   f"R2'(tau) = 2tau+d1 = 0): "
                   f'{all(ALLKEYS[b[2]][4] == b[0] and r2p_at(ALLKEYS[b[2]][4], b[0]) == 0 for b in bad2)}; '
                   f"B0'-clause (w=6, dig=R2(tau)) holds on ALL of them: "
                   f'{all(set(b[4]) == {(6, r2_at(ALLKEYS[b[2]][4], b[0], b[1]))} for b in bad2)}')
    for d1, d0, k, mu, t0, t1 in bad2[:20]:
        out.append(f'  DEVIATION cell (d1={F9N[d1]}, d0={F9N[d0]}) cand '
                   f'{ALLKEYS[k][0]} mu={mu}: T0={dstr(t0)} T1={dstr(t1)}')
    if len(bad2) > 20:
        out.append(f'  ... plus {len(bad2) - 20} more (same structure)')
    # P3: cell (d1=zb, d0=2=zb^2): unique both-rise at tau=zb; tau=zb+1 dig(B1')=2
    cell = (3 - 1) * 8 + (2 - 1)
    t0m, t1m = dist(T0[cell * NK + 3]), dist(T1[cell * NK + 3])
    ok_m = all(w >= 7 for w, _ in t0m) and all(w >= 4 for w, _ in t1m)
    others_no_rise = all(set(dist(T1[cell * NK + k])) <= {(3, g) for g in range(9)}
                         for k in range(1, 9) if k != 3)
    t1_k4 = dist(T1[cell * NK + 4])
    ok_k4 = set(t1_k4) == {(3, 2)}
    v['P3'] = ok_m and others_no_rise and ok_k4
    out.append(f"\n== P3 (cell d1=zb, d0=2=d1^2, {cm[cell]} members): matched tau=zb "
               f"both-rise on all members: {ok_m} (T0={dstr(t0m)}, T1={dstr(t1m)}); "
               f"all 7 other candidates keep w(B1')=3: {others_no_rise}; "
               f"tau=zb+1 gives dig(B1')=2 on all: {ok_k4} (T1={dstr(t1_k4)})")
    bad4 = []
    out.append('\n== P4 (fresh-digit genericity) per mu>=1 combo '
               '[fractions of the cell]:')
    for d1 in range(1, 9):
        for d0 in range(1, 9):
            cell = (d1 - 1) * 8 + (d0 - 1)
            for k in range(1, 9):
                tau = ALLKEYS[k][4]
                mu = mult(tau, d1, d0)
                if mu == 0:
                    continue
                t0, t1 = dist(T0[cell * NK + k]), dist(T1[cell * NK + k])
                tot = cm[cell]
                f7 = Frac(sum(n for (w, _), n in t0.items() if w == 7), tot)
                f8 = Frac(sum(n for (w, _), n in t0.items() if w >= 8), tot)
                line = (f'  cell (d1={F9N[d1]}, d0={F9N[d0]}) tau={F9N[tau]} mu={mu}: '
                        f"w(B0')=7 frac {f7}, >=8 frac {f8}")
                ok = f7 == Frac(2, 3) and f8 == Frac(1, 3)
                if mu == 2:
                    g4 = Frac(sum(n for (w, _), n in t1.items() if w == 4), tot)
                    g5 = Frac(sum(n for (w, _), n in t1.items() if w >= 5), tot)
                    line += f"; w(B1')=4 frac {g4}, >=5 frac {g5}"
                    ok = ok and g4 == Frac(2, 3) and g5 == Frac(1, 3)
                if not ok:
                    line += '   <-- DEVIATION'
                    bad4.append((d1, d0, tau))
                out.append(line)
    v['P4'] = not bad4
    # P5 controls
    a0d = [0] * (NW * 9)
    for cell in range(64):
        for i, n in enumerate(T0[cell * NK + 9]):
            a0d[i] += n
    a0d = dist(a0d)
    n_ge6 = sum(n for (w, _), n in a0d.items() if w >= 6)
    soft = set(a0d) == {(4, 1)}
    v['P5'] = n_ge6 == 0
    out.append(f"\n== P5 control t=9 (weight 2): aggregated (w(B0'),dig(B0')) = "
               f"{dstr(a0d)}; members with w(B0')>=6: {n_ge6} (MUST be 0); "
               f"all mass at (4, dig=1): {soft}")
    bad81 = [(d1, d0) for d1 in range(1, 9) for d0 in range(1, 9)
             if not (set(dist(T0[((d1 - 1) * 8 + d0 - 1) * NK + 10])) == {(6, d0)}
                     and set(dist(T1[((d1 - 1) * 8 + d0 - 1) * NK + 10]))
                     == {(3, d1)})]
    v['P5'] = v['P5'] and not bad81
    out.append(f"   control t=81 (weight 4): cells NOT keeping (w,dig) of both B0,B1 "
               f'unchanged: {len(bad81)} of 64'
               + (f' — first: {bad81[:5]}' if bad81 else ''))
    bad6 = []
    out.append('\n== P6 (lift independence):')
    for a, b in LIFTPAIRS:
        c0 = [c for c in range(64) if T0[c * NK + a] != T0[c * NK + b]]
        c1 = [c for c in range(64) if T1[c * NK + a] != T1[c * NK + b]]
        bad6 += [(a, b, c) for c in sorted(set(c0) | set(c1))]
        out.append(f'  pair {ALLKEYS[a][0]} vs {ALLKEYS[b][0]}: T0 tables differ '
                   f'on {len(c0)} cells {[(F9N[c // 8 + 1], F9N[c % 8 + 1]) for c in c0]}; '
                   f'T1 tables differ on {len(c1)} cells '
                   f'{[(F9N[c // 8 + 1], F9N[c % 8 + 1]) for c in c1]}')
        for which, tabs, cs in (('T0', T0, c0), ('T1', T1, c1)):
            if cs:
                c = cs[0]
                da, db = dist(tabs[c * NK + a]), dist(tabs[c * NK + b])
                ks = sorted(set(da) | set(db))
                diff = {kk: (da.get(kk, 0), db.get(kk, 0)) for kk in ks
                        if da.get(kk, 0) != db.get(kk, 0)}
                out.append(f'    example {which} diff, cell (d1={F9N[c // 8 + 1]}, '
                           f'd0={F9N[c % 8 + 1]}), (orig,lift) at differing entries: '
                           + ', '.join(f'(w={w},dig={F9N[g]}):{x}/{y}'
                                       for (w, g), (x, y) in sorted(diff.items())))
    v['P6'] = not bad6
    out.append(f'  P6 verdict basis: (pair,cell) combos with any table difference: '
               f'{len(bad6)} of 128')
    return v


def pjoint(tbl, out):
    rows = sorted({i // NW for i, n in enumerate(tbl) if n})
    cols = sorted({i % NW for i, n in enumerate(tbl) if n})
    out.append('      ' + ''.join(f'{c:>10}' for c in cols))
    for rr in rows:
        out.append(f'{rr:<6}' + ''.join(f'{tbl[rr * NW + c]:>10}' for c in cols))


def main():
    t_start = time.time()
    out = []
    out.append('SEALED CASE-K GATE CENSUS, p = 3 (predictions: '
               'CASE_K_SEALED_PREDICTIONS_2026-07-25.md)')
    out.append(f'N = {N}, mod 3^{N} = {M}; caps: main {CAP_MAIN} '
               f'(3^{4 * CAP_MAIN} members), stability {CAP_CHK}.')
    out.append('Keys (Phi\' = Phi - t; (alpha,beta) = (tau1, tau0 - 9)):')
    for lab, tau1, tau0, kind, tc in ALLKEYS:
        out.append(f'  {lab:28s} kind={kind:5s} '
                   + (f'tau={F9N[tc]}' if tc is not None else ''))
    nm, misB, misA, napp, recbad = sign_check()
    out.append(f'\n== SIGN CHECK ({nm} members x {NK} keys, genuine polydiv by the '
               f'literal Phi - t):')
    out.append(f'  sign B (tau1, tau0-9):  mismatches {misB} of {nm * NK}; '
               f'reconstruction failures {recbad}')
    out.append(f'  sign A (tau1, -9-tau0): mismatches {misA} of {napp} '
               f'sign-distinguishable (tau0 != -tau0) cases')
    t0 = time.time()
    r = census(CAP_MAIN)
    out.append(f'\n== BASE JOINT (w(B1) rows, w(B0) cols) at cap {CAP_MAIN} '
               f"({r['total']} members; census {time.time() - t0:.0f}s):")
    pjoint(r['joint'], out)
    verd = evaluate(r, out)
    t0 = time.time()
    r2 = census(CAP_CHK)
    out2 = []
    verd2 = evaluate(r2, out2)
    out.append(f'\n== CAP-STABILITY RE-CENSUS at cap {CAP_CHK} '
               f"({r2['total']} members; census {time.time() - t0:.0f}s):")
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
    out.append(f'\nCAP STABILITY: verdict dicts identical: {same_verd}; SUB + cell '
               f'fractions equal: {fr_eq}; base-joint cells with cap{CAP_MAIN} != '
               f'{scale}*cap{CAP_CHK}: {ndj} (cap-truncation tail); (cell,key) probe '
               f'tables not scaling exactly: {ndt} of {64 * NK}')
    summary = [
        '=' * 72,
        f'SUMMARY — SEALED CASE-K GATE p=3 (cap {CAP_MAIN}, '
        f"{r['total']} members, SUB {r['n_sub']}):",
        f'sign: (tau1, tau0-9) matches genuine division by Phi - t '
        f'({misB} mismatches / {nm * NK}); (tau1, -9-tau0) mismatches '
        f'{misA}/{napp} distinguishable',
        f"P1 {'PASS' if verd['P1'] else 'FAIL'} — 64 cells, counts min "
        f"{min(r['cellmass'])} max {max(r['cellmass'])}",
        f"P2 {'PASS' if verd['P2'] else 'FAIL'} — 512 (cell,tau) combos "
        f'(456 mu=0 / 48 mu=1 / 8 mu=2 expected)',
        f"P3 {'PASS' if verd['P3'] else 'FAIL'} — unique both-rise at tau=d1 "
        f'on cell (zb, 2); tau=zb+1 digit law',
        f"P4 {'PASS' if verd['P4'] else 'FAIL'} — 2/3 vs 1/3 fresh-digit splits "
        f'on all mu>=1 combos',
        f"P5 {'PASS' if verd['P5'] else 'FAIL'} — controls t=9 (no w>=6) and "
        f't=81 (digits unchanged)',
        f"P6 {'PASS' if verd['P6'] else 'FAIL'} — lift tables identical",
        f'cap stability (cap {CAP_CHK}): verdicts identical: {same_verd}; '
        f'fractions equal: {fr_eq}',
        f'total wall time {time.time() - t_start:.0f}s',
        '=' * 72,
    ]
    out.extend(summary)
    print('\n'.join(out))
    print('\n'.join(summary), file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
