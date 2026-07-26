#!/usr/bin/env python3
"""case_d4n3_gate.py — SEALED D4-n3 gate census (n = 3 class-3 prefix, p = 2, 3).

Predictions preregistered in CASE_D4N3_SEALED_PREDICTIONS.md (committed BEFORE
this script existed).  This script is the CENSUS: it exhaustively enumerates
EVERY box f = x^3 + c2 x^2 + c1 x + c0 mod p^N at the four sealed (p, N)
configs — (2,6), (2,7), (3,5), (3,6) — classifies each against the prefix
P-hat* (root read side (0,3)-(3,0) slope 1, residual = irreducible quadratic
psi * (z - r), key Phi1 = x^2 + [s1] p x + [s0] p^2, depth-1 adjacent descend
side (0,4)-(1,1)), materializes the per-box membership sums for the partition
checks (P5 step-0 over the FC8 stratum list; P6 step-1 over the FC9 list), and
reports PASS/FAIL per sealed prediction with exact counts.  It never adjusts a
prediction; FAIL is a valid outcome; falsifiers F1-F6 are one-hit kills.

Enumeration is literal: for each scalar c2 residue, all (c1, c0) pairs are
materialized as 2-D membership-sum arrays (int8), so every one of the p^{3N}
boxes contributes an individually verified membership sum.  Frame-1 objects
use the sealed closed forms q0 = c2 - S1, r1 = c1 - S0 - S1*q0,
r0 = c0 - S0*q0 (S1 = [s1] p, S0 = [s0] p^2), cross-checked on random
subsamples against genuine subtract-multiples long division by the LITERAL
Phi1 plus full reconstruction f = B1*Phi1 + B0 (falsifier F5).  All digit
reads sit at base levels <= 4; every classification is recomputed from
c mod p^5 and must agree member-by-member (cap-5 stability, F6).

Run:  uv run --with numpy python case_d4n3_gate.py
      (long output -> /tmp/d4n3_census.out; results ->
       results/case_d4n3_results.json; summary on stdout)
"""
import json
import os
import random
import sys
import time
from itertools import product

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPATH = '/tmp/d4n3_census.out'
JSONPATH = os.path.join(HERE, 'results', 'case_d4n3_results.json')
CONFIGS = [(2, 6), (2, 7), (3, 5), (3, 6)]
SEED = 20260726
NSUB = 2000

# Sealed quad*lin cell tables (S2): (psi=(s1,s0), r, (d2,d1,d0)).
SEALED_CELLS = {
    2: [((1, 1), 1, (0, 0, 1))],
    3: [((0, 1), 1, (2, 1, 2)), ((0, 1), 2, (1, 1, 1)),
        ((1, 2), 1, (0, 1, 1)), ((1, 2), 2, (2, 0, 2)),
        ((2, 2), 1, (1, 0, 1)), ((2, 2), 2, (0, 1, 2))],
}


def derive_cells(p):
    """Independent in-script rederivation of the quad*lin cells (F6 check):
    all monic irreducible quadratics psi = z^2+s1 z+s0 over F_p, r in F_p^x,
    tuple (d2,d1,d0) of R = psi*(z-r) = z^3+(s1-r)z^2+(s0-r s1)z-r s0."""
    out = []
    for s1 in range(p):
        for s0 in range(p):
            if all((z * z + s1 * z + s0) % p for z in range(p)):
                for r in range(1, p):
                    out.append(((s1, s0), r,
                                ((s1 - r) % p, (s0 - r * s1) % p,
                                 (-r * s0) % p)))
    return out


def polydiv(f, d, mod):
    """Genuine long division (subtract multiples of the literal monic divisor
    d, low->high coefficient lists), returns (quotient, remainder)."""
    f = [x % mod for x in f]
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


def vcap(lvl, cap):
    """Elementwise min(v_p(x), cap) from digit arrays lvl[k] (k = 0..cap-1)."""
    v = np.full(lvl[0].shape, cap, dtype=np.int8)
    for k in range(cap - 1, -1, -1):
        v[lvl[k] != 0] = k
    return v


def census(p, N, out):
    """Exhaustive census at one sealed (p, N).  Returns the result dict."""
    M = p ** N
    p3, p4, p5 = p ** 3, p ** 4, p ** 5
    c = np.arange(M, dtype=np.int64)
    lvl = [(c // p ** k) % p for k in range(5)]          # base levels 0..4
    cl = lvl[0] == 0                                     # cluster condition
    V0, V1, V2 = vcap(lvl, 4), vcap(lvl, 3), vcap(lvl, 2)
    cells = SEALED_CELLS[p]
    ncell = len(cells)
    # FC8 step-0 stratum list: 20 non-target V-lumps + p^2(p-1) digit cells.
    lumps = [t for t in product((1, 2, 3, 4), (1, 2, 3), (1, 2))
             if not (t[0] == 3 and t[1] >= 2)]
    dcells = [(d2, d1, d0) for d2 in range(p) for d1 in range(p)
              for d0 in range(1, p)]
    # 1-D membership factors (c1-axis and c0-axis), computed once:
    lump1 = {V1v: cl & (V1 == V1v) for V1v in (1, 2, 3)}
    lump0 = {V0v: cl & (V0 == V0v) for V0v in (1, 2, 3, 4)}
    dc1 = {d1: cl & (lvl[1] == 0) & (lvl[2] == d1) for d1 in range(p)}
    dc0 = {d0: cl & (lvl[1] == 0) & (lvl[2] == 0) & (lvl[3] == d0)
           for d0 in range(1, p)}
    res = dict(p=p, N=N, box=M ** 3, nc=0, cluster=0,
               nbad0=0, bad0_ex=[], nbad1=0, nboxviol=0, nP7=0, ncap_bad=0,
               dcell_counts={str(t): 0 for t in dcells},
               lump_counts={str(t): 0 for t in lumps},
               delta_counts=[{f'({dc},{dx})': 0 for dc in range(p)
                              for dx in range(p)} for _ in range(ncell)])
    t0 = time.time()
    for c2v in range(M):
        cl2 = c2v % p == 0
        l1c2 = (c2v // p) % p
        V2s = 2 if c2v % (p * p) == 0 else (1 if cl2 else 0)
        # ---- step-0 membership sum (P5), literal per box ----
        S0 = np.ones((M, M), dtype=np.int8)              # NC baseline
        if cl2:
            cl_i8_1, cl_i8_0 = cl.astype(np.int8), cl.astype(np.int8)
            S0 -= np.multiply.outer(cl_i8_1, cl_i8_0)    # NC = 1 - cluster
            res['cluster'] += int(cl.sum()) ** 2
            res['nc'] += M * M - int(cl.sum()) ** 2
            for (V0v, V1v, V2v) in lumps:                # V-lumps
                if V2v != V2s:
                    continue
                a, b = lump1[V1v], lump0[V0v]
                S0 += np.multiply.outer(a.astype(np.int8), b.astype(np.int8))
                res['lump_counts'][str((V0v, V1v, V2v))] += \
                    int(a.sum()) * int(b.sum())
            for (d2, d1, d0) in dcells:                  # target digit cells
                if d2 != l1c2:
                    continue
                a, b = dc1[d1], dc0[d0]
                S0 += np.multiply.outer(a.astype(np.int8), b.astype(np.int8))
                res['dcell_counts'][str((d2, d1, d0))] += \
                    int(a.sum()) * int(b.sum())
        else:
            res['nc'] += M * M
        bad = S0 != 1
        nb = int(bad.sum())
        if nb:
            res['nbad0'] += nb
            if len(res['bad0_ex']) < 3:
                w = np.argwhere(bad)[:3]
                res['bad0_ex'] += [(c2v, int(i), int(j), int(S0[i, j]))
                                   for i, j in w]
        # ---- step-1 within each quad*lin cell (P1/P2/P4/P6/P7) ----
        if not cl2:
            continue
        for ci, ((s1, s0), r, (d2, d1, d0)) in enumerate(cells):
            if d2 != l1c2:
                continue
            S1c, S0c = s1 * p, s0 * p * p
            m1, m0 = dc1[d1], dc0[d0]
            n1, n0 = int(m1.sum()), int(m0.sum())
            q0 = (c2v - S1c) % M
            r1 = (c - S0c - S1c * q0) % M                # c1-axis
            r0 = (c - S0c * q0) % M                      # c0-axis
            vr1 = r1 % p3 == 0                           # v(r1) >= 3
            vr0 = r0 % p4 == 0                           # v(r0) >= 4
            dr1 = (r1 // p3) % p                         # lvl-3 digit of r1
            dr0 = (r0 // p4) % p                         # lvl-4 digit of r0
            # inherited-(BOX) violations (F3): member not (vr1 and vr0)
            res['nboxviol'] += n1 * n0 - \
                int((m1 & vr1).sum()) * int((m0 & vr0).sum())
            # P7 vertex: w(B1) = 1 exactly and vertex digit zbar - r
            if not (q0 % p == 0 and (q0 // p) % p == (p - r) % p):
                res['nP7'] += n1 * n0
            # step-1 membership sum over the p^2 FC9 systems, literal
            S1 = np.zeros((M, M), dtype=np.int8)
            for dx in range(p):
                a = (m1 & vr1 & (dr1 == dx)).astype(np.int8)
                for dc_ in range(p):
                    b = (m0 & vr0 & (dr0 == dc_)).astype(np.int8)
                    S1 += np.multiply.outer(a, b)
                    res['delta_counts'][ci][f'({dc_},{dx})'] += \
                        int(a.sum()) * int(b.sum())
            region = np.multiply.outer(m1, m0)
            res['nbad1'] += int((region & (S1 != 1)).sum())
            # cap-5 stability (F6): recompute frame-1 reads from c mod p^5
            q05 = ((c2v % p5) - S1c) % p5
            r15 = ((c % p5) - S0c - S1c * q05) % p5
            r05 = ((c % p5) - S0c * q05) % p5
            res['ncap_bad'] += int((r1 % p5 != r15).sum()) + \
                int((r0 % p5 != r05).sum()) + \
                int((dr1 != (r15 // p3) % p).sum()) + \
                int((dr0 != (r05 // p4) % p).sum())
    res['secs'] = round(time.time() - t0, 1)
    return res


def verification_pass(p, N, out):
    """F5: closed forms vs genuine subtract-multiples division by the LITERAL
    Phi1, plus reconstruction f = B1*Phi1 + B0, on NSUB random boxes (half
    general, half constructed inside the quad*lin cells)."""
    M = p ** N
    rng = random.Random(SEED + p)
    cells = SEALED_CELLS[p]
    mis = rec = 0
    for i in range(NSUB):
        (s1, s0), r, (d2, d1, d0) = cells[i % len(cells)]
        if i % 2 == 0:
            c2, c1, c0 = (rng.randrange(M) for _ in range(3))
        else:                       # in-cell member (where the gate reads)
            c2 = (d2 * p + p * p * rng.randrange(max(M // p**2, 1))) % M
            c1 = (d1 * p**2 + p**3 * rng.randrange(max(M // p**3, 1))) % M
            c0 = (d0 * p**3 + p**4 * rng.randrange(max(M // p**4, 1))) % M
        f = [c0, c1, c2, 1]
        for (t1, t0_), rr, _tup in cells:
            S1c, S0c = t1 * p, t0_ * p * p
            phi1 = [S0c, S1c, 1]
            qL, rL = polydiv(f, phi1, M)
            q0 = (c2 - S1c) % M
            r1 = (c1 - S0c - S1c * q0) % M
            r0 = (c0 - S0c * q0) % M
            if qL != [q0, 1] or rL != [r0, r1]:
                mis += 1
            recon = polymul(qL, phi1, M)
            for j, x in enumerate(rL):
                recon[j] = (recon[j] + x) % M
            if recon != [x % M for x in f]:
                rec += 1
    out.append(f'  F5 verification p={p} N={N}: {NSUB} members x {len(cells)}'
               f' literal divisors: closed-form mismatches {mis},'
               f' reconstruction failures {rec}')
    return mis, rec


def evaluate(p, N, res, mis, rec, cellsmatch, out):
    """PASS/FAIL per sealed prediction at one (p, N)."""
    C = {2: 3, 3: 48}[p]
    CR = {2: 1, 3: 6}[p]
    e_eta = p ** (3 * N - 11)
    e_dc = p ** (3 * N - 9)
    cells = SEALED_CELLS[p]
    fiber = sum(v for ci in range(len(cells))
                for k, v in res['delta_counts'][ci].items() if k != '(0,0)')
    deeps = [res['delta_counts'][ci]['(0,0)'] for ci in range(len(cells))]
    etas = {(ci, k): v for ci in range(len(cells))
            for k, v in res['delta_counts'][ci].items() if k != '(0,0)'}
    dcs = res['dcell_counts']
    rootfiber = sum(dcs[str(t[2])] for t in cells)
    v = {
        'P1': fiber == C * e_eta,
        'P2': all(x == e_eta for x in etas.values()),
        'P3': all(x == e_dc for x in dcs.values()) and rootfiber == CR * e_dc,
        'P4': all(x == e_eta for x in deeps),
        'P5': res['nbad0'] == 0,
        'P6': res['nbad1'] == 0 and res['nboxviol'] == 0,
        'P7': res['nP7'] == 0,
        'P8': fiber * p ** 11 == C * p ** (3 * N)
              and fiber * p ** 4 <= p ** (3 * N),
        'F5': mis == 0 and rec == 0,
        'F6': res['ncap_bad'] == 0 and cellsmatch,
    }
    drv = (res['cluster'] == p ** (3 * N - 3)
           and res['nc'] == p ** (3 * N) - p ** (3 * N - 3)
           and sum(dcs.values()) == p * p * (p - 1) * e_dc)
    v['derived'] = drv
    out.append(f'\n== EVALUATION p={p} N={N} (box {p}^{3*N} = {res["box"]}):')
    out.append(f'  P1 fiber count: census {fiber}, sealed {C * e_eta}'
               f'  -> {"PASS" if v["P1"] else "FAIL"}')
    out.append(f'  P2 per-eta cells (sealed {e_eta} each): '
               f'{sorted(set(etas.values()))} -> '
               f'{"PASS" if v["P2"] else "FAIL"}')
    out.append(f'  P3 digit cells (sealed {e_dc} each): '
               f'{sorted(set(dcs.values()))}; root fiber {rootfiber} '
               f'(sealed {CR * e_dc}) -> {"PASS" if v["P3"] else "FAIL"}')
    out.append(f'  P4 DEEP lumps (sealed {e_eta} each): {deeps} -> '
               f'{"PASS" if v["P4"] else "FAIL"}')
    out.append(f'  P5 step-0 partition: boxes with membership sum != 1: '
               f'{res["nbad0"]} {res["bad0_ex"] or ""} -> '
               f'{"PASS" if v["P5"] else "FAIL"}')
    out.append(f'  P6 step-1 partition: sum != 1: {res["nbad1"]}; '
               f'(BOX) violations: {res["nboxviol"]} -> '
               f'{"PASS" if v["P6"] else "FAIL"}')
    out.append(f'  P7 vertex/(HV) exceptions: {res["nP7"]} -> '
               f'{"PASS" if v["P7"] else "FAIL"}')
    out.append(f'  P8 net bound: mu-hat = {fiber}/{p}^{3*N} '
               f'(= C p^-11: {fiber * p**11 == C * p**(3*N)}), '
               f'<= p^-4: {fiber * p**4 <= p**(3*N)} -> '
               f'{"PASS" if v["P8"] else "FAIL"}')
    out.append(f'  F5 division cross-check -> {"PASS" if v["F5"] else "FAIL"}'
               f'; F6 cap-5/cell-table: cap mismatches {res["ncap_bad"]}, '
               f'cell table match {cellsmatch} -> '
               f'{"PASS" if v["F6"] else "FAIL"}')
    out.append(f'  derived sub-totals (cluster/NC/target region) -> '
               f'{"PASS" if drv else "FAIL"}  ({res["secs"]}s census)')
    return v, fiber


def main():
    t0 = time.time()
    out = ['SEALED CASE-D4N3 GATE CENSUS (predictions: '
           'CASE_D4N3_SEALED_PREDICTIONS.md, committed before this script '
           'existed)',
           'n = 3 monic cubics; prefix P-hat*: root side (0,3)-(3,0) slope 1,'
           ' R = psi(z)(z-r) irred-quad*linear, key Phi1 = x^2+[s1]px+[s0]p^2,'
           ' adjacent descend side (0,4)-(1,1), delta in F_{p^2}*',
           f'configs {CONFIGS}, seed {SEED}, NSUB {NSUB}']
    allres, verdicts, fibers = {}, {}, {}
    for p, N in CONFIGS:
        cellsmatch = sorted(derive_cells(p)) == sorted(SEALED_CELLS[p])
        out.append(f'\n#### p = {p}, N = {N} (exhaustive {p}^{3*N} boxes) ####')
        out.append(f'  in-script cell rederivation matches sealed table: '
                   f'{cellsmatch}')
        res = census(p, N, out)
        mis, rec = verification_pass(p, N, out)
        v, fiber = evaluate(p, N, res, mis, rec, cellsmatch, out)
        allres[f'p{p}N{N}'] = res
        verdicts[f'p{p}N{N}'] = v
        fibers[(p, N)] = fiber
        out.append('  full delta-cell tables per root cell:')
        for ci, ((s1, s0), r, tup) in enumerate(SEALED_CELLS[p]):
            out.append(f'    cell psi=z^2+{s1}z+{s0}, r={r}, tuple {tup}: '
                       f'{allres[f"p{p}N{N}"]["delta_counts"][ci]}')
        out.append(f'  lump counts: {res["lump_counts"]}')
        out.append(f'  digit-cell counts: {res["dcell_counts"]}')
    # P9: N-stability across the two levels per prime
    p9 = {p: fibers[(p, Ns[1])] == p ** 3 * fibers[(p, Ns[0])]
          for p, Ns in ((2, (6, 7)), (3, (5, 6)))}
    order = ['P1', 'P2', 'P3', 'P4', 'P5', 'P6', 'P7', 'P8', 'F5', 'F6',
             'derived']
    summary = ['=' * 72, 'SUMMARY — SEALED D4-N3 GATE (all four configs):']
    for key in verdicts:
        summary.append(f'  {key}: ' + '  '.join(
            f'{k}:{"PASS" if verdicts[key][k] else "FAIL"}' for k in order))
    summary.append(f'  P9 N-stability: p=2 '
                   f'{"PASS" if p9[2] else "FAIL"} '
                   f'(384->3072 sealed); p=3 {"PASS" if p9[3] else "FAIL"} '
                   f'(3888->104976 sealed)')
    gate = all(all(v.values()) for v in verdicts.values()) and all(p9.values())
    summary.append(f'GATE VERDICT: {"PASS" if gate else "FAIL"}   '
                   f'(wall {time.time() - t0:.0f}s)')
    summary.append('=' * 72)
    out.extend(summary)
    os.makedirs(os.path.dirname(JSONPATH), exist_ok=True)
    with open(JSONPATH, 'w') as fh:
        json.dump(dict(seal='CASE_D4N3_SEALED_PREDICTIONS.md', seed=SEED,
                       results=allres, verdicts={
                           k: {kk: bool(vv) for kk, vv in v.items()}
                           for k, v in verdicts.items()},
                       P9={str(k): bool(v) for k, v in p9.items()},
                       gate='PASS' if gate else 'FAIL'), fh, indent=1)
    with open(OUTPATH, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    print('\n'.join(summary))
    return 0


if __name__ == '__main__':
    sys.exit(main())
